(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA Pm9DiagKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCB CStrKitCA PmCurSpecsBLocal.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_cstr_cboth_T Cut_cstr_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_cstr_cboth.
Module GT := Cut_cstr_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module CSA.
Definition PC_STRLEN : Z := 436492.
Definition PC_AMEMMOVE : Z := 522512.
Definition RETPC : Z := 863472.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10.
Definition IA (k : Z) : expr := EAlu Instr.ALU_ADD oE (ELit k).

Definition chain (i : nat) : nat := (i mod 3)%nat.
Definition stage (i : nat) : nat := (i / 3)%nat.
Definition SRCL (ch : nat) : Z := match ch with 0%nat => 155648 | 1%nat => 155584 | _ => 155616 end.
Definition KL (ch : nat) : Z := match ch with 2%nat => 5 | _ => 4 end.
Definition TXTL (ch : nat) : list Z := match ch with 0%nat => [110; 117; 108; 108] | 1%nat => [116; 114; 117; 101] | _ => [102; 97; 108; 115; 101] end.

Definition BUFL (ch : nat) : list Z := match ch with 0%nat => [110; 117; 108; 108; 0; 0; 0; 0] | 1%nat => [116; 114; 117; 101; 0; 0; 0; 0] | _ => [102; 97; 108; 115; 101; 0; 0; 0] end.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].
Definition TERM (ch : nat) : expr := IA (KL ch + 1).
Definition NEWS_MM (ch : nat) : list kentry := STAT ++ [KZero (SA (CHA.SRL3 (TERM ch)) SBz) (ELit 1)].
Definition FEX (ch : nat) : list SGP.region := [(EVar 2, -4176, ELit 4176); (TERM ch, 0, ELit 1)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition exit_cells (ch : nat) (cells : list kentry) : bool :=
  (has cells (KWord (SA oE 0) 1 (ELit (2 * KL ch))) && has cells (KWord (SA oE (KL ch + 1)) 1 (ELit 0)))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (Nat.eqb (chain j) (chain i) && Nat.eqb (stage j) (Datatypes.S (stage i)) && Nat.ltb i 9 && Nat.ltb j 9 &&
               CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) [] && CHA.foot_chk GT.NF G.HDECL c [] [] &&
              if Z.eqb pc PC_STRLEN then
                (Z.eqb (SR.ps_pc ps) PC_STRLEN && Nat.eqb (stage i) 0
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2304 0 [] [] [] STAT (Some (ELit (KL (chain i)))) c ps cj [] [] [] [])
                 && CL.ps_reg_is ps 10 (ELit (SRCL (chain i))))%bool
              else if Z.eqb pc PC_AMEMMOVE then
                (Z.eqb (SR.ps_pc ps) PC_AMEMMOVE && Nat.eqb (stage i) 1
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 [] [] [(IA 1, 0, ELit (KL (chain i)))] (NEWS_MM (chain i)) (Some (IA 1)) c ps cj [] [] [] [])
                 && CL.ps_reg_is ps 10 (IA 1) && CL.ps_reg_is ps 11 (ELit (SRCL (chain i))) && CL.ps_reg_is ps 12 (ELit (KL (chain i)))
                 && has cells (KZero (SA (CHA.SRL3 oE) SBz) (ELit 3)))%bool
              else false)%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c [] [] && CH2.blocks_eqb (nth i G.BLS []) []
           && Nat.eqb (stage i) 2 && Nat.ltb i 9 && CBA.regions_eqb (CC.cp_F c) (FEX (chain i)) && exit_cells (chain i) cells)%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.

Lemma kn_entry : CC.cp_know G.cp1 = CC.cp_know G.cp0 /\ CC.cp_know G.cp2 = CC.cp_know G.cp0.
Proof. vm_compute. split; reflexivity. Qed.

Lemma rom_lit : forall ch, (ch <= 2)%nat -> rdn RSEGS (fun _ => None) (Z_to_bv 64 (SRCL ch)) 8 = Some (map (Z_to_bv 8) (BUFL ch)).
Proof. intros ch Hch. destruct ch as [|[|[|ch]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia]. Qed.
Lemma rom_txt : forall ch, (ch <= 2)%nat -> rdn RSEGS (fun _ => None) (Z_to_bv 64 (SRCL ch)) (Z.to_nat (KL ch)) = Some (map (Z_to_bv 8) (TXTL ch)).
Proof. intros ch Hch. destruct ch as [|[|[|ch]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia]. Qed.

Lemma regs_entry : forall ch (R : bvmap 5 word), (ch <= 2)%nat -> getr R 11%bv = Z_to_bv 64 (SRCL ch) ->
  regs_ok (Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])) (CC.cp_regs (nth ch G.CPS G.cp0)) R.
Proof.
  intros ch R Hch Ha1 rr. unfold sr_get. destruct (bv_eqb rr 0) eqn:Hr0.
  - assert (rr = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; clear - Hr0; lia). subst rr. unfold getr. rewrite Hr0.
    destruct ch as [|[|[|ch]]]; [reflexivity | reflexivity | reflexivity | exfalso; clear - Hch; lia].
  - unfold reg_ev. rewrite <- (ridx_roundtrip rr) at 1. pose proof (ridx_range rr) as Hlt. set (nn := ridx rr) in *. clearbody nn.
    destruct ch as [|[|[|ch]]]; [| | | exfalso; clear - Hch; lia];
      [ let l := eval vm_compute in (CC.cp_regs (nth 0 G.CPS G.cp0)) in change (CC.cp_regs (nth 0 G.CPS G.cp0)) with l
      | let l := eval vm_compute in (CC.cp_regs (nth 1 G.CPS G.cp0)) in change (CC.cp_regs (nth 1 G.CPS G.cp0)) with l
      | let l := eval vm_compute in (CC.cp_regs (nth 2 G.CPS G.cp0)) in change (CC.cp_regs (nth 2 G.CPS G.cp0)) with l ];
      (do 32 (destruct nn as [|nn]; [cbn [nth edenot ev Nat.ltb Nat.leb Nat.sub]; first [reflexivity | exact Ha1] |]); exfalso; clear - Hlt; lia).
Qed.
End CSA.

Section CStrOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Abbreviation IC := PMLA.C_cboth.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis STRLEN : astrlen_spec L ar IL SCFG HI.
Hypothesis ILS : icl_strlen IL = CSA.PC_STRLEN.
Hypothesis ILSCR : 0 <= icl_scr_strlen IL <= 2304.
Hypothesis ILRO : PMLA.IMG_RO_LO IC <= icl_ro_lo IL /\ icl_ro_hi IL <= PMLA.IMG_RO_HI IC.
Hypothesis RTG : rt_globals IL HI.
Hypothesis ILG : forall ch, (ch <= 2)%nat -> In (CSA.SRCL ch, CSA.KL ch + 1) (icl_globals IL).

Lemma FFSnil : forall i, nth i CSA.FFS [] = [].
Proof. intros i. unfold CSA.FFS. do 9 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma est0 : forall E k, 0 <= k -> estart E (SA (ELit 0) k) = k.
Proof. intros E k Hk. unfold estart. cbn [a_base a_off edenot]. rewrite u64_of_Z by lia. lia. Qed.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.
Lemma lit_facts : forall ch, (ch <= 2)%nat ->
  Z.of_nat (length (CSA.TXTL ch)) = CSA.KL ch /\ (1 <= CSA.KL ch <= 5) /\ 155584 <= CSA.SRCL ch <= 155648 /\ CSA.SRCL ch mod 8 = 0 /\ length (CSA.BUFL ch) = 8%nat /\
  firstn (length (CSA.TXTL ch)) (CSA.BUFL ch) = CSA.TXTL ch /\ nth (Z.to_nat (CSA.KL ch)) (CSA.BUFL ch) 0 = 0 /\
  (forall j, (j < Z.to_nat (CSA.KL ch))%nat -> nth j (CSA.BUFL ch) 0 <> 0) /\ Forall (fun v => 0 <= v < 256) (CSA.BUFL ch).
Proof.
  intros ch Hch. destruct ch as [|[|[|ch]]]; [| | | exfalso; lia]; (split; [reflexivity|]); (split; [cbn; lia|]); (split; [cbn; lia|]); (split; [reflexivity|]);
    (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [intros j Hj; cbn in Hj; do 5 (destruct j as [|j]; [cbn; lia|]); exfalso; lia|]);
    repeat constructor; lia.
Qed.

Lemma al_word : forall s k, s mod 8 = 0 -> 0 <= k < 8 -> (s + k) / 8 * 8 + 8 = s + 8.
Proof. intros s k H1 H2. replace (s + k) with (k + (s / 8) * 8) by (pose proof (Z.div_mod s 8 ltac:(lia)); lia). rewrite Z.div_add by lia. rewrite (Z.div_small k 8) by lia. pose proof (Z.div_mod s 8 ltac:(lia)). lia. Qed.
Lemma byte_neq : forall v, 0 < v < 256 -> Z_to_bv 8 v <> Z_to_bv 8 0.
Proof. intros v Hv E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E. change (2 ^ Z.of_N 8) with 256 in E. rewrite (Z.mod_small v) in E by lia. cbn in E. lia. Qed.

Theorem cstr_ok : PMCSB.cstr_ctor_specB L ar HI IC 863168.
Proof.
  intros LB FF LK cr A o src sp r txt. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & HIN & HRO & _ & (Ofr & O8 & Osh) & DO & _) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMLA.apart in *. change (64 + (16 + 4096)) with 4176 in *.

  assert (HCH : exists ch0, (ch0 <= 2)%nat /\ src = CSA.SRCL ch0 /\ txt = CSA.TXTL ch0).
  { cbn [In] in HIN. destruct HIN as [E|[E|[E|[]]]]; injection E as E1 E2; subst src txt; [exists 0%nat | exists 1%nat | exists 2%nat]; (split; [lia | split; reflexivity]). }
  destruct HCH as (ch0 & Hch0 & -> & ->).
  pose proof (lit_facts ch0 Hch0) as (LN & LK1 & LSR & LA8 & LB8 & LFT & LNUL & LNZ & LV).
  set (src := CSA.SRCL ch0) in *. set (txt := CSA.TXTL ch0) in *. set (n := CSA.KL ch0) in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM. pose proof (L5A.aly_memmove L C LAY) as PCAMM.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar _ FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  assert (SHR : forall p k a, 0 <= p -> 0 < k -> p + k <= 2 ^ 47 -> in_shadow_of p k a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4176) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(o, 24)] : list L5.range).
  assert (RFr : CHA.rng_facts L ar LB FF) by exact RFx.
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFr Ofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (UOK : forall k, 0 <= k -> k <= 24 -> bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 10) (ELit k))) = o + k).
  { intros k K0 K1. cbn [edenot]. rewrite AX2S.u_add64, U10, (u64_of_Z k) by (clear - K0 K1; lia). apply Z.mod_small. clear - K0 K1 O3 O6; lia. }
  assert (GRN : forall k, 0 <= k < 24 -> (o + k) / 8 = o / 8 + k / 8).
  { intros k Hk. clear - O8 Hk. apply Z.mod_divide in O8; [|lia]. destruct O8 as [q ->]. rewrite Z.div_mul by lia. rewrite Z.div_add_l by lia. lia. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; cbv beta iota in Ha; rewrite CL5A.estart_srl3' in Ha; unfold CL5A.uv, elenZ in Ha.
    cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFr Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) =>
     L5.defined M1 o 24 /\ PMLA.img_ro IC M1 /\ CSA.chain i = ch0 /\ (CSA.stage i = 2%nat -> L5.bytes_at (hl_segs L) M1 (o + 1) txt)).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ CSA.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }
  assert (ST0 : CSA.stage ch0 = 0%nat /\ CSA.chain ch0 = ch0 /\ nth ch0 G.BLS [] = [] /\ nth_error G.CPS ch0 = Some (nth ch0 G.CPS G.cp0) /\ CC.cp_pc (nth ch0 G.CPS G.cp0) = 863168).
  { destruct ch0 as [|[|[|ch0]]]; [repeat split; reflexivity | repeat split; reflexivity | repeat split; reflexivity | exfalso; clear - Hch0; lia]. }
  destruct ST0 as (ST0 & CHN0 & BLS0 & CP0 & PC0).
  rewrite <- LS in FPM. rewrite <- PC0.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS CSA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := ch0) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact CSA.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    assert (UVE : forall E e z, env_agree GT.NF E0 E -> APC.expr_vars_lt GT.NF e = true -> CL5A.uv E0 e = z -> CL5A.uv E e = z).
    { intros E e z Hag Hv Hz. rewrite (CL5A.uv_agree GT.NF E0 E e Hag Hv). exact Hz. }
    assert (ULIT : forall E z, 0 <= z < 2 ^ 64 -> CL5A.uv E (ELit z) = z) by (intros E z Hz; unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; exact Hz).

    set (PZ := fun a : Z => PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).
    assert (PZV : forall a, PZ a <-> 65536 <= a < 1400832) by (intros a; unfold PZ; cbn; clear; lia).
    assert (PZC : forall LBx FFx spx scrx a, PZ a -> aclient L ar LBx FFx spx scrx a).
    { intros LBx FFx spx scrx a Ha. apply (proj1 (PZV _)) in Ha. right; right; left. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
    assert (NPZ_STK : forall a, sp - 4176 <= a < sp -> ~ PZ a) by (intros a Ha Hz; apply (proj1 (PZV _)) in Hz; clear - Ha Hz S2 CL; lia).
    assert (NPZ_O : forall a, o <= a < o + 24 -> ~ PZ a) by (intros a Ha Hz; apply (proj1 (PZV _)) in Hz; clear - Ha Hz O1 FSLO; lia).
    assert (IMGRO : forall (M1 M2 : mem), (forall a, PZ a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> PMLA.img_ro IC M1 -> PMLA.img_ro IC M2).
    { intros M1 M2 AG R1 a Ha. rewrite (AG a Ha). exact (R1 a Ha). }
    assert (HPZ : forall (M1 M2 : mem) LBx spx scrx Wc, CHA.ahpres L ar LBx FF spx scrx Wc M1 M2 -> (forall w a, In w Wc -> L5.in_rng w a -> ~ PZ a) ->
              forall a, PZ a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros M1 M2 LBx spx scrx Wc (HP1 & _ & _) HW a Ha. apply HP1. split; [apply (proj1 (PZV _)) in Ha; clear - Ha; lia|]. split; [exact (PZC _ _ _ _ a Ha)|]. intros w Hw Hin. exact (HW w a Hw Hin Ha). }
    assert (KDEF : forall (M1 M2 : mem) LBx spx scrx Wc, CHA.ahpres L ar LBx FF spx scrx Wc M1 M2 -> L5.defined M1 o 24 -> L5.defined M2 o 24).
    { intros M1 M2 LBx spx scrx Wc (_ & _ & HP3) XD i Hi. apply (HP3 (o + i)); [clear - Hi O3 O6; lia | | exact (XD i Hi)].
      right; right; right; left. destruct Ofr as (f & Hf & F1 & F2). exists f. split; [exact Hf | clear - Hi F1 F2; lia]. }

    assert (KOSH : forall (M1 M2 : mem) LBx spx scrx Wc, CHA.ahpres L ar LBx FF spx scrx Wc M1 M2 ->
              (forall w a, In w Wc -> L5.in_rng w a -> a < 2147446784 \/ 17594333495296 <= a) -> forall j, 0 <= j < 3 -> M2 (Z_to_bv 64 (S o + j)) = M1 (Z_to_bv 64 (S o + j))).
    { intros M1 M2 LBx spx scrx Wc (HP1 & _ & _) HW j Hj. pose proof (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia)) as SH. change (8 * 3) with 24 in SH.
      pose proof (SHR o 24 (S o + j) O3 ltac:(clear; lia) O6 SH) as SRa. apply HP1. split; [clear - SRa; lia|].
      split; [do 5 right; left; destruct Ofr as (f & Hf & F1 & F2); exists f; split; [exact Hf | exact (CL5A.in_shadow_mono o 24 (ff_addr f) (ff_bytes (ff_class f)) (S o + j) ltac:(clear - F1; lia) ltac:(clear - F2; lia) ltac:(clear; lia) SH)]|].
      intros w Hw Hin. pose proof (HW w _ Hw Hin) as X. clear - X SRa. lia. }

    assert (LAG : forall i c ps0 E E' R1 R' A1 M1 m1 M' m', nth i G.BLS [] = [] ->
              CHA.foot_chk GT.NF G.HDECL c [] [] = true ->
              CCA.AtV (hl_segs L) c E R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS CSA.FFS Cred 0 i E A1 M1 m1 ->
              env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
              forall a, PZ a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros i c ps0 E E' R1 R' A1 M1 m1 M' m' HBL Hfoot HAt HA Hag HLF a Ha.
      assert (A64 : 0 <= a < 2 ^ 64) by (apply (proj1 (PZV _)) in Ha; clear - Ha; lia).
      refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS CSA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK i c ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a A64 _);
        [rewrite FFSnil, HBL; exact Hfoot|].
      rewrite FFSnil, HBL. intros [X|[X|[X|[X|X]]]].
      - rewrite SCRV in X. exact (NPZ_STK a X Ha).
      - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (NPZ_O a Hin Ha).
      - destruct X as (b & Hb & _). exact Hb.
      - destruct X as (f & [] & _).
      - destruct X as (f & [] & _). }
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS CSA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.

    assert (AMM : forall dst sr nn bs LBx LKx crx Ax spx rx, CBA.cps_asanG L ar HI PMSA.fp_ok CSA.PC_AMEMMOVE rx spx 2560 LBx FF LKx crx Ax 0 (CRC.memcpy_pre L ar LBx FF spx 2560 dst sr nn bs) (CRC.memcpy_post LBx crx dst nn bs)).
    { intros dst sr nn bs LBx LKx crx Ax spx rx. unfold CSA.PC_AMEMMOVE. rewrite <- PCAMM. exact (CRC.asan_memmove_cps L ar C HI HIok PMSA.fp_ok 2560 LBx FF LKx crx Ax dst sr nn bs spx rx ltac:(rewrite SCRMEM; clear; lia)). }
    assert (SLEN : forall LBx LKx crx Ax spx rx s k buf, CBA.cps_asanG L ar HI PMSA.fp_ok CSA.PC_STRLEN rx spx 2304 LBx FF LKx crx Ax 0 (CSK.strlen_pre L ar IL LBx FF spx 2304 s k buf) (CSK.strlen_post LBx crx k)).
    { intros LBx LKx crx Ax spx rx s k buf. rewrite <- ILS. exact (CSK.strlen_cps L ar HI IL PMSA.fp_ok STRLEN 2304 LBx FF LKx crx Ax s k buf spx rx ILSCR). }

    assert (STNEWS : forall E2 A2 m2 M2 LB2 LK2 cr2, ri_inv HI LB2 FF LK2 cr2 A2 M2 (vml_of m2) -> forall X0, In X0 CSA.STAT -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0).
    { intros E2 A2 m2 M2 LB2 LK2 cr2 HH2 X0 HX0. unfold CSA.STAT in HX0. cbn [In] in HX0.
      destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). }

    assert (LITROM : forall (Mx : mem), PMLA.img_ro IC Mx -> rdn (hl_segs L) Mx (Z_to_bv 64 src) 8 = Some (map (Z_to_bv 8) (CSA.BUFL ch0)) /\
                       rdn (hl_segs L) Mx (Z_to_bv 64 src) (Z.to_nat n) = Some (map (Z_to_bv 8) txt)).
    { intros Mx Hro. rewrite LS. split.
      - rewrite (DK.rdn_img Mx 65536 1400832 src 8 Hro ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - LSR; lia) ltac:(clear - LSR; lia)). exact (CSA.rom_lit ch0 Hch0).
      - rewrite (DK.rdn_img Mx 65536 1400832 src (Z.to_nat n) Hro ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - LSR; lia) ltac:(rewrite Z2Nat.id by (clear - LK1; lia); clear - LSR LK1; lia)).
        exact (CSA.rom_txt ch0 Hch0). }
    assert (LITACC : forall LBx FFx LKx crx Ax (Mx : mem) V k, ri_inv HI LBx FFx LKx crx Ax Mx V -> 0 <= k <= n + 1 -> aacc Mx src k).
    { intros LBx FFx LKx crx Ax Mx V k HHx Hk. pose proof (RTG _ _ _ _ _ _ _ HHx) as GL. rewrite Forall_forall in GL. destruct (GL _ (ILG ch0 Hch0)) as (SB & _). cbn [fst snd] in SB.
      exact (CRC.aacc_blk Mx src (n + 1) src k SB LA8 ltac:(clear - LSR; lia) ltac:(clear; lia) ltac:(clear - Hk; lia)). }
    assert (LITAPP : forall k, 0 <= k <= 8 -> app_rng ar src k).
    { intros k Hk. unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. split; [clear - LSR; lia|]. split; [left; clear - LSR Hk; lia | left; clear - LSR Hk S2 S3 CL; lia]. }
    assert (LITIMG : forall k i, 0 <= i < k -> k <= 8 -> hl_img_lo L <= src + i < hl_img_hi L) by (intros k i Hi Hk; rewrite ILO, IHI; clear - LSR Hi Hk; lia).

    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ CSA.leaf_ok _ _ _ _ _ HIL) as X. unfold CSA.leaf_chk in X.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in X as [X0 XIF]. apply andb_prop in X0 as [X0 YF]. apply andb_prop in X0 as [X0 YBj]. apply andb_prop in X0 as [X0 YBi].
      apply andb_prop in X0 as [X0 Yj9]. apply andb_prop in X0 as [X0 Yi9]. apply andb_prop in X0 as [YCH YST].
      apply Nat.eqb_eq in YCH, YST. apply CH2.blocks_eqb_eq in YBi, YBj.
      assert (HcF : forall E, CHA.curF FF sp CSA.FFS i E = FF) by (intros E; unfold CHA.curF; rewrite FFSnil; reflexivity).
      assert (HcB : forall E, CHA.curB LB G.BLS i E = LB) by (intros E; unfold CHA.curB; rewrite YBi; reflexivity).
      assert (HcBj : forall E, CHA.curB LB G.BLS j E = LB) by (intros E; unfold CHA.curB; rewrite YBj; reflexivity).
      destruct (Z.eqb_spec pc CSA.PC_STRLEN) as [->|Hne1].
      {
        apply andb_prop in XIF as [XIF Y10]. apply andb_prop in XIF as [XIF Ychk]. apply andb_prop in XIF as [Y0 Ys0]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Ys0.
        lazymatch type of Ychk with CSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        unfold XI in HXi. destruct HXi as (XD & XR & XC & _).
        refine (CALLEE CSA.PC_STRLEN 2304 0%nat [] [] CSA.STAT (Some (ELit (CSA.KL (CSA.chain i)))) 0 i c ps0 j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LKc CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        pose proof (LAG i c ps0 E E' R1 R' A1 M1 m1 M' m' YBi YF HAt HA Hag HLF) as AGL.
        assert (XR' : PMLA.img_ro IC M') by exact (IMGRO M1 M' AGL XR).
        assert (XD' : L5.defined M' o 24) by exact (L5.defined_grows M1 M' o 24 (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) XD).
        rewrite XC in Y10 |- *. destruct (LITROM M' XR') as (ROM8 & _).
        eexists. eexists. split; [exact (SLEN LB LKc cr A1 (sp + CH2.ci_csp ci) (CC.cp_pc cj) src n (map (Z_to_bv 8) (CSA.BUFL ch0)))|]. split.
        { unfold CSK.strlen_pre. rewrite length_map, LB8. change (Z.of_nat 8) with 8.
          split; [exact (REG 10%nat _ src Y10 (ULIT E' src ltac:(clear - LSR; lia)))|]. split; [clear - LSR; lia|]. split; [clear - LSR; lia|]. split; [clear - LK1; lia|].
          split; [exact ROM8|]. split; [rewrite (al_word src n LA8 ltac:(clear - LK1; lia)); clear; lia|].
          split; [rewrite (map_nth (Z_to_bv 8) (CSA.BUFL ch0) 0), LNUL; reflexivity|].
          split.
          { intros jj Hjj. assert (Hj8 : (jj < length (CSA.BUFL ch0))%nat).
            { rewrite LB8. assert (T : (Z.to_nat n <= 5)%nat) by (apply Nat2Z.inj_le; rewrite Z2Nat.id by (clear - LK1; lia); cbn; clear - LK1; lia). clear - Hjj T; lia. }
            rewrite (map_nth (Z_to_bv 8) (CSA.BUFL ch0) 0). apply byte_neq. rewrite Forall_forall in LV. pose proof (LV _ (nth_In _ 0 Hj8)) as Z2. pose proof (LNZ jj Hjj) as Z1. clear - Z1 Z2; lia. }
          split; [intros ii Hii; left; exact (LITIMG 8 ii Hii ltac:(clear; lia))|].
          split; [intros a Ha; apply XR'; destruct ILRO as (IR1 & IR2); clear - Ha IR1 IR2; lia|].
          split; [exact (LITACC _ _ _ _ _ _ _ (n + 1) HH1 ltac:(clear - LK1; lia)) | exact (LITAPP (n + 1) ltac:(clear - LK1; lia))]. }
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        exists []. split; [reflexivity|]. cbv zeta. set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        split; [rewrite Ha0'; reflexivity|].
        split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
        split; [rewrite HcBj; exact HH2|]. split; [unfold Cred; reflexivity|].
        split.
        { unfold XI. split; [exact (KDEF M' M2 LB _ 2304 [] HP XD')|]. split; [exact (IMGRO M' M2 (HPZ M' M2 LB _ 2304 [] HP (fun w a Hw _ => match Hw with end)) XR')|].
          split; [rewrite YCH; exact XC|]. intros Hs2. exfalso. rewrite YST, Ys0 in Hs2. discriminate Hs2. }
        intros X0 HX0 _. exact (STNEWS E2 A2 m2 M2 _ _ _ HH2 X0 HX0). }
      destruct (Z.eqb_spec pc CSA.PC_AMEMMOVE) as [->|Hne2]; [|cbn iota in XIF; discriminate XIF].

      apply andb_prop in XIF as [XIF Ysh]. apply andb_prop in XIF as [XIF Y12]. apply andb_prop in XIF as [XIF Y11]. apply andb_prop in XIF as [XIF Y10].
      apply andb_prop in XIF as [XIF Ychk]. apply andb_prop in XIF as [Y0 Ys1]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Ys1.
      lazymatch type of Ychk with CSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
      unfold XI in HXi. destruct HXi as (XD & XR & XC & _).
      refine (CALLEE CSA.PC_AMEMMOVE 2560 0%nat [] [(CSA.IA 1, 0, ELit (CSA.KL (CSA.chain i)))] (CSA.NEWS_MM (CSA.chain i)) (Some (CSA.IA 1)) 0 i c ps0 j cj ci Hcj _ Y0 _ _
                fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LKc CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (CELL : forall X0, CSA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
      assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
      { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      assert (W10 : CL5A.uv E' (EVar 10) = o) by exact (UVE E' (EVar 10) o HagE' eq_refl U10).
      assert (SZ' : shadow_zero M' o 3).
      { intros jj Hj. apply (CL5A.byte_full (ahid A1 m') M'). exact (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 3 o (CELL _ Ysh) W10 ltac:(clear; lia) jj Hj). }
      assert (XD' : L5.defined M' o 24) by exact (L5.defined_grows M1 M' o 24 (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF) XD).
      pose proof (LAG i c ps0 E E' R1 R' A1 M1 m1 M' m' YBi YF HAt HA Hag HLF) as AGL.
      assert (XR' : PMLA.img_ro IC M') by exact (IMGRO M1 M' AGL XR).
      rewrite XC in Y11, Y12 |- *. destruct (LITROM M' XR') as (_ & ROMN).
      assert (UD : CL5A.uv E' (CSA.IA 1) = o + 1) by exact (UVE E' (CSA.IA 1) (o + 1) HagE' eq_refl (UOK 1 ltac:(clear; lia) ltac:(clear; lia))).
      eexists. eexists. split; [exact (AMM (o + 1) src n (map (Z_to_bv 8) txt) LB LKc cr A1 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
      { unfold CRC.memcpy_pre. split; [exact (REG 10%nat _ (o + 1) Y10 UD)|]. split; [exact (REG 11%nat _ src Y11 (ULIT E' src ltac:(clear - LSR; lia)))|].
        split; [exact (REG 12%nat _ n Y12 (ULIT E' n ltac:(clear - LK1; lia)))|]. split; [|split].
        -
          unfold CRC.mem_dst. split; [clear - LK1; lia|]. split.
          + intros a Ha. left. replace (S a) with (S o + (a - o) / 8) by (unfold S; pose proof (GRN (a - o) ltac:(clear - Ha LK1; lia)) as G; replace (o + (a - o)) with a in G by (clear; lia); rewrite G; clear; lia).
            apply SZ'. split; [apply Z.div_pos; clear - Ha; lia | apply Z.div_lt_upper_bound; clear - Ha LK1; lia].
          + split; [intros k Hk; exact (CL5A.infr_clientw L ar LB FF _ 2560 o 24 (o + 1 + k) Ofr ltac:(clear - Hk LK1; lia))|].
            split; [exact (L5C.writable_of_defined (hl_segs L) M' (o + 1) n (L5.defined_sub M' o 24 (o + 1) n XD' ltac:(clear; lia) ltac:(clear - LK1; lia)) ltac:(clear - O3; lia) ltac:(clear - O6 LK1; lia))|].
            unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. unfold hid in O5. split; [clear - O3; lia|]. split; [clear - O5 LK1; lia | left; clear - O4 S2 S3 LK1; lia].
        - unfold CRC.mem_src. split; [exact (LITACC _ _ _ _ _ _ _ n HH1 ltac:(clear - LK1; lia))|].
          split; [clear - LSR LK1; lia|]. split; [exact (LITAPP n ltac:(clear - LK1; lia))|]. split; [intros ii Hii; left; exact (LITIMG n ii Hii ltac:(clear - LK1; lia))|]. exact ROMN.
        - clear - LSR LK1 O1 FSLO. lia. }
      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Hnew & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      exists []. split; [reflexivity|]. cbv zeta. set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
      pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' E2) as Hag2.
      assert (HagE2 : env_agree GT.NF E0 E2).
      { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
      assert (UD2 : CL5A.uv E2 (CSA.IA 1) = o + 1) by exact (UVE E2 (CSA.IA 1) (o + 1) HagE2 eq_refl (UOK 1 ltac:(clear; lia) ltac:(clear; lia))).
      split; [rewrite Ha0'; unfold CL5A.uv in UD2; rewrite <- UD2; apply Z_to_bv_bv_unsigned|].
      split; [cbn [CH2.den map app]; apply incl_refl|].
      assert (WIN : forall w a, In w [(o + 1, n)] -> L5.in_rng w a -> o + 1 <= a < o + 1 + n) by (intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin).
      split.
      { intros w a Hw Hin. pose proof (WIN w a Hw Hin) as Ha. exists (CSA.IA 1, 0, ELit n). split; [left; reflexivity|].
        unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. pose proof (ULIT E' n ltac:(clear - LK1; lia)) as UN. unfold CL5A.uv in UD, UN. rewrite UD, UN. clear - Ha. lia. }
      split.
      { intros w a Hw Hin (Ka & Kc & Kw). apply (Kw (o, 24)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. pose proof (WIN w a Hw Hin). clear - H LK1. lia. }
      split; [rewrite HcBj; exact HH2|]. split; [unfold Cred; reflexivity|].
      assert (KO2 : forall jj, 0 <= jj < 3 -> M2 (Z_to_bv 64 (S o + jj)) = M' (Z_to_bv 64 (S o + jj))).
      { apply (KOSH M' M2 LB _ 2560 _ HP). intros w a Hw Hin. pose proof (WIN w a Hw Hin). unfold hid in O5. clear - H O5 LK1. lia. }
      split.
      { unfold XI. split; [exact (KDEF M' M2 LB _ 2560 _ HP XD')|].
        split; [exact (IMGRO M' M2 (HPZ M' M2 LB _ 2560 _ HP (fun w a Hw Hin => NPZ_O a ltac:(pose proof (WIN w a Hw Hin); clear - H LK1; lia))) XR')|].
        split; [rewrite YCH; exact XC|]. intros _. apply (TKA.bytes_of_copy2 (hl_segs L) M2 (o + 1) txt). intros ii Hii. apply Hnew. rewrite <- LN. exact Hii. }

      intros X0 HX0 _. unfold CSA.NEWS_MM in HX0. apply in_app_or in HX0. destruct HX0 as [HX0|[<-|[]]]; [exact (STNEWS E2 A2 m2 M2 _ _ _ HH2 X0 HX0)|].
      assert (UT2 : CL5A.uv E2 (CSA.TERM ch0) = o + n + 1) by exact (UVE E2 (CSA.TERM ch0) (o + n + 1) HagE2 eq_refl ltac:(unfold CSA.TERM, CSA.IA, CSA.oE, CL5A.uv; fold n; rewrite (UOK (n + 1)) by (clear - LK1; lia); clear; lia)).
      eapply CL5A.kzero_intro with (A := (o + n + 1) / 8 + 2147450880) (N := 1);
        [rewrite CL5A.estart_srl3, UT2; reflexivity | apply elit; clear; lia | clear - O3 LK1; lia | clear - O3 O6 LK1; lia | clear - O3 O6 LK1; lia |].
      intros jj Hj. replace ((o + n + 1) / 8 + 2147450880 + jj) with (S o + (n + 1) / 8) by (unfold S, SB; replace (o + n + 1) with (o + (n + 1)) by (clear; lia); rewrite (GRN (n + 1)) by (clear - LK1; lia); clear - Hj; lia).
      pose proof (Z.div_pos (n + 1) 8 ltac:(clear - LK1; lia) ltac:(clear; lia)) as G0. pose proof (Z.div_lt_upper_bound (n + 1) 8 3 ltac:(clear; lia) ltac:(clear - LK1; lia)) as G1.
      apply CL5A.byte_vis; [| unfold byte_at; rewrite (KO2 ((n + 1) / 8) ltac:(clear - G0 G1; lia)); exact (SZ' ((n + 1) / 8) ltac:(clear - G0 G1; lia))].
      destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + (n + 1) / 8) RFx Ofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + (n + 1) / 8) O8 ltac:(clear; lia) ltac:(unfold S; clear - G0 G1; lia))) as (V1 & V2' & V3).
      exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 _ HH2 V1 (aclientw_client _ _ _ _ _ _ _ V2') V3).
    +
      apply andb_prop in X as [X YEX]. apply andb_prop in X as [X YFX]. apply andb_prop in X as [X Yi9]. apply andb_prop in X as [X Ys2]. apply andb_prop in X as [X YB].
      apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Y0 Xbase].
      apply Z.eqb_eq in Y0. subst pc. apply CH2.blocks_eqb_eq in YB. apply Nat.eqb_eq in Ys2. apply CBA.regions_eqb_eq in YFX.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      unfold XI in HXi. destruct HXi as (XD & XR & XC & XBY). specialize (XBY Ys2).
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS CSA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok CSA.RETPC i c ps0 _ Xbase _ (FFSnil i) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact CSA.ret_at | rewrite FFSnil, YB; exact Xfoot |].
      intros model2 cr1 LK1' HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (CELL : forall X0, CSA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS CSA.FFS Cred 0 i E A1 M' m' HA') as Hoff.
      assert (W10 : CL5A.uv E' (EVar 10) = o) by exact (UVE E' (EVar 10) o HagE' eq_refl U10).
      assert (EST : forall k, estart E' (SA CSA.oE k) = o + k) by (intros k; unfold estart; cbn [a_base a_off]; unfold CL5A.uv in W10; unfold CSA.oE; rewrite W10; reflexivity).
      rewrite SCRV in HP.
      assert (U8C : forall a v Aa z, CSA.has (SR.ps_cells ps0) (KWord a 1 v) = true -> estart E' a = Aa -> CL5A.uv E' v = z -> L5.u8_at (hl_segs L) M' Aa z).
      { intros a v Aa z Hc Ha Hz. apply (CL5A.u8_full (hl_segs L) _ Hoff). rewrite <- Hz. exact (CL5A.kword8_elim (hl_segs L) E' _ a v Aa (CELL _ Hc) Ha). }
      rewrite XC in YEX, YFX. unfold CSA.exit_cells in YEX. apply andb_prop in YEX as [Yo0 Yt].
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (HB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite YB; reflexivity). rewrite HB in HH1.

      assert (BY : L5.bytes_at (hl_segs L) M' (o + 1) txt).
      { apply (CL5A.bytes_same (hl_segs L) M1 M' (o + 1) txt ltac:(clear - O3; lia) ltac:(rewrite LN; clear - O6 LK1; lia)); [|exact XBY]. intros a Ha. rewrite LN in Ha.
        apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF (Z_to_bv 64 a)). rewrite YFX. unfold CSA.FEX, SGP.outside. rewrite u64_of_Z by (clear - Ha O3 O6 LK1; lia).
        constructor; [|constructor; [|constructor]].
        - rewrite (CL5.estart_lin E' (EVar 2) (-4176) sp ltac:(lin_eval; rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); rewrite U2; clear; lia) ltac:(clear - S2 S3 CL SP1; lia)).
          left. clear - Ha O4 S2 LK1. lia.
        - unfold estart. cbn [a_base a_off]. pose proof (UVE E' (CSA.TERM ch0) (o + n + 1) HagE' eq_refl ltac:(unfold CSA.TERM, CSA.IA, CSA.oE, CL5A.uv; fold n; rewrite (UOK (n + 1)) by (clear - LK1; lia); clear; lia)) as UT.
          unfold CL5A.uv in UT. rewrite UT. left. clear - Ha; lia. }
      apply (Hcont fx' R' M' model2 LB cr LB WW LK1' A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      split; [reflexivity|]. split; [reflexivity|]. split; [| split; reflexivity].
      cbn [PMLA.str_at_w]. unfold L5.lstr_short. rewrite LN.
      split; [apply Nat2Z.inj_le; rewrite LN; clear - LK1; cbn; lia|].
      split; [pose proof (U8C _ _ _ (2 * n) Yo0 (EST 0) (ULIT E' (2 * n) ltac:(clear - LK1; lia))) as G; rewrite Z.add_0_r in G; exact G|].
      split; [exact BY|].
      pose proof (U8C _ _ _ 0 Yt (EST (n + 1)) (ULIT E' 0 ltac:(clear; lia))) as G. replace (o + (n + 1)) with (o + 1 + n) in G by (clear; lia). exact G.
  - exact CP0.
  -
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) o 24).
    { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Ofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Ofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) O8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4176) 4176).
    { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DOv : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact DO).
    assert (DSv : L5.defined Mv (sp - 4176) 4176) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    split; [exact (CSA.regs_entry ch0 R Hch0 Ha1)|]. unfold know_ok.
    assert (KN0 : CC.cp_know (nth ch0 G.CPS G.cp0) = CC.cp_know G.cp0).
    { destruct ch0 as [|[|[|ch0]]]; [reflexivity | exact (proj1 CSA.kn_entry) | exact (proj2 CSA.kn_entry) | exfalso; clear - Hch0; lia]. }
    rewrite KN0. let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |]. intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Osh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.kunk_intro with (A := sp - 4176) (N := 4176); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DSv].
    + eapply CL5.kwr_intro with (A := sp - 4176) (N := 4176); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DSv].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4176) (N1 := 4176) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite FFSnil, BLS0. cbn [app CHA.denF CH2.den map length].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; reflexivity | exact Hroom].
    + unfold XI. split; [exact DO|]. split; [exact HRO|]. split; [exact CHN0|]. intros H2. rewrite ST0 in H2. discriminate H2.
  - exact Hfp.
Qed.

End CStrOk.
