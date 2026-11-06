(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_vec_push_casan_T Cut_vec_push_casan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_vec_push_casan.
Module GT := Cut_vec_push_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module VPA.
Definition PC_AINC : Z := 807940.
Definition PC_SLOW : Z := 807460.
Definition RETPC : Z := 807400.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10. Definition xaE := EVar 11. Definition bE := EVar 32. Definition lnE := EVar 33. Definition capE := EVar 34.
Definition shvE := EVar 35. Definition sheE := EVar 36. Definition xvE := EVar 37.
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1427896) 8 (ELit SBz)].

Definition WSH : list SGP.region := [(CHA.SRL3 bE, SBz, CHA.SRL3 (APC.eaddz capE 7))].
Definition NEWS_AINC : list kentry := STAT ++ [KWord (SA (CHA.SRL3 (APC.eadd bE lnE)) SBz) 1 sheE].
Definition NEWS_SLOW : list kentry := STAT ++ [KWord (SA oE 0) 8 (EVar 48); KWord (SA oE 16) 8 (APC.eadd (EVar 48) (EVar 49))].

Definition kind (j : nat) : Z :=
  match find (fun r : nat * nat * nat * Z => Nat.eqb (fst (fst (fst r))) j) G.RETS with Some (_, _, _, pc) => pc | None => 0 end.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.
Definition vec_cells (cells : list kentry) : bool :=
  (has cells (KWord (SA oE 0) 8 bE) && has cells (KWord (SA oE 8) 8 (APC.eadd bE lnE)) && has cells (KWord (SA oE 16) 8 (APC.eadd bE capE)))%bool.

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      if Z.eqb pc PC_AINC then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_AINC && Z.eqb (kind i) 0 && Z.eqb (kind j) PC_AINC
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [] && CH2.blocks_eqb (nth i G.BLS []) [(bE, capE)] && CH2.blocks_eqb (nth j G.BLS []) [(bE, capE)]
                                  && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 (nth i G.BLS []) [] WSH NEWS_AINC None c ps cj (nth i G.BLS []) [] (nth j G.BLS []) [])
                                  && CL.ps_reg_is ps 10 oE && CL.ps_reg_is ps 11 (ELit 1) && vec_cells cells
                                  && CBA.has_range cells (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) lnE) capE) 1 (2 ^ 62))%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc PC_SLOW then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => (Z.eqb (SR.ps_pc ps) PC_SLOW && Z.eqb (kind i) 0 && Z.eqb (kind j) PC_SLOW && Nat.eqb (CC.cp_nx cj) 67
                                  && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [] && CH2.blocks_eqb (nth i G.BLS []) [(bE, capE)] && CH2.blocks_eqb (nth j G.BLS []) [(EVar 48, EVar 49)]
                                  && has cells (KBlob (SA bE 0) lnE 0)
                                  && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 8192 3 [] [] [(oE, 0, ELit 24)] NEWS_SLOW (Some (APC.eadd (EVar 48) (EVar 50)))
                                               c ps cj (nth i G.BLS []) [] (nth j G.BLS []) [])
                                  && CL.ps_reg_is ps 10 oE && CL.ps_reg_is ps 11 xaE && vec_cells cells
                                  && CBA.has_range cells (EAlu Instr.ALU_ADD lnE (EMd Instr.M_MUL (ELit (-1)) capE)) 0 (2 ^ 62))%bool
                    | None => false end
        | None => false end
      else
        (CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [] &&
         (if Z.eqb (kind i) PC_AINC then
            (CH2.blocks_eqb (nth i G.BLS []) [(bE, capE)] && has cells (KWord (SA oE 0) 8 bE) && has cells (KWord (SA oE 8) 8 (EAlu Instr.ALU_ADD (APC.eadd bE lnE) (ELit 1))) && has cells (KWord (SA oE 16) 8 (APC.eadd bE capE))
             && has cells (KBlob (SA bE 0) lnE 0) && has cells (KWord (SA (APC.eadd bE lnE) 0) 1 xvE))
          else if Z.eqb (kind i) PC_SLOW then
            (CH2.blocks_eqb (nth i G.BLS []) [(EVar 48, EVar 49)] && Nat.ltb 50 (CC.cp_nx c) && CBA.regions_eqb (CC.cp_F c) [(EVar 2, -8240, ELit 8240); (oE, 0, ELit 24)] && has cells (KWord (SA oE 0) 8 (EVar 48)) && has cells (KWord (SA oE 8) 8 (APC.eadd (EVar 48) (EVar 50))) && has cells (KWord (SA oE 16) 8 (APC.eadd (EVar 48) (EVar 49))))
          else false))%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End VPA.

Section VecPushOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis AINC_OK : PMSA.annotate_increase_spec L ar HI VPA.PC_AINC.
Hypothesis SLOW_OK : PMSA.vec_push_slow_spec L ar HI VPA.PC_SLOW.

Definition al (x m : Z) : Prop := x mod m = 0.
Definition eqz (a b : Z) : Prop := a = b.
Definition ltm (x m v : Z) : Prop := x mod m < v.
Definition hid (P : Prop) : Prop := P.
Lemma FFSnil : forall i, nth i VPA.FFS [] = [].
Proof. intros i. unfold VPA.FFS. do 13 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma byte_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Zmod_mod. Qed.

Lemma cont_end_byte : forall (M : word -> option byte) b cap len, 0 <= len -> shadow_cont M b cap (len + 1) -> byte_at M (S b + len / 8) ((len + 1) mod 8).
Proof.
  intros M b cap len Hl (Z0 & P0 & _). pose proof (Z.div_mod len 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound len 8 ltac:(lia)) as R.
  pose proof (Z.div_mod (len + 1) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (len + 1) 8 ltac:(lia)) as R1.
  destruct (Z.eq_dec ((len + 1) mod 8) 0) as [e|ne].
  - rewrite e. apply Z0. lia.
  - replace (len / 8) with ((len + 1) / 8) by lia. exact (P0 ne).
Qed.

Theorem vec_push_ok : PMSA.vec_push_specA L ar HI 807200.
Proof.
  intros LB FF LK cr A o b cap xa x sp r st. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Hvec & Hbytes & Hx & Hxfr & Hxacc & Hxo & Hcred & Hstksh) Hcont.
  destruct Hvec as ((Hw0 & Hw8 & Hw16) & Hofr & Ho8 & Hosh & HinLB & Hlen & Hcap & Hshc).
  set (len := Z.of_nat (length st)) in *.
  unfold PMSA.a0, PMSA.a1, PMSA.u64, PMSA.u8, PMSA.VPUSH_SCR, PMSA.VSLOW_SCR, PMSA.ainfr, PMSA.acobj in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (b, cap) HinLB) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bdef, Bsa, Bap, Bfap.
  pose proof (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH (b, cap) HinLB ltac:(cbn [snd]; lia)) as BHI. cbn [fst] in BHI.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)).
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  change (al sp 16) in S1. change (al o 8) in Ho8. change (al b 16) in B16. change (al (ahl_ceil ar) 8) in C8. change (al (ar_sptop ar) 16) in SP16.
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Hofr ltac:(lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.acobj_rng L ar LB FF sp xa 1 RFx ltac:(lia) Hxfr ltac:(lia)) as (X3 & X6 & X5 & X1 & X4).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (B1' : hl_img_hi L <= b) by (rewrite ILO, IHI in *; lia). clear B1 B6.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (xa + 1 <= 2147446784 \/ 17594333495296 <= xa)) in X5.
  change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7. change (hid (xa + 1 <= o \/ o + 24 <= xa)) in Hxo.
  change (hid (ar_fs ar + 32 <= xa \/ ahl_ceil ar <= xa)) in X1. change (hid (xa + 1 <= ahl_ceil ar \/ sp <= xa)) in X4.
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  assert (RFr : CHA.rng_facts L ar (lb_remove b LB) FF).
  { apply (CHA.rng_incl L ar LB FF); [exact RFx | intros y Hy; exact (L5C.in_lb_remove b y LB Hy) | apply incl_refl]. }

  assert (SHV : exists shv, byte_at M (S xa) shv /\ (shv = 0 \/ (1 <= shv <= 7 /\ ltm xa 8 shv))).
  { destruct (Hxacc xa ltac:(lia)) as [H0|(v & Hv & Hr & Hl)]; [exists 0; split; [exact H0 | left; reflexivity] | exists v; split; [exact Hv | right; split; assumption]]. }
  destruct SHV as (shv & Hshv & Hshr).
  assert (SHVR : 0 <= shv <= 7) by (destruct Hshr as [->|[? _]]; lia). change (hid (shv = 0 \/ 1 <= shv <= 7 /\ ltm xa 8 shv)) in Hshr.
  pose proof (Z.mod_pos_bound (len + 1) 8 ltac:(lia)) as SHE. pose proof (Z.mod_pos_bound x 256 ltac:(lia)) as XM.
  assert (Hxm : L5.u8_at (hl_segs L) M xa (x mod 256)) by (unfold L5.u8_at; rewrite byte_mod; exact Hx).
  remember ((len + 1) mod 8) as she eqn:Eshe. remember (x mod 256) as xm eqn:Exm. change (eqz she ((len + 1) mod 8)) in Eshe. change (eqz xm (x mod 256)) in Exm.

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; len; cap; shv; she; xm] 0))) (fun id => nth id [map (Z_to_bv 8) st] [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 xa) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 len) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 cap) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 shv) by reflexivity.
  assert (V36 : ev E0 36 = Z_to_bv 64 she) by reflexivity.
  assert (V37 : ev E0 37 = Z_to_bv 64 xm) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = xa) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = len) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = cap) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = shv) by (rewrite V35; apply u64_of_Z; lia).
  assert (U36 : bv_unsigned (ev E0 36) = she) by (rewrite V36; apply u64_of_Z; lia).
  assert (U37 : bv_unsigned (ev E0 37) = xm) by (rewrite V37; apply u64_of_Z; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 8240) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (WOK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar (lb_remove b LB) FF sp _ o 24 a RFr Hofr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar (lb_remove b LB) FF sp G.HDECL a)).
  { intros rg Hrg. change (CH.hd_crs G.HDECL) with (CH.hd_crs GT.HDECL) in Hrg. cbn [CH.hd_crs GT.HDECL In] in Hrg. destruct Hrg as [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; unfold CHA.sclientA.
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia.
      pose proof (CL5A.shreg_in_shadow o 3 a Ho8 ltac:(lia) ltac:(unfold SB; lia)) as SH. change (8 * 3) with 24 in SH.
      destruct (CL5A.infr_sh_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) o 24 a RFr Hofr ltac:(lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. unfold estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia.
      destruct (CL5A.acobj_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) xa 1 a RFr CSP Hxfr ltac:(lia)) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia.
      pose proof (CL5A.shreg1_in_shadow xa a ltac:(unfold SB; lia)) as SH.
      destruct (CL5A.acobj_sh_wok L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) xa 1 a RFr CSP Hxfr ltac:(lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. lia. }

  set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => if Z.eqb (VPA.kind i) VPA.PC_SLOW then cr1 = adebit L cr (2 * cap) else cr1 = cr).
  set (SLOWP := fun (E : env) (M' : word -> option byte) => len = cap /\ exists b', CL5A.uv E (EVar 48) = b' /\ CL5A.uv E (EVar 49) = 2 * cap /\ CL5A.uv E (EVar 50) = cap + 1 /\
                 L5.bytes_at (hl_segs L) M' b' (st ++ [x]) /\ PMSA.afresh_cont L ar (lb_remove b LB) FF M' b' (2 * cap) (cap + 1)).
  set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M' : word -> option byte) (_ : Model) =>
               if Z.eqb (VPA.kind i) VPA.PC_SLOW then SLOWP E M'
               else if Z.eqb (VPA.kind i) VPA.PC_AINC then len < cap /\ shadow_cont M' b cap (len + 1) else shadow_cont M' b cap len).

  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  assert (KSH : forall p n a, CL5A.acobj ar FF sp p n -> 0 < n -> in_shadow_of p n a -> CHA.akept L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) [(o, 24)] a).
  { intros p n a Hp Hn Ha. destruct (CL5A.acobj_sh_wok L ar _ FF sp (CH.hd_scr G.HDECL) p n a RFr CSP Hp Hn Ha) as (G1 & G2 & _).
    destruct (CL5A.acobj_rng L ar LB FF sp p n RFx CSP Hp Hn) as (P3 & P6 & _). pose proof (SHR p n a P3 Hn P6 Ha) as SR.
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin SR O5. lia. }
  assert (KXA : CHA.akept L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) [(o, 24)] xa).
  { destruct (CL5A.acobj_wok L ar _ FF sp (CH.hd_scr G.HDECL) xa 1 xa RFr CSP Hxfr ltac:(clear; lia)) as (G1 & G2 & _).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in Hxo. clear - Hin Hxo. lia. }

  assert (AL8240 : (sp - (48 + 8192)) mod 8 = 0).
  { unfold al in S1. clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp / 16) - (48 + 8192)) with ((2 * (sp / 16) - 1030) * 8) by lia. apply Z_mod_mult. }
  assert (KSTK : forall a, S (sp - (48 + 8192)) <= a < S (sp - (48 + 8192)) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - (48 + 8192))) / 8 ->
            CHA.akept L ar (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) [(o, 24)] a).
  { intros a Ha. unfold al in C8. destruct (PTA.stksh_rng ar sp (48 + 8192) a ltac:(clear - S2; lia) AL8240 C8 (proj2 S4) (CHA.wf_top _ _ _ _ _ _ _ _ WF) ltac:(clear - CL; lia) Ha) as (G1 & G2).
    split; [exact G1|]. split; [right; right; right; right; left; exact G2|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
    unfold in_shadow_of, S, SB in G2. unfold hid in O5. clear - Hin G2 O5 CL. lia. }

  assert (NOFOOT : forall a, 2147450880 <= a < 17594333495296 -> ~ CHA.afoot_sem sp G.HDECL [(o, 24)] [(b, cap)] [] a).
  { intros a Ha [X|[X|[X|[X|X]]]].
    - rewrite SCRV in X. clear - X Ha S2 CL. lia.
    - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin Ha O5. lia.
    - destruct X as (bb & [<-|[]] & Hin). cbn [fst snd] in Hin. clear - Hin Ha BHI. lia.
    - destruct X as (f & [] & _).
    - destruct X as (f & [] & _). }
  assert (NOGOTO : forall i c kk ps j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps (CC.TGoto j sg) -> False).
  { intros i c kk ps j sg IL. pose proof (CH2.leaves_all_sound _ _ _ VPA.leaf_ok _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X. }

  assert (MAIN : forall i c, nth_error G.CPS i = Some c -> (i < 4)%nat -> CC.cp_pc c = 807200 -> CCA.AtV (hl_segs L) c E0 R A M model ->
            srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 807200) M (seg_rom (hl_segs L))) model) K).
  { intros i0 c0 Hc0 Hi0 Hpc0 HAt0. rewrite <- Hpc0.
    eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] [(o, 24)] G.BLS VPA.FFS Cred 4 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
              G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
    - rewrite LS. exact FPM.
    - rewrite LS. exact G.plans.
    - exact G.tags_ok.
    - exact VPA.heap_ok.
    - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
    - intros i c kk ps j sg IL. exfalso. exact (NOGOTO _ _ _ _ _ _ IL).
    -
      intros i c kk ps pc IL. pose proof (CH2.leaves_all_sound _ _ _ VPA.leaf_ok _ _ _ _ _ IL) as X. unfold VPA.leaf_chk in X.
      pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] [(o, 24)] G.BLS VPA.FFS Cred 4 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                    G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
      destruct (Z.eqb_spec pc VPA.PC_AINC) as [->|Hne1].
      {
        destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
        apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y9]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y7]. apply andb_prop in X as [X Y6].
        apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0, Y1, Y2. apply CH2.blocks_eqb_eq in Y4, Y5.
        lazymatch type of Y6 with VPA.isSome ?t = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        assert (HXi' : shadow_cont M1 b cap len) by (unfold XI in HXi; rewrite Y1 in HXi; exact HXi).
        assert (HcB : CHA.curB (lb_remove b LB) G.BLS i E = (b, cap) :: lb_remove b LB).
        { unfold CHA.curB. rewrite Y4. unfold CH2.den. cbn [map fst snd VPA.bE VPA.capE edenot app]. rewrite <- (proj1 HagE 32%nat), <- (proj1 HagE 34%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U32, U34. reflexivity. }
        assert (HcF : CHA.curF FF sp VPA.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE VPA.PC_AINC 4112 0%nat (nth i G.BLS []) VPA.WSH VPA.NEWS_AINC None 0 i c ps j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite Y1 in HC1; exact HC1). subst cr1.
        assert (FZ : forall n, (n <? 48)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
        assert (W33 : bv_unsigned (ev E' 33) = len) by (rewrite (FZ 33%nat eq_refl); exact U33).
        assert (W34 : bv_unsigned (ev E' 34) = cap) by (rewrite (FZ 34%nat eq_refl); exact U34).
        assert (W36 : bv_unsigned (ev E' 36) = she) by (rewrite (FZ 36%nat eq_refl); exact U36).
        assert (CELL : forall X0, VPA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] G.BLS VPA.FFS Cred 4 i E A1 M' m' HA') as Hoff.
        pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
        unfold VPA.vec_cells in Y9. apply andb_prop in Y9 as [Y9 Yc]. apply andb_prop in Y9 as [Ya Yb]. unfold VPA.oE, VPA.bE, VPA.lnE, VPA.capE in *.

        assert (LT : len + 1 <= cap).
        { pose proof (CBA.has_range_sound (hl_segs L) E' _ _ _ _ _ (proj1 (Forall_forall _ _) HK) Y10) as KR. destruct (CL5A.lin_val E' (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 33)) (EVar 34))) as [q Hq].
          assert (LV : lden E' (lin_of (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 33)) (EVar 34))) = cap - len) by (lin_eval; rw_atoms; clear; lia).
          unfold CL5A.uv in Hq. rewrite LV in Hq. clear - KR Hq Hlen Hcap. lia. }
        eexists. eexists. split; [exact (AINC_OK ((b, cap) :: lb_remove b LB) FF LK1 cr A1 o b len cap 1 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
        {
          unfold PMSA.a0, PMSA.a1, PMSA.vec_at, PMSA.u64, PMSA.ainfr.
          split; [replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y7); cbn [edenot]; rewrite (FZ 10%nat eq_refl); exact V10|].
          split; [replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 11 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y8); reflexivity|].
          split.
          { split; [|split]; apply (CL5A.u64_full (hl_segs L) _ Hoff).
            - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Ya) ltac:(ev_start)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W32 in G0. exact G0.
            - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yb) ltac:(ev_start)) as G0.
              replace (CL5A.uv E' (APC.eadd (EVar 32) (EVar 33))) with (b + len) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia].
            - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc) ltac:(ev_start)) as G0.
              replace (CL5A.uv E' (APC.eadd (EVar 32) (EVar 34))) with (b + cap) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia]. }
          split; [exact Hofr|]. split; [exact Ho8|]. split.
          { apply (CL5A.shadow_zero_same M M' o 3); [|exact Hosh]. intros jj Hj. apply Hfr1. apply (KSH o 24); [left; exact Hofr | clear; lia |].
            apply (CL5A.shreg_in_shadow o 3); [exact Ho8 | clear; lia | unfold S; clear - Hj; lia]. }
          split; [left; reflexivity|]. split; [clear - Hlen; lia|]. split; [clear; lia|]. split; [exact LT|]. split; [|clear - B0 Hcap; lia].
          apply (CL5A.shadow_cont_same M1 M' b cap len ltac:(clear - Hlen; lia) (CHA.mod8_of_16 _ B16)); [|exact HXi']. intros a Ha.
          pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
          refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] [(o, 24)] G.BLS VPA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                    i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil; exact Y3|].
          rewrite FFSnil, Y4. replace (CH2.den E [(EVar 32, EVar 34)]) with [(b, cap)]; [exact (NOFOOT a SRa)|].
          unfold CH2.den. cbn [map fst snd edenot]. rewrite <- (proj1 HagE 32%nat), <- (proj1 HagE 34%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U32, U34. reflexivity. }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Hsc2 & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (HagE2 : env_agree GT.NF E0 E2).
          { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
          assert (FZ2 : forall n, (n <? 48)%nat = true -> ev E2 n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE2); apply Nat.ltb_lt; exact Hn).
          assert (DEN' : CH2.den E' [(EVar 32, EVar 34)] = [(b, cap)]) by (unfold CH2.den; cbn [map fst snd edenot]; rewrite W32, W34; reflexivity).
          assert (DEN2 : CH2.den E2 [(EVar 32, EVar 34)] = [(b, cap)]).
          { unfold CH2.den. cbn [map fst snd edenot]. rewrite (FZ2 32%nat eq_refl), (FZ2 34%nat eq_refl), U32, U34. reflexivity. }
          split; [rewrite Y4, DEN'; apply incl_refl|]. split.
          { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (CHA.SRL3 (EVar 32), VPA.SBz, CHA.SRL3 (APC.eaddz (EVar 34) 7)). split; [left; reflexivity|].
            unfold CHA.in_reg. rewrite CL5A.estart_srl3. unfold elenZ. rewrite CHA.u_srl3. unfold CL5A.uv. cbn [edenot]. rewrite W32.
            replace (bv_unsigned (edenot E' (APC.eaddz (EVar 34) 7))) with (cap + 7) by (symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia]).
            unfold S, SB, VPA.SBz in *. exact Hin. }
          split.
          { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
            refine (CHA.obj_not_client L ar LYI (lb_remove b LB) FF sp (CH.hd_scr G.HDECL) b cap a RFr _ B3 (CHA.mod8_of_16 _ B16) B4 (or_intror B1') Bap _ (or_intror _) Kc).
            - unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - B0 B7 BHI. lia.
            - intros f Hf. apply Bfap. apply in_or_app. left. exact Hf.
            - exact (CL5A.blk_shadow_in b cap a (CHA.mod8_of_16 _ B16) B3 Hin). }
          split; [unfold CHA.curB; rewrite Y5, DEN2; exact HH2|].
          split; [unfold Cred; rewrite Y2; reflexivity|].
          split; [unfold XI; rewrite Y2; split; [clear - LT; lia | exact Hsc2]|].
          intros X0 HX0 _. unfold VPA.NEWS_AINC, VPA.STAT in HX0. cbn [app In] in HX0. destruct HX0 as [<-|[<-|[<-|[]]]].
          - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
          - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
          - apply (CL5A.shbyte_intro (hl_segs L) E2 _ (APC.eadd (EVar 32) (EVar 33)) (EVar 36) (b + len) she).
            + apply CL5.u_lin; [lin_eval; rewrite (FZ2 32%nat eq_refl), (FZ2 33%nat eq_refl), U32, U33; clear; lia | clear - B0 B7 Hlen Hcap; lia].
            + cbn [edenot]. rewrite (FZ2 36%nat eq_refl). exact V36.
            + clear - SHE. lia.
            + clear - B0 B7 Hlen Hcap LT. lia.
            + assert (INS : in_shadow_of b cap (S (b + len))).
              { apply (CL5A.blk_shadow_in b cap _ (CHA.mod8_of_16 _ B16) B3). rewrite (CL5A.S_add_al b len (CHA.mod8_of_16 _ B16)).
                pose proof (Z.div_le_mono len (cap - 1) 8 ltac:(clear; lia) ltac:(clear - LT; lia)) as DL.
                assert (E1 : (cap - 1) / 8 = (cap + 7) / 8 - 1).
                { pose proof (Z.div_mod (cap + 7) 8 ltac:(clear; lia)) as D7. pose proof (Z.mod_pos_bound (cap + 7) 8 ltac:(clear; lia)) as R7.
                  symmetry. apply (Zdiv_unique _ 8 _ ((cap + 7) mod 8)); clear - D7 R7; lia. }
                pose proof (Z.div_pos len 8 ltac:(clear - Hlen; lia) ltac:(clear; lia)) as DP. clear - DL E1 DP. lia. }
              pose proof (SHR b cap _ ltac:(clear - B0; lia) B3 B7 INS) as SRa.
              apply CL5A.byte_vis.
              * apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 (S (b + len)) HH2).
                -- clear - SRa. lia.
                -- do 6 right. exists (b, cap). split; [left; reflexivity | exact INS].
                -- apply (CL5A.not_stk_shadow_sh L ar ((b, cap) :: lb_remove b LB) FF b cap); [exact (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2)) | clear - B0; lia | exact B3 | exact B4 | exact INS].
              * rewrite (CL5A.S_add_al b len (CHA.mod8_of_16 _ B16)). unfold eqz in Eshe. rewrite Eshe. exact (cont_end_byte M2 b cap len ltac:(clear - Hlen; lia) Hsc2). } }
      destruct (Z.eqb_spec pc VPA.PC_SLOW) as [->|Hne2].
      {
        destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
        apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y9]. apply andb_prop in X as [X Y8]. apply andb_prop in X as [X Y7]. apply andb_prop in X as [X Y6].
        apply andb_prop in X as [X Yblob]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Ynx].
        apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0, Y1, Y2. apply CH2.blocks_eqb_eq in Y4, Y5. apply Nat.eqb_eq in Ynx.
        lazymatch type of Y6 with VPA.isSome ?t = true => destruct t as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        assert (HXi' : shadow_cont M1 b cap len) by (unfold XI in HXi; rewrite Y1 in HXi; exact HXi).
        assert (HcB : CHA.curB (lb_remove b LB) G.BLS i E = (b, cap) :: lb_remove b LB).
        { unfold CHA.curB. rewrite Y4. unfold CH2.den. cbn [map fst snd VPA.bE VPA.capE edenot app]. rewrite <- (proj1 HagE 32%nat), <- (proj1 HagE 34%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U32, U34. reflexivity. }
        assert (HcF : CHA.curF FF sp VPA.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE VPA.PC_SLOW 8192 3%nat [] [(VPA.oE, 0, ELit 24)] VPA.NEWS_SLOW (Some (APC.eadd (EVar 48) (EVar 50))) 4 i c ps j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite Y1 in HC1; exact HC1). subst cr1.
        assert (NX : CH2.ci_nx ci = 48%nat) by (destruct HV as (_ & _ & _ & _ & HV5); rewrite Ynx in HV5; unfold APC.NCS in HV5; clear - HV5; lia).
        assert (FZ : forall n, (n <? 48)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
        assert (W33 : bv_unsigned (ev E' 33) = len) by (rewrite (FZ 33%nat eq_refl); exact U33).
        assert (W34 : bv_unsigned (ev E' 34) = cap) by (rewrite (FZ 34%nat eq_refl); exact U34).
        assert (CELL : forall X0, VPA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] G.BLS VPA.FFS Cred 4 i E A1 M' m' HA') as Hoff.
        pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
        unfold VPA.vec_cells in Y9. apply andb_prop in Y9 as [Y9 Yc]. apply andb_prop in Y9 as [Ya Yb]. unfold VPA.oE, VPA.xaE, VPA.bE, VPA.lnE, VPA.capE in *.

        assert (EQ : len = cap).
        { pose proof (CBA.has_range_sound (hl_segs L) E' _ _ _ _ _ (proj1 (Forall_forall _ _) HK) Y10) as KR. destruct (CL5A.lin_val E' (EAlu Instr.ALU_ADD (EVar 33) (EMd Instr.M_MUL (ELit (-1)) (EVar 34)))) as [q Hq].
          assert (LV : lden E' (lin_of (EAlu Instr.ALU_ADD (EVar 33) (EMd Instr.M_MUL (ELit (-1)) (EVar 34)))) = len - cap) by (lin_eval; rw_atoms; clear; lia).
          unfold CL5A.uv in Hq. rewrite LV in Hq. clear - KR Hq Hlen Hcap. lia. }
        assert (LBR : lb_remove b ((b, cap) :: lb_remove b LB) = lb_remove b LB) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
        eexists. eexists. split; [exact (SLOW_OK ((b, cap) :: lb_remove b LB) FF LK1 cr A1 o b cap xa x (sp + CH2.ci_csp ci) (CC.cp_pc cj) st)|]. split.
        {
          unfold PMSA.a0, PMSA.a1, PMSA.vec_ok, PMSA.vec_at, PMSA.u64, PMSA.u8, PMSA.ainfr.
          split; [replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 10 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y7); cbn [edenot]; rewrite (FZ 10%nat eq_refl); exact V10|].
          split; [replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity);
                  rewrite (CL.ps_reg_is_sound (hl_segs L) c ps E' R' _ _ 11 _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Y8); cbn [edenot]; rewrite (FZ 11%nat eq_refl); exact V11|].
          split.
          { split.
            { split; [|split]; apply (CL5A.u64_full (hl_segs L) _ Hoff).
              - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Ya) ltac:(ev_start)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W32 in G0. exact G0.
              - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yb) ltac:(ev_start)) as G0.
                replace (CL5A.uv E' (APC.eadd (EVar 32) (EVar 33))) with (b + cap) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear - EQ; lia | clear - B0 B7 Hlen Hcap; lia].
              - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc) ltac:(ev_start)) as G0.
                replace (CL5A.uv E' (APC.eadd (EVar 32) (EVar 34))) with (b + cap) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia]. }
            split; [exact Hofr|]. split; [exact Ho8|]. split.
            { apply (CL5A.shadow_zero_same M M' o 3); [|exact Hosh]. intros jj Hj. apply Hfr1. apply (KSH o 24); [left; exact Hofr | clear; lia |].
              apply (CL5A.shreg_in_shadow o 3); [exact Ho8 | clear; lia | unfold S; clear - Hj; lia]. }
            split; [left; reflexivity|]. split; [clear - Hcap; lia|]. split; [exact Hcap|].
            rewrite <- EQ at 2. apply (CL5A.shadow_cont_same M1 M' b cap len ltac:(clear - Hlen; lia) (CHA.mod8_of_16 _ B16)); [|exact HXi']. intros a Ha.
            pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
            refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] [(o, 24)] G.BLS VPA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                      i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil; exact Y3|].
            rewrite FFSnil, Y4. replace (CH2.den E [(EVar 32, EVar 34)]) with [(b, cap)]; [exact (NOFOOT a SRa)|].
            unfold CH2.den. cbn [map fst snd edenot]. rewrite <- (proj1 HagE 32%nat), <- (proj1 HagE 34%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U32, U34. reflexivity. }
          split; [exact EQ|]. split.
          { apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat b st (CELL _ Yblob) ltac:(ev_start) _)). rewrite <- (proj2 HagE'). reflexivity. }
          split; [apply (CL5A.u8_same (hl_segs L) M M' xa x ltac:(clear - X3; lia) ltac:(clear - X6; lia) (Hfr1 xa KXA) Hx)|].
          split; [unfold PMSA.acobj; destruct Hxfr as [Hx1|[Hx1 Hx2]]; [left; exact Hx1 | right; split; [clear - Hx1 Hc1; lia | exact Hx2]]|]. split.
          { intros a Ha. assert (a = xa) by (clear - Ha; lia). subst a.
            assert (BX : byte_at M' (S xa) shv) by (unfold byte_at; rewrite (Hfr1 _ (KSH xa 1 (S xa) Hxfr ltac:(clear; lia) (CL5A.shreg1_in_shadow xa _ eq_refl))); exact Hshv).
            unfold hid in Hshr. destruct Hshr as [->|[Hr Hl]]; [left; exact BX | right; exists shv; split; [exact BX | split; [exact Hr | exact Hl]]]. }
          split; [unfold hid in Hxo; exact Hxo|]. destruct (Hcred EQ) as (QC1 & QC2 & QC4). split; [exact QC1|]. split; [exact QC2|]. split; [|exact QC4].

          unfold PMSA.stksh, PMSA.VSLOW_SCR. unfold PMSA.stksh, PMSA.VPUSH_SCR, PMSA.VSLOW_SCR in Hstksh.
          apply (PTA.stksh_mono ar M' sp (48 + 8192) (sp + CH2.ci_csp ci) 8192); [| exact AL8240 | | clear - Hc2 SCRV; rewrite SCRV in Hc2; lia].
          - apply (PTA.stksh_ag ar M M' sp (48 + 8192)); [|exact Hstksh]. intros a Ha. exact (Hfr1 a (KSTK a Ha)).
          - destruct HSTK as (T1 & _). clear - T1. pose proof (Z_div_mod_eq_full (sp + CH2.ci_csp ci) 16) as D. rewrite T1, Z.add_0_r in D. rewrite D.
            replace (16 * ((sp + CH2.ci_csp ci) / 16) - 8192) with ((2 * ((sp + CH2.ci_csp ci) / 16) - 1024) * 8) by lia. apply Z_mod_mult. }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (b' & Ha0' & (Hv0 & Hv8 & Hv16) & Hbytes' & Hfresh' & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          rewrite LBR in *. pose proof Hfresh' as ((Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)) & Qap & Qfap & Qdef & Qsh).
          exists [Z_to_bv 64 b'; Z_to_bv 64 (2 * cap); Z_to_bv 64 (cap + 1)]. split; [reflexivity|]. cbv zeta. rewrite NX.
          pose proof (CH2.retEx_agree E' 48 [Z_to_bv 64 b'; Z_to_bv 64 (2 * cap); Z_to_bv 64 (cap + 1)] R2) as Hag2.
          pose proof (CH2.retEx_ghost E' 48 [Z_to_bv 64 b'; Z_to_bv 64 (2 * cap); Z_to_bv 64 (cap + 1)] R2 0 ltac:(cbn; clear; lia)) as G48.
          pose proof (CH2.retEx_ghost E' 48 [Z_to_bv 64 b'; Z_to_bv 64 (2 * cap); Z_to_bv 64 (cap + 1)] R2 1 ltac:(cbn; clear; lia)) as G49.
          pose proof (CH2.retEx_ghost E' 48 [Z_to_bv 64 b'; Z_to_bv 64 (2 * cap); Z_to_bv 64 (cap + 1)] R2 2 ltac:(cbn; clear; lia)) as G50.
          set (E2 := CH2.retEx E' 48 [Z_to_bv 64 b'; Z_to_bv 64 (2 * cap); Z_to_bv 64 (cap + 1)] R2) in *. cbn [nth Nat.add] in G48, G49, G50.
          assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | exact Hag2]).
          assert (FZ2 : forall n, (n <? 48)%nat = true -> ev E2 n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE2); apply Nat.ltb_lt; exact Hn).
          assert (T48 : bv_unsigned (ev E2 48) = b') by (rewrite G48; apply u64_of_Z; clear - Q0 Q3 Q4 CL SP1 Hcap; lia).
          assert (T49 : bv_unsigned (ev E2 49) = 2 * cap) by (rewrite G49; apply u64_of_Z; clear - Hcap; lia).
          assert (T50 : bv_unsigned (ev E2 50) = cap + 1) by (rewrite G50; apply u64_of_Z; clear - Hcap; lia).
          assert (T10 : bv_unsigned (ev E2 10) = o) by (rewrite (FZ2 10%nat eq_refl); exact U10).
          split.
          { unfold PMSA.a0 in Ha0'. rewrite Ha0'. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E2 _)). f_equal. symmetry.
            apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q3 Q4 CL SP1 Hcap; lia]. }
          split; [cbn [CH2.den map app]; apply incl_refl|]. split.
          { intros w a [<-|[]] Hin. exists (EVar 10, 0, ELit 24). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite W10.
            rewrite u64_of_Z by (clear; lia). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin. lia. }
          split; [intros w a [<-|[]] Hin (_ & _ & Ko); exact (Ko (o, 24) (or_introl eq_refl) Hin)|].
          split.
          { unfold CHA.curB. rewrite Y5. unfold CH2.den. cbn [map fst snd edenot app]. rewrite T48, T49. exact HH2. }
          split; [unfold Cred; rewrite Y2; reflexivity|].
          split.
          { unfold XI. rewrite Y2. unfold SLOWP. split; [exact EQ|]. exists b'. unfold CL5A.uv. cbn [edenot]. repeat (split; [assumption|]). exact Hfresh'. }
          intros X0 HX0 _. unfold VPA.NEWS_SLOW, VPA.STAT, VPA.oE in HX0. cbn [app In] in HX0.
          assert (VISO : CL5A.visr (ahid A2 m2) o 24).
          { intros k Hk. apply (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ m2 sp 0 (o + k) HH2); [clear - Hk O3 O6; lia | |].
            - exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar _ FF sp 0 o 24 (o + k) Hofr ltac:(clear - Hk; lia))).
            - apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in O5. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hk O5. lia. }
          destruct HX0 as [<-|[<-|[<-|[<-|[]]]]].
          - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
          - apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2). reflexivity.
          - eapply CL5.kword64_intro with (A := o) (z := b'); [ev_start | clear - O3; lia | clear - O6; lia | cbn [edenot]; exact G48 |].
            apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 8 VISO ltac:(clear; lia) ltac:(clear; lia)) | exact Hv0].
          - eapply CL5.kword64_intro with (A := o + 16) (z := b' + 2 * cap); [ev_start | clear - O3; lia | clear - O6; lia | |].
            + rewrite <- (Z_to_bv_bv_unsigned _ (edenot E2 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q3 Q4 CL SP1 Hcap; lia].
            + apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 16) 8 VISO ltac:(clear; lia) ltac:(clear; lia)) | exact Hv16]. } }

      apply andb_prop in X as [X Ypat]. apply andb_prop in X as [Xbase Xfoot].
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] [(o, 24)] G.BLS VPA.FFS Cred 4 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok VPA.RETPC i c ps _ Xbase _ (FFSnil i) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
        [rewrite LS; exact VPA.ret_at | rewrite FFSnil; exact Xfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      assert (FZ : forall n, (n <? 48)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
      assert (W10 : bv_unsigned (ev E' 10) = o) by (rewrite (FZ 10%nat eq_refl); exact U10).
      assert (W32 : bv_unsigned (ev E' 32) = b) by (rewrite (FZ 32%nat eq_refl); exact U32).
      assert (W33 : bv_unsigned (ev E' 33) = len) by (rewrite (FZ 33%nat eq_refl); exact U33).
      assert (W34 : bv_unsigned (ev E' 34) = cap) by (rewrite (FZ 34%nat eq_refl); exact U34).
      assert (W37 : bv_unsigned (ev E' 37) = xm) by (rewrite (FZ 37%nat eq_refl); exact U37).
      assert (CELL : forall X0, VPA.has (SR.ps_cells ps) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] G.BLS VPA.FFS Cred 4 i E A1 M' m' HA') as Hoff.
      unfold VPA.oE, VPA.bE, VPA.lnE, VPA.capE, VPA.xvE in Ypat.
      destruct (Z.eqb (VPA.kind i) VPA.PC_AINC) eqn:Hk1.
      {
        apply Z.eqb_eq in Hk1. apply andb_prop in Ypat as [Ypat Ye]. apply andb_prop in Ypat as [Ypat Yd]. apply andb_prop in Ypat as [Ypat Yc]. apply andb_prop in Ypat as [Ypat Yb].
        apply andb_prop in Ypat as [Ybl Ya]. apply CH2.blocks_eqb_eq in Ybl.
        assert (HXi' : len < cap /\ shadow_cont M1 b cap (len + 1)) by (unfold XI in HXi; rewrite Hk1 in HXi; exact HXi). destruct HXi' as [LT HSC].
        assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite Hk1 in HC1; exact HC1). subst cr1.
        assert (DENE : CH2.den E [(EVar 32, EVar 34)] = [(b, cap)]).
        { unfold CH2.den. cbn [map fst snd edenot]. rewrite <- (proj1 HagE 32%nat), <- (proj1 HagE 34%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U32, U34. reflexivity. }
        unfold CHA.curB in HH1. rewrite Ybl, DENE in HH1. cbn [app] in HH1.
        apply (Hcont fx' R' M' model2 LB cr (lb_remove b LB) [(o, 24)] LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact (CBA.own_back L ar C HI HIok _ _ _ _ _ _ _ b cap HH1 HinLB ND1)].
        split; [reflexivity|]. split; [reflexivity|]. left. fold len. split; [exact LT|]. split.
        { unfold PMSA.vec_at, PMSA.u64. split; [|split]; apply (CL5A.u64_full (hl_segs L) _ Hoff).
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Ya) ltac:(ev_start)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W32 in G0. exact G0.
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yb) ltac:(ev_start)) as G0.
            replace (CL5A.uv E' (EAlu Instr.ALU_ADD (APC.eadd (EVar 32) (EVar 33)) (ELit 1))) with (b + (len + 1)) in G0; [exact G0|].
            symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia].
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc) ltac:(ev_start)) as G0.
            replace (CL5A.uv E' (APC.eadd (EVar 32) (EVar 34))) with (b + cap) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia]. }
        split.
        { apply (CL5.bytes_at_app (hl_segs L)).
          - apply (CL5A.bytes_full (hl_segs L) _ Hoff). refine (proj1 (CL5.kblob_elim (hl_segs L) E' _ _ _ 0%nat b st (CELL _ Yd) ltac:(ev_start) _)). rewrite <- (proj2 HagE'). reflexivity.
          - intros k Hk. cbn [length] in Hk. assert (k = 0%nat) by (clear - Hk; lia). subst k. cbn [nth]. rewrite Z.add_0_r. fold len.
            pose proof (CL5A.kword8_elim (hl_segs L) E' _ _ _ (b + len) (CELL _ Ye)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W37 in G0.
            apply (CL5A.u8_full (hl_segs L) _ Hoff) in G0; [|rewrite (CL5.estart_lin E' _ 0 (b + len)); [clear; lia | lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia]].
            unfold L5.u8_at in *. unfold eqz in Exm. rewrite Exm, byte_mod in G0. exact G0. }
        split; [|split; reflexivity].
        apply (CL5A.shadow_cont_same M1 M' b cap (len + 1) ltac:(clear - Hlen LT; lia) (CHA.mod8_of_16 _ B16)); [|exact HSC]. intros a Ha.
        pose proof (SHR b cap a ltac:(clear - B0; lia) B3 B7 Ha) as SRa.
        refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A (lb_remove b LB) FF LK sp G.HDECL [(o, 24)] [(o, 24)] G.BLS VPA.FFS Cred 4 STKF SCRP NF32 U2 WRS_OK
                  i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil; exact Xfoot|].
        rewrite FFSnil, Ybl, DENE. exact (NOFOOT a SRa). }
      destruct (Z.eqb (VPA.kind i) VPA.PC_SLOW) eqn:Hk2; [|discriminate].
      {
        apply Z.eqb_eq in Hk2. apply andb_prop in Ypat as [Ypat Yc]. apply andb_prop in Ypat as [Ypat Yb]. apply andb_prop in Ypat as [Ypat Ya]. apply andb_prop in Ypat as [Ypat YF].
        apply andb_prop in Ypat as [Ybl Ynx]. apply CH2.blocks_eqb_eq in Ybl. apply CBA.regions_eqb_eq in YF. apply Nat.ltb_lt in Ynx.
        assert (HXi' : SLOWP E M1) by (unfold XI in HXi; rewrite Hk2 in HXi; exact HXi). destruct HXi' as (EQ & b' & G48 & G49 & G50 & Hbytes' & Hfresh').
        assert (Hcr1 : cr1 = adebit L cr (2 * cap)) by (unfold Cred in HC1; rewrite Hk2 in HC1; exact HC1). subst cr1.
        pose proof Hfresh' as ((Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)) & Qap & Qfap & Qdef & Qsh).
        assert (T48 : bv_unsigned (ev E' 48) = b') by (rewrite <- (proj1 Hag 48%nat) by (clear - Ynx; lia); exact G48).
        assert (T49 : bv_unsigned (ev E' 49) = 2 * cap) by (rewrite <- (proj1 Hag 49%nat) by (clear - Ynx; lia); exact G49).
        assert (T50 : bv_unsigned (ev E' 50) = cap + 1) by (rewrite <- (proj1 Hag 50%nat) by (clear - Ynx; lia); exact G50).
        unfold CHA.curB in HH1. rewrite Ybl in HH1. unfold CH2.den in HH1. cbn [map fst snd edenot app] in HH1. unfold CL5A.uv in G48, G49. cbn [edenot] in G48, G49. rewrite G48, G49 in HH1.

        assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 8240 <= a < sp) -> ~ (o <= a < o + 24) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros a Ha N1 N2. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF). rewrite YF. unfold SGP.outside. rewrite L5.unsigned_lit by exact Ha.
          constructor; [|constructor; [|constructor]]; unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite ?W10, ?(FZ 2%nat eq_refl), ?U2; rewrite u64_of_Z by (clear; lia); clear - N1 N2; lia. }
        destruct Hofr as (f & Hf & F1 & F2). pose proof (Qfap f Hf) as QF.
        assert (FRB : forall a, b' <= a < b' + 2 * cap -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros a Ha. apply FR; [clear - Ha Q0 Q4 CL SP1; lia | clear - Ha Q4 S2; lia | clear - Ha QF F1 F2; lia]. }
        assert (FRS : forall a, in_shadow_of b' (2 * cap) a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros a Ha. pose proof (SHR b' (2 * cap) a ltac:(clear - Q0; lia) Q3 Q7 Ha) as SRa. unfold hid in O5. apply FR; [clear - SRa; lia | clear - SRa S2 CL; lia | clear - SRa O5; lia]. }
        apply (Hcont fx' R' M' model2 ((b', 2 * cap) :: lb_remove b LB) (adebit L cr (2 * cap)) (lb_remove b LB) [(o, 24)] LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
        split; [reflexivity|]. split; [reflexivity|]. right. fold len. split; [exact EQ|]. exists b'. split.
        { unfold PMSA.vec_at, PMSA.u64. split; [|split]; apply (CL5A.u64_full (hl_segs L) _ Hoff).
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ o (CELL _ Ya) ltac:(ev_start)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite T48 in G0. exact G0.
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 8) (CELL _ Yb) ltac:(ev_start)) as G0.
            replace (CL5A.uv E' (APC.eadd (EVar 48) (EVar 50))) with (b' + (cap + 1)) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q3 Q4 CL SP1 Hcap; lia].
          - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (o + 16) (CELL _ Yc) ltac:(ev_start)) as G0.
            replace (CL5A.uv E' (APC.eadd (EVar 48) (EVar 49))) with (b' + 2 * cap) in G0; [exact G0|]. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q0 Q3 Q4 CL SP1 Hcap; lia]. }
        split.
        { apply (CL5A.bytes_same (hl_segs L) M1 M' b' (st ++ [x])); [clear - Q0; lia | rewrite length_app; cbn [length]; fold len; clear - Q0 Q3 Q4 CL SP1 EQ Hcap; lia | | exact Hbytes'].
          intros k Hk. apply FRB. rewrite length_app in Hk. cbn [length] in Hk. fold len in Hk. clear - Hk EQ Hcap. lia. }
        split; [|split; reflexivity].
        split; [exact (conj Q0 (conj Q1 (conj Q16 (conj Q3 (conj Q4 (conj Q5 (conj Q6 Q7)))))))|]. split; [exact Qap|]. split; [exact Qfap|]. split.
        - exact (CL5A.defined_same M1 M' b' (2 * cap) FRB Qdef).
        - exact (CL5A.shadow_cont_same M1 M' b' (2 * cap) (cap + 1) ltac:(clear - Hcap; lia) (CHA.mod8_of_16 _ Q16) FRS Qsh). }
    - exact Hc0.
    - exact HAt0.
    -
      assert (Hk0 : VPA.kind i0 = 0) by (do 4 (destruct i0 as [|i0]; [reflexivity|]); lia).
      assert (HB0 : CH2.den E0 (nth i0 G.BLS []) = [(b, cap)]).
      { assert (HBL : nth i0 G.BLS [] = [(VPA.bE, VPA.capE)]) by (do 4 (destruct i0 as [|i0]; [reflexivity|]); lia).
        rewrite HBL. unfold CH2.den. cbn [map fst snd VPA.bE VPA.capE edenot]. rewrite U32, U34. reflexivity. }
      split.
      + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
        split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
        exists cr, LK. unfold CHA.curB, CHA.curF. rewrite HB0, FFSnil. cbn [app CHA.denF map length]. split; [exact (CBA.own_front L ar C HI HIok _ _ _ _ _ _ _ b cap HH HinLB)|].
        split; [apply incl_refl|]. split; [unfold Cred; rewrite Hk0; reflexivity | exact Hroom].
      + unfold XI. rewrite Hk0. exact Hshc.
    - exact Hfp. }

  assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
    by (intros a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hc Hs)).
  assert (VO : CL5A.visr (ahid A model) o 24).
  { intros k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + k) RFx Hofr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VX : CL5A.visr (ahid A model) xa 1).
  { intros k Hk. destruct (CL5A.acobj_wok L ar LB FF sp 0 xa 1 (xa + k) RFx CSP Hxfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VSO : forall j, 0 <= j < 3 -> ahid A model (Z_to_bv 64 (S o + j)) = false).
  { intros j Hj. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 o 24 (S o + j) RFx Hofr ltac:(clear; lia) (CL5A.shreg_in_shadow o 3 (S o + j) Ho8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
    exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VSX : ahid A model (Z_to_bv 64 (S xa)) = false).
  { destruct (CL5A.acobj_sh_wok L ar LB FF sp 0 xa 1 (S xa) RFx CSP Hxfr ltac:(clear; lia) (CL5A.shreg1_in_shadow xa _ eq_refl)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VB : CL5A.visr (ahid A model) b cap).
  { intros k Hk. apply CLV; [clear - Hk B0 B7; lia | left; exists (b, cap); split; [exact HinLB | cbn [fst snd]; clear - Hk; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk BHI. lia. }
  assert (VS : CL5A.visr (ahid A model) (sp - 8240) 8240).
  { intros k Hk. apply CLV; [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
  set (Mv := CCA.vis A model M).
  assert (DO : L5.defined Mv o 24).
  { apply (CL5A.defined_vis _ M o 24 VO). destruct Hofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ WF f Hf) as (_ & _ & _ & _ & Fdef & _).
    intros k Hk. replace (o + k) with (ff_addr f + (o - ff_addr f + k)) by (clear; lia). apply Fdef. clear - Hk F1 F2. lia. }
  assert (DB : L5.defined Mv b cap) by (apply (CL5A.defined_vis _ M b cap VB); exact Bdef).
  assert (DS : L5.defined Mv (sp - 8240) 8240) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (COMMON : Forall (kentry_ok (hl_segs L) E0 Mv) (firstn 36 (CC.cp_know G.cp0))).
  { cbn [firstn CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.kword64_intro with (A := o) (z := b); [ev_start | clear - O3; lia | clear - O6; lia | exact V32 |].
      apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := b + len); [ev_start | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia].
      * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 8) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := b + cap); [ev_start | clear - O3; lia | clear - O6; lia | |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B7 Hlen Hcap; lia].
      * apply (CL5A.u64_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 (o + 16) 8 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hw16].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev_start | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact Ho8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Hosh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5A.kword8_intro with (A := xa) (z := xm); [ev_start | clear - X3; lia | clear - X6; lia | exact V37 | clear - XM; lia |].
      apply (CL5A.u8_vis (hl_segs L)); [clear - X3; lia | clear - X6; lia | exact VX | exact Hxm].
    + eapply CL5.krange_intro with (v := xm); [lin_eval; rw_atoms; clear; lia | clear - XM; lia | clear - XM; lia].
    + eapply CL5.krange_intro with (v := xa); [lin_eval; rw_atoms; clear; lia | clear - X3 X6; lia | unfold hid in X1; clear - X1 X6 FSLO CL; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := xa) (N2 := 1); [reflexivity | reflexivity | ev_start | reflexivity | unfold hid in X5; clear - X5; lia].
    + apply (CL5A.shbyte_intro (hl_segs L) E0 Mv _ _ xa shv); [exact U11 | exact V35 | clear - SHVR; lia | clear - X3 X6; lia | apply CL5A.byte_vis; [exact VSX | exact Hshv]].
    + eapply CL5.kblob_intro with (bs := st) (A := b); [ev_start | unfold elenZ; cbn [edenot]; exact U33 | clear - B0; lia | fold len; clear - B7 Hlen; lia | clear - B0 B7 B3; lia | reflexivity | |].
      * apply (CL5A.bytes_vis (hl_segs L)); [clear - B0; lia | fold len; clear - B7 Hlen; lia | fold len; exact (CL5A.visr_sub _ b cap b len VB ltac:(clear; lia) ltac:(clear - Hlen; lia)) | exact Hbytes].
      * fold len. apply (L5.defined_sub Mv b cap b len DB); [clear; lia | clear - Hlen; lia].
    + eapply CL5.kwr_intro with (A := b) (N := cap); [ev_start | unfold elenZ; cbn [edenot]; exact U34 | clear - B0; lia | clear - B7; lia | clear - B0 B7 B3; lia | exact DB].
    + eapply CL5.krange_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear - BHI B4 B3 SP1; lia].
    + eapply CL5.kalign_intro with (v := b); [lin_eval; rw_atoms; clear; lia | clear - B0 B7 B3; lia | clear; lia | exact B16].
    + eapply CL5.krange_intro with (v := len); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap; lia].
    + eapply CL5.krange_intro with (v := cap - len); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap; lia].
    + eapply CL5.krange_intro with (v := cap); [lin_eval; rw_atoms; clear; lia | clear - Hlen Hcap; lia | clear - Hlen Hcap; lia].
    + eapply CL5.kunk_intro with (A := sp - 8240) (N := 8240); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 8240) (N := 8240); [ev_start | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 8240) (N1 := 8240) (A2 := o) (N2 := 24); [ev_start | reflexivity | ev_start | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 8240) (N1 := 8240) (A2 := xa) (N2 := 1); [ev_start | reflexivity | ev_start | reflexivity | unfold hid in X4; clear - X4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 8240) (N1 := 8240) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U34 | clear - B4 S2; lia].
    + destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF.
      eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U34 | clear - QF F1 F2; lia].
    + eapply CL5.kdisj_intro with (A1 := xa) (N1 := 1) (A2 := b) (N2 := cap); [ev_start | reflexivity | ev_start | unfold elenZ; cbn [edenot]; exact U34 |].
      destruct Hxfr as [(f & Hf & F1 & F2)|(XS1 & XS2)]; [pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF; clear - QF F1 F2; lia | clear - XS1 B4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := xa) (N2 := 1); [ev_start | reflexivity | ev_start | reflexivity | unfold hid in Hxo; clear - Hxo; lia].
    + destruct Hofr as (f & Hf & F1 & F2). pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _).
      eapply CL5.kdisj_intro with (A1 := o / 8 + SB) (N1 := 3) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U10; reflexivity | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      pose proof (CL5A.gran_blk cap ltac:(clear - Hcap; lia)) as GB. destruct QF as [QF|QF].
      * right. pose proof (CL5A.gran_le b ((cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) o ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
      * left. pose proof (CL5A.gran_le o 3 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ b QF) as G2. clear - G1 G2. lia.
    + eapply CL5.kdisj_intro with (A1 := xa / 8 + SB) (N1 := 1) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U11; reflexivity | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      pose proof (CL5A.gran_blk cap ltac:(clear - Hcap; lia)) as GB.
      destruct Hxfr as [(f & Hf & F1 & F2)|(XS1 & XS2)];
        [|right; pose proof (CL5A.gran_le b ((cap + 7) / 8) (ahl_ceil ar) C8 ltac:(clear - B4 GB; lia)) as G1; pose proof (CL5A.div8_le (ahl_ceil ar) xa ltac:(clear - XS1 S2; lia)) as G2; clear - G1 G2; lia].
      pose proof (Bfap f (in_or_app _ _ _ (or_introl Hf))) as QF. destruct (CHA.frm_align L ar LB FF LK cr A M f WF Hf) as (FA & FB & _). destruct QF as [QF|QF].
      * right. pose proof (CL5A.gran_le b ((cap + 7) / 8) (ff_addr f) (CHA.mod8_of_64 _ FA) ltac:(clear - QF GB; lia)) as G1. pose proof (CL5A.div8_le (ff_addr f) xa ltac:(clear - F1; lia)) as G2. clear - G1 G2. lia.
      * left. pose proof (CL5A.gran_le xa 1 (ff_addr f + ff_bytes (ff_class f)) (CL5A.al64_add8 _ _ FA FB) ltac:(clear - F2; lia)) as G1. pose proof (CL5A.div8_le _ b QF) as G2. clear - G1 G2. lia.
    + destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G1 & G2).
      eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [ev_start | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold hid in O5. unfold SB in *. clear - O5 G1 G2. lia.
    + destruct (CL5A.shreg_bounds b cap ltac:(clear - B0; lia) ltac:(clear - Hcap; lia) B7 (CHA.mod8_of_16 _ B16)) as (G1 & G2).
      eapply CL5.kdisj_intro with (A1 := xa) (N1 := 1) (A2 := b / 8 + SB) (N2 := (cap + 7) / 8);
        [ev_start | reflexivity | rewrite CL5A.estart_srl3'; unfold CL5A.uv; cbn [edenot]; rewrite U32; reflexivity
        | rewrite CL5A.elen_srl3'; f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Hcap; lia] |].
      unfold hid in X5. unfold SB in *. clear - X5 G1 G2. lia. }

  assert (HAND : forall e v, bv_unsigned (edenot E0 e) = v -> bv_unsigned (edenot E0 (EAlu Instr.ALU_AND e (ELit 7))) = v mod 8) by (intros e v <-; apply CL5A.u_and7).
  assert (CX0 : shv = 0 -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 35) 0 0)) by (intros Hz; eapply CL5.krange_intro with (v := shv); [lin_eval; rw_atoms; clear; lia | clear - SHVR; lia | clear - Hz; lia]).
  assert (CX1 : 1 <= shv <= 7 -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 35) 1 7)) by (intros Hz; eapply CL5.krange_intro with (v := shv); [lin_eval; rw_atoms; clear; lia | clear - SHVR; lia | clear - Hz; lia]).
  assert (CX2 : 1 <= shv <= 7 -> ltm xa 8 shv -> kentry_ok (hl_segs L) E0 Mv (KRange (EAlu Instr.ALU_ADD (EVar 35) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EVar 11) (ELit 7)))) 1 7)).
  { intros Hz Hl. unfold ltm in Hl. pose proof (Z.mod_pos_bound xa 8 ltac:(clear; lia)) as MB.
    eapply CL5.krange_intro with (v := shv - xa mod 8); [lin_form; rewrite (HAND (EVar 11) xa U11); cbn [edenot]; rw_atoms; clear; lia | clear - Hz Hl MB; lia | clear - Hz Hl MB; lia]. }
  assert (CE0 : she = 0 -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 36) 0 0)) by (intros Hz; eapply CL5.krange_intro with (v := she); [lin_eval; rw_atoms; clear; lia | clear - SHE; lia | clear - Hz; lia]).
  assert (CE1 : she <> 0 -> kentry_ok (hl_segs L) E0 Mv (KRange (EVar 36) 1 7)) by (intros Hz; eapply CL5.krange_intro with (v := she); [lin_eval; rw_atoms; clear; lia | clear - SHE; lia | clear - Hz SHE; lia]).
  assert (CE2 : she <> 0 -> kentry_ok (hl_segs L) E0 Mv (KRange (EAlu Instr.ALU_ADD (EVar 36) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EVar 33) (ELit 7)))) 1 7)).
  { intros Hz. unfold eqz in Eshe. assert (G : she - len mod 8 = 1) by (clear - Hz Eshe Hlen; subst she; lia).
    eapply CL5.krange_intro with (v := she - len mod 8); [lin_form; rewrite (HAND (EVar 33) len U33); cbn [edenot]; rw_atoms; clear; lia | clear - G; lia | clear - G; lia]. }
  assert (ATI : forall c tl, firstn 36 (CC.cp_know c) = firstn 36 (CC.cp_know G.cp0) -> skipn 36 (CC.cp_know c) = tl -> CC.cp_regs c = CC.cp_regs G.cp0 ->
            Forall (kentry_ok (hl_segs L) E0 Mv) tl -> CCA.AtV (hl_segs L) c E0 R A M model).
  { intros c tl H1 H2 H3 HT. split; [rewrite H3; exact (regs_ok_id R _ _)|]. unfold know_ok. rewrite <- (firstn_skipn 36 (CC.cp_know c)), H1, H2. apply Forall_app. split; [exact COMMON | exact HT]. }
  unfold hid in Hshr. destruct Hshr as [Hs0|[Hs1 Hs2]]; destruct (Z.eq_dec she 0) as [He0|He1].
  - apply (MAIN 0%nat G.cp0 eq_refl ltac:(clear; lia) eq_refl). apply (ATI G.cp0 [_; _] eq_refl eq_refl eq_refl). apply Forall_cons; [exact (CX0 Hs0) | apply Forall_cons; [exact (CE0 He0) | apply Forall_nil]].
  - apply (MAIN 1%nat G.cp1 eq_refl ltac:(clear; lia) eq_refl). apply (ATI G.cp1 [_; _; _] eq_refl eq_refl eq_refl). apply Forall_cons; [exact (CX0 Hs0) | apply Forall_cons; [exact (CE1 He1) | apply Forall_cons; [exact (CE2 He1) | apply Forall_nil]]].
  - apply (MAIN 2%nat G.cp2 eq_refl ltac:(clear; lia) eq_refl). apply (ATI G.cp2 [_; _; _] eq_refl eq_refl eq_refl). apply Forall_cons; [exact (CX1 Hs1) | apply Forall_cons; [exact (CX2 Hs1 Hs2) | apply Forall_cons; [exact (CE0 He0) | apply Forall_nil]]].
  - apply (MAIN 3%nat G.cp3 eq_refl ltac:(clear; lia) eq_refl). apply (ATI G.cp3 [_; _; _; _] eq_refl eq_refl eq_refl). apply Forall_cons; [exact (CX1 Hs1) | apply Forall_cons; [exact (CX2 Hs1 Hs2) | apply Forall_cons; [exact (CE1 He1) | apply Forall_cons; [exact (CE2 He1) | apply Forall_nil]]]].
Qed.
End VecPushOk.

