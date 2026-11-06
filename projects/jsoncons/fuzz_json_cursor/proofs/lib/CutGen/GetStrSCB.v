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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmCurDefs PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCB GetSpecCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_getstr_cboth_T Cut_getstr_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_getstr_cboth.
Module GT := Cut_getstr_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module GSC.
Definition PC_STRINIT : Z := 849628.
Definition RETPC : Z := 842596.
Definition SBz : Z := 2147450880.
Definition oE := EVar 10.

Definition chain (i : nat) : nat := (i mod 4)%nat.
Definition stage (i : nat) : nat := (i / 4)%nat.
Definition long (ch : nat) : bool := Nat.odd ch.
Definition FLG (ch : nat) : Z := match ch with 0%nat | 1%nat => 1 | _ => 4097 end.
Definition NLO (ch : nat) : Z := if long ch then 23 else 0.
Definition NHI (ch : nat) : Z := if long ch then 67108863 else 22.
Definition BLR (ch : nat) : CA.blocks := if long ch then [(EVar 40, EVar 41)] else [].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].
Definition FST : list SGP.region := [(EVar 2, -14384, ELit 14384)].
Definition has := CC.has_cell.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (Nat.eqb (chain j) (chain i) && Nat.eqb (stage j) 1 && Nat.eqb (stage i) 0 && Nat.ltb i 8 && Nat.ltb j 8 &&
               CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) (BLR (chain i)) && CHA.foot_chk GT.NF G.HDECL c [] [] && CBA.regions_eqb (CC.cp_F c) FST &&
               Z.eqb pc PC_STRINIT && Z.eqb (SR.ps_pc ps) PC_STRINIT
               && match CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4176 2 [] [] [(oE, 0, ELit 24)] STAT None c ps cj [] [] (BLR (chain i)) [] with
                  | Some ci => Z.eqb (CH2.ci_csp ci) (-48) && Nat.eqb (CH2.ci_nx ci) 40 | None => false end
               && CL.ps_reg_is ps 10 oE && CL.ps_reg_is ps 11 (EVar 32) && CL.ps_reg_is ps 12 (EVar 33)
               && has cells (KZero (SA (CHA.SRL3 oE) SBz) (ELit 3)))%bool
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c (BLR (chain i)) [] && CH2.blocks_eqb (nth i G.BLS []) (BLR (chain i))
           && Nat.eqb (stage i) 1 && Nat.ltb i 8 && CBA.regions_eqb (CC.cp_F c) FST)%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Definition KNC : list kentry := firstn 29 (CC.cp_know G.cp0).
Lemma kn_entry : forall ch, (ch <= 3)%nat -> CC.cp_know (nth ch G.CPS G.cp0) =
  (KNC ++ [KWord (SA (EVar 11) 0) 8 (ELit (FLG ch))]) ++ [KWord (SA (EVar 11) 24) 8 (EVar 32); KWord (SA (EVar 11) 32) 8 (EVar 33); KRange (EVar 33) (NLO ch) (NHI ch)].
Proof. intros ch Hch. destruct ch as [|[|[|[|ch]]]]; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exfalso; lia]. Qed.
Lemma regs_entry : forall ch (R : bvmap 5 word) (pv nv : Z), (ch <= 3)%nat ->
  regs_ok (Env (reg_ev R (fun k => Z_to_bv 64 (nth (k - 32) [pv; nv] 0))) (fun _ => [])) (CC.cp_regs (nth ch G.CPS G.cp0)) R.
Proof.
  intros ch R pv nv Hch rr. unfold sr_get. destruct (bv_eqb rr 0) eqn:Hr0.
  - assert (rr = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; clear - Hr0; lia). subst rr. unfold getr. rewrite Hr0.
    destruct ch as [|[|[|[|ch]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | exfalso; clear - Hch; lia].
  - unfold reg_ev. rewrite <- (ridx_roundtrip rr) at 1. pose proof (ridx_range rr) as Hlt. set (nn := ridx rr) in *. clearbody nn.
    destruct ch as [|[|[|[|ch]]]]; [| | | | exfalso; clear - Hch; lia];
      [ let l := eval vm_compute in (CC.cp_regs (nth 0 G.CPS G.cp0)) in change (CC.cp_regs (nth 0 G.CPS G.cp0)) with l
      | let l := eval vm_compute in (CC.cp_regs (nth 1 G.CPS G.cp0)) in change (CC.cp_regs (nth 1 G.CPS G.cp0)) with l
      | let l := eval vm_compute in (CC.cp_regs (nth 2 G.CPS G.cp0)) in change (CC.cp_regs (nth 2 G.CPS G.cp0)) with l
      | let l := eval vm_compute in (CC.cp_regs (nth 3 G.CPS G.cp0)) in change (CC.cp_regs (nth 3 G.CPS G.cp0)) with l ];
      (do 32 (destruct nn as [|nn]; [cbn [nth edenot ev Nat.ltb Nat.leb Nat.sub]; reflexivity |]); exfalso; clear - Hlt; lia).
Qed.
End GSC.

Lemma str_cap_even : forall n, PML.str_cap n mod 2 = 0.
Proof.
  intros n. unfold PML.str_cap. destruct (Z.lor n 7 =? 23); [reflexivity|].
  rewrite Zmod_even, Z.even_add.
  replace (Z.even (Z.lor n 7)) with false; [reflexivity|].
  symmetry. rewrite <- Z.negb_odd, <- Z.bit0_odd, Z.lor_spec, Bool.orb_true_r. reflexivity.
Qed.

Lemma str_cap_ge24 : forall n, 23 <= n -> 24 <= PML.str_cap n.
Proof.
  intros n Hn. unfold PML.str_cap. destruct (Z.lor n 7 =? 23); [lia|].
  pose proof (Z.add_lor_land n 7) as E.
  assert (LA : Z.land n 7 = n mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia.
Qed.

Section GetTxtOk.
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
Hypothesis FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static L a /\ ~ hl_rt_ro L a.
Hypothesis STRINIT_OK : PMSA.strinit_specA L ar HI GSC.PC_STRINIT.

Lemma FFSnil : forall i, nth i GSC.FFS [] = [].
Proof. intros i. unfold GSC.FFS. do 8 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma est0 : forall E k, 0 <= k -> estart E (SA (ELit 0) k) = k.
Proof. intros E k Hk. unfold estart. cbn [a_base a_off edenot]. rewrite u64_of_Z by lia. lia. Qed.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.

Lemma lstr_ag : forall (M1 M2 : mem) o s, 0 <= o -> o + 24 <= 2 ^ 64 -> (forall a, o <= a < o + 24 -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  L5.lstr_short (hl_segs L) M1 o s -> L5.lstr_short (hl_segs L) M2 o s.
Proof.
  intros M1 M2 o s H0 H1 AG (X1 & X2 & X3 & X4).
  assert (OO : PTA.out (fun a => o <= a < o + 24) o 24) by (split; [lia|]; split; [lia|]; intros i Hi; exact Hi).
  split; [exact X1|]. split; [exact (PTA.u8_ag (hl_segs L) M1 M2 _ AG o _ (PTA.out_sub _ o 24 o 1 OO ltac:(lia) ltac:(lia)) X2)|].
  split; [exact (PTA.bytes_ag (hl_segs L) M1 M2 _ AG (o + 1) s (PTA.out_sub _ o 24 (o + 1) (Z.of_nat (length s)) OO ltac:(lia) ltac:(lia)) X3)|].
  exact (PTA.u8_ag (hl_segs L) M1 M2 _ AG (o + 1 + Z.of_nat (length s)) _ (PTA.out_sub _ o 24 (o + 1 + Z.of_nat (length s)) 1 OO ltac:(lia) ltac:(lia)) X4).
Qed.

Theorem get_txt_ok : GSP.get_string_on L ar HI IC GSP.is_txt 841728.
Proof.
  intros LB FF LK cr A o V E sp r e g He. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & Ha3 & HEV & HSRC & DV & HEC & HRO & HLS & HG0 & (Ofr & O8 & Osh) & DO & (Efr & E8 & Esh) & APOE & APOV & APVE & HCR & (Vfr & V8 & Vsh) & Hstksh & SP32) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a3, PMLA.apart in *. assert (SCRG : PMCSA.GETSTR_SCR = 14384) by reflexivity. rewrite SCRG in *.

  assert (HCH : exists ch0 tp tn, (ch0 <= 3)%nat /\ L5.u64_at (hl_segs L) M (V + 8) (GSC.FLG ch0) /\ L5.u64_at (hl_segs L) M (V + 32) tp /\ L5.u64_at (hl_segs L) M (V + 40) tn /\
                 (0 <= tn < 2 ^ 26 /\ L5.defined M tp tn /\ aacc M tp tn /\ (tn = 0 \/ exists b, In b LB /\ fst b <= tp /\ tp + tn <= fst b + snd b)) /\ PMCSA.conv_ok e /\
                 acredit_ok L cr (Z.max 48 (PML.str_cap tn)) /\ (GSC.long ch0 = true <-> 23 <= tn) /\
                 (match e with PMCUR.EvStr _ tn' | PMCUR.EvKey _ tn' => PML.str_cap tn' | _ => 0 end) = PML.str_cap tn).
  { destruct e as [| | | | |p0 n0|p0 n0| | | |]; try contradiction He; destruct HEV as (_ & HF1 & HF2 & HF3);
      [exists (if Z.leb n0 22 then 0%nat else 1%nat) | exists (if Z.leb n0 22 then 2%nat else 3%nat)]; exists p0, n0;
      destruct (Z.leb_spec n0 22) as [HN|HN];
        (split; [clear - HN; lia|]); (split; [exact HF1|]); (split; [exact HF2|]); (split; [exact HF3|]); (split; [exact HSRC|]); (split; [exact I|]); (split; [exact HCR|]);
        (split; [cbn; split; intros HX; first [discriminate HX | reflexivity | clear - HN HX; lia] | reflexivity]). }
  destruct HCH as (ch0 & tp & tn & Hch0 & HFL & HPV & HNV & (N26 & DFP & ACP & SRCB) & HCO & HCR' & LNG & EQM).
  set (pv := bv_unsigned (Z_to_bv 64 tp)).
  assert (PV : 0 <= pv < 2 ^ 64) by (unfold pv; apply (bv_unsigned_in_range 64)).
  assert (HPV' : L5.u64_at (hl_segs L) M (V + 32) pv) by (unfold L5.u64_at in *; unfold pv; rewrite Z_to_bv_bv_unsigned; exact HPV).
  assert (DEV : L5.defined M (V + 8) 40) by exact (proj1 HEV).

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM. pose proof (L5A.aly_memset L C LAY) as PCAMS.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar _ FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.infr_rng L ar _ FF V 48 RFx Vfr ltac:(clear; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  destruct (CL5A.infr_rng L ar _ FF E 16 RFx Efr ltac:(clear; lia)) as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  change (hid (V + 48 <= 2147446784 \/ 17594333495296 <= V)) in Q5. change (hid (V + 48 <= hl_img_lo L \/ hl_img_hi L <= V)) in Q7.
  change (hid (E + 16 <= 2147446784 \/ 17594333495296 <= E)) in W5. change (hid (E + 16 <= hl_img_lo L \/ hl_img_hi L <= E)) in W7.
  change (hid (o + 24 <= E \/ E + 16 <= o)) in APOE. change (hid (o + 24 <= V \/ V + 48 <= o)) in APOV. change (hid (V + 48 <= E \/ E + 16 <= V)) in APVE.

  assert (PVE : tn = 0 \/ (pv = tp /\ 4096 <= tp /\ tp + tn <= ahl_ceil ar)).
  { destruct SRCB as [->|(b & Hb & B1 & B2)]; [left; reflexivity|]. right. destruct (CHA.rf_blk _ _ _ _ RFx b Hb) as (A1 & _ & _ & _ & A5 & _).
    assert (0 <= tp < 2 ^ 64) by (clear - A1 A5 B1 B2 N26 S2 S3 SP1; lia). split; [unfold pv; apply u64_of_Z; exact H|]. clear - A1 A5 B1 B2 N26. lia. }
  assert (TXO : PTA.out (fun a => 0 <= a < 2 ^ 64 /\ ~ (sp - 14384 <= a < sp)) pv tn).
  { destruct PVE as [->|(PE & P1 & P2)]; [split; [clear - PV; lia|]; split; [clear - PV; lia|]; intros a Ha; exfalso; clear - Ha; lia|].
    split; [clear - PV; lia|]. split; [clear - PE P2 S2 S3 SP1; lia|]. intros a Ha. clear - PE P1 P2 Ha S2 S3 SP1. lia. }
  assert (SHO : forall a, pv <= a < pv + tn -> 0 <= S a < 2 ^ 64 /\ ~ (sp - 14384 <= S a < sp)).
  { intros a Ha. destruct PVE as [->|(PE & P1 & P2)]; [exfalso; clear - Ha; lia|]. unfold S, SB. split; [split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; clear - Ha P1 PE; lia | clear; lia] |] |].
    - assert (a / 8 <= a) by (apply Z.div_le_upper_bound; clear - Ha P1 PE; lia). clear - H Ha P2 PE S2 S3 SP1. lia.
    - assert (a / 8 <= a) by (apply Z.div_le_upper_bound; clear - Ha P1 PE; lia). assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [clear; lia | clear - Ha PE P2 S2 S3 SP1; lia]).
      clear - H0 CL S2. lia. }
  assert (DFP' : L5.defined M pv tn) by (destruct PVE as [->|(-> & _)]; [intros k Hk; exfalso; clear - Hk; lia | exact DFP]).
  assert (ACP' : aacc M pv tn) by (destruct PVE as [->|(-> & _)]; [intros k Hk; exfalso; clear - Hk; lia | exact ACP]).
  destruct (PTA.defined_bytes (hl_segs L) M pv (Z.to_nat tn) ltac:(rewrite Z2Nat.id by (clear - N26; lia); exact DFP')) as (txt & TL & TB).
  assert (LEN : Z.of_nat (length txt) = tn) by (rewrite TL; apply Z2Nat.id; clear - N26; lia).
  assert (SRCB' : txt = [] \/ exists b, In b LB /\ fst b <= pv /\ pv + Z.of_nat (length txt) <= fst b + snd b).
  { destruct (Z.eq_dec tn 0) as [N0|N0].
    - left. destruct txt; [reflexivity | cbn [length] in LEN; clear - LEN N0; lia].
    - right. destruct SRCB as [->|(b & Hb & B1 & B2)]; [exfalso; exact (N0 eq_refl)|]. exists b. rewrite LEN.
      destruct PVE as [->|(-> & _)]; [exfalso; exact (N0 eq_refl) | split; [exact Hb | split; [exact B1 | exact B2]]]. }
  assert (CRT : (23 <= length txt)%nat -> acredit_ok L cr (PML.str_cap (Z.of_nat (length txt)))).
  { intros _. rewrite LEN. destruct HCR' as (K1 & K2). split; [exact K1|]. destruct (L5A.aly_cost L C LAY) as (_ & BL & _).
    assert (hl_b_lin L * PML.str_cap tn <= hl_b_lin L * Z.max 48 (PML.str_cap tn)) by (apply Z.mul_le_mono_nonneg_l; [exact BL | apply Z.le_max_r]). clear - K2 H. lia. }
  assert (SHR : forall p k a, 0 <= p -> 0 < k -> p + k <= 2 ^ 47 -> in_shadow_of p k a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  set (E0 := Env (reg_ev R (fun k => Z_to_bv 64 (nth (k - 32) [pv; tn] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 (V + 8)) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V13 : ev E0 13 = Z_to_bv 64 E) by (rewrite <- Ha3; exact (EV 13%bv)).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = V + 8) by (rewrite V11; apply u64_of_Z; clear - Q3 Q6; lia).
  assert (U13 : bv_unsigned (ev E0 13) = E) by (rewrite V13; apply u64_of_Z; clear - W3 W6; lia).
  assert (U32 : bv_unsigned (ev E0 32) = pv) by (cbn; apply u64_of_Z; exact PV).
  assert (U33 : bv_unsigned (ev E0 33) = tn) by (cbn; apply u64_of_Z; clear - N26; lia).
  assert (GRN : forall k, 0 <= k < 24 -> (o + k) / 8 = o / 8 + k / 8).
  { intros k Hk. clear - O8 Hk. apply Z.mod_divide in O8; [|lia]. destruct O8 as [q ->]. rewrite Z.div_mul by lia. rewrite Z.div_add_l by lia. lia. }

  assert (SCRV : CH.hd_scr G.HDECL = 14384) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(o, 24); (E, 16); (PMLA.CONVCAT_GUARD IC, 2); (PMLA.ATEXIT_TAB IC, ATEXIT_TAB_BYTES); (hl_tp L - 164, 4)] : list L5.range).
  set (Wo := [(o, 24); (E, 16)] : list L5.range).
  assert (RFr : CHA.rng_facts L ar LB FF) by exact RFx.
  assert (WINC : incl Wo WW) by (intros w [<-|[<-|[]]]; [left; reflexivity | right; left; reflexivity]).
  assert (WOK : forall (w : L5.range) (a : Z), In w Wo -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin;
      [exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFr Ofr Hin) | exact (CL5A.infr_wok L ar LB FF sp _ E 16 a RFr Efr Hin)]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w Wo /\ L5.in_rng w a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_wrs G.HDECL) in change (CH.hd_wrs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
    - rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia].
    - rewrite U13 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (E, 16). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
  { assert (GOBJ : forall p n (Hf : CL5A.ainfr FF p n) a, 0 < n -> p <= a < p + n -> CHA.sclientA L ar LB FF sp G.HDECL a).
    { intros p n Hf a Hn Ha. destruct (CL5A.infr_wok L ar LB FF sp (CH.hd_scr G.HDECL) p n a RFr Hf Ha) as (G1 & G2 & G3). split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
    assert (GSH : forall p n (Hf : CL5A.ainfr FF p n) a, 0 < n -> p mod 8 = 0 -> p / 8 + 2147450880 <= a < p / 8 + 2147450880 + n / 8 -> CHA.sclientA L ar LB FF sp G.HDECL a).
    { intros p n Hf a Hn Hp8 Ha. pose proof (CL5A.shreg_in_shadow p (n / 8) a Hp8 ltac:(clear - Ha; lia) ltac:(unfold SB; clear - Ha; lia)) as SH.
      destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) p n a RFr Hf Hn (CL5A.in_shadow_mono p (8 * (n / 8)) p n a ltac:(clear; lia) ltac:(pose proof (Z.mul_div_le n 8 ltac:(clear; lia)); clear - H; lia) ltac:(clear - Ha; lia) SH)) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
    intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[<-|[]]]]].
    - split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      exact (GOBJ V 48 Vfr a ltac:(clear; lia) ltac:(clear - Ha; lia)).
    - split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      exact (GSH o 24 Ofr a ltac:(clear; lia) O8 Ha).
    - split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U11 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      assert (SV : (V + 8) / 8 = V / 8 + 1) by (clear - V8; apply Z.mod_divide in V8; [|lia]; destruct V8 as [q ->]; rewrite Z.div_mul by lia; replace (q * 8 + 8) with ((q + 1) * 8) by lia; rewrite Z.div_mul by lia; lia).
      rewrite SV in Ha. exact (GSH V 48 Vfr a ltac:(clear; lia) V8 ltac:(clear - Ha; lia)).
    - split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U13 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      exact (GSH E 16 Efr a ltac:(clear; lia) E8 Ha). }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (Cred := fun (i : nat) (E1 : env) (cr1 : credit) => cr1 = if (Nat.eqb (GSC.stage i) 1 && GSC.long (GSC.chain i))%bool then adebit L cr (CL5A.uv E1 (EVar 41)) else cr).
  set (XI := fun (i : nat) (E1 : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) =>
     GSC.chain i = ch0 /\ PMLA.img_ro IC M1 /\ PMLA.ec_at (hl_segs L) IC M1 E 0 /\ PMLA.ls_ok (hl_segs L) IC g M1 /\
     (GSC.stage i = 0%nat -> L5.defined M1 o 24 /\ PMSA.stksh ar M1 sp 14384 /\ L5.bytes_at (hl_segs L) M1 pv txt /\ L5.defined M1 pv tn /\ aacc M1 pv tn) /\
     (GSC.stage i = 1%nat -> if GSC.long ch0 then PMLA.str_at_w (hl_segs L) M1 o (PML.SLong (CL5A.uv E1 (EVar 41)) (CL5A.uv E1 (EVar 40)) txt) /\
                                                  PMLA.afresh L ar LB FF M1 (CL5A.uv E1 (EVar 40)) (CL5A.uv E1 (EVar 41)) /\ CL5A.uv E1 (EVar 41) = PML.str_cap tn
                             else PMLA.str_at_w (hl_segs L) M1 o (PML.SShort txt))).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ GSC.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }
  assert (ST0 : GSC.stage ch0 = 0%nat /\ GSC.chain ch0 = ch0 /\ nth ch0 G.BLS [] = [] /\ nth_error G.CPS ch0 = Some (nth ch0 G.CPS G.cp0) /\ CC.cp_pc (nth ch0 G.CPS G.cp0) = 841728).
  { destruct ch0 as [|[|[|[|ch0]]]]; [repeat split; reflexivity | repeat split; reflexivity | repeat split; reflexivity | repeat split; reflexivity | exfalso; clear - Hch0; lia]. }
  destruct ST0 as (ST0 & CHN0 & BLS0 & CP0 & PC0).
  rewrite <- LS in FPM. rewrite <- PC0.
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS GSC.FFS Cred 6 STKF SCRP NF32 U2 WINC WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := ch0) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact GSC.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).  -
    assert (UVE : forall E1 e1 z, env_agree GT.NF E0 E1 -> APC.expr_vars_lt GT.NF e1 = true -> CL5A.uv E0 e1 = z -> CL5A.uv E1 e1 = z).
    { intros E1 e1 z Hag Hv Hz. rewrite (CL5A.uv_agree GT.NF E0 E1 e1 Hag Hv). exact Hz. }
    assert (ULIT : forall E1 z, 0 <= z < 2 ^ 64 -> CL5A.uv E1 (ELit z) = z) by (intros E1 z Hz; unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; exact Hz).

    assert (FOOTRG : forall a, PMLA.in_foot IC a \/ PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> 65536 <= a < 7020804).
    { intros a [Ha|Ha]; [|cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Ha; clear - Ha; lia].
      pose proof Ha as (iv & Hiv & Hr). cbn [PMLA.FOOT PMLA.C_cboth] in Hiv. repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hiv. }
    assert (STF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 1
               \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
               \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a).
    { intros a Ha. cbn [PMLA.GLOC_GUARD PMLA.GLOC_PTR PMLA.SYSCAT_GUARD PMLA.ERRCAT_GUARD PMLA.ATEXIT_TAB PMLA.NEED_LOCKS PMLA.LOCALE_LOCK PMLA.CONVCAT_GUARD PMLA.C_cboth] in Ha.
      unfold PMLA.in_foot. cbn [PMLA.FOOT PMLA.C_cboth].
      destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]].
      - exists (6882768, 6883272). split; [right; right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (6882768, 6883272). split; [right; right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (6882752, 6882754). split; [right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (6882184, 6882186). split; [left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (7020000, 7020544). split; [do 5 right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (7020579, 7020580). split; [do 6 right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (7020800, 7020804). split; [do 7 right; left; reflexivity | cbn [fst snd]; clear - Ha; lia].
      - exists (6882176, 6882178). split; [do 8 right; left; reflexivity | cbn [fst snd]; clear - Ha; lia]. }

    set (KS := fun a : Z => (o <= a < o + 24) \/ (E <= a < E + 16) \/ PMLA.in_foot IC a \/ PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).
    assert (KSR : forall a, KS a -> 0 <= a < 2 ^ 64 /\ ~ (sp - 14384 <= a < sp)).
    { intros a [Ha|[Ha|Ha]]; [clear - Ha O3 O6 O4 S2; lia | clear - Ha W3 W6 W4 S2; lia | pose proof (FOOTRG a Ha); clear - H S2 CL; lia]. }
    assert (KSC : forall LBx spx scrx a, incl LB LBx -> KS a -> aclient L ar LBx FF spx scrx a).
    { intros LBx spx scrx a HiB [Ha|[Ha|Ha]].
      - right; right; right; left. destruct Ofr as (f & Hf & F1 & F2). exists f. split; [exact Hf | clear - Ha F1 F2; lia].
      - right; right; right; left. destruct Efr as (f & Hf & F1 & F2). exists f. split; [exact Hf | clear - Ha F1 F2; lia].
      - right; right; left. pose proof (FOOTRG a Ha) as RG. rewrite ILO, IHI. split; [clear - RG; lia|].
        destruct Ha as [Ha|Ha]; [exact (proj1 (FOOTC2 a Ha)) | intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_cboth] in Ha; clear - Ha H; lia]. }

    assert (LFR : forall c ps0 E1 R' A1 M1 m1 M' m', CBA.regions_eqb (CC.cp_F c) GSC.FST = true -> env_agree GT.NF E0 E1 ->
              CCA.leaf_factsA (hl_segs L) c ps0 E1 R' A1 M1 m1 M' m' -> forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 14384 <= a < sp) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros c ps0 E1 R' A1 M1 m1 M' m' HF Hag1 HLF a Ha Hn. apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF (Z_to_bv 64 a)).
      apply CBA.regions_eqb_eq in HF. rewrite HF. unfold GSC.FST, SGP.outside. rewrite u64_of_Z by exact Ha. constructor; [|constructor].
      rewrite (CL5.estart_lin E1 (EVar 2) (-14384) sp ltac:(lin_eval; rewrite <- (proj1 Hag1 2%nat) by (apply Nat.ltb_lt; reflexivity); rewrite U2; clear; lia) ltac:(clear - S2 S3 CL SP1; lia)).
      unfold elenZ. cbn [edenot]. rewrite u64_of_Z by (clear; lia). clear - Hn. lia. }

    set (KS2 := fun a : Z => (E <= a < E + 16) \/ PMLA.in_foot IC a \/ PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC).
    assert (KS2_KS : forall a, KS2 a -> KS a) by (intros a Ha; right; exact Ha).
    assert (TR : forall (M1 M2 : mem), (forall a, KS2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
              (PMLA.img_ro IC M1 -> PMLA.img_ro IC M2) /\
              (forall code, PMLA.ec_at (hl_segs L) IC M1 E code -> PMLA.ec_at (hl_segs L) IC M2 E code) /\
              (PMCSA.ec_conv_atA L IC M1 E 11 -> PMCSA.ec_conv_atA L IC M2 E 11) /\
              (forall gg, gg <> PML.LS0 -> PMLA.ls_ok (hl_segs L) IC gg M1 -> PMLA.ls_ok (hl_segs L) IC gg M2)).
    { intros M1 M2 AG.
      assert (OE : PTA.out KS2 E 16) by (split; [clear - W3; lia|]; split; [clear - W6; lia|]; intros ii Hii; left; exact Hii).
      split; [exact (PTA.clear_ag M1 M2 KS2 AG _ _ (fun ii Hii => or_intror (or_intror Hii)))|].
      split; [intros code H; exact (PTA.ec_at_ag (hl_segs L) IC M1 M2 KS2 AG E code OE H)|].
      split.
      { intros (X1 & X2 & X3). unfold PMLA.u32, PMLA.u64 in *. split; [exact (PTA.u32_ag (hl_segs L) M1 M2 KS2 AG E 11 (PTA.out_sub KS2 E 16 E 4 OE ltac:(clear; lia) ltac:(clear; lia)) X1)|].
        split; [exact (PTA.def_ag M1 M2 KS2 AG E 16 OE X2)|]. exact (PTA.u64_ag (hl_segs L) M1 M2 KS2 AG (E + 8) _ (PTA.out_sub KS2 E 16 (E + 8) 8 OE ltac:(clear; lia) ltac:(clear; lia)) X3). }
      intros gg Hgg H. refine (PTA.ls_ok_ag (hl_segs L) IC M1 M2 KS2 AG gg Hgg _ STF H).
      intros a Ha. pose proof (FOOTRG a ltac:(destruct Ha as [Ha|Ha]; [right; exact Ha | left; exact Ha])) as RG. split; [clear - RG; lia|]. right. destruct Ha as [Ha|Ha]; [right; exact Ha | left; exact Ha]. }
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS GSC.FFS Cred 6 STKF SCRP NF32 U2 V4 WINC WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    assert (STNEWS : forall E2 A2 m2 M2 LB2 LK2 cr2, ri_inv HI LB2 FF LK2 cr2 A2 M2 (vml_of m2) -> forall X0, In X0 GSC.STAT -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X0).
    { intros E2 A2 m2 M2 LB2 LK2 cr2 HH2 X0 HX0. unfold GSC.STAT in HX0. cbn [In] in HX0.
      destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). }

    assert (ACC_AG : forall (M1 M2 : mem), (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 14384 <= a < sp) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> aacc M1 pv tn -> aacc M2 pv tn).
    { intros M1 M2 AG HA a Ha. destruct (SHO a Ha) as (H1 & H2).
      destruct (HA a Ha) as [B|(v & B & B1 & B2)]; [left; exact (PTA.byte_ag M1 M2 _ (fun x Hx => AG x (proj1 Hx) (proj2 Hx)) _ _ (conj H1 H2) B)|].
      right. exists v. split; [exact (PTA.byte_ag M1 M2 _ (fun x Hx => AG x (proj1 Hx) (proj2 Hx)) _ _ (conj H1 H2) B) | split; [exact B1 | exact B2]]. }
    assert (AFR_AG : forall (M1 M2 : mem) q m, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 14384 <= a < sp) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
              PMLA.afresh L ar LB FF M1 q m -> PMLA.afresh L ar LB FF M2 q m).
    { intros M1 M2 q m AG (AB & BA & FA & D & SBK). pose proof AB as (A1 & _ & A3 & A4 & A5 & _).
      assert (AG' : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp - 14384 <= x < sp)) -> M2 (Z_to_bv 64 x) = M1 (Z_to_bv 64 x)) by (intros x Hx; exact (AG x (proj1 Hx) (proj2 Hx))).
      split; [exact AB|]. split; [exact BA|]. split; [exact FA|]. split.
      - apply (PTA.def_ag M1 M2 _ AG' q m); [|exact D]. split; [clear - A1; lia|]. split; [clear - A5 S2 S3 SP1; lia|]. intros x Hx. clear - Hx A1 A5 S2 S3 SP1. lia.
      - apply (PTA.shadow_blk_ag M1 M2 _ AG' q m); [clear - A4; lia | | clear - A3; apply Z.mod_divide in A3; [|lia]; destruct A3 as [k ->]; replace (k * 16) with ((2 * k) * 8) by lia; apply Z.mod_mul; lia | exact SBK].
        intros x Hx. unfold in_shadow_of, S, SB in Hx. assert ((q + m - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [clear; lia | clear - A5 S2 S3 SP1; lia]).
        assert (0 <= q / 8) by (apply Z.div_pos; clear - A1; lia). split; [clear - Hx H H0; lia | clear - Hx H CL S2; lia]. }
    assert (STRW_AG : forall (M1 M2 : mem) rep, (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 14384 <= a < sp) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
              (match rep with PML.SShort _ => True | PML.SLong cap q _ => 0 <= q /\ q + cap <= ahl_ceil ar end) ->
              PMLA.str_at_w (hl_segs L) M1 o rep -> PMLA.str_at_w (hl_segs L) M2 o rep).
    { intros M1 M2 rep AG HR HS.
      assert (AG' : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp - 14384 <= x < sp)) -> M2 (Z_to_bv 64 x) = M1 (Z_to_bv 64 x)) by (intros x Hx; exact (AG x (proj1 Hx) (proj2 Hx))).
      assert (OO : PTA.out (fun x => 0 <= x < 2 ^ 64 /\ ~ (sp - 14384 <= x < sp)) o 24).
      { split; [clear - O3; lia|]. split; [clear - O6; lia|]. intros x Hx. exact (KSR x (or_introl Hx)). }
      destruct rep as [s|cap q s].
      - cbn [PMLA.str_at_w] in HS |- *. apply (lstr_ag M1 M2 o s ltac:(clear - O3; lia) ltac:(clear - O6; lia)); [|exact HS]. intros a Ha. destruct (KSR a (or_introl Ha)) as (K1 & K2). exact (AG a K1 K2).
      - cbn [PMLA.str_at_w] in HS |- *. destruct HR as (QQ0 & QQ1). destruct HS as ((B & W0 & W8 & W16 & BS & NUL) & LT).
        assert (OQ : PTA.out (fun x => 0 <= x < 2 ^ 64 /\ ~ (sp - 14384 <= x < sp)) q cap).
        { split; [exact QQ0|]. split; [clear - QQ1 S2 S3 SP1; lia|]. intros x Hx. clear - Hx QQ0 QQ1 S2 S3 SP1. lia. }
        split; [|exact LT]. split; [exact B|].
        split; [exact (PTA.u64_ag (hl_segs L) M1 M2 _ AG' o _ (PTA.out_sub _ o 24 o 8 OO ltac:(clear; lia) ltac:(clear; lia)) W0)|].
        split; [exact (PTA.u64_ag (hl_segs L) M1 M2 _ AG' (o + 8) _ (PTA.out_sub _ o 24 (o + 8) 8 OO ltac:(clear; lia) ltac:(clear; lia)) W8)|].
        split; [exact (PTA.u64_ag (hl_segs L) M1 M2 _ AG' (o + 16) _ (PTA.out_sub _ o 24 (o + 16) 8 OO ltac:(clear; lia) ltac:(clear; lia)) W16)|].
        split; [exact (PTA.bytes_ag (hl_segs L) M1 M2 _ AG' q s (PTA.out_sub _ q cap q (Z.of_nat (length s)) OQ ltac:(clear; lia) ltac:(clear - LT; lia)) BS)|].
        exact (PTA.u8_ag (hl_segs L) M1 M2 _ AG' (q + Z.of_nat (length s)) _ (PTA.out_sub _ q cap (q + Z.of_nat (length s)) 1 OQ ltac:(clear - QQ0; lia) ltac:(clear - LT; lia)) NUL). }
    assert (WIN : forall w a, In w [(o, 24)] -> L5.in_rng w a -> o <= a < o + 24) by (intros w a [<-|[]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin).
    assert (KEO : forall (M1 M2 : mem) LBk spx scrx, CHA.ahpres L ar LBk FF spx scrx [(o, 24)] M1 M2 -> incl LB LBk -> forall a, KS2 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros M1 M2 LBk spx scrx HP HiB a KSa. pose proof HP as (HP1 & _ & _). apply HP1. split; [exact (proj1 (KSR a (KS2_KS a KSa)))|]. split; [exact (KSC LBk _ _ a HiB (KS2_KS a KSa))|].
      intros w Hw Hin. pose proof (WIN w a Hw Hin) as Hoa. destruct KSa as [Ha|Ha]; [unfold hid in APOE; clear - Ha Hoa APOE; lia|].
      pose proof (FOOTRG a ltac:(destruct Ha as [Ha|Ha]; [left; exact Ha | right; exact Ha])) as RG. clear - RG Hoa O1 FSLO. lia. }

    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ GSC.leaf_ok _ _ _ _ _ HIL) as X. unfold GSC.leaf_chk in X.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].

      apply andb_prop in X as [X Ysh]. apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Ychk].
      apply andb_prop in X as [X Y0]. apply andb_prop in X as [X YPC]. apply andb_prop in X as [X YFS]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YBj].
      apply andb_prop in X as [X YBi]. apply andb_prop in X as [X Yj8]. apply andb_prop in X as [X Yi8]. apply andb_prop in X as [X YSI]. apply andb_prop in X as [YCH YSJ].
      apply Nat.eqb_eq in YCH, YSJ, YSI. apply CH2.blocks_eqb_eq in YBi, YBj. apply Z.eqb_eq in YPC, Y0. subst pc.
      destruct (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4176 2 [] [] [(GSC.oE, 0, ELit 24)] GSC.STAT None c ps0 cj [] [] (GSC.BLR (GSC.chain i)) []) as [ci|] eqn:Hchk; [|discriminate].
      apply andb_prop in Ychk as [Ychk Ynx]. apply Z.eqb_eq in Ychk. apply Nat.eqb_eq in Ynx.
      assert (HcF : forall E1, CHA.curF FF sp GSC.FFS i E1 = FF) by (intros E1; unfold CHA.curF; rewrite FFSnil; reflexivity).
      assert (HcB : forall E1, CHA.curB LB G.BLS i E1 = LB) by (intros E1; unfold CHA.curB; rewrite YBi; reflexivity).
      assert (HcBj : forall E1, CHA.curB LB G.BLS j E1 = CH2.den E1 (GSC.BLR (GSC.chain i)) ++ LB) by (intros E1; unfold CHA.curB; rewrite YBj; reflexivity).
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
      unfold XI in HXi. destruct HXi as (XC & XR & XEC & XLS & XS0 & _). destruct (XS0 YSI) as (XD & XSK & XTB & XDP & XAC).
      refine (CALLEE GSC.PC_STRINIT 4176 2%nat [] [(GSC.oE, 0, ELit 24)] GSC.STAT None 0 i c ps0 j cj ci Hcj _ Y0 _ _ fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LKc CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite YSI in HC1; exact HC1). subst cr1. rewrite Ychk in *.
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (CELL : forall X0, GSC.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
      assert (REG : forall (q : nat) (e1 : expr) (z : Z), CL.ps_reg_is ps0 q e1 = true -> CL5A.uv E' e1 = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
      { intros q e1 z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (LFRc : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 14384 <= a < sp) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by exact (LFR c ps0 E' R' A1 M1 m1 M' m' YFS HagE' HLF).
      assert (AGL : forall a, KS a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha; exact (LFRc a (proj1 (KSR a Ha)) (proj2 (KSR a Ha)))).
      destruct (TR M1 M' (fun a Ha => AGL a (KS2_KS a Ha))) as (TRO & TEC & _ & TLS).
      assert (XD' : L5.defined M' o 24) by (intros ii Hii; rewrite (AGL (o + ii) ltac:(left; clear - Hii; lia)); exact (XD ii Hii)).
      assert (XSK' : PMLA.stksh ar M' (sp + -48) 4176).
      { assert (XSK2 : PMLA.stksh ar M1 (sp + -48) 4176) by (apply (PTA.stksh_mono ar M1 sp 14384); [exact XSK | clear - SP32; lia | clear - SP32; lia | clear; lia]).
        apply (PTA.stksh_ag ar M1 M' (sp + -48) 4176); [|exact XSK2].
        intros a Ha. destruct (PTA.stksh_rng ar (sp + -48) 4176 a ltac:(clear - S2; lia) ltac:(clear - SP32; lia) C8 (proj2 SP1) ltac:(pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as STT; clear - STT; lia) ltac:(clear - CL; lia) Ha) as (R1a & R2a).
        apply (LFRc a R1a). unfold in_shadow_of in R2a. clear - R2a S2 S3 SP1 CL. unfold S, SB in *. lia. }
      assert (AGS : forall x, (0 <= x < 2 ^ 64 /\ ~ (sp - 14384 <= x < sp)) -> M' (Z_to_bv 64 x) = M1 (Z_to_bv 64 x)) by (intros x Hx; exact (LFRc x (proj1 Hx) (proj2 Hx))).
      assert (XTB' : L5.bytes_at (hl_segs L) M' pv txt) by (apply (PTA.bytes_ag (hl_segs L) M1 M' _ AGS pv txt); [rewrite LEN; exact TXO | exact XTB]).
      assert (XDP' : L5.defined M' pv tn) by exact (PTA.def_ag M1 M' _ AGS pv tn TXO XDP).
      assert (XAC' : aacc M' pv tn) by exact (ACC_AG M1 M' LFRc XAC).
      assert (W10 : CL5A.uv E' GSC.oE = o) by exact (UVE E' (EVar 10) o HagE' eq_refl U10).
      assert (W32 : CL5A.uv E' (EVar 32) = pv) by exact (UVE E' (EVar 32) pv HagE' eq_refl U32).
      assert (W33 : CL5A.uv E' (EVar 33) = tn) by exact (UVE E' (EVar 33) tn HagE' eq_refl U33).
      assert (SZ' : shadow_zero M' o 3).
      { intros jj Hj. apply (CL5A.byte_full (ahid A1 m') M'). exact (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 3 o (CELL _ Ysh) W10 ltac:(clear; lia) jj Hj). }
      eexists. eexists. split; [exact (STRINIT_OK LB FF LKc cr A1 o pv (sp + -48) (CC.cp_pc cj) txt)|]. split.
      { unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.stksh, PMSA.fobj. split; [exact (REG 10%nat _ o Y10 W10)|]. split; [exact (REG 11%nat _ pv Y11 W32)|].
        split; [rewrite LEN; exact (REG 12%nat _ tn Y12 W33)|]. split; [rewrite LEN; clear - N26; lia|]. split; [exact XSK'|].
        split; [exact XTB'|]. split; [rewrite LEN; exact XDP'|]. split; [rewrite LEN; exact XAC'|]. split; [exact (conj Ofr (conj O8 SZ'))|]. split; [exact XD'|].
        split; [exact SRCB' | exact CRT]. }
      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (-> & -> & HPO) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      pose proof (KEO M' M2 LB _ _ HP (incl_refl _)) as KEI.
      destruct (TR M' M2 KEI) as (TRO2 & TEC2 & _ & TLS2).
      destruct HPO as [(HL22 & HSS & -> & ->) | (H23 & p' & HSL & HFR & -> & ->)].
      *
        assert (LG : GSC.long ch0 = false) by (destruct (GSC.long ch0) eqn:HLG; [exfalso; pose proof (proj1 LNG eq_refl) as X; rewrite <- LEN in X; clear - X HL22; lia | reflexivity]).
        exists [Z_to_bv 64 0; Z_to_bv 64 0]. split; [reflexivity|]. cbv zeta. set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 0; Z_to_bv 64 0] R2) in *.
        split; [exact I|]. split; [cbn [CH2.den map app]; apply incl_refl|].
        split.
        { intros w a Hw Hin. pose proof (WIN w a Hw Hin) as Ha. exists (GSC.oE, 0, ELit 24). split; [left; reflexivity|].
          unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. unfold CL5A.uv in W10. unfold GSC.oE in *. rewrite W10, u64_of_Z by (clear; lia). clear - Ha. lia. }
        split.
        { intros w a Hw Hin (Ka & Kc & Kw). apply (Kw (o, 24)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. exact (WIN w a Hw Hin). }
        split; [rewrite HcBj, XC; unfold GSC.BLR; rewrite LG; cbn [CH2.den map app]; exact HH2|].
        split; [unfold Cred; rewrite YSJ, YCH, XC, LG; reflexivity|].
        split.
        { unfold XI. split; [rewrite YCH; exact XC|]. split; [exact (TRO2 (TRO XR))|]. split; [exact (TEC2 0 (TEC 0 XEC))|].
          split; [exact (TLS2 g HG0 (TLS g HG0 XLS))|]. split; [intros Hs; exfalso; rewrite YSJ in Hs; discriminate Hs|]. intros _. rewrite LG. exact HSS. }
        intros X0 HX0 _. exact (STNEWS E2 A2 m2 M2 _ _ _ HH2 X0 HX0).
      *
        assert (LG : GSC.long ch0 = true) by (apply (proj2 LNG); rewrite <- LEN; clear - H23; lia).
        set (cap := PML.str_cap (Z.of_nat (length txt))) in *.
        pose proof HFR as ((F1 & _ & _ & F4 & F5 & _) & _).
        assert (PR : 0 <= p' < 2 ^ 64) by (clear - F1 F5 F4 S2 S3 SP1; lia).
        assert (CR : 0 <= cap < 2 ^ 64) by (clear - F1 F5 F4 S2 S3 SP1; lia).
        exists [Z_to_bv 64 p'; Z_to_bv 64 cap]. split; [reflexivity|]. cbv zeta. set (E2 := CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 p'; Z_to_bv 64 cap] R2) in *.
        assert (G40 : CL5A.uv E2 (EVar 40) = p').
        { unfold CL5A.uv. cbn [edenot]. unfold E2. rewrite Ynx. pose proof (CH2.retEx_ghost E' 40 [Z_to_bv 64 p'; Z_to_bv 64 cap] R2 0 ltac:(cbn; clear; lia)) as GG; cbn [Nat.add] in GG; rewrite GG. cbn [nth]. apply u64_of_Z. exact PR. }
        assert (G41 : CL5A.uv E2 (EVar 41) = cap).
        { unfold CL5A.uv. cbn [edenot]. unfold E2. rewrite Ynx. pose proof (CH2.retEx_ghost E' 40 [Z_to_bv 64 p'; Z_to_bv 64 cap] R2 1 ltac:(cbn; clear; lia)) as GG; cbn [Nat.add] in GG; rewrite GG. cbn [nth]. apply u64_of_Z. exact CR. }
        split; [exact I|]. split; [cbn [CH2.den map app]; apply incl_refl|].
        split.
        { intros w a Hw Hin. pose proof (WIN w a Hw Hin) as Ha. exists (GSC.oE, 0, ELit 24). split; [left; reflexivity|].
          unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. unfold CL5A.uv in W10. unfold GSC.oE in *. rewrite W10, u64_of_Z by (clear; lia). clear - Ha. lia. }
        split.
        { intros w a Hw Hin (Ka & Kc & Kw). apply (Kw (o, 24)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. exact (WIN w a Hw Hin). }
        split; [rewrite HcBj, XC; unfold GSC.BLR; rewrite LG; cbn [CH2.den map app fst snd]; unfold CL5A.uv in G40, G41; rewrite G40, G41; exact HH2|].
        split; [unfold Cred; rewrite YSJ, YCH, XC, LG; cbn [Nat.eqb andb]; rewrite G41; reflexivity|].
        split.
        { unfold XI. split; [rewrite YCH; exact XC|]. split; [exact (TRO2 (TRO XR))|]. split; [exact (TEC2 0 (TEC 0 XEC))|].
          split; [exact (TLS2 g HG0 (TLS g HG0 XLS))|]. split; [intros Hs; exfalso; rewrite YSJ in Hs; discriminate Hs|]. intros _. rewrite LG, G40, G41. split; [exact HSL|]. split; [exact HFR | unfold cap; rewrite LEN; reflexivity]. }
        intros X0 HX0 _. exact (STNEWS E2 A2 m2 M2 _ _ _ HH2 X0 HX0).
    +
      apply andb_prop in X as [X YFX]. apply andb_prop in X as [X Yi8]. apply andb_prop in X as [X Ys1]. apply andb_prop in X as [X YB].
      apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Y0 Xbase].
      apply Z.eqb_eq in Y0. subst pc. apply CH2.blocks_eqb_eq in YB. apply Nat.eqb_eq in Ys1.
      intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      unfold XI in HXi. destruct HXi as (XC & XR & XEC & XLS & _ & XS1). specialize (XS1 Ys1).
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW Wo G.BLS GSC.FFS Cred 6 STKF SCRP NF32 U2 WINC WOK WRS_OK
                K DEF0 R r EV Hra Hraok GSC.RETPC i c ps0 _ Xbase _ (FFSnil i) fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact GSC.ret_at | rewrite FFSnil, YB; exact Xfoot |].
      intros model2 cr1 LK1' HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      rewrite SCRV in HP.
      assert (LFRc : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 14384 <= a < sp) -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by exact (LFR c ps0 E' R' A1 M1 m1 M' m' YFX HagE' HLF).
      assert (AGL : forall a, KS a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) by (intros a Ha; exact (LFRc a (proj1 (KSR a Ha)) (proj2 (KSR a Ha)))).
      destruct (TR M1 M' (fun a Ha => AGL a (KS2_KS a Ha))) as (_ & TEC & _ & TLS).
      assert (HB : CHA.curB LB G.BLS i E1 = CH2.den E1 (GSC.BLR ch0) ++ LB) by (unfold CHA.curB; rewrite YB, XC; reflexivity). rewrite HB in HH1.
      unfold Cred in HC1. rewrite Ys1, XC in HC1.
      apply (Hcont fx' R' M' model2 (CH2.den E1 (GSC.BLR ch0) ++ LB) cr1 LB WW LK1' A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
      pose proof (TEC 0 XEC) as XEC'. pose proof XEC' as (XU & XDF & _).
      exists 0, g. split.
      { unfold GSC.BLR. destruct (GSC.long ch0) eqn:LG; cbn [andb Nat.eqb] in HC1 |- *.
        - destruct XS1 as (XSL & XFR & XCAP). pose proof XFR as ((F1 & _ & _ & F4 & F5 & _) & _).
          exists (PML.SLong (CL5A.uv E1 (EVar 41)) (CL5A.uv E1 (EVar 40)) txt).
          assert (QR : 0 <= CL5A.uv E1 (EVar 40) /\ CL5A.uv E1 (EVar 40) + CL5A.uv E1 (EVar 41) <= ahl_ceil ar) by (split; [clear - F1; lia | exact F5]).
          split; [exact (STRW_AG M1 M' (PML.SLong (CL5A.uv E1 (EVar 41)) (CL5A.uv E1 (EVar 40)) txt) LFRc QR XSL)|].
          pose proof (AFR_AG M1 M' _ _ LFRc XFR) as XFR'. cbn [PMLA.srep_sh PML.srep_blocks app].
          split; [exact (proj2 (proj2 (proj2 (proj2 XFR'))))|]. split; [reflexivity|]. split; [intros X; discriminate X|].
          intros b [<-|[]]. cbn [fst snd]. split; [exact XFR'|]. split; [exact HC1 | split; [rewrite XCAP, EQM; apply Z.le_max_r | split; [rewrite XCAP; apply str_cap_even | rewrite XCAP; apply str_cap_ge24; apply (proj1 LNG); first [exact LG | reflexivity]]]].
        - exists (PML.SShort txt). split; [exact (STRW_AG M1 M' (PML.SShort txt) LFRc I XS1)|]. cbn [PMLA.srep_sh PML.srep_blocks app CH2.den map].
          split; [exact I|]. split; [reflexivity|]. split; [intros _; exact HC1 | intros b []]. }
      split; [reflexivity|]. split; [exact XU|]. split; [exact XDF|]. split; [exact (TLS g HG0 XLS)|].
      split; [left; split; [exact HCO | split; [reflexivity | split; [reflexivity | exact XEC']]]|]. reflexivity.
  - exact CP0.
  -
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VOBJ : forall p n, CL5A.ainfr FF p n -> CL5A.visr (ahid A model) p n).
    { intros p n Hf k Hk. destruct (CL5A.infr_wok L ar LB FF sp 0 p n (p + k) RFx Hf ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSH : forall p n j, CL5A.ainfr FF p n -> p mod 8 = 0 -> 0 <= j < n / 8 -> 0 < n -> ahid A model (Z_to_bv 64 (S p + j)) = false).
    { intros p n j Hf Hp8 Hj Hn. destruct (CL5A.infr_sh_wok L ar LB FF sp 0 p n (S p + j) RFx Hf Hn
                (CL5A.in_shadow_mono p (8 * (n / 8)) p n (S p + j) ltac:(clear; lia) ltac:(pose proof (Z.mul_div_le n 8 ltac:(clear; lia)); clear - H; lia) ltac:(clear - Hj; lia)
                   (CL5A.shreg_in_shadow p (n / 8) (S p + j) Hp8 ltac:(clear - Hj; lia) ltac:(unfold S; clear - Hj; lia)))) as (G1 & G2 & G3).
      exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 14384) 14384).
    { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (DOv : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 (VOBJ o 24 Ofr)); exact DO).
    assert (DEv : L5.defined Mv (V + 8) 40) by (apply (CL5A.defined_vis _ M (V + 8) 40 (CL5A.visr_sub _ V 48 (V + 8) 40 (VOBJ V 48 Vfr) ltac:(clear; lia) ltac:(clear; lia))); exact DEV).
    assert (DEE : L5.defined Mv E 16) by (apply (CL5A.defined_vis _ M E 16 (VOBJ E 16 Efr)); exact (proj1 (proj2 HEC))).
    assert (DSv : L5.defined Mv (sp - 14384) 14384) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (SZv : forall p n j, CL5A.ainfr FF p n -> p mod 8 = 0 -> 0 < n -> shadow_zero M p (n / 8) -> 0 <= j < n / 8 -> byte_at Mv (S p + j) 0).
    { intros p n j Hf Hp8 Hn HZ Hj. apply CL5A.byte_vis; [exact (VSH p n j Hf Hp8 Hj Hn) | exact (HZ j Hj)]. }
    assert (SEV : S (V + 8) = S V + 1) by (unfold S; clear - V8; apply Z.mod_divide in V8; [|lia]; destruct V8 as [q ->]; rewrite Z.div_mul by lia; replace (q * 8 + 8) with ((q + 1) * 8) by lia; rewrite Z.div_mul by lia; lia).
    split; [exact (GSC.regs_entry ch0 R pv tn Hch0)|]. unfold know_ok. rewrite (GSC.kn_entry ch0 Hch0). rewrite <- app_assoc. apply Forall_app. split.
    + let l := eval vm_compute in GSC.KNC in change GSC.KNC with l. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      * apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
      * eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
      * eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DOv].
      * eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1; lia].
      * eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
      * apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 3 o); [exact U10 | clear; lia | clear - O3 O6; lia |]. intros j Hj. exact (SZv o 24 j Ofr O8 ltac:(clear; lia) Osh Hj).
      * eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
      * eapply CL5.kunk_intro with (A := V + 8) (N := 40); [ev0 | reflexivity | clear - Q3; lia | clear - Q6; lia | clear - Q6; lia | exact DEv].
      * eapply CL5.krange_intro with (v := V + 8); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear - Q1 Q4 FSLO S2 S3 SP1; lia].
      * eapply CL5.kalign_intro with (v := V + 8); [lin_eval; rw_atoms; clear; lia | clear - Q3 Q6; lia | clear; lia | clear - V8; rewrite Z.add_mod, V8 by lia; reflexivity].
      * apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 5 (V + 8)); [exact U11 | clear; lia | clear - Q3 Q6; lia |]. intros j Hj. rewrite SEV. replace (S V + 1 + j) with (S V + (j + 1)) by (clear; lia).
        exact (SZv V 48 (j + 1) Vfr V8 ltac:(clear; lia) Vsh ltac:(change (48 / 8) with 6; clear - Hj; lia)).
      * eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := V + 8) (N2 := 40); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in Q5; clear - Q5; lia].
      * eapply CL5.kunk_intro with (A := E) (N := 16); [ev0 | reflexivity | clear - W3; lia | clear - W6; lia | clear - W6; lia | exact DEE].
      * eapply CL5.kwr_intro with (A := E) (N := 16); [ev0 | reflexivity | clear - W3; lia | clear - W6; lia | clear - W6; lia | exact DEE].
      * eapply CL5.krange_intro with (v := E); [lin_eval; rw_atoms; clear; lia | clear - W3 W6; lia | clear - W1 W4 FSLO S2 S3 SP1; lia].
      * eapply CL5.kalign_intro with (v := E); [lin_eval; rw_atoms; clear; lia | clear - W3 W6; lia | clear; lia | exact E8].
      * apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 2 E); [exact U13 | clear; lia | clear - W3 W6; lia |]. intros j Hj. exact (SZv E 16 j Efr E8 ltac:(clear; lia) Esh Hj).
      * eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := E) (N2 := 16); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in W5; clear - W5; lia].
      * eapply CL5.kunk_intro with (A := sp - 14384) (N := 14384); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DSv].
      * eapply CL5.kwr_intro with (A := sp - 14384) (N := 14384); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DSv].
      * eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
      * eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact SP32].
      * eapply CL5.kdisj_intro with (A1 := sp - 14384) (N1 := 14384) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
      * eapply CL5.kdisj_intro with (A1 := sp - 14384) (N1 := 14384) (A2 := V + 8) (N2 := 40); [ev0 | reflexivity | ev0 | reflexivity | clear - Q4 S2; lia].
      * eapply CL5.kdisj_intro with (A1 := sp - 14384) (N1 := 14384) (A2 := E) (N2 := 16); [ev0 | reflexivity | ev0 | reflexivity | clear - W4 S2; lia].
      * eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := V + 8) (N2 := 40); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in APOV; clear - APOV; lia].
      * eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := E) (N2 := 16); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in APOE; clear - APOE; lia].
      * eapply CL5.kdisj_intro with (A1 := V + 8) (N1 := 40) (A2 := E) (N2 := 16); [ev0 | reflexivity | ev0 | reflexivity | unfold hid in APVE; clear - APVE; lia].
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * eapply CL5.kword64_intro with (A := V + 8) (z := GSC.FLG ch0); [ev0 | clear - Q3; lia | clear - Q6; lia | cbn [edenot]; reflexivity |].
        exact (CL5A.u64_vis (hl_segs L) (ahid A model) M (V + 8) _ ltac:(clear - Q3; lia) ltac:(clear - Q6; lia) (CL5A.visr_sub _ V 48 (V + 8) 8 (VOBJ V 48 Vfr) ltac:(clear; lia) ltac:(clear; lia)) HFL).
      * eapply CL5.kword64_intro with (A := V + 32) (z := pv); [ev0 | clear - Q3; lia | clear - Q6; lia | cbn [edenot ev E0 reg_ev Nat.ltb Nat.leb Nat.sub nth]; reflexivity |].
        exact (CL5A.u64_vis (hl_segs L) (ahid A model) M (V + 32) _ ltac:(clear - Q3; lia) ltac:(clear - Q6; lia) (CL5A.visr_sub _ V 48 (V + 32) 8 (VOBJ V 48 Vfr) ltac:(clear; lia) ltac:(clear; lia)) HPV').
      * eapply CL5.kword64_intro with (A := V + 40) (z := tn); [ev0 | clear - Q3; lia | clear - Q6; lia | cbn [edenot ev E0 reg_ev Nat.ltb Nat.leb Nat.sub nth]; reflexivity |].
        exact (CL5A.u64_vis (hl_segs L) (ahid A model) M (V + 40) _ ltac:(clear - Q3; lia) ltac:(clear - Q6; lia) (CL5A.visr_sub _ V 48 (V + 40) 8 (VOBJ V 48 Vfr) ltac:(clear; lia) ltac:(clear; lia)) HNV).
      * eapply CL5.krange_intro with (v := tn); [lin_eval; rw_atoms; clear; lia | clear - N26; lia |].
        unfold GSC.NLO, GSC.NHI. destruct (GSC.long ch0) eqn:LG; [pose proof (proj1 LNG eq_refl); clear - H N26; lia|].
        destruct (Z.leb_spec 23 tn) as [HN|HN]; [pose proof (proj2 LNG HN) as X; discriminate X | clear - HN N26; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. rewrite FFSnil, BLS0. cbn [app CHA.denF CH2.den map length].
      split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; rewrite ST0; reflexivity | exact Hroom].
    + unfold XI. split; [exact CHN0|]. split; [exact HRO|]. split; [exact HEC|]. split; [exact HLS|]. split; [intros _; exact (conj DO (conj Hstksh (conj TB (conj DFP' ACP'))))|].
      intros H0. exfalso. rewrite ST0 in H0. discriminate H0.
  - exact Hfp.
Qed.

End GetTxtOk.
