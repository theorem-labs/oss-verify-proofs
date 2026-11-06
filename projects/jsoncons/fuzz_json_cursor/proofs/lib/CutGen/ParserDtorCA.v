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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_pdtor_casan_T Cut_pdtor_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_pdtor_casan.
Module GT := Cut_pdtor_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module PDA.
Definition PC_VDTOR : Z := 726216.
Definition PC_OPDEL : Z := 975272.
Definition RETPC : Z := 725688.
Definition SLOT : Z := 1364952.
Definition IMGSH : Z := 2147621499.
Definition SBz : Z := 2147450880.
Definition PE := EVar 10. Definition sbE := EVar 32. Definition slenE := EVar 33. Definition scapE := EVar 34. Definition bptrE := EVar 35. Definition w0E := EVar 36.
Definition bcapE : expr := EAlu Instr.ALU_ADD w0E (ELit (-1)).
Definition tE : expr := EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)).
Definition BLK0 : list (expr * expr) := [(bptrE, bcapE); (sbE, scapE)].
Definition BLK1 : list (expr * expr) := [(bptrE, bcapE)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1427896) 8 (ELit SBz)].
Definition IMGK : kentry := KWord (SA (ELit 0) IMGSH) 1 (ELit 0).
Definition NEWS2 : list kentry := STAT ++ [IMGK].
Definition WVD : list SGP.region := [(PE, 248, ELit 24)].
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
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
              if Z.eqb pc PC_VDTOR then
                (Z.eqb (SR.ps_pc ps) PC_VDTOR && Nat.eqb i 0 && Nat.eqb j 1 && CH2.blocks_eqb (nth i G.BLS []) BLK0 && CH2.blocks_eqb (nth j G.BLS []) BLK1
                 && CHA.foot_chk GT.NF G.HDECL c BLK0 []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4192 0 BLK1 [] WVD STAT None c ps cj BLK0 [] BLK1 [])
                 && CL.ps_reg_is ps 10 tE && CL.ps_reg_is ps 2 tE
                 && has cells (KWord (SA (EVar 2) (-32)) 8 (EAlu Instr.ALU_ADD PE (ELit 248)))
                 && has cells (KWord (SA PE 248) 8 sbE) && has cells (KWord (SA PE 256) 8 (EAlu Instr.ALU_ADD sbE slenE)) && has cells (KWord (SA PE 264) 8 (EAlu Instr.ALU_ADD sbE scapE))
                 && has cells (KZero (SA (CHA.SRL3 PE) SBz) (ELit 34)) && has cells (KZero (SA (CHA.SRL3 tE) SBz) (ELit 1)))%bool
              else if Z.eqb pc PC_OPDEL then
                (Z.eqb (SR.ps_pc ps) PC_OPDEL && Nat.eqb i 1 && Nat.eqb j 2 && CH2.blocks_eqb (nth i G.BLS []) BLK1 && CH2.blocks_eqb (nth j G.BLS []) []
                 && CHA.foot_chk GT.NF G.HDECL c BLK1 []
                 && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4096 0 [] [] [] NEWS2 None c ps cj BLK1 [] [] [])
                 && CL.ps_reg_is ps 10 bptrE)%bool
              else false
          | None => false
          end
      | None =>
          (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && CHA.foot_chk GT.NF G.HDECL c [] [] && Nat.eqb i 2 && CH2.blocks_eqb (nth i G.BLS []) [])%bool
      end
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
Lemma imgk_in : In IMGK (CC.cp_know G.cp2).
Proof. apply CC.has_cell_In. vm_compute. reflexivity. Qed.
End PDA.

Section ParserDtorOk.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Abbreviation IC := PMLA.C_casan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis VDTOR_OK : PMSA.vec_dtor_specA L ar HI PDA.PC_VDTOR.
Hypothesis OPDEL_OK : PMSA.opdel_specA L ar HI PDA.PC_OPDEL.
Hypothesis ISH : rt_img_shadow L IL HI.
Hypothesis POI : Forall (fun r : Z * Z => PDA.SLOT + 8 <= fst r \/ snd r <= PDA.SLOT) (icl_poison IL).

Lemma FFSnil : forall i, nth i PDA.FFS [] = [].
Proof. intros i. unfold PDA.FFS. do 4 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Definition hid (P : Prop) : Prop := P.

Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Definition parser_dtor_specA' (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r P : Z) (ps : PML.pstate),
    PMSA.cps_asan L ar HI pc r sp PMSA.PDTOR_SCR (PML.ps_blocks ps ++ LBo) FF LK cr A 0
      (fun R M => PMSA.a0 R P /\ PMLA.parser_at (hl_segs L) IC M P ps /\ PMLA.parser_sh M ps /\ PMLA.img_ro IC M /\ PMSA.fobj M FF P 272 /\ PMSA.stksh ar M sp PMSA.PDTOR_SCR /\
                  0 < PML.ps_scap ps <= 4096)
      (fun R M R' M' LB' cr' LBk W => LB' = LBo /\ cr' = cr /\ LBk = LBo /\ W = [(P, 272)]).

Theorem parser_dtor_ok : PMSA.parser_dtor_specA L ar HI IC 725196.
Proof.
  intros LBo FF LK cr A sp r P ps. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & HPA & (HSHB & HSHC) & RO & (Pfr & P8 & Psh) & Hstksh & Hscap) Hcont.
  unfold PMSA.a0, PMSA.PDTOR_SCR, PMSA.AINC_SCR, PMSA.fobj, PMSA.stksh, PMLA.stksh in *. change (160 + 4112) with 4272 in *.
  set (sb := PML.ps_sb ps) in *. set (scap := PML.ps_scap ps) in *. set (slen := Z.of_nat (length (PML.ps_stack ps))) in *.
  set (bptr := PML.ps_bptr ps) in *. set (bcap := PML.ps_bcap ps) in *.
  destruct HPA as (Pvt & _ & _ & _ & _ & _ & _ & _ & _ & S24 & S48 & S72 & P96 & P128 & _ & _ & _ & _ & _ & _ & _ & _ & _ & ((Ptb & P224 & P232 & P240 & _ & _) & Pbcap8 & Pblen) & Pbcap & P248 & P256 & P264 & _ & Pslen & PDEF).
  fold sb in P248, P256, P264, HSHC |- *. fold scap in P264, HSHC, Hscap, Pslen |- *. fold slen in P256, HSHC, Pslen |- *. fold bptr in P240, HSHB |- *. fold bcap in P224, Pbcap8, Pblen, Pbcap, HSHB |- *.
  change (PML.ps_blocks ps ++ LBo) with ((bptr, bcap) :: (sb, scap) :: LBo) in *.
  change (PMLA.VT_FUNC IC) with 1364920 in P96. replace (P + 224 + 16) with (P + 240) in P240 by (clear; lia).
  assert (SLEN0 : 0 <= slen) by (unfold slen; clear; lia).

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (bptr, bcap) (or_introl eq_refl)) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bdef, Bsa, Bap, Bfap.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)).
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (sb, scap) (or_intror (or_introl eq_refl))) as (QR & Qdef & Qsa & Qap & Qfap). cbn [fst snd] in QR, Qdef, Qsa, Qap, Qfap.
  destruct QR as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
  pose proof (PmHeapIfaceA.aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ HH (sb, scap) (or_intror (or_introl eq_refl)) ltac:(cbn [snd]; clear - Hscap; lia)) as QHI. cbn [fst] in QHI.
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  assert (NE : bptr <> sb).
  { intros E. cbn [map fst] in ND1. apply list_relations.list.NoDup_cons in ND1 as [X _]. apply X. rewrite E. left. }
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as STT.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar _ FF P 272 RFx Pfr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (P + 272 <= 2147446784 \/ 17594333495296 <= P)) in O5.
  change (hid (bptr + bcap <= 2147446784 \/ 17594333495296 <= bptr)) in B6. change (hid (bptr + bcap <= hl_img_lo L \/ hl_img_hi L <= bptr)) in B1.
  change (hid (sb + scap <= hl_img_lo L \/ hl_img_hi L <= sb)) in Q1. change (hid (sb + scap <= 2147446784 \/ 17594333495296 <= sb)) in Q6.
  change (hid (P + 272 <= hl_img_lo L \/ hl_img_hi L <= P)) in O7.
  assert (SHR : forall p n a, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  destruct Pfr as (f0 & Hf0 & F01 & F02).
  assert (Pfr : CL5A.ainfr FF P 272) by (exists f0; split; [exact Hf0 | split; [exact F01 | exact F02]]).
  pose proof (Bfap f0 (in_or_app _ _ _ (or_introl Hf0))) as BFP. pose proof (Qfap f0 (in_or_app _ _ _ (or_introl Hf0))) as QFP.
  change (hid (bptr + bcap <= ff_addr f0 \/ ff_addr f0 + ff_bytes (ff_class f0) <= bptr)) in BFP. change (hid (sb + scap <= ff_addr f0 \/ ff_addr f0 + ff_bytes (ff_class f0) <= sb)) in QFP.
  pose proof (Bap (sb, scap) ltac:(cbn [lb_remove fst]; rewrite Z.eqb_refl; left; reflexivity)) as BQ. cbn [fst snd] in BQ. change (hid (bptr + bcap <= sb \/ sb + scap <= bptr)) in BQ.

  assert (SPA : (sp - 4272) mod 8 = 0).
  { clear - S1. apply Z.mod_divide in S1; [|lia]. destruct S1 as [q Hq]. rewrite Hq. replace (q * 16 - 4272) with ((2 * q - 534) * 8) by lia. apply Z_mod_mult. }
  assert (T8 : (sp - 32) mod 8 = 0).
  { clear - S1. apply Z.mod_divide in S1; [|lia]. destruct S1 as [q Hq]. rewrite Hq. replace (q * 16 - 32) with ((2 * q - 4) * 8) by lia. apply Z_mod_mult. }
  assert (ST530 : S (sp - 32) = S (sp - 4272) + 530).
  { unfold S. clear - SPA. apply Z.mod_divide in SPA; [|lia]. destruct SPA as [q Hq]. replace (sp - 32) with (q * 8 + 4240) by lia. rewrite Hq, Z.div_add_l, Z.div_mul by lia. lia. }
  assert (Htsh : byte_at M (S (sp - 32)) 0).
  { rewrite ST530. apply Hstksh. split; [clear; lia|]. apply (Z.lt_le_trans _ 531); [clear; lia|]. apply Z.div_le_lower_bound; [clear; lia|]. clear - S3. lia. }
  assert (TSH : forall a, (sp - 32) / 8 + SB <= a < (sp - 32) / 8 + SB + 1 -> 0 <= a < 2 ^ 64 /\ in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a /\ a < S (ar_sptop ar)).
  { intros a Ha. assert (Ea : a = S (sp - 32)) by (unfold S; clear - Ha; lia).
    destruct (PTA.stksh_rng ar sp 4272 a ltac:(clear - S2; lia) SPA C8 (proj2 SP1) STT ltac:(clear - CL; lia)) as (G1 & G2).
    - rewrite Ea, ST530. split; [clear; lia|]. apply Z.add_lt_mono_l. apply (Z.lt_le_trans _ 531); [clear; lia|]. apply Z.div_le_lower_bound; [clear; lia|]. clear - S3. lia.
    - split; [exact G1|]. split; [exact G2|]. rewrite Ea. unfold S. clear - S3 SP16. apply Z.add_lt_mono_r.
      apply Z.mod_divide in SP16; [|lia]. destruct SP16 as [q Hq]. rewrite Hq. replace (q * 16) with ((2 * q) * 8) by lia. rewrite Z.div_mul by lia.
      apply Z.div_lt_upper_bound; lia. }

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [sb; slen; scap; bptr; bcap + 1] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 P) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 sb) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 slen) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 scap) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 bptr) by reflexivity.
  assert (V36 : ev E0 36 = Z_to_bv 64 (bcap + 1)) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = P) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U32 : bv_unsigned (ev E0 32) = sb) by (rewrite V32; apply u64_of_Z; clear - Q5 Q7 Q3; lia).
  assert (U33 : bv_unsigned (ev E0 33) = slen) by (rewrite V33; apply u64_of_Z; clear - SLEN0 Pslen Hscap; lia).
  assert (U34 : bv_unsigned (ev E0 34) = scap) by (rewrite V34; apply u64_of_Z; clear - Hscap; lia).
  assert (U35 : bv_unsigned (ev E0 35) = bptr) by (rewrite V35; apply u64_of_Z; clear - B5 B7 B3; lia).
  assert (U36 : bv_unsigned (ev E0 36) = bcap + 1) by (rewrite V36; apply u64_of_Z; clear - B0 B3 B4 SP1; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 4272) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
  set (WW := [(P, 272)] : list L5.range).
  assert (RFr : CHA.rng_facts L ar LBo FF) by (apply (CHA.rng_incl L ar _ FF _ FF RFx); [intros y Hy; right; right; exact Hy | apply incl_refl]).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar LBo FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LBo FF sp _ P 272 a RFr Pfr Hin). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (UT0 : bv_unsigned (edenot E0 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)))) = sp - 32) by (apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 SP1 CL; lia]).
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LBo FF sp G.HDECL a)).
  { intros rg Hrg. let l := eval vm_compute in (CH.hd_crs G.HDECL) in change (CH.hd_crs G.HDECL) with l in Hrg. cbn [In] in Hrg.
    destruct Hrg as [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CHA.in_reg in Ha; unfold CHA.sclientA.
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      pose proof (CL5A.shreg_in_shadow P 34 a P8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 34) with 272 in SH.
      destruct (CL5A.infr_sh_wok L ar LBo FF sp (CH.hd_scr G.HDECL) P 272 a RFr Pfr ltac:(clear; lia) SH) as (G1 & G2 & G3).
      split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
    - cbv beta iota in Ha. rewrite CL5A.estart_srl3' in Ha. unfold CL5A.uv, elenZ in Ha. rewrite UT0 in Ha. cbn [edenot] in Ha. rewrite u64_of_Z in Ha by (clear; lia).
      destruct (TSH a ltac:(unfold SB; clear - Ha; lia)) as (G1 & G2 & G3). split; [exact G1|]. split; [do 4 right; left; exact G2 | intros _; exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  assert (NOFOOT : forall LBown a, Forall (fun bb => 17594333495296 <= fst bb \/ fst bb + snd bb <= 2147446784) LBown -> 2147450880 <= a < 17594333495296 -> ~ CHA.afoot_sem sp G.HDECL WW LBown [] a).
  { intros LBown a HF Ha [X|[X|[X|[X|X]]]].
    - rewrite SCRV in X. clear - X Ha S2 CL. lia.
    - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin Ha O5. lia.
    - destruct X as (bb & Hbb & Hin). pose proof (proj1 (Forall_forall _ _) HF bb Hbb) as Y. cbn beta in Y. clear - Hin Ha Y. destruct Y as [Y|Y]; lia.
    - destruct X as (f & [] & _).
    - destruct X as (f & [] & _). }
  assert (HF0 : Forall (fun bb : Z * Z => 17594333495296 <= fst bb \/ fst bb + snd bb <= 2147446784) [(bptr, bcap); (sb, scap)]).
  { constructor; [cbn [fst snd]; unfold hid in B6; clear - B6; lia | constructor; [cbn [fst snd]; left; exact QHI | constructor]]. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (i : nat) (_ : env) (_ : list (Z * Z)) (M1 : word -> option byte) (_ : Model) => match i with 0%nat => shadow_cont M1 sb scap slen | _ => True end).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ PDA.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }
  assert (UBC : forall E, env_agree GT.NF E0 E -> bv_unsigned (edenot E PDA.bcapE) = bcap).
  { intros E HagE. assert (W36 : bv_unsigned (ev E 36) = bcap + 1) by (rewrite <- (proj1 HagE 36%nat) by (apply Nat.ltb_lt; reflexivity); exact U36).
    unfold PDA.bcapE, PDA.w0E. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B3 B4 SP1; lia]. }
  assert (DEN0 : forall E, env_agree GT.NF E0 E -> CH2.den E PDA.BLK0 = [(bptr, bcap); (sb, scap)]).
  { intros E HagE. unfold CH2.den, PDA.BLK0, PDA.bptrE, PDA.sbE, PDA.scapE. cbn [map fst snd]. rewrite (UBC E HagE). cbn [edenot].
    rewrite <- (proj1 HagE 35%nat), <- (proj1 HagE 32%nat), <- (proj1 HagE 34%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U35, U32, U34. reflexivity. }
  assert (DEN1 : forall E, env_agree GT.NF E0 E -> CH2.den E PDA.BLK1 = [(bptr, bcap)]).
  { intros E HagE. unfold CH2.den, PDA.BLK1, PDA.bptrE. cbn [map fst snd]. rewrite (UBC E HagE). cbn [edenot]. rewrite <- (proj1 HagE 35%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U35. reflexivity. }
  rewrite <- LS in FPM.
  change 725196 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LBo FF LK sp G.HDECL WW WW G.BLS PDA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact PDA.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ PDA.leaf_ok _ _ _ _ _ HIL) as X. unfold PDA.leaf_chk in X.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LBo FF LK sp G.HDECL WW WW G.BLS PDA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    + destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      destruct (Z.eqb_spec pc PDA.PC_VDTOR) as [->|Hne1].
      {
        apply andb_prop in X as [X Ytz]. apply andb_prop in X as [X Ypz]. apply andb_prop in X as [X Yc264]. apply andb_prop in X as [X Yc256]. apply andb_prop in X as [X Yc248]. apply andb_prop in X as [X Yt].
        apply andb_prop in X as [X Y2r]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
        apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply CH2.blocks_eqb_eq in Y3, Y4.
        lazymatch type of Y5 with PDA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        assert (HcB : CHA.curB LBo G.BLS 0 E = (bptr, bcap) :: (sb, scap) :: LBo) by (unfold CHA.curB; rewrite Y3, (DEN0 E HagE); reflexivity).
        assert (HcF : CHA.curF FF sp PDA.FFS 0 E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE PDA.PC_VDTOR 4192 0%nat PDA.BLK1 PDA.WVD PDA.STAT None 0 0%nat c ps0 1%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        assert (W2 : bv_unsigned (ev E' 2) = sp) by (rewrite (FZ 2%nat eq_refl); exact U2).
        assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite (FZ 10%nat eq_refl); exact U10).
        assert (W32 : bv_unsigned (ev E' 32) = sb) by (rewrite (FZ 32%nat eq_refl); exact U32).
        assert (W33 : bv_unsigned (ev E' 33) = slen) by (rewrite (FZ 33%nat eq_refl); exact U33).
        assert (W34 : bv_unsigned (ev E' 34) = scap) by (rewrite (FZ 34%nat eq_refl); exact U34).
        assert (CELL : forall X0, PDA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
        { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PDA.FFS Cred 0 0%nat E A1 M' m' HA') as Hoff.
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        unfold PDA.PE, PDA.sbE, PDA.slenE, PDA.scapE, PDA.tE in *.
        assert (UT : bv_unsigned (edenot E' (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32)))) = sp - 32) by (apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - S2 S3 SP1 CL; lia]).

        assert (CSPV : CH2.ci_csp ci = -32).
        { pose proof (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 2 _ HLFv Y2r) as R2E.
          replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2E by (apply bv_eq; reflexivity). rewrite HSP in R2E.
          apply (f_equal bv_unsigned) in R2E. rewrite UT in R2E. rewrite SCRV in Hc2. rewrite u64_of_Z in R2E by (clear - Hc1 Hc2 S2 S3 SP1 CL; lia). clear - R2E. lia. }
        rewrite CSPV. replace (sp + -32) with (sp - 32) by (clear; lia).

        assert (FRS : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
        { intros q n a Hq Hn Hqn Ha. pose proof (SHR q n a Hq Hn Hqn Ha) as SRa.
          refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LBo FF LK sp G.HDECL WW WW G.BLS PDA.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                    0%nat c ps0 E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil, Y3; exact YF|].
          rewrite FFSnil, Y3, (DEN0 E HagE). exact (NOFOOT _ a HF0 SRa). }
        eexists. eexists. split; [exact (VDTOR_OK ((bptr, bcap) :: (sb, scap) :: LBo) FF LK1 cr A1 (sp - 32) (P + 248) sb slen scap (sp - 32) (CC.cp_pc cj))|]. split.
        {
          unfold PMSA.a0, PMSA.u64, PMSA.acobj, PMSA.vec_ok, PMSA.vec_at, PMSA.ainfr.
          split. { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ HLFv Y10).
                   rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. exact UT. }
          split. { apply (CL5A.u64_full (hl_segs L) _ Hoff). pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (sp - 32) (CELL _ Yt) ltac:(ev0)) as G0.
                   replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EVar 10) (ELit 248))) with (P + 248) in G0; [exact G0 | symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia]]. }
          split; [right; clear - S3; lia|]. split; [exact T8|].
          split. { pose proof (CL5A.shz_elim (hl_segs L) E' _ (EAlu Instr.ALU_ADD (EVar 2) (ELit (-32))) 1 (sp - 32) (CELL _ Ytz) ltac:(unfold CL5A.uv; exact UT) ltac:(clear; lia)) as SZ.
                   intros jj Hj. exact (CL5A.byte_full _ _ _ _ (SZ jj Hj)). }
          split; [right; clear - O4 S2; lia|].
          split. { replace (P + 248 + 8) with (P + 256) by (clear; lia). replace (P + 248 + 16) with (P + 264) by (clear; lia). split; [|split]; apply (CL5A.u64_full (hl_segs L) _ Hoff).
                   - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (P + 248) (CELL _ Yc248) ltac:(ev0)) as G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite W32 in G0. exact G0.
                   - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (P + 256) (CELL _ Yc256) ltac:(ev0)) as G0.
                     replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EVar 32) (EVar 33))) with (sb + slen) in G0; [exact G0 | symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q5 Q7 Pslen SLEN0; lia]].
                   - pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (P + 264) (CELL _ Yc264) ltac:(ev0)) as G0.
                     replace (CL5A.uv E' (EAlu Instr.ALU_ADD (EVar 32) (EVar 34))) with (sb + scap) in G0; [exact G0 | symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q5 Q7 Q3; lia]]. }
          split; [exact (CL5A.ainfr_sub FF P 272 (P + 248) 24 Pfr ltac:(clear; lia) ltac:(clear; lia))|].
          split; [clear - P8; apply Z.mod_divide in P8; [|lia]; destruct P8 as [q ->]; replace (q * 8 + 248) with ((q + 31) * 8) by lia; apply Z_mod_mult|].
          split. { pose proof (CL5A.shz_elim (hl_segs L) E' _ (EVar 10) 34 P (CELL _ Ypz) ltac:(unfold CL5A.uv; cbn [edenot]; exact W10) ltac:(clear; lia)) as SZ.
                   intros jj Hj. rewrite (CL5A.S_add_al P 248 P8). change (248 / 8) with 31. replace (S P + 31 + jj) with (S P + (31 + jj)) by (clear; lia).
                   exact (CL5A.byte_full _ _ _ _ (SZ (31 + jj) ltac:(clear - Hj; lia))). }
          split; [right; left; reflexivity|]. split; [clear - Pslen SLEN0; lia|]. split; [exact Hscap|].
          apply (CL5A.shadow_cont_same M1 M' sb scap slen ltac:(clear - Pslen SLEN0; lia) (CHA.mod8_of_16 _ Q16)); [|exact HXi]. intros a Ha.
          exact (FRS sb scap a ltac:(clear - Q5; lia) Q3 Q7 Ha). }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (-> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          assert (RM : lb_remove sb ((bptr, bcap) :: (sb, scap) :: LBo) = (bptr, bcap) :: LBo) by (cbn [lb_remove fst]; rewrite (proj2 (Z.eqb_neq bptr sb) NE), Z.eqb_refl; reflexivity).
          rewrite RM in HP, HH2 |- *.
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (HagE2 : env_agree GT.NF E0 E2).
          { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
          split; [rewrite (DEN1 E' HagE'); apply incl_refl|]. split.
          { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (EVar 10, 248, ELit 24). split; [left; reflexivity|].
            unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite W10. rewrite u64_of_Z by (clear; lia). clear - Hin. lia. }
          split.
          { intros w a [<-|[]] Hin (Ka & Kc & Kw). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply (Kw (P, 272)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. clear - Hin. lia. }
          split; [unfold CHA.curB; rewrite Y4, (DEN1 E2 HagE2); exact HH2|]. split; [reflexivity|]. split; [exact I|].
          intros X0 HX0 _. unfold PDA.STAT in HX0. cbn [In] in HX0.
          destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity). } }
      destruct (Z.eqb_spec pc PDA.PC_OPDEL) as [->|Hne2]; [|discriminate X].
      {
        apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X Y4]. apply andb_prop in X as [X Y3].
        apply andb_prop in X as [X Y2]. apply andb_prop in X as [Y0 Y1].
        apply Z.eqb_eq in Y0. apply Nat.eqb_eq in Y1, Y2. subst i j. apply CH2.blocks_eqb_eq in Y3, Y4.
        lazymatch type of Y5 with PDA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA _].
        assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
        assert (HcB : CHA.curB LBo G.BLS 1 E = (bptr, bcap) :: LBo) by (unfold CHA.curB; rewrite Y3, (DEN1 E HagE); reflexivity).
        assert (HcF : CHA.curF FF sp PDA.FFS 1 E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE PDA.PC_OPDEL 4096 0%nat [] [] PDA.NEWS2 None 0 1%nat c ps0 2%nat cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, Y3, Y4; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
        assert (FZ : forall n, (n <? 40)%nat = true -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 HagE'); apply Nat.ltb_lt; exact Hn).
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        unfold PDA.bptrE in *.
        eexists. eexists. split; [exact (OPDEL_OK ((bptr, bcap) :: LBo) FF LK1 cr A1 bptr bcap (sp + CH2.ci_csp ci) (CC.cp_pc cj))|]. split.
        { unfold PMSA.a0. split; [|left; reflexivity].
          replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
          rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ HLFv Y10). cbn [edenot]. rewrite (FZ 35%nat eq_refl). exact V35. }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (-> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          assert (RM : lb_remove bptr ((bptr, bcap) :: LBo) = LBo) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
          rewrite RM in HP, HH2 |- *.
          exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          split; [cbn [CH2.den map app]; apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
          split; [unfold CHA.curB; rewrite Y4; cbn [CH2.den map app]; exact HH2|]. split; [reflexivity|]. split; [exact I|].

          intros X0 HX0 _. unfold PDA.NEWS2, PDA.STAT in HX0. cbn [In app] in HX0.
          destruct HX0 as [<-|[<-|[<-|[]]]]; [apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity
                                          | apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity |].
          destruct (ISH _ _ _ _ _ _ _ HH2 PDA.SLOT 8 ltac:(rewrite ILO; unfold PDA.SLOT; clear; lia) ltac:(rewrite IHI; unfold PDA.SLOT; clear; lia) ltac:(clear; lia) POI) as [BZ BA].
          assert (ISX : in_shadow_of PDA.SLOT 8 PDA.IMGSH) by (unfold in_shadow_of, S, PDA.SLOT, PDA.IMGSH, SB; clear; split; reflexivity).
          unfold PDA.IMGK. eapply CL5A.kword8_intro with (A := PDA.IMGSH) (z := 0); [reflexivity | unfold PDA.IMGSH; clear; lia | unfold PDA.IMGSH; clear; lia | reflexivity | clear; lia |].
          apply (CL5A.u8_vis (hl_segs L)); [unfold PDA.IMGSH; clear; lia | unfold PDA.IMGSH; clear; lia | | apply CL5A.byte_at_u8; exact (BZ _ ISX)].
          intros k Hk. replace (PDA.IMGSH + k) with PDA.IMGSH by (clear - Hk; lia). apply CHA.vis_allowed. exact (BA _ ISX). } }
    +
      apply andb_prop in X as [X Y3]. apply andb_prop in X as [X Y1]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Y0 Xbase].
      apply Z.eqb_eq in Y0. subst pc. apply Nat.eqb_eq in Y1. subst i. apply CH2.blocks_eqb_eq in Y3.
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA _].
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LBo FF LK sp G.HDECL WW WW G.BLS PDA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok PDA.RETPC 2%nat c ps0 _ Xbase _ (FFSnil 2%nat) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
        [rewrite LS; exact PDA.ret_at | rewrite FFSnil, Y3; exact Xfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (HB : CHA.curB LBo G.BLS 2 E = LBo) by (unfold CHA.curB; rewrite Y3; reflexivity). rewrite HB in HH1.
      rewrite SCRV in HP.
      apply (Hcont fx' R' M' model2 LBo cr LBo WW LK1 A1 HFP); [repeat split; reflexivity | exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
  - reflexivity.
  -
    set (LBf := (bptr, bcap) :: (sb, scap) :: LBo) in *.
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LBf FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) P 272).
    { intros k Hk. destruct (CL5A.infr_wok L ar LBf FF sp 0 P 272 (P + k) RFx Pfr ltac:(clear - Hk; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VSO : forall j, 0 <= j < 34 -> ahid A model (Z_to_bv 64 (S P + j)) = false).
    { intros j Hj. destruct (CL5A.infr_sh_wok L ar LBf FF sp 0 P 272 (S P + j) RFx Pfr ltac:(clear; lia) (CL5A.shreg_in_shadow P 34 (S P + j) P8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia))) as (G1 & G2 & G3).
      exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VST : ahid A model (Z_to_bv 64 (S (sp - 32))) = false).
    { destruct (TSH (S (sp - 32)) ltac:(unfold S; clear; lia)) as (G1 & G2 & G3). exact (CLV 0 _ G1 ltac:(do 4 right; left; exact G2) ltac:(intros _; exact G3)). }
    assert (VS : CL5A.visr (ahid A model) (sp - 4272) 4272).
    { intros k Hk. apply (CLV 0); [clear - Hk S2 S3 CL SP1; lia | right; left; split; [clear - Hk S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LBf FF _ RFx). unfold BIGSHADOW_HI. clear - Hk S2 CL. lia. }
    set (Mv := CCA.vis A model M).
    assert (UBC0 : elenZ E0 (EAlu Instr.ALU_ADD (EVar 36) (ELit (-1))) = bcap) by (unfold elenZ; apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - B0 B3 B4 SP1; lia]).
    assert (DO : L5.defined Mv P 272) by (apply (CL5A.defined_vis _ M P 272 VO); exact PDEF).
    assert (DS : L5.defined Mv (sp - 4272) 4272) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (U8V : forall k v, 0 <= k -> k < 272 -> L5.u8_at (hl_segs L) M (P + k) v -> L5.u8_at (hl_segs L) Mv (P + k) v).
    { intros k v K0 K1 Hk. apply (CL5A.u8_vis (hl_segs L)); [clear - O3 K0; lia | clear - O6 K1; lia | exact (CL5A.visr_sub _ P 272 (P + k) 1 VO ltac:(clear - K0; lia) ltac:(clear - K1; lia)) | exact Hk]. }
    assert (U64V : forall k v, 0 <= k -> k + 8 <= 272 -> L5.u64_at (hl_segs L) M (P + k) v -> L5.u64_at (hl_segs L) Mv (P + k) v).
    { intros k v K0 K1 Hk. apply (CL5A.u64_vis (hl_segs L)); [clear - O3 K0; lia | clear - O6 K1; lia | exact (CL5A.visr_sub _ P 272 (P + k) 8 VO ltac:(clear - K0; lia) ltac:(clear - K1; lia)) | exact Hk]. }
    assert (LB1 : ((bcap + 1) / 2 ^ (8 * Z.of_nat 0)) mod 2 ^ (8 * Z.of_nat 1) mod 2 ^ 1 = 1).
    { change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. rewrite Z.pow_0_r, Z.div_1_r.
      clear - Pbcap8 Pbcap. apply Z.mod_divide in Pbcap8; [|lia]. destruct Pbcap8 as [q Hq].
      pose proof (Z.div_mod q 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound q 32 ltac:(lia)) as Bq.
      rewrite <- (Z.mod_unique (bcap + 1) (2 ^ 8) (q / 32) (8 * (q mod 32) + 1)) by lia.
      symmetry. apply (Z.mod_unique _ (2 ^ 1) (4 * (q mod 32)) 1); lia. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok. cbn [CC.cp_know G.cp0]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5A.kword8_intro with (A := P + 24) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia | exact (U8V 24 0 ltac:(clear; lia) ltac:(clear; lia) (proj1 (proj2 S24)))].
    + eapply CL5A.kword8_intro with (A := P + 48) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia | exact (U8V 48 0 ltac:(clear; lia) ltac:(clear; lia) (proj1 (proj2 S48)))].
    + eapply CL5A.kword8_intro with (A := P + 72) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia | exact (U8V 72 0 ltac:(clear; lia) ltac:(clear; lia) (proj1 (proj2 S72)))].
    + eapply CL5.kword64_intro with (A := P + 96) (z := 1364920); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 96 _ ltac:(clear; lia) ltac:(clear; lia) P96)].
    + eapply CL5.kword64_intro with (A := P + 128) (z := P + 96); [ev0 | clear - O3; lia | clear - O6; lia | | exact (U64V 128 _ ltac:(clear; lia) ltac:(clear; lia) P128)].
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia].
    + eapply CL5.kword64_intro with (A := P + 224) (z := bcap + 1); [ev0 | clear - O3; lia | clear - O6; lia | exact V36 | exact (U64V 224 _ ltac:(clear; lia) ltac:(clear; lia) P224)].
    + eapply CL5.kword64_intro with (A := P + 240) (z := bptr); [ev0 | clear - O3; lia | clear - O6; lia | exact V35 | exact (U64V 240 _ ltac:(clear; lia) ltac:(clear; lia) P240)].
    +
      cbn [kentry_ok]. rewrite (AX2S.u_and_mask E0 _ 1 1 ltac:(clear; lia) eq_refl). cbn [edenot]. rewrite (proj1 (AX2S.u_ext_zx 0 1 (ev E0 36))). rewrite U36. rewrite LB1. clear; lia.
    + eapply CL5.krange_intro with (v := bcap + 1); [lin_eval; rw_atoms; clear; lia | clear - B0 B3 B4 SP1; lia | clear - Pbcap B0 B3 B4 SP1; lia].
    + eapply CL5.kword64_intro with (A := P + 248) (z := sb); [ev0 | clear - O3; lia | clear - O6; lia | exact V32 | exact (U64V 248 _ ltac:(clear; lia) ltac:(clear; lia) P248)].
    + eapply CL5.kword64_intro with (A := P + 256) (z := sb + slen); [ev0 | clear - O3; lia | clear - O6; lia | | exact (U64V 256 _ ltac:(clear; lia) ltac:(clear; lia) P256)].
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q5 Q7 Pslen SLEN0; lia].
    + eapply CL5.kword64_intro with (A := P + 264) (z := sb + scap); [ev0 | clear - O3; lia | clear - O6; lia | | exact (U64V 264 _ ltac:(clear; lia) ltac:(clear; lia) P264)].
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - Q5 Q7 Q3; lia].
    + eapply CL5.kunk_intro with (A := P) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | intros k Hk; apply DO; clear - Hk; lia].
    + eapply CL5.kunk_intro with (A := P + 232) (N := 8); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | intros k Hk; replace (P + 232 + k) with (P + (232 + k)) by (clear; lia); apply DO; clear - Hk; lia].
    + eapply CL5.kwr_intro with (A := P) (N := 272); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := P); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO CL SP1; lia].
    + eapply CL5.kalign_intro with (v := P); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact P8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 34 P); [exact U10 | clear; lia | clear - O3 O6; lia |].
      intros j Hj. apply CL5A.byte_vis; [exact (VSO j Hj) | exact (Psh j Hj)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := P) (N2 := 272); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.krange_intro with (v := sb); [lin_eval; rw_atoms; clear; lia | clear - Q5 Q7 Q3; lia | clear - QHI Q4 Q3 SP1; lia].
    + eapply CL5.kalign_intro with (v := sb); [lin_eval; rw_atoms; clear; lia | clear - Q5 Q7 Q3; lia | clear; lia | exact Q16].
    + eapply CL5.krange_intro with (v := scap); [lin_eval; rw_atoms; clear; lia | clear - Hscap; lia | clear - Hscap; lia].
    + eapply CL5.krange_intro with (v := slen); [lin_eval; rw_atoms; clear; lia | clear - Pslen SLEN0 Hscap; lia | clear - Pslen SLEN0 Hscap; lia].
    + eapply CL5.krange_intro with (v := scap - slen); [lin_eval; rw_atoms; clear; lia | clear - Pslen SLEN0 Hscap; lia | clear - Pslen SLEN0 Hscap; lia].
    + eapply CL5.krange_intro with (v := bptr); [lin_eval; rw_atoms; clear; lia | clear - B5 B7 B3; lia | clear - B0 B4 B3 SP1; lia].
    + eapply CL5.kalign_intro with (v := bptr); [lin_eval; rw_atoms; clear; lia | clear - B5 B7 B3; lia | clear; lia | exact B16].
    + eapply CL5.kunk_intro with (A := sp - 4272) (N := 4272); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4272) (N := 4272); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv _ 1 (sp - 32)); [unfold CL5A.uv; exact UT0 | clear; lia | clear - S2 S3 CL SP1; lia |].
      intros j Hj. assert (j = 0) by (clear - Hj; lia). subst j. apply CL5A.byte_vis; [rewrite Z.add_0_r; exact VST | rewrite Z.add_0_r; exact Htsh].
    + eapply CL5.kdisj_intro with (A1 := sp - 4272) (N1 := 4272) (A2 := P) (N2 := 272); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4272) (N1 := 4272) (A2 := sb) (N2 := scap); [ev0 | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U34 | clear - Q4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := P) (N1 := 272) (A2 := sb) (N2 := scap); [ev0 | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U34 | unfold hid in QFP; clear - QFP F01 F02; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4272) (N1 := 4272) (A2 := bptr) (N2 := bcap); [ev0 | reflexivity | ev0 | exact UBC0 | clear - B4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := P) (N1 := 272) (A2 := bptr) (N2 := bcap); [ev0 | reflexivity | ev0 | exact UBC0 | unfold hid in BFP; clear - BFP F01 F02; lia].
    + eapply CL5.kdisj_intro with (A1 := sb) (N1 := scap) (A2 := bptr) (N2 := bcap); [ev0 | unfold elenZ; cbn [edenot]; exact U34 | ev0 | exact UBC0 | unfold hid in BQ; clear - BQ; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := sb) (N2 := scap); [reflexivity | reflexivity | ev0 | unfold elenZ; cbn [edenot]; exact U34 | unfold hid in Q6; clear - Q6; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := bptr) (N2 := bcap); [reflexivity | reflexivity | ev0 | exact UBC0 | unfold hid in B6; clear - B6; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 G.BLS []) with PDA.BLK0. rewrite (DEN0 E0 (CC.env_agree_refl _ _)), FFSnil. cbn [app CHA.denF map length].
      split; [exact HH|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + exact HSHC.
  - exact Hfp.
Qed.

End ParserDtorOk.
