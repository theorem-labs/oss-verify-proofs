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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCA TopSpecsCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_xsgetn_casan_T Cut_xsgetn_casan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_xsgetn_casan.
Module GT := Cut_xsgetn_casan_T.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.

Module XSA.
Definition PC_MM : Z := 519788.
Definition RETPC : Z := 1007368.
Definition SBz : Z := 2147450880.
Definition sbE := EVar 10. Definition dstE := EVar 11. Definition gE := EVar 32. Definition avE := EVar 33.
Definition ADDE (a b : expr) : expr := EAlu Instr.ALU_ADD a b.
Definition BLK0 : list (expr * expr) := [(dstE, ELit 16384)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1427896) 8 (ELit SBz)].
Definition CPF : list SGP.region := [(EVar 2, -2624, ELit 2624); (sbE, 24, ELit 8)].

Definition CNT (j : nat) : expr := if Nat.eqb j 1 then ELit 16384 else avE.
Definition CRNG (j : nat) : kentry := if Nat.eqb j 1 then KRange avE 16385 67108864 else KRange avE 1 16384.

Definition SLTUF : expr := EAlu Instr.ALU_SLTU gE (ADDE gE avE).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition has := CC.has_cell.

Definition ek1 (ps : SR.post_spec) : bool := (CL.ps_reg_is ps 10 (ELit 0) && has (SR.ps_cells ps) (KWord (SA sbE 24) 8 gE) && has (SR.ps_cells ps) (KRange SLTUF 0 0))%bool.
Definition ek2 (ps : SR.post_spec) : bool := (CL.ps_reg_is ps 10 (ELit 16384) && has (SR.ps_cells ps) (KWord (SA sbE 24) 8 (ADDE gE (ELit 16384))) && has (SR.ps_cells ps) (KRange avE 16385 67108864))%bool.
Definition ek3 (ps : SR.post_spec) : bool := (CL.ps_reg_is ps 10 avE && has (SR.ps_cells ps) (KWord (SA sbE 24) 8 (ADDE gE avE)) && has (SR.ps_cells ps) (KRange avE 1 16383))%bool.
Definition ek4 (ps : SR.post_spec) : bool := (CL.ps_reg_is ps 10 (ELit 16384) && has (SR.ps_cells ps) (KWord (SA sbE 24) 8 (ADDE gE avE)) && has (SR.ps_cells ps) (KRange avE 16384 16384))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      let cells := SR.ps_cells ps in
      (CH2.blocks_eqb (nth i G.BLS []) BLK0 && CHA.foot_chk GT.NF G.HDECL c BLK0 [] && CBA.regions_eqb (CC.cp_F c) CPF && Nat.leb 34 (CC.cp_nx c) &&
      match CH2.ret_of G.RETS i k with
      | Some j =>
          match nth_error G.CPS j with
          | Some cj =>
              (Z.eqb pc PC_MM && Z.eqb (SR.ps_pc ps) PC_MM && Nat.eqb i 0 && (Nat.eqb j 1 || Nat.eqb j 2) && CH2.blocks_eqb (nth j G.BLS []) BLK0
               && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 BLK0 [] [(dstE, 0, CNT j)] STAT (Some dstE) c ps cj BLK0 [] BLK0 [])
               && CL.ps_reg_is ps 10 dstE && CL.ps_reg_is ps 11 gE && CL.ps_reg_is ps 12 (CNT j) && has cells (CRNG j) && has cells (KWord (SA sbE 24) 8 gE))%bool
          | None => false
          end
      | None => (Z.eqb pc RETPC && CBA.exit_base_chk GT.NF RETPC c ps && (ek1 ps || ek2 ps || ek3 ps || ek4 ps))%bool
      end)%bool
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RETPC.
Proof. CL.solve_is_ret. Qed.
End XSA.

Section XsgetnOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Abbreviation IC := PMLA.C_casan.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis MEMMOVE_LIBC : amemcpy_spec_at L ar SCFG HI XSA.PC_MM false.

Lemma FFSnil : forall i, nth i XSA.FFS [] = [].
Proof. intros i. unfold XSA.FFS. do 3 (destruct i as [|i]; [reflexivity|]). destruct i; reflexivity. Qed.
Lemma BLSi : forall i, (i <= 2)%nat -> nth i G.BLS [] = XSA.BLK0.
Proof. intros i Hi. do 3 (destruct i as [|i]; [reflexivity|]). exfalso. lia. Qed.
Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.
Lemma est0 : forall E k, 0 <= k -> estart E (SA (ELit 0) k) = k.
Proof. intros E k Hk. unfold estart. cbn [a_base a_off edenot]. rewrite u64_of_Z by lia. lia. Qed.
Lemma elit : forall E k, 0 <= k < 2 ^ 64 -> elenZ E (ELit k) = k.
Proof. intros E k Hk. unfold elenZ. cbn [edenot]. apply u64_of_Z. exact Hk. Qed.

Lemma u32_u8_low : forall (M : mem) a w, 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at (hl_segs L) M a w -> L5.u8_at (hl_segs L) M a (w mod 256).
Proof.
  intros M a w Ha Ha4 H. unfold L5.u32_at, L5.u8_at, cell_is in *.
  assert (EQ : forall x k, rdn (hl_segs L) M x (Datatypes.S k) = match (match M x with Some b => Some b | None => seg_rom (hl_segs L) x end) with
                 | Some b => match rdn (hl_segs L) M (x + 1)%bv k with Some rest => Some (b :: rest) | None => None end | None => None end) by reflexivity.
  rewrite (EQ _ 3%nat) in H. rewrite (EQ _ 0%nat). cbn [rdn].
  destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom (hl_segs L) (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
  destruct (rdn (hl_segs L) M (Z_to_bv 64 a + 1)%bv 3) as [rest|] eqn:ER; [|discriminate].
  unfold word_to_le_bytes in H. cbn [Z_to_le_bytes] in H. injection H as H1 H2. f_equal. f_equal. rewrite H1. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  replace (2 ^ 64) with (256 * 2 ^ 56) by reflexivity. rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Theorem xsgetn_ok : TPSA.xsgetn_specA L ar HI IC 1007104.
Proof.
  unfold TPSA.xsgetn_specA. intros LB FF LK cr A IS ch gp rdst sp r rep. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs (Ha0 & Ha1 & Ha2 & ISRC & SSH & RO & LEN & (Ifr & I8 & Ish) & HinLB & CSH & CDEF & SBLK & Hstksh) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, TPSA.XSGETN_SCR, PMSA.MEM_SCR, PMSA.fobj, PMSA.stksh, PMLA.stksh in *. change (64 + 2560) with 2624 in *.
  pose proof ISRC as ISRC0. unfold PMLA.isrc_at in ISRC0. cbv zeta in ISRC0.
  remember (PML.srep_data (IS + 80) rep) as D eqn:HD. remember (Z.of_nat (length (PML.srep_chars rep))) as n eqn:HN.
  destruct ISRC0 as (I0 & I16 & I24 & I32 & I40 & I48 & GRNG & I56 & I64 & I72 & STR & I104 & I112 & I120 & IOSB & RDST & IDEF).
  change (PMLA.VT_STRINGBUF IC) with 1379512 in I16.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYHN : hl_img_lo L <= 65536 /\ 7024640 <= hl_img_hi L) by (rewrite ILO, IHI; clear; lia).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM.

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (ch, 16384) HinLB) as (BR & Bdef & Bsa & Bap & Bfap). cbn [fst snd] in BR, Bdef, Bsa, Bap, Bfap.
  destruct BR as (B0 & B1 & B16 & B3 & B4 & (B5 & B6 & B7)).
  destruct (CHA.wf_nodup _ _ _ _ _ _ _ _ WF) as (ND1 & ND2).
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (CSP : ahl_ceil ar <= sp) by (clear - S2; lia).
  destruct (CL5A.infr_rng L ar _ FF IS 272 RFx Ifr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  change (hid (IS + 272 <= 2147446784 \/ 17594333495296 <= IS)) in O5. change (hid (IS + 272 <= hl_img_lo L \/ hl_img_hi L <= IS)) in O7.
  change (hid (ch + 16384 <= 2147446784 \/ 17594333495296 <= ch)) in B6. change (hid (ch + 16384 <= hl_img_lo L \/ hl_img_hi L <= ch)) in B1.
  assert (SHR : forall p k a, 0 <= p -> 0 < k -> p + k <= 2 ^ 47 -> in_shadow_of p k a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.
  destruct Ifr as (f0 & Hf0 & F01 & F02).
  assert (Ifr : CL5A.ainfr FF IS 272) by (exists f0; split; [exact Hf0 | split; [exact F01 | exact F02]]).
  pose proof (Bfap f0 (in_or_app _ _ _ (or_introl Hf0))) as BFP. change (hid (ch + 16384 <= ff_addr f0 \/ ff_addr f0 + ff_bytes (ff_class f0) <= ch)) in BFP.
  assert (APIC : IS + 272 <= ch \/ ch + 16384 <= IS) by (unfold hid in BFP; clear - BFP F01 F02; lia).
  assert (B8 : ch mod 8 = 0) by exact (CHA.mod8_of_16 _ B16).
  assert (RFr : CHA.rng_facts L ar (lb_remove ch LB) FF).
  { apply (CHA.rng_incl L ar LB FF); [exact RFx | intros y Hy; exact (L5C.in_lb_remove ch y LB Hy) | apply incl_refl]. }

  assert (NRNG : 0 <= n < 2 ^ 26) by (clear - LEN HN; lia).
  set (av := D + n - gp).
  assert (AVR : 0 <= av <= n) by (subst av; clear - GRNG; lia).

  assert (TB : match rep with PML.SShort s => D = IS + 81 /\ n <= 22
               | PML.SLong cap p s => D = p /\ In (p, cap) (lb_remove ch LB) /\ n < cap /\ cap mod 8 = 0 /\ 4096 <= p /\ p + cap <= ahl_ceil ar /\ p mod 16 = 0 /\
                                      (p + cap <= 2147446784 \/ 17594333495296 <= p) /\ p + cap <= 2 ^ 47 /\ (p + cap <= ch \/ ch + 16384 <= p) /\
                                      (p + cap <= hl_img_lo L \/ hl_img_hi L <= p) /\ HeapIface.defined M p cap /\ shadow_blk M p cap end).
  { destruct rep as [s|cap p s].
    - rewrite HD, HN. cbn [PML.srep_chars PML.srep_data]. destruct STR as (SL & _). clear - SL. lia.
    - destruct (SBLK (p, cap) (or_introl eq_refl)) as [PinLB Pne]. cbn [fst] in Pne.
      destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (p, cap) PinLB) as (PR & Pdef & Psa & Pap & Pfap). cbn [fst snd] in PR, Pdef, Psa, Pap, Pfap.
      destruct PR as (P0 & P1 & P16 & P3 & P4 & (P5 & P6 & P7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in P6.
      destruct STR as (_ & PC8 & PLT). rewrite HD, HN. cbn [PML.srep_chars PML.srep_data].
      split; [reflexivity|]. split; [exact (L5C.in_lb_remove_neq ch p cap LB PinLB Pne)|]. split; [exact PLT|]. split; [exact PC8|]. split; [exact P0|]. split; [exact P4|]. split; [exact P16|].
      split; [exact P6|]. split; [exact P7|]. split; [|split; [exact P1 | split; [exact Pdef | exact SSH]]].
      destruct (Pap (ch, 16384) (L5C.in_lb_remove_neq p ch 16384 LB HinLB ltac:(clear - Pne; congruence))) as [X|X]; cbn [fst snd] in X; [left | right]; exact X. }
  assert (DRNG : 0 <= D /\ D + n + 1 <= 2 ^ 47 /\ (D + n + 1 <= 2147446784 \/ 17594333495296 <= D) /\ (D + n <= ch \/ ch + 16384 <= D)).
  { destruct rep as [s|cap p s].
    - destruct TB as (-> & N22). unfold hid in O5. clear - O3 O6 O5 N22 NRNG APIC. lia.
    - destruct TB as (-> & _ & LT & _ & P0 & _ & _ & P6 & P7 & PAC & _). clear - LT P0 P6 P7 PAC NRNG. lia. }
  assert (DTOP : D + n <= ahl_ceil ar).
  { destruct rep as [s|cap p s]; [destruct TB as (TD & N22); clear - TD N22 O4; lia | destruct TB as (TD & _ & LT & _ & _ & P4 & _); clear - TD LT P4; lia]. }

  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [gp; av] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 (IS + 16)) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 ch) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 16384) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 gp) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 av) by reflexivity.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
  assert (U10 : bv_unsigned (ev E0 10) = IS + 16) by (rewrite V10; apply u64_of_Z; clear - O3 O6; lia).
  assert (U11 : bv_unsigned (ev E0 11) = ch) by (rewrite V11; apply u64_of_Z; clear - B5 B7; lia).
  assert (U32 : bv_unsigned (ev E0 32) = gp) by (rewrite V32; apply u64_of_Z; clear - GRNG DRNG; lia).
  assert (U33 : bv_unsigned (ev E0 33) = av) by (rewrite V33; apply u64_of_Z; clear - AVR NRNG; lia).

  assert (SCRV : CH.hd_scr G.HDECL = 2624) by reflexivity.
  assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia). assert (NF34 : GT.NF = 34%nat) by reflexivity.
  set (WW := [(IS + 40, 8)] : list L5.range).
  assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
            0 <= a < 2 ^ 64 /\ aclientw L ar (lb_remove ch LB) FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar (lb_remove ch LB) FF sp _ IS 272 a RFr Ifr ltac:(clear - Hin; lia)). }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (IS + 40, 8). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar (lb_remove ch LB) FF sp G.HDECL a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
    destruct (CL5A.infr_wok L ar (lb_remove ch LB) FF sp (CH.hd_scr G.HDECL) IS 272 a RFr Ifr ltac:(clear - Ha; lia)) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
  assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
  { intros rg a [<-|[<-|[]]] Ha; cbn [fst snd] in Ha; rewrite ILO, IHI; (split; [clear - Ha; lia|]); intros Hs; pose proof (L5A.aly_static_lo L C LAY a Hs); clear - Ha H; lia. }
  assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
  assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
  { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; lia]. }
  assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
  { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

  set (PZB := fun a : Z => match rep with PML.SShort _ => False | PML.SLong cap p _ => (p <= a < p + cap) \/ in_shadow_of p cap a end).
  assert (AKO : forall a, IS <= a < IS + 272 -> ~ (IS + 40 <= a < IS + 48) -> CHA.akept L ar (lb_remove ch LB) FF sp 2624 WW a).
  { intros a Ha Hn. split; [clear - Ha O3 O6; lia|]. split; [apply aclientw_client; exact (CL5A.infr_clientw L ar _ FF sp _ IS 272 a Ifr Ha)|].
    intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hr Hn. lia. }
  assert (AKS : forall a, in_shadow_of IS 272 a -> CHA.akept L ar (lb_remove ch LB) FF sp 2624 WW a).
  { intros a Ha. pose proof (SHR IS 272 a O3 ltac:(clear; lia) O6 Ha) as SRa. split; [clear - SRa; lia|].
    split; [apply aclientw_client; exact (CL5A.infr_sh_clientw L ar _ FF sp _ IS 272 a Ifr ltac:(clear; lia) Ha)|].
    intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold hid in O5. clear - Hr SRa O5. lia. }
  assert (AKB : forall a, PZB a -> CHA.akept L ar (lb_remove ch LB) FF sp 2624 WW a).
  { subst PZB. destruct rep as [s|cap p s]; [intros a []|]. destruct TB as (_ & PinR & LT & PC8 & P0 & P4 & P16 & P6 & P7 & PAC & P1 & _).
    assert (PAI : p + cap <= IS \/ IS + 272 <= p).
    { destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (p, cap) (L5C.in_lb_remove ch _ LB PinR)) as (_ & _ & _ & _ & Pfap). cbn [fst snd] in Pfap.
      pose proof (Pfap f0 (in_or_app _ _ _ (or_introl Hf0))) as X. clear - X F01 F02. lia. }
    intros a [Ha|Ha].
    - split; [clear - Ha P0 P7; lia|]. split; [left; exists (p, cap); split; [exact PinR | cbn [fst snd]; exact Ha]|].
      intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hr Ha PAI. lia.
    - pose proof (SHR p cap a ltac:(clear - P0; lia) ltac:(clear - LT NRNG; lia) P7 Ha) as SRa. split; [clear - SRa; lia|]. split; [do 6 right; exists (p, cap); split; [exact PinR | cbn [fst snd]; exact Ha]|].
      intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold hid in O5. clear - Hr SRa O5. lia. }

  assert (TRANS : forall (My : mem) g', (forall a, CHA.akept L ar (lb_remove ch LB) FF sp 2624 WW a -> My (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
            L5.u64_at (hl_segs L) My (IS + 40) g' -> D <= g' <= D + n -> L5.defined My IS 272 ->
            PMLA.isrc_at (hl_segs L) IC My IS rep g' rdst /\ PMLA.srep_sh My rep /\ shadow_zero My IS 34).
  { intros My g' AG G40 GR DEF'.
    assert (OO : forall k w, 0 <= k -> k + w <= 272 -> (k + w <= 40 \/ 48 <= k) -> PTA.out (CHA.akept L ar (lb_remove ch LB) FF sp 2624 WW) (IS + k) w).
    { intros k w K0 K1 K2. split; [clear - K0 O3; lia|]. split; [clear - K1 O6; lia|]. intros i Hi. apply AKO; clear - Hi K0 K1 K2; lia. }
    assert (U64T : forall k v, 0 <= k -> k + 8 <= 272 -> (k + 8 <= 40 \/ 48 <= k) -> L5.u64_at (hl_segs L) M (IS + k) v -> L5.u64_at (hl_segs L) My (IS + k) v).
    { intros k v K0 K1 K2 Hv. exact (PTA.u64_ag (hl_segs L) M My _ AG (IS + k) v (OO k 8 K0 K1 K2) Hv). }
    assert (U32T : forall k v, 0 <= k -> k + 4 <= 272 -> (k + 4 <= 40 \/ 48 <= k) -> L5.u32_at (hl_segs L) M (IS + k) v -> L5.u32_at (hl_segs L) My (IS + k) v).
    { intros k v K0 K1 K2 Hv. exact (PTA.u32_ag (hl_segs L) M My _ AG (IS + k) v (OO k 4 K0 K1 K2) Hv). }
    split; [|split].
    - unfold PMLA.isrc_at. cbv zeta. rewrite <- HD, <- HN.
      split; [replace IS with (IS + 0) by (clear; lia); apply (U64T 0); [clear; lia | clear; lia | clear; lia | rewrite Z.add_0_r; exact I0]|].
      split; [exact (U64T 16 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I16)|]. split; [exact (U64T 24 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I24)|].
      split; [exact (U64T 32 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I32)|]. split; [exact G40|].
      split; [exact (U64T 48 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I48)|]. split; [exact GR|].
      split; [exact (U64T 56 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I56)|]. split; [exact (U64T 64 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I64)|].
      split; [exact (U64T 72 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I72)|].
      split.
      { subst PZB. destruct rep as [s|cap p s].
        - destruct TB as (_ & N22). destruct STR as (SL & SH0 & SBY & SNUL). unfold PMLA.str_at. split; [exact SL|].
          split; [exact (PTA.u8_ag (hl_segs L) M My _ AG (IS + 80) _ (OO 80 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) SH0)|].
          split; [replace (IS + 80 + 1) with (IS + 81) in SBY |- * by (clear; lia); exact (PTA.bytes_ag (hl_segs L) M My _ AG (IS + 81) s (OO 81 (Z.of_nat (length s)) ltac:(clear; lia) ltac:(rewrite HN in N22; cbn [PML.srep_chars] in N22; clear - N22; lia) ltac:(clear; lia)) SBY)|].
          replace (IS + 80 + 1 + Z.of_nat (length s)) with (IS + (81 + Z.of_nat (length s))) in SNUL |- * by (clear; lia).
          exact (PTA.u8_ag (hl_segs L) M My _ AG _ _ (OO (81 + Z.of_nat (length s)) 1 ltac:(clear; lia) ltac:(rewrite HN in N22; cbn [PML.srep_chars] in N22; clear - N22; lia) ltac:(clear; lia)) SNUL).
        - destruct TB as (_ & PinR & LT & PC8 & P0 & P4 & P16 & P6 & P7 & PAC & P1 & _).
          apply (PTA.str_long_ag (hl_segs L) M My _ AG (IS + 80) cap p s (OO 80 24 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))); [|exact STR].
          split; [clear - P0; lia|]. split; [clear - P7; lia|]. intros i Hi. apply AKB. left. exact Hi. }
      split; [exact (U64T 104 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I104)|]. split; [exact (U32T 112 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I112)|].
      split; [exact (U64T 120 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) I120)|].
      split.
      { destruct IOSB as (J32 & J36 & J40 & J48 & JZ & JDEF). unfold PMLA.iosb_at.
        replace (IS + 120 + 32) with (IS + 152) in J32 |- * by (clear; lia). replace (IS + 120 + 36) with (IS + 156) in J36 |- * by (clear; lia).
        replace (IS + 120 + 40) with (IS + 160) in J40 |- * by (clear; lia). replace (IS + 120 + 48) with (IS + 168) in J48 |- * by (clear; lia).
        split; [exact (U32T 152 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) J32)|]. split; [exact (U32T 156 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) J36)|].
        split; [exact (U64T 160 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) J40)|]. split; [exact (U64T 168 _ ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) J48)|].
        split; [intros k Hk; replace (IS + 120 + 56 + 8 * k) with (IS + (176 + 8 * k)) by (clear; lia); apply (U64T (176 + 8 * k)); [clear - Hk; lia | clear - Hk; lia | clear - Hk; lia | replace (IS + (176 + 8 * k)) with (IS + 120 + 56 + 8 * k) by (clear; lia); exact (JZ k Hk)]|].
        intros q Hq. replace (IS + 120 + q) with (IS + (120 + q)) by (clear; lia). apply DEF'. clear - Hq. lia. }
      split; [exact RDST | exact DEF'].
    - subst PZB. destruct rep as [s|cap p s]; [exact I|]. destruct TB as (_ & PinR & LT & PC8 & P0 & P4 & P16 & P6 & P7 & PAC & P1 & Pdef & PSH). unfold PMLA.srep_sh.
      apply (PTA.shadow_blk_ag M My _ AG p cap ltac:(clear - LT NRNG; lia)); [intros a Ha; apply AKB; right; exact Ha | exact (CHA.mod8_of_16 _ P16) | exact PSH].
    - apply (PTA.shadow_zero_ag M My _ AG IS 34); [|exact Ish]. intros j Hj. apply AKS. apply (CL5A.shreg_in_shadow IS 34); [exact I8 | clear; lia | unfold S in Hj |- *; clear - Hj; lia]. }

  set (Cred := fun (_ : nat) (_ : env) (cr1 : credit) => cr1 = cr).
  set (XI := fun (_ : nat) (_ : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) => shadow_blk M1 ch 16384).
  assert (NOGOTO : forall i c kk ps0 j sg, CH2.is_leaf G.CPS G.TAGS i c kk ps0 (CC.TGoto j sg) -> False).
  { intros i c kk ps0 j sg HIL. pose proof (CH2.leaves_all_sound _ _ _ XSA.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. discriminate X. }
  assert (DEN0 : forall E, env_agree GT.NF E0 E -> CH2.den E XSA.BLK0 = [(ch, 16384)]).
  { intros E HagE. unfold CH2.den, XSA.BLK0, XSA.dstE. cbn [map fst snd edenot]. rewrite <- (proj1 HagE 11%nat) by (apply Nat.ltb_lt; reflexivity). rewrite U11, u64_of_Z by (clear; lia). reflexivity. }

  assert (NOFOOTSH : forall c ps0 E' R' A1 (M1 : mem) m1 (M' : mem) m' a, CBA.regions_eqb (CC.cp_F c) XSA.CPF = true -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
      env_agree GT.NF E0 E' -> in_shadow_of ch 16384 a -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros c ps0 E' R' A1 M1 m1 M' m' a YF HLF HagE' Ha. apply CBA.regions_eqb_eq in YF. pose proof (SHR ch 16384 a B5 ltac:(clear; lia) B7 Ha) as SRa.
    apply (CCA.lfa_frame _ _ _ _ _ _ _ _ _ _ HLF (Z_to_bv 64 a)). rewrite YF. unfold XSA.CPF, SGP.outside.
    assert (Wsp : bv_unsigned (ev E' 2) = sp) by (rewrite <- (proj1 HagE' 2%nat) by (apply Nat.ltb_lt; reflexivity); exact U2).
    assert (WR : bv_unsigned (edenot E' XSA.sbE) = IS + 16) by (unfold XSA.sbE; cbn [edenot]; rewrite <- (proj1 HagE' 10%nat) by (apply Nat.ltb_lt; reflexivity); exact U10).
    constructor; [unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite Wsp; rewrite !u64_of_Z by (clear - SRa; lia); clear - SRa S2 CL; lia|].
    constructor; [unfold estart, elenZ; cbn [a_base a_off]; rewrite WR; cbn [edenot]; rewrite !u64_of_Z by (clear - SRa; lia); unfold hid in O5; clear - SRa O5; lia|]. constructor. }
  assert (CHNK : forall a, ch <= a < ch + 16384 \/ in_shadow_of ch 16384 a -> ~ CHA.akept L ar (lb_remove ch LB) FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha (Ka & Kc & Kw). rewrite SCRV in Kc.
    exact (CHA.obj_not_client L ar LYI (lb_remove ch LB) FF sp 2624 ch 16384 a RFr (conj B5 (conj B6 B7)) ltac:(clear; lia) B8 B4 B1 Bap (fun f Hf => Bfap f (in_or_app _ _ _ (or_introl Hf))) Ha Kc). }
  rewrite <- LS in FPM.
  change 1007104 with (CC.cp_pc G.cp0).
  eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A (lb_remove ch LB) FF LK sp G.HDECL WW WW G.BLS XSA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
            G.CPS K PMSA.fp_ok XI G.TAGS) with (i := 0%nat) (E := E0).
  - exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact XSA.heap_ok.
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  - intros i c kk ps0 j sg HIL. exfalso. exact (NOGOTO _ _ _ _ _ _ HIL).
  -
    intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ XSA.leaf_ok _ _ _ _ _ HIL) as X. unfold XSA.leaf_chk in X. cbv zeta in X.
    apply andb_prop in X as [X XK]. apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YFX]. apply andb_prop in X as [YB Yfoot].
    apply CH2.blocks_eqb_eq in YB. apply Nat.leb_le in Ynx.
    pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A (lb_remove ch LB) FF LK sp G.HDECL WW WW G.BLS XSA.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                  G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
    assert (UVE : forall E e z, env_agree GT.NF E0 E -> APC.expr_vars_lt GT.NF e = true -> CL5A.uv E0 e = z -> CL5A.uv E e = z).
    { intros E e z Hag Hv Hz. rewrite (CL5A.uv_agree GT.NF E0 E e Hag Hv). exact Hz. }
    destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret.
    +
      destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
      apply andb_prop in XK as [XK Yg]. apply andb_prop in XK as [XK Yrng]. apply andb_prop in XK as [XK Y12]. apply andb_prop in XK as [XK Y11]. apply andb_prop in XK as [XK Y10]. apply andb_prop in XK as [XK Y5].
      apply andb_prop in XK as [XK YBj]. apply andb_prop in XK as [XK Yj]. apply andb_prop in XK as [XK Yi]. apply andb_prop in XK as [Ypc Y0].
      apply Z.eqb_eq in Ypc, Y0. apply Nat.eqb_eq in Yi. subst pc i. apply CH2.blocks_eqb_eq in YBj.
      lazymatch type of Y5 with XSA.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.

      assert (HJ : (j = 1%nat /\ XSA.CNT j = ELit 16384 /\ XSA.CRNG j = KRange XSA.avE 16385 67108864) \/ (j = 2%nat /\ XSA.CNT j = XSA.avE /\ XSA.CRNG j = KRange XSA.avE 1 16384)).
      { apply orb_prop in Yj. destruct Yj as [Yj|Yj]; apply Nat.eqb_eq in Yj; subst j; [left | right]; repeat split; reflexivity. }
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      assert (HcB : CHA.curB (lb_remove ch LB) G.BLS 0 E = (ch, 16384) :: lb_remove ch LB) by (unfold CHA.curB; rewrite YB, (DEN0 E HagE); reflexivity).
      assert (HcF : CHA.curF FF sp XSA.FFS 0 E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
      refine (CALLEE XSA.PC_MM 2560 0%nat XSA.BLK0 [(XSA.dstE, 0, XSA.CNT j)] XSA.STAT (Some XSA.dstE) 0 0%nat c ps0 j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
        [rewrite !FFSnil, YB, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length]; clear; lia |].
      rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
      destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & Hdf1). rewrite SCRV in Hfr1.
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (CELL : forall X0, XSA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (proj1 (Forall_forall _ _) HK _ HX0). }
      assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
      { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (W11 : CL5A.uv E' XSA.dstE = ch) by exact (UVE E' XSA.dstE ch HagE' eq_refl U11).
      assert (W32 : CL5A.uv E' XSA.gE = gp) by (unfold CL5A.uv, XSA.gE; cbn [edenot]; rewrite <- (proj1 HagE' 32%nat) by (apply Nat.ltb_lt; reflexivity); exact U32).
      assert (W33 : CL5A.uv E' XSA.avE = av) by (unfold CL5A.uv, XSA.avE; cbn [edenot]; rewrite <- (proj1 HagE' 33%nat) by (apply Nat.ltb_lt; reflexivity); exact U33).

      set (cnt := CL5A.uv E' (XSA.CNT j)).
      assert (CNTR : 1 <= cnt <= 16384 /\ cnt <= av /\ getr R' 12%bv = Z_to_bv 64 cnt).
      { destruct HJ as [(Hj & HC & HR0)|(Hj & HC & HR0)]; rewrite HR0 in Yrng; pose proof (CELL _ Yrng) as RR; cbn [kentry_ok] in RR; change (bv_unsigned (edenot E' XSA.avE)) with (CL5A.uv E' XSA.avE) in RR; rewrite W33 in RR.
        - assert (Hc : cnt = 16384) by (subst cnt; rewrite HC; unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia).
          rewrite Hc. split; [clear; lia|]. split; [clear - RR; lia|]. rewrite <- Hc. exact (REG 12%nat _ cnt Y12 eq_refl).
        - assert (Hc : cnt = av) by (subst cnt; rewrite HC; exact W33).
          rewrite Hc. split; [clear - RR; lia|]. split; [clear; lia|]. rewrite <- Hc. exact (REG 12%nat _ cnt Y12 eq_refl). }
      destruct CNTR as (CN1 & CN2 & R12).

      assert (Hsh' : shadow_blk M' ch 16384).
      { apply (PTA.shadow_blk_ag M1 M' (in_shadow_of ch 16384)); [| clear; lia | intros a Ha; exact Ha | exact B8 | exact HXi].
        intros a Ha. exact (NOFOOTSH c ps0 E' R' A1 M1 m1 M' m' a YFX HLF HagE' Ha). }
      assert (DEFI' : L5.defined M' IS 272).
      { intros q Hq Hn0. apply (Hdf1 (IS + q)); [clear - Hq O3 O6; lia | apply aclientw_client; exact (CL5A.infr_clientw L ar _ FF sp _ IS 272 (IS + q) Ifr ltac:(clear - Hq; lia)) | exact (IDEF q Hq) | exact Hn0]. }
      assert (G40' : L5.u64_at (hl_segs L) M' (IS + 40) gp).
      { pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove ch LB) FF LK sp G.HDECL WW G.BLS XSA.FFS Cred 0 0%nat E A1 M' m' HA') as Hoff.
        apply (CL5A.u64_full (hl_segs L) _ Hoff). rewrite <- W32.
        exact (CL5A.kword64_elim (hl_segs L) E' _ _ XSA.gE (IS + 40) (CELL _ Yg) ltac:(unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' XSA.sbE)) with (CL5A.uv E' XSA.sbE); rewrite (UVE E' XSA.sbE (IS + 16) HagE' eq_refl U10); clear; lia)). }
      destruct (TRANS M' gp Hfr1 G40' GRNG DEFI') as (ISRC' & SSH' & ISH').

      assert (SRCDEF : L5.defined M' gp cnt).
      { subst PZB. destruct rep as [s|cap p s].
        - destruct TB as (TD & N22). intros q Hq. replace (gp + q) with (IS + (gp + q - IS)) by (clear; lia). apply DEFI'. subst av. clear - Hq TD N22 GRNG CN1 CN2 AVR. lia.
        - destruct TB as (TD & PinR & LT & _). destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1) (p, cap) (or_intror PinR)) as (_ & Pdef' & _). cbn [fst snd] in Pdef'.
          intros q Hq. replace (gp + q) with (p + (gp + q - p)) by (clear; lia). apply Pdef'. subst av. clear - Hq TD LT GRNG CN1 CN2 AVR. lia. }
      destruct (PTA.defined_bytes (hl_segs L) M' gp (Z.to_nat cnt) ltac:(rewrite Z2Nat.id by (clear - CN1; lia); exact SRCDEF)) as (bs & Lbs & BS).
      assert (SRCACC : aacc M' gp cnt).
      { subst PZB. destruct rep as [s|cap p s].
        - destruct TB as (TD & N22). apply (CRC.aacc_blk M' IS 272 gp cnt); [| exact I8 | exact O3 | subst av; clear - TD GRNG; lia | subst av; clear - TD N22 GRNG CN1 CN2 AVR; lia].
          split; [change (272 / 8) with 34; exact ISH' | intros Hm; exfalso; apply Hm; reflexivity].
        - destruct TB as (TD & PinR & LT & PC8 & P0 & P4 & P16 & _). apply (CRC.aacc_blk M' p cap gp cnt SSH' (CHA.mod8_of_16 _ P16) ltac:(clear - P0; lia)); subst av; clear - TD LT GRNG CN1 CN2 AVR; lia. }
      eexists. eexists. split; [exact (CRC.memcpy_cps L ar HI PMSA.fp_ok XSA.PC_MM MEMMOVE_LIBC 2560 ((ch, 16384) :: lb_remove ch LB) FF LK1 cr A1 ch gp cnt (map (fun z => Z_to_bv 8 z) bs) (sp + CH2.ci_csp ci) (CC.cp_pc cj) ltac:(rewrite SCRMEM; clear; lia))|].
      split.
      { unfold CRC.memcpy_pre. split; [exact (REG 10%nat XSA.dstE ch Y10 W11)|]. split; [exact (REG 11%nat XSA.gE gp Y11 W32)|]. split; [exact R12|].
        split; [exact (CRC.dst_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 ch 16384 ch cnt HH1 (or_introl eq_refl) Hsh' ltac:(clear; lia) ltac:(clear - CN1; lia) ltac:(clear - CN1; lia))|].
        split.
        - unfold CRC.mem_src. split; [exact SRCACC|]. split; [subst av; clear - DRNG GRNG CN1 CN2 AVR; lia|].
          split; [unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI; subst av; split; [clear - DRNG GRNG; lia|]; split; [clear - DRNG GRNG CN2 AVR; lia | left; clear - DTOP GRNG CN2 AVR S2 S3; lia]|].
          split.
          + intros q Hq. right. subst PZB. destruct rep as [s|cap p s].
            * destruct TB as (TD & N22). apply aclientw_client. apply (CL5A.infr_clientw L ar _ FF _ _ IS 272 (gp + q) Ifr). subst av. clear - Hq TD N22 GRNG CN2 AVR. lia.
            * destruct TB as (TD & PinR & LT & _). left. exists (p, cap). split; [right; exact PinR | cbn [fst snd]; subst av; clear - Hq TD LT GRNG CN2 AVR; lia].
          + rewrite <- Lbs.
            exact (L5C.bytes_at_rdn (hl_segs L) M' bs gp ltac:(clear - DRNG GRNG; lia) ltac:(rewrite Lbs, Z2Nat.id by (clear - CN1; lia); subst av; clear - DRNG GRNG CN2 AVR; lia) BS).
        - subst av. clear - DRNG GRNG CN1 CN2 AVR. lia. }

      intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & HBY & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
      assert (RM : lb_remove ch ((ch, 16384) :: lb_remove ch LB) = lb_remove ch LB) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
      exists []. split; [reflexivity|]. cbv zeta.
      pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
      set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
      assert (HagE2 : env_agree GT.NF E0 E2).
      { eapply CC.env_agree_trans; [exact HagE'|]. eapply CC.env_agree_le; [exact Hag2|]. destruct HV as (_ & _ & HV3 & HV4 & _). clear - HV3 HV4. lia. }
      assert (T11 : CL5A.uv E2 XSA.dstE = ch) by exact (UVE E2 XSA.dstE ch HagE2 eq_refl U11).
      split; [rewrite Ha0'; unfold CL5A.uv in T11; rewrite <- T11; apply Z_to_bv_bv_unsigned|].
      split; [unfold XSA.BLK0; cbn [CH2.den map app fst snd]; change (bv_unsigned (edenot E' XSA.dstE)) with (CL5A.uv E' XSA.dstE); rewrite W11; cbn [edenot]; rewrite u64_of_Z by (clear; lia); apply incl_refl|].
      split.
      { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exists (XSA.dstE, 0, XSA.CNT j). split; [left; reflexivity|].
        unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off]. change (bv_unsigned (edenot E' XSA.dstE)) with (CL5A.uv E' XSA.dstE). rewrite W11.
        change (bv_unsigned (edenot E' (XSA.CNT j))) with cnt. clear - Hin. lia. }
      split.
      { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply CHNK. left. clear - Hin CN1; lia. }
      assert (HBj : CHA.curB (lb_remove ch LB) G.BLS j E2 = (ch, 16384) :: lb_remove ch LB).
      { unfold CHA.curB. rewrite YBj, (DEN0 E2 HagE2). reflexivity. }
      split; [rewrite HBj; exact HH2|]. split; [reflexivity|].
      pose proof HP as (HP1 & _ & HP3).
      assert (KB : forall a, in_shadow_of ch 16384 a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { intros a Ha. apply HP1. pose proof (SHR ch 16384 a B5 ltac:(clear; lia) B7 Ha) as SRa. split; [clear - SRa; lia|].
        split; [do 6 right; exists (ch, 16384); split; [left; reflexivity | exact Ha]|].
        intros w [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. unfold hid in B6. clear - Hr SRa B6 CN1. lia. }
      split; [exact (PTA.shadow_blk_ag M' M2 (in_shadow_of ch 16384) KB ch 16384 ltac:(clear; lia) (fun a Ha => Ha) B8 Hsh')|].

      intros X0 HX0 _. unfold XSA.STAT in HX0. cbn [In app] in HX0.
      destruct HX0 as [<-|[<-|[]]]; (apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity).
    +
      apply andb_prop in XK as [XK YEK]. apply andb_prop in XK as [Ypc Xbase]. apply Z.eqb_eq in Ypc. subst pc.
      assert (Hi2 : (i <= 2)%nat).
      { destruct (Nat.le_gt_cases i 2) as [Hle|Hgt]; [exact Hle|]. exfalso. unfold CH2.is_leaf in HIL.
        destruct (nth_error G.CPS i) as [c'|] eqn:Hc'; [|destruct HIL as [? [? ?]]; discriminate].
        assert (Hlen : (i < length G.CPS)%nat) by (apply nth_error_Some; rewrite Hc'; discriminate). cbn in Hlen. clear - Hgt Hlen. lia. }
      intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
      assert (HagE : env_agree GT.NF E0 E) by exact (proj1 (proj2 (proj2 (proj2 HA)))).
      refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A (lb_remove ch LB) FF LK sp G.HDECL WW WW G.BLS XSA.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                K DEF0 R r EV Hra Hraok XSA.RETPC i c ps0 _ Xbase _ (FFSnil i) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _); [rewrite LS; exact XSA.ret_at | rewrite (FFSnil i), YB; exact Yfoot |].
      intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
      pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & Hdf1). rewrite SCRV in Hfr1.
      pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
      assert (CELL : forall X0, XSA.has (SR.ps_cells ps0) X0 = true -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X0).
      { intros X0 HX0. apply CC.has_cell_In in HX0. exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HX0). }
      pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A (lb_remove ch LB) FF LK sp G.HDECL WW G.BLS XSA.FFS Cred 0 i E A1 M' m' HA') as Hoff.
      assert (Hcr1 : cr1 = cr) by exact HC1. subst cr1.
      assert (HB : CHA.curB (lb_remove ch LB) G.BLS i E = (ch, 16384) :: lb_remove ch LB) by (unfold CHA.curB; rewrite YB, (DEN0 E HagE); reflexivity).
      rewrite HB in HH1.
      assert (W10 : CL5A.uv E' XSA.sbE = IS + 16) by exact (UVE E' XSA.sbE (IS + 16) HagE' eq_refl U10).
      assert (W32 : CL5A.uv E' XSA.gE = gp) by (unfold CL5A.uv, XSA.gE; cbn [edenot]; rewrite <- (proj1 HagE' 32%nat) by (apply Nat.ltb_lt; reflexivity); exact U32).
      assert (W33 : CL5A.uv E' XSA.avE = av) by (unfold CL5A.uv, XSA.avE; cbn [edenot]; rewrite <- (proj1 HagE' 33%nat) by (apply Nat.ltb_lt; reflexivity); exact U33).
      assert (REGA0 : forall e z, CL.ps_reg_is ps0 10 e = true -> CL5A.uv E' e = z -> getr R' 10%bv = Z_to_bv 64 z).
      { intros e z Hq Hz. replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
        rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (GCELL : forall v z, XSA.has (SR.ps_cells ps0) (KWord (SA XSA.sbE 24) 8 v) = true -> CL5A.uv E' v = z -> L5.u64_at (hl_segs L) M' (IS + 40) z).
      { intros v z Hc Hz. apply (CL5A.u64_full (hl_segs L) _ Hoff). rewrite <- Hz.
        exact (CL5A.kword64_elim (hl_segs L) E' _ _ v (IS + 40) (CELL _ Hc) ltac:(unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' XSA.sbE)) with (CL5A.uv E' XSA.sbE); rewrite W10; clear; lia)). }
      assert (RFACT : forall e lo hi, XSA.has (SR.ps_cells ps0) (KRange e lo hi) = true -> lo <= CL5A.uv E' e <= hi).
      { intros e lo hi Hc. pose proof (CELL _ Hc) as RR. cbn [kentry_ok] in RR. exact RR. }

      assert (EK : exists k, getr R' 10%bv = Z_to_bv 64 k /\ k = Z.min 16384 av /\ L5.u64_at (hl_segs L) M' (IS + 40) (gp + k)).
      { apply orb_prop in YEK. destruct YEK as [YEK|Y4]; [apply orb_prop in YEK; destruct YEK as [YEK|Y3]; [apply orb_prop in YEK; destruct YEK as [Y1|Y2]|]|].
        -
          unfold XSA.ek1 in Y1. apply andb_prop in Y1 as [Y1 Yf]. apply andb_prop in Y1 as [Ya0 Yg].
          pose proof (RFACT _ _ _ Yf) as RR. unfold XSA.SLTUF, XSA.ADDE, CL5A.uv in RR. cbn [edenot] in RR. rewrite u_sltu64, u_add64 in RR.
          change (bv_unsigned (edenot E' XSA.gE)) with (CL5A.uv E' XSA.gE) in RR. change (bv_unsigned (edenot E' XSA.avE)) with (CL5A.uv E' XSA.avE) in RR. rewrite W32, W33 in RR.
          rewrite (Z.mod_small (gp + av)) in RR by (subst av; clear - GRNG DRNG; lia).
          assert (AV0 : av = 0) by (destruct (Z.ltb_spec gp (gp + av)); [cbn in RR; clear - RR; lia | clear - H AVR; lia]).
          exists 0. split; [exact (REGA0 _ 0 Ya0 ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia))|]. split; [rewrite AV0; clear; lia|].
          rewrite Z.add_0_r. exact (GCELL _ gp Yg W32).
        -
          unfold XSA.ek2 in Y2. apply andb_prop in Y2 as [Y2 Yf]. apply andb_prop in Y2 as [Ya0 Yg]. pose proof (RFACT _ _ _ Yf) as RR. rewrite W33 in RR.
          exists 16384. split; [exact (REGA0 _ 16384 Ya0 ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia))|]. split; [clear - RR; lia|].
          apply (GCELL _ (gp + 16384) Yg). unfold CL5A.uv, XSA.ADDE. cbn [edenot]. rewrite u_add64. change (bv_unsigned (edenot E' XSA.gE)) with (CL5A.uv E' XSA.gE). rewrite W32, u64_of_Z by (clear; lia).
          apply Z.mod_small. subst av. clear - GRNG DRNG RR. lia.
        -
          unfold XSA.ek3 in Y3. apply andb_prop in Y3 as [Y3 Yf]. apply andb_prop in Y3 as [Ya0 Yg]. pose proof (RFACT _ _ _ Yf) as RR. rewrite W33 in RR.
          exists av. split; [exact (REGA0 _ av Ya0 W33)|]. split; [clear - RR; lia|].
          apply (GCELL _ (gp + av) Yg). unfold CL5A.uv, XSA.ADDE. cbn [edenot]. rewrite u_add64. change (bv_unsigned (edenot E' XSA.gE)) with (CL5A.uv E' XSA.gE). change (bv_unsigned (edenot E' XSA.avE)) with (CL5A.uv E' XSA.avE).
          rewrite W32, W33. apply Z.mod_small. subst av. clear - GRNG DRNG. lia.
        -
          unfold XSA.ek4 in Y4. apply andb_prop in Y4 as [Y4 Yf]. apply andb_prop in Y4 as [Ya0 Yg]. pose proof (RFACT _ _ _ Yf) as RR. rewrite W33 in RR.
          exists av. split; [apply (REGA0 _ av Ya0); unfold CL5A.uv; cbn [edenot]; rewrite u64_of_Z by (clear; lia); clear - RR; lia|]. split; [clear - RR; lia|].
          apply (GCELL _ (gp + av) Yg). unfold CL5A.uv, XSA.ADDE. cbn [edenot]. rewrite u_add64. change (bv_unsigned (edenot E' XSA.gE)) with (CL5A.uv E' XSA.gE). change (bv_unsigned (edenot E' XSA.avE)) with (CL5A.uv E' XSA.avE).
          rewrite W32, W33. apply Z.mod_small. subst av. clear - GRNG DRNG. lia. }
      destruct EK as (k & RA0 & HK & G40').
      assert (KR : D <= gp + k <= D + n) by (rewrite HK; subst av; clear - GRNG AVR; lia).
      assert (DEFI' : L5.defined M' IS 272).
      { intros q Hq Hn0. apply (Hdf1 (IS + q)); [clear - Hq O3 O6; lia | apply aclientw_client; exact (CL5A.infr_clientw L ar _ FF sp _ IS 272 (IS + q) Ifr ltac:(clear - Hq; lia)) | exact (IDEF q Hq) | exact Hn0]. }
      destruct (TRANS M' (gp + k) Hfr1 G40' KR DEFI') as (ISRC' & SSH' & ISH').
      assert (Hsh' : shadow_blk M' ch 16384).
      { apply (PTA.shadow_blk_ag M1 M' (in_shadow_of ch 16384)); [| clear; lia | intros a Ha; exact Ha | exact B8 | exact HXi].
        intros a Ha. exact (NOFOOTSH c ps0 E' R' A1 M1 m1 M' m' a YFX HLF HagE' Ha). }
      assert (CDEF' : L5.defined M' ch 16384).
      { destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1) (ch, 16384) (or_introl eq_refl)) as (_ & D' & _). exact D'. }
      apply (Hcont fx' R' M' model2 LB cr (lb_remove ch LB) WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact (CBA.own_back L ar C HI HIok _ _ _ _ _ _ _ ch 16384 HH1 HinLB ND1)].
      exists k. split; [exact RA0|]. split; [exact HK|]. split; [exact ISRC'|]. split; [exact SSH'|]. split; [exact Hsh'|]. split; [exact CDEF'|]. repeat split; reflexivity.
  - reflexivity.
  -
    assert (CLV : forall scr a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
      by (intros scr a Ha Hc Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp scr a HH Ha Hc Hs)).
    assert (VO : CL5A.visr (ahid A model) IS 272).
    { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 IS 272 (IS + q) RFx Ifr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
    assert (VS : CL5A.visr (ahid A model) (sp - 2624) 2624).
    { intros q Hq. apply (CLV 0); [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_HI. clear - Hq S2 CL. lia. }
    assert (VB : CL5A.visr (ahid A model) ch 16384).
    { intros q Hq. apply (CLV 0); [clear - Hq B5 B7; lia | left; exists (ch, 16384); split; [exact HinLB | cbn [fst snd]; clear - Hq; lia] |].
      apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold hid in B6. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq B6. lia. }
    set (Mv := CCA.vis A model M).
    assert (DOv : L5.defined Mv IS 272) by (apply (CL5A.defined_vis _ M IS 272 VO); exact IDEF).
    assert (DS : L5.defined Mv (sp - 2624) 2624) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    assert (DBv : L5.defined Mv ch 16384) by (apply (CL5A.defined_vis _ M _ _ VB); exact CDEF).
    assert (U64V : forall k v, 0 <= k -> k + 8 <= 272 -> L5.u64_at (hl_segs L) M (IS + k) v -> L5.u64_at (hl_segs L) Mv (IS + k) v).
    { intros k v K0 K1 Hk. apply (CL5A.u64_vis (hl_segs L)); [clear - O3 K0; lia | clear - O6 K1; lia | exact (CL5A.visr_sub _ IS 272 (IS + k) 8 VO ltac:(clear - K0; lia) ltac:(clear - K1; lia)) | exact Hk]. }
    assert (M8 : L5.u8_at (hl_segs L) Mv (IS + 112) 8).
    { apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ IS 272 (IS + 112) 1 VO ltac:(clear; lia) ltac:(clear; lia)) |].
      exact (u32_u8_low M (IS + 112) 8 ltac:(clear - O3; lia) ltac:(clear - O6; lia) I112). }
    assert (IMGK : forall lo hi, 65536 <= lo -> hi <= 1392640 -> kentry_ok (hl_segs L) E0 Mv (KImg lo hi)).
    { pose proof RO as HIR. unfold PMLA.img_ro, L5.img_clear in HIR. cbn [PMLA.IMG_RO_LO PMLA.IMG_RO_HI PMLA.C_casan] in HIR.
      intros lo hi Hlo Hhi. apply AxSymRun3.kimg_intro; [clear - Hlo; lia | clear - Hhi; lia |]. intros i1 Hi1. unfold Mv, CCA.vis.
      destruct (mrestrict (ahid A model) M (Z_to_bv 64 i1)) eqn:Hv; [|reflexivity]. exfalso. exact (CL5A.vis_def (ahid A model) M (Z_to_bv 64 i1) ltac:(rewrite Hv; discriminate) (HIR i1 ltac:(clear - Hi1 Hlo Hhi; lia))). }
    assert (REGS : regs_ok E0 (CC.cp_regs G.cp0) R).
    { intros rr. unfold sr_get. destruct (bv_eqb rr 0) eqn:Hr0.
      - assert (rr = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; clear - Hr0; lia). subst rr. unfold getr. rewrite Hr0. reflexivity.
      - unfold E0, reg_ev. rewrite <- (ridx_roundtrip rr) at 1. pose proof (ridx_range rr) as Hlt. set (nn := ridx rr) in *. clearbody nn.
        let l := eval vm_compute in (CC.cp_regs G.cp0) in change (CC.cp_regs G.cp0) with l.
        do 32 (destruct nn as [|nn]; [cbn [nth edenot ev Nat.ltb Nat.leb]; first [reflexivity | rewrite <- Ha2; reflexivity] |]). exfalso. clear - Hlt. lia. }
    assert (UEG : edenot E0 (EAlu ALU_ADD (EVar 32) (EVar 33)) = Z_to_bv 64 (gp + av)).
    { cbn [edenot]. apply bv_eq. rewrite u_add64, U32, U33, (u64_of_Z (gp + av)) by (subst av; clear - GRNG DRNG; lia). apply Z.mod_small. subst av; clear - GRNG DRNG; lia. }
    split; [exact REGS|]. unfold know_ok.
    let l := eval vm_compute in (CC.cp_know G.cp0) in change (CC.cp_know G.cp0) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    +   apply IMGK; clear; lia.
    + eapply CL5.kdisj_intro with (A1 := 1379512) (N1 := 96) (A2 := ch) (N2 := 16384); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in B1; rewrite ILO, IHI in B1; clear - B1; lia].
    + eapply CL5.kword64_intro with (A := IS + 16) (z := 1379512); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 16 _ ltac:(clear; lia) ltac:(clear; lia) I16)].
    + eapply CL5.kword64_intro with (A := IS + 40) (z := gp); [ev0 | clear - O3; lia | clear - O6; lia | exact V32 | exact (U64V 40 _ ltac:(clear; lia) ltac:(clear; lia) I40)].
    + eapply CL5.kword64_intro with (A := IS + 48) (z := gp + av); [ev0 | clear - O3; lia | clear - O6; lia | exact UEG | replace (gp + av) with (D + n) by (subst av; clear; lia); exact (U64V 48 _ ltac:(clear; lia) ltac:(clear; lia) I48)].
    + eapply CL5.kword64_intro with (A := IS + 64) (z := 0); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | exact (U64V 64 _ ltac:(clear; lia) ltac:(clear; lia) I64)].
    + eapply CL5.kword64_intro with (A := IS + 104) (z := gp + av); [ev0 | clear - O3; lia | clear - O6; lia | exact UEG | replace (gp + av) with (D + n) by (subst av; clear; lia); exact (U64V 104 _ ltac:(clear; lia) ltac:(clear; lia) I104)].
    + apply (CL5A.kword8_intro (hl_segs L) E0 Mv _ _ (IS + 112) 8); [ev0 | clear - O3; lia | clear - O6; lia | reflexivity | clear; lia | exact M8].
    + eapply CL5.kunk_intro with (A := IS + 40) (N := 8); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | intros q Hq; replace (IS + 40 + q) with (IS + (40 + q)) by (clear; lia); apply DOv; clear - Hq; lia].
    + eapply CL5.kwr_intro with (A := IS + 40) (N := 8); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | intros q Hq; replace (IS + 40 + q) with (IS + (40 + q)) by (clear; lia); apply DOv; clear - Hq; lia].
    + eapply CL5.krange_intro with (v := IS + 16); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1 CL; lia].
    + eapply CL5.kalign_intro with (v := IS + 16); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | clear - I8; apply Z.mod_divide in I8; [|lia]; destruct I8 as [q ->]; replace (q * 8 + 16) with ((q + 2) * 8) by lia; apply Z.mod_mul; lia].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := IS + 16) (N2 := 104); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.krange_intro with (v := gp); [lin_eval; rw_atoms; clear; lia | clear - GRNG DRNG; lia | subst PZB; destruct rep; [destruct TB as (TD & _); clear - GRNG DRNG TD O1 FSLO; lia | destruct TB as (TD & _ & _ & _ & P0 & _); clear - GRNG DRNG TD P0; lia]].
    + eapply CL5.krange_intro with (v := av); [lin_eval; rw_atoms; clear; lia | clear - AVR NRNG; lia | clear - AVR NRNG; lia].
    + eapply CL5.krange_intro with (v := ch); [lin_eval; rw_atoms; clear; lia | clear - B5 B7; lia | clear - B0 B4 B3 SP1 S2 S3; lia].
    + eapply CL5.kalign_intro with (v := ch); [lin_eval; rw_atoms; clear; lia | clear - B5 B7; lia | clear; lia | exact B16].
    + eapply CL5.kunk_intro with (A := ch) (N := 16384); [ev0 | reflexivity | clear - B5; lia | clear - B7; lia | clear - B7; lia | exact DBv].
    + eapply CL5.kwr_intro with (A := ch) (N := 16384); [ev0 | reflexivity | clear - B5; lia | clear - B7; lia | clear - B7; lia | exact DBv].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := ch) (N2 := 16384); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in B6; clear - B6; lia].
    + eapply CL5.kunk_intro with (A := sp - 2624) (N := 2624); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 2624) (N := 2624); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 2624) (N1 := 2624) (A2 := IS + 16) (N2 := 104); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 2624) (N1 := 2624) (A2 := ch) (N2 := 16384); [ev0 | reflexivity | ev0 | reflexivity | clear - B4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := IS + 16) (N1 := 104) (A2 := ch) (N2 := 16384); [ev0 | reflexivity | ev0 | reflexivity | clear - APIC; lia].
  -
    split.
    + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
      exists cr, LK. unfold CHA.curB, CHA.curF. change (nth 0 G.BLS []) with XSA.BLK0. rewrite (DEN0 E0 (CC.env_agree_refl _ _)), FFSnil. cbn [app CHA.denF map length].
      split; [exact (CBA.own_front L ar C HI HIok _ _ _ _ _ _ _ ch 16384 HH HinLB)|]. split; [apply incl_refl|]. split; [reflexivity | exact Hroom].
    + exact CSH.
  - exact Hfp.
Qed.

End XsgetnOk.
