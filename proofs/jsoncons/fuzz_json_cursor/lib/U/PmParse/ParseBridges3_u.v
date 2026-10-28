(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PB3.
Import PB.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Lemma bytes_of_defined_r : forall (M : mem) (n : nat) (p : Z), 0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> L5.defined M p (Z.of_nat n) ->
  exists s : list Z, length s = n /\ L5.bytes_at RSEGS M p s /\ Forall (fun c => 0 <= c < 256) s.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hb Hd.
  - exists []. split; [reflexivity|]. split; [|constructor]. intros i Hi. cbn [length] in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (s & Hl & Hs & Hr).
    { intros i Hi. replace (p + 1 + i) with (p + (i + 1)) by lia. apply Hd. lia. }
    pose proof (Hd 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:Hb0; [|contradiction].
    exists (bv_unsigned b :: s). split; [cbn [length]; rewrite Hl; reflexivity|]. split.
    + intros i Hi. destruct i as [|i].
      * cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. unfold rd1. rewrite Hb0. rewrite Z_to_bv_bv_unsigned. reflexivity.
      * cbn [nth]. replace (p + Z.of_nat (S i)) with (p + 1 + Z.of_nat i) by lia. apply Hs. cbn [length] in Hi. lia.
    + constructor; [|exact Hr]. pose proof (bv_unsigned_in_range _ b) as Bb. change (bv_modulus 8) with 256 in Bb. lia.
Qed.

Lemma str_retext : forall (M : mem) o cap p (s s0 : list Z), PML.str_at M o (PML.SLong cap p s) -> L5.bytes_at RSEGS M p s0 -> length s0 = length s -> PML.str_at M o (PML.SLong cap p s0).
Proof.
  intros M o cap p s s0 (HL & Hc & Hlt) Hb Hl. unfold PML.str_at. rewrite Hl. split; [|split; assumption].
  destruct HL as (T0 & U0 & U8 & U16 & _ & Hnul). unfold L5.lstr_long. rewrite Hl. repeat split; assumption.
Qed.
Lemma bytes_at_firstn : forall (M : mem) p (s : list Z) n, L5.bytes_at RSEGS M p s -> L5.bytes_at RSEGS M p (firstn n s).
Proof.
  intros M p s n H i Hi. rewrite length_firstn in Hi. specialize (H i ltac:(lia)).
  replace (nth i (firstn n s) 0) with (nth i s 0); [exact H|]. rewrite <- (firstn_skipn n s) at 1. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
Qed.
Lemma bytes_at_skipn : forall (M : mem) p (s : list Z) n, (n <= length s)%nat -> L5.bytes_at RSEGS M p s -> L5.bytes_at RSEGS M (p + Z.of_nat n) (skipn n s).
Proof.
  intros M p s n Hn H i Hi. rewrite length_skipn in Hi. specialize (H (n + i)%nat ltac:(lia)).
  replace (p + Z.of_nat n + Z.of_nat i) with (p + Z.of_nat (n + i)) by lia.
  replace (nth i (skipn n s) 0) with (nth (n + i) s 0); [exact H|]. rewrite <- (firstn_skipn n s) at 1. rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn. f_equal. lia.
Qed.

Lemma mod_neg64 : forall x, - 2 ^ 64 < x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. intros x Hx. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma win_arith2 : forall q q2 wseg wlen, 0 <= q < 2 ^ 64 -> 0 <= q2 < 2 ^ 64 -> 4096 <= wseg -> 0 <= wlen -> wseg + wlen <= 2 ^ 47 ->
  0 <= (q - wseg) mod 2 ^ 64 <= 16384 -> 0 <= ((wseg + wlen) mod 2 ^ 64 - q2) mod 2 ^ 64 <= 16384 -> 0 <= (q2 - q) mod 2 ^ 64 <= 16384 ->
  wseg <= q /\ q <= q2 /\ q2 <= wseg + wlen.
Proof.
  intros q q2 wseg wlen Hq Hq2 Hw Hl Hwl F2 F3 F5.
  rewrite (Z.mod_small (wseg + wlen)) in F3 by lia.
  assert (A : wseg <= q <= wseg + 16384) by (destruct (Z_lt_dec (q - wseg) 0) as [N|N]; [rewrite mod_neg64 in F2 by lia; lia | rewrite Z.mod_small in F2 by lia; lia]).
  assert (C : q <= q2 <= q + 16384) by (destruct (Z_lt_dec (q2 - q) 0) as [N|N]; [rewrite mod_neg64 in F5 by lia; lia | rewrite Z.mod_small in F5 by lia; lia]).
  assert (B : q2 <= wseg + wlen) by (destruct (Z_lt_dec (wseg + wlen - q2) 0) as [N|N]; [rewrite mod_neg64 in F3 by lia; lia | lia]).
  lia.
Qed.

Section Inst3.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBrest sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Variable XI : nat -> env -> mem -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := LYI_ L LAY.
Let LYE := LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Lemma FLOOR : hl_sptop L - 2 ^ 23 + CH.hd_scr d <= sp0.
Proof. destruct STK as (_ & S2 & _). unfold hl_ceil in S2. lia. Qed.

Abbreviation AMB3 := (CH2.amb3 L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred XI).
Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Variable OB : expr.
Variable OK : Z.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Variable oaddr : Z.
Hypothesis OADDR : estart E0 (SA OB OK) = oaddr.
Hypothesis OBJ : sp0 <= oaddr /\ oaddr + 24 <= hl_sptop L /\ oaddr mod 8 = 0 /\ forall a, oaddr <= a < oaddr + 24 -> exists w, In w W /\ L5.in_rng w a.

Variables KXf BXf : list (Z * Z) -> Z.
Hypothesis CRED_EQ : forall i E cr, Cred i E cr <-> PPS.bufcred L cr (PB.cap_of BLS i E) (KXf (PB.tl_of BLS i E)) (BXf (PB.tl_of BLS i E)).

Variables WSEG WLEN : expr.
Hypothesis WSEG_frozen : APC.expr_vars_lt NF WSEG = true.
Hypothesis WLEN_frozen : APC.expr_vars_lt NF WLEN = true.
Variables wseg wlen : Z.
Hypothesis WSEGV : uv E0 WSEG = wseg.
Hypothesis WLENV : uv E0 WLEN = wlen.
Hypothesis WCHUNK : exists ch, In (ch, 16384) LBrest /\ ch <= wseg /\ wseg + wlen <= ch + 16384.
Hypothesis APPENDROK : PMS.str_append_range_spec L HI.
Definition appendr_chk (KMIN : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in let cells := SR.ps_cells ps in
  let nx := (CC.cp_nx cj - APC.NCS - 2)%nat in
  let a1e := nth 11 regs (ELit 0) in let a2e := nth 12 regs (ELit 0) in
  match split_lit (nth 10 regs (ELit 0)), BLi with
  | (ob, ok), (pe, ce) :: BLk =>
      match CAX.cell_at cells ob (ok + 8) 8 with
      | Some se =>
          if (expr_eqb ob OB && Z.eqb ok OK && Z.leb 12 KMIN && str_pat cells ob ok pe ce se (2 * KMIN) (2 ^ 26 - 1)
              && has cells (KUnk (SA WSEG 0) WLEN) && prove cells (KRange (APC.esub a1e WSEG) 0 16384)
              && prove cells (KRange (APC.esub (APC.eadd WSEG WLEN) a2e) 0 16384) && prove cells (KRange (PSU.eadd se (PSU.esub a2e a1e)) 0 (2 ^ 26 - 1)) && prove cells (KRange (APC.esub a2e a1e) 0 16384)
              && CH2.blocks_eqb BLj ((EVar nx, PSU.emul2 (EVar (nx + 1))) :: BLk) && CH2.blocks_vars_lt nx BLk
              && forallb (fun X => (CH2.fresh_fact_ok d 0x10000 0xf8000 cells nx BLk nx (PSU.emul2 (EVar (nx + 1))) X
                                    || APC.kentry_eqb X (KDisj (SA (EVar nx) 0) (PSU.emul2 (EVar (nx + 1))) (SA WSEG 0) WLEN))%bool) (PSU.blk_facts d nx BLk))%bool
          then CH2.custom_chk NF d STR_SCR 2 BLk [(ob, ok, ELit 24)] (PSU.str_news d ob ok (PSU.eadd se (PSU.esub a2e a1e)) nx KMIN BLk) None c ps cj BLi
          else None
      | None => None
      end
  | _, _ => None
  end.

Lemma appendr_leaf_ok : forall KMIN i c k ps j cj ci,
  is_leaf i c k ps (CC.TOther PML.PC_APPEND_RANGE) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj ->
  SR.ps_pc ps = PML.PC_APPEND_RANGE ->
  appendr_chk KMIN c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) pe ce BLk se, env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> XI i E M ->
     nth i BLS [] = (pe, ce) :: BLk -> CAX.cell_at (SR.ps_cells ps) OB (OK + 8) 8 = Some se ->
     exists s src : list Z,
       L5.bytes_at RSEGS M' (uv E' pe) s /\ Z.of_nat (length s) = uv E' se /\
       L5.bytes_at RSEGS M' (uv E' (nth 11 (CA.ps_reglist ps) (ELit 0))) src /\
       Z.of_nat (length src) = uv E' (nth 12 (CA.ps_reglist ps) (ELit 0)) - uv E' (nth 11 (CA.ps_reglist ps) (ELit 0)) /\
       (forall E2 (M2 : mem) LBk spc cap' p', env_agree (CC.cp_nx cj - APC.NCS - 2) E' E2 -> L5C.hpres L LBk spc STR_SCR [(oaddr, 24)] M' M2 -> incl LBrest LBk ->
          PML.str_at M2 oaddr (PML.SLong cap' p' (s ++ src)) ->
          CH2.den E2 (nth j BLS []) = (p', cap') :: CH2.den E' BLk   ->
          XI j E2 M2)) ->
  CC.leaf_ok (hl_segs L) CPS AMB3 K PML.fp_ok i c ps.
Proof.
  intros KMIN i c k ps j cj ci IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  pose proof (proj2 HAmb) as HXI0.
  unfold appendr_chk in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [ob ok] eqn:Hsplit.
  destruct (nth i BLS []) as [|[pe ce] BLk] eqn:HBLi; [discriminate|].
  destruct (CAX.cell_at (SR.ps_cells ps) ob (ok + 8) 8) as [se|] eqn:Hcell; [|discriminate].
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B7]. apply andb_prop in Hb as [Hb B6b]. apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb W5]. apply andb_prop in Hb as [Hb W4]. apply andb_prop in Hb as [Hb W3].
  apply andb_prop in Hb as [Hb W2]. apply andb_prop in Hb as [Hb W1]. apply andb_prop in Hb as [Hb B4].
  apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply Z.eqb_eq in B2. apply Z.leb_le in B3. subst ob ok.
  apply CH2.blocks_eqb_eq in B6.
  set (nx := (CC.cp_nx cj - APC.NCS - 2)%nat) in *. set (cells := SR.ps_cells ps) in *.
  rewrite <- HBLi in Hchk.
  destruct (CH2.custom_ret L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok XI DEF0
              STR_SCR 2%nat BLk _ _ None i c ps j cj ci Hcj Hchk E R M model E' R' M' HAt HAmb Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = nx) by (unfold nx; lia).
  assert (Va2 : APC.expr_vars_lt nx (nth 12 (CA.ps_reglist ps) (ELit 0)) = true) by (rewrite <- Hnx, <- Hreq; apply CH.nth_vars_lt; exact V1).
  assert (Va1 : APC.expr_vars_lt nx (nth 11 (CA.ps_reglist ps) (ELit 0)) = true) by (rewrite <- Hnx, <- Hreq; apply CH.nth_vars_lt; exact V1).
  destruct HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  pose proof HK as HK0. rewrite LS in HK.

  assert (Ho : estart E' (SA OB OK) = oaddr) by (rewrite (estart_agree NF E0 E' OB OK HagE' OB_frozen); exact OADDR).
  destruct OBJ as (O1 & O2 & O3 & O4). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  destruct (str_view E' M' cells OB OK pe ce se (2 * KMIN) (2 ^ 26 - 1) HK B4 ltac:(lia) ltac:(rewrite Ho; lia) ltac:(rewrite Ho; lia)) as (sv & Hstrv & Hlenv & Hcap & Hlt & Hsm & Hc8 & Hpr & Hpdef).
  rewrite Ho in Hstrv.
  destruct (USER E E' R' M M' pe ce BLk se HagE' Hag HLF HXI0 eq_refl Hcell) as (s & src & Hbs & Hlen & Hbsrc & Hnsrc0 & UCONT).
  assert (Hstr : PML.str_at M' oaddr (PML.SLong (uv E' ce) (uv E' pe) s)) by (apply (str_retext M' oaddr _ _ sv s Hstrv Hbs); apply Nat2Z.inj; rewrite Hlen, Hlenv; reflexivity). set (p := uv E' pe) in *. set (cap := uv E' ce) in *. set (size := uv E' se) in *.

  unfold CH2.cur in HH. rewrite <- Hden, HBLi, den_cons in HH. fold p cap in HH. set (rest := CH2.den E' BLk ++ LBrest) in *.
  change ((p, cap) :: CH2.den E' BLk ++ LBrest) with ((p, cap) :: rest) in HH.

  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 oaddr).
  { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Hreq.
    rewrite (APS.split_lit_denot E' _ _ _ Hsplit). f_equal. exact Ho. }
  set (a1e := nth 11 (CA.ps_reglist ps) (ELit 0)) in *. set (a2e := nth 12 (CA.ps_reglist ps) (ELit 0)) in *.
  set (q := uv E' a1e). set (q2 := uv E' a2e). set (n := q2 - q).
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 q).
  { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat. rewrite Hreq.
    unfold q, uv. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Ga2 : getr R' 12%bv = Z_to_bv 64 q2).
  { rewrite (HR 12%bv). unfold sr_get. change (bv_eqb (12%bv : bv 5) 0) with false. cbv iota. change (ridx 12%bv) with 12%nat. rewrite Hreq.
    unfold q2, uv. symmetry. apply Z_to_bv_bv_unsigned. }

  pose proof (uv_range E' a1e) as Rq. pose proof (uv_range E' a2e) as Rq2. fold q in Rq. fold q2 in Rq2.
  destruct WCHUNK as (ch & Hch & Hch1 & Hch2).
  assert (Uws : uv E' WSEG = wseg) by (rewrite (uv_agree NF E0 E' WSEG HagE' WSEG_frozen); exact WSEGV).
  assert (Uwl : uv E' WLEN = wlen) by (rewrite (uv_agree NF E0 E' WLEN HagE' WLEN_frozen); exact WLENV).
  pose proof (has_ok E' M' cells _ HK W1) as HWU.
  assert (Hdefw : L5.defined M' wseg wlen).
  { apply (CL5.kunk_elim RSEGS E' M' _ _ wseg wlen HWU); [unfold estart; cbn [a_base a_off]; fold (uv E' WSEG); lia | exact Uwl]. }
  pose proof (prove_ok E' M' cells _ HK W2) as F2. cbn [kentry_ok] in F2. fold (uv E' (APC.esub a1e WSEG)) in F2. rewrite uv_esub in F2. fold q in F2. rewrite Uws in F2.
  pose proof (prove_ok E' M' cells _ HK W3) as F3. cbn [kentry_ok] in F3. fold (uv E' (APC.esub (APC.eadd WSEG WLEN) a2e)) in F3.
  rewrite uv_esub, uv_eadd in F3. fold q2 in F3. rewrite Uws, Uwl in F3.
  pose proof (prove_ok E' M' cells _ HK W4) as F4. cbn [kentry_ok] in F4. fold (uv E' (PSU.eadd se (PSU.esub a2e a1e))) in F4. unfold PSU.eadd, PSU.esub in F4. rewrite uv_eadd, uv_esub in F4. fold q q2 in F4.
  pose proof (prove_ok E' M' cells _ HK W5) as F5. cbn [kentry_ok] in F5. fold (uv E' (APC.esub a2e a1e)) in F5. rewrite uv_esub in F5. fold q q2 in F5.

  set (kx := KXf (CH2.den E' BLk)). set (bx := BXf (CH2.den E' BLk)).
  assert (HBC : PPS.bufcred L cr cap kx bx).
  { apply CRED_EQ in HC. unfold PB.cap_of, PB.tl_of in HC. rewrite <- Hden, HBLi, den_cons in HC. exact HC. }
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & _ & Hcr0 & Hcr1).

  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _ & _).
  assert (Hchin : In (ch, 16384) ((p, cap) :: rest)) by (right; unfold rest; apply in_or_app; right; exact Hch).
  destruct (Hwf _ Hchin) as ((C0 & C1 & C2 & C3 & C4) & _ & _). cbn [fst snd] in C0, C1, C2, C3, C4.
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO0.
  assert (Hwl0 : 0 <= wlen) by (rewrite <- Uwl; apply uv_range).
  assert (Hwr : 4096 <= wseg /\ wseg + wlen <= 2 ^ 47) by (clear - C0 C4 Hch1 Hch2 S3 S4 S5 S2 SCR_pos; unfold hl_ceil in *; lia).
  destruct (win_arith2 q q2 wseg wlen Rq Rq2 (proj1 Hwr) Hwl0 (proj2 Hwr) F2 F3 F5) as (Hq1a & Hq1b & Hq2).
  assert (Hn16 : 0 <= n <= 16384) by (clear - F5 Hq1b Rq Rq2; unfold n; rewrite Z.mod_small in F5 by lia; lia).
  assert (Hsn : size + n <= 2 ^ 26 - 1) by (clear - F4 F5 Hsm Hq1b Rq Rq2 Hlen Hn16; unfold n in *; rewrite (Z.mod_small (q2 - q)) in F4 by lia; rewrite Z.mod_small in F4 by lia; lia).
  clear F2 F3 F4 F5 HWU C1.
  assert (Hnsrc : Z.of_nat (length src) = n) by (fold a1e a2e in Hnsrc0; fold q q2 in Hnsrc0; exact Hnsrc0).
  fold a1e in Hbsrc. fold q in Hbsrc.

  rewrite Hpc. rewrite LS.
  apply (APPENDROK ((p, cap) :: rest) cr oaddr cap p q (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) s src fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [rewrite Hnsrc; unfold n; replace (q + (q2 - q)) with q2 by lia; exact Ga2|]. split; [exact Hstr|]. split; [lia|]. split; [left; reflexivity|].
    split; [unfold PML.obj_on_stack; lia|]. split; [exact Hbsrc|].
    split; [intros i0 Hi0; rewrite Hnsrc in Hi0; replace (q + i0) with (wseg + (q - wseg + i0)) by lia; apply Hdefw; lia|].
    split; [exists (ch, 16384); split; [exact Hchin|]; cbn [fst snd]; split; [|rewrite Hnsrc; lia]|].
    { intros Heq. cbn [fst] in Heq. subst ch. apply (CH2.nodup_app_disj [p] (map fst rest) p Hnd); [left; reflexivity|].
      change p with (fst (p, 16384)). apply in_map. unfold rest. apply in_or_app. right. exact Hch. }
    split; [rewrite Hnsrc; lia|].
    intros Hg. apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 [Hgrown HWc] HRP HPRES Hbv2 HH2.
  assert (Hs1 : Z.of_nat (length (s ++ src)) = size + n) by (rewrite length_app, Nat2Z.inj_add; lia).
  assert (EXP : exists p' cap', PML.str_at M2 oaddr (PML.SLong cap' p' (s ++ src)) /\ LB' = (p', cap') :: rest /\ LBk = rest /\ 2 * KMIN <= cap' <= 2 ^ 27 /\ PPS.bufcred L cr' cap' kx bx).
  { assert (Hrm : lb_remove p ((p, cap) :: rest) = rest) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity).
    destruct Hgrown as [(G1 & G2 & G3 & G4) | (p' & Hex)].
    - exists p, cap. rewrite G2, G3, G4, Hrm. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia | exact HBC].
    - cbv zeta in Hex. destruct Hex as (G0 & G1 & G2 & G3 & G4 & G5). rewrite Hs1 in *.
      destruct (PPS.grow_cap_facts cap (size + n) ltac:(lia) Hc8 ltac:(lia) ltac:(lia)) as (F1' & F2' & F3' & F4').
      exists p', (PML.grow_cap cap (size + n)). rewrite G3, G5, Hrm, G4. split; [exact G1|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      apply (PPS.bufcred_grow L cr cap _ kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) HBC); lia. }
  destruct EXP as (p' & cap' & Hstr2 & -> & -> & Hcap' & HBC').
  destruct (CH2.first_block_facts L HI HIok p' cap' rest cr' M2 _ HH2) as (BR & BD & BA). pose proof BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.

  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] rest Wc eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - intros w a Hw Hin. subst Wc. destruct Hw as [<-|[]]. exists (OB, OK, ELit 24). split; [left; reflexivity|].
    unfold CH2.in_reg. rewrite Ho. unfold elenZ. cbn [edenot]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. rewrite u64_of_Z by lia. lia.
  -
    intros X HX _. rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    assert (BF : forall Y, In Y (PSU.blk_facts d nx BLk) -> kentry_ok (hl_segs L) E2 M2 Y).
    { intros Y HY. rewrite forallb_forall in B7. specialize (B7 Y HY). apply orb_prop in B7 as [B7|B7].
      - exact (CH2.ghost_block_fact L LYI LYE NF E0 LBrest sp0 d W STK SCR_pos NF32 SP0 W_ok CRS_ok WRS_ok 0x10000 0xf8000 (PmLayout.ly_img_lo L LAY) (PmLayout.ly_img_hi L LAY)
                 E' E2 nx M' M2 BLk cells nx (PSU.emul2 (EVar (nx + 1))) p' cap' Y HagE' HK0 Hag2 G0 Ucap BR BA BD B7).
      - apply APS.kentry_eqb_eq in B7. subst Y. cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite G0.
        fold (uv E2 (PSU.emul2 (EVar (nx + 1)))) (uv E2 WSEG) (uv E2 WLEN). rewrite Ucap, (uv_agree NF E0 E2 WSEG HagE2 WSEG_frozen), (uv_agree NF E0 E2 WLEN HagE2 WLEN_frozen), WSEGV, WLENV.
        assert (Hin : In (ch, 16384) rest) by (unfold rest; apply in_or_app; right; exact Hch).
        pose proof (L5C.blocks_apart_in p' cap' rest ch 16384 BA Hin) as AP. lia. }
    unfold PSU.str_news in HX. apply in_app_or in HX as [HX|HX]; [|apply in_app_or in HX as [HX|HX]].
    + rewrite LS.
      assert (Hest : estart E2 (SA OB OK) = oaddr) by (rewrite (estart_agree NF E0 E2 OB OK HagE2 OB_frozen); exact OADDR).
      assert (Hsz : uv E2 (PSU.eadd se (PSU.esub a2e a1e)) = Z.of_nat (length (s ++ src))).
      { destruct (cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        unfold PSU.eadd, PSU.esub. rewrite uv_eadd, uv_esub, (uv_agree nx E' E2 se Hag2 Vse), (uv_agree nx E' E2 a2e Hag2 Va2), (uv_agree nx E' E2 a1e Hag2 Va1). fold size q q2. rewrite Hs1.
        rewrite (Z.mod_small (q2 - q)) by (fold n; lia). fold n. apply Z.mod_small. lia. }
      assert (Hpr' : 4096 <= p' <= 2 ^ 47) by (unfold hl_ceil in *; lia).
      exact (str_cells_ok E2 M2 OB OK (PSU.eadd se (PSU.esub a2e a1e)) nx KMIN oaddr cap' p' (s ++ src) Hest ltac:(lia) ltac:(lia) G0 G1 Hsz (conj Hl2 (conj Hc8' Hlt2)) Hcap' Hpr' X HX).
    + exact (BF X HX).
    + rewrite LS.
      assert (Hsz : uv E2 (PSU.eadd se (PSU.esub a2e a1e)) = size + n).
      { destruct (cell_at_has _ _ _ _ _ Hcell) as (b' & Hin & ->).
        pose proof (kn_vars_in _ _ _ V2 Hin) as Vk. cbn [APC.kentry_vars_lt] in Vk. apply andb_prop in Vk as [_ Vse]. rewrite Hnx in Vse.
        unfold PSU.eadd, PSU.esub. rewrite uv_eadd, uv_esub, (uv_agree nx E' E2 se Hag2 Vse), (uv_agree nx E' E2 a2e Hag2 Va2), (uv_agree nx E' E2 a1e Hag2 Va1). fold size q q2.
        rewrite (Z.mod_small (q2 - q)) by (fold n; lia). fold n. apply Z.mod_small. lia. }
      apply (nul_facts_ok E2 M2 d (PSU.eadd se (PSU.esub a2e a1e)) nx BLk p' cap' (size + n) G0 Ucap Hsz ltac:(rewrite <- Hs1; lia) ltac:(unfold hl_ceil in *; lia)); [|exact HX].
      intros Y HY. rewrite <- LS. exact (BF Y HY).
  -
    rewrite Hnx. set (E2 := CH2.retEx E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2).
    assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
    assert (G0 : bv_unsigned (ev E2 nx) = p').
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. lia. }
    assert (Hchh : 0 <= cap' / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (G1 : bv_unsigned (ev E2 (nx + 1)) = cap' / 2).
    { pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 p'; Z_to_bv 64 (cap' / 2)] R2 1 ltac:(cbn; lia)) as G. fold E2 in G. rewrite G. cbn [nth]. apply u64_of_Z. exact Hchh. }
    destruct Hstr2 as (Hl2 & Hc8' & Hlt2).
    assert (Hcd : cap' = 2 * (cap' / 2)).
    { pose proof (Z.div_mod cap' 8 ltac:(lia)) as D. rewrite Hc8' in D. rewrite D at 2. replace (8 * (cap' / 8) + 0) with ((4 * (cap' / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
    assert (Ucap : uv E2 (PSU.emul2 (EVar (nx + 1))) = cap').
    { unfold PSU.emul2. rewrite uv_escale. unfold uv. cbn [edenot]. rewrite G1, <- Hcd. apply Z.mod_small. lia. }
    assert (Hcur : CH2.cur LBrest BLS j E2 = (p', cap') :: rest).
    { unfold CH2.cur. rewrite B6, den_cons, Ucap. unfold uv at 1. cbn [edenot]. rewrite G0. unfold rest. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). reflexivity. }
    split; [|apply (UCONT E2 M2 rest (sp0 + CH2.ci_csp ci) cap' p' Hag2); [subst Wc; exact HPRES | intros b0 Hb0; unfold rest; apply in_or_app; right; exact Hb0 | exact (conj Hl2 (conj Hc8' Hlt2)) | rewrite B6, den_cons, Ucap; unfold uv at 1; cbn [edenot]; rewrite G0; rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b); reflexivity]].
    apply (CH2.amb_callee_x L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 FLOOR STR_SCR 2%nat c ps cj ci i j E E' R' M' model E2 M2 model2 rest Wc cr' CF HPRES).
    + intros b Hb. unfold rest. apply in_or_app. right. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout). subst Wc. destruct Hw as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (O4 a Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
    + exact Hbv2.
    + rewrite Hcur. exact HH2.
    + rewrite Hnx. exact Hag2.
    + apply CRED_EQ. unfold PB.cap_of, PB.tl_of. rewrite B6, den_cons. cbn [hd snd tl]. rewrite Ucap. rewrite (CH2.den_agree nx E' E2 BLk Hag2 B6b). exact HBC'.
Qed.

End Inst3.
End PB3.
