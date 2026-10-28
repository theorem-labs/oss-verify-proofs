(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound HeapIface LibIface L5Defs L5Core.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmCurSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ReadBase_u RnStretch_u RnInv_u.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RNX.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Ltac kin := vm_compute; repeat first [left; reflexivity | right].

Definition ee (rdst : Z) : Z := if Z.eqb rdst 2 then 0 else 1.
Definition ww (ps : PML.pstate) : Z := if Z.eqb (RB.wp ps) (RB.we ps) then 0 else 1.
Definition rank (ps : PML.pstate) : Z := if (Z.eqb (PML.ps_st ps) 17 || Z.eqb (PML.ps_st ps) 28)%bool then 2 else 1.
Lemma ee_range : forall rdst, 0 <= ee rdst <= 1. Proof. intros rdst. unfold ee. destruct (Z.eqb rdst 2); lia. Qed.
Lemma ww_range : forall ps, 0 <= ww ps <= 1. Proof. intros ps. unfold ww. destruct (Z.eqb (RB.wp ps) (RB.we ps)); lia. Qed.
Lemma rank_range : forall ps, 1 <= rank ps <= 2. Proof. intros ps. unfold rank. destruct (_ || _)%bool; lia. Qed.
Lemma rank_in : forall ps, In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] -> rank ps = 2.
Proof. intros ps [H|[H|[]]]; unfold rank; rewrite <- H; reflexivity. Qed.
Lemma rank_nin : forall ps, ~ In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] -> rank ps = 1.
Proof.
  intros ps H. unfold rank. destruct (Z.eqb_spec (PML.ps_st ps) 17) as [X|X]; [exfalso; apply H; left; symmetry; exact X|].
  destruct (Z.eqb_spec (PML.ps_st ps) 28) as [Y|Y]; [exfalso; apply H; right; left; symmetry; exact Y | reflexivity].
Qed.
Lemma wp_setwin : forall ps p e, RB.wp (PML.ps_set_win ps (Some (p, e))) = p. Proof. intros [] p e. reflexivity. Qed.
Lemma we_setwin : forall ps p e, RB.we (PML.ps_set_win ps (Some (p, e))) = e. Proof. intros [] p e. reflexivity. Qed.
Lemma more_setwin : forall ps w, PML.ps_more (PML.ps_set_win ps w) = PML.ps_more ps. Proof. intros ps w. destruct ps. reflexivity. Qed.
Lemma st_setwin : forall ps w, PML.ps_st (PML.ps_set_win ps w) = PML.ps_st ps. Proof. intros [] w. reflexivity. Qed.
Lemma level_setwin : forall ps w, PML.ps_level (PML.ps_set_win ps w) = PML.ps_level ps. Proof. intros [] w. reflexivity. Qed.
Lemma b2z_range : forall b, 0 <= PML.b2z b <= 255. Proof. intros []; cbn; lia. Qed.
Lemma b2z_land : forall b, Z.land (PML.b2z b) 1 = PML.b2z b. Proof. intros []; reflexivity. Qed.
Lemma b2z_nz : forall b, PML.b2z b <> 0 -> b = true. Proof. intros [] H; [reflexivity | exfalso; apply H; reflexivity]. Qed.
Lemma b2z_z : forall b, PML.b2z b = 0 -> b = false. Proof. intros [] H; [discriminate H | reflexivity]. Qed.
Lemma ra_lit : forall x, 0 <= x < 2 ^ 47 -> x mod 2 = 0 -> L5.ra_ok x. Proof. intros x H1 H2. split; assumption. Qed.

Lemma stop_not_start : forall segs ps ps' M' V, PMCUR.cur_post segs ps ps' 0 M' V -> PML.ps_more ps' = false -> PML.ps_st ps' <> PML.ST_START.
Proof.
  intros segs ps ps' M' V (_ & H2) HM. destruct (H2 eq_refl HM) as [(_ & X & _)|(_ & e & _ & HE)].
  - rewrite X. unfold PML.ST_DONE, PML.ST_START. lia.
  - unfold PML.ST_START. destruct e; cbn [PMCUR.ev_rel] in HE; unfold PMCUR.after_value_st in HE;
      repeat match type of HE with _ /\ _ => destruct HE as [HE _] end; try (cbn [In] in HE); unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_COLON,
      PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_VALUE_OR_END in HE; lia.
Qed.

Section H.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis PSOME : PMS.parse_some_spec L HI STRTOD_SCR.
Hypothesis SETEC : PMS.set_ec_spec L.
Hypothesis RCHUNK : PMCS.read_chunk_c_spec L.

Section Run.
Variables (LBo : list (Z * Z)) (sp r C IS E ch kx bx Bs : Z) (rep : PML.srep) (g0 : PML.ls_state) (ps0 : PML.pstate) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model) (K : ShapeAlg.TSet).
Let SS := PMCS.RN_SCR STRTOD_SCR.
Let n := Z.of_nat (length (PML.srep_chars rep)).
Let D := PML.srep_data (IS + 80) rep.
Let P := C + 320.
Let V := C + 592.
Let S := C + 8.
Let LBk := lb_remove ch LBo.
Hypothesis Hn : n < 2 ^ 26.
Hypothesis HBs : Bs < 2 ^ 26.
Hypothesis G0 : g0 <> PML.LS0.
Hypothesis SPOK : RNS.spok sp.
Hypothesis Hceil : hl_ceil L + SS <= sp.
Hypothesis Hsptop : sp <= hl_sptop L.
Hypothesis Htop : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis Prok : L5.ra_ok r.
Hypothesis OC : PML.obj_on_stack L sp C PMCS.CURSOR_SIZE.
Hypothesis OI : PML.obj_on_stack L sp IS 272.
Hypothesis OE : PML.obj_on_stack L sp E 16.
Hypothesis AP : PML.apart C PMCS.CURSOR_SIZE IS 272 /\ PML.apart C PMCS.CURSOR_SIZE E 16 /\ PML.apart IS 272 E 16.
Hypothesis INch : In (ch, 16384) LBo.
Hypothesis INrep : forall b, In b (PML.srep_blocks rep) -> In b LBo.
Hypothesis NEch : forall b, In b (PML.srep_blocks rep) -> fst b <> ch.
Hypothesis R0sp : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis R0tp : getr R0 4%bv = Z_to_bv 64 PML.TP.
Hypothesis HK0 : K [].
Hypothesis DC0 : L5.defined M0 C PMCS.CURSOR_SIZE.
Hypothesis CONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (cr' : credit) (ps' : PML.pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (bof' dn' : bool),
  PML.fp_ok fx' ->
  PMCS.cursor_at M' C IS ch bof' dn' ps' -> PML.isrc_at M' IS rep gp' rdst' -> PMCS.rn_bound ps' IS rep gp' Bs -> PML.ec_at M' E code -> PML.ls_ok g' M' ->
  (g' = g0 \/ (g' = PML.regJ g0 /\ code <> 0)) -> PMCUR.wf_c ps' -> PML.win_ok M' LBo ps' -> PML.pcredit_x L cr' ps' kx bx ->
  PMCS.rn_rel ps0 ps' code dn' M' V LBo ->
  regs_preserved R0 R' -> L5C.hpres L LBk sp SS (RNI.Wr C IS E) M0 M' -> model_but_vm model0 model' -> hi_heap HI (PML.ps_blocks ps' ++ LBo) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' r M' model') K.

Definition ginv := RNI.ginv L HI STRTOD_SCR LBo sp C IS E ch kx bx Bs rep g0 M0 model0.
Lemma lay : 2 ^ 40 <= sp /\ sp mod 16 = 0 /\ sp <= C /\ C + 656 <= hl_sptop L /\ sp <= IS /\ IS + 272 <= hl_sptop L /\ sp <= V /\ V + 48 <= hl_sptop L /\ sp <= E /\ E + 16 <= hl_sptop L /\
            0xf8000 <= hl_ceil L /\ hl_ceil L + SS <= sp /\ SS = 144 + PMS.PSOME_SCR STRTOD_SCR /\ 9376 <= PMS.PSOME_SCR STRTOD_SCR /\ PMS.PSOME_SCR STRTOD_SCR = 128 + PMS.PF_SCR STRTOD_SCR.
Proof. eapply RNI.lay; eassumption. Qed.
Lemma mk_entry : forall R M spc rc scr, getr R 1%bv = Z_to_bv 64 rc -> L5.ra_ok rc -> getr R 2%bv = Z_to_bv 64 spc -> getr R 4%bv = Z_to_bv 64 PML.TP ->
  (forall a, sp - SS <= a < sp -> M (Z_to_bv 64 a) <> None) -> spc mod 16 = 0 -> sp - SS <= spc - scr -> spc <= sp -> 0 <= scr -> PML.entry L R M spc rc scr.
Proof.
  intros R M spc rc scr H1 Hra H2 H4 F2 Hal Hlo Hhi Hscr. split; [exact H1|]. split; [exact Hra|]. split; [exact H2|]. split; [exact H4|].
  eapply RNI.mk_stk; eassumption.
Qed.
Lemma oos : forall spc o sz, PML.obj_on_stack L sp o sz -> spc <= sp -> PML.obj_on_stack L spc o sz.
Proof. intros spc o sz (A & B & C') H. split; [lia | split; assumption]. Qed.
Lemma ginv_g0 : forall M model cr ps gp rdst bof g B, ginv M model cr ps gp rdst 0 bof g B -> g = g0.
Proof. intros M model cr ps gp rdst bof g B (_ & _ & _ & _ & _ & _ & _ & _ & GG & _). destruct GG as [->|(_ & X)]; [reflexivity | exfalso; apply X; reflexivity]. Qed.

Lemma foot_C : forall a, C <= a < C + 656 -> RNI.foot C IS E a.
Proof. intros a Ha HO. apply (HO (C, PMCS.CURSOR_SIZE) (or_introl eq_refl)). unfold L5.in_rng, PMCS.CURSOR_SIZE. cbn [fst snd]. lia. Qed.

Lemma finish : forall (fx : FPState) R M model cr ps gp rdst code bof g B,
  PML.fp_ok fx -> ginv M model cr ps gp rdst code bof g B -> regs_preserved R0 R -> PMCS.rn_rel ps0 ps code false M V LBo ->
  srealizes RSEGS SCFG (@PML.cfg fx R r M model) K.
Proof.
  intros fx R M model cr ps gp rdst code bof g B Hfp (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN) RP REL.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & _).
  assert (DCM : L5.defined M C PMCS.CURSOR_SIZE).
  { intros i Hi. unfold PMCS.CURSOR_SIZE in Hi. apply (DW (C + i)); [lia | exact (foot_C (C + i) ltac:(lia)) | apply DC0; unfold PMCS.CURSOR_SIZE; exact Hi]. }
  apply (CONT fx R M model cr ps code gp rdst g bof false Hfp); try assumption.
  - destruct RDR as [SRC _]. split; [exact SRC|]. split; [exact PAR|]. split; [exact VIS|]. split; [exact DN | exact DCM].
  - unfold PMCS.rn_bound. destruct BB as [BB1 BB2]. destruct ISRC as (_ & _ & _ & _ & _ & _ & GR & _). fold D n in GR. unfold PMCS.undelivered. fold D n.
    pose proof (RB.win_cells M P ps PAR) as (_ & _ & W3). unfold PML.winlen, RB.wp, RB.we in *. destruct (PML.ps_win ps) as [[p e]|]; lia.
  - destruct FR as [F1 F2]. apply L5C.hpres_intro.
    + intros a (Ha & HC & HE & HO). apply F1; [exact Ha | exact HC | intros X; exact (X HO) | exact HE].
    + intros i Hi. apply F2. lia.
    + intros a Ha HC HE Hd. destruct (classic (L5.outside (RNI.Wr C IS E) a)) as [Y|N]; [rewrite (F1 a Ha HC (fun X => X Y) HE); exact Hd | exact (DW a Ha N Hd)].
Qed.

Lemma blk : forall M model cr ps, hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model) ->
  TK2.blocks_ok L (PML.ps_blocks ps ++ LBo) /\ (forall b, In b (PML.ps_blocks ps ++ LBo) -> 0 <= fst b /\ fst b + snd b <= hl_ceil L /\ 0 < snd b /\ (fst b + snd b <= 0x10000 \/ 0xf8000 <= fst b)).
Proof. intros. eapply RNI.blk; eassumption. Qed.
Lemma hfacts : forall M model cr ps, hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model) ->
  (forall b, In b (PML.ps_blocks ps ++ LBo) -> fst b <> ch -> PML.apart (fst b) (snd b) ch 16384) /\
  PML.ps_bptr ps <> ch /\ PML.ps_sb ps <> ch /\ (forall b, In b LBk -> PML.apart (fst b) (snd b) ch 16384) /\
  0 <= ch /\ ch + 16384 <= hl_ceil L /\ (ch + 16384 <= 0x10000 \/ 0xf8000 <= ch) /\ L5.defined M ch 16384 /\ block_range L ch 16384.
Proof. intros. eapply RNI.hfacts; eassumption. Qed.
Lemma ginv_stack : forall M M' model cr ps gp rdst code bof g B lo hi,
  ginv M model cr ps gp rdst code bof g B -> TK.samem (fun a => ~ (lo <= a < hi)) M M' -> mem_grows M M' -> sp - SS <= lo -> hi <= sp ->
  ginv M' model cr ps gp rdst code bof g B.
Proof. intros. eapply RNI.ginv_stack; eassumption. Qed.
Lemma ginv_ptrans : forall M M' model model' cr cr' ps ps' gp rdst bof code' g' B spc scr,
  ginv M model cr ps gp rdst 0 bof g0 B ->
  L5C.hpres L LBo spc scr (PMS.W_parc P V E) M M' -> sp - SS <= spc - scr -> spc <= sp -> 0 <= scr -> spc mod 16 = 0 ->
  model_but_vm model model' -> hi_heap HI (PML.ps_blocks ps' ++ LBo) cr' M' (m_vmmaps model') ->
  PML.parser_at M' P ps' -> PMCUR.wf_c ps' -> PML.win_ok M' LBo ps' -> PML.buf_bound ps' B -> PML.ec_at M' E code' -> PML.ls_ok g' M' ->
  (g' = g0 \/ (g' = PML.regJ g0 /\ code' <> 0)) -> PML.pcredit_x L cr' ps' kx bx ->
  ginv M' model' cr' ps' gp rdst code' bof g' B.
Proof. intros. eapply RNI.ginv_ptrans; eassumption. Qed.
Lemma ginv_chunk : forall M M' model cr ps gp rdst bof gp' rdst' code' bof' g' B spc,
  ginv M model cr ps gp rdst 0 bof g0 B -> PMS.win_exhausted ps ->
  L5.frame_but ((spc - 512, 512) :: RNI.Wc C IS E ch) M M' -> mem_grows M M' -> sp - SS <= spc - 512 -> spc <= sp ->
  PMCS.rdc_at M' S IS ch bof' -> PML.isrc_at M' IS rep gp' rdst' -> gp <= gp' -> PML.ec_at M' E code' -> PML.ls_ok g' M' -> (g' = g0 \/ (g' = PML.regJ g0 /\ code' <> 0)) ->
  ginv M' model cr ps gp' rdst' code' bof' g' B.
Proof. intros. eapply RNI.ginv_chunk; eassumption. Qed.
Lemma ginv_setwin : forall M M' model cr ps gp rdst bof g B p' k,
  ginv M model cr ps gp rdst 0 bof g B -> PMS.win_exhausted ps ->
  TK.samem (fun a => ~ (C + 512 <= a < C + 528)) M M' -> mem_grows M M' ->
  PML.u64 M' (C + 512) (p' + k) -> PML.u64 M' (C + 520) p' -> 0 < k -> ch <= p' -> p' + k <= ch + 16384 -> (B + k) + (D + n - gp) <= Bs ->
  ginv M' model cr (PML.ps_set_win ps (Some (p', p' + k))) gp rdst 0 bof g (B + k).
Proof. intros. eapply RNI.ginv_setwin; eassumption. Qed.

Lemma call_psome : forall (fx : FPState) R M model cr ps gp rdst bof B spc rc,
  PML.fp_ok fx -> ginv M model cr ps gp rdst 0 bof g0 B -> PML.ps_more ps = true ->
  getr R 1%bv = Z_to_bv 64 rc -> L5.ra_ok rc -> getr R 2%bv = Z_to_bv 64 spc -> getr R 4%bv = Z_to_bv 64 PML.TP ->
  getr R 10%bv = Z_to_bv 64 P -> getr R 11%bv = Z_to_bv 64 V -> getr R 12%bv = Z_to_bv 64 E ->
  spc mod 16 = 0 -> sp - SS <= spc - PMS.PSOME_SCR STRTOD_SCR -> spc <= sp ->
  (forall (fx' : FPState) R' M' model' cr' ps' code' g', PML.fp_ok fx' -> regs_preserved R R' -> ginv M' model' cr' ps' gp rdst code' bof g' B ->
      (code' <> 0 -> PML.ps_more ps' = false) ->
      ((code' <> 0 \/ PML.ps_more ps' = false \/ PMS.win_exhausted ps') /\
       (PML.ps_st ps = PML.ST_ACCEPT -> code' = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) /\
       (PMS.win_exhausted ps -> code' = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR])) ->
      PMCUR.cur_post RSEGS ps ps' code' M' V -> PML.win_ok M' LBo ps -> TK.samem (fun a => spc <= a < sp) M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rc M' model') K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PARSE_SOME M model) K.
Proof.
  intros fx R M model cr ps gp rdst bof B spc rc Hfp GI MT H1 Hra H2 H4 H10 H11 H12 Hal Hlo Hhi Hcont.
  pose proof GI as (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN).
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2].
  apply (PSOME LBo cr spc rc P V E B kx bx g0 ps fx R M model K HH MOK HK0 Hfp).
  { split; [exact (mk_entry R M spc rc _ H1 Hra H2 H4 (proj2 FR) Hal Hlo Hhi ltac:(lia))|]. split; [split; [split; [exact H10 | split; [exact H11 | exact H12]] | exact MT]|].
    split; [exact PAR|]. split; [exact WF|]. split; [exact WOK|]. split; [exact BB|].
    split; [exact VIS|]. split; [exact EC|]. split; [exact LS|]. split; [exact G0|]. split; [exact PC|].
    destruct OC as (O1 & O2 & O3). destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in *.
    assert (M8 : forall k, k mod 8 = 0 -> (C + k) mod 8 = 0) by (intros k Hk; rewrite Z.add_mod by lia; rewrite O3, Hk; reflexivity).
    split; [unfold P; split; [lia | split; [lia | exact (M8 320 eq_refl)]]|]. split; [unfold V; split; [lia | split; [lia | exact (M8 592 eq_refl)]]|].
    split; [exact (oos spc E 16 OE Hhi)|]. unfold P, V. split; [lia|]. split; lia. }
  intros fx' R' M' model' LB' cr' LBk' W Hfp' (ps' & code' & g' & PAR' & WF' & WOK' & BB' & EC' & CM & LS' & GG' & -> & -> & -> & PC' & REL & CUR) RP HP BV' HH'.
  assert (GI' : ginv M' model' cr' ps' gp rdst code' bof g' B)
    by exact (ginv_ptrans M M' model model' cr cr' ps ps' gp rdst bof code' g' B spc _ GI HP ltac:(lia) Hhi ltac:(lia) Hal BV' HH' PAR' WF' WOK' BB' EC' LS' GG' PC').
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  assert (BOKo : TK2.blocks_ok L LBo) by (intros b Hb; apply BOK; apply in_or_app; right; exact Hb).
  assert (STK : L5C.stk (hl_sptop L) M spc (PMS.PSOME_SCR STRTOD_SCR)) by (destruct (mk_entry R M spc rc _ H1 Hra H2 H4 (proj2 FR) Hal Hlo Hhi ltac:(lia)) as (_ & _ & _ & _ & X); exact X).
  pose proof (TK2.hpres_samem L LAY LBo spc _ _ M M' HP BOKo STK ltac:(lia)) as AG.
  assert (WSI : TK2.w_si L (PMS.W_parc P V E)) by (intros w Hw; unfold PMS.W_parc, PML.W_par in Hw; repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; unfold P, V; unfold hl_ceil in *; lia|]); destruct Hw).
  apply (Hcont fx' R' M' model' cr' ps' code' g' Hfp' RP GI' CM REL CUR).
  - apply (RB.win_ok_x _ M M' AG); [|exact WOK]. intros b Hb. pose proof (BOKo b Hb) as (B0 & B1 & B2 & B3 & B4). rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1.
    unfold hl_ceil in *. split; [lia|]. split; [lia|]. destruct b as [p cap]. exact (TK2.cov_block L LAY _ _ _ _ p cap WSI Hb (BOKo (p, cap) Hb)).
  - apply (TK.samem_weaken _ _ _ _ AG). intros a Ha. split; [|left; lia]. intros w Hw Hin. unfold PMS.W_parc, PML.W_par in Hw. unfold L5.in_rng in Hin. unfold hl_ceil in *. unfold P, V in Hw.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hin; lia.
Qed.

Lemma ginv_setec : forall M M' model cr ps gp rdst bof B spc code',
  ginv M model cr ps gp rdst 0 bof g0 B -> L5.frame_but ((spc - 256, 256) :: RNI.We E) M M' -> mem_grows M M' -> sp - SS <= spc - 256 -> spc <= sp ->
  PML.ec_at M' E code' -> code' <> 0 -> PML.ls_ok (PML.regJ g0) M' ->
  ginv M' model cr ps gp rdst code' bof (PML.regJ g0) B.
Proof. intros. eapply RNI.ginv_setec; eassumption. Qed.

Lemma call_chunk : forall (fx : FPState) R M model cr ps gp rdst bof B spc rc,
  PML.fp_ok fx -> ginv M model cr ps gp rdst 0 bof g0 B -> PMS.win_exhausted ps ->
  getr R 1%bv = Z_to_bv 64 rc -> L5.ra_ok rc -> getr R 2%bv = Z_to_bv 64 spc -> getr R 4%bv = Z_to_bv 64 PML.TP -> getr R 10%bv = Z_to_bv 64 S -> getr R 11%bv = Z_to_bv 64 E ->
  spc mod 16 = 0 -> sp - SS <= spc - 512 -> spc <= sp ->
  (forall (fx' : FPState) R' M' p k gp' rdst' code' bof' g', PML.fp_ok fx' -> regs_preserved R R' -> ginv M' model cr ps gp' rdst' code' bof' g' B ->
      getr R' 10%bv = Z_to_bv 64 p -> getr R' 11%bv = Z_to_bv 64 k -> 0 <= p -> p + k < 2 ^ 64 -> 0 <= k <= 16384 -> (0 < k -> ch <= p /\ p + k <= ch + 16384) ->
      gp <= gp' -> k <= gp' - gp -> (code' = 0 -> k = 0 -> rdst' = 2) -> (rdst' = 0 \/ rdst' = 2) -> TK.samem (fun a => spc <= a < sp) M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rc M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_READ_CHUNK M model) K.
Proof.
  intros fx R M model cr ps gp rdst bof B spc rc Hfp GI WEX H1 Hra H2 H4 H10 H11 Hal Hlo Hhi Hcont.
  pose proof GI as (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & (Hh & Hl & Hmat) & BV & PC & BB & BG & FR & DW & DN).
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  destruct (hfacts _ _ _ _ HH) as (HA & N1 & N2 & HK & C0 & C1 & C2 & C3 & C4).
  pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK.
  destruct OC as (O1 & O2 & O3). destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in *.
  apply (RCHUNK spc rc S IS E ch gp rdst rep bof g0 fx R M model K Hh Hl HK0 Hfp).
  { split; [exact (mk_entry R M spc rc _ H1 Hra H2 H4 (proj2 FR) Hal Hlo Hhi ltac:(unfold PMCS.RCHUNK_SCR; lia))|]. split; [exact H10|]. split; [exact H11|].
    split; [exact RDR|]. split; [exact ISRC|]. split; [exact EC|]. split; [exact LS|]. split; [exact G0|]. split; [exact Hn|].
    split; [unfold S; split; [lia | split; [lia | rewrite Z.add_mod by lia; rewrite O3; reflexivity]]|]. split; [exact (oos spc IS 272 OI Hhi)|]. split; [exact (oos spc E 16 OE Hhi)|].
    unfold S. split; [unfold PML.apart; lia|]. split; [unfold PML.apart; lia|]. split; [unfold PML.apart; lia|]. split; [exact C4|]. split; [exact C3|].
    intros b Hb. assert (Hb' : In b (PML.ps_blocks ps ++ LBo)) by (apply in_or_app; right; exact (INrep b Hb)). split; [exact (BOK b Hb') | exact (HA b Hb' (NEch b Hb))]. }
  intros fx' R' M' Hfp' (p & k & gp' & rdst' & code' & bof' & g' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & RDR' & ISRC' & Q7 & Q8 & Q9 & EC' & LS' & GG') RP FB MG.
  unfold PMCS.RCHUNK_SCR in FB.
  apply (Hcont fx' R' M' p k gp' rdst' code' bof' g' Hfp' RP); try assumption.
  - exact (ginv_chunk M M' model cr ps gp rdst bof gp' rdst' code' bof' g' B spc GI WEX FB MG Hlo Hhi RDR' ISRC' Q7 EC' LS' GG').
  - destruct ISRC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X.
  - pose proof (TK2.frame_but_samem _ _ _ FB) as AG. apply (TK.samem_weaken _ _ _ _ AG). intros a Ha w Hw Hin. unfold L5.in_rng in Hin. unfold hl_ceil in *.
    clear - Hw Hin Ha Hlo Y1 Y3 Y5 Y9 Y11 Y12 Y13 Y14 C1. unfold RNI.Wc in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Hin; lia.
Qed.

Lemma gcells : forall M model cr ps gp rdst code bof g B, ginv M model cr ps gp rdst code bof g B ->
  PML.u64 M (C + 248) IS /\ PML.u64 M IS PML.VT_ISS /\ PML.u32 M (IS + 152) rdst /\ PML.u8 M (IS + 152) rdst /\ (rdst = 0 \/ rdst = 2) /\ PML.img_ro M /\
  PML.u64 M (C + 296) 0 /\ PML.u64 M (C + 512) (RB.we ps) /\ PML.u64 M (C + 520) (RB.wp ps) /\ 0 <= RB.wp ps <= RB.we ps /\ RB.we ps < 2 ^ 62 /\
  PML.u32 M E code /\ 0 <= code < 2 ^ 31 /\ L5.defined M (C + 512) 16 /\
  PML.u8 M (C + 528) (PML.ps_st ps mod 256) /\ PML.u8 M (C + 531) (PML.b2z (PML.ps_more ps)) /\ PML.u8 M (C + 532) (PML.b2z (PML.ps_done ps)) /\ D <= gp <= D + n.
Proof.
  intros M model cr ps gp rdst code bof g B (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN).
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2].
  destruct RDR as ((A240 & A248 & A264 & A272 & Ade & A288 & A296 & Aio & A32) & Adef).
  unfold PML.isrc_at in ISRC. cbv zeta in ISRC. destruct ISRC as (I0 & I16 & I24 & I32 & I40 & I48 & Ig & I56 & I64 & I72 & Is & I104 & I112 & I120 & Iio & Ird & Idef).
  destruct Iio as (J32 & _). replace (IS + 120 + 32) with (IS + 152) in J32 by lia.
  pose proof (RB.win_cells M P ps PAR) as (W1 & W2 & W3). unfold P in W1, W2. replace (C + 320 + 200) with (C + 520) in W1 by lia. replace (C + 320 + 192) with (C + 512) in W2 by lia.
  destruct (hfacts _ _ _ _ HH) as (_ & _ & _ & _ & C0 & C1 & _).
  assert (WR : 0 <= RB.wp ps /\ RB.we ps < 2 ^ 62).
  { unfold RB.wp, RB.we, PML.win_ok in *. destruct (PML.ps_win ps) as [[p e]|]; [|lia]. destruct WOK as (ch' & Hin & H1 & H2 & _).
    pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH (ch', 16384) ltac:(apply in_or_app; right; exact Hin)) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in *. unfold hl_ceil in *. lia. }
  destruct EC as (E0 & Edef & Ecode).
  unfold PML.parser_at in PAR. destruct PAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A208 & _ & _ & A211 & A212 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pdef).
  unfold P in A208, A211, A212, Pdef. replace (C + 320 + 208) with (C + 528) in A208 by lia. replace (C + 320 + 211) with (C + 531) in A211 by lia. replace (C + 320 + 212) with (C + 532) in A212 by lia.
  unfold S in *. replace (C + 8 + 240) with (C + 248) in A240 by lia. replace (C + 8 + 288) with (C + 296) in A288 by lia.
  split; [exact A240|]. split; [exact I0|]. split; [exact J32|]. split; [apply RB.u32_u8_low; [lia | lia | lia | exact J32]|]. split; [exact Ird|]. split; [exact (proj1 LS)|].
  split; [exact A288|]. split; [exact W2|]. split; [exact W1|]. split; [lia|]. split; [lia|]. split; [exact E0|]. split; [lia|].
  split; [intros i Hi; replace (C + 512 + i) with (C + 320 + (192 + i)) by lia; apply Pdef; lia|].
  split; [exact (RB.u8_mod _ _ _ A208)|]. split; [exact A211|]. split; [exact A212|]. exact Ig.
Qed.

Definition KSM : list nat := [3; 4; 24; 25; 26; 27]%nat.
Definition rn_regs (R : bvmap 5 word) : Prop :=
  getr R 2%bv = Z_to_bv 64 (sp - 80) /\ getr R 8%bv = Z_to_bv 64 E /\ getr R 9%bv = Z_to_bv 64 C /\ getr R 18%bv = Z_to_bv 64 V /\ getr R 19%bv = Z_to_bv 64 P /\
  getr R 20%bv = Z_to_bv 64 S /\ getr R 21%bv = Z_to_bv 64 1 /\ getr R 22%bv = Z_to_bv 64 2 /\ TK.keepsR KSM R0 R.
Definition rn_fr (M : mem) : Prop := RNS.rn_frame M sp r R0.
Lemma KSM_KSQ : forall q, In q KSM -> In q RNS.KSQ. Proof. intros q Hq. clear - Hq. cbn in Hq |- *. intuition lia. Qed.
Lemma KSM_KSP : forall q, In q KSM -> In q RNS.KSP. Proof. intros q Hq. clear - Hq. cbn in Hq |- *. intuition lia. Qed.
Lemma KSM_KSL : forall q, In q KSM -> In q RNS.KSL. Proof. intros q Hq. clear - Hq. cbn in Hq |- *. intuition lia. Qed.
Lemma KSM_KSE : forall q, In q KSM -> In q RNS.KSE. Proof. intros q Hq. clear - Hq. cbn in Hq |- *. intuition lia. Qed.
Lemma rn_fr_x : forall M M' lo, TK.samem (fun a => lo <= a < sp) M M' -> lo <= sp - 80 -> rn_fr M -> rn_fr M'.
Proof.
  intros M M' lo AG Hlo (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). pose proof lay as (Y1 & _).
  repeat split; (eapply (TK2.u64_x _ M M' AG); [lia | intros i Hi; lia | eassumption]).
Qed.
Lemma rn_tp : forall R, rn_regs R -> getr R 4%bv = Z_to_bv 64 PML.TP.
Proof. intros R (_ & _ & _ & _ & _ & _ & _ & _ & KR). rewrite (KR 4%bv ltac:(kin)). exact R0tp. Qed.
Lemma al80 : (sp - 80) mod 16 = 0. Proof. pose proof lay as (_ & Y2 & _). apply RNI.al16; [exact Y2 | reflexivity]. Qed.
Lemma rn_regs_rp : forall R R' : bvmap 5 word, rn_regs R -> regs_preserved R R' -> rn_regs R'.
Proof.
  intros R R' (C2 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & KR) RP.
  split; [rewrite (RP 2%bv ltac:(kin)); exact C2|]. split; [rewrite (RP 8%bv ltac:(kin)); exact C8|]. split; [rewrite (RP 9%bv ltac:(kin)); exact C9|].
  split; [rewrite (RP 18%bv ltac:(kin)); exact C18|]. split; [rewrite (RP 19%bv ltac:(kin)); exact C19|]. split; [rewrite (RP 20%bv ltac:(kin)); exact C20|].
  split; [rewrite (RP 21%bv ltac:(kin)); exact C21|]. split; [rewrite (RP 22%bv ltac:(kin)); exact C22|].
  assert (KP : TK.keepsR KSM R R') by (apply TK.keepsR_preserved; [exact RP | intros q Hq; clear - Hq; cbn in Hq |- *; intuition (subst; cbn; tauto)]).
  intros q Hq. rewrite (KP q Hq). exact (KR q Hq).
Qed.

Lemma rn_regs_keepL : forall R R' : bvmap 5 word, rn_regs R -> TK.keepsR RNS.KSL R R' -> getr R' 2%bv = Z_to_bv 64 (sp - 80) -> rn_regs R'.
Proof.
  intros R R' (C2 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & KR) KS R'sp.
  split; [exact R'sp|]. split; [rewrite (KS 8%bv ltac:(kin)); exact C8|]. split; [rewrite (KS 9%bv ltac:(kin)); exact C9|].
  split; [rewrite (KS 18%bv ltac:(kin)); exact C18|]. split; [rewrite (KS 19%bv ltac:(kin)); exact C19|]. split; [rewrite (KS 20%bv ltac:(kin)); exact C20|].
  split; [rewrite (KS 21%bv ltac:(kin)); exact C21|]. split; [rewrite (KS 22%bv ltac:(kin)); exact C22|].
  intros q Hq. rewrite (KS q); [exact (KR q Hq)|]. first [exact (KSM_KSL _ Hq) | exact (KSM_KSQ _ Hq)].
Qed.
Lemma rn_regs_keepQ : forall R R' : bvmap 5 word, rn_regs R -> TK.keepsR RNS.KSQ R R' -> getr R' 2%bv = Z_to_bv 64 (sp - 80) -> getr R' 21%bv = Z_to_bv 64 1 -> getr R' 22%bv = Z_to_bv 64 2 -> rn_regs R'.
Proof.
  intros R R' (C2 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & KR) KS R'sp R'21 R'22.
  split; [exact R'sp|]. split; [rewrite (KS 8%bv ltac:(kin)); exact C8|]. split; [rewrite (KS 9%bv ltac:(kin)); exact C9|].
  split; [rewrite (KS 18%bv ltac:(kin)); exact C18|]. split; [rewrite (KS 19%bv ltac:(kin)); exact C19|]. split; [rewrite (KS 20%bv ltac:(kin)); exact C20|].
  split; [exact R'21|]. split; [exact R'22|].
  intros q Hq. rewrite (KS q); [exact (KR q Hq)|]. first [exact (KSM_KSL _ Hq) | exact (KSM_KSQ _ Hq)].
Qed.

Lemma rp_back : forall R R' : bvmap 5 word, TK.keepsR KSM R0 R -> getr R' 2%bv = Z_to_bv 64 sp -> RNS.same_s07 R0 R' -> TK.keepsR RNS.KSX R R' -> regs_preserved R0 R'.
Proof.
  intros R R' KR R'sp (S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23) KS q Hq. unfold callee_saved_idx in Hq. cbn [In] in Hq.
  assert (Q : forall z : Z, bv_unsigned q = z -> 0 <= z < 32 -> q = Z_to_bv 5 z) by (intros z <- _; symmetry; apply Z_to_bv_bv_unsigned).
  destruct Hq as [Hq|Hq]; [rewrite (Q 2 (eq_sym Hq) ltac:(lia)); etransitivity; [exact R'sp | symmetry; exact R0sp]|].
  assert (KQ : In (ridx q) RNS.KSX -> getr R' q = getr R0 q) by (intros X; rewrite (KS q X); exact (KR q X)).
  repeat (destruct Hq as [Hq|Hq]; [first [rewrite (Q _ (eq_sym Hq) ltac:(lia)); assumption | apply KQ; unfold ridx; rewrite <- Hq; cbn; tauto]|]). destruct Hq.
Qed.

Lemma rn_exit : forall (fx : FPState) R M model cr ps gp rdst code bof g B,
  PML.fp_ok fx -> ginv M model cr ps gp rdst code bof g B -> getr R 2%bv = Z_to_bv 64 (sp - 80) -> TK.keepsR KSM R0 R -> rn_fr M -> PMCS.rn_rel ps0 ps code false M V LBo ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.EPI M model) K.
Proof.
  intros fx R M model cr ps gp rdst code bof g B Hfp GI R2 KR CF REL.
  pose proof GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hh & Hl & _) & _).
  apply (RNS.s_epi FPM fx R M model K sp r R0 Hh Hl Hfp R2 SPOK CF Prok).
  intros fx' R' Hfp' R'sp SAME KS'.
  exact (finish fx' R' M model cr ps gp rdst code bof g B Hfp' GI (rp_back R R' KR R'sp SAME KS') REL).
Qed.

Lemma finish_done : forall (fx : FPState) R M M' model cr ps gp rdst bof g B,
  PML.fp_ok fx -> ginv M model cr ps gp rdst 0 bof g B -> TK.samem (fun a => ~ (C + 640 <= a < C + 641)) M M' -> mem_grows M M' -> PML.u8 M' (C + 640) 1 ->
  regs_preserved R0 R -> PML.ps_st ps0 <> PML.ST_ACCEPT -> srealizes RSEGS SCFG (@PML.cfg fx R r M' model) K.
Proof.
  intros fx R M M' model cr ps gp rdst bof g B Hfp (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN) AG MG C640 RP NA.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2].
  destruct (blk _ _ _ _ HH) as [BOK BF].
  assert (INo : forall b, In b LBo -> In b (PML.ps_blocks ps ++ LBo)) by (intros b Hb; apply in_or_app; right; exact Hb).
  set (KK := fun a => ~ (C + 640 <= a < C + 641)) in *.
  assert (CB : forall b, In b (PML.ps_blocks ps ++ LBo) -> TK2.cov KK (fst b) (snd b)) by (intros b Hb i Hi; destruct (BF b Hb); unfold KK, hl_ceil in *; lia).
  assert (CO : forall lo len, (lo + len <= C + 640 \/ C + 641 <= lo) -> TK2.cov KK lo len) by (intros lo len H i Hi; unfold KK; lia).
  destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in *.
  assert (DCM : L5.defined M C PMCS.CURSOR_SIZE).
  { intros i Hi. unfold PMCS.CURSOR_SIZE in Hi. apply (DW (C + i)); [lia | exact (foot_C (C + i) ltac:(lia)) | apply DC0; unfold PMCS.CURSOR_SIZE; exact Hi]. }
  pose proof (BF _ (or_introl eq_refl)) as X1. pose proof (BF _ (or_intror (or_introl eq_refl))) as X2. cbn [fst snd] in X1, X2.
  assert (PCOV : TK2.ps_cov KK ps).
  { unfold hl_ceil in *. split; [lia|]. split; [lia|]. split; [exact (CB _ (or_introl eq_refl))|]. split; [lia|]. split; [lia|]. exact (CB _ (or_intror (or_introl eq_refl))). }
  apply (CONT fx R M' model cr ps 0 gp rdst g bof true Hfp).
  - split; [exact (proj1 (RNI.rdc_at_x KK M M' AG S IS ch bof ltac:(unfold S; lia) ltac:(apply CO; unfold S; lia) RDR))|].
    split; [apply (TK2.parser_at_x _ M M' AG); [unfold P; lia | apply CO; unfold P; lia | exact PCOV | exact PAR]|].
    split; [apply (TK2.vis_at_x _ M M' AG); [unfold V; lia | apply CO; unfold V; lia | exact VIS]|].
    split; [exact C640 | exact (L5.defined_grows _ _ _ _ MG DCM)].
  - apply (TK2.isrc_at_x _ M M' AG); [lia | apply CO; lia | | exact ISRC].
    split; [apply CO; lia|]. destruct rep as [s|cap p s]; [exact I|]. pose proof (INo _ (INrep _ (or_introl eq_refl))) as Hb. pose proof (BF _ Hb) as X. cbn [fst snd] in X. unfold hl_ceil in *.
    split; [lia|]. split; [lia|]. exact (CB _ Hb).
  - unfold PMCS.rn_bound. destruct BB as [BB1 BB2]. destruct ISRC as (_ & _ & _ & _ & _ & _ & GR & _). fold D n in GR. unfold PMCS.undelivered. fold D n.
    pose proof (RB.win_cells M P ps PAR) as (_ & _ & W3). unfold PML.winlen, RB.wp, RB.we in *. destruct (PML.ps_win ps) as [[p e]|]; lia.
  - apply (TK2.ec_at_x _ M M' AG); [lia | apply CO; lia | exact EC].
  - apply (TK2.ls_ok_x _ M M' AG); [|exact LS]. apply TK2.statics_cov_lo; intros a Ha; unfold KK; unfold hl_ceil in *; lia.
  - exact GG.
  - exact WF.
  - apply (RB.win_ok_x _ M M' AG); [|exact WOK]; intros b Hb; destruct (BF b (INo b Hb)); unfold hl_ceil in *; split; [lia|]; split; [lia | exact (CB b (INo b Hb))].
  - exact PC.
  - split; [intros X; contradiction | intros _ X; discriminate X].
  - exact RP.
  - destruct FR as [F1 F2]. apply L5C.hpres_intro.
    + intros a (Ha & HC & HE & HO). rewrite (AG a Ha); [apply F1; [exact Ha | exact HC | intros X; exact (X HO) | exact HE]|].
      unfold KK. intros Hc. exact (foot_C a ltac:(lia) HO).
    + intros i Hi. apply MG. apply F2. lia.
    + intros a Ha HC HE Hd. apply MG. destruct (classic (L5.outside (RNI.Wr C IS E) a)) as [Y|N]; [rewrite (F1 a Ha HC (fun X => X Y) HE); exact Hd | exact (DW a Ha N Hd)].
  - exact BV.
  - apply (TK2.heap_pure_write L HI HIok LAY _ _ M M' _ _ HH ltac:(lia) AG MG). intros a Ha NK. unfold KK in NK. unfold hl_ceil in *. left. lia.
Qed.

Lemma rn_tail : forall (fx : FPState) R M model cr ps gp rdst bof B,
  PML.fp_ok fx -> ginv M model cr ps gp rdst 0 bof g0 B -> getr R 2%bv = Z_to_bv 64 (sp - 80) -> getr R 8%bv = Z_to_bv 64 E -> TK.keepsR KSM R0 R -> rn_fr M ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.TAILEPI M model) K.
Proof.
  intros fx R M model cr ps gp rdst bof B Hfp GI R2 R8 KR CF.
  pose proof GI as (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & (Hh & Hl & Hmat) & BV & PC & BB & BG & FR & DW & DN).
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2].
  pose proof Prok as [Pr1 Pr2].
  apply (RNS.s_tailepi FPM fx R M model K sp r R0 Hh Hl Hfp R2 SPOK CF ltac:(lia)).
  intros fx' R' Hfp' R'sp R'ra R'a0 R'a1 SAME KS'.
  assert (RP1 : regs_preserved R0 R') by exact (rp_back R R' KR R'sp SAME KS').
  assert (R'tp : getr R' 4%bv = Z_to_bv 64 PML.TP) by (rewrite (RP1 4%bv ltac:(kin)); exact R0tp).
  apply (SETEC E 1 sp r g0 fx' R' M model K Hh Hl HK0 Hfp').
  { split; [exact (mk_entry R' M sp r PMS.SETEC_SCR R'ra Prok R'sp R'tp (proj2 FR) (proj2 SPOK) ltac:(unfold PMS.SETEC_SCR; lia) ltac:(lia) ltac:(unfold PMS.SETEC_SCR; lia))|].
    split; [unfold PML.a0; rewrite R'a0; exact R8|]. split; [exact R'a1|]. split; [lia|]. split; [destruct EC as (_ & X & _); exact X|].
    split; [exact OE|]. split; [exact LS | exact G0]. }
  intros fx2 R2' M2 Hfp2 (EC2 & LS2 & _) RP2 FB2 MG2. unfold PMS.SETEC_SCR in FB2.
  assert (GI2 : ginv M2 model cr ps gp rdst 1 bof (PML.regJ g0) B) by exact (ginv_setec M M2 model cr ps gp rdst bof B sp 1 GI FB2 MG2 ltac:(lia) ltac:(lia) EC2 ltac:(lia) LS2).
  apply (finish fx2 R2' M2 model cr ps gp rdst 1 bof (PML.regJ g0) B Hfp2 GI2).
  - intros q Hq. rewrite (RP2 q Hq). exact (RP1 q Hq).
  - split; [intros _ X; discriminate X | intros X; discriminate X].
Qed.

Definition muA (ps : PML.pstate) (gp rdst : Z) : Z := ((2 * (D + n - gp) + ee rdst) * 2 + ww ps) * 4 + rank ps.
Definition atA (m : Z) : Prop := forall (fx : FPState) R M model cr ps gp rdst bof B,
  muA ps gp rdst < m -> PML.fp_ok fx -> ginv M model cr ps gp rdst 0 bof g0 B -> PML.ps_more ps = true ->
  (PML.ps_st ps0 = PML.ST_ACCEPT -> PML.ps_st ps = PML.ST_ACCEPT) -> PML.ps_level ps = PML.ps_level ps0 ->
  rn_regs R -> rn_fr M ->
  srealizes RSEGS SCFG (@PML.cfg fx R RNT.LOOP M model) K.

Lemma stop_mod : forall segs ps ps' M' V', PMCUR.cur_post segs ps ps' 0 M' V' -> PML.ps_more ps' = false -> PML.ps_st ps' mod 256 <> 1.
Proof.
  intros segs ps ps' M' V' (_ & H2) HM. destruct (H2 eq_refl HM) as [(_ & X & _)|(_ & e & _ & HE)].
  - rewrite X. intro H. vm_compute in H. discriminate H.
  - destruct e; cbn [PMCUR.ev_rel] in HE; unfold PMCUR.after_value_st in HE;
      repeat match type of HE with _ /\ _ => destruct HE as [HE _] end; try (cbn [In] in HE); unfold PML.ST_ACCEPT, PML.ST_EXPECT_COMMA_OR_END, PML.ST_EXPECT_COLON,
      PML.ST_EXPECT_MEMBER_NAME_OR_END, PML.ST_EXPECT_VALUE_OR_END in HE;
      repeat match type of HE with _ \/ _ => destruct HE as [HE|HE] end; try contradiction; first [rewrite HE | rewrite <- HE]; intro H; vm_compute in H; discriminate H.
Qed.

Lemma psome_call : forall m, atA m -> forall (fx : FPState) R M model cr ps gp rdst bof B nte,
  muA ps gp rdst <= m -> PML.fp_ok fx -> ginv M model cr ps gp rdst 0 bof g0 B -> PML.ps_more ps = true ->
  (PML.ps_st ps0 = PML.ST_ACCEPT -> PML.ps_st ps = PML.ST_ACCEPT) -> PML.ps_level ps = PML.ps_level ps0 ->
  rn_regs R -> rn_fr M ->
  getr R 1%bv = Z_to_bv 64 RNT.R_PSOME -> getr R 10%bv = Z_to_bv 64 P -> getr R 11%bv = Z_to_bv 64 V -> getr R 12%bv = Z_to_bv 64 E ->
  getr R 23%bv = Z_to_bv 64 nte -> (nte = 0 \/ nte = 1) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_PARSE_SOME M model) K.
Proof.
  intros m IH fx R M model cr ps gp rdst bof B nte Hm Hfp GI MT ACC LV CR CF H1 H10 H11 H12 H23 Hnte.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2]. destruct SPOK as [S1 S2].
  pose proof CR as (R2 & _).
  apply (call_psome fx R M model cr ps gp rdst bof B (sp - 80) RNT.R_PSOME Hfp GI MT H1 ltac:(apply ra_lit; [unfold RNT.R_PSOME; lia | reflexivity]) R2 (rn_tp R CR) H10 H11 H12 al80 ltac:(lia) ltac:(lia)).
  intros fx2 R2x M2 model2 cr2 ps2 code2 g2 Hfp2 RP2 GI2 CM (REL1 & REL2 & REL3) CUR WOLD AG2.
  assert (CR2 : rn_regs R2x) by exact (rn_regs_rp R R2x CR RP2).
  pose proof (rn_fr_x M M2 (sp - 80) AG2 ltac:(lia) CF) as CF2.
  pose proof (gcells _ _ _ _ _ _ _ _ _ _ GI2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cc & Rc & _ & Cst & Cmo & Cdn & Hgp2).
  pose proof GI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hh2 & Hl2 & _) & _).
  pose proof CR2 as (S2x & S8 & S9 & S18 & S19 & S20 & S21 & S22 & KR2).
  assert (X23 : getr R2x 23%bv = Z_to_bv 64 nte) by (rewrite (RP2 23%bv ltac:(kin)); exact H23).
  pose proof (Z.mod_pos_bound (PML.ps_st ps2) 256 ltac:(lia)) as STR. pose proof (b2z_range (PML.ps_done ps2)) as DNR. pose proof (b2z_range (PML.ps_more ps2)) as MOR.
  destruct OC as (O1 & O2 & O3). destruct OE as (E1 & E2 & E3).
  assert (KC : forall Rb qs, TK.keepsR qs R2x Rb -> (forall q, In q KSM -> In q qs) -> TK.keepsR KSM R0 Rb).
  { intros Rb qs KS HQ q Hq. rewrite (KS q (HQ _ Hq)). exact (KR2 q Hq). }
  assert (QM : forall q, In q KSM -> In q RNS.KSQ) by exact KSM_KSQ.
  assert (DC2 : L5.defined M2 C PMCS.CURSOR_SIZE).
  { pose proof GI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DW2 & _).
    intros i Hi. unfold PMCS.CURSOR_SIZE in Hi. apply (DW2 (C + i)); [lia | exact (foot_C (C + i) ltac:(lia)) | apply DC0; unfold PMCS.CURSOR_SIZE; exact Hi]. }
  apply (RNS.s_r_psome FPM fx2 R2x M2 model2 K sp C E code2 (PML.ps_st ps2 mod 256) (PML.b2z (PML.ps_done ps2)) (PML.b2z (PML.ps_more ps2)) nte
           Hh2 Hl2 Hfp2 S2x (conj S1 S2) S9 S8 ltac:(split; lia) ltac:(split; lia) S21 S22 X23 Hnte Cc Rc Cst Cdn Cmo ltac:(lia)
           ltac:(unfold PML.b2z; destruct (PML.ps_done ps2); lia) ltac:(unfold PML.b2z; destruct (PML.ps_more ps2); lia)).
  -
    intros NZ fx3 R3 Hfp3 R3sp KS3.
    apply (rn_exit fx3 R3 M2 model2 cr2 ps2 gp rdst code2 bof g2 B Hfp3 GI2 R3sp (KC R3 _ KS3 QM) CF2).
    split; [intros _ X; contradiction | intros X; contradiction].
  -
    intros Z0 N0 ST1 fx3 R3 Hfp3 R3sp KS3. subst code2.
    assert (NA : PML.ps_st ps0 <> PML.ST_ACCEPT).
    { intros X. destruct (REL2 (ACC X)) as (_ & MF & _). exact (stop_mod _ _ _ _ _ CUR MF ST1). }
    pose proof (ginv_g0 _ _ _ _ _ _ _ _ _ GI2) as ->.
    apply (RNS.s_done FPM fx3 R3 M2 model2 K sp C Hh2 Hl2 Hfp3 R3sp (conj S1 S2) ltac:(rewrite (KS3 9%bv ltac:(kin)); exact S9) ltac:(split; lia)
             ltac:(apply (L5.defined_sub _ _ _ _ _ DC2); unfold PMCS.CURSOR_SIZE; lia)).
    intros fx4 R4 M4 Hfp4 R4sp KS4 C640 AG4 MG4.
    assert (CF4 : rn_fr M4) by (apply (rn_fr_x M2 M4 (sp - 80)); [apply (TK.samem_weaken _ _ _ _ AG4); intros a Ha; lia | lia | exact CF2]).
    apply (RNS.s_epi FPM fx4 R4 M4 model2 K sp r R0 Hh2 Hl2 Hfp4 R4sp (conj S1 S2) CF4 Prok).
    intros fx5 R5 Hfp5 R5sp SAME KS5.
    apply (finish_done fx5 R5 M2 M4 model2 cr2 ps2 gp rdst bof g0 B Hfp5 GI2 AG4 MG4 C640); [|exact NA].
    apply (rp_back R4 R5); [| exact R5sp | exact SAME | exact KS5].
    intros q Hq. rewrite (KS4 q (KSM_KSP _ Hq)). exact (KC R3 _ KS3 QM q Hq).
  -
    intros Z0 MO GD fx3 R3 Hfp3 R3sp KS3. subst code2.
    rewrite b2z_land in MO. apply b2z_z in MO.
    apply (rn_exit fx3 R3 M2 model2 cr2 ps2 gp rdst 0 bof g2 B Hfp3 GI2 R3sp (KC R3 _ KS3 QM) CF2).
    split.
    + intros X _. destruct (REL2 (ACC X)) as (_ & _ & DN2). split; [reflexivity | exact DN2].
    + intros _ _. split; [exact MO|]. destruct CUR as (_ & CUR2). destruct (CUR2 eq_refl MO) as [(D1 & D2 & _)|(W2 & EVP)].
      * left. split; [exact D1 | exact D2].
      * right. split; [exact W2|]. exists (PML.ps_win ps). split; [|rewrite <- LV; exact EVP].
        unfold PML.win_ok in WOLD. destruct (PML.ps_win ps) as [[p e]|]; [|exact I]. destruct WOLD as (b & Hb & B1 & B2 & Bd). exists b. split; [exact Hb|]. split; [exact B1|]. split; [exact B2 | exact Bd].
  -
    intros Z0 MO GD fx3 R3 Hfp3 R3sp R3s5 R3s6 KS3. subst code2. pose proof (ginv_g0 _ _ _ _ _ _ _ _ _ GI2) as ->.
    rewrite b2z_land in MO. apply b2z_nz in MO.
    apply (IH fx3 R3 M2 model2 cr2 ps2 gp rdst bof B); try assumption.
    + assert (WEX2 : PMS.win_exhausted ps2) by (destruct REL1 as [X|[X|X]]; [exfalso; apply X; reflexivity | rewrite MO in X; discriminate X | exact X]).
      apply RB.exhausted_iff in WEX2. pose proof (rank_range ps) as RK. pose proof (rank_range ps2) as RK2. pose proof (ee_range rdst) as EE.
      unfold muA in *. unfold ww in *. rewrite WEX2, Z.eqb_refl. destruct (Z.eqb_spec (RB.wp ps) (RB.we ps)) as [WE|WN]; [|lia].
      destruct (REL3 ltac:(apply RB.exhausted_iff; exact WE) eq_refl MO) as [I1 I2]. rewrite (rank_in ps I1) in Hm. rewrite (rank_nin ps2 I2). lia.
    + intros X. destruct (REL2 (ACC X)) as (_ & MF & _). rewrite MO in MF. discriminate MF.
    + destruct CUR as (CUR1 & _). rewrite (CUR1 eq_refl MO). exact LV.
    + exact (rn_regs_keepQ R2x R3 CR2 KS3 R3sp R3s5 R3s6).
  -
    intros Z0 N0 _ _ _ fx3 R3 Hfp3 R3sp KS3. subst code2. pose proof (ginv_g0 _ _ _ _ _ _ _ _ _ GI2) as ->.
    exact (rn_tail fx3 R3 M2 model2 cr2 ps2 gp rdst bof B Hfp3 GI2 R3sp ltac:(rewrite (KS3 8%bv ltac:(kin)); exact S8) (KC R3 _ KS3 QM) CF2).
Qed.

Lemma loop_step : forall m, atA m -> atA (m + 1).
Proof.
  intros m IH fx R M model cr ps gp rdst bof B Hm Hfp GI MT ACC LV CR CF.
  pose proof (gcells _ _ _ _ _ _ _ _ _ _ GI) as (_ & _ & _ & _ & Hrd & _ & _ & Cwe & Cwp & Wr1 & Wr2 & _ & _ & _ & _ & _ & _ & Hgp).
  pose proof GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hh & Hl & _) & _ & _ & _ & BG & _).
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2]. destruct SPOK as [S1 S2].
  pose proof CR as (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & KR).
  pose proof (ee_range rdst) as EE. pose proof (ww_range ps) as WW. pose proof (rank_range ps) as RK.
  apply (RNS.s_loop FPM fx R M model K sp C (RB.wp ps) (RB.we ps) Hh Hl Hfp R2 (conj S1 S2) R9 ltac:(split; lia) Cwe Cwp ltac:(lia) ltac:(lia)).
  -
    intros EQ fx1 R1x Hfp1 R1sp R1ra R1a0 R1a1 KS1. rewrite R20 in R1a0. rewrite R8 in R1a1.
    assert (WEX : PMS.win_exhausted ps) by (apply RB.exhausted_iff; exact EQ).
    assert (CR1 : rn_regs R1x) by exact (rn_regs_keepL R R1x CR KS1 R1sp).
    apply (call_chunk fx1 R1x M model cr ps gp rdst bof B (sp - 80) RNT.R_CHUNK Hfp1 GI WEX R1ra ltac:(apply ra_lit; [unfold RNT.R_CHUNK; lia | reflexivity]) R1sp (rn_tp R1x CR1) R1a0 R1a1
             al80 ltac:(lia) ltac:(lia)).
    intros fx2 R2x M2 p k gp' rdst' code' bof' g' Hfp2 RP2 GI2 R2a0 R2a1 Hp Hpk Hk Hspan Hgp' Hkgp Heof Hrd' AG2.
    assert (CR2 : rn_regs R2x) by exact (rn_regs_rp R1x R2x CR1 RP2).
    pose proof (rn_fr_x M M2 (sp - 80) AG2 ltac:(lia) CF) as CF2.
    pose proof (gcells _ _ _ _ _ _ _ _ _ _ GI2) as (C248 & Cvt & _ & Crd8 & _ & RO2 & C296 & Cwe2 & Cwp2 & _ & _ & Cc & Rc & Dw & _ & _ & _ & Hgp2).
    pose proof CR2 as (T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & KR2).
    destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in A1, A2, A3. destruct OI as (I1 & I2 & I3).
    assert (PK : k <> 0 -> RNS.pok p).
    { intros NK. pose proof GI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HH2 & _).
      destruct (hfacts _ _ _ _ HH2) as (_ & _ & _ & _ & _ & HC1 & _ & _ & (HB1 & _)). destruct (Hspan ltac:(lia)) as [Sp1 Sp2]. split; lia. }
    apply (RNS.s_r_chunk FPM fx2 R2x M2 model K sp C E code' (RB.wp ps) (RB.we ps) 0 IS rdst' p k Hh Hl Hfp2 T2 (conj S1 S2) T9 T8 T20 ltac:(split; lia) ltac:(split; lia) R2a0 R2a1 Hp ltac:(lia) Hpk
             ltac:(lia) PK Cc Rc Cwe2 Cwp2 C296 C248 ltac:(split; lia) I3 Cvt Crd8 ltac:(destruct Hrd' as [-> | ->]; lia) RO2 ltac:(lia) ltac:(lia) ltac:(lia) Dw ltac:(lia) ltac:(lia)).
    + intros NZ fx3 R3 Hfp3 R3sp KS3.
      apply (rn_exit fx3 R3 M2 model cr ps gp' rdst' code' bof' g' B Hfp3 GI2 R3sp); [| exact CF2 | split; [intros _ X; contradiction | intros X; contradiction]].
      intros q Hq. rewrite (KS3 q (KSM_KSL _ Hq)). exact (KR2 q Hq).
    + intros Z0 fx3 R3 M3 pn en Hfp3 R3sp R3ra R3a0 R3a1 R3a2 EOFF KS3 HC. subst code'. pose proof (ginv_g0 _ _ _ _ _ _ _ _ _ GI2) as ->.
      rewrite T19 in R3a0. rewrite T18 in R3a1.
      assert (CR3 : rn_regs R3) by exact (rn_regs_keepL R2x R3 CR2 KS3 R3sp).
      assert (NTE : exists nte, getr R3 23%bv = Z_to_bv 64 nte /\ (nte = 0 \/ nte = 1)) by (destruct EOFF as [(X & _)|(X & _)]; [exists 0 | exists 1]; split; [exact X | lia | exact X | lia]).
      destruct NTE as (nte & R3s7 & Rnte).
      pose proof (ee_range rdst') as EE'.
      destruct HC as [(K0 & -> & -> & ->)|(K0 & -> & -> & C1 & C2 & AG3 & MG3)].
      * apply (psome_call m IH fx3 R3 M2 model cr ps gp' rdst' bof' B nte); try assumption.
        rewrite (Heof eq_refl K0). unfold muA in *. change (ee 2) with 0. lia.
      * assert (GI3 : ginv M3 model cr (PML.ps_set_win ps (Some (p, p + k))) gp' rdst' 0 bof' g0 (B + k)).
        { apply (ginv_setwin M2 M3 model cr ps gp' rdst' bof' g0 B p k GI2 WEX AG3 MG3 C1 C2); [lia | lia | lia | lia]. }
        assert (CF3 : rn_fr M3).
        { destruct CF2 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
          repeat split; (eapply (TK2.u64_x _ M2 M3 AG3); [lia | intros i Hi; lia | eassumption]). }
        apply (psome_call m IH fx3 R3 M3 model cr (PML.ps_set_win ps (Some (p, p + k))) gp' rdst' bof' (B + k) nte); try assumption;
          try (rewrite more_setwin; exact MT); try (rewrite st_setwin; exact ACC); try (rewrite level_setwin; exact LV).
        pose proof (ww_range (PML.ps_set_win ps (Some (p, p + k)))) as WW'. unfold muA in *. unfold rank in *. rewrite st_setwin. unfold ww in Hm. rewrite EQ, Z.eqb_refl in Hm. lia.
  -
    intros NE fx1 R1x Hfp1 R1sp R1ra R1a0 R1a1 R1a2 R1s7 KS1. rewrite R19 in R1a0. rewrite R18 in R1a1. rewrite R8 in R1a2.
    apply (psome_call m IH fx1 R1x M model cr ps gp rdst bof B 1); try assumption; try lia; try exact (rn_regs_keepL R R1x CR KS1 R1sp); try (right; reflexivity).
Qed.
Lemma loop_all : forall k : nat, atA (Z.of_nat k).
Proof.
  induction k as [|k IH].
  - intros fx R M model cr ps gp rdst bof B Hm Hfp GI. exfalso.
    pose proof (gcells _ _ _ _ _ _ _ _ _ _ GI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgp).
    pose proof (ee_range rdst). pose proof (ww_range ps). pose proof (rank_range ps). unfold muA in Hm. cbn in Hm. lia.
  - rewrite Nat2Z.inj_succ. unfold Z.succ. exact (loop_step _ IH).
Qed.

Lemma entry_ok : forall (fx : FPState) cr gp rdst bof,
  PML.fp_ok fx -> getr R0 1%bv = Z_to_bv 64 r -> getr R0 10%bv = Z_to_bv 64 C -> getr R0 11%bv = Z_to_bv 64 V -> getr R0 12%bv = Z_to_bv 64 E ->
  PMCS.cursor_at M0 C IS ch bof false ps0 -> PMCUR.wf_c (PMCUR.ps_set_more ps0 true) -> PML.win_ok M0 LBo ps0 -> PML.isrc_at M0 IS rep gp rdst ->
  PMCS.rn_bound (PMCUR.ps_set_more ps0 true) IS rep gp Bs -> PML.ec_at M0 E 0 -> PML.ls_ok g0 M0 ->
  hi_heap HI (PML.ps_blocks ps0 ++ LBo) cr M0 (m_vmmaps model0) -> PML.model_ok model0 -> PML.pcredit_x L cr ps0 kx bx -> L5.defined M0 (sp - SS) SS ->
  srealizes RSEGS SCFG (@PML.cfg fx R0 RNT.RN M0 model0) K.
Proof.
  intros fx cr gp rdst bof Hfp E1 A0 A1 A2 CUR WF WOK ISRC RNB EC LS HH MOK PC DS.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2].
  pose proof MOK as (Hh & Hl & _). pose proof Prok as [Pr1 Pr2].
  destruct OC as (O1 & O2 & O3).
  assert (DF : L5.defined M0 (sp - 80) 80) by (apply (L5.defined_sub _ _ _ _ _ DS); lia).
  assert (D531 : L5.defined M0 (C + 531) 1) by (apply (L5.defined_sub _ _ _ _ _ DC0); unfold PMCS.CURSOR_SIZE; lia).
  apply (RNS.s_rn_entry FPM fx R0 M0 model0 K sp C r Hh Hl Hfp R0sp SPOK A0 E1 ltac:(lia) ltac:(split; lia) DF D531 ltac:(lia)).
  intros fx1 R1 M1 Hfp1 R1sp R1s0 R1s1 R1s2 R1s3 R1s4 R1s5 R1s6 KS1 FR1 C531 AG1 MG1.
  destruct RNB as (RB1 & RB2 & RB3).
  set (B0 := Z.of_nat (length (PML.ps_buf (PMCUR.ps_set_more ps0 true))) + PML.winlen (PMCUR.ps_set_more ps0 true) + PML.buf_need (PMCUR.ps_set_more ps0 true)).
  assert (GI : ginv M1 model0 cr (PMCUR.ps_set_more ps0 true) gp rdst 0 bof g0 B0).
  { pose proof ISRC as (_ & _ & _ & _ & _ & _ & GR & _). cbv zeta in GR.
    unfold ginv. eapply RNI.ginv_entry; try eassumption.
    all: unfold PML.buf_bound; unfold B0; unfold PMCS.undelivered in RB1; split; lia. }
  assert (MT : PML.ps_more (PMCUR.ps_set_more ps0 true) = true) by (destruct ps0; reflexivity).
  assert (ACC : PML.ps_st ps0 = PML.ST_ACCEPT -> PML.ps_st (PMCUR.ps_set_more ps0 true) = PML.ST_ACCEPT) by (destruct ps0; intros X; exact X).
  assert (LV : PML.ps_level (PMCUR.ps_set_more ps0 true) = PML.ps_level ps0) by (destruct ps0; reflexivity).
  assert (CR1 : rn_regs R1).
  { split; [exact R1sp|]. split; [rewrite R1s0; exact A2|]. split; [exact R1s1|]. split; [rewrite R1s2; exact A1|]. split; [exact R1s3|]. split; [exact R1s4|].
    split; [exact R1s5|]. split; [exact R1s6|]. intros q Hq. exact (KS1 q (KSM_KSE _ Hq)). }
  apply (loop_all (Z.to_nat (muA (PMCUR.ps_set_more ps0 true) gp rdst + 1)) fx1 R1 M1 model0 cr (PMCUR.ps_set_more ps0 true) gp rdst bof B0); try assumption.
  pose proof (ee_range rdst). pose proof (ww_range (PMCUR.ps_set_more ps0 true)). pose proof (rank_range (PMCUR.ps_set_more ps0 true)).
  pose proof (gcells _ _ _ _ _ _ _ _ _ _ GI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgp).
  rewrite Z2Nat.id by (unfold muA; lia). lia.
Qed.
End Run.

Theorem read_next_ok : PMCS.read_next_spec L HI STRTOD_SCR.
Proof.
  unfold PMCS.read_next_spec. intros LBo cr sp r C IS E ch gp rdst B kx bx rep g bof ps. unfold PML.cps_heap.
  intros fx R M model K HH MOK HK0 Hfp PRE Hcont.
  destruct PRE as (ENT & A0 & A1 & A2 & CUR & WF & WOK & ISRC & RNB & EC & INch & INrep & HN & LS & GNE & PC & OC & OI & OE & AP1 & AP2 & AP3).
  destruct ENT as (E1 & E2 & E3 & E4 & STK). pose proof STK as (S1 & S2 & S3 & S4 & S5).
  assert (RSP : 9520 <= PMCS.RN_SCR STRTOD_SCR).
  { unfold PMCS.RN_SCR, PMS.READNEXT_SCR, PMS.PSOME_SCR, PMS.PF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK. pose proof (Z.le_max_l (16 + 8224) STRTOD_SCR). lia. }
  assert (SPOK : RNS.spok sp) by (split; [lia | exact S1]).
  pose proof CUR as (_ & _ & _ & _ & DC).
  pose proof RNB as (_ & HBs & _).
  change PMCS.PC_READ_NEXT_C with RNT.RN.
  eapply (entry_ok LBo sp r C IS E ch kx bx B rep g ps R M model K); try eassumption.
  - split; [exact AP1 | split; [exact AP2 | exact AP3]].
  - intros b Hb. exact (proj1 (INrep b Hb)).
  - intros b Hb. exact (proj2 (INrep b Hb)).
  - intros fx' R' M' model' cr' ps' code gp' rdst' g' bof' dn' Hfp' Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 RP HP BV HH'.
    apply (Hcont fx' R' M' model' (PML.ps_blocks ps' ++ LBo) cr' (lb_remove ch LBo) (RNI.Wr C IS E) Hfp'); try assumption.
    exists ps', code, gp', rdst', g', bof', dn'. repeat (split; [first [assumption | reflexivity]|]). exact Q10.
Qed.
End H.
End RNX.

