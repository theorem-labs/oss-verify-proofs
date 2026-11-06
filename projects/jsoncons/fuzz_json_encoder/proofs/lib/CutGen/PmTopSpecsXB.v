(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface L5Defs L5Core L5LazyA Pm5L5DefsA
  PmHeapIfaceA IcptIfaceA PmIcptIfaceA PmLibIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmLibSpecsXA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopSpecsXB HnKitXB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module TPSXA.
Section SpecsXA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.            (* [comment removed for export] *)
Variable EC : PMESA.econsts.          (* [comment removed for export] *)
(* [comment removed for export] *)
Variable enc_invA : PMSA.mem -> Z -> Z -> PMES.eghost -> Prop.
Variable VIS_SCRA : Z.
Variable VIS_D : Z.
Variable benc : PMES.eghost -> Z.
Variable eroomA : PMES.eghost -> PMES.eev -> Prop.

Abbreviation cps_asan := (PMSA.cps_asan L ar HI).
Abbreviation mem := PMSA.mem.   Abbreviation pstate := PML.pstate.
Abbreviation a0 := PMSA.a0.   Abbreviation a1 := PMSA.a1.   Abbreviation a2 := PMSA.a2.
Abbreviation fobj := PMSA.fobj.   Abbreviation stksh := (PMSA.stksh ar).   Abbreviation apart := PMLA.apart.
Abbreviation u8 := (PMSA.u8 L).   Abbreviation u64 := (PMSA.u64 L).
Abbreviation segs := (hl_segs L).
Abbreviation ENC_SIZE := PMES.ENC_SIZE.
Abbreviation kenc := (PMXA.kenc L).
Abbreviation lits_ok := (PMXA.lits_ok L IC).
Abbreviation W_encA := (PMXA.W_encA IC).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENC_CTOR_SCRXA : Z := 512 + PMSA.STR_SCR.          (* [comment removed for export] *)
Definition ENC_CTOR_DXA : Z := 2.                             (* [comment removed for export] *)
Definition enc_ctor_specXA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 SKT : Z),
    cps_asan pc r sp ENC_CTOR_SCRXA LB FF LK cr A ENC_CTOR_DXA
      (fun R M => a0 R V /\ a1 R SKT /\ sp mod 32 = 0 /\ stksh M sp ENC_CTOR_SCRXA /\
                  u64 M SKT S2 /\ L5.defined M SKT 8 /\ PMLA.rstk ar sp SKT 8 /\ SKT mod 8 = 0 /\
                  PMESA.sink_atA L M S2 (PML.SShort []) /\ L5.defined M V ENC_SIZE /\ PMESA.objs_encA M FF V S2 /\ PMLA.img_ro IC M /\ PMLA.libc_quiet segs IC M)
      (fun R M R' M' LB' cr' LBk W => enc_invA M' V S2 PMES.g0 /\ PMESA.opts_idle L M' V /\ u64 M' SKT 0 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(V, ENC_SIZE); (SKT, 8)]).
(* [comment removed for export] *)
Definition ENC_DTOR_SCRXA : Z := 96 + PMSA.ANEW_SCR.           (* [comment removed for export] *)
Definition enc_dtor_specXA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 : Z) (g : PMES.eghost),
    cps_asan pc r sp ENC_DTOR_SCRXA (LBo ++ PMES.g_lbv g) FF LK cr A 0
      (fun R M => a0 R V /\ stksh M sp ENC_DTOR_SCRXA /\ enc_invA M V S2 g /\ PMESA.opts_idle L M V /\ PMESA.objs_encA M FF V S2 /\ PMLA.img_ro IC M)
      (fun R M R' M' LB' cr' LBk W => PMESA.sink_atA L M' S2 (PMES.g_rep g) /\ L5.defined M' S2 24 /\
                                      LB' = LBo ++ PML.srep_blocks (PMES.g_rep g) /\ cr' = cr /\ LBk = LBo ++ PML.srep_blocks (PMES.g_rep g) /\ W = [(V, ENC_SIZE)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WRDX (Rr IS E V S2 : Z) : list L5.range := TPSA.WRD L IC Rr IS E ++ W_encA V S2.
Definition read_specXA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r Rr IS V E S2 ch gp sb bptr kx bx : Z) (rep : PML.srep) (g : PML.ls_state) (eg : PMES.eghost),
    let ps := PMSA.ps_init sb bptr in
    cps_asan pc r sp (PMXA.READXA_SCR VIS_SCRA) (PML.ps_blocks ps ++ LBo ++ PMES.g_lbv eg) FF LK cr A (PMXA.DPSOMEXA VIS_D)                            (* [comment removed for export] *)
      (fun R M => a0 R Rr /\ a1 R E /\ stksh M sp (PMXA.READXA_SCR VIS_SCRA) /\
                  PMSA.reader_preA L IC M LBo FF Rr IS V E ch rep gp 0 true ps /\ gp = PML.srep_data (IS + 80) rep /\
                  (forall b, In b (PML.srep_blocks rep) -> fst b <> ch) /\
                  Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\ PMLA.ls_ok segs IC g M /\ g <> PML.LS0 /\
                  enc_invA M V S2 eg /\ lits_ok M /\ PMXA.enc_sync ps eg /\                                                                         (* [comment removed for export] *)
                  0 <= kx /\ 0 <= bx /\ PMLA.pcredit_xA L cr ps (kx + kenc eg) (bx + benc eg) /\                                                  (* [comment removed for export] *)
                  sp mod 32 = 0 /\
                  fobj M FF V ENC_SIZE /\ fobj M FF S2 24 /\ apart V ENC_SIZE S2 24 /\                                                              (* [comment removed for export] *)
                  apart Rr 592 V ENC_SIZE /\ apart Rr 592 S2 24 /\ apart IS 272 V ENC_SIZE /\ apart IS 272 S2 24 /\ apart V ENC_SIZE E 16 /\ apart S2 24 E 16)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : pstate) (code gp' rdst' : Z) (g' : PML.ls_state) (eg' : PMES.eghost),
          PMLA.source_at segs IC M' Rr ch /\ PMLA.parser_at segs IC M' (Rr + 320) ps' /\ PMLA.parser_sh M' ps' /\ PMLA.isrc_at segs IC M' IS rep gp' rdst' /\
          PMLA.ec_at segs IC M' E code /\ PMLA.ls_ok segs IC g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          enc_invA M' V S2 eg' /\ lits_ok M' /\                                                                                                  (* [comment removed for export] *)
          LB' = PML.ps_blocks ps' ++ LBo ++ PMES.g_lbv eg' /\ LBk = lb_remove ch LBo /\                                                          (* [comment removed for export] *)
          PMLA.pcredit_xA L cr' ps' (kx + kenc eg') (bx + benc eg') /\ PML.wf_ps ps' /\                                                          (* [comment removed for export] *)
          W = WRDX Rr IS E V S2).                                                                                                                (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HARN_SCRXA : Z := 18432.                           (* [comment removed for export] *)
Definition LIB_FRAMESXA : Z := 12.                            (* [comment removed for export] *)
Definition EMPTY_X : Z := HNK.EMPTY_A11.                      (* [comment removed for export] *)
Definition pm_creditxA (n : Z) : credit :=
  (28 * hl_k_per_malloc L + kenc PMES.g0, hl_b_lin L * (2 * n + 2 ^ 28 + 32768) + 28 * hl_b_overhead L + benc PMES.g0).
Definition foot_rangesX : list L5.range := PMSA.foot_ranges IC ++ [(PMLA.LIT_LO IC, PMLA.LIT_HI IC - PMLA.LIT_LO IC)].
Definition harness_preX (LB : list (Z * Z)) (cr : credit) (sp ptr : Z) (txt : list Z) (g : PML.ls_state) (R : bvmap 5 word) (M : mem) : Prop :=
  let n := Z.of_nat (length txt) in
  a0 R ptr /\ a1 R n /\ n < 2 ^ 26 /\ sp mod 16 = 0 /\ stksh M sp HARN_SCRXA /\
  ((txt = [] /\ ptr = EMPTY_X) \/ (0 < n /\ In (ptr, n) LB)) /\ L5.bytes_at segs M ptr txt /\ L5.defined M ptr n /\ (0 < n -> shadow_blk M ptr n) /\
  PMLA.ls_okx segs IC g M /\
  fst (pm_creditxA n) <= fst cr /\ snd (pm_creditxA n) <= snd cr.
Definition harness_postX (LB : list (Z * Z)) (cr : credit) (txt : list Z)
           (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  let n := Z.of_nat (length txt) in
  exists g' : PML.ls_state,
    a0 R' 0 /\ PMLA.ls_okx segs IC g' M' /\ (g' = PML.LS1 \/ g' = PML.LS2) /\ LB' = LB /\ LBk = LB /\
    fst cr - fst (pm_creditxA n) <= fst cr' /\ snd cr - snd (pm_creditxA n) <= snd cr' /\
    W = foot_rangesX ++ [(hl_tp L - 164, 4)].
(* [comment removed for export] *)
Definition harness_chainXA (pc aln : Z) (lng : bool) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r ptr : Z) (txt : list Z) (g : PML.ls_state),
    sp mod 32 = aln -> HNK.len_class lng txt ->
    cps_asan pc r sp HARN_SCRXA LB FF LK cr A LIB_FRAMESXA (harness_preX LB cr sp ptr txt g) (harness_postX LB cr txt).
(* [comment removed for export] *)
Definition harness_specXA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r ptr : Z) (txt : list Z) (g : PML.ls_state),
    cps_asan pc r sp HARN_SCRXA LB FF LK cr A LIB_FRAMESXA (harness_preX LB cr sp ptr txt g) (harness_postX LB cr txt).
(* [comment removed for export] *)
Definition scr_okP : Prop := 176 + PMXA.READXA_SCR VIS_SCRA <= HARN_SCRXA /\ 176 + ENC_CTOR_SCRXA <= HARN_SCRXA /\ 0 <= VIS_SCRA.
Definition frames_okP : Prop := 1 + PMXA.DPSOMEXA VIS_D <= LIB_FRAMESXA /\ 0 <= VIS_D.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIB_SCRXA : Z := 176 + Z.max (PMXA.READXA_SCR VIS_SCRA) (Z.max PMSA.RCTOR_SCR (Z.max PMSA.ISS_SCR ENC_CTOR_SCRXA)).
Definition pm_staticsxA : lib_statics := {| LibIface.ls_state := PML.ls_state; LibIface.ls_ok := PMLA.ls_okx segs IC; LibIface.ls_g0 := PML.LS0 |}.
Definition pm_layout_okxA (Lay : lib_layoutA) : Prop :=
  lla_L Lay = L /\ LIB_SCRXA <= lla_stack Lay /\ lla_stack Lay mod 16 = 0 /\ lla_foot Lay = PMLA.FOOTX IC /\
  lla_junk Lay = [(hl_tp L - 164, hl_tp L - 160)] /\
  (forall k, In k PM_FS_CLASSES -> lla_frames Lay k = LIB_FRAMESXA /\ lla_leak Lay k = 0) /\
  (forall n, lla_credit Lay n = pm_creditxA n) /\ PMLA.IMG_RO_HI IC <= lla_rw_lo Lay /\
  lla_atexit Lay = PMLA.ATEXIT_TAB IC /\ lla_hs0 Lay = PMLA.HS0 IC /\ lla_need_locks Lay = PMLA.NEED_LOCKS IC /\
  (forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ (PMLA.in_footx IC a /\ ~ PMLA.in_tab IC a /\ a <> PMLA.NEED_LOCKS IC) ->
             exists iv, In iv (lla_init_img Lay) /\ fst iv <= a < snd iv) /\
  (forall M : mem, (forall a, PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 -> M (Z_to_bv 64 a) = None) -> cell_is segs M (PMLA.LOCALE_LOCK IC) 4 0).
Definition lib_specxA (Lay : lib_layoutA) : Prop := pm_layout_okxA Lay -> PmLibIfaceA.lib_call_okA Lay ar SCFG HI pm_staticsxA.

(* [comment removed for export] *)
Lemma lib_exit_okxA : forall (Lay : lib_layoutA), pm_layout_okxA Lay -> PmLibIfaceA.lib_exit_factsA Lay pm_staticsxA (PMLA.ls_atexit IC).
Proof.
  intros Lay (HL & _ & _ & _ & _ & _ & _ & _ & HA & HH & HN & _) g M [Hok _]. rewrite HA, HH, HN, HL. exact (PMLA.ls_ok_exit segs IC g M Hok).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma enc_sync_init : forall sb bptr eg, PMES.depth (PMES.g_es eg) = 0 -> PMXA.enc_sync (PMSA.ps_init sb bptr) eg.
Proof.
  intros sb bptr eg H. split; [exact H|]. intros _ [K|(x & Hin & K)]; exfalso.
  - unfold PMXA.KEY_STATES in K. cbn in K. destruct K as [K|[K|[K|[]]]]; discriminate K.
  - cbn in Hin. destruct Hin as [<-|[]]. unfold PMXA.KEY_STATES in K. cbn in K. destruct K as [K|[K|[K|[K|[]]]]]; discriminate K.
Qed.
Lemma kenc_g0 : kenc PMES.g0 = 54 * hl_k_per_malloc L.
Proof. reflexivity. Qed.
Lemma pm_creditxA_fst : forall n, fst (pm_creditxA n) = 82 * hl_k_per_malloc L.
Proof. intros n. unfold pm_creditxA. cbn [fst]. rewrite kenc_g0. lia. Qed.
End SpecsXA.
End TPSXA.
