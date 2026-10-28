(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3Sound HeapIface LibIface L5Defs L5Core.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmCurSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutLib.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ReadBase_u RnStretch_u.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RNI.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Lemma al16 : forall sp k, sp mod 16 = 0 -> k mod 16 = 0 -> (sp - k) mod 16 = 0.
Proof. intros sp k H1 H2. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; apply Z.mod_divide; try lia; assumption. Qed.
Lemma not_outside : forall F a, ~ L5.outside F a -> exists w, In w F /\ L5.in_rng w a.
Proof.
  induction F as [|w F IH]; intros a H; [exfalso; apply H; intros w []|].
  destruct (classic (L5.in_rng w a)) as [Y|N]; [exists w; split; [left; reflexivity | exact Y]|].
  destruct (IH a) as (w' & Hw' & Hin); [|exists w'; split; [right; exact Hw' | exact Hin]].
  intros Ho. apply H. intros w0 [<-|Hw0]; [exact N | exact (Ho w0 Hw0)].
Qed.
Lemma in_lb_remove : forall A (LB : list (Z * Z)) b, In b LB -> fst b <> A -> In b (lb_remove A LB).
Proof.
  intros A LB b. induction LB as [|c LB IH]; intros Hin Hne; [destruct Hin|]. cbn [lb_remove].
  destruct (Z.eqb_spec (fst c) A) as [Heq|Hn]; [destruct Hin as [<-|Hin]; [contradiction | exact Hin] | destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH Hin Hne)]].
Qed.
Lemma lb_remove_in : forall A (LB : list (Z * Z)) b, In b (lb_remove A LB) -> In b LB.
Proof.
  intros A LB b. induction LB as [|c LB IH]; intros Hin; [destruct Hin|]. cbn [lb_remove] in Hin.
  destruct (Z.eqb (fst c) A); [right; exact Hin | destruct Hin as [<-|Hin]; [left; reflexivity | right; exact (IH Hin)]].
Qed.
Lemma lb_remove_fst : forall A (LB : list (Z * Z)) b, NoDup (map fst LB) -> In b (lb_remove A LB) -> fst b <> A.
Proof.
  intros A LB b. induction LB as [|c LB IH]; intros ND Hin; [destruct Hin|]. cbn [lb_remove] in Hin. cbn [map] in ND. inversion ND as [|x l N1 N2]; subst.
  destruct (Z.eqb_spec (fst c) A) as [Heq|Hn].
  - intros X. apply N1. apply stdpp.base.list_elem_of_In. rewrite Heq, <- X. apply in_map. exact Hin.
  - destruct Hin as [<-|Hin]; [exact Hn | exact (IH N2 Hin)].
Qed.
Lemma wf_setwin : forall ps w, PMCUR.wf_c ps -> PMCUR.wf_c (PML.ps_set_win ps w).
Proof. intros [] w H. exact H. Qed.

Section Xfer.
Variable K : Z -> Prop.
Variables M M' : mem.
Hypothesis AG : TK.samem K M M'.
Lemma rdc_at_x : forall S IS ch bof, 0 <= S < 2 ^ 59 -> TK2.cov K S 304 -> PMCS.rdc_at M S IS ch bof -> PMCS.rdc_at M' S IS ch bof.
Proof.
  intros S IS ch bof HS HK ((A240 & A248 & A264 & A272 & (de & A280 & Hde) & A288 & A296 & (st0 & Aio) & A32) & Adef). unfold PMCS.rdc_at, PMCS.src_at.
  split; [|apply (TK.defined_samem K M M' _ _ AG); [lia | lia | exact HK | exact Adef]].
  repeat (split; [apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption]|]).
  split; [exists de; split; [apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption] | exact Hde]|].
  split; [apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption]|].
  split; [apply (TK2.u8_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | assumption]|].
  split; [exists st0; apply (TK2.iosb_at_x K M M' AG); [lia | eapply TK2.cov_sub; [exact HK | lia | lia] | exact Aio]|].
  apply (TK2.u64_x K M M' AG); [lia | (eapply TK2.cov_sub; [exact HK | lia | lia]) | assumption].
Qed.
End Xfer.

Lemma parser_at_setmore : forall (K : Z -> Prop) (M M' : mem) P ps,
  PML.parser_at M P ps -> TK.samem K M M' -> mem_grows M M' -> 0 <= P < 2 ^ 60 -> TK2.cov K P 211 -> TK2.cov K (P + 212) 60 -> TK2.ps_cov K ps ->
  PML.u8 M' (P + 211) 1 ->
  PML.parser_at M' P (PMCUR.ps_set_more ps true).
Proof.
  intros K M M' P ps H AG MG HP K1 K2 (B1 & B2 & B3 & S1 & S2 & S3) HM. unfold PML.parser_at in *.
  destruct H as (A0 & A8 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A24 & A48 & A72 & A96 & A128 & A144 & Aw & A208 & A209 & A210 & A211 & A212 & A213 & A216 & Abuf & Abc & A248 & A256 & A264 & Astk & Asl & Adef).
  assert (C0 : forall a n, (P <= a /\ a + n <= P + 211) \/ (P + 212 <= a /\ a + n <= P + 272) -> TK2.cov K a n).
  { intros a n [[X1 X2]|[X1 X2]] i Hi; [apply K1; lia | apply K2; lia]. }
  destruct ps as [st sst nst more done level stack sb scap bcap bptr buf win].
  cbn [PMCUR.ps_set_more PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win] in *.
  repeat (split; [first [apply (TK2.u64_x K M M' AG); [lia | apply C0; lia | assumption] | apply (TK2.u32_x K M M' AG); [lia | apply C0; lia | assumption] | apply (TK2.u8_x K M M' AG); [lia | apply C0; lia | assumption]
                        | apply (TK2.lstr_short_x K M M' AG); [lia | apply C0; lia | assumption] ]|]).
  split; [destruct win as [[p e]|]; [destruct Aw as (W1 & W2 & W3); split; [|split; [|exact W3]] | destruct Aw as (W1 & W2); split];
          (apply (TK2.u64_x K M M' AG); [lia | apply C0; lia | assumption])|].
  repeat (split; [first [apply (TK2.u8_x K M M' AG); [lia | apply C0; lia | assumption]]|]).
  split; [exact HM|].
  repeat (split; [first [apply (TK2.u64_x K M M' AG); [lia | apply C0; lia | assumption] | apply (TK2.u32_x K M M' AG); [lia | apply C0; lia | assumption] | apply (TK2.u8_x K M M' AG); [lia | apply C0; lia | assumption]]|]).
  split; [apply (TK2.str_at_x K M M' AG); [lia | split; [apply C0; lia | split; [lia | split; [lia | exact B3]]] | exact Abuf]|].
  split; [exact Abc|].
  repeat (split; [apply (TK2.u64_x K M M' AG); [lia | apply C0; lia | assumption]|]).
  split; [apply (TK.bytes_samem K M M' _ _ AG); [lia | lia | intros i Hi; apply S3; lia | exact Astk]|].
  split; [exact Asl|]. exact (L5.defined_grows M M' _ _ MG Adef).
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

Section Run.
Variables (LBo : list (Z * Z)) (sp r C IS E ch kx bx Bs : Z) (rep : PML.srep) (g0 : PML.ls_state) (M0 : mem) (model0 : Model).
Let SS := PMCS.RN_SCR STRTOD_SCR.
Let n := Z.of_nat (length (PML.srep_chars rep)).
Let D := PML.srep_data (IS + 80) rep.
Let P := C + 320.
Let V := C + 592.
Let S := C + 8.
Definition Wr : list L5.range := [(C, PMCS.CURSOR_SIZE); (IS, 272); (E, 16); (0xd4df8, 2); (0xf6848, 544)].
Let LBk := lb_remove ch LBo.
Hypothesis Hn : n < 2 ^ 26.
Hypothesis HBs : Bs < 2 ^ 26.
Hypothesis G0 : g0 <> PML.LS0.
Hypothesis SPOK : RNS.spok sp.
Hypothesis Hceil : hl_ceil L + SS <= sp.
Hypothesis Hsptop : sp <= hl_sptop L.
Hypothesis Htop : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis OC : PML.obj_on_stack L sp C PMCS.CURSOR_SIZE.
Hypothesis OI : PML.obj_on_stack L sp IS 272.
Hypothesis OE : PML.obj_on_stack L sp E 16.
Hypothesis AP : PML.apart C PMCS.CURSOR_SIZE IS 272 /\ PML.apart C PMCS.CURSOR_SIZE E 16 /\ PML.apart IS 272 E 16.
Hypothesis INch : In (ch, 16384) LBo.
Hypothesis INrep : forall b, In b (PML.srep_blocks rep) -> In b LBo.
Hypothesis NEch : forall b, In b (PML.srep_blocks rep) -> fst b <> ch.

Definition foot (a : Z) : Prop := ~ L5.outside Wr a.

Definition ginv (M : mem) (model : Model) (cr : credit) (ps : PML.pstate) (gp rdst code : Z) (bof : bool) (g : PML.ls_state) (B : Z) : Prop :=
  PMCS.rdc_at M S IS ch bof /\ PML.parser_at M P ps /\ PMCUR.wf_c ps /\ PML.win_ok M LBo ps /\ PML.isrc_at M IS rep gp rdst /\ PML.vis_at M V /\ PML.ec_at M E code /\
  PML.ls_ok g M /\ (g = g0 \/ (g = PML.regJ g0 /\ code <> 0)) /\
  hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model) /\ PML.model_ok model /\ model_but_vm model0 model /\
  PML.pcredit_x L cr ps kx bx /\ PML.buf_bound ps B /\ B + (D + n - gp) <= Bs /\
  TK2.FR L LBk sp SS foot M0 M /\ (forall a, 0 <= a < 2 ^ 64 -> foot a -> M0 (Z_to_bv 64 a) <> None -> M (Z_to_bv 64 a) <> None) /\
  PML.u8 M (C + 640) 0.

Lemma lay : 2 ^ 40 <= sp /\ sp mod 16 = 0 /\ sp <= C /\ C + 656 <= hl_sptop L /\ sp <= IS /\ IS + 272 <= hl_sptop L /\ sp <= V /\ V + 48 <= hl_sptop L /\ sp <= E /\ E + 16 <= hl_sptop L /\
            0xf8000 <= hl_ceil L /\ hl_ceil L + SS <= sp /\ SS = 144 + PMS.PSOME_SCR STRTOD_SCR /\ 9376 <= PMS.PSOME_SCR STRTOD_SCR /\ PMS.PSOME_SCR STRTOD_SCR = 128 + PMS.PF_SCR STRTOD_SCR.
Proof.
  destruct SPOK as [S1 S2]. destruct OC as (A1 & A2 & _). destruct OI as (B1 & B2 & _). destruct OE as (D1 & D2 & _). unfold PMCS.CURSOR_SIZE in *.
  unfold hl_ceil in *. unfold SS, V, PMCS.RN_SCR, PMS.READNEXT_SCR, PMS.PSOME_SCR, PMS.PF_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  pose proof (Z.le_max_l (16 + 8224) STRTOD_SCR) as MX. set (mx := Z.max (16 + 8224) STRTOD_SCR) in *. clearbody mx. repeat split; lia.
Qed.

Lemma blk : forall M model cr ps, hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model) ->
  TK2.blocks_ok L (PML.ps_blocks ps ++ LBo) /\ (forall b, In b (PML.ps_blocks ps ++ LBo) -> 0 <= fst b /\ fst b + snd b <= hl_ceil L /\ 0 < snd b /\ (fst b + snd b <= 0x10000 \/ 0xf8000 <= fst b)).
Proof.
  intros M model cr ps HH. pose proof (TK2.blocks_ok_heap L HI HIok _ _ _ _ HH) as BOK. split; [exact BOK|].
  intros b Hb. destruct (BOK b Hb) as (B0 & B1 & B2 & B3 & B4). rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1. lia.
Qed.

Lemma ginv_stack : forall M M' model cr ps gp rdst code bof g B lo hi,
  ginv M model cr ps gp rdst code bof g B -> TK.samem (fun a => ~ (lo <= a < hi)) M M' -> mem_grows M M' -> sp - SS <= lo -> hi <= sp ->
  ginv M' model cr ps gp rdst code bof g B.
Proof.
  intros M M' model cr ps gp rdst code bof g B lo hi (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN) AG MG Hlo Hhi.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2].
  destruct (blk _ _ _ _ HH) as [BOK BF].
  assert (CB : forall b, In b (PML.ps_blocks ps ++ LBo) -> TK2.cov (fun a => ~ (lo <= a < hi)) (fst b) (snd b)) by (intros b Hb i Hi; destruct (BF b Hb); lia).
  assert (INo : forall b, In b LBo -> In b (PML.ps_blocks ps ++ LBo)) by (intros b Hb; apply in_or_app; right; exact Hb).
  unfold ginv. split; [apply (rdc_at_x _ M M' AG); [unfold S; lia | intros i Hi; unfold S in Hi; lia | exact RDR]|].
  split; [apply (TK2.parser_at_x _ M M' AG); [unfold P; lia | intros i Hi; unfold P in Hi; lia | | exact PAR]|].
  { pose proof (BF _ (or_introl eq_refl)) as X1. pose proof (BF _ (or_intror (or_introl eq_refl))) as X2. cbn [fst snd] in X1, X2. unfold hl_ceil in *.
    split; [lia|]. split; [lia|]. split; [exact (CB _ (or_introl eq_refl))|]. split; [lia|]. split; [lia|]. exact (CB _ (or_intror (or_introl eq_refl))). }
  split; [exact WF|].
  split; [apply (RB.win_ok_x _ M M' AG); [|exact WOK]; intros b Hb; destruct (BF b (INo b Hb)); unfold hl_ceil in *; split; [lia|]; split; [lia | exact (CB b (INo b Hb))]|].
  split; [apply (TK2.isrc_at_x _ M M' AG); [lia | intros i Hi; lia | | exact ISRC]|].
  { split; [intros i Hi; lia|]. destruct rep as [s|cap p s]; [exact I|]. pose proof (INo _ (INrep _ (or_introl eq_refl))) as Hb. pose proof (BF _ Hb) as X. cbn [fst snd] in X. unfold hl_ceil in *.
    split; [lia|]. split; [lia|]. exact (CB _ Hb). }
  split; [apply (TK2.vis_at_x _ M M' AG); [unfold V; lia | intros i Hi; unfold V in *; lia | exact VIS]|].
  split; [apply (TK2.ec_at_x _ M M' AG); [lia | intros i Hi; lia | exact EC]|].
  split; [apply (TK2.ls_ok_x _ M M' AG); [|exact LS]|].
  { apply TK2.statics_cov_lo; intros a Ha; lia. }
  split; [exact GG|].
  split; [apply (TK2.heap_stack_write L HI HIok LAY _ _ M M' _ lo hi HH); [lia | lia | lia | exact AG | exact MG]|].
  split; [exact MOK|]. split; [exact BV|]. split; [exact PC|]. split; [exact BB|]. split; [exact BG|].
  split; [|split].
  - apply (TK2.FR_samem L _ _ _ _ M0 M M' _ FR AG); [|intros a Ha Hd; apply MG; exact Hd].
    intros a Ha HC HF HE. assert (BOKk : TK2.blocks_ok L LBk) by (intros b Hb; apply BOK; apply INo; exact (lb_remove_in _ _ _ Hb)).
    pose proof (TK2.client_not_window L LAY LBk sp SS a HC BOKk ltac:(lia) ltac:(lia)) as NW. lia.
  - intros a Ha Hf Hd. apply MG. exact (DW a Ha Hf Hd).
  - apply (TK2.u8_x _ M M' AG); [lia | intros i Hi; lia | exact DN].
Qed.

Lemma foot_cases : forall a, foot a -> (C <= a < C + 656) \/ (IS <= a < IS + 272) \/ (E <= a < E + 16) \/ (0xd4df8 <= a < 0xd4dfa) \/ (0xf6848 <= a < 0xf6a68).
Proof.
  intros a Hf. clear - Hf. destruct (not_outside _ _ Hf) as (w & Hw & Hin). unfold Wr, PMCS.CURSOR_SIZE in Hw. unfold L5.in_rng in Hin.
  repeat (destruct Hw as [<-|Hw]; [cbn [fst snd] in Hin; lia|]). destruct Hw.
Qed.
Lemma in_foot : forall a, (C <= a < C + 656) \/ (IS <= a < IS + 272) \/ (E <= a < E + 16) \/ (0xd4df8 <= a < 0xd4dfa) \/ (0xf6848 <= a < 0xf6a68) -> foot a.
Proof.
  intros a Ha HO. clear - Ha HO. unfold Wr, PMCS.CURSOR_SIZE in HO. destruct Ha as [X|[X|[X|[X|X]]]].
  - apply (HO (C, 656) (or_introl eq_refl)). unfold L5.in_rng. cbn [fst snd]. lia.
  - apply (HO (IS, 272) (or_intror (or_introl eq_refl))). unfold L5.in_rng. cbn [fst snd]. lia.
  - apply (HO (E, 16) (or_intror (or_intror (or_introl eq_refl)))). unfold L5.in_rng. cbn [fst snd]. lia.
  - apply (HO (0xd4df8, 2) (or_intror (or_intror (or_intror (or_introl eq_refl))))). unfold L5.in_rng. cbn [fst snd]. lia.
  - apply (HO (0xf6848, 544) (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))). unfold L5.in_rng. cbn [fst snd]. lia.
Qed.
Lemma wparc_foot : forall w a, In w (PMS.W_parc P V E) -> L5.in_rng w a -> foot a.
Proof.
  intros w a Hw Hin. apply in_foot. unfold PMS.W_parc, PML.W_par in Hw. unfold L5.in_rng in Hin. unfold P, V in *.
  destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hin; lia.
Qed.
Lemma mk_stk : forall M spc scr, (forall a, sp - SS <= a < sp -> M (Z_to_bv 64 a) <> None) -> spc mod 16 = 0 -> sp - SS <= spc - scr -> spc <= sp -> 0 <= scr -> L5C.stk (hl_sptop L) M spc scr.
Proof.
  intros M spc scr F2 Hal H1 H2 H3. pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2]. unfold hl_ceil in *.
  split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [exact Htop|]. intros i Hi. apply F2. lia.
Qed.
Lemma mok_bv : forall model model', PML.model_ok model -> model_but_vm model model' -> PML.model_ok model'.
Proof.
  intros model model' (Hh & Hl & Hm) BV. split; [rewrite (L5C.halted_but_vm _ _ BV); exact Hh | split; [rewrite (L5C.lazy_but_vm _ _ BV); exact Hl | rewrite (L5C.materialized_but_vm _ _ BV); exact Hm]].
Qed.

Lemma ginv_ptrans : forall M M' model model' cr cr' ps ps' gp rdst bof code' g' B spc scr,
  ginv M model cr ps gp rdst 0 bof g0 B ->
  L5C.hpres L LBo spc scr (PMS.W_parc P V E) M M' -> sp - SS <= spc - scr -> spc <= sp -> 0 <= scr -> spc mod 16 = 0 ->
  model_but_vm model model' -> hi_heap HI (PML.ps_blocks ps' ++ LBo) cr' M' (m_vmmaps model') ->
  PML.parser_at M' P ps' -> PMCUR.wf_c ps' -> PML.win_ok M' LBo ps' -> PML.buf_bound ps' B -> PML.ec_at M' E code' -> PML.ls_ok g' M' ->
  (g' = g0 \/ (g' = PML.regJ g0 /\ code' <> 0)) -> PML.pcredit_x L cr' ps' kx bx ->
  ginv M' model' cr' ps' gp rdst code' bof g' B.
Proof.
  intros M M' model model' cr cr' ps ps' gp rdst bof code' g' B spc scr (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN) HP Hlo Hhi Hscr Hal BV' HH' PAR' WF' WOK' BB' EC' LS' GG' PC'.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2]. destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in *.
  destruct (blk _ _ _ _ HH) as [BOK BF].
  assert (INo : forall b, In b LBo -> In b (PML.ps_blocks ps ++ LBo)) by (intros b Hb; apply in_or_app; right; exact Hb).
  assert (BOKo : TK2.blocks_ok L LBo) by (intros b Hb; apply BOK; apply INo; exact Hb).
  pose proof (TK2.hpres_samem L LAY LBo spc scr _ M M' HP BOKo (mk_stk M spc scr (proj2 FR) Hal Hlo Hhi Hscr) Hscr) as AG.
  assert (WSI : TK2.w_si L (PMS.W_parc P V E)) by (intros w Hw; unfold PMS.W_parc, PML.W_par in Hw; repeat (destruct Hw as [<-|Hw]; [cbn [fst snd]; unfold P, V; lia|]); destruct Hw).
  assert (OUT : forall a, (C <= a < C + 320 \/ C + 592 <= a < C + 600 \/ C + 640 <= a < C + 656 \/ IS <= a < IS + 272) -> TK2.keepH L LBo (PMS.W_parc P V E) spc scr a).
  { intros a Ha. split; [|left; lia]. intros w Hw Hin. unfold PMS.W_parc, PML.W_par in Hw. unfold L5.in_rng in Hin. repeat (destruct Hw as [<-|Hw]; [cbn [fst snd] in Hin; unfold P, V in Hin; lia|]). destruct Hw. }
  assert (DEF' : forall a, 0 <= a < 2 ^ 64 -> sp <= a < hl_sptop L -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None).
  { intros a Ha Hs Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha); [right; left; unfold hl_ceil in *; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); unfold hl_ceil in *; lia | exact Hd]. }
  unfold ginv. split; [apply (rdc_at_x _ M M' AG); [unfold S; lia | intros i Hi; apply OUT; unfold S in Hi; lia | exact RDR]|].
  split; [exact PAR'|]. split; [exact WF'|]. split; [exact WOK'|].
  split; [apply (TK2.isrc_at_x _ M M' AG); [lia | intros i Hi; apply OUT; lia | | exact ISRC]|].
  { apply (TK2.str_cov_keepH L LAY); [lia | intros i Hi; apply OUT; lia | exact WSI | intros b Hb; split; [exact (INrep b Hb) | exact (BOKo b (INrep b Hb))]]. }
  split.
  { destruct VIS as (VP & VD). split; [apply (TK2.u64_x _ M M' AG); [unfold V; lia | intros i Hi; apply OUT; unfold V in Hi; lia | exact VP]|].
    intros i Hi. apply DEF'; [unfold V in *; lia | unfold V in *; lia | exact (VD i Hi)]. }
  split; [exact EC'|]. split; [exact LS'|]. split; [exact GG'|]. split; [exact HH'|].
  split; [exact (mok_bv _ _ MOK BV')|]. split; [exact (L5C.model_but_vm_trans _ _ _ BV BV')|]. split; [exact PC'|]. split; [exact BB'|]. split; [exact BG|].
  assert (BOKk : TK2.blocks_ok L LBk) by (intros b Hb; apply BOKo; exact (lb_remove_in _ _ _ Hb)).
  split; [|split].
  - apply (TK2.FR_hpres L LAY LBk sp SS foot M0 M M' LBo spc scr _ FR HP BOKk); [intros b Hb; exact (lb_remove_in _ _ _ Hb) | lia | lia | lia | lia | lia | lia |].
    intros w a Hw Hin. right. exact (wparc_foot w a Hw Hin).
  - intros a Ha Hf Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP Ha); [| | exact (DW a Ha Hf Hd)].
    + pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. unfold hl_ceil in *.
      destruct (foot_cases a Hf) as [X|[X|[X|[X|X]]]]; [right; left; lia | right; left; lia | right; left; lia | right; right | right; right];
        (split; [rewrite ILO, IHI; lia | intros Z0; apply (PmLayout.ly_static L LAY) in Z0; lia]).
    + unfold in_errno. rewrite (PmLayout.ly_errno L LAY). unfold hl_ceil in *. destruct (foot_cases a Hf) as [X|[X|[X|[X|X]]]]; lia.
  - apply (TK2.u8_x _ M M' AG); [lia | intros i Hi; apply OUT; lia | exact DN].
Qed.

Definition Wc : list L5.range := [(S, 304); (IS, 272); (E, 16); (ch, 16384); (0xd4df8, 2); (0xf6848, 544)].
Lemma hfacts : forall M model cr ps, hi_heap HI (PML.ps_blocks ps ++ LBo) cr M (m_vmmaps model) ->
  (forall b, In b (PML.ps_blocks ps ++ LBo) -> fst b <> ch -> PML.apart (fst b) (snd b) ch 16384) /\
  PML.ps_bptr ps <> ch /\ PML.ps_sb ps <> ch /\ (forall b, In b LBk -> PML.apart (fst b) (snd b) ch 16384) /\
  0 <= ch /\ ch + 16384 <= hl_ceil L /\ (ch + 16384 <= 0x10000 \/ 0xf8000 <= ch) /\ L5.defined M ch 16384 /\ block_range L ch 16384.
Proof.
  intros M model cr ps HH. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & ND & _).
  assert (INc : In (ch, 16384) (PML.ps_blocks ps ++ LBo)) by (apply in_or_app; right; exact INch).
  destruct (Hwf _ INc) as (BRc & DFc & APc). cbn [fst snd] in *.
  assert (A1 : forall b, In b (PML.ps_blocks ps ++ LBo) -> fst b <> ch -> PML.apart (fst b) (snd b) ch 16384).
  { intros b Hb Hne. pose proof (APc b (in_lb_remove ch _ b Hb Hne)) as X. unfold PML.apart. lia. }
  assert (N1 : PML.ps_bptr ps <> ch /\ PML.ps_sb ps <> ch).
  { unfold PML.ps_blocks in ND. cbn [app map fst] in ND. inversion ND as [|x1 l1 X1 X2]; subst. inversion X2 as [|x2 l2 X3 X4]; subst.
    assert (Hc : In ch (map fst LBo)) by (change ch with (fst (ch, 16384)); apply in_map; exact INch).
    split; intros Y; [apply X1; rewrite Y; right; apply stdpp.base.list_elem_of_In; exact Hc | apply X3; rewrite Y; apply stdpp.base.list_elem_of_In; exact Hc]. }
  split; [exact A1|]. split; [exact (proj1 N1)|]. split; [exact (proj2 N1)|].
  split.
  { intros b Hb. apply A1; [apply in_or_app; right; exact (lb_remove_in _ _ _ Hb)|].
    apply (lb_remove_fst ch LBo b); [|exact Hb]. unfold PML.ps_blocks in ND. cbn [app map fst] in ND. inversion ND as [|x1 l1 X1 X2]; subst. inversion X2 as [|x2 l2 X3 X4]; subst. exact X4. }
  destruct BRc as (B0 & B1 & B2 & B3 & B4). rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in B1.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact DFc|]. unfold block_range. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). lia.
Qed.

Ltac ow F := unfold L5.outside; let w := fresh "w" in let Hw := fresh "Hw" in let Hin := fresh "Hin" in
  intros w Hw Hin; unfold F in Hw; cbn [In] in Hw; unfold L5.in_rng in Hin;
  repeat (destruct Hw as [<-|Hw]; [cbn [fst snd] in Hin; lia|]); destruct Hw.

Lemma ginv_chunk : forall M M' model cr ps gp rdst bof gp' rdst' code' bof' g' B spc,
  ginv M model cr ps gp rdst 0 bof g0 B -> PMS.win_exhausted ps ->
  L5.frame_but ((spc - 512, 512) :: Wc) M M' -> mem_grows M M' -> sp - SS <= spc - 512 -> spc <= sp ->
  PMCS.rdc_at M' S IS ch bof' -> PML.isrc_at M' IS rep gp' rdst' -> gp <= gp' -> PML.ec_at M' E code' -> PML.ls_ok g' M' -> (g' = g0 \/ (g' = PML.regJ g0 /\ code' <> 0)) ->
  ginv M' model cr ps gp' rdst' code' bof' g' B.
Proof.
  intros M M' model cr ps gp rdst bof gp' rdst' code' bof' g' B spc (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN) WEX FB MG Hlo Hhi RDR' ISRC' Hgp EC' LS' GG'.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2]. destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in *.
  destruct (blk _ _ _ _ HH) as [BOK BF]. destruct (hfacts _ _ _ _ HH) as (HA & N1 & N2 & HK & C0 & C1 & C2 & C3 & C4).
  pose proof (TK2.frame_but_samem _ _ _ FB) as AG. set (F := (spc - 512, 512) :: Wc) in *.
  assert (CP : forall b, In b (PML.ps_blocks ps) -> TK2.cov (L5.outside F) (fst b) (snd b)).
  { intros b Hb i Hi. assert (Hb' : In b (PML.ps_blocks ps ++ LBo)) by (apply in_or_app; left; exact Hb). pose proof (BF b Hb') as X.
    assert (Hne : fst b <> ch) by (destruct Hb as [<-|[<-|[]]]; assumption). pose proof (HA b Hb' Hne) as Y. unfold PML.apart in Y. unfold hl_ceil in *.
    clear - X Y Hi Y1 Y3 Y4 Y5 Y6 Y9 Y10 Y11 Y12 Y13 Y14 Yt1 Yt2 Hlo Hhi. unfold F, Wc, S. ow F. }
  unfold ginv. split; [exact RDR'|].
  split; [apply (TK2.parser_at_x _ M M' AG); [unfold P; lia | intros i Hi; unfold P in Hi; unfold hl_ceil in *; unfold F, Wc, S; ow F | | exact PAR]|].
  { pose proof (BF _ (or_introl eq_refl)) as X1. pose proof (BF _ (or_intror (or_introl eq_refl))) as X2. cbn [fst snd] in X1, X2. unfold hl_ceil in *.
    split; [lia|]. split; [lia|]. split; [exact (CP _ (or_introl eq_refl))|]. split; [lia|]. split; [lia|]. exact (CP _ (or_intror (or_introl eq_refl))). }
  split; [exact WF|].
  split.
  { unfold PML.win_ok in *. unfold PMS.win_exhausted in WEX. destruct (PML.ps_win ps) as [[p e]|]; [|exact I]. destruct WOK as (ch' & W1 & W2 & W3 & W4). subst e.
    exists ch'. split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. intros i Hi. lia. }
  split; [exact ISRC'|].
  split; [apply (TK2.vis_at_x _ M M' AG); [unfold V; lia | intros i Hi; unfold V in *; unfold hl_ceil in *; unfold F, Wc, S; ow F | exact VIS]|].
  split; [exact EC'|]. split; [exact LS'|]. split; [exact GG'|].
  split.
  { apply (RB.heap_write_blk L HI HIok LAY _ _ M M' _ _ HH ltac:(lia) AG MG). intros a Ha NK. destruct (not_outside _ _ NK) as (w & Hw & Hin). unfold F, Wc, S in Hw. unfold L5.in_rng in Hin. unfold hl_ceil in *.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Hin; [left; lia | left; lia | left; lia | left; lia | | right; left; lia | right; left; lia].
    right; right. exists (ch, 16384). split; [apply in_or_app; right; exact INch | exact Hin]. }
  split; [exact MOK|]. split; [exact BV|]. split; [exact PC|]. split; [exact BB|].
  split; [lia|].
  assert (BOKk : TK2.blocks_ok L LBk) by (intros b Hb; apply BOK; apply in_or_app; right; exact (lb_remove_in _ _ _ Hb)).
  split; [|split].
  - apply (TK2.FR_samem L _ _ _ _ M0 M M' _ FR AG); [|intros a Ha Hd; apply MG; exact Hd].
    intros a Ha HC HF HE. pose proof (TK2.client_not_window L LAY LBk sp SS a HC BOKk ltac:(lia) ltac:(lia)) as NW.
    intros w Hw Hin. unfold F, Wc, S in Hw. unfold L5.in_rng in Hin.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn [fst snd] in Hin; [lia | | | | | | ];
      try (apply HF; apply in_foot; lia).
    pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
    destruct HC as [(b & Hb & Hr)|[(Q1 & Q2)|(Q1 & _)]]; [pose proof (HK b Hb) as Z0; unfold PML.apart in Z0; lia | unfold hl_ceil in *; lia | rewrite ILO, IHI in Q1; lia].
  - intros a Ha Hf Hd. apply MG. exact (DW a Ha Hf Hd).
  - apply (TK2.u8_x _ M M' AG); [lia | intros i Hi; unfold F, Wc, S; ow F | exact DN].
Qed.

Lemma pcredit_setwin : forall cr ps w, PML.pcredit_x L cr ps kx bx -> PML.pcredit_x L cr (PML.ps_set_win ps w) kx bx.
Proof. intros cr [] w H. exact H. Qed.

Lemma ginv_setwin : forall M M' model cr ps gp rdst bof g B p' k,
  ginv M model cr ps gp rdst 0 bof g B -> PMS.win_exhausted ps ->
  TK.samem (fun a => ~ (C + 512 <= a < C + 528)) M M' -> mem_grows M M' ->
  PML.u64 M' (C + 512) (p' + k) -> PML.u64 M' (C + 520) p' -> 0 < k -> ch <= p' -> p' + k <= ch + 16384 -> (B + k) + (D + n - gp) <= Bs ->
  ginv M' model cr (PML.ps_set_win ps (Some (p', p' + k))) gp rdst 0 bof g (B + k).
Proof.
  intros M M' model cr ps gp rdst bof g B p' k (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN) WEX AG MG C1 C2 Hk Hp1 Hp2 HB.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2].
  destruct (blk _ _ _ _ HH) as [BOK BF]. destruct (hfacts _ _ _ _ HH) as (HA & N1 & N2 & HK & Q0 & Q1 & Q2 & Q3 & Q4).
  assert (INo : forall b, In b LBo -> In b (PML.ps_blocks ps ++ LBo)) by (intros b Hb; apply in_or_app; right; exact Hb).
  assert (CB : forall b, In b (PML.ps_blocks ps ++ LBo) -> TK2.cov (fun a => ~ (C + 512 <= a < C + 528)) (fst b) (snd b)).
  { intros b Hb i Hi. destruct (BF b Hb) as (X1 & X2 & X3 & _). unfold hl_ceil in *. clear - X1 X2 X3 Hi Y1 Y3 Y12 Y13 Y14. lia. }
  pose proof (BF _ (or_introl eq_refl)) as X1. pose proof (BF _ (or_intror (or_introl eq_refl))) as X2. cbn [fst snd] in X1, X2.
  assert (AO : forall a, (a < C + 512 \/ C + 528 <= a) -> ~ (C + 512 <= a < C + 528)) by (intros a Ha; lia).
  destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in *.
  unfold ginv. split; [apply (rdc_at_x _ M M' AG); [unfold S; lia | intros i Hi; apply AO; unfold S in Hi; lia | exact RDR]|].
  split.
  { unfold P. apply (RB.parser_at_setwin M M' (C + 320) ps (Some (p', p' + k)) PAR); [| exact MG | lia | | |].
    - apply (TK.samem_weaken _ _ _ _ AG). intros a Ha. lia.
    - unfold hl_ceil in *. clear - X1 Y1 Y3 Y12 Y13 Y14 Yt2. lia.
    - unfold hl_ceil in *. clear - X2 Y1 Y3 Y12 Y13 Y14 Yt2. lia.
    - replace (C + 320 + 200) with (C + 520) by lia. replace (C + 320 + 192) with (C + 512) by lia. split; [exact C2 | split; [exact C1 | lia]]. }
  split; [exact (wf_setwin _ _ WF)|].
  split.
  { unfold PML.win_ok. destruct ps; cbn [PML.ps_set_win PML.ps_win]. exists ch. split; [exact INch|]. split; [exact Hp1|]. split; [exact Hp2|].
    intros i Hi. apply MG. replace (p' + i) with (ch + (p' + i - ch)) by lia. apply Q3. lia. }
  split; [apply (TK2.isrc_at_x _ M M' AG); [lia | intros i Hi; apply AO; lia | | exact ISRC]|].
  { split; [intros i Hi; apply AO; lia|]. destruct rep as [s|cap p s]; [exact I|]. pose proof (INo _ (INrep _ (or_introl eq_refl))) as Hb. pose proof (BF _ Hb) as X. cbn [fst snd] in X. unfold hl_ceil in *.
    split; [lia|]. split; [lia|]. exact (CB _ Hb). }
  split; [apply (TK2.vis_at_x _ M M' AG); [unfold V; lia | intros i Hi; apply AO; unfold V in Hi; lia | exact VIS]|].
  split; [apply (TK2.ec_at_x _ M M' AG); [lia | intros i Hi; apply AO; lia | exact EC]|].
  split; [apply (TK2.ls_ok_x _ M M' AG); [|exact LS]|].
  { apply TK2.statics_cov_lo; intros a Ha; apply AO; lia. }
  split; [exact GG|].
  split; [destruct ps; cbn [PML.ps_set_win PML.ps_blocks PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap] in *; apply (TK2.heap_stack_write L HI HIok LAY _ _ M M' _ (C + 512) (C + 528) HH); [lia | unfold hl_ceil in *; lia | lia | exact AG | exact MG]|].
  split; [exact MOK|]. split; [exact BV|]. split; [exact (pcredit_setwin _ _ _ PC)|].
  split.
  { destruct BB as [BB1 BB2]. unfold PMS.win_exhausted in WEX. unfold PML.buf_bound, PML.winlen, PML.buf_need in *. destruct ISRC as (_ & _ & _ & _ & _ & _ & GR & _).
    fold D n in GR. destruct ps as [st sst nst more done level stack sb scap bcap bptr buf win]; cbn [PML.ps_set_win PML.ps_win PML.ps_buf PML.ps_more PML.ps_st PML.ps_sst] in *.
    split; [|lia]. destruct win as [[p e]|]; lia. }
  split; [exact HB|].
  assert (BOKk : TK2.blocks_ok L LBk) by (intros b Hb; apply BOK; apply INo; exact (lb_remove_in _ _ _ Hb)).
  split; [|split].
  - apply (TK2.FR_samem L _ _ _ _ M0 M M' _ FR AG); [|intros a Ha Hd; apply MG; exact Hd].
    intros a Ha HC HF HE Hin. apply HF. apply in_foot. lia.
  - intros a Ha Hf Hd. apply MG. exact (DW a Ha Hf Hd).
  - apply (TK2.u8_x _ M M' AG); [lia | intros i Hi; apply AO; lia | exact DN].
Qed.

Lemma ginv_entry : forall M' cr ps gp rdst bof B,
  PMCS.cursor_at M0 C IS ch bof false ps -> PMCUR.wf_c (PMCUR.ps_set_more ps true) -> PML.win_ok M0 LBo ps -> PML.isrc_at M0 IS rep gp rdst -> PML.ec_at M0 E 0 ->
  PML.ls_ok g0 M0 -> hi_heap HI (PML.ps_blocks ps ++ LBo) cr M0 (m_vmmaps model0) -> PML.model_ok model0 -> PML.pcredit_x L cr ps kx bx ->
  PML.buf_bound (PMCUR.ps_set_more ps true) B -> B + (D + n - gp) <= Bs -> L5.defined M0 (sp - SS) SS ->
  TK.samem (fun a => ~ (sp - 80 <= a < sp) /\ ~ (C + 531 <= a < C + 532)) M0 M' -> mem_grows M0 M' -> PML.u8 M' (C + 531) 1 ->
  ginv M' model0 cr (PMCUR.ps_set_more ps true) gp rdst 0 bof g0 B.
Proof.
  intros M' cr ps gp rdst bof B (SRC & PAR & VIS & DN & DC) WF WOK ISRC EC LS HH MOK PC BB HB DS AG MG C531.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2]. destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in *.
  destruct (blk _ _ _ _ HH) as [BOK BF].
  assert (INo : forall b, In b LBo -> In b (PML.ps_blocks ps ++ LBo)) by (intros b Hb; apply in_or_app; right; exact Hb).
  set (K := fun a => ~ (sp - 80 <= a < sp) /\ ~ (C + 531 <= a < C + 532)) in *.
  assert (CB : forall b, In b (PML.ps_blocks ps ++ LBo) -> TK2.cov K (fst b) (snd b)) by (intros b Hb i Hi; destruct (BF b Hb); unfold K, hl_ceil in *; lia).
  assert (CO : forall lo len, sp <= lo -> (lo + len <= C + 531 \/ C + 532 <= lo) -> TK2.cov K lo len) by (intros lo len H1 H2 i Hi; unfold K; lia).
  pose proof (BF _ (or_introl eq_refl)) as X1. pose proof (BF _ (or_intror (or_introl eq_refl))) as X2. cbn [fst snd] in X1, X2.
  unfold ginv. split.
  { apply (rdc_at_x K M0 M' AG); [unfold S; lia | apply CO; unfold S; lia |]. split; [exact SRC | apply (L5.defined_sub _ _ _ _ _ DC); unfold S; lia]. }
  split.
  { unfold P. apply (parser_at_setmore K M0 M' (C + 320) ps PAR AG MG); [lia | apply CO; lia | apply CO; lia | | replace (C + 320 + 211) with (C + 531) by lia; exact C531].
    unfold hl_ceil in *. split; [lia|]. split; [lia|]. split; [exact (CB _ (or_introl eq_refl))|]. split; [lia|]. split; [lia|]. exact (CB _ (or_intror (or_introl eq_refl))). }
  split; [exact WF|].
  split; [destruct ps; cbn [PMCUR.ps_set_more PML.ps_win] in *; apply (RB.win_ok_x _ M0 M' AG); [|exact WOK]; intros b Hb; destruct (BF b (INo b Hb)); unfold hl_ceil in *; split; [lia|]; split; [lia | exact (CB b (INo b Hb))]|].
  split; [apply (TK2.isrc_at_x _ M0 M' AG); [lia | apply CO; lia | | exact ISRC]|].
  { split; [apply CO; lia|]. destruct rep as [s|cap p s]; [exact I|]. pose proof (INo _ (INrep _ (or_introl eq_refl))) as Hb. pose proof (BF _ Hb) as X. cbn [fst snd] in X. unfold hl_ceil in *.
    split; [lia|]. split; [lia|]. exact (CB _ Hb). }
  split; [apply (TK2.vis_at_x _ M0 M' AG); [unfold V; lia | apply CO; unfold V; lia | exact VIS]|].
  split; [apply (TK2.ec_at_x _ M0 M' AG); [lia | apply CO; lia | exact EC]|].
  split; [apply (TK2.ls_ok_x _ M0 M' AG); [|exact LS]|].
  { apply TK2.statics_cov_lo; intros a Ha; unfold K; unfold hl_ceil in *; lia. }
  split; [left; reflexivity|].
  split; [destruct ps; cbn [PMCUR.ps_set_more PML.ps_blocks PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap] in *;
          apply (TK2.heap_pure_write L HI HIok LAY _ _ M0 M' _ _ HH ltac:(lia) AG MG); intros a Ha NK; unfold K in NK; unfold hl_ceil in *; left; lia|].
  split; [exact MOK|]. split; [apply L5C.model_but_vm_refl|]. split; [destruct ps; exact PC|]. split; [exact BB|]. split; [exact HB|].
  assert (BOKk : TK2.blocks_ok L LBk) by (intros b Hb; apply BOK; apply INo; exact (lb_remove_in _ _ _ Hb)).
  split; [|split].
  - split.
    + intros a Ha HC HF HE. apply AG; [exact Ha|]. pose proof (TK2.client_not_window L LAY LBk sp SS a HC BOKk ltac:(lia) ltac:(lia)) as NW.
      split; [lia|]. intros Hc. apply HF. apply in_foot. lia.
    + intros a Ha. apply MG. replace a with (sp - SS + (a - (sp - SS))) by lia. apply DS. lia.
  - intros a Ha Hf Hd. apply MG. exact Hd.
  - apply (TK2.u8_x _ M0 M' AG); [lia | apply CO; lia | exact DN].
Qed.

Definition We : list L5.range := [(E, 16); (0xd4df8, 2); (0xf6848, 544)].
Lemma ginv_setec : forall M M' model cr ps gp rdst bof B spc code',
  ginv M model cr ps gp rdst 0 bof g0 B -> L5.frame_but ((spc - 256, 256) :: We) M M' -> mem_grows M M' -> sp - SS <= spc - 256 -> spc <= sp ->
  PML.ec_at M' E code' -> code' <> 0 -> PML.ls_ok (PML.regJ g0) M' ->
  ginv M' model cr ps gp rdst code' bof (PML.regJ g0) B.
Proof.
  intros M M' model cr ps gp rdst bof B spc code' (RDR & PAR & WF & WOK & ISRC & VIS & EC & LS & GG & HH & MOK & BV & PC & BB & BG & FR & DW & DN) FB MG Hlo Hhi EC' NZ LS'.
  pose proof lay as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15). pose proof Htop as [Yt1 Yt2].
  destruct (blk _ _ _ _ HH) as [BOK BF].
  pose proof (TK2.frame_but_samem _ _ _ FB) as AG. set (F := (spc - 256, 256) :: We) in *.
  assert (INo : forall b, In b LBo -> In b (PML.ps_blocks ps ++ LBo)) by (intros b Hb; apply in_or_app; right; exact Hb).
  assert (CB : forall b, In b (PML.ps_blocks ps ++ LBo) -> TK2.cov (L5.outside F) (fst b) (snd b)).
  { intros b Hb i Hi. pose proof (BF b Hb) as X. unfold hl_ceil in *. clear - X Hi Y1 Y9 Y10 Y11 Y12 Y13 Y14 Yt1 Yt2 Hlo Hhi. unfold F, We. ow F. }
  assert (CO : forall lo len, (lo + len <= E \/ E + 16 <= lo) -> sp <= lo -> TK2.cov (L5.outside F) lo len).
  { intros lo len H1 H2 i Hi. clear - H1 H2 Hi Y1 Y9 Y10 Y12 Y13 Y14 Hlo Hhi. unfold F, We. ow F. }
  destruct AP as (A1 & A2 & A3). unfold PML.apart, PMCS.CURSOR_SIZE in *.
  unfold ginv. split; [apply (rdc_at_x _ M M' AG); [unfold S; lia | apply CO; unfold S; lia | exact RDR]|].
  split; [apply (TK2.parser_at_x _ M M' AG); [unfold P; lia | unfold P; apply CO; lia | | exact PAR]|].
  { pose proof (BF _ (or_introl eq_refl)) as X1. pose proof (BF _ (or_intror (or_introl eq_refl))) as X2. cbn [fst snd] in X1, X2. unfold hl_ceil in *.
    split; [lia|]. split; [lia|]. split; [exact (CB _ (or_introl eq_refl))|]. split; [lia|]. split; [lia|]. exact (CB _ (or_intror (or_introl eq_refl))). }
  split; [exact WF|].
  split; [apply (RB.win_ok_x _ M M' AG); [|exact WOK]; intros b Hb; destruct (BF b (INo b Hb)) as (Z1 & Z2 & _); unfold hl_ceil in *; split; [lia|]; split; [lia | exact (CB b (INo b Hb))]|].
  split; [apply (TK2.isrc_at_x _ M M' AG); [lia | apply CO; lia | | exact ISRC]|].
  { split; [apply CO; lia|]. destruct rep as [s|cap p s]; [exact I|]. pose proof (INo _ (INrep _ (or_introl eq_refl))) as Hb. pose proof (BF _ Hb) as X. cbn [fst snd] in X. unfold hl_ceil in *.
    split; [lia|]. split; [lia|]. exact (CB _ Hb). }
  split; [apply (TK2.vis_at_x _ M M' AG); [unfold V; lia | apply CO; unfold V; lia | exact VIS]|].
  split; [exact EC'|]. split; [exact LS'|]. split; [right; split; [reflexivity | exact NZ]|].
  split.
  { apply (TK2.heap_pure_write L HI HIok LAY _ _ M M' _ _ HH ltac:(lia) AG MG). intros a Ha NK. destruct (not_outside _ _ NK) as (w & Hw & Hin). unfold F, We in Hw. unfold L5.in_rng in Hin. unfold hl_ceil in *.
    clear - Hw Hin Y1 Y9 Y10 Y12 Y13 Y14 Yt1 Yt2 Hlo Hhi Hsptop. destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [left; lia | left; lia | right; lia | right; lia]. }
  split; [exact MOK|]. split; [exact BV|]. split; [exact PC|]. split; [exact BB|]. split; [exact BG|].
  assert (BOKk : TK2.blocks_ok L LBk) by (intros b Hb; apply BOK; apply INo; exact (lb_remove_in _ _ _ Hb)).
  split; [|split].
  - apply (TK2.FR_samem L _ _ _ _ M0 M M' _ FR AG); [|intros a Ha Hd; apply MG; exact Hd].
    intros a Ha HC HF HE. pose proof (TK2.client_not_window L LAY LBk sp SS a HC BOKk ltac:(lia) ltac:(lia)) as NW.
    intros w Hw Hin. unfold F, We in Hw. unfold L5.in_rng in Hin. clear - Hw Hin NW HF Hlo Hhi Y12 Y13 Y14.
    destruct Hw as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [lia | | | ]; apply HF; apply in_foot; lia.
  - intros a Ha Hf Hd. apply MG. exact (DW a Ha Hf Hd).
  - apply (TK2.u8_x _ M M' AG); [lia | apply CO; lia | exact DN].
Qed.
End Run. End H. End RNI.
