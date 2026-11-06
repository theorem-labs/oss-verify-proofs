(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmLibSpecs PmEncSpecs PmLibSpecsXA PmLibSpecsX PmLibSpecsW PmRef PmRefFacts PmRefXA PmLibSpecsXAW RelLeaf.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import SmallPtXBW.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SPTAW2.
Import PML PMES.
Abbreviation mem := (word -> option byte).
Section W.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma room_end_container : forall (eroomA : eghost -> eev -> Prop) CL (arr : bool) c (M : mem) P ps w eg rest,
  PMXAW.roomwP eroomA CL -> (PMRXA.rm_matchA L) c M P ps -> 1 <= ps_level ps -> ps_stack ps = rest ++ [SPTAW.EC_KIND arr] ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) (if arr then PMW.FEndArray else PMW.FEndObject) c w) -> eroomA eg EvEnd.
Proof.
  intros eroomA CL arr c M P ps w eg rest RW ((R1 & R2 & R3 & R4 & R5) & _) HL HS HW.
  rewrite (SPTAW.end_container_step L) in HW. unfold PMXAW.wroomr, PMR.end_container in HW. rewrite R4 in HW.
  replace (ps_level ps <? 1) with false in HW by (symmetry; apply Z.ltb_ge; exact HL).
  unfold PMR.top in HW. rewrite R5, HS, last_last in HW. unfold SPTAW.EC_KIND in HW.
  assert (E : (if arr then ST_ARRAY else ST_OBJECT) =? (if arr then ST_ARRAY else ST_OBJECT) = true) by (apply Z.eqb_refl). rewrite E in HW.
  cbn [PMR.r_of PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al PMR.q_c PMR.q_w PMR.q_code] in HW.
  apply (SPTAW.room_first eroomA CL eg PMW.EkEnd [] 0 EvEnd RW HW eq_refl). cbn. lia.
Qed.
(* [comment removed for export] *)
Lemma wroom_end_number : forall CL (frac : bool) c buf eg,
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) (if frac then PMW.FEndFrac else PMW.FEndInt) c buf) ->
  PMXAW.wroom CL eg [PMW.EkNum] (28 + Z.of_nat (length buf)).
Proof.
  intros CL frac c buf eg HW.
  assert (E : PMW.rm_step (PMRXA.the_rmA L) (if frac then PMW.FEndFrac else PMW.FEndInt) c buf = PMR.r_of0 (PMR.end_number (PMR.of_text c buf) [])) by (destruct frac; reflexivity).
  rewrite E in HW. unfold PMXAW.wroomr, PMR.end_number in HW. rewrite PMRF.bind_ok in HW by reflexivity.
  assert (AV : forall c0 w0, PMR.q_evs (PMR.after_value c0 w0) = [] /\ PMR.q_al (PMR.after_value c0 w0) = 0).
  { intros c0 w0. unfold PMR.after_value. destruct (_ || _); [split; reflexivity|]. destruct (_ =? _); split; reflexivity. }
  cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMRF.pre PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code] in HW.
  destruct (AV (PMR.set_more (PMR.of_text c buf) true) (@nil Z)) as [AE AA]. rewrite AE, AA, Z.add_0_r in HW. cbn [app] in HW.
  unfold PMR.al_num in HW. cbn [PMR.c_dlen PMR.of_text PMR.set_tok PMR.set_more] in HW. exact HW.
Qed.
Lemma room_end_number : forall (eroomA : eghost -> eev -> Prop) CL (frac : bool) c buf eg ev,
  PMXAW.roomwP eroomA CL ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) (if frac then PMW.FEndFrac else PMW.FEndInt) c buf) ->
  PMW.kind_of ev = PMW.EkNum -> PMXAW.pay_hi ev <= 28 + Z.of_nat (length buf) -> eroomA eg ev.
Proof.
  intros eroomA CL frac c buf eg ev RW HW Hk Hp. exact (SPTAW.room_first eroomA CL eg PMW.EkNum [] (28 + Z.of_nat (length buf)) ev RW (wroom_end_number CL frac c buf eg HW) Hk Hp).
Qed.
(* [comment removed for export] *)
Lemma room_end_number_raw : forall (eroomA : eghost -> eev -> Prop) CL (frac : bool) c buf eg tag,
  PMXAW.roomwP eroomA CL ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) (if frac then PMW.FEndFrac else PMW.FEndInt) c buf) ->
  tag = 2 \/ tag = 3 -> eroomA eg (EvStr tag buf).
Proof.
  intros eroomA CL frac c buf eg tag RW HW Ht. pose proof (wroom_end_number CL frac c buf eg HW) as W. apply RW.
  unfold PMXAW.kmax. rewrite (proj1 (PMXAW.ind_raw_num (g_es eg) tag buf Ht)). unfold PMXAW.wroom in W. cbn [PMW.ind_run] in W.
  assert (PH : PMXAW.pay_hi (EvStr tag buf) = PMES.len buf) by (destruct Ht as [-> | ->]; reflexivity). rewrite PH. unfold PMES.len. clear - W. lia.
Qed.
End W.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AfterValueDone.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Definition after_value_specA_done (pc : Z) : Prop :=
  PMSA.ptrans_stalekA L ar HI IC pc PMSA.AFTERV_SCR 3 true (fun R M LBo P V E ps => PMSA.a0 R P /\ PMSA.a1 R E /\ ps_more ps = true /\ ps_st ps = ST_NUMBER)
         (fun ps ps' code R' => (code = 0 /\ ps_more ps' = true /\ ps_st ps' = (if Z.eqb (ps_level ps) 0 then ST_ACCEPT else ST_EXPECT_COMMA_OR_END) /\
                                 ps_stack ps' = ps_stack ps /\ ps_level ps' = ps_level ps /\ ps_win ps' = ps_win ps) /\ ps_done ps' = ps_done ps).
Lemma after_value_done_c : forall c w, PMR.c_done (PMR.q_c (PMR.after_value c w)) = PMR.c_done c.
Proof. intros c w. unfold PMR.after_value. destruct (_ || _); [reflexivity|]. destruct (_ =? _); reflexivity. Qed.
Lemma after_value_done_of_w : forall pc, PMXAW.after_value_specAW L ar HI IC (PMRXA.the_rmA L) pc -> after_value_specA_done pc.
Proof.
  intros pc HW mw LBo FF LK cr A sp r P V E B kx bx g ps. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE Hcont.
  pose proof PRE as (HA & Hsp32 & Hstksh & HPA & HPSH & HWF & HWIN & HBB & HVIS & HEC & HLS & HG & HPC & FO1 & FO2 & FO3 & AP1 & AP2 & AP3).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF.
  assert (RB : forall ch, In (ch, 16384) LBo -> 0 <= ch /\ ch + 16384 <= 2 ^ 64).
  { intros ch Hch. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WF (ch, 16384) ltac:(apply in_or_app; right; exact Hch)) as ((D0 & _ & _ & _ & _ & (D5 & _ & D7)) & _). cbn [fst snd] in D0, D5, D7. clear - D0 D5 D7. lia. }
  destruct (SPTAW.win_bytesA_exists L M LBo ps HWIN (proj2 (proj2 HBB)) RB) as (w & Hw).
  set (c := PMR.CT (ps_st ps) (ps_sst ps) (ps_nst ps) (ps_more ps) (ps_done ps) (ps_level ps) (ps_stack ps) 0 0 0 PMR.u8_init).
  apply (HW mw LBo FF LK cr A sp r P V E B kx bx g ps w [] c fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs).
  { repeat (split; [assumption|]). repeat split; reflexivity. }
  intros fx' R' M' model' LB' cr' LBk Wr LK' A' Hfp' (ps' & code & g' & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & HREL & W3a & W3b & W3c & KB) X1 X2 X3 X4 X5 X6 X7.
  apply (Hcont fx' R' M' model' LB' cr' LBk Wr LK' A' Hfp'); [| exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6 | exact X7].
  exists ps', code, g'. repeat (split; [assumption|]). split; [| exact KB]. split; [exact HREL|].
  destruct (W3c (proj1 HREL)) as (((_ & _ & Hd & _) & _) & _). cbn [PMW.rm_step PMRXA.the_rmA PMR.rstep PMW.r_ctrl PMR.r_of] in Hd. rewrite after_value_done_c in Hd. symmetry. exact Hd.
Qed.
End AfterValueDone.

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation uv := CL5A.uv.
#[local] Notation S := Datatypes.S (only parsing).      (* [comment removed for export] *)
Section Lit.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
#[local] Notation RSEGS := (hl_segs L).
Lemma byte_var_sound2 : forall seg cells k v E' (Mv M' : mem) p w,
  SPTAW.byte_var seg cells k = Some v -> SPTAW.has cells (KRange (EVar v) 0 255) = true -> know_ok RSEGS E' Mv cells ->
  (forall a b, L5.u8_at RSEGS Mv a b -> L5.u8_at RSEGS M' a b) ->
  uv E' seg = p -> L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w ->
  0 <= k < Z.of_nat (length w) -> uv E' (EVar v) = nth (Z.to_nat k) w 0.
Proof.
  intros seg cells k v E' Mv M' p w Hbv Hrg HK U8F Hp HB HF Hk. unfold SPTAW.byte_var in Hbv.
  pose proof (SPTAW.has_ok L E' Mv _ _ HK Hrg) as R1. cbn [kentry_ok] in R1. fold (uv E' (EVar v)) in R1.
  destruct (find _ cells) as [K|] eqn:Hf; [|discriminate Hbv]. apply find_some in Hf as [Hin HKc].
  destruct K as [[b o] w1 e| | | | | | | | | ]; try discriminate Hbv. destruct w1 as [|[|w1]]; try discriminate HKc. destruct e; try discriminate HKc.
  injection Hbv as <-. apply andb_prop in HKc as [Hb Ho]. apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. subst b o.
  pose proof ((CL5A.kword8_elim RSEGS) E' Mv _ _ (p + k) (proj1 (Forall_forall _ _) HK _ Hin) ltac:(unfold estart; cbn [a_base a_off]; fold (uv E' seg); rewrite Hp; reflexivity)) as U1.
  apply U8F in U1.
  pose proof (HB (Z.to_nat k) ltac:(lia)) as U2. rewrite Z2Nat.id in U2 by lia.
  pose proof (proj1 (Forall_forall _ _) HF (nth (Z.to_nat k) w 0) ltac:(apply nth_In; lia)) as R2. cbn beta in R2.
  exact (SPTAW.u8_inj L M' (p + k) _ _ U1 U2 ltac:(clear -R1; lia) ltac:(clear -R2; lia)).
Qed.
Lemma wmatch_sound2 : forall seg cells litb E' (Mv M' : mem) p w, SPTAW.wmatch_chk seg cells litb = true -> know_ok RSEGS E' Mv cells ->
  (forall a b, L5.u8_at RSEGS Mv a b -> L5.u8_at RSEGS M' a b) -> uv E' seg = p ->
  L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w -> (forall kl, In kl litb -> 0 <= fst kl < Z.of_nat (length w)) ->
  forall kl, In kl litb -> nth (Z.to_nat (fst kl)) w 0 = snd kl.
Proof.
  intros seg cells litb E' Mv M' p w H HK U8F Hp HB HF Hr kl Hin. unfold SPTAW.wmatch_chk in H. apply forallb_forall with (x := kl) in H; [|exact Hin].
  destruct (SPTAW.byte_var seg cells (fst kl)) as [v|] eqn:Hbv; [|discriminate H]. apply andb_prop in H as [Hrg H].
  pose proof (byte_var_sound2 seg cells (fst kl) v E' Mv M' p w Hbv Hrg HK U8F Hp HB HF (Hr kl Hin)) as Hv.
  pose proof (proj1 (Forall_forall _ _) HF (nth (Z.to_nat (fst kl)) w 0) ltac:(apply nth_In; pose proof (Hr kl Hin); lia)) as R2. cbn beta in R2.
  pose proof (SPTAW.adm_all_sound L v cells 0 256 _ E' Mv _ H HK Hv ltac:(clear -R2; lia)) as X. cbn beta in X. apply Z.eqb_eq in X. exact X.
Qed.
Lemma wmiss_sound2 : forall seg cells litb E' (Mv M' : mem) p w, SPTAW.wmiss_chk seg cells litb = true -> know_ok RSEGS E' Mv cells ->
  (forall a b, L5.u8_at RSEGS Mv a b -> L5.u8_at RSEGS M' a b) -> uv E' seg = p ->
  L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w -> (forall kl, In kl litb -> 0 <= fst kl < Z.of_nat (length w)) ->
  exists kl, In kl litb /\ nth (Z.to_nat (fst kl)) w 0 <> snd kl.
Proof.
  intros seg cells litb E' Mv M' p w H HK U8F Hp HB HF Hr. unfold SPTAW.wmiss_chk in H. apply existsb_exists in H as (kl & Hin & H). exists kl. split; [exact Hin|].
  destruct (SPTAW.byte_var seg cells (fst kl)) as [v|] eqn:Hbv; [|discriminate H]. apply andb_prop in H as [Hrg H].
  pose proof (byte_var_sound2 seg cells (fst kl) v E' Mv M' p w Hbv Hrg HK U8F Hp HB HF (Hr kl Hin)) as Hv.
  pose proof (proj1 (Forall_forall _ _) HF (nth (Z.to_nat (fst kl)) w 0) ltac:(apply nth_In; pose proof (Hr kl Hin); lia)) as R2. cbn beta in R2.
  pose proof (SPTAW.adm_all_sound L v cells 0 256 _ E' Mv _ H HK Hv ltac:(clear -R2; lia)) as X. cbn beta in X. apply negb_true_iff in X. apply Z.eqb_neq in X. exact X.
Qed.
(* [comment removed for export] *)
Lemma litb_of_pos : forall (tail w : list Z) (kl : Z * Z), (S (length tail) <= length w)%nat -> In kl (SPTAW.litb_of tail) -> 0 <= fst kl < Z.of_nat (length w).
Proof.
  intros tail w [k b] Hlen Hin. unfold SPTAW.litb_of in Hin. apply in_combine_l in Hin. apply in_map_iff in Hin as (i & <- & Hi). apply in_seq in Hi. cbn [fst]. lia.
Qed.
(* [comment removed for export] *)
Lemma lit_match_of_chk : forall seg tail cells E' (Mv M' : mem) p w,
  SPTAW.wmatch_chk seg cells (SPTAW.litb_of tail) = true -> know_ok RSEGS E' Mv cells -> (forall a b, L5.u8_at RSEGS Mv a b -> L5.u8_at RSEGS M' a b) ->
  uv E' seg = p -> L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w -> (S (length tail) <= length w)%nat ->
  forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = true.
Proof.
  intros seg tail cells E' Mv M' p w H HK U8F Hp HB HF Hlen. apply SPTAW.lit_cmp_true; [exact Hlen|].
  exact (wmatch_sound2 seg cells _ E' Mv M' p w H HK U8F Hp HB HF (fun kl Hkl => litb_of_pos tail w kl Hlen Hkl)).
Qed.
Lemma lit_miss_of_chk : forall seg tail cells E' (Mv M' : mem) p w,
  SPTAW.wmiss_chk seg cells (SPTAW.litb_of tail) = true -> know_ok RSEGS E' Mv cells -> (forall a b, L5.u8_at RSEGS Mv a b -> L5.u8_at RSEGS M' a b) ->
  uv E' seg = p -> L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w -> (S (length tail) <= length w)%nat ->
  forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = false.
Proof.
  intros seg tail cells E' Mv M' p w H HK U8F Hp HB HF Hlen. apply SPTAW.lit_cmp_false; [exact Hlen|].
  exact (wmiss_sound2 seg cells _ E' Mv M' p w H HK U8F Hp HB HF (fun kl Hkl => litb_of_pos tail w kl Hlen Hkl)).
Qed.
(* [comment removed for export] *)
Lemma wroom_lit : forall CL f tail sst c w eg,
  SPTAW.lit_f f = Some (tail, sst) -> (S (length tail) <= length w)%nat -> forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = true ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) f c w) -> PMXAW.wroom CL eg [PMW.EkLit] PMR.AL_LIT.
Proof.
  intros CL f tail sst c w eg Hf Hlen Hcmp HW. rewrite (SPTAW.lit_step L f tail sst c w Hf) in HW. unfold PMXAW.wroomr, PMR.parse_lit in HW.
  replace (S (length tail) <=? length w)%nat with true in HW by (symmetry; apply Nat.leb_le; exact Hlen). rewrite Hcmp in HW. unfold PMR.lit_done in HW.
  cbn [PMR.r_of PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al PMR.q_c PMR.q_w PMR.q_code] in HW. exact HW.
Qed.
Lemma room_lit : forall (eroomA : eghost -> eev -> Prop) CL f tail sst c w eg ev,
  PMXAW.roomwP eroomA CL -> SPTAW.lit_f f = Some (tail, sst) -> (S (length tail) <= length w)%nat ->
  forallb (fun q => fst q =? snd q) (combine (tl (firstn (S (length tail)) w)) tail) = true ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) f c w) -> (ev = EvNull \/ exists b, ev = EvBool b) -> eroomA eg ev.
Proof.
  intros eroomA CL f tail sst c w eg ev RW Hf Hlen Hcmp HW Hev.
  apply (SPTAW.room_first eroomA CL eg PMW.EkLit [] PMR.AL_LIT ev RW (wroom_lit CL f tail sst c w eg Hf Hlen Hcmp HW)).
  - destruct Hev as [-> | (b & ->)]; reflexivity.
  - unfold PMR.AL_LIT. destruct Hev as [-> | (b & ->)]; cbn; [lia|]. destruct b; lia.
Qed.
End Lit.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SkipSpace.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
#[local] Notation RSEGS := (hl_segs L).
Lemma named_byte2 : forall cells cur k v E' (Mv M' : mem) p w (n : nat),
  SPTAW.has cells (KWord (SA cur k) 1 (EVar v)) = true -> SPTAW.has cells (KRange (EVar v) 0 255) = true -> know_ok RSEGS E' Mv cells ->
  (forall a b, L5.u8_at RSEGS Mv a b -> L5.u8_at RSEGS M' a b) ->
  L5.bytes_at RSEGS M' p w -> Forall (fun b => 0 <= b <= 255) w -> uv E' cur + k = p + Z.of_nat n -> (n < length w)%nat ->
  uv E' (EVar v) = nth n w 0.
Proof.
  intros cells cur k v E' Mv M' p w n Hl Hrg HK U8F HB HF Hcur Hn.
  pose proof (SPTAW.has_ok L E' Mv _ _ HK Hrg) as R1. cbn [kentry_ok] in R1. fold (uv E' (EVar v)) in R1.
  pose proof ((CL5A.kword8_elim RSEGS) E' Mv _ _ (p + Z.of_nat n) (SPTAW.has_ok L E' Mv _ _ HK Hl) ltac:(unfold estart; cbn [a_base a_off]; fold (uv E' cur); rewrite <- Hcur; reflexivity)) as U1.
  apply U8F in U1.
  pose proof (HB n Hn) as U2.
  pose proof (proj1 (Forall_forall _ _) HF (nth n w 0) ltac:(apply nth_In; exact Hn)) as R2. cbn beta in R2.
  exact (SPTAW.u8_inj L M' (p + Z.of_nat n) _ _ U1 U2 ltac:(clear -R1; lia) ltac:(clear -R2; lia)).
Qed.
(* [comment removed for export] *)
Lemma w3_skip_space : forall c c2 (M M' : mem) P ps ps' w (n : nat),
  (PMRXA.rm_matchA L) c M P ps -> PMR.skip_space c w = (c2, skipn n w) -> (n <= length w)%nat ->
  ((c2 = c /\ ps_st ps' = ps_st ps /\ ps_stack ps' = ps_stack ps) \/
   (c2 = PMR.set_st (PMR.push c (PMR.c_st c)) ST_CR /\ ps_st ps' = ST_CR /\ ps_stack ps' = ps_stack ps ++ [ps_st ps])) ->
  ps_more ps' = ps_more ps -> ps_done ps' = ps_done ps -> ps_level ps' = ps_level ps ->
  ps_st ps <> ST_STRING -> ps_st ps <> ST_NUMBER ->
  winlen ps - winlen ps' = Z.of_nat n -> (PMXAW.win_bytesA L) M' ps' (skipn n w) ->
  SPTAW.w3p L PMW.FSkipSpace c w M' P ps ps' w 0.
Proof.
  intros c c2 M M' P ps ps' w n ((R1 & R2 & R3 & R4 & R5) & _ & _) Hss Hn Hcase Q2 Q3 Q4 NS NN HU HWB. unfold SPTAW.w3p.
  change (PMW.rm_step (PMRXA.the_rmA L) PMW.FSkipSpace c w) with (PMR.r_of w (PMR.skip_space_r c w)). unfold PMR.skip_space_r. rewrite Hss.
  unfold PMW.w_after. cbn [fst snd PMR.r_of PMR.ret PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMR.q_c PMR.q_w PMR.q_evs PMR.q_code].
  rewrite length_skipn. replace (Z.of_nat (length w) - Z.of_nat (length w - n)) with (Z.of_nat n) by lia. rewrite Nat2Z.id.
  split; [reflexivity|]. split; [reflexivity|]. intros _. split; [|split; [symmetry; exact HU | exact HWB]].
  destruct Hcase as [(-> & S1 & S5)|(-> & S1 & S5)].
  - apply (SPTAW.rm_match_plain L); cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack];
      [rewrite S1; exact R1 | rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite S5; exact R5 | rewrite S1; exact NS | rewrite S1; exact NN].
  - apply (SPTAW.rm_match_plain L); cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.set_st PMR.push PMR.set_stack PMR.c_sst PMR.c_nst PMR.c_cp PMR.c_cp2 PMR.c_dlen PMR.c_u8];
      [rewrite S1; reflexivity | rewrite Q2; exact R2 | rewrite Q3; exact R3 | rewrite Q4; exact R4 | rewrite S5, R5, R1; reflexivity
      | rewrite S1; unfold ST_CR, ST_STRING; lia | rewrite S1; unfold ST_CR, ST_NUMBER; lia].
Qed.
End SkipSpace.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Esv.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Lemma wroom_esv : forall CL c x (ps : pstate) rest top eg,
  PMR.rm_core c ps -> PMR.validate x = 0 -> ps_stack ps = rest ++ [top] ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) PMW.FEndStringValue c x) ->
  (top = ST_MEMBER_NAME -> PMXAW.wroom CL eg [PMW.EkKey] (PMR.al_str (Z.of_nat (length x)))) /\
  (top = ST_OBJECT \/ top = ST_ARRAY \/ top = ST_ROOT -> PMXAW.wroom CL eg [PMW.EkStr true] (PMR.al_str (Z.of_nat (length x)))).
Proof.
  intros CL c x ps rest top eg (R1 & R2 & R3 & R4 & R5) Hv Hs HW.
  unfold PMXAW.wroomr in HW. rewrite (SPTAW.end_string_step L) in HW. unfold PMR.end_string in HW.
  destruct (SPTAW.of_text_fields c x) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). rewrite F7, Hv in HW. cbn [negb Z.eqb] in HW.
  unfold PMR.top in HW. rewrite F5, R5, Hs, last_last, F6 in HW.
  split; intros Ht.
  - subst top. change (ST_MEMBER_NAME =? ST_MEMBER_NAME) with true in HW. cbv iota in HW.
    cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in HW. exact HW.
  - destruct Ht as [-> |[-> | ->]].
    + change (ST_OBJECT =? ST_MEMBER_NAME) with false in HW. change ((ST_OBJECT =? ST_OBJECT) || (ST_OBJECT =? ST_ARRAY)) with true in HW.
      cbv iota in HW. cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in HW. exact HW.
    + change (ST_ARRAY =? ST_MEMBER_NAME) with false in HW. change ((ST_ARRAY =? ST_OBJECT) || (ST_ARRAY =? ST_ARRAY)) with true in HW.
      cbv iota in HW. cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in HW. exact HW.
    + change (ST_ROOT =? ST_MEMBER_NAME) with false in HW. change ((ST_ROOT =? ST_OBJECT) || (ST_ROOT =? ST_ARRAY)) with false in HW. change (ST_ROOT =? ST_ROOT) with true in HW.
      cbv iota in HW. cbn [PMR.r_of0 PMW.r_evs PMW.r_allow PMR.q_evs PMR.q_al] in HW. exact HW.
Qed.
Lemma room_esv_key : forall (eroomA : eghost -> eev -> Prop) CL c x (ps : pstate) rest eg,
  PMXAW.roomwP eroomA CL -> PMR.rm_core c ps -> PMR.validate x = 0 -> ps_stack ps = rest ++ [ST_MEMBER_NAME] ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) PMW.FEndStringValue c x) -> eroomA eg (EvKey x).
Proof.
  intros eroomA CL c x ps rest eg RW HC Hv Hs HW.
  apply (SPTAW.room_first eroomA CL eg PMW.EkKey [] (PMR.al_str (Z.of_nat (length x))) (EvKey x) RW (proj1 (wroom_esv CL c x ps rest _ eg HC Hv Hs HW) eq_refl) eq_refl).
  unfold PMXAW.pay_hi, PMR.al_str. pose proof (SPTAW.esc_len_bound x). lia.
Qed.
Lemma room_esv_value : forall (eroomA : eghost -> eev -> Prop) CL c x (ps : pstate) rest top eg tag,
  PMXAW.roomwP eroomA CL -> PMR.rm_core c ps -> PMR.validate x = 0 -> ps_stack ps = rest ++ [top] -> (top = ST_OBJECT \/ top = ST_ARRAY \/ top = ST_ROOT) -> 0 <= tag <= 1 ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) PMW.FEndStringValue c x) -> eroomA eg (EvStr tag x).
Proof.
  intros eroomA CL c x ps rest top eg tag RW HC Hv Hs Htop Htag HW.
  apply (SPTAW.room_first eroomA CL eg (PMW.EkStr true) [] (PMR.al_str (Z.of_nat (length x))) (EvStr tag x) RW (proj2 (wroom_esv CL c x ps rest top eg HC Hv Hs HW) Htop)).
  - cbn. replace ((tag =? 2) || (tag =? 3)) with false; [reflexivity|]. symmetry. apply orb_false_intro; apply Z.eqb_neq; lia.
  - unfold PMXAW.pay_hi, PMR.al_str. pose proof (SPTAW.esc_len_bound x). unfold len. destruct ((tag =? 1) || (tag =? 2) || (tag =? 3)); lia.
Qed.
End Esv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma retE_a1 : forall E' nx R2, ev (CH2.retE E' nx R2) (nx + 5) = getr R2 11%bv.
Proof. intros E' nx R2. unfold CH2.retE. rewrite APS.ext_list_at by (clear; cbn; lia). cbn [APC.caller_saved map nth]. f_equal. Qed.
Lemma retEx_a1 : forall E' nx ghosts R2, ev (CH2.retEx E' nx ghosts R2) (nx + length ghosts + 5) = getr R2 11%bv.
Proof. intros. unfold CH2.retEx. apply retE_a1. Qed.
End SPTAW2.
