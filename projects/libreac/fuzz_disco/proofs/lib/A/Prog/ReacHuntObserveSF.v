(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 794 of its 824 lines of code are new or changed and 39 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd ACbf ACj1 DiscoACja DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve DiscoRo ReacFrameCleanLen ReacHuntObserve ReacHuntObserveSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Module HoFM.
Import CtrlParsed disco_classify_c disco_table_c disco_table reac_frame_clean_len_c reac_disco_table_observe_c
  hunt_c reac_hunt_observe_c HuntObsLib HuntObsFacts.
Lemma hof_facts : forall H FR L now T' c r,
  hunt_ok H -> length FR = 50%nat ->
  cm_ret FR L (sub H 412 6) (Some (sub H 400 12)) = 0 ->
  observe_model (sub H 0 400) (sight FR L) 0 now T' c ->
  tbl_T1 T' -> tbl_T2 T' -> tbl_T4 T' -> length T' = 400%nat ->
  find_res T' (s_mac (sight FR L)) r ->
  ho_facts H FR L (sub H 0 400) (if r <? 0 then sight FR L else ho_entry T' (sight FR L) r).
Proof.
  intros H FR L now T' c r HOK LF R0 OM T1' T2' T4' LT' FRr.
  set (G := sight FR L) in *. set (T := sub H 0 400) in *.
  pose proof (cm_ret0_len _ _ _ _ R0) as L50.
  destruct (cm_ret0_facts _ _ _ _ R0) as [NU DK].
  destruct (sight_vals FR L LF) as (SM & SR & SC & SH & SD). fold G in SM, SR, SC, SH, SD.
  pose proof (sight_len FR L LF) as LG. fold G in LG.
  destruct (sight_ok FR L LF) as [S1 S2]. fold G in S1, S2.
  assert (LH : length H = 480%nat) by (destruct HOK as (X & _); exact X).
  assert (TOK : table_ok T) by (destruct HOK as (_ & X & _); exact X).
  destruct TOK as (TT1 & TT2 & TT3 & TT4).
  assert (LT : length T = 400%nat) by (unfold T; apply length_sub; lia).
  destruct (obs_at T G 0 now T' c r LT LG TT1 TT3 S1 OM FRr) as [CH RL].
  assert (MG : s_mac G = sub FR 6 6).
  { rewrite SM. unfold src, fld, sub. change (Z.to_nat 6) with 6%nat. reflexivity. }
  assert (NE : s_mac G <> sub H 412 6).
  { rewrite SM. intros X. unfold bytes_eqb in NU. rewrite X in NU.
    match type of NU with context [list_eq_dec ?d ?a ?b] => destruct (list_eq_dec d a b) as [_|Y] end;
      [discriminate | apply Y; reflexivity]. }
  assert (DF : (fb FR 16 = 0 /\ fb FR 17 = 0) \/ fsum FR = 0).
  { destruct DK as [DK|DK]; [left; apply dkind1 in DK; exact DK | right; exact DK]. }
  unfold ho_facts. destruct (r <? 0) eqn:RL0; cbv beta iota.
  - apply Z.ltb_lt in RL0.
    split; [lia|]. split; [exact MG|]. split; [exact NE|]. split; [rewrite SC; lia|].
    split; [exact S1|]. split; [exact DF|]. split; [exact SH|].
    split; [intros X; apply SD; lia|].
    intros (j & Hj & Ej & Rj). destruct (RL j Hj Ej Rj) as [X _]. lia.
  - apply Z.ltb_ge in RL0. unfold tbl_T1 in T1'.
    assert (Hrn : 0 <= r < n_of T') by (destruct FRr as [(X & _) | (X & _)]; lia).
    destruct (ho_entry_f T' G r LT' LG ltac:(lia)) as (EM & ER & EH & EI & EO & EC).
    destruct (T4' r Hrn) as (H01 & H40 & _).
    rewrite EM, ER, EH, EI, EO, EC.
    split; [lia|]. split; [exact MG|]. split; [exact NE|]. split; [rewrite <- SC; apply CH; lia|].
    split; [apply T2'; exact Hrn|]. split; [exact DF|]. split; [exact H01|].
    split; [intros X; apply H40; lia|].
    intros (j & Hj & Ej & Rj). destruct (RL j Hj Ej Rj) as [_ X]. exact X.
Qed.
End HoFM.

Module HoFM2.
Import CtrlParsed disco_classify_c disco_table_c reac_frame_clean_len_c reac_disco_table_observe_c
  hunt_c reac_hunt_observe_c.
Lemma hof_F : forall H FB O len now out r H2 T' G ret (OUT : list byte -> Prop),
  hunt_ok H -> length FB = 50%nat -> hunt_ok H2 -> H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  observe_model (sub H 0 400) G 0 now T' ret ->
  cm_ret FB (reac_frame_clean_len_model len) (sub H 412 6) (Some (sub H 400 12)) = 0 ->
  G = sight FB (reac_frame_clean_len_model len) ->
  skipn 400 H2 = (match cm_lock FB (reac_frame_clean_len_model len) (sub H 412 6) (Some (sub H 400 12)) with
                  | Some x => x | None => sub H 400 12 end) ++ sub H 412 12 ++
    (if n_of (sub H 0 400) =? 0 then Mem.le8 (Z_to_bv 64 now) else sub H 424 8) ++ skipn 432 H ->
  r = (if ret =? 0 then 0 else 1) ->
  (out <> 0 -> exists A, ho_answer T' G A /\ OUT A) ->
  tho_model H FB O len now out r H2 OUT.
Proof.
  intros H FB O len now out r H2 T' G ret OUT HOK LFB HOK2 HH2 LT' OM R0 HG Hsk Hr HA.
  unfold tho_model. cbv zeta. split.
  - intros X. exfalso. exact (X R0).
  - intros _. exists T', ret. split; [rewrite <- HG; exact OM|]. split; [exact Hr|].
    split; [rewrite HH2 at 1; rewrite Hsk; reflexivity|].
    intros Hout. destruct (HA Hout) as (A & HAns & HOA). exists A.
    split; [rewrite <- HG; exact HAns|]. split; [exact HOA|].
    destruct HAns as (rr & Hfr & ->). subst G.
    assert (Hf4 : firstn 400 H2 = T').
    { rewrite HH2. rewrite firstn_app, <- LT', firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
    destruct HOK2 as (_ & HT2 & _). rewrite Hf4 in HT2. destruct HT2 as (T1' & T2' & _ & T4').
    exact (HoFM.hof_facts H FB _ now T' ret rr HOK LFB R0 OM T1' T2' T4' LT' Hfr).
Qed.
Lemma hof_ans0 : forall T' G, n_of T' <= 0 -> ho_answer T' G G.
Proof.
  intros T' G Hn. exists (-1). split; [left; split; [reflexivity | intros j Hj; lia] | reflexivity].
Qed.
Lemma hof_mono : forall H FB O len now out r H2 A (OUT : list byte -> Prop),
  tho_model H FB O len now out r H2 (fun A' => A' = A) -> OUT A -> tho_model H FB O len now out r H2 OUT.
Proof.
  intros H FB O len now out r H2 A OUT. unfold tho_model. cbv zeta. intros [X Y] HO. split.
  - intros N. destruct (X N) as (a & b & d). split; [exact a|]. split; [exact b|].
    intros Ho. rewrite (d Ho). exact HO.
  - intros Z0. destruct (Y Z0) as (T'' & cc & a & b & d & e). exists T'', cc.
    split; [exact a|]. split; [exact b|]. split; [exact d|].
    intros Ho. destruct (e Ho) as (A' & f & g & h). exists A'.
    split; [exact f|]. split; [rewrite g; exact HO | exact h].
Qed.
End HoFM2.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).

Definition hoW (c : hoC) (a : Z) : Prop :=
  (c_out c <> 0 /\ c_out c <= a < c_out c + 24) \/
  (spZ (c_regs c) - REAC_HUNT_OBSERVE_STK <= a < spZ (c_regs c) - 104).

Lemma ho_vm_kept : forall (Wx : world SEGS) m m' a n v,
  (forall k, (k < n)%nat -> aview SEGS (w_H Wx) m' (a + Z.of_nat k) = aview SEGS (w_H Wx) m (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict (w_H Wx) m) a n v -> val_mem SEGS (mrestrict (w_H Wx) m') a n v.
Proof.
intros Wx m m' a n v HE HV k Hk. rewrite <- (HV k Hk). apply (mbyte_of_aview SEGS). exact (HE k Hk).
Qed.

Lemma ho_garr_moved : forall (Wx : world SEGS) m m' a b l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H Wx) m' (a + i) = aview SEGS (w_H Wx) m (b + i)) ->
  garr8 SEGS (mrestrict (w_H Wx) m) b l -> garr8 SEGS (mrestrict (w_H Wx) m') a l.
Proof.
intros Wx m m' a b l HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H Wx) (w_H Wx) m m' (b + Z.of_nat j) (a + Z.of_nat j) 1 _); [|exact Hv].
intros k Hk. cbn [Z.of_nat Pos.to_nat] in Hk. rewrite <- !Z.add_assoc. apply HE. lia.
Qed.

Lemma ho_apr_grows : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
pose proof (HG (Z_to_bv 64 a)) as X. unfold mrestrict in X. rewrite Hh, Hb in X. cbv iota in X.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply X; [discriminate | reflexivity]].
Qed.

Lemma ho_out_loc : forall c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F,
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F -> c_out c <> 0 ->
  (c_out c + 24 <= F \/ F + 128 <= c_out c) /\
  (forall a, c_out c <= a < c_out c + 24 -> ~ in_img SEGS a) /\
  (spZ (c_regs c) <= c_out c \/ c_out c + 24 <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK) /\
  (c_out c + 24 <= c_h c \/ c_h c + 480 <= c_out c) /\
  amem_range (c_out c) 24 /\ c_out c mod 8 = 0 /\ c_out c + 24 <= 2 ^ 63.
Proof.
intros c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB Hn.
destruct HB as (HP & HM & HS1 & HFe & HR & HSV).
pose proof HP as ((mdc & HJc) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hout & _ & _).
pose proof HJc as (HARc & _).
destruct HM as (HJ2 & Hfrs & EFA & Hperm & _).
pose proof HJ2 as (HAR2 & _).
destruct (Hout Hn) as ((Hm8 & H63 & Ham & Hwo & _ & _ & _ & _ & _ & _ & Hloc) & Hoh & _).
assert (Hfin : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFB : fs_frame_bytes 1 = 128) by reflexivity.
assert (HF2 : frame_addr ly2 1 fpos = F) by (rewrite EFA; symmetry; exact HFe).
split; [|split; [|split; [exact Hwo | split; [exact Hoh | split; [exact Ham | split; [exact Hm8 | exact H63]]]]]].
- destruct Hloc as [(cid & pos & Hfi & Hf1 & Hf2) | (b & m & Hbi & Hb1 & Hb2)].
  + destruct (in_split _ _ Hfi) as (l2 & l3 & El).
    pose proof (sep_frames_pos SEGS B LAWS ly2 S2 W2 mem md (1, fpos) (cid, pos) [] l2 l3 HAR2
      ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite HF2, HFB, (EFA cid pos) in Hd. lia.
  + assert (Hb2' : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbi).
    pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem md b m 1 fpos HAR2 Hb2' Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HF2, HFB in Hd. lia.
- intros a Ha. destruct Hloc as [(cid & pos & Hfi & Hf1 & Hf2) | (b & m & Hbi & Hb1 & Hb2)].
  + apply (frm_img SEGS B LAWS _ _ _ _ _ cid pos a HARc Hfi). lia.
  + apply (blk_img SEGS B LAWS _ _ _ _ _ b m a HARc Hbi). lia.
Qed.

Lemma ho_rdword_ext : forall (rd rd' : Z -> option Z) a,
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a HE. unfold rdword.
pose proof (HE 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. rewrite E0.
rewrite (HE 1), (HE 2), (HE 3), (HE 4), (HE 5), (HE 6), (HE 7) by lia. reflexivity.
Qed.

Ltac ho_cls := assert (8192 <= CLS_STK) by (unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK; lia);
  assert (REAC_HUNT_OBSERVE_STK = 176 + CLS_STK) by reflexivity.

Lemma ho_Fb : forall c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F,
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F ->
  4096 <= F /\ F + 128 <= YM05.alloc_ceiling /\ F mod 32 = 0 /\ in_app F 128 /\
  In (1, fpos) (frames S2) /\ frame_addr ly2 1 fpos = F /\
  YM05.alloc_ceiling <= spZ (c_regs c) - REAC_HUNT_OBSERVE_STK /\ spZ (c_regs c) <= 2 ^ 47 /\
  spZ (c_regs c) - 176 <= sp1 <= spZ (c_regs c) - 160 /\ sp1 mod 32 = 0 /\ 8192 + 176 <= REAC_HUNT_OBSERVE_STK.
Proof.
intros c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB.
destruct HB as (HP & HM & HS1 & HFe & HR & HSV).
pose proof HP as ((mdc & HJc) & _ & _ & _ & _ & _ & _ & Hwin & Hsp & _).
pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct HM as (HJ2 & Hfrs & EFA & Hperm & _). pose proof HJ2 as (HAR2 & _).
destruct HS1 as (_ & Hs1 & Hs2).
ho_cls.
assert (Hfin : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFB : fs_frame_bytes 1 = 128) by reflexivity.
assert (HF2 : frame_addr ly2 1 fpos = F) by (rewrite EFA; symmetry; exact HFe).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (Hf4 & Hfc & Happ).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin) as (Hal & _).
rewrite HF2, HFB in *.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [exact Happ|]. split; [exact Hfin|].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hs2 | lia].
Qed.

Lemma ho_step : forall c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F mem' md' regs',
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem' md' k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ hoW c a -> aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem a) ->
  (forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a) ->
  ho_regs_mid B c regs' sp1 F ->
  ho_base B c fpos ly2 S2 W2 mem' md' k2 H2 regs' sp1 F.
Proof.
intros c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F mem' md' regs' HB HJ' HE HA HR'.
pose proof (ho_out_loc c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as Hob.
destruct (ho_Fb c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as (HFf4 & HFfc & _).
destruct HB as (HP & HM & HS1 & HFe & HR & HSV).
pose proof HP as ((mdc & HJc) & _ & _ & _ & _ & _ & _ & Hwin & Hsp & _ & _ & _ & Rout & Hh0 & _ & Hin & Hhb & Hhe & _ & HOK & _ & _ & _ & _ & _ & _ & _).
pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
ho_cls.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & Hbceil & _).
split; [exact HP|].
split.
{ destruct HM as (_ & Hfrs & EFA & Hperm & HK & HG2 & HFL & HL2 & Hk2).
  split; [exact HJ'|]. split; [exact Hfrs|]. split; [exact EFA|]. split; [exact Hperm|].
  split.
  - destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
    split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha Hns Hnt. rewrite (HE a ltac:(lia)); [apply K1; assumption|].
      intros [[Hn Ho] | Hs]; [apply Hnt; right; split; assumption | apply Hns; lia].
    + intros b m i Hbi Hi Hnt. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hbi) as (_ & Hb4 & Hbc & _).
      rewrite (HE (b + i) ltac:(lia)); [exact (K2 b m i Hbi Hi Hnt)|].
      intros [[Hn Ho] | Hs]; [apply Hnt; right; split; assumption | lia].
    + intros a Ha Hown Herr. pose proof (pa_segs_low a Ha) as Hlow.
      rewrite (HE a ltac:(unfold kLowMemEnd in Hlow; lia)); [apply K3; assumption|].
      intros [[Hn Ho] | Hs]; [exact (proj1 (proj2 (Hob Hn)) a Ho Ha) | unfold kLowMemEnd in Hlow; lia].
    + intros cid pos a Hfi Hr Hnt. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hfi) as (Hf4 & Hfc & _).
      assert (Hbr : 0 <= a < YM05.alloc_ceiling).
      { unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr; cbn [fst snd] in Hr.
        assert (0 <= frame_addr (c_lyc c) cid pos / 8 <= frame_addr (c_lyc c) cid pos) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        assert (0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
        destruct Hr; lia. }
      rewrite (HE a ltac:(lia)); [exact (K4 cid pos a Hfi Hr Hnt)|].
      intros [[Hn Ho] | Hs]; [apply Hnt; right; split; assumption | lia].
    + intros a Ha Hns Hp. apply HA. apply K5; assumption.
    + intros a Ha. apply HA. apply K6. exact Ha.
  - split; [|split; [|exact (conj HL2 Hk2)]].
    2: { rewrite <- HFL. apply ho_rdword_ext. intros k Hk. rewrite <- HFe. apply HE; [lia|].
         intros [[Hn Ho] | Hs]; [destruct (proj1 (Hob Hn)); lia | lia]. }
    apply (ho_garr_kept W2 W2 mem mem'); [|exact HG2].
    intros i Hi. rewrite length_map, HL2 in Hi. destruct HOK as (HLH & _). rewrite HLH in Hi.
    apply HE; [lia|]. intros [[Hn Ho] | Hs]; [destruct (proj1 (proj2 (proj2 (proj2 (Hob Hn))))); lia | lia]. }
split; [exact HS1|]. split; [exact HFe|]. split; [exact HR'|].
intros j Hj. apply (ho_vm_kept W2 mem mem'); [|exact (HSV j Hj)].
intros k Hk. apply HE; [lia|].
intros [[Hn Ho] | Hs]; [destruct (proj1 (proj2 (proj2 (Hob Hn)))); lia | lia].
Qed.

Lemma ho_fsh_step : forall c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F mem' SH,
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ hoW c a -> aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem a) ->
  ho_fsh W2 mem F SH -> ho_fsh W2 mem' F SH.
Proof.
intros c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F mem' SH HB HE HS i Hi.
pose proof (ho_out_loc c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as Hob.
destruct (ho_Fb c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as (Hf4 & Hfc & _ & _ & _ & _ & Hst & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (0 <= F / 8 <= F) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
rewrite HE; [exact (HS i Hi) | unfold SB; lia |].
intros [[Hn Ho] | Hs]; [|unfold SB in *; lia].
destruct (Hob Hn) as (_ & _ & _ & _ & Ham & _).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SB in *. lia.
Qed.

Lemma ho_garrF_step : forall c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F mem' o l,
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ hoW c a -> aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem a) ->
  0 <= o -> o + Z.of_nat (length l) <= 128 ->
  garr8 SEGS (mrestrict (w_H W2) mem) (F + o) l -> garr8 SEGS (mrestrict (w_H W2) mem') (F + o) l.
Proof.
intros c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F mem' o l HB HE Ho0 Ho1 HG.
pose proof (ho_out_loc c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as Hob.
destruct (ho_Fb c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as (Hf4 & Hfc & _ & _ & _ & _ & Hst & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (ho_garr_kept W2 W2 mem mem'); [|exact HG].
intros i Hi. apply HE; [lia|].
intros [[Hn Ho] | Hs]; [destruct (proj1 (Hob Hn)); lia | lia].
Qed.

Lemma ho_snez : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff n 0)) = Z_to_bv 64 (if v =? 0 then 0 else 1).
Proof.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r, zalu64_sound by lia.
unfold zalu64, zalu_raw, zcanon, M64. rewrite (Z.mod_small 0), (Z.mod_small v) by lia. f_equal.
destruct (Z.eqb_spec v 0) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec 0 v); [reflexivity | lia].
Qed.
Ltac rget HS r X :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as X;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in X;
    cbn [ms_regs restrict] in X
  end.

Lemma ho_awr_tr : forall STK sp0 FP bl0 blc blc' ly ly' own x a,
  (forall p, In p blc -> In p blc') -> (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc' ly' (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own x a Hincl EFA [H|[H|[H|H]]].
- left; exact H.
- right; left. destruct H as (Hfp & b & n & Hin & Hr). split; [exact Hfp|]. exists b, n. split; [apply Hincl; exact Hin | exact Hr].
- right; right; left. destruct H as (b & n & Hin & Hnin & Hr). exists b, n. split; [apply Hincl; exact Hin|]. split; assumption.
- right; right; right. destruct H as (cid & pos & Hin & Hr). exists cid, pos. split; [right; exact Hin|]. rewrite !EFA. exact Hr.
Qed.

Lemma ho_ra_ext : forall (rd rd' : Z -> option Z) b a n,
  (forall s, rd' s = rd s) -> range_addressable rd b a n -> range_addressable rd' b a n.
Proof. intros rd rd' b a n HE HR x Hx. rewrite HE. exact (HR x Hx). Qed.

Lemma ho_hull_ext : forall (rd rd' : Z -> option Z) a n,
  (forall s, rd' s = rd s) -> shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof. intros rd rd' a n HE HR s Hs. rewrite HE. exact (HR s Hs). Qed.

Lemma ho_denot_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by lia. reflexivity. Qed.

Lemma ho_garr_some : forall (Wx : world SEGS) m b l i, garr8 SEGS (mrestrict (w_H Wx) m) b l ->
  0 <= i < Z.of_nat (length l) -> aview SEGS (w_H Wx) m (b + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros Wx m b l i HG Hi. destruct (HG (Z.to_nat i) ltac:(lia)) as [Hv Hr].
pose proof (Hv 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z2Nat.id, Z.add_0_r in X by lia.
unfold aview. rewrite X. cbn [option_map]. f_equal.
unfold YO0f.le_byte. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
rewrite !Z.mod_small; lia.
Qed.

Lemma ho_out_ok : forall c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F,
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F -> c_out c <> 0 ->
  range_addressable (aview SEGS (w_H W2) mem) SHADOW_OFF (c_out c) 24 /\ shadow_hull_vis (aview SEGS (w_H W2) mem) (c_out c) 24 /\
  (forall a, c_out c <= a < c_out c + 24 ->
     awr_byte (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c)) (ablocks B ly2 S2) ly2 ((1, fpos) :: c_own c) a).
Proof.
intros c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB Hn.
pose proof (ho_out_loc c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB Hn) as (_ & _ & _ & _ & Ham & _).
destruct HB as (HP & HM & HS1 & HFe & HR & HSV).
pose proof HP as ((mdc & HJc) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rout & Hh0 & _ & Hin & Hhb & Hhe & _ & _ & _ & _ & _ & Hout & _ & _ & _).
pose proof HJc as (HARc & _).
destruct HM as (HJ2 & Hfrs & EFA & Hperm & HK & _).
pose proof HJ2 as (HAR2 & _).
destruct (Hout Hn) as ((Hm8 & H63 & _ & Hwo & _ & Hra & Hhv & Hawr & _ & _ & Hloc) & Hoh & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hincl : forall p, In p (ablocks B (c_lyc c) (c_Sc c)) -> In p (ablocks B ly2 S2))
  by (intros p Hp; apply (Permutation_in _ (Permutation_sym Hperm)); exact Hp).
split; [|split].
- destruct Hloc as [(cid & pos & Hfi & Hf1 & Hf2) | (b & m & Hbi & Hb1 & Hb2)].
  + destruct HK as (_ & _ & _ & K4 & _).
    destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HARc Hfi) as (Hfal & _).
    destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HARc Hfi) as (_ & Hb64 & Hb64').
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & _ & Happ & _).
    intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    unfold shadow_of_addr in *.
    rewrite (K4 cid pos (SHADOW_OFF + x / 8) Hfi); [exact Hs| |].
    * right. unfold in_zr, shadow_addr. cbn [fst snd].
      set (F' := frame_addr (c_lyc c) cid pos) in *.
      assert (F' / 8 <= x / 8) by (apply Z.div_le_mono; lia).
      assert (x / 8 < F' / 8 + fs_frame_bytes cid / 8).
      { replace F' with (8 * (F' / 8)) in Hf2 by (pose proof (Z.div_mod F' 8 ltac:(lia)); lia).
        replace (fs_frame_bytes cid) with (8 * (fs_frame_bytes cid / 8)) in Hf2 by (pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)); lia).
        apply Z.div_lt_upper_bound; lia. }
      lia.
    * unfold tho_wr. unfold in_app, amem_range, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, SHADOW_OFF in *.
      assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      lia.
  + assert (Hb' : In (b, m) (ablocks B ly2 S2)) by (apply Hincl; exact Hbi).
    exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem md b m (c_out c) 24 HAR2 Hb' Hb1 Hb2).
- destruct Hloc as [(cid & pos & Hfi & Hf1 & Hf2) | (b & m & Hbi & Hb1 & Hb2)].
  + assert (Hfi' : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hfi).
    apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 mem md cid pos (c_out c) 24 HAR2 Hfi'); try rewrite EFA; lia.
  + assert (Hb' : In (b, m) (ablocks B ly2 S2)) by (apply Hincl; exact Hbi).
    apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem md b m (c_out c) 24 HAR2 Hb' Hb1 Hb2). lia.
- intros a Ha. apply (ho_awr_tr _ _ _ _ _ _ _ _ _ _ a Hincl EFA). exact (proj1 (Hawr a Ha)).
Qed.

Lemma ho_G_ok : forall c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F,
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F -> ho_fsh W2 mem F ho_shC ->
  range_addressable (aview SEGS (w_H W2) mem) SHADOW_OFF (F + 32) 24 /\ shadow_hull_vis (aview SEGS (w_H W2) mem) (F + 32) 24 /\
  amem_range (F + 32) 24.
Proof.
intros c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB Hfsh.
destruct (ho_Fb c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as (Hf4 & Hfc & Hf32 & Happ & Hfin & HF2 & _).
destruct HB as (HP & HM & _). destruct HM as (HJ2 & _). pose proof HJ2 as (HAR2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split].
- intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  assert (Hq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
  assert (Hi : 4 <= x / 8 - F / 8 <= 6).
  { rewrite Hq in Hx |- *. replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. rewrite Z.div_mul by lia.
    split; [apply Z.le_add_le_sub_l; apply Z.div_le_lower_bound; lia | apply Z.le_sub_le_add_l; apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]. }
  replace (SB + x / 8) with (SB + F / 8 + (x / 8 - F / 8)) by lia.
  rewrite (Hfsh (x / 8 - F / 8) ltac:(lia)).
  destruct (Z.eq_dec (x / 8 - F / 8) 4) as [-> | N4]; [reflexivity|].
  destruct (Z.eq_dec (x / 8 - F / 8) 5) as [-> | N5]; [reflexivity|].
  replace (x / 8 - F / 8) with 6 by lia. reflexivity.
- apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 mem md 1 fpos (F + 32) 24 HAR2 Hfin); try rewrite HF2; [lia | change (fs_frame_bytes 1) with 128; lia | lia].
- unfold in_app, amem_range, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.

Lemma ho_frame_av : forall E rs (Wx : world SEGS) ma mb, frame_of E rs (mrestrict (w_H Wx) ma) (mrestrict (w_H Wx) mb) ->
  (forall a, ~ in_wrange E rs a) -> forall a, aview SEGS (w_H Wx) mb a = aview SEGS (w_H Wx) ma a.
Proof. intros E rs Wx ma mb HF Hn a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a) (Hn _)). reflexivity. Qed.
Ltac rgetc HS r X :=
  lazymatch type of HS with
  | st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H E ss ms r HS) as X;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in X;
    cbn [ms_regs restrict] in X
  end.

Lemma ho_denot_reg : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Ltac csv := unfold acallee_saved; vm_compute;
  first [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
        | right; right; right; left; reflexivity | right; right; right; right; left; reflexivity
        | right; right; right; right; right; split; discriminate ].

Definition hoF_env (regs : bvmap 5 word) (T' : list byte) : env := Eimg (Ereg regs [Z_to_bv 64 (disco_table_c.n_of T')]).
Definition hoF_sr : list sv := Eval vm_compute in
  sr_set (sr_set sr_atoms 21%bv (SOff 22 384)) 24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 384) (SLit 3)) (SOff 27 0)).
Definition hoF_rs : smem :=
  [YP09.mkRegion (Some 9%nat) 0 32 24 32 []; YP09.mkRegion (Some 22%nat) 0 480 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 32 0))]].
Definition hoF_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (22%nat, mkAF 4096 140737479966720 3); (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 8 0)] [] [].

Lemma ho_sub0 : forall (H2 T' : list byte), H2 = T' ++ skipn 400 H2 -> length T' = 400%nat -> disco_table_c.sub H2 0 400 = T'.
Proof.
intros H2 T' HH LT. unfold disco_table_c.sub. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 400) with 400%nat. cbn [skipn].
rewrite skipn_O. rewrite HH at 1. rewrite firstn_app, <- LT, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

Lemma hoF_enter2 : forall fq c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F T',
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F ->
  getr regs 21 = w64 (c_h c + 384) -> getr regs 24 = w64 (SB + (c_h c + 384) / 8) ->
  hunt_c.hunt_ok H2 -> H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  st_ok_pi (fx := fq) SEGS VAL (hoF_env regs T') (mkSS 0x7270 hoF_sr hoF_rs None hoF_facts)
    (restrict (w_H W2) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + 0x7270)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 27 0) [mkSHE 22 0 480] (hoF_env regs T') (mrestrict (w_H W2) mem).
Proof.
intros fq c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F T' HB R21 R24 HOK2 HH2 LT'.
destruct (ho_Fb c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as (Hf4 & Hfc & Hf32 & Happ & Hfin & HF2 & Hstk & Hsp47 & Hsp1r & Hsp1al & HSTK).
destruct HB as (HP & HM & HS1 & HFe & HR & HSV).
pose proof HP as ((mdc & HJc) & _ & _ & _ & _ & _ & _ & Hwin & Hsp & _ & _ & _ & Rout & Hh0 & Hh8 & Hin & Hhb & Hhe & _ & HOK & _ & _ & _ & _ & _ & _ & _).
destruct HM as (HJ2 & Hfrs & EFA & Hperm & HK & HG2 & HFL & HL2 & Hk2).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin2 : In (c_hb c, c_hn c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (_ & Hb4 & Hbc & Hbapp & _).
destruct (ho_count (mrestrict (w_H W2) mem) (c_h c) H2 HOK2 HG2) as [Hnr HVn].
rewrite (ho_sub0 H2 T' HH2 LT') in Hnr, HVn.
set (E := hoF_env regs T').
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; unfold E, hoF_env; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (disco_table_c.n_of T'))
  by (unfold E, hoF_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E22 : ew E 22 = Z_to_bv 64 (c_h c)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hhr : c_h c + 480 <= YM05.alloc_ceiling) by lia.
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
    repeat (destruct Hz as [<-|Hz];
      [ lazymatch goal with |- _ = sv_denot ?E (sr_get ?sr ?q) =>
          let v := eval vm_compute in (sr_get sr q) in change (sr_get sr q) with v end;
        first
        [ reflexivity
        | lazymatch goal with |- getr _ ?q = sv_denot _ (SOff ?n 0) =>
            cbn [sv_denot]; rewrite (EE n q eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end
        | lazymatch goal with |- getr _ ?q = sv_denot _ (SOff 22 384) =>
            cbn [sv_denot]; rewrite E22, unsigned_lit_small by lia; exact R21 end
        | rewrite R24; rewrite (denot_shx _ 22 27 384 (c_h c) SB E22 E27) by (unfold SB; lia); f_equal; lia ]
      | ]).
    destruct Hz.
  + vm_compute. reflexivity.
  + unfold hoF_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB 22%nat (c_h c) E22) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (c_h c) 384 4 (SOff 32 0) (disco_table_c.n_of T'));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      change (N.to_nat 4) with 4%nat. exact HVn.
  + apply pairwise_disjoint_of_extents. unfold hoF_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat sp1 E9) by lia. rewrite (VB 22%nat (c_h c) E22) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + unfold hoF_facts. split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E22, E27, E32, !unsigned_lit_small by (unfold SB; lia).
    repeat split; try lia.
- unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W2) mem E (SOff 27 0) 22 (c_h c) 480 (c_h c) 0 480).
  + exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem md (c_hb c) (c_hn c) (c_h c) 480 HAR2 Hin2 Hhb Hhe).
  + rewrite (U_atom E 27 SB E27) by (unfold SB; lia). symmetry. exact SB_SHADOW_OFF.
  + apply (U_atom E 22 (c_h c) E22). lia.
  + lia.
  + lia.
  + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma ho_mul48 : forall E n, ew E 32 = Z_to_bv 64 n -> 0 <= n <= 8 ->
  sv_denot E (SMd M_MUL (SOff 32 0) (SLit 48)) = Z_to_bv 64 (48 * n).
Proof.
intros E n H1 H2. cbn [sv_denot]. rewrite H1, unsigned_lit_small, Z.add_0_r, zmd64_sound by lia.
unfold zmd64, zcanon, M64. cbn [zmd_raw]. rewrite (Z.mod_small n), (Z.mod_small 48) by lia.
rewrite Z.mod_small by lia. f_equal. lia.
Qed.
Lemma ho_br_ge : forall E n, ew E 32 = Z_to_bv 64 n -> 0 <= n <= 8 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff 32 0)) = negb (0 <? n).
Proof.
intros E n H1 H2. cbn [branch_taken sv_denot]. rewrite H1, unsigned_lit_small, Z.add_0_r by lia.
rewrite bv_lts_small by lia. reflexivity.
Qed.
Lemma ho_br_lt : forall E n, ew E 32 = Z_to_bv 64 n -> 0 <= n <= 8 ->
  branch_taken BC_LT (sv_denot E (SLit 0)) (sv_denot E (SOff 32 0)) = (0 <? n).
Proof.
intros E n H1 H2. cbn [branch_taken sv_denot]. rewrite H1, unsigned_lit_small, Z.add_0_r by lia.
rewrite bv_lts_small by lia. reflexivity.
Qed.

Lemma ho_seg_F : ho_seg_G_stmt B -> ho_seg_T_stmt B -> ho_seg_F_stmt B.
Proof.
intros SG ST c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G ret HB R10 Rret R19 R21 R24 R23 R25 Hfsh HOK2 HH2 LT' HGg LG Hobs Hcm HGs Hsk Hout.
pose proof (paj_run (fx := c_fq c) B LAWS) as RUN.
pose proof (paj_run_to (fx := c_fq c) B LAWS) as RUNTO.
pose proof (paj_branch (fx := c_fq c) (PI := PI)) as BR.
pose proof HB as (HP & HM & HS1 & HFe & HR & HSV).
pose proof HM as (HJ & Hfrs & EFA & Hperm & HK & HG2 & HFL & HL2 & Hk2).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R26 & R27).
set (E := Eimg (Ereg regs2 [])).
assert (HEI : img_env VAL A_LIM E) by (apply Eimg_env).
assert (HS : st_ok_pi (fx := c_fq c) SEGS VAL E (mkSS 0x7258 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 0x7258)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold E. apply (regs_ok_agree 32 (Ereg regs2 []));
    [split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity] | vm_compute; reflexivity | apply regs_ok_Ereg].
  - vm_compute; reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - repeat split; constructor. }
assert (SHOK : sh_ok SEGS HOx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
unfold ho_cfg.
paj_run_tok RUN HS HJ SHOK HOspan.
{ apply awr_ok_nil. }
rename HFr into FR1, HG into FG1. clear HF.
assert (HAG : env_agree 32 (Ereg regs2 []) E) by (unfold E; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof HP as ((mdc & HJc) & HROD & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin & Hsp & Hdep & Rlen & Rnow & Rout & Hh0 & Hh8 & Hin & Hhb & Hhe & Hwr & HOK & LFB & HGH & Hf50 & HoutP & HKM & HKT & Hch).
destruct (ho_Fb c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB) as (Hf4 & Hfc & Hf32 & Happ & Hfin & HF2 & Hstk & Hsp47 & Hsp1r & Hsp1al & HSTK).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
psrr_branch_tok RUN BR HS SHOK HOspan.
- assert (Hout0 : c_out c = 0).
  { rewrite branch_eq_U, U_lit in Hc by lia. rewrite (U_atom E 19 (c_out c)) in Hc; [lia | | lia].
    rewrite (EE 19%nat 19%bv eq_refl). exact R19. }
  paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x71a0.
  { apply awr_ok_nil. }
  rename HFr into FR2, HG into FG2. clear HF.
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi E _ _ regs2 [] [2; 3; 4; 8; 9; 18; 22; 25; 26; 27]%bv HS HAG eq_refl) as RK.
  cbn [ms_regs restrict] in RK.
  rget HS (20%bv : bv 5) R20.
  rewrite (ho_snez E 10 ret ltac:(rewrite (EE 10%nat 10%bv eq_refl); exact R10) Rret) in R20.
  eapply (ST c fpos ly2 S2 W2 (ms_mem ms0) _ k2 (ms_regs ms0) sp1 F H2 (if ret =? 0 then 0 else 1)).
  + apply (ho_step c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ _ _ HB HJ).
    * intros a Ha _.
      rewrite (ho_aview_frame E _ W2 (ms_mem ms) (ms_mem ms0) a FR2 Ha ltac:(intros (rg & Hrg & _); cbn in Hrg; destruct Hrg)).
      exact (ho_aview_frame E _ W2 mem2 (ms_mem ms) a FR1 Ha ltac:(intros (rg & Hrg & _); cbn in Hrg; destruct Hrg)).
    * intros a Ha. exact (ho_apr_grows _ _ _ a FG2 (ho_apr_grows _ _ _ a FG1 Ha)).
    * split; [rewrite (RK 2%bv ltac:(cbn; tauto)); exact R2|].
      split; [rewrite (RK 3%bv ltac:(cbn; tauto)); exact R3|].
      split; [rewrite (RK 4%bv ltac:(cbn; tauto)); exact R4|].
      split; [rewrite (RK 8%bv ltac:(cbn; tauto)); exact R8|].
      split; [rewrite (RK 9%bv ltac:(cbn; tauto)); exact R9|].
      split; [rewrite (RK 18%bv ltac:(cbn; tauto)); exact R18|].
      split; [rewrite (RK 22%bv ltac:(cbn; tauto)); exact R22|].
      split; [rewrite (RK 26%bv ltac:(cbn; tauto)); exact R26|].
      rewrite (RK 27%bv ltac:(cbn; tauto)); exact R27.
  + exact R20.
  + destruct (ret =? 0); [right; left | right; right]; reflexivity.
  + rewrite (RK 25%bv ltac:(cbn; tauto)); exact R25.
  + apply (ho_fsh_step c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ _ HB); [|exact Hfsh].
    intros a Ha _.
    rewrite (ho_aview_frame E _ W2 (ms_mem ms) (ms_mem ms0) a FR2 Ha ltac:(intros (rg & Hrg & _); cbn in Hrg; destruct Hrg)).
    exact (ho_aview_frame E _ W2 mem2 (ms_mem ms) a FR1 Ha ltac:(intros (rg & Hrg & _); cbn in Hrg; destruct Hrg)).
  + exact HOK2.
  + apply (HoFM2.hof_F (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) _ H2 T' G ret _ HOK LFB HOK2 HH2 LT' Hobs Hcm HGs Hsk eq_refl).
    intros Hn. exfalso. exact (Hn Hout0).
- assert (Hon : c_out c <> 0).
  { rewrite branch_eq_U, U_lit in Hc by lia. rewrite (U_atom E 19 (c_out c)) in Hc; [| rewrite (EE 19%nat 19%bv eq_refl); exact R19 | lia].
    apply Z.eqb_neq in Hc. exact Hc. }
  clear Hc.
  pose proof (ho_out_loc c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hon) as (HoF & HoImg & HoSp & HoH & HoAm & HoM8 & Ho63).
  pose proof (ho_out_ok c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hon) as (HoRa & HoHv & HoAwr).
  pose proof (ho_G_ok c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hfsh) as (HGra & HGhv & HGam).
  paj_run_tok RUN HS HJ SHOK HOspan.
  { apply awr_ok_nil. }
  rename HFr into FR2, HG into FG2. clear HF.
  assert (EAV1 : forall a, aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
  { intros a. rewrite (ho_frame_av E _ W2 (ms_mem ms) (ms_mem ms0) FR2 ltac:(intros a' (rg & Hrg & _); cbn in Hrg; destruct Hrg)).
    exact (ho_frame_av E _ W2 mem2 (ms_mem ms) FR1 ltac:(intros a' (rg & Hrg & _); cbn in Hrg; destruct Hrg) a). }
  rgetc HS (10%bv : bv 5) Ra0. rgetc HS (11%bv : bv 5) Ra1. rgetc HS (12%bv : bv 5) Ra2. rgetc HS (1%bv : bv 5) Rra.
  rgetc HS (2%bv : bv 5) Rsp. rgetc HS (3%bv : bv 5) Rgp. rgetc HS (4%bv : bv 5) Rtp.
  rewrite ho_denot_reg, (EE 19%nat 19%bv eq_refl), R19 in Ra0.
  rewrite ho_denot_reg, (EE 23%nat 23%bv eq_refl), R23 in Ra1.
  change (SOff 240 29296) with (SOff A_TEXT 29296) in Rra. rewrite (codeptr_val E 29296 HEI) in Rra.
  cbn [sv_denot] in Ra2.
  rewrite ho_denot_reg, (EE 2%nat 2%bv eq_refl), R2 in Rsp.
  rewrite ho_denot_reg, (EE 3%nat 3%bv eq_refl), R3 in Rgp.
  rewrite ho_denot_reg, (EE 4%nat 4%bv eq_refl), R4 in Rtp.
  rgetc HS (20%bv : bv 5) Rs4. rewrite (ho_snez E 10 ret ltac:(rewrite (EE 10%nat 10%bv eq_refl); exact R10) Rret) in Rs4.
  rgetc HS (8%bv : bv 5) Rc8. rewrite ho_denot_reg, (EE 8%nat 8%bv eq_refl), R8 in Rc8.
  rgetc HS (9%bv : bv 5) Rc9. rewrite ho_denot_reg, (EE 9%nat 9%bv eq_refl), R9 in Rc9.
  rgetc HS (18%bv : bv 5) Rc18. rewrite ho_denot_reg, (EE 18%nat 18%bv eq_refl), R18 in Rc18.
  rgetc HS (19%bv : bv 5) Rc19. rewrite ho_denot_reg, (EE 19%nat 19%bv eq_refl), R19 in Rc19.
  rgetc HS (21%bv : bv 5) Rc21. rewrite ho_denot_reg, (EE 21%nat 21%bv eq_refl), R21 in Rc21.
  rgetc HS (22%bv : bv 5) Rc22. rewrite ho_denot_reg, (EE 22%nat 22%bv eq_refl), R22 in Rc22.
  rgetc HS (23%bv : bv 5) Rc23. rewrite ho_denot_reg, (EE 23%nat 23%bv eq_refl), R23 in Rc23.
  rgetc HS (24%bv : bv 5) Rc24. rewrite ho_denot_reg, (EE 24%nat 24%bv eq_refl), R24 in Rc24.
  rgetc HS (25%bv : bv 5) Rc25. rewrite ho_denot_reg, (EE 25%nat 25%bv eq_refl), R25 in Rc25.
  rgetc HS (26%bv : bv 5) Rc26. rewrite ho_denot_reg, (EE 26%nat 26%bv eq_refl), R26 in Rc26.
  rgetc HS (27%bv : bv 5) Rc27. rewrite ho_denot_reg, (EE 27%nat 27%bv eq_refl), R27 in Rc27.
  rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc setpc].
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA DS___asan_memcpy) (AMEMCPY (c_fq c)) W2 (ms_regs ms0) (ms_mem ms0)
      (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c) ((1, fpos) :: c_own c) ly2 S2 _ k2
      (c_out c) (F + 32) 24 (sp1 - c_sp0 c) (Z_to_bv 64 (BASE + 0x7270)) HJ).
    + exact Ra0.
    + exact Ra1.
    + exact Ra2.
    + lia.
    + lia.
    + exact Ho63.
    + unfold spZ at 1. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + clear - Hsp1al Hsp0al. lia.
    + lia.
    + unfold ESTACK. lia.
    + exact Rgp.
    + exact Rtp.
    + exact Rra.
    + apply ret_ok_codeptr_v; [lia | reflexivity].
    + intros a Ha. split; [exact (HoAwr a Ha) | unfold ESTACK; destruct HoSp; lia].
    + exact HoAm.
    + apply (ho_ra_ext _ _ _ _ _ EAV1). exact HoRa.
    + intros _. apply (ho_hull_ext _ _ _ _ EAV1). exact HoHv.
    + split; [lia|]. split; [lia|]. split.
      * intros a Ha. split.
        -- rewrite EAV1. replace a with (F + 32 + (a - (F + 32))) by lia.
           rewrite (ho_garr_some W2 mem2 (F + 32) _ (a - (F + 32)) HGg ltac:(rewrite length_map, LG; lia)). discriminate.
        -- unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
      * split; [lia|]. split; [exact HGam|]. split; [apply (ho_ra_ext _ _ _ _ _ EAV1); exact HGra|].
        intros _. apply (ho_hull_ext _ _ _ _ EAV1). exact HGhv. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff & Hfr3 & Hpres3 & HSM3).
  assert (RC : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms0) r).
  { intros r Hr. pose proof (HP3 (bv_unsigned r) Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X. }
  assert (Q2 : getr regs3 2 = w64 sp1) by (rewrite (RC 2%bv ltac:(csv)); exact Rsp).
  assert (Q3 : getr regs3 3 = w64 (as_gp B)) by (rewrite (RC 3%bv ltac:(csv)); exact Rgp).
  assert (Q4 : getr regs3 4 = w64 (as_tp B)) by (rewrite (RC 4%bv ltac:(csv)); exact Rtp).
  assert (Q8 : getr regs3 8 = w64 (spZ (c_regs c))) by (rewrite (RC 8%bv ltac:(csv)); exact Rc8).
  assert (Q9 : getr regs3 9 = w64 sp1) by (rewrite (RC 9%bv ltac:(csv)); exact Rc9).
  assert (Q18 : getr regs3 18 = w64 F) by (rewrite (RC 18%bv ltac:(csv)); exact Rc18).
  assert (Q19 : getr regs3 19 = w64 (c_out c)) by (rewrite (RC 19%bv ltac:(csv)); exact Rc19).
  assert (Q20 : getr regs3 20 = Z_to_bv 64 (if ret =? 0 then 0 else 1)) by (rewrite (RC 20%bv ltac:(csv)); exact Rs4).
  assert (Q21 : getr regs3 21 = w64 (c_h c + 384)) by (rewrite (RC 21%bv ltac:(csv)); exact Rc21).
  assert (Q22 : getr regs3 22 = w64 (c_h c)) by (rewrite (RC 22%bv ltac:(csv)); exact Rc22).
  assert (Q23 : getr regs3 23 = w64 (F + 32)) by (rewrite (RC 23%bv ltac:(csv)); exact Rc23).
  assert (Q24 : getr regs3 24 = w64 (SB + (c_h c + 384) / 8)) by (rewrite (RC 24%bv ltac:(csv)); exact Rc24).
  assert (Q25 : getr regs3 25 = w64 (SB + F / 8)) by (rewrite (RC 25%bv ltac:(csv)); exact Rc25).
  assert (Q26 : getr regs3 26 = w64 F) by (rewrite (RC 26%bv ltac:(csv)); exact Rc26).
  assert (Q27 : getr regs3 27 = w64 SB) by (rewrite (RC 27%bv ltac:(csv)); exact Rc27).
  assert (HE3 : forall a, 0 <= a < 2 ^ 64 -> ~ hoW c a -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hn. rewrite (Hfr3 a Ha); [exact (EAV1 a)| |].
    - intros Ho. apply Hn. left. split; [exact Hon | exact Ho].
    - intros Hs. apply Hn. right. unfold ESTACK in Hs. lia. }
  assert (HA3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a)
    by (intros a Ha; exact (Hpres3 a (ho_apr_grows _ _ _ a FG2 (ho_apr_grows _ _ _ a FG1 Ha)))).
  assert (HB3 : ho_base B c fpos ly2 S2 W2 mem3 md3 k2 H2 regs3 sp1 F).
  { apply (ho_step c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 HB HJ3 HE3 HA3).
    split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q8|]. split; [exact Q9|].
    split; [exact Q18|]. split; [exact Q22|]. split; [exact Q26 | exact Q27]. }
  destruct (hoF_enter2 (c_fq c) c fpos ly2 S2 W2 mem3 md3 k2 H2 regs3 sp1 F T' HB3 Q21 Q24 HOK2 HH2 LT') as [HS3 SHOK3].
  assert (HEI3 : img_env VAL A_LIM (hoF_env regs3 T')) by apply Eimg_env.
  clear HS SHOK.
  paj_run_tok RUN HS3 HJ3 SHOK3 HOspan.
  { eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - c_sp0 c);
    [reflexivity | unfold hoF_env; rewrite ew_Eimg_Ereg_nat with (r := 9%bv) by reflexivity; rewrite Q9; unfold w64; rewrite unsigned_lit_small by lia; lia
    | cbn; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rename HFr into FR3, HG into FG3. clear HF.
  destruct (ho_count (mrestrict (w_H W2) mem2) (c_h c) H2 HOK2 HG2) as [Hnr _].
  rewrite (ho_sub0 H2 T' HH2 LT') in Hnr.
  assert (E32' : ew (hoF_env regs3 T') 32 = Z_to_bv 64 (disco_table_c.n_of T'))
    by (unfold hoF_env; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (U9 : bv_unsigned (ew (hoF_env regs3 T') 9) = sp1)
    by (unfold hoF_env; rewrite ew_Eimg_Ereg_nat with (r := 9%bv) by reflexivity; rewrite Q9; unfold w64; apply unsigned_lit_small; lia).
  assert (HAG3 : env_agree 32 (Ereg regs3 [Z_to_bv 64 (disco_table_c.n_of T')]) (hoF_env regs3 T'))
    by (unfold hoF_env; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Hgo : forall i, 0 <= i < 24 -> ~ (sp1 + 24 <= c_out c + i < sp1 + 32)) by (intros i Hi; destruct HoSp; lia).
  psrr_branch_tok RUN BR HS3 SHOK3 HOspan.
  + rewrite (ho_br_ge _ (disco_table_c.n_of T') E32' Hnr) in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS3 HJ3 SHOK3 HOspan 0x71a0.
    { eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - c_sp0 c); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
      apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
    rename HFr into FR4, HG into FG4. clear HF.
    assert (NW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 32) -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem3 a).
    { intros a Ha0 Ha. rewrite (ho_aview_frame _ _ W2 (ms_mem ms1) (ms_mem ms2) a FR4 Ha0); [|intros (rg & Hrg & Hr); cbn in Hrg; destruct Hrg as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U9 in Hr|]; lia].
      apply (ho_aview_frame _ _ W2 mem3 (ms_mem ms1) a FR3 Ha0). intros (rg & Hrg & Hr). cbn in Hrg. destruct Hrg as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U9 in Hr|]; lia. }
    pmkst HS3.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ [2; 3; 4; 8; 9; 18; 20; 22; 23; 25; 26; 27]%bv HS3 HAG3 eq_refl) as RK.
    cbn [ms_regs restrict] in RK.
    assert (HEf : forall a, 0 <= a < 2 ^ 64 -> ~ hoW c a -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha Hn. rewrite (NW a Ha); [exact (HE3 a Ha Hn)|]. intros Hs. apply Hn. right. lia. }
    assert (HAf : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
      by (intros a Ha; exact (ho_apr_grows _ _ _ a FG4 (ho_apr_grows _ _ _ a FG3 (HA3 a Ha)))).
    assert (HRf : ho_regs_mid B c (ms_regs ms2) sp1 F).
    { split; [rewrite (RK 2%bv ltac:(cbn; tauto)); exact Q2|].
      split; [rewrite (RK 3%bv ltac:(cbn; tauto)); exact Q3|].
      split; [rewrite (RK 4%bv ltac:(cbn; tauto)); exact Q4|].
      split; [rewrite (RK 8%bv ltac:(cbn; tauto)); exact Q8|].
      split; [rewrite (RK 9%bv ltac:(cbn; tauto)); exact Q9|].
      split; [rewrite (RK 18%bv ltac:(cbn; tauto)); exact Q18|].
      split; [rewrite (RK 22%bv ltac:(cbn; tauto)); exact Q22|].
      split; [rewrite (RK 26%bv ltac:(cbn; tauto)); exact Q26|].
      rewrite (RK 27%bv ltac:(cbn; tauto)). exact Q27. }
    assert (HGout : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms2)) (c_out c) (map (fun b : byte => bv_unsigned b) G)).
    { apply (ho_garr_moved W2 mem2 (ms_mem ms2) (c_out c) (F + 32)); [|exact HGg].
      intros i Hi. rewrite length_map, LG in Hi.
      rewrite (NW (c_out c + i) ltac:(lia) (Hgo i ltac:(lia))). rewrite (Heff i ltac:(lia)). exact (EAV1 (F + 32 + i)). }
    eapply (ST c fpos ly2 S2 W2 (ms_mem ms2) _ k2 (ms_regs ms2) sp1 F H2 (if ret =? 0 then 0 else 1)).
    * exact (ho_step c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ _ _ HB HJ3 HEf HAf HRf).
    * rewrite (RK 20%bv ltac:(cbn; tauto)). exact Q20.
    * destruct (ret =? 0); [right; left | right; right]; reflexivity.
    * rewrite (RK 25%bv ltac:(cbn; tauto)). exact Q25.
    * exact (ho_fsh_step c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ _ HB HEf Hfsh).
    * exact HOK2.
    * apply (HoFM2.hof_F (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) _ H2 T' G ret _ HOK LFB HOK2 HH2 LT' Hobs Hcm HGs Hsk eq_refl).
      intros _. exists G. split; [apply HoFM2.hof_ans0; exact Hc | exact HGout].
  + rewrite (ho_br_ge _ (disco_table_c.n_of T') E32' Hnr) in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS3 HJ3 SHOK3 HOspan 0x7294.
    { eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - c_sp0 c); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
      apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
    rename HFr into FR4, HG into FG4. clear HF.
    assert (NW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 24 <= a < sp1 + 32) -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem3 a).
    { intros a Ha0 Ha. rewrite (ho_aview_frame _ _ W2 (ms_mem ms1) (ms_mem ms2) a FR4 Ha0); [|intros (rg & Hrg & Hr); cbn in Hrg; destruct Hrg as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U9 in Hr|]; lia].
      apply (ho_aview_frame _ _ W2 mem3 (ms_mem ms1) a FR3 Ha0). intros (rg & Hrg & Hr). cbn in Hrg. destruct Hrg as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U9 in Hr|]; lia. }
    pmkst HS3.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ [2; 3; 4; 8; 9; 18; 20; 22; 23; 25; 26; 27]%bv HS3 HAG3 eq_refl) as RK.
    cbn [ms_regs restrict] in RK.
    assert (HEf : forall a, 0 <= a < 2 ^ 64 -> ~ hoW c a -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha Hn. rewrite (NW a Ha); [exact (HE3 a Ha Hn)|]. intros Hs. apply Hn. right. lia. }
    assert (HAf : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a)
      by (intros a Ha; exact (ho_apr_grows _ _ _ a FG4 (ho_apr_grows _ _ _ a FG3 (HA3 a Ha)))).
    assert (HRf : ho_regs_mid B c (ms_regs ms2) sp1 F).
    { split; [rewrite (RK 2%bv ltac:(cbn; tauto)); exact Q2|].
      split; [rewrite (RK 3%bv ltac:(cbn; tauto)); exact Q3|].
      split; [rewrite (RK 4%bv ltac:(cbn; tauto)); exact Q4|].
      split; [rewrite (RK 8%bv ltac:(cbn; tauto)); exact Q8|].
      split; [rewrite (RK 9%bv ltac:(cbn; tauto)); exact Q9|].
      split; [rewrite (RK 18%bv ltac:(cbn; tauto)); exact Q18|].
      split; [rewrite (RK 22%bv ltac:(cbn; tauto)); exact Q22|].
      split; [rewrite (RK 26%bv ltac:(cbn; tauto)); exact Q26|].
      rewrite (RK 27%bv ltac:(cbn; tauto)). exact Q27. }
    assert (HGout : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms2)) (c_out c) (map (fun b : byte => bv_unsigned b) G)).
    { apply (ho_garr_moved W2 mem2 (ms_mem ms2) (c_out c) (F + 32)); [|exact HGg].
      intros i Hi. rewrite length_map, LG in Hi.
      rewrite (NW (c_out c + i) ltac:(lia) (Hgo i ltac:(lia))). rewrite (Heff i ltac:(lia)). exact (EAV1 (F + 32 + i)). }
    rget HS3 (19%bv : bv 5) R19f. rewrite (ho_mul48 _ (disco_table_c.n_of T') E32' Hnr) in R19f.
    rget HS3 (24%bv : bv 5) R24f. cbn [sv_denot] in R24f.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS3 eq_refl) as HRg. cbn [ms_mem restrict] in HRg.
    pose proof (field_of_region _ _ 9 sp1 _ 0 32 24 32 24 8 (SOff 19 0) (c_out c) HRg U9 ltac:(left; reflexivity)
      ltac:(rewrite ho_denot_reg; unfold hoF_env; rewrite ew_Eimg_Ereg_nat with (r := 19%bv) by reflexivity; exact Q19)
      ltac:(cbn; lia) ltac:(cbn; lia)) as Vout.
    eapply (SG c fpos ly2 S2 W2 (ms_mem ms2) _ k2 (ms_regs ms2) sp1 F H2 T' G (if ret =? 0 then 0 else 1) (disco_table_c.n_of T') 0).
    * exact (ho_step c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ _ _ HB HJ3 HEf HAf HRf).
    * rewrite (RK 20%bv ltac:(cbn; tauto)). exact Q20.
    * destruct (ret =? 0); [left | right]; reflexivity.
    * exact R19f.
    * exact R24f.
    * rewrite (RK 23%bv ltac:(cbn; tauto)). exact Q23.
    * rewrite (RK 25%bv ltac:(cbn; tauto)). exact Q25.
    * exact (ho_fsh_step c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ _ HB HEf Hfsh).
    * exact HOK2.
    * exact HH2.
    * exact LT'.
    * reflexivity.
    * lia.
    * exact Hnr.
    * exact (ho_garrF_step c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ 32 _ HB HEf ltac:(lia) ltac:(rewrite length_map, LG; lia) HGg).
    * exact LG.
    * intros j Hj. lia.
    * exact Hon.
    * exact (rdword_of_val_mem SEGS (w_H W2) (ms_mem ms2) (sp1 + 24) (c_out c) Vout ltac:(lia)).
    * exact HGout.
    * intros A HA _.
      apply (HoFM2.hof_F (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) _ H2 T' G ret _ HOK LFB HOK2 HH2 LT' Hobs Hcm HGs Hsk eq_refl).
      intros _. exists A. split; [exact HA | reflexivity].
Qed.

End h.
End f.
End d.
