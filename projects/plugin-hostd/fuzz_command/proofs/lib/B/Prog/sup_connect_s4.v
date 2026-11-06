(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the tail of sup_connect's walk on fuzz_command.asan-ubsan (image B, 0x8b45c):
   from the return point of the last arg_s call (BASE + SCB_R5 = 0x8b4c0) through the epilogue to the tail jump
   into answer (0x8b4ec), and answer's contract to sup_connect's post (sup_connect_s0.v SCB_T_stmt). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaLibG PaCall CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c arg_line_c answer_c sup_connect_c RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaLibH PaCallPg RecBridge CmdRecBase CmdRecRo sup_connect_s0.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* answer's contract keeps the recorder's blocks that start at the old answer with stdpp's list filter *)
Lemma scb4_filter_sub : forall (P : Z * Z -> Prop) (D : forall x, Decision (P x)) (l : list (Z * Z)) x,
  In x (filter P l) -> In x l.
Proof.
intros P D l x. induction l as [|y l IH]; intros H; [exact H|].
cbn in H.
lazymatch type of H with
| context [if ?d then _ else _] => destruct d
end.
- destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)].
- right. exact (IH H).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run whose only region is read-only writes nothing: every byte reads as before *)
Lemma scb4_ro_keeps : forall E (H : word -> bool) (m m' : word -> option byte) a,
frame_of E scb_regs_m (mrestrict H m) (mrestrict H m') -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E H m m' a Hfr. unfold aview, mbyte. rewrite (Hfr (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Ha). destruct Hr as [<- | []]. cbn [scb_stack_m YP09.r_wlo YP09.r_whi] in Ha. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.

(* the shape "resp 0" is one of CmdRo's objects *)
Lemma scb4_lit_in : In (0x21d20, RO_lit_21d20) cmd_ro_list.
Proof. unfold cmd_ro_list. repeat (first [left; reflexivity | right]). Qed.

(* two live blocks with one start are one block *)
Lemma scb4_start_uniq : forall ly S (W : world SEGS) mem md p n m,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (p, m) (ablocks B ly S) -> n = m.
Proof.
intros ly S W mem md p n m HAR H1 H2.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR H1) as (_ & _ & _ & _ & _ & HP & _).
assert (HN : forall q k, In (q, k) (ablocks B ly S) -> 1 <= req_size k).
{ intros q k Hq. pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hq) as (_ & _ & _ & _ & _ & _ & Hk).
  unfold req_size. destruct (Z.eqb_spec k 0); lia. }
revert HP H1 H2 HN. generalize (ablocks B ly S) as l.
induction l as [|x tl IH]; intros HP H1 H2 HN; [destruct H1|].
cbn [map] in HP. destruct HP as [HF HP].
assert (HF' : forall y, In y tl -> zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y))).
{ intros y Hy. first [rewrite Forall_forall in HF | idtac].
  apply (HF (fst y, req_size (snd y))). apply in_map_iff. exists y. split; [reflexivity | exact Hy]. }
destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
- subst x. injection E2 as E2. exact E2.
- subst x. exfalso. specialize (HF' _ H2). unfold zdisjoint in HF'. cbn [fst snd] in HF'.
  pose proof (HN p n (or_introl eq_refl)). pose proof (HN p m (or_intror H2)). lia.
- subst x. exfalso. specialize (HF' _ H1). unfold zdisjoint in HF'. cbn [fst snd] in HF'.
  pose proof (HN p m (or_introl eq_refl)). pose proof (HN p n (or_intror H1)). lia.
- apply IH; [exact HP | exact H1 | exact H2 |]. intros q k Hq. apply (HN q k). right. exact Hq.
Qed.

(* the read-only bytes are kept along the walk's journal: its footprint is the program's statics (no read-only
   byte, RPG) and heap blocks (outside the image) *)
Lemma scb4_arod : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (scb_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HAR HOin HJ HR.
apply (arodata_ok_journalP SEGS RLO RHI (RRO SEGS B LAWS HB IMG) (RO := ROB SEGS B LAWS HB IMG)
  B STK sp0 (scb_FP O) ly S W mem md own ly' S' W' mem' md' k HJ); [|exact HR].
intros a Hro (r & Hr & Ha). unfold scb_FP in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
1-4: apply (RPG SEGS B LAWS HB IMG a); [|exact Hro].
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS in Ha; lia].
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_CALLS, OFF_ANSWER in Ha; lia].
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_STATE in Ha; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm). cbn [fst snd] in Ha.
  assert (Himg : in_img SEGS a).
  { destruct Hro as [(sg & Hsg & _ & Hrng) | Hrr]; [exists sg; split; [exact Hsg | exact Hrng] | exact (RRO SEGS B LAWS HB IMG a Hrr)]. }
  exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ q (ex_intro _ m (conj (HOin _ Hqm) Ha)))))
    Himg).
Qed.

(* answer's premises at its entry and its contract composed with the walk's journal: sup_connect's post *)
Lemma scb4_answer : forall ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc (Wc : world SEGS) regsc
  memc mdc kc Oc (regsa : bvmap 5 word) mema mdv,
let t := snd (sup_connect_m R verb line (Some port_a) (Some port_b)) in
scb_pre B MT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scb_mid B MT ly S W regs mem md R O (scb_A5 verb line port_a port_b) (SCB_EV5 R)
  (SCB_XM5 MT R verb line port_a port_b) (SCB_LV5 verb line port_a port_b) lyc Sc Wc regsc memc mdc kc Oc ->
ajournal SEGS B SUP_CONNECT_STK (spZ regs) (scb_FP O) ly S W mem md [] lyc Sc Wc mema mdv kc ->
(forall a, rdW Wc mema a = rdW Wc memc a) ->
aregs_preserved regs regsa -> getr regsa 1 = getr regs 1 ->
getr regsa 10 = w64 (rec_slot R) -> getr regsa 11 = w64 0x21d20 -> getr regsa 12 = w64 1 ->
SRr SEGS Wc (cfg_at SEGS (BASE + AF_answer) regsa mema mdv)
  (scb_post B MT ly S W regs mem md verb line port_a port_b R O t).
Proof.
intros ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc regsa mema mdv.
cbv zeta. intros HPRE HMID HJa HVIEW HPT HPT1 HA10 HA11 HA12.
set (t := snd (sup_connect_m R verb line (Some port_a) (Some port_b))) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof scb_stk as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
pose proof HPRE as (HPRE0 & HFRM & Hfr8 & HROD & HRO & H10 & Hpv64 & H11 & Hpl64 & H12 & Hpa64 & H13 & Hpb64 &
  HSV & HSVT & HSL & HSA & HSB & HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJ & Hkc & HRA & HFR & HREPc & HOcO & HBc & HSv & Hfrc & Hbbc & Hmlec).
pose proof (proj1 HJa) as HARa.
pose proof HJa as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _).
assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
set (A5 := scb_A5 verb line port_a port_b) in *.
set (R0 := rec_record R REC_CONNECT A5) in *.
(* the registers at answer's entry *)
assert (Hspa : spZ regsa = spZ regs).
{ unfold spZ. pose proof (HPT 2 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. reflexivity. }
assert (Hs0a : s0Z regsa = s0Z regs).
{ unfold s0Z. pose proof (HPT 8 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 8) with (8%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. reflexivity. }
assert (Hgpa : getr regsa 3 = w64 (as_gp B)).
{ pose proof (HPT 3 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 3) with (3%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact Hgp. }
assert (Htpa : getr regsa 4 = w64 (as_tp B)).
{ pose proof (HPT 4 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 4) with (4%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact Htp. }
(* the recorder's blocks are live *)
assert (HO0 : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (scb_rep_live B ly S _ R O pn HREP0 Hpn)).
assert (HOcB : forall pn, In pn Oc -> In pn (ablocks B lyc Sc))
by (intros pn Hpn; exact (scb_rep_live B lyc Sc _ R0 Oc pn HREPc Hpn)).
(* the run wrote nothing: the recorder at answer's entry *)
assert (HREPa : rec_repA B lyc Sc (rdW Wc mema) R0 Oc)
by exact (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc mema) R0 Oc HREPc HOcB (fun a _ => HVIEW a)).
(* the answer g_rec holds: 0, or the start of one of the recorder's blocks *)
pose proof HREPa as (Q & HARP & HOQ).
assert (HOLD : exists old, aval_mem (rdW Wc mema) (A_G_REC + OFF_ANSWER) 8 old /\
  (old = 0 \/ exists pa0, In pa0 Oc /\ fst pa0 = old)).
{ pose proof HARP as (_ & _ & _ & _ & HANS & _).
  revert HANS. unfold aanswer_at.
  destruct (r_answer R0) as [x|]; destruct (l_answer Q) as [pa0|] eqn:EQ; intros HANS; cbv beta iota in HANS;
  try contradiction.
  - exists (fst pa0). split; [exact (proj1 HANS)|]. right. exists pa0. split; [|reflexivity].
    apply HOQ. unfold lay_blocks. rewrite EQ. cbn [oblk].
    apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. left; reflexivity.
  - exists 0. split; [exact HANS | left; reflexivity]. }
destruct HOLD as (old & Hold & Hold2).
assert (HOLDR : 0 <= old < 2 ^ 64).
{ destruct Hold2 as [-> | ([ap ak] & Hpa0 & Hpa0f)]; [lia|].
  cbn [fst] in Hpa0f. subst ap. pose proof (HOcB _ Hpa0) as HaB.
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARa HaB) as (_ & H4 & Hc & _ & _ & _ & Hk).
  pose proof (req_size_pos ak (proj1 Hk)) as [HR HR'].
  lia. }
(* a block of the entry state that is not the recorder's is not the old answer *)
assert (HNOLD : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> fst pn <> old).
{ intros [pp pk] Hb Hno Hfst. cbn [fst] in Hfst. pose proof (HSv _ Hb Hno) as HbT.
  destruct Hold2 as [Eo | ([ap ak] & Hpa0 & Hpa0f)].
  - pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARa HbT) as (_ & H4 & _). lia.
  - cbn [fst] in Hpa0f. pose proof (HOcB _ Hpa0) as HaB.
    rewrite <- Hpa0f in Hfst. subst pp.
    pose proof (scb4_start_uniq _ _ _ _ _ _ _ _ HARa HbT HaB) as Ek. subst pk.
    exact (Hno (HOcO _ Hpa0 Hb)). }
(* the footprint of the walk lies below the stack *)
assert (HFPhi : forall a, alloc_ceiling <= a -> ~ inFP (scb_FP O) a).
{ intros a Ha Hin. pose proof (scb_fp_low B LAWS ly S W mem md O a HAR HO0 Hin). lia. }
assert (HCR : 0 <= rec_slot R < 2 ^ 64).
{ unfold rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt.
  - apply Nat.ltb_lt in Elt. unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia.
  - unfold A_REC_SPILL. lia. }
(* answer's premises *)
assert (HPA : afn_pre SEGS B ANSWER_STK lyc Sc Wc regsa mema mdv ch).
{ apply (afn_pre_at SEGS B SUP_CONNECT_STK (spZ regs) (scb_FP O) ly S W mem md [] lyc Sc Wc mema mdv kc regsa
    ANSWER_STK 0 ch HJa);
  [lia | reflexivity | lia | exact K8 | lia | rewrite HPT1; exact Hra | unfold raZ in *; rewrite HPT1; exact Hra4
  | exact Hgpa | exact Htpa |].
  rewrite Hspa, Hs0a.
  apply (achain_ly_top ly lyc); [exact ET|].
  apply (achain_kept ly (rdW W mem) (rdW Wc mema) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. exact (aview_above_of_journal B SUP_CONNECT_STK (spZ regs) (scb_FP O) ly S W mem md [] lyc Sc Wc
    mema mdv kc HJa a Ha (HFPhi a ltac:(lia))). }
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW Wc mema))
by exact (scb4_arod SUP_CONNECT_STK (spZ regs) O ly S W mem md [] lyc Sc Wc mema mdv kc HAR HO0 HJa HROD).
assert (HRO5 : cmd_ro_ok (rdW Wc mema)) by exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc mema mdv HARa HROD5).
(* the shape "resp 0" at 0x21d20: a read-only literal no runtime entry owns *)
assert (HLIT : abytes_atR (rdW Wc mema) 0x21d20 RO_lit_21d20)
by exact (cmd_ro_obj_bytes SEGS B LAWS HB IMG lyc Sc Wc mema mdv _ HARa HROD5 scb4_lit_in).
assert (HRIN : forall i, 0 <= i < 7 -> in_roP SEGS RLO RHI (0x21d20 + i) /\
  ~ Exists (in_zr (0x21d20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21d20 + i < as_errno B + 4)).
{ intros i Hi.
  assert (Hl : (Z.to_nat i < length (snd (0x21d20, RO_lit_21d20)))%nat).
  { cbn [snd]. assert (L7 : length RO_lit_21d20 = 7%nat) by reflexivity. rewrite L7. lia. }
  pose proof (crf_ro_list_in _ _ scb4_lit_in Hl) as Hx. cbn [fst] in Hx. rewrite Z2Nat.id in Hx by lia.
  split; [exact (cmd_ro_in_to _ (cif_ro_in _ _ IMG) _ Hx)|].
  exact (cmd_ro_in_to _ (cif_ro_unowned _ _ IMG) _ Hx). }
assert (HSTR : astr_atR (rdW Wc mema) 0x21d20 REC_MOD_HOST_SHAPE).
{ assert (EQL : REC_MOD_HOST_SHAPE ++ [Z_to_bv 8 0] = RO_lit_21d20) by reflexivity.
  unfold astr_atR. rewrite EQL. split; [exact HLIT|].
  assert (HN : forallb (fun b : byte => negb (bv_unsigned b =? 0)) REC_MOD_HOST_SHAPE = true)
    by (vm_compute; reflexivity).
  intros Hin. rewrite forallb_forall in HN. specialize (HN _ Hin). vm_compute in HN. discriminate. }
assert (HARG : astr_argA B lyc Sc (rdW Wc mema) (in_roP SEGS RLO RHI) Oc 0x21d20 (Some REC_MOD_HOST_SHAPE)).
{ assert (HL : Z.of_nat (length REC_MOD_HOST_SHAPE) + 1 = 7) by reflexivity.
  assert (HL6 : 0x21d20 + Z.of_nat (length REC_MOD_HOST_SHAPE) = 0x21d26) by reflexivity.
  unfold astr_argA. cbv beta iota zeta. rewrite HL, HL6.
  split; [lia|]. split; [exact HSTR|]. split; [unfold LMAX; lia|].
  right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity |]]].
  - intros i Hi. exact (HRIN i Hi).
  - assert (E : existsb (Z.eqb 0x21d26) cmd_ro_ends = true) by (vm_compute; reflexivity).
    apply existsb_exists in E as (y & Hy & E). apply Z.eqb_eq in E. subst y. exact Hy. }
assert (HFIT : fits REC_MOD_HOST_SHAPE) by (unfold fits; apply Z.leb_le; vm_compute; reflexivity).
(* the slot c is the call record() started *)
assert (HSLOT : r_refuse R0 = 0 -> true = true ->
  (exists k, nth_error (r_calls R0) k = Some (REC_CONNECT, A5) /\
     rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (rec_slot R = A_REC_SPILL /\ (REC_CONNECT, A5) = r_spill R0))
by (intros _ _; exact (rec_slot_entry R REC_CONNECT A5)).
assert (HEVA : st_nev Sc + EV_ANSWER <= EV_MAX).
{ pose proof HJa as (_ & _ & _ & _ & _ & _ & Hnev & _).
  unfold EV_SUP_CONNECT, SCB_EV5, SCB_EV4, SCB_EV3, SCB_EV2, SCB_EV1 in *. lia. }
assert (HLVA : blocks_bytes Sc + LIVE_ANSWER t <= LIVE_MAX).
{ unfold LIVE_SUP_CONNECT, SCB_LV5, SCB_LV4, SCB_LV3, SCB_LV2, SCB_LV1 in Hlive, Hbbc. lia. }
assert (HMOKA : mo_ok MT Sc (XM_ANSWER MT t)).
{ apply (mo_ok_step MT MTL S Sc (SCB_XM5 MT R verb line port_a port_b) (XM_ANSWER MT t)); [exact HMOK | exact Hmlec]. }
pose proof (TANSWER fx lyc Sc Wc regsa mema mdv ch (rec_slot R) 0x21d20 old (REC_CONNECT, A5) REC_MOD_HOST_SHAPE true
  R0 Oc HPA HFRM ltac:(rewrite Hfrc; exact Hfr8) HROD5 HRO5 HA10 HCR HA11 ltac:(lia)
  ltac:(rewrite HA12; reflexivity) HREPa Hold HOLDR (fun _ => conj HARG HFIT) HSLOT HEVA HLVA HMOKA) as HA.
(* answer's post, composed with the walk's journal *)
eapply SRr_mono; [exact HA|].
intros W2 c2 _ HAP. destruct HAP as (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfx1 & Hfx2 & HJ1 & HP1 & HK).
destruct HK as (p1 & p2 & O' & Hq10 & Hq4096 & Hp12 & Hfr2 & Hbl2 & HREP2 & HO' & Hstr2 & Hbb2 & Hmle2).
change (snd (rec_answer R0 (REC_CONNECT, A5) REC_MOD_HOST_SHAPE true)) with t in *.
assert (HPS : as_prog_static B = recb_PG) by (rewrite (ts_prog B HB); reflexivity).
assert (HF : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) ::
    (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) Oc)) a ->
  awr_byte SEGS B SUP_CONNECT_STK (spZ regs) (scb_FP O) (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [] a).
{ intros a (r & Hr & Hb). unfold awr_byte, awr_prog_or_caller.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hb.
  - right. right. right. right. left.
    assert (HPG : inFP cmd_PG a).
    { exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_ANSWER in Hb; lia]. }
    split; [|split; [rewrite HPS; apply recb_grec_in; unfold REC_SIZE, OFF_ANSWER in *; lia
      | exact (cif_prog_img _ _ IMG a HPG)]].
    exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8). unfold scb_FP.
    split; [right; left; reflexivity | cbn [fst snd]; unfold OFF_CALLS, OFF_ANSWER in *; lia].
  - right. right. right. right. left.
    assert (HPG : inFP cmd_PG a).
    { exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_STATE in Hb; lia]. }
    split; [|split; [rewrite HPS; apply recb_grec_in; unfold REC_SIZE, OFF_STATE in *; lia
      | exact (cif_prog_img _ _ IMG a HPG)]].
    exists (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8). unfold scb_FP.
    split; [right; right; left; reflexivity | cbn [fst snd]; lia].
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([bp bn] & <- & Hb2).
    pose proof (scb4_filter_sub _ _ _ _ Hb2) as HbOc.
    cbn [fst snd] in Hb. pose proof (HOcB _ HbOc) as HbB.
    destruct (in_dec DEC (bp, bn) (ablocks B ly S)) as [Hin | Hnin].
    + right. left. split.
      * exists (bp, bp + req_size bn). split; [|cbn [fst snd]; lia].
        unfold scb_FP. right. right. right. right. unfold ablocks_fp. apply in_map_iff.
        exists (bp, bn). split; [reflexivity | exact (HOcO _ HbOc Hin)].
      * exists bp, bn. split; [exact HbB | lia].
    + right. right. left. exists bp, bn. split; [exact HbB|]. split; [exact Hnin | lia]. }
assert (VIS : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) ::
    (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) Oc)) a ->
  spZ regs - SUP_CONNECT_STK <= a < spZ regs -> ~ (spZ regsa - ANSWER_STK <= a < spZ regsa) ->
  aview SEGS (w_H W2) mem2 a <> None).
{ intros a (r & Hr & Hb) Hw _. exfalso.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hb.
  - unfold A_G_REC, OFF_ANSWER in Hb. lia.
  - unfold A_G_REC, OFF_STATE in Hb. lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([bp bn] & <- & Hb2).
    pose proof (scb4_filter_sub _ _ _ _ Hb2) as HbOc.
    cbn [fst snd] in Hb. pose proof (HOcB _ HbOc) as HbB.
    pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARa HbB) as (_ & _ & Hc & _). lia. }
pose proof (ajournal_sub_wide SEGS B LAWS pa_segs_low SUP_CONNECT_STK (spZ regs) (scb_FP O) ly S W mem md []
  lyc Sc Wc mema mdv kc ANSWER_STK (spZ regsa) _ [] ly2 S2 W2 mem2 md2 EV_ANSWER HJa HJ1 ltac:(lia) ltac:(lia)
  HF VIS) as HJ2.
pose proof HJ1 as (HAR2 & _).
(* sup_connect's post *)
unfold scb_post, apost_baseF. cbv beta.
exists fx', ly2, S2, regs2, mem2, md2.
split; [rewrite HPT1; reflexivity|].
split; [exact Hfx1|]. split; [exact Hfx2|].
split.
{ apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2).
  unfold EV_SUP_CONNECT, SCB_EV5, SCB_EV4, SCB_EV3, SCB_EV2, SCB_EV1 in *. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPT HP1)|].
exists (fst (sup_connect_m R verb line (Some port_a) (Some port_b))), O', p2.
split; [apply surjective_pairing|].
cbv zeta.
split; [exact Hq10|]. split; [exact Hq4096|]. split; [exact HREP2|].
split.
{ intros pn Hpn Hb. apply HO' in Hpn as [[HpnOc _] | ->]; [exact (HOcO pn HpnOc Hb)|].
  destruct (in_dec DEC (p1, Z.of_nat (length t) + 1) O) as [Hin | Hnin]; [exact Hin|].
  exfalso. exact (proj1 (Hfr2 _ (HSv _ Hb Hnin) (HNOLD _ Hb Hnin)) eq_refl). }
split.
{ intros pn Hpn. apply Hbl2 in Hpn as [[Hb Hne] | [-> | ->]].
  - destruct (HBc pn Hb) as [X | HpnOc]; [left; exact X|].
    right. left. apply HO'. left. split; [exact HpnOc | exact Hne].
  - right. left. apply HO'. right. reflexivity.
  - right. right. reflexivity. }
split.
{ intros pn Hb Hno. apply Hbl2. left. split; [exact (HSv _ Hb Hno) | exact (HNOLD pn Hb Hno)]. }
split; [apply Hbl2; right; right; reflexivity|].
split.
{ intros Hin. destruct (in_dec DEC (p2, Z.of_nat (length t) + 1) O) as [HO | Hno]; [exact HO|].
  exfalso. exact (proj2 (Hfr2 _ (HSv _ Hin Hno) (HNOLD _ Hin Hno)) eq_refl). }
split.
{ intros Hin. apply in_map_iff in Hin as ([pp pk] & Hf & Hpn). cbn [fst] in Hf. subst pp.
  apply HO' in Hpn as [[HpnOc Hne] | Heq].
  - pose proof (HOcB _ HpnOc) as HbT.
    assert (Hb2 : In (p2, pk) (ablocks B ly2 S2)) by (apply Hbl2; left; split; [exact HbT | exact Hne]).
    assert (Hq2 : In (p2, Z.of_nat (length t) + 1) (ablocks B ly2 S2)) by (apply Hbl2; right; right; reflexivity).
    pose proof (scb4_start_uniq _ _ _ _ _ _ _ _ HAR2 Hb2 Hq2) as Ek. subst pk.
    exact (proj2 (Hfr2 _ HbT Hne) eq_refl).
  - injection Heq as E1 _. exact (Hp12 (eq_sym E1)). }
split; [exact Hstr2|].
split; [unfold LIVE_SUP_CONNECT, SCB_LV5, SCB_LV4, SCB_LV3, SCB_LV2, SCB_LV1 in *; lia|].
exact (mo_le_trans MT MTL S Sc S2 _ _ Hmlec Hmle2).
Qed.

Lemma scb_tail_ok : SCB_T_stmt B MT.
Proof.
unfold SCB_T_stmt.
intros ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc.
cbv zeta. intros HPRE HMID H20.
set (t := snd (sup_connect_m R verb line (Some port_a) (Some port_b))) in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof scb_stk as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
pose proof HPRE as (HPRE0 & HFRM & Hfr8 & HROD & HRO & H10 & Hpv64 & H11 & Hpl64 & H12 & Hpa64 & H13 & Hpb64 &
  HSV & HSVT & HSL & HSA & HSB & HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJ & Hkc & HRA & HFR & HREPc & HOcO & HBc & HSv & Hfrc & Hbbc & Hmlec).
pose proof HRA as (Rsp & R8 & R9 & R18 & R19 & R3 & R4 & Rhi).
pose proof (proj1 HJ) as HARc.
destruct (scb_seed B SCB_R5 ly regs regsc lyc Sc Wc memc mdc Hstk HARc Rsp HFR) as [HS SHOK].
remember (Eimg (Ereg regsc (scb_extra_m regs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite HE. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = getr regs (Z_to_bv 5 (nth j scb_saved 0))).
{ intros j Hj. rewrite HE. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  unfold scb_extra_m. do 6 (destruct j as [|j]; [reflexivity|]). lia. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 48) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
(* 0x8b4c0 .. 0x8b4ec: a1 := "resp 0", a2 := 1, a0 := s4, the frame's six words back, sp += 48, `j answer` *)
paj_run_tok RUN HS HJ SHOK scb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms5 end.
assert (HVIEW : forall a, rdW Wc (ms_mem ms5) a = rdW Wc memc a) by (intros a; exact (scb4_ro_keeps E _ _ _ a HFr)).
clear HF HFr HG.
pmkst HS.
rewrite (scb_sig_answer SIGP).
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
(* the registers at answer's entry *)
assert (HPT1 : getr (ms_regs ms5) 1 = getr regs 1).
{ rewrite Q1. pose proof (EX 0%nat ltac:(lia)) as X. cbn [Nat.add nth scb_saved] in X. rewrite X.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
assert (HA10 : getr (ms_regs ms5) 10 = w64 (rec_slot R)) by (rewrite Q10, (EE 20%nat 20%bv eq_refl); exact H20).
assert (HA11 : getr (ms_regs ms5) 11 = w64 0x21d20).
{ rewrite Q11. apply bv_eq. rewrite (HEI 283%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  change (VAL 283%nat) with (VAL (A_OBJ 42)). rewrite (scb_obj42 VOBJS). rewrite unsigned_lit_small by lia. reflexivity. }
assert (HA12 : getr (ms_regs ms5) 12 = w64 1) by (rewrite Q12; reflexivity).
assert (HPT : aregs_preserved regs (ms_regs ms5)).
{ unfold aregs_preserved. intros r Hr. unfold acallee_saved in Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by lia.
  clear Hr. repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases].
  all: rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
      let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
  1: { rewrite U2. replace (spZ regs - 48 + 48) with (spZ regs) by lia. unfold spZ.
    replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). apply Z_to_bv_bv_unsigned. }
  1: { rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl).
    replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact R3. }
  1: { rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl).
    replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact R4. }
  all: lazymatch goal with
    | |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) =>
      first [ let j := eval compute in (n - 32)%nat in
              pose proof (EX j ltac:(lia)) as X; cbn [Nat.add nth scb_saved] in X; exact X
            | rewrite (EE n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia ]
    end. }
exact (scb4_answer ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc
  (ms_regs ms5) (ms_mem ms5) mdv HPRE HMID HJ HVIEW HPT HPT1 HA10 HA11 HA12).
Qed.

End e.
End f.
End d.
