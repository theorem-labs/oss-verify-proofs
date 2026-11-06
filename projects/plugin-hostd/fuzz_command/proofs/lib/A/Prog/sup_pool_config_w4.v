(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of sup_pool_config's ASan walk (plugin-hostd/fuzz_command): from
   the return of arg_i (0x8bdfc) through rec_shape_of to the tail jump to answer and the member's post, proved at any
   FP state (arg_i's printf may change it), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v (a seed, the symbolic run to a call, the callee's contract
   through cl_callS, the state after the call). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c rec_shape_of_c answer_c hand_back_c mix_call_c sup_pool_config_c PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas sup_pool_config_s1 sup_pool_config_s2 sup_pool_config_s3 sup_pool_config_s4 sup_pool_config_s5
sup_pool_config_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HY : spc_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma spc_filter_in : forall (f : Z * Z -> bool) (l : list (Z * Z)) x, In x (filter f l) -> In x l.
Proof.
intros f l x. induction l as [|a l IH]; intros H; [exact H|].
revert H. cbn. destruct (Is_true_dec (f a)); intros H;
[destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H)].
Qed.

(* the caller's frame chain above the entry sp, carried by the journal (sup_instance_verb_s5.v's siv_chain) *)
Lemma spc_chain : forall STK sp0 FP ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc k v ch,
ajournal SEGS B STK sp0 FP ly S W mem md [] lyc Sc Wc memc mdc k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch -> achain lyc (rdW Wc memc) sp0 v ch.
Proof.
intros STK sp0 FP ly S W mem md lyc Sc Wc memc mdc k v ch HJ HFP Hch.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly lyc); [first [exact Etop | symmetry; exact Etop]|].
apply (achain_kept ly (rdW W mem) (rdW Wc memc) sp0 v ch sp0 Hch); [lia | lia |].
intros a Ha. apply F1; [lia | lia | intros Hin; pose proof (HFP a Hin); lia].
Qed.

(* a write to g_rec is a footprint write to a program static *)
Lemma spc_awr_grec : forall STK sp0 O bl0 blc fr0 lyc own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp0 (spc_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha. spc_unpack HY.
right; right; right; right. unfold awr_prog_or_caller. left.
split; [exact (spc_inFP_grec O a Ha)|].
pose proof (recb_grec_in a Ha) as HPG.
split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)].
Qed.

(* a string argument read through a reader that agrees on every address *)
Lemma spc_argA_ext : forall ly S (rd rd' : reader) O p (x : list byte),
(forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) -> 0 <= p -> p + Z.of_nat (length x) < 2 ^ 64 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) -> astr_argA B ly S rd' (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S rd rd' O p x Hrd Hp0 Hp1 (Hn0 & [Hb Hnz] & Hn & Harm).
split; [exact Hn0|]. split; [|split; [exact Hn | exact Harm]].
split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (Hrd (p + Z.of_nat i)) by lia. exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.


Lemma spc_seg_tail : forall ly S W (regs : bvmap 5 word) mem md ch (max : Z) name R O O0 F p1 p2 ly3 S3
  (W3 : world SEGS) mem3 md3 (regs3 : bvmap 5 word),
afn_pre SEGS B SUP_POOL_CONFIG_STK ly S W regs mem md ch ->
frm0 fx ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
-2 ^ 31 <= max < 2 ^ 31 ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_POOL_CONFIG R <= EV_MAX -> blocks_bytes S + LIVE_SUP_POOL_CONFIG R name max <= LIVE_MAX ->
mo_ok MT S (XM_SUP_POOL_CONFIG MT R name max) ->
spc_midI B MT ly S W regs mem md R O name max O0 F p1 p2 ly3 S3 W3 mem3 md3 regs3 ->
SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + SPC_ARGI)) mem3 (seg_rom SEGS)) md3)
  (spc_goal B MT ly S W regs mem md R O name max).
Proof.
intros ly S W regs mem md ch max name R O O0 F p1 p2 ly3 S3 W3 mem3 md3 regs3 HFN HFR0 HROD Hmax HREP HEV HLIVE HMOK HMID.
spc_unpack HY.
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
unfold spc_midI in HMID. cbv zeta in HMID.
set (sp0 := spZ regs) in *.
set (c := spc_slot R) in *. set (x := sarg name) in *.
set (t := snd (sup_pool_config_m R name max)) in *.
set (n1 := LIVE_XSTRDUP x) in *. set (n2 := Z.of_nat (length (dec max)) + 1) in *.
destruct HMID as (HJ3 & HA3 & HFO & HO0 & Hb1 & Hb2 & P12 & HBB3 & HMLE3 & HFR3 & HFRM3 & HREP3 & R2 & R8 & R9 & R20 & RK).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfr3 & Hnev3 & _).
destruct (spc_rep_ncalls B ly S _ R O HREP) as [_ Hlen16].
pose proof (spc_slot_okR R Hlen16) as Hc. fold c in Hc.
destruct (spc_slot_bounds c Hc) as [Hcb Hc8].
assert (HSTKv : SUP_POOL_CONFIG_STK = 16592) by (vm_compute; reflexivity).
rewrite HSTKv in *.
assert (Hsp46 : 2 ^ 46 <= sp0 - 64) by lia.
(* the seed: the frame and the registers arg_i returned with *)
destruct (spc_seed_fr B LAWS HB SPC_ARGI spc_regsJ W3 regs regs3 mem3 sp0 0 c ly3 S3 md3 HAR3 Hsp46 ltac:(lia) Hsp16 Hc
  ltac:(rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
  (spc_regs_okJ regs regs3 c Hcb R9 R20) HFRM3) as [HS SHOK].
set (E := Eimg (Ereg regs3 (spc_extra regs 0 c))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r) by exact (spc_E_reg regs regs3 0 c).
destruct (spc_E_lit regs regs3 0 c) as (E32 & _ & E34). fold E in E32, E34.
assert (E2u : bv_unsigned (ew E 2) = sp0 - 64) by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJ3 SHOK SPC_SPAN.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS. spc_md.
assert (K54 : forall a, 0 <= a < 2 ^ 64 -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a).
{ intros a Ha. match goal with HFr : frame_of E _ _ _ |- _ => apply (recb_run_keeps_m E _ (w_H W3) mem3 (ms_mem ms) a HFr Ha) end.
  intros (r & Hr & Hrw). destruct Hr as [<- | []]. cbn in Hrw. lia. }
(* 0x8be08: the call of rec_shape_of on the verb "pool_config" (.str.12) and its length 11 *)
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
rewrite (EE 2%nat 2%bv eq_refl), R2 in T2. rewrite (EE 3%nat 3%bv eq_refl) in T3. rewrite (EE 4%nat 4%bv eq_refl) in T4.
rewrite (EE 8%nat 8%bv eq_refl), R8 in T8.
assert (T10' : getr (ms_regs ms) 10 = w64 0x21e80).
{ rewrite T10. apply bv_eq. pose proof (HEI 309%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H.
  change (309%nat) with (A_OBJ 68) in H |- *. rewrite H, (spc_verb_val VOBJS). unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (T11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length spc_verb))) by (rewrite T11; reflexivity).
assert (T3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite T3; exact (eq_trans (RK 3 ltac:(cbn; tauto)) Hgp)).
assert (T4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite T4; exact (eq_trans (RK 4 ltac:(cbn; tauto)) Htp)).
pose proof HJ3 as (HAR3' & Hly3' & _ & _ & _ & Hfr3' & Hnev3' & _).
assert (HRO3 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms)))
  by exact (spc_aro B MT HY _ _ O ly S W mem md _ _ _ _ _ _ _ HAR (spc_rep_in B ly S _ R O HREP) HJ3 HROD).
assert (HROK3 : cmd_ro_ok (rdW W3 (ms_mem ms))) by exact (cmd_ro_ok_of_aro ly3 S3 W3 (ms_mem ms) _ HAR3' HRO3).
(* the verb "pool_config" in astr_argA's read-only form: the record's literal facts *)
assert (HVERB : astr_argA B ly3 S3 (rdW W3 (ms_mem ms)) (in_roP SEGS RLO RHI) [] 0x21e80 (Some spc_verb)).
{ split; [lia|]. split; [exact (spc_verb_str _ HROK3)|]. split; [rewrite spc_verb_len; unfold LMAX; lia|].
  right. split; [|split; [exact (proj1 spc_verb_chk) | split; [exact (proj2 spc_verb_chk) | exact spc_verb_end]]].
  intros i Hi. rewrite spc_verb_len in Hi. split; [exact (spc_verb_ro _ CMD_RO_IN i Hi)|].
  exact (spc_verb_unowned B MT HY (0x21e80 + i) ltac:(lia)). }
assert (SR : SIG CS_rec_shape_of = BASE + AF_rec_shape_of).
{ rewrite (SIGP CS_rec_shape_of ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))). f_equal. }
rewrite SR.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W3 (ms_regs ms) (ms_mem ms) _ _ sp0 (spc_FP O) ly S W mem md [] ly3 S3 _ _
    REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-64) (getr (ms_regs ms) 1)).
  - exact HJ3.
  - unfold spZ. rewrite T2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - reflexivity.
  - lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - exact T3'.
  - exact T4'.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite T1, unsigned_lit_small by lia. lia.
  - intros HPRE1. unfold cfg_at in *.
    exact (TREC_SHAPE_OF fx ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ 0x21e80 spc_verb HPRE1 HRO3 T10' ltac:(lia)
      T11' ltac:(rewrite spc_verb_len; lia) HROK3 VOBJS (fun _ => conj (spc_verb_bytes _ HROK3) (or_intror HVERB))
      ltac:(unfold EV_SUP_POOL_CONFIG, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP, EV_REC_SHAPE_OF in *; lia)).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
(* back at 0x8be0c: a0 = q, the shape "pool_config" maps to *)
cbv beta. intros W4 c4 HW4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJr & HP4 & ((q & S10 & Sq & SARG) & Sperm & Sly & SS)).
pose proof HJr as (HAR4 & _ & _ & _ & _ & Sfrs & Snev & _ & SK394 & SKB & SKI & _).
assert (K65g : forall a, Exists (in_zr a) recb_PG -> rdW W4 mem4 a = rdW W3 (ms_mem ms) a).
{ intros a HPG. destruct (spc_prog_unowned B HB a HPG) as [Hown Herr].
  apply SKI; [exact (cmd_prog_img a HPG) | exact Hown | exact Herr|].
  apply fp_spares_closed; [apply sink_closed_pos; constructor | exact (inFP_nil a)]. }
assert (K65b : forall p n i, In (p, n) (ablocks B ly3 S3) -> 0 <= i < req_size n ->
  rdW W4 mem4 (p + i) = rdW W3 (ms_mem ms) (p + i)).
{ intros p n i Hin Hi. apply (SKB p n i); [exact Hin | apply (Permutation_in _ (Permutation_sym Sperm)); exact Hin | exact Hi | exact (inFP_nil _)]. }
jafter_call_keep_pi HS 48%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. constructor; [|constructor]; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val spc_frame]; intros a Ha.
  - rewrite E2u in Ha. apply (mbyte_of_aview SEGS). apply SK394; [lia | lia | exact (inFP_nil a)].
  - lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
set (E4 := havoc E 48 (map (getr regs4) CLOB)) in *.
assert (HEIu : img_env VAL A_LIM E4) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD4 : forall k, (k < 48)%nat -> ew E4 k = ew E k) by (intros k Hk; apply ew_havoc_old; exact Hk).
assert (SHOK4 : sh_ok SEGS SPC_Bx SPC_SH E4 (mrestrict (w_H W4) mem4)).
{ apply (spc_sh_ok B LAWS HB ly4 S4 W4 mem4 md4 E4 c HAR4); [rewrite OLD4 by lia; exact E32 | rewrite OLD4 by lia; exact E34 | exact Hc]. }
rewrite T1.
paj_run_tok RUN HS HJ4 SHOK4 SPC_SPAN.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS. spc_md.
assert (K76 : forall a, 0 <= a < 2 ^ 64 -> rdW W4 (ms_mem ms0) a = rdW W4 mem4 a).
{ intros a Ha. match goal with HFr : frame_of E4 _ _ _ |- _ => apply (recb_run_keeps_m E4 _ (w_H W4) mem4 (ms_mem ms0) a HFr Ha) end.
  intros (r & Hr & Hrw). destruct Hr as [<- | []]. cbn in Hrw. lia. }
(* the registers at answer's entry: the prologue's registers restored, a0 = c, a1 = q, a2 = 1 *)
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11.
prreg HS (12%bv : bv 5) U12.
assert (ES4 : forall j r, nth_error spc_saved j = Some r -> ew E4 (35 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj. assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some spc_saved j)); rewrite Hj; discriminate).
  rewrite OLD4 by lia. exact (spc_E_saved regs regs3 0 c j r Hj). }
assert (A1 : getr (ms_regs ms0) 1 = getr regs 1) by (rewrite U1; exact (ES4 0%nat 1 eq_refl)).
assert (A2 : getr (ms_regs ms0) 2 = getr regs 2).
{ rewrite U2, OLD4 by lia. rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia.
  unfold sp0, spZ. replace (bv_unsigned (getr regs 2) - 64 + 64) with (bv_unsigned (getr regs 2)) by lia.
  apply Z_to_bv_bv_unsigned. }
assert (A3 : getr (ms_regs ms0) 3 = w64 (as_gp B)).
{ rewrite U3, OLD4 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact (eq_trans (RK 3 ltac:(cbn; tauto)) Hgp). }
assert (A4 : getr (ms_regs ms0) 4 = w64 (as_tp B)).
{ rewrite U4, OLD4 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact (eq_trans (RK 4 ltac:(cbn; tauto)) Htp). }
assert (A8 : getr (ms_regs ms0) 8 = getr regs 8) by (rewrite U8; exact (ES4 1%nat 8 eq_refl)).
assert (A9 : getr (ms_regs ms0) 9 = getr regs 9) by (rewrite U9; exact (ES4 2%nat 9 eq_refl)).
assert (A10 : getr (ms_regs ms0) 10 = w64 c) by (rewrite U10, OLD4 by lia; rewrite E34; reflexivity).
assert (A11 : getr (ms_regs ms0) 11 = w64 q) by (rewrite U11; exact S10).
assert (Ahi : forall r, 18 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hr10 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr10 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
  (rewrite (st_ok_restrict_reg SEGS (w_H W4) E4 _ _ _ HS); cbn [ms_regs];
   lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
   cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
   first [ exact (ES4 3%nat 18 eq_refl) | exact (ES4 4%nat 19 eq_refl) | exact (ES4 5%nat 20 eq_refl) | exact (ES4 6%nat 21 eq_refl)
         | lazymatch goal with |- ew E4 ?k = getr regs (Z_to_bv 5 ?rv) =>
             rewrite (OLD4 k ltac:(lia)), (EE k (Z_to_bv 5 rv) eq_refl); apply RK; cbn; tauto end ]). }
assert (HPT : aregs_preserved regs (ms_regs ms0)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]];
  [ exact A2 | exact (eq_trans A3 (eq_sym Hgp)) | exact (eq_trans A4 (eq_sym Htp)) | exact A8 | exact A9 | exact (Ahi r Hr) ]. }
(* the recorder at answer's call: the state after arg_i, kept by the two runs and rec_shape_of *)
assert (KS4 : forall a, Exists (in_zr a) recb_PG -> rdW W4 (ms_mem ms0) a = rdW W3 mem3 a).
{ intros a HPG. pose proof (pa_img_range a (cmd_prog_img a HPG)) as Hr.
  rewrite K76 by lia. rewrite K65g by exact HPG. apply K54. lia. }
assert (Kblk3 : forall p n i, In (p, n) (ablocks B ly3 S3) -> 0 <= i < req_size n ->
  rdW W4 (ms_mem ms0) (p + i) = rdW W3 mem3 (p + i)).
{ intros p n i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR3 Hin) as (_ & H4096 & Hcp & _ & _ & _ & Hn0).
  rewrite K76 by lia. rewrite (K65b p n i Hin Hi). apply K54. lia. }
assert (Hin4 : forall bq, In bq (ablocks B ly3 S3) -> In bq (ablocks B ly4 S4))
  by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym Sperm)); exact Hbk).
assert (HREPA : rec_repA B ly4 S4 (rdW W4 (ms_mem ms0)) (rec_record R REC_POOL_CONFIG [x; dec max]) (O0 ++ [(p1, n1); (p2, n2)])).
{ apply (spc_rep_keep B ly3 S3 ly4 S4 (rdW W3 mem3) (rdW W4 (ms_mem ms0)) _ _ HREP3).
  - intros bq Hbq. exact (Hin4 _ (spc_rep_in B ly3 S3 _ _ _ HREP3 _ Hbq)).
  - intros a Ha. exact (KS4 a (recb_grec_in a Ha)).
  - intros a Ha. exact (KS4 a (recb_spill_in a Ha)).
  - intros [pb nb] i Hbq Hi. cbn [fst snd] in *.
    pose proof (spc_rep_in B ly3 S3 _ _ _ HREP3 _ Hbq) as Hin.
    destruct (req_size_pos nb ltac:(lia)) as [_ Hrq].
    exact (Kblk3 pb nb i Hin ltac:(lia)). }
(* the shape at answer's call: rec_shape_of's astr_argA, read through the memory the run left *)
assert (HSHAPE : astr_argA B ly4 S4 (rdW W4 (ms_mem ms0)) (in_roP SEGS RLO RHI) (O0 ++ [(p1, n1); (p2, n2)]) q (Some (shape_of spc_verb))).
{ pose proof (SARG (O0 ++ [(p1, n1); (p2, n2)])) as HS0.
  apply (spc_argA_ext ly4 S4 (rdW W4 mem4) _ _ q _ K76 ltac:(lia)); [|exact HS0].
  destruct HS0 as (_ & _ & _ & [((b & k & Hbk & Hbq & Hqe) & _) | (Hro & _)]).
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR4 Hbk) as (_ & _ & Hce & _ & _ & _ & Hk0).
    destruct (req_size_pos k ltac:(lia)). lia.
  - destruct (Hro (Z.of_nat (length (shape_of spc_verb))) ltac:(lia)) as (Hr & _).
    pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia. }
destruct (spc_rep_answer_old B ly4 S4 _ _ _ HREPA) as (old & Hold & Hold').
pose proof HJ4 as (HAR4' & Hly4 & _ & _ & _ & Hfr4 & Hnev4 & Hk4 & _).
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Hold' as [-> | (m & Hm)]; [lia|].
  pose proof (spc_rep_in B ly4 S4 _ _ _ HREPA _ Hm) as Hm4.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ old m HAR4' Hm4) as (_ & H4096 & Hce & _ & _ & _ & Hm0).
  destruct (req_size_pos m ltac:(lia)). lia. }
assert (HT : t = snd (rec_answer (rec_record R REC_POOL_CONFIG [x; dec max]) (REC_POOL_CONFIG, [x; dec max]) (shape_of spc_verb) true))
  by (unfold t; rewrite spc_model; reflexivity).
assert (HMN : 0 <= mo_free MT /\ (forall n, 0 <= n -> 0 <= mo_malloc MT n))
  by (split; [exact (mo_free_nonneg MT MTL) | exact (mo_malloc_nonneg MT MTL)]).
assert (XMA : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (proj2 HMN (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
assert (HBB4 : blocks_bytes S4 <= blocks_bytes S + n1 + n2) by (rewrite SS; exact HBB3).
assert (HMLE4 : mo_le MT S S4 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x + XM_ARG_I MT max + 0)).
{ apply (mle_station MT S S3 S4 _ _ MTL HMLE3). rewrite SS. exact (mle_start MT S3 MTL). }
assert (HFR4 : Z.of_nat (length (frames S4)) <= 8) by (rewrite SS; exact HFR3).
assert (SN : SIG CS_answer = BASE + AF_answer).
{ rewrite (SIGP CS_answer ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))). f_equal. }
rewrite SN.
assert (WA : ANSWER_STK = 16592) by (vm_compute; reflexivity).
assert (Hspa : spZ (ms_regs ms0) = sp0) by (unfold spZ at 1; rewrite A2; reflexivity).
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W4 (ms_regs ms0) (ms_mem ms0) (Z_to_bv 64 (BASE + AF_answer)) _ sp0 (spc_FP O)
    ly S W mem md [] ly4 S4 _ _ ANSWER_STK _ _ 0 (getr (ms_regs ms0) 1) ch _ HJ4).
  - unfold spZ at 1. rewrite A2. fold (spZ regs). lia.
  - reflexivity.
  - lia.
  - rewrite WA. lia.
  - rewrite WA. lia.
  - exact A3.
  - exact A4.
  - reflexivity.
  - rewrite A1. exact Hra.
  - rewrite A1. exact Hra4.
  - rewrite Z.add_0_r. unfold s0Z. rewrite A8.
    exact (spc_chain _ sp0 _ ly S W mem md ly4 S4 W4 (ms_mem ms0) _ _ _ ch HJ4
      (spc_FP_low B ly S W mem md O HAR (spc_rep_in B ly S _ R O HREP)) Hch).
  - intros HPRE1. unfold tanswer_spec in TANSWER. unfold cfg_at in *.
    eapply (TANSWER fx ly4 S4 W4 (ms_regs ms0) (ms_mem ms0) _ ch c q old (REC_POOL_CONFIG, [x; dec max]) (shape_of spc_verb) true
      (rec_record R REC_POOL_CONFIG [x; dec max]) (O0 ++ [(p1, n1); (p2, n2)]) HPRE1).
    + exact HFR0.
    + exact HFR4.
    + exact (spc_aro B MT HY _ _ O ly S W mem md _ _ _ _ _ _ _ HAR (spc_rep_in B ly S _ R O HREP) HJ4 HROD).
    + exact (cmd_ro_ok_of_aro ly4 S4 W4 (ms_mem ms0) _ HAR4'
        (spc_aro B MT HY _ _ O ly S W mem md _ _ _ _ _ _ _ HAR (spc_rep_in B ly S _ R O HREP) HJ4 HROD)).
    + exact A10.
    + unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
    + exact A11.
    + exact Sq.
    + rewrite U12. reflexivity.
    + exact HREPA.
    + exact Hold.
    + exact Hold64.
    + intros _. split; [exact HSHAPE | exact (proj1 (shape_of_facts spc_verb))].
    + intros _ _. exact (spc_slot_answer R REC_POOL_CONFIG [x; dec max] Hlen16).
    + unfold EV_SUP_POOL_CONFIG, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP, EV_REC_SHAPE_OF in *. lia.
    + rewrite <- HT. unfold LIVE_SUP_POOL_CONFIG, LIVE_ARG_I, LIVE_XSTRDUP in *. fold x t in HLIVE.
      unfold n1, n2, LIVE_XSTRDUP in *. lia.
    + rewrite <- HT. apply (mok_station MT S S4 (XM_SUP_POOL_CONFIG MT R name max) _ _ MTL HMOK HMLE4 XMA).
      unfold XM_SUP_POOL_CONFIG. fold x t. lia.
  - intros a (r & Hr & Har). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Har.
    + apply spc_awr_grec. unfold OFF_ANSWER, REC_SIZE in *. lia.
    + apply spc_awr_grec. unfold OFF_STATE, REC_SIZE in *. lia.
    + destruct (inFP_ablocks_fp_inv _ a (ex_intro _ r (conj Hr Har))) as (pb & nb & Hbq & Hpa).
      apply spc_filter_in in Hbq.
      assert (Hn4 : In (pb, nb) (ablocks B ly4 S4)) by exact (Hin4 _ (spc_rep_in B ly3 S3 _ _ _ HREP3 _ Hbq)).
      apply in_app_or in Hbq as [Hbq | Hbq].
      * right; left. split.
        -- replace a with (pb + (a - pb)) by lia. apply (spc_inFP_blk O pb nb (a - pb)); [exact (proj1 (proj1 (HO0 _) Hbq)) | lia].
        -- exists pb, nb. split; [exact Hn4 | exact Hpa].
      * destruct (spc_fb_in_dec (pb, nb) (ablocks B ly S)) as [HinS | HninS].
        -- (* a block record() freed that the allocator handed out again: one of the recorder's blocks at the entry *)
           assert (HFb : In (pb, nb) F).
           { destruct (spc_fb_in_dec (pb, nb) F) as [Hf | Hf]; [exact Hf|]. exfalso.
             destruct Hbq as [Eb | [Eb | []]]; rewrite <- Eb in HinS, Hf; [exact (Hb1 (conj HinS Hf)) | exact (Hb2 (conj HinS Hf))]. }
           right; left. split.
           ++ replace a with (pb + (a - pb)) by lia. apply (spc_inFP_blk O pb nb (a - pb)); [exact (HFO _ HFb) | lia].
           ++ exists pb, nb. split; [exact Hn4 | exact Hpa].
        -- right; right; left. exists pb, nb. split; [exact Hn4|]. split; [exact HninS | exact Hpa].
  - intros ly5 S5 W5 regs5 mem5 md5 _ a _ H1 H2. exfalso. rewrite WA in H2. lia. }
(* answer returned to the caller: the member's post *)
cbv beta. intros W5 c5 _ (fx2 & ly5 & S5 & regs5 & mem5 & md5 & Hfx2 & -> & HJ5 & HJa & HP5 & HK5).
destruct HK5 as (q1 & q2 & O' & B10 & Bq2 & B12 & Bnew & BBL & BREP & BO & BSTR & Bbb & BMLE).
pose proof HJ5 as (HAR5 & _).
rewrite <- HT in Bnew, BBL, BO, BSTR, Bbb, BMLE.
unfold spc_goal. rewrite A1.
apply (apost_baseF_intro (fx := fx) SEGS fx2 _ _ _ _ _ _ _ _ _ _ _ _ ly5 S5);
  [exact Hfx2 | eapply ajournal_mono_k; [exact HJ5 | unfold EV_SUP_POOL_CONFIG, EV_REC_SHAPE_OF; lia]
  | exact (aregs_preserved_trans _ _ _ HPT HP5) |].
unfold spc_post.
set (nq := Z.of_nat (length t) + 1) in *.
assert (HA : forall bq, In bq (ablocks B ly4 S4) <->
  (In bq (ablocks B ly S) /\ ~ In bq F) \/ bq = (p1, n1) \/ bq = (p2, n2)).
{ intros bq. rewrite <- (HA3 bq). split; intros H; [exact (Permutation_in _ Sperm H) | exact (Hin4 _ H)]. }
assert (Hsep : forall ly' S' (W' : world SEGS) mem' md', AR SEGS B ly' S' W' mem' md' -> spc_sep req_size (ablocks B ly' S')).
{ intros ly' S' W' mem' md' HA' b m p n Hb Hp Hne. pose proof (sep_blocks SEGS B LAWS ly' S' W' mem' md' b m p n HA' Hb Hp Hne) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. exact Hz. }
assert (Hpos : forall ly' S' (W' : world SEGS) mem' md', AR SEGS B ly' S' W' mem' md' -> spc_pos (ablocks B ly' S')).
{ intros ly' S' W' mem' md' HA' b m Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HA' Hb) as (_ & H4096 & _ & _ & _ & _ & Hn). lia. }
destruct (spc_final_blocks req_size (ablocks B ly S) (ablocks B ly4 S4) (ablocks B ly5 S5) O F O0 O' (p1, n1) (p2, n2) old q1 q2 nq
  (fun m Hm => req_size_pos m Hm) (spc_rep_in B ly S _ R O HREP) HFO HO0 HA Hb1 Hb2
  ltac:(intros Eq12; injection Eq12 as Eq1 _; exact (P12 (eq_sym Eq1)))
  (Hsep _ _ _ _ _ HAR4') (Hpos _ _ _ _ _ HAR4') Hold' BBL Bnew B12 BO (Hsep _ _ _ _ _ HAR5) (Hpos _ _ _ _ _ HAR5))
  as (G1 & G2 & G3 & G4 & G5 & G6).
exists (fst (rec_answer (rec_record R REC_POOL_CONFIG [x; dec max]) (REC_POOL_CONFIG, [x; dec max]) (shape_of spc_verb) true)), t, q2, O'.
split; [rewrite HT; unfold t; rewrite spc_model; apply surjective_pairing|].
split; [exact B10|]. split; [exact Bq2|]. split; [exact BREP|]. split; [exact G1|]. split; [exact G2|].
split; [exact G3|].
split; [exact G4|]. split; [exact BSTR|]. split; [exact G5|]. split; [exact G6|].
split.
{ unfold LIVE_SUP_POOL_CONFIG. fold x t. unfold LIVE_ARG_I. unfold n1, n2 in *. unfold LIVE_XSTRDUP in *. lia. }
apply (mle_weaken MT S S5 _ _ MTL (mle_station MT S S4 S5 _ _ MTL HMLE4 BMLE)).
unfold XM_SUP_POOL_CONFIG. fold x t. lia.
Qed.

End e.
End f.
End d.
