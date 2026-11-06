(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 1029 of its 1060 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs2.v, with its module paths, module names and numbers changed; 93 of its 155 lines of code are new or changed and 998 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma o10_S1 : forall S : list byte, disco_classify_c.sighting_ok S -> sighting_S1 S.
Proof.
intros S (HL & HR & HD).
assert (Hb : 0 <= CtrlParsed.fu S 8 4 < 2 ^ 32).
{ unfold CtrlParsed.fu, CtrlParsed.fld. pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn 8 S))).
  pose proof (bytes_le_to_Z_bound (firstn 4 (skipn 8 S))) as Hu. rewrite length_firstn, length_skipn, HL in Hu. cbn in Hu. lia. }
assert (SW : bv_swrap 32 (CtrlParsed.fu S 8 4) = CtrlParsed.s32 (CtrlParsed.fu S 8 4)).
{ unfold CtrlParsed.s32. change (bv_swrap 32 (CtrlParsed.fu S 8 4)) with ((CtrlParsed.fu S 8 4 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31).
  destruct (Z.ltb_spec (CtrlParsed.fu S 8 4) (2 ^ 31)); lia. }
unfold sighting_S1, s_role, s32_at. change (u_at S 8 4) with (CtrlParsed.fu S 8 4). rewrite SW. lia.
Qed.

Lemma o10_role1 : forall (T Sg T' : list byte) (ow now ret ai r : Z),
  length T = 400%nat -> length Sg = 24%nat -> disco_table_c.table_ok T ->
  disco_table_c.sighting_S1 Sg ->
  disco_table_c.find_res T (disco_table_c.s_mac Sg) ai -> 0 <= ai ->
  disco_table_c.role_of_e T ai = 1 ->
  reac_disco_table_observe_c.observe_model T Sg ow now T' ret ->
  disco_table_c.find_res T' (disco_table_c.s_mac Sg) r ->
  (if r <? 0 then -1 else disco_table_c.role_of_e T' r) = 1.
Proof.
intros T Sg T' ow now ret ai r LT LS (T1 & T2 & T3 & T4) S1 FR Hai Hrole OM FR2.
pose proof (slot_observe.known_find T Sg ow now T' ret ai r LT LS T1 FR Hai OM FR2) as ->.
replace (ai <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
assert (Hr8 : 0 <= ai < 8) by (pose proof T1 as T1'; unfold tbl_T1 in T1'; destruct FR as [[? _]|[? _]]; lia).
pose proof (slot_observe.known_arm T Sg ow now T' ret ai FR Hai OM) as E.
destruct (slot_observe.ok_facts T Sg ow now ai T' ret LT LS Hr8 E) as (_ & _ & _ & E8 & _).
rewrite (slot_observe.c_role_box T Sg ai Hrole S1) in E8.
unfold role_of_e, s32_at, u_at in *. rewrite E8. exact Hrole.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Context {PX : PAXcalls lib_both3_0_listing}.

Lemma o10_obT_pt : forall cx now Sg T T' ai ow ret (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) -> obT cx now Sg T T' ai ow ret W m -> obT cx now Sg T T' ai ow ret W m'.
Proof.
intros cx now Sg T T' ai ow ret W m m' HM (LT & TO & FR & HOW & SP & V360 & OM).
pose proof (oy_mrestrict_ext (w_H W) m m' HM) as Hpt.
destruct SP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11).
refine (conj LT (conj TO (conj FR (conj HOW (conj _ (conj (oy_val_mem_pt _ _ _ _ _ Hpt V360) OM)))))).
exact (conj (oy_val_mem_pt _ _ _ _ _ Hpt S1) (conj (oy_val_mem_pt _ _ _ _ _ Hpt S2) (conj (oy_val_mem_pt _ _ _ _ _ Hpt S3)
  (conj (oy_val_mem_pt _ _ _ _ _ Hpt S4) (conj (oy_val_mem_pt _ _ _ _ _ Hpt S5) (conj (oy_val_mem_pt _ _ _ _ _ Hpt S6)
  (conj (oy_val_mem_pt _ _ _ _ _ Hpt S7) (conj (oy_val_mem_pt _ _ _ _ _ Hpt S8) (conj (oy_val_mem_pt _ _ _ _ _ Hpt S9)
  (conj (oy_val_mem_pt _ _ _ _ _ Hpt S10) (oy_val_mem_pt _ _ _ _ _ Hpt S11))))))))))).
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.

Theorem ob_s89 : ob_seg89 B MT XM_LIB RLO RHI tfib_K.
Proof.
clear XN_LIB. intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & r & v & HOC & HOT & HRT & R23 & Hai & Hrole & R10 & HFR2 & Hv).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof alloc_ceiling_val as Hac.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof HOT as (LT & TOK & HFR & HOW & HSP & H360 & HOM).
assert (S1 : sighting_S1 Sg) by (apply o10_S1; destruct HSf as (_ & _ & _ & _ & _ & HSok & _); exact HSok).
assert (Hv1 : v = 1) by (rewrite Hv; exact (o10_role1 T Sg T' ow now ret ai r LT HSgl TOK S1 HFR Hai Hrole HOM HFR2)).
rewrite Hv1 in R10. clear Hv Hv1.
pose proof (regs_ok_obs B cx E regs HdE HrL HAr2) as A1.
assert (E541 : ew (d_env cx E (obs_vals regs)) 541 = w64 1).
{ change 541%nat with (AT_X + 10)%nat. rewrite oy_d_env_x by (unfold obs_vals; rewrite length_map, length_seq; lia).
  unfold obs_vals. cbn [nth map seq]. rewrite <- R10. f_equal; apply bv_eq; reflexivity. }
assert (HFA : facts_ok (d_env cx E (obs_vals regs)) (d_facts [(541%nat, mkAF 1 1 0)] [])).
{ apply (FACTS LAWS cx ly3 S3 W mem3 md3 k E _ _ [] HC HdE); [|exact I].
  cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E541.
  unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_RO_RET obs_sr (obs_vals regs)
  [] [] [] (d_facts [(541%nat, mkAF 1 1 0)] []) HC HdE Hregs Hflag A1 HFA (Forall_nil _) (Forall_nil _)
  (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (oy_d_E_env cx E (obs_vals regs) HdE) as HdE'.
pose proof HdE' as (_ & _ & HEI & _ & HEF & _).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs)) (rd W mem3)) by constructor.
set (Ev := d_env cx E (obs_vals regs)) in *. clearbody Ev.
unfold ss_d in HS. ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + OB_RO_RET)) with (Z_to_bv 64 (BASE + OB_RO_RET)).
paj_run_to_tok RUNTO HS HJ SHOK OBspan OB_C9.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MEQ.
clear HF HFr HG.
assert (GU : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 23; 25; 26; 27]%bv -> getr (ms_regs ms) r0 = getr regs r0).
{ intros r0 Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r0 HS), (A1 r0).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (HrL' : d_rL B cx (ms_regs ms)).
{ destruct HrL as (L2 & L3 & L4 & L8 & L9 & L19 & L18 & L20 & L27). unfold d_rL, spZ in *.
  rewrite !GU by (cbv; tauto). repeat split; assumption. }
pose proof (st_ok_pi_restrict_mkst (w_H W) Ev _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms.
apply SRr_ret.
unfold ob_c9, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms). eexists. exists k, acc.
split; [unfold cfg_at; rewrite Hms at 1; reflexivity|].
split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
exists T, T', ai, ow, ret.
split; [exact (oy_oc_pt B cx h i n now op nb fr len Sg T' regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) BRT MEQ HrL' HOC)|].
split; [exact (o10_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) MEQ HOT)|].
destruct HRT as (R25 & R26).
split; [rewrite GU by (cbv; tauto); exact R25|].
split; [rewrite GU by (cbv; tauto); exact R23|].
exact Hai.
Qed.
End h.
End f.
End d.
