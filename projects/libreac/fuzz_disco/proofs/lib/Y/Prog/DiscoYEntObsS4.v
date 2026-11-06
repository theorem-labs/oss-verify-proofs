(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v, with its module paths changed; 129 of its 204 lines of code are new or changed and 913 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntObsCuts CheckTable.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

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

Lemma o4_obT_pt : forall cx now Sg T T' ai ow ret (W : world SEGS) (m m' : word -> option byte),
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
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.
Hypothesis BCK : d_body_call_keep_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis TCHK : CheckTable.tcheck_table_spec B.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).

Theorem ob_s45 : ob_seg45 B MT XM_LIB RLO RHI tfib_K.
Proof.
clear XN_LIB. intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HOT & HRT & R10 & R22 & R21).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & _).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof alloc_ceiling_val as Hac.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof HOT as (LT & TOK & HFR & HOW & HSP & H360 & HOM).
assert (Hret : ret = 0 \/ ret = 1) by exact (slot_observe.obs_ret T Sg ow now T' ret LT HSgl (proj1 TOK) HOM).
pose proof (regs_ok_obs B cx E regs HdE HrL HAr2) as A1.
assert (E541 : ew (d_env cx E (obs_vals regs)) 541 = w64 ret).
{ change 541%nat with (AT_X + 10)%nat. rewrite oy_d_env_x by (unfold obs_vals; rewrite length_map, length_seq; lia).
  unfold obs_vals. cbn [nth map seq]. rewrite <- R10. f_equal; apply bv_eq; reflexivity. }
assert (HFA : facts_ok (d_env cx E (obs_vals regs)) (d_facts [(541%nat, mkAF 0 1 0)] [])).
{ apply (FACTS LAWS cx ly3 S3 W mem3 md3 k E _ _ [] HC HdE); [|exact I].
  cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E541.
  unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (SEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E OB_TO_RET obs_sr (obs_vals regs)
  [] [] [] (d_facts [(541%nat, mkAF 0 1 0)] []) HC HdE Hregs Hflag A1 HFA (Forall_nil _) (Forall_nil _)
  (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (oy_d_E_env cx E (obs_vals regs) HdE) as HdE'.
pose proof HdE' as (_ & _ & HEI & _ & HEF & _).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs)) (rd W mem3)) by constructor.
set (Ev := d_env cx E (obs_vals regs)) in *. clearbody Ev.
assert (D516 : forall q, sv_denot Ev (SOff 516 q) = Z_to_bv 64 (d_FB cx + q)).
{ intros q. cbn [sv_denot]. change 516%nat with AT_F. rewrite HEF. unfold w64. apply oy_w64_add_w. }
unfold ss_d in HS. ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + OB_TO_RET)) with (Z_to_bv 64 (BASE + OB_TO_RET)).
paj_run_tok RUN HS HJ SHOK OBspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pose proof (oy_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MEQ.
clear HF HFr HG.
rewrite (pa_sigma_check_table (PX := PX)) in HS.
lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
  assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_both3_check_table) msx) by exact HS end.
clear HS.
assert (GU : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r HSpi), (A1 r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (HrL' : d_rL B cx (ms_regs ms)).
{ destruct HrL as (L2 & L3 & L4 & L8 & L9 & L19 & L18 & L20 & L27). unfold d_rL, spZ in *.
  rewrite !GU by (cbv; tauto). repeat split; assumption. }
lazymatch type of HSpi with st_ok_pi _ _ _ ?ssy _ =>
  assert (GR : forall (r : bv 5) e, sr_get (ss_regs ssy) r = e -> getr (ms_regs ms) r = sv_denot Ev e)
    by (intros r e He; rewrite (st_ok_pi_restrict_reg _ _ _ ms r HSpi), He; reflexivity) end.
assert (G1 : getr (ms_regs ms) 1 = w64 (BASE + OB_CT_RET)).
{ rewrite (GR 1%bv (SOff 240 6236) ltac:(vm_compute; reflexivity)). cbn [sv_denot].
  rewrite (img_env_codeptr Ev HEI). reflexivity. }
assert (G10 : getr (ms_regs ms) 10 = w64 (d_obj cx OT))
  by (rewrite (GR 10%bv (SOff 516 2160) ltac:(vm_compute; reflexivity)), D516; reflexivity).
assert (G24 : getr (ms_regs ms) 24 = w64 (d_obj cx OT))
  by (rewrite (GR 24%bv (SOff 516 2160) ltac:(vm_compute; reflexivity)), D516; reflexivity).
assert (G23 : getr (ms_regs ms) 23 = w64 ret)
  by (rewrite (GR 23%bv (SOff 541 0) ltac:(vm_compute; reflexivity)), sv_denot_SOff0, E541; reflexivity).
pose proof (st_ok_pi_restrict_mkst (w_H W) Ev _ ms HSpi eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
apply SRr_ret.
unfold ob_c5, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md3) mat md3), k, acc.
split; [unfold cfg_at; rewrite Hms at 1; reflexivity|].
split; [exact HFRM0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact Hmo|]. split; [exact Hacc|].
exists T, T', ai, ow, ret.
split; [exact (oy_oc_pt B cx h i n now op nb fr len Sg T' regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) BRT MEQ HrL' HOC)|].
split; [exact (o4_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) MEQ HOT)|].
destruct HRT as (R25 & R26).
split; [split; rewrite GU by (cbv; tauto); assumption|].
split; [exact G1|]. split; [exact G10|]. split; [exact G23|]. split; [exact G24|].
split; rewrite GU by (cbv; tauto); assumption.
Qed.

Theorem ob_s56 : ob_seg56 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & HoT & HrT & Hra & Ha0 & H23 & H24 & H22 & H21).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & HREC &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcan & Hstk & Hawr).
assert (Hc3 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (oy_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc3)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof alloc_ceiling_val as Hac.
destruct (oy_d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HrL as (Hsp & _).
assert (FB8 : d_FB cx mod 8 = 0) by lia.
eapply SRr_mono.
{ apply (TCHK fq ly3 S3 W regs mem3 md3 [] (d_obj cx OT) T'
    (oy_pre8 B MT XM_LIB RLO RHI tfib_K cx regs ly3 S3 W mem3 md3 k TCHECK_TABLE_STK OB_CT_RET LAWS Hc3 HrL Hra
      ltac:(unfold OB_CT_RET; lia) ltac:(reflexivity)
      ltac:(unfold TCHECK_TABLE_STK, ESTACK; lia) ltac:(unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK; lia)) Himg Ha0).
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - exact HTl.
  - exact HT.
  - apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; unfold d_obj, dobj_off; lia |
      unfold d_obj, dobj_off; lia].
  - exact (oy_ra_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => oy_dsh_rec_t kk ltac:(lia))).
  - exact (oy_hull_frame cx dsh_rec W mem3 2160 400 Hshadow FB8 ltac:(lia) ltac:(lia) ltac:(lia)).
  - left. rewrite Hsp. unfold d_obj, dobj_off, TCHECK_TABLE_STK, ESTACK, LLVMF_STK in *. lia.
  - unfold off_img in *. unfold d_obj, dobj_off. lia.
  - exact (proj1 HTok).
  - exact (proj1 (proj2 HTok)).
  - exact (proj1 (proj2 (proj2 HTok))). }
cbv beta. intros W2 c2 _ HQ. unfold tcheck_table_post, apost_base in HQ.
destruct HQ as (fx' & ly4 & S4 & regs4 & mem4 & md4 & -> & HFxr & HFxc & HJ1 & HP & HPm & Hkept).
assert (HFRM1 : lib.Lib.FP.frm0 (@YK11.fp_csr fx')) by (destruct HFxc as [Ec|Ec]; [rewrite Ec; exact HFRM0 | exact Ec]).
rewrite Hsp in HJ1, Hkept.
pose proof (oy_post B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k TCHECK_TABLE_STK ly4 S4 W2 mem4 md4 LAWS Hc3
  ltac:(unfold TCHECK_TABLE_STK, ESTACK; lia) ltac:(unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK; lia) HJ1) as Hc4.
pose proof (oy_oc_call_keep B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 md3 k
  regs4 ly4 S4 W2 mem4 md4 (k + 0) TCHECK_TABLE_STK LAWS BCK Hc3 Hc4 HOC ltac:(unfold TCHECK_TABLE_STK, ESTACK; lia)
  ltac:(unfold TCHECK_TABLE_STK, ESTACK, LLVMF_STK; lia) Hkept HPm HP) as HOC4.
rewrite Hra.
apply (oy_dat B MT XM_LIB RLO RHI tfib_K cx OB_CT_RET kmax accmax _ fx' ly4 S4 regs4 mem4 md4 (k + 0) acc W2 MT_TRIV HFRM1 Hc4
  ltac:(lia) Hacc).
exists T, T', ai, ow, ret. split; [exact HOC4|].
split; [exact (oy_obT_keep cx now Sg T T' ai ow ret W W2 mem3 mem4 TCHECK_TABLE_STK Hkept
  ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HoT)|].
split; [destruct HrT as (R25 & R26); split;
  [transitivity (getr regs 25%bv); [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact R25]
  |transitivity (getr regs 26%bv); [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact R26]]|].
split; [transitivity (getr regs 23%bv); [exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact H23]|].
split; [transitivity (getr regs 24%bv); [exact (HP 24 ltac:(unfold acallee_saved; lia)) | exact H24]|].
split; [transitivity (getr regs 22%bv); [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact H22]|].
transitivity (getr regs 21%bv); [exact (HP 21 ltac:(unfold acallee_saved; lia)) | exact H21].
Qed.
End h.
End f.
End d.
