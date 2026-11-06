(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 1029 of its 1060 lines of code are new or changed and 38 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs2.v; 160 of its 242 lines of code are new or changed and 978 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat FindEntry DiscoEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_observe CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j.
From Stdlib Require Import FunctionalExtensionality.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition sr89_x (ai : Z) (r : nat) : sv :=
  match r with
  | 10%nat => SLit ai
  | _ => sr_x r
  end.
Definition sr89 (ai : Z) : list sv := map (sr89_x ai) (seq 0 32).
Definition ob89_fcs (ai : Z) : list YP09.chunk := [YP09.mkChunk (2168 + 48 * ai) (CVal 4 (SLit 1))].

Lemma ob89_sw1 : forall x, 0 <= x < 2 ^ 32 -> bv_swrap 32 x = 1 -> x = 1.
Proof.
intros x Hx H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
change (2 ^ Z.of_N 32) with 4294967296 in H. change (2 ^ (Z.of_N 32 - 1)) with 2147483648 in H. lia.
Qed.

Lemma ob89_S1 : forall Sg, disco_classify_c.sighting_ok Sg -> sighting_S1 Sg.
Proof.
intros Sg (HL & HR & _). unfold sighting_S1, s_role, s32_at, u_at.
change (sub Sg 8 4) with (CtrlParsed.fld Sg 8 4).
pose proof (bytes_le_to_Z_nonneg (CtrlParsed.fld Sg 8 4)) as H0.
pose proof (bytes_le_to_Z_bound (CtrlParsed.fld Sg 8 4)) as H1.
assert (HLf : length (CtrlParsed.fld Sg 8 4) = 4%nat) by (unfold CtrlParsed.fld; rewrite length_firstn, length_skipn; lia).
rewrite HLf in H1. change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in H1.
unfold CtrlParsed.fu, CtrlParsed.s32 in HR.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
destruct (Z.ltb_spec (bytes_le_to_Z (CtrlParsed.fld Sg 8 4)) (2 ^ 31)); lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ob89_u4 : forall H (m : word -> option byte) t (T : list byte) k, 0 <= k -> (Z.to_nat k + 4 <= length T)%nat ->
  garr8 SEGS (mrestrict H m) t (map bv_unsigned T) ->
  val_mem SEGS (mrestrict H m) (t + k) 4 (u_at T k 4).
Proof.
intros H m t T k Hk LT GT kk Hkk.
assert (Hlen : length (sub T k 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_bound (sub T k 4)) as Hb1. pose proof (bytes_le_to_Z_nonneg (sub T k 4)) as Hb0.
rewrite Hlen in Hb1.
destruct (nth_error T (Z.to_nat k + kk)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + k + Z.of_nat kk) with (t + Z.of_nat (Z.to_nat k + kk)) by lia.
rewrite (fe_garr8_nth _ t T (Z.to_nat k + kk) b GT Hb2). f_equal.
rewrite le_byte_small by first [lia | unfold u_at; split; [exact Hb0 | exact Hb1]].
rewrite <- (fe_sub_nth T (Z.to_nat k) 4 kk Hkk) in Hb2. rewrite Z2Nat.id in Hb2 by exact Hk.
pose proof (YA0j.nth_error_le_byte _ _ _ Hb2) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold u_at. rewrite <- Hv.
first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let DSEAT := d_seat B MT XM_LIB RLO RHI tfib_K.
Let DFACTS := d_facts_ok B MT XM_LIB RLO RHI tfib_K.
#[local] Notation oc := (oc B).
#[local] Notation ob_c9 := (ob_c9 B MT XM_LIB RLO RHI tfib_K).

Lemma regs_ok_89 : forall cx E regs ai, d_E cx E -> d_rL B cx regs ->
  0 <= d_A cx < 2 ^ 64 -> getr regs 10 = Z_to_bv 64 ai ->
  regs_ok (d_env cx E (obs_vals regs)) (sr89 ai) regs.
Proof.
intros cx E regs ai HE HL HA H10.
destruct HE as (HER & H32 & _ & HA60 & _ & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth obs_vals map seq Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot]; exact H10.
Qed.

Lemma ob89_post : forall cx h i n now op nb fr len Sg kmax accmax W (fq : YK11.FPState) ly3 S3 regs mem3 md' k acc
  (ms : machine_state) T T' ai ow ret,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  oc cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 -> getr regs 26 = w64 (d_obj cx OOUR) ->
  obT cx now Sg T T' ai ow ret W mem3 -> ob_rT T ai regs -> ob_rX nb fr len ret regs -> 0 <= ai ->
  ms = YK11.mkst (fx := fq) (ms_regs ms) (Z_to_bv 64 (BASE + 0x18b8)) (ms_mem ms) (YK11.seg_rom SEGS) ->
  (forall x, ms_mem ms x = mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r) ->
  getr (ms_regs ms) 13 = w64 (d_obj cx OT) ->
  SRr SEGS W (mkCfg ms md') (ob_c9 cx h i n now op nb fr len Sg kmax accmax).
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W fq ly3 S3 regs mem3 md' k acc ms T T' ai ow ret
  Hf0 HB HJ HF Hk Hev Hmo Hacc HOC H26 HobT HrT HrX Hai Hms Hpt RG R13.
assert (Em : ms_mem ms = mem3) by (apply functional_extensionality; exact Hpt).
assert (R2 := RG 2%bv ltac:(cbv; tauto)). assert (R3 := RG 3%bv ltac:(cbv; tauto)). assert (R4 := RG 4%bv ltac:(cbv; tauto)).
assert (R8 := RG 8%bv ltac:(cbv; tauto)). assert (R9 := RG 9%bv ltac:(cbv; tauto)). assert (R18 := RG 18%bv ltac:(cbv; tauto)).
assert (R19 := RG 19%bv ltac:(cbv; tauto)). assert (R20 := RG 20%bv ltac:(cbv; tauto)). assert (R21 := RG 21%bv ltac:(cbv; tauto)).
assert (R22 := RG 22%bv ltac:(cbv; tauto)). assert (R23 := RG 23%bv ltac:(cbv; tauto)). assert (R24 := RG 24%bv ltac:(cbv; tauto)).
assert (R25 := RG 25%bv ltac:(cbv; tauto)). assert (R26 := RG 26%bv ltac:(cbv; tauto)). assert (R27 := RG 27%bv ltac:(cbv; tauto)).
rewrite Em in HJ, Hms.
apply SRr_ret. unfold ob_c9, d_at.
exists fq, ly3, S3, (ms_regs ms), mem3, md', k, acc.
split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
split; [exact Hf0|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HF|]. split; [exact Hk|].
split; [exact Hev|]. split; [exact Hmo|]. split; [exact Hacc|].
exists T, T', ai, ow, ret.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- unfold oc. pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hrest).
  refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ Hrest)))))).
  destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
  rewrite R2, R3, R4, R8, R9, R18, R20, R25. repeat split; assumption.
- rewrite R26. exact H26.
- exact HobT.
- destruct HrT as (H19 & H22). unfold ob_rT. rewrite R19, R22. split; assumption.
- destruct HrX as (H21 & H23 & H24 & H27). unfold ob_rX. rewrite R21, R23, R24, R27. repeat split; assumption.
- exact Hai.
- exact R13.
Qed.

Theorem ob_s89 : ob_seg89 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & idx & HOC & H26 & HobT & HrT & HrX & Hai & Hrole & H10 & HFR2).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl' & HT' & HTok' & Hbody).
pose proof HobT as (HTl & HTok & HFR & How & Hsp22 & H408 & HOM).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (T1 : tbl_T1 T) by (destruct HTok as (T1 & _); exact T1).
assert (Eidx : idx = ai) by exact (slot_observe.known_find T Sg ow now T' ret ai idx HTl HSgl T1 HFR Hai HOM HFR2).
subst idx.
assert (Hai8 : ai < 8) by (unfold tbl_T1 in T1; destruct HFR as [[? _]|[? _]]; lia).
assert (S1 : sighting_S1 Sg) by (apply ob89_S1; destruct HSf as (_ & _ & _ & _ & _ & HSok & _); exact HSok).
pose proof (slot_observe.known_arm T Sg ow now T' ret ai HFR Hai HOM) as EK.
destruct (slot_observe.ok_facts T Sg ow now ai T' ret HTl HSgl ltac:(lia) EK) as (_ & _ & _ & E8 & _).
rewrite (slot_observe.c_role_box T Sg ai Hrole S1) in E8. cbv iota in E8.
assert (Hu1 : u_at T' (48 * ai + 8) 4 = 1).
{ unfold u_at. rewrite E8. apply ob89_sw1; [|exact Hrole].
  assert (Hl4 : length (sub T (48 * ai + 8) 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia).
  pose proof (bytes_le_to_Z_bound (sub T (48 * ai + 8) 4)) as Hb1.
  pose proof (bytes_le_to_Z_nonneg (sub T (48 * ai + 8) 4)) as Hb0.
  rewrite Hl4 in Hb1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb1. lia. }
assert (V1 : val_mem SEGS (rd W mem3) (d_FB cx + (2168 + 48 * ai)) 4 1).
{ pose proof (ob89_u4 (w_H W) mem3 (d_obj cx OT) T' (48 * ai + 8) ltac:(lia) ltac:(rewrite HTl'; lia) HT') as V.
  rewrite Hu1 in V. unfold d_obj in V. cbn [dobj_off] in V.
  replace (d_FB cx + (2168 + 48 * ai)) with (d_FB cx + 2160 + (48 * ai + 8)) by lia. exact V. }
assert (H10a : getr regs 10 = Z_to_bv 64 ai) by exact H10.
assert (HROK : regs_ok (d_env cx E (obs_vals regs)) (sr89 ai) regs) by exact (regs_ok_89 cx E regs ai HdE HrL HAr2 H10a).
assert (HFCS : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs)) (rd W mem3) (d_FB cx)) (ob89_fcs ai)).
{ unfold ob89_fcs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_FB cx) (2168 + 48 * ai) 4%N (SLit 1) 1).
  - reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact V1. }
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (EFB : ew (d_env cx E (obs_vals regs)) 516 = Z_to_bv 64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HF & _). exact HF. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs)) (rd W mem3)) by constructor.
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
assert (Hcase : ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
clear HFR2 E8 EK Hu1 V1 H10a.
destruct Hcase as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
all: pose proof (DSEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0x1874 (sr89 _) (obs_vals regs) [] (ob89_fcs _) []
    (d_facts [] []) HctxD HdE Hregs Hflag HROK
    (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs) [] [] HctxD HdE I I)
    (Forall_nil _) HFCS (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS;
  clear HFCS.
all: unfold ss_d in HS; ro_base HS 516%nat; ro_base HS 529%nat; ro_base HS 60%nat.
all: unfold cfg_at; change (w64 (BASE + 0x1874)) with (Z_to_bv 64 (BASE + 0x1874)).
all: paj_run_to_tok RUNTO HS HJ SHOK OBspan 0x18b8;
  [ cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil | ].
all: assert (Hpt := frame_of_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)); clear HF HFr HG.
all: pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ ms HS eq_refl) as Hms; cbn [ss_pc] in Hms.
all: assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms) r = getr regs r) by
  (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), (HROK r);
   cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr).
all: assert (R13 : getr (ms_regs ms) 13 = w64 (d_obj cx OT)) by
  (rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms 13%bv HS);
   match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
   cbn [sv_denot]; rewrite EFB, w64_add_w; reflexivity).
all: exact (ob89_post cx h i n now op nb fr len Sg kmax accmax W fq ly3 S3 regs mem3 _ k acc ms T T' _ ow ret
  Hf0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HOC H26 HobT HrT HrX ltac:(lia) Hms Hpt RG R13).
Qed.

End h.
End f.
End d.
