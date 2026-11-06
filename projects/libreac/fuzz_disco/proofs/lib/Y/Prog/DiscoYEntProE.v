(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 437 of its 472 lines of code are new or changed and 1243 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntSeat DiscoYEntProCuts DiscoYEntProSeat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pe_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 19%nat => SOff 32 0 | 27%nat => SOff AT_SH 0
  | _ => SOff (AT_X + r) 0
  end.
Definition pe_sr : list sv := map pe_x (seq 0 32).
Definition pe_vals (h : Z) (regs : bvmap 5 word) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ [w64 h].
Definition pe_acs : list YP09.chunk := [YP09.mkChunk 184 (CVal 8 (SOff (AT_X + 32) 0))].

Ltac pe_ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac pe_awr cx EA60 :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|];
apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
  [reflexivity
  | cbn [YP09.r_base]; rewrite EA60; lia
  | cbn [YP09.r_wlo]; unfold MFRAME, LLVMF_STK in *; lia
  | cbn [YP09.r_whi]; unfold MFRAME, LLVMF_STK in *; lia
  |];
repeat (apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]); apply awr_ok_nil.
Ltac pe_sr_get :=
  match goal with |- context [sr_get ?sr ?rr] =>
    let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.

Lemma pe_w64_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Lemma pe_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64).
pose proof (Z.add_lnot_diag x) as Hln.
assert (E : Z.lxor x (Z.ones 64) = (Z.lnot x) mod 2 ^ 64).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec x 0) as [->|Hne]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2 ^ 64)) with (2 ^ 64 - 1).
replace (Z.lnot x) with (- x - 1) by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma pe_not_denot : forall E (k : nat) (v c : Z), ew E k = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff k c) (SLit (-1))) = Z_to_bv 64 (dnot (v + c)).
Proof.
intros E k v c Hk Hv Hc. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E k v c Hk) by lia.
change (zcanon (-1)) with 18446744073709551615.
rewrite pe_lxor_ones by lia. unfold dnot. apply zcanon_id. unfold M64. lia.
Qed.
Lemma pe_and7_denot : forall E (k : nat) (v : Z), ew E k = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> v mod 8 = 0 ->
  sv_denot E (SAlu ALU_AND (SOff k 0) (SLit 7)) = Z_to_bv 64 0.
Proof.
intros E k v Hk Hv H8. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E k v 0 Hk) by lia.
rewrite (zcanon_id 7) by (unfold M64; lia).
replace (v + 0) with v by lia.
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
rewrite H8. apply zcanon_id. unfold M64. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pe_keep_garr : forall (W : world SEGS) (m m' : word -> option byte) (lo : Z) a l,
  (forall x, 0 <= x < 2 ^ 64 -> x < lo -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + Z.of_nat (length l) <= lo -> lo <= 2 ^ 64 ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
intros W m m' lo a l HK Ha Hal Hlo Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. assert (kk = 0) by lia. subst kk. rewrite Z.add_0_r. apply HK; lia.
Qed.

Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.
Hypothesis KCAN : ak_canary tfib_K = FF_canary.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Let DFACTS := d_facts_ok B MT XM_LIB RLO RHI tfib_K.
Let DLAND := d_land B MT XM_LIB RLO RHI tfib_K.

Lemma pe_ewx : forall cx E regs h (n j : nat), (n = AT_X + j)%nat -> (j < 32)%nat ->
  ew (d_env cx E (pe_vals h regs)) n = getr regs (Z_to_bv 5 (Z.of_nat j)).
Proof.
intros cx E regs h n j -> Hj.
rewrite (d_env_x cx E (pe_vals h regs) j
  ltac:(unfold pe_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia)).
unfold pe_vals. rewrite app_nth1 by (rewrite length_map, length_seq; exact Hj).
rewrite (nth_indep _ (Z_to_bv 64 0) (getr regs (Z_to_bv 5 (Z.of_nat 0))))
  by (rewrite length_map, length_seq; exact Hj).
rewrite (map_nth (fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) 0%nat j).
rewrite seq_nth by exact Hj. reflexivity.
Qed.
Lemma pe_ewh : forall cx E regs h (n : nat), (n = AT_X + 32)%nat ->
  ew (d_env cx E (pe_vals h regs)) n = w64 h.
Proof.
intros cx E regs h n ->.
rewrite (d_env_x cx E (pe_vals h regs) 32
  ltac:(unfold pe_vals; rewrite length_app, length_map, length_seq; cbn [length]; lia)).
unfold pe_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. replace (32 - 32)%nat with 0%nat by lia. reflexivity.
Qed.
Lemma pe_regs_ok : forall cx E regs h, d_E cx E ->
  spZ regs = d_A cx -> getr regs 8 = w64 (d_S cx) -> getr regs 9 = w64 (d_A cx) ->
  getr regs 19 = w64 SHADOW_OFF -> getr regs 27 = w64 (shadow_addr (d_FB cx)) ->
  regs_ok (d_env cx E (pe_vals h regs)) pe_sr regs.
Proof.
intros cx E regs h HE Hsp H8 H9 H19 H27.
destruct HE as (HER & H32 & _ & HA60 & HF516 & HSH529).
unfold w64 in *.
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_SH with 529%nat in HSH529.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite Z.add_0_r, HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite Z.add_0_r, HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite Z.add_0_r, H32, Z_to_bv_bv_unsigned; exact H19
          | rewrite Z.add_0_r, HSH529, Z_to_bv_bv_unsigned; exact H27 ]
  | rewrite Z.add_0_r; unfold d_env, havoc;
    cbn [ew Nat.ltb Nat.leb Nat.sub nth app pe_vals map seq Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ].
Qed.

Theorem pb_proE : pro_segE B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold pro_segE. intros cx h W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcanok & Hr5 & Hpf & Hbl & H184 & (T0 & G0 & Lk0 & H0 & Hobjs)).
pose proof Hr5 as ((Hsp & Hgp & Htp & H8 & H9 & H19 & H27) & H24 & H23).
destruct Hpf as (E & HdE & HRG & HFL).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (HAbove : alloc_ceiling <= d_A cx) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HA64 : 0 <= d_A cx <= 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof Hbase as (Hpre & Hext & Hcanary).
pose proof Hpre as (HPRE & Hra0 & H10 & H11 & Hpn & Hlen & Harr & Hfr0 & Hnev0 & Hbb & Harod & Hsink & Hfd & Hfs & Hmeta & Hmo0).
pose proof HPRE as (HAR0 & _).
assert (Hin3 : forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3)).
{ intros p n Hin. destruct Hbl as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)).
  right. exact Hin. }
assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ destruct Hbl as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & _).
unfold req_size, HUNT_SIZE in Hhceil. cbn [Z.eqb] in Hhceil.
assert (Hh64 : 0 <= h < 2 ^ 64) by (unfold HUNT_SIZE in *; clear - Hh4096 Hhceil C1; lia).
assert (Hh8 : h mod 8 = 0).
{ pose proof (Z.div_mod h 16 ltac:(lia)) as Hd. rewrite Hh16, Z.add_0_r in Hd.
  rewrite Hd. replace (16 * (h / 16)) with (2 * (h / 16) * 8) by lia. apply Z_mod_mult. }
assert (Hregs : regs_ok (d_env cx E (pe_vals h regs)) pe_sr regs)
  by (exact (pe_regs_ok cx E regs h HdE Hsp H8 H9 H19 H27)).
assert (E563 : ew (d_env cx E (pe_vals h regs)) 563 = w64 h)
  by (apply (pe_ewh cx E regs h 563); vm_compute; reflexivity).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E (pe_vals h regs)) (rd W mem3) (d_A cx)) pe_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 184 8%N (SOff (AT_X + 32) 0) h).
  - cbn [sv_denot]. rewrite Z.add_0_r.
    change (AT_X + 32)%nat with 563%nat. rewrite E563. unfold w64.
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hh64.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. exact H184. }
pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C3 ly3 S3 W regs mem3 md3 k E POFF_C5 pe_sr
  (pe_vals h regs) pe_acs [] [] (d_facts [] []) HctxD HdE HRG HFL Hregs
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (pe_vals h regs) [] [] HctxD HdE I I)
  Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_p in HS.
pe_ro_base HS 516%nat. pe_ro_base HS 529%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (pe_vals h regs))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env.
  rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
unfold cfg_at. change (w64 (BASE + POFF_C5)) with (Z_to_bv 64 (BASE + POFF_C5)).
assert (EA60 : bv_unsigned (ew (d_env cx E (pe_vals h regs)) 60) = d_A cx).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia).
  destruct HdE as (_ & _ & _ & HA & _). change AT_A with 60%nat in HA. rewrite HA.
  unfold w64. apply unsigned_lit_small. unfold MFRAME, LLVMF_STK in *. lia. }
assert (E32' : ew (d_env cx E (pe_vals h regs)) 32 = Z_to_bv 64 SHADOW_OFF).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & H32 & _). exact H32. }
assert (EF' : ew (d_env cx E (pe_vals h regs)) 516 = Z_to_bv 64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HF & _).
  unfold w64 in HF. exact HF. }
assert (ESH' : ew (d_env cx E (pe_vals h regs)) 529 = Z_to_bv 64 (shadow_addr (d_FB cx))).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & _ & HSa).
  unfold w64 in HSa. exact HSa. }
assert (E2' : ew (d_env cx E (pe_vals h regs)) 2 = Z_to_bv 64 (d_S cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (HER & _).
  rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (E534 : ew (d_env cx E (pe_vals h regs)) 534 = getr regs 3).
{ rewrite (pe_ewx cx E regs h 534 3 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (E535 : ew (d_env cx E (pe_vals h regs)) 535 = getr regs 4).
{ rewrite (pe_ewx cx E regs h 535 4 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (E554 : ew (d_env cx E (pe_vals h regs)) 554 = getr regs 23).
{ rewrite (pe_ewx cx E regs h 554 23 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (E555 : ew (d_env cx E (pe_vals h regs)) 555 = getr regs 24).
{ rewrite (pe_ewx cx E regs h 555 24 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (HFBhi : d_FB cx + 4096 < 2 ^ 64) by (clear - HFc C1; lia).
paj_run_to_sh RUNTO HS HJ HDR_OFF.
{ pe_awr cx EA60. }
lazymatch goal with |- SRr _ _ (mkCfg ?msv ?mdv) _ => set (md4 := mdv) in *; set (msF := msv) in * end.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a < d_A cx ->
  aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hout.
  assert (Hb : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  apply aview_eq_of. apply HFr.
  rewrite Hb. intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      first [ exfalso; lia | rewrite EA60 in Hr; exfalso; lia ] | ]).
  destruct Hin. }
pose proof (conj Hbase (conj HJ Hfrs)) as Hctx4.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ Hctx4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres4 & _ & _ & HARf & Hfin4 & Efa4 & _).
lazymatch type of HS with st_ok_pi _ _ _ ?ss ?msx =>
  let r := eval vm_compute in (nth 1 (ss_mem ss) got_regionP) in
  pose proof (st_ok_pi_region_nth _ ss msx 1 r HS ltac:(vm_compute; reflexivity)) as RFIN end.
destruct RFIN as (_ & _ & _ & RC).
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in RC. rewrite EA60 in RC.
assert (V184 : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 184) 8 h).
{ apply (val_of_chunk_ok SEGS _ _ (d_A cx) 184 8%N (SOff 563 0) h
    (proj1 (Forall_forall _ _) RC (YP09.mkChunk 184 (CVal 8 (SOff 563 0))) ltac:(cbn [In]; tauto))).
  - cbn [sv_denot]. rewrite Z.add_0_r, E563. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hh64.
  - cbn [Z.of_N]. lia. }
assert (V120 : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 120) 8 (h + 440)).
{ apply (val_of_chunk_ok SEGS _ _ (d_A cx) 120 8%N (SOff 563 440) (h + 440)
    (proj1 (Forall_forall _ _) RC (YP09.mkChunk 120 (CVal 8 (SOff 563 440))) ltac:(cbn [In]; tauto))).
  - cbn [sv_denot]. rewrite E563. unfold w64. rewrite pe_w64_add. reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. unfold HUNT_SIZE in *. lia.
  - cbn [Z.of_N]. lia. }
assert (V136 : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 136) 8 0).
{ apply (val_of_chunk_ok SEGS _ _ (d_A cx) 136 8%N (SAlu ALU_AND (SOff 563 0) (SLit 7)) 0
    (proj1 (Forall_forall _ _) RC (YP09.mkChunk 136 (CVal 8 (SAlu ALU_AND (SOff 563 0) (SLit 7)))) ltac:(cbn [In]; tauto))).
  - apply (pe_and7_denot _ 563%nat h); [exact E563 | exact Hh64 | exact Hh8].
  - cbn [Z.of_N]. change (8 * 8) with 64. lia.
  - cbn [Z.of_N]. lia. }
assert (V376 : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 376) 8 (dnot (d_obj cx OG))).
{ apply (val_of_chunk_ok SEGS _ _ (d_A cx) 376 8%N (SAlu ALU_XOR (SOff 516 2624) (SLit (-1))) (dnot (d_obj cx OG))
    (proj1 (Forall_forall _ _) RC (YP09.mkChunk 376 (CVal 8 (SAlu ALU_XOR (SOff 516 2624) (SLit (-1))))) ltac:(cbn [In]; tauto))).
  - unfold d_obj. cbn [dobj_off]. apply (pe_not_denot _ 516%nat (d_FB cx) 2624 EF'); lia.
  - cbn [Z.of_N]. change (8 * 8) with 64. unfold dnot, d_obj. cbn [dobj_off]. lia.
  - cbn [Z.of_N]. lia. }
assert (V280 : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 280) 8 (dnot (d_obj cx OT))).
{ apply (val_of_chunk_ok SEGS _ _ (d_A cx) 280 8%N (SAlu ALU_XOR (SOff 516 2160) (SLit (-1))) (dnot (d_obj cx OT))
    (proj1 (Forall_forall _ _) RC (YP09.mkChunk 280 (CVal 8 (SAlu ALU_XOR (SOff 516 2160) (SLit (-1))))) ltac:(cbn [In]; tauto))).
  - unfold d_obj. cbn [dobj_off]. apply (pe_not_denot _ 516%nat (d_FB cx) 2160 EF'); lia.
  - cbn [Z.of_N]. change (8 * 8) with 64. unfold dnot, d_obj. cbn [dobj_off]. lia.
  - cbn [Z.of_N]. lia. }
assert (V232 : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 232) 8 (dnot (d_obj cx OO))).
{ apply (val_of_chunk_ok SEGS _ _ (d_A cx) 232 8%N (SAlu ALU_XOR (SOff 516 240) (SLit (-1))) (dnot (d_obj cx OO))
    (proj1 (Forall_forall _ _) RC (YP09.mkChunk 232 (CVal 8 (SAlu ALU_XOR (SOff 516 240) (SLit (-1))))) ltac:(cbn [In]; tauto))).
  - unfold d_obj. cbn [dobj_off]. apply (pe_not_denot _ 516%nat (d_FB cx) 240 EF'); lia.
  - cbn [Z.of_N]. change (8 * 8) with 64. unfold dnot, d_obj. cbn [dobj_off]. lia.
  - cbn [Z.of_N]. lia. }
assert (V264 : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED))).
{ apply (val_of_chunk_ok SEGS _ _ (d_A cx) 264 8%N (SAlu ALU_XOR (SOff 516 1664) (SLit (-1))) (dnot (d_obj cx OUSED))
    (proj1 (Forall_forall _ _) RC (YP09.mkChunk 264 (CVal 8 (SAlu ALU_XOR (SOff 516 1664) (SLit (-1))))) ltac:(cbn [In]; tauto))).
  - unfold d_obj. cbn [dobj_off]. apply (pe_not_denot _ 516%nat (d_FB cx) 1664 EF'); lia.
  - cbn [Z.of_N]. change (8 * 8) with 64. unfold dnot, d_obj. cbn [dobj_off]. lia.
  - cbn [Z.of_N]. lia. }
destruct (DLAND LAWS FFL fq cx h dsh_loop ly3 S3 W md4 k (d_env cx E (pe_vals h regs)) _ msF
  Hctx4 (d_E_env cx E _ HdE) (d_env_fl cx E _) HS ltac:(vm_compute; reflexivity)
  V184 V120 V136 V376 V280 V232 V264) as (HFrame4 & HShadow4).
assert (HCORE : forall a, FF_canary <= a < FF_canary + 8 -> aenv_core tfib_K a).
{ intros a Ha. unfold aenv_core. right. right. right. rewrite KCAN. exact Ha. }
assert (HCANA : forall a, FF_canary <= a < FF_canary + 8 ->
  aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
{ intros a Ha. unfold aview.
  rewrite (aenv_kept SEGS B tfib_K AIL LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem msF) md4 k a HJ
    (aenv_of_core SEGS B tfib_K AIL a (or_introl (HCORE a Ha)))
    (fp_spares_off [] a (ail_env_static _ _ _ AIL a (ail_owned_core _ _ _ AIL a (HCORE a Ha))))).
  reflexivity. }
assert (HCANV : d_can cx W (ms_mem msF)).
{ unfold d_can. split.
  { apply (val_mem_kept SEGS (w_H (c_W cx)) (w_H W) (c_mem cx) (ms_mem msF) FF_canary 8 (c_canary cx)).
    - intros kk Hkk. apply HCANA. cbn [Z.of_nat] in Hkk. lia.
    - exact Hcanary. }
  split; [exact Hcanok|].
  intros a Ha. exact (proj1 (ail_env _ _ _ AIL a (aenv_of_core SEGS B tfib_K AIL a (or_introl (HCORE a Ha))))). }
pose proof HJ as (_ & Hlyf & _ & _ & _ & _ & _ & _ & _ & F2 & _ & _ & _ & _ & Hstkf & _).
pose proof Hstkf as (_ & _ & Hceil0 & Hslo0 & _).
pose proof Hlyf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo3 & Ehi3 & _).
pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ msF HS eq_refl) as Hms. cbn [ss_pc] in Hms.
apply SRr_ret. left. unfold loop_inv, d_at.
exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), md4, k, acc.
split; [unfold cfg_at, w64, HDR_OFF; rewrite <- Hms; reflexivity|].
split; [exact Hfrm|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|].
split; [unfold EV_HEAD, EV_ITER in *; lia|].
split; [unfold EV_HEAD, EV_ITER in *; lia|].
split; [exact Hmo|]. split; [unfold ACC_HEAD; lia|].
exists (p_n3 cx), 1000000000.
split; [unfold MAX_OPS; lia|]. split; [unfold p_n3; lia|]. split; [lia|].
split.
+ unfold d_rH, d_rL.
  repeat split.
  * unfold spZ. rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 2%bv HS).
    pe_sr_get. cbn [sv_denot]. rewrite EA60, Z.add_0_r. apply unsigned_lit_small.
    unfold MFRAME, LLVMF_STK in *; lia.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 3%bv HS). pe_sr_get. cbn [sv_denot].
    rewrite E534, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hgp.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 4%bv HS). pe_sr_get. cbn [sv_denot].
    rewrite E535, Z.add_0_r, Z_to_bv_bv_unsigned. exact Htp.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 8%bv HS). pe_sr_get. cbn [sv_denot].
    rewrite E2', Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 9%bv HS). pe_sr_get. cbn [sv_denot].
    rewrite Z.add_0_r. unfold w64. f_equal. exact EA60.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 19%bv HS). pe_sr_get. cbn [sv_denot].
    rewrite E32', Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 18%bv HS). pe_sr_get. cbn [sv_denot].
    unfold w64, WS_MASK. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 20%bv HS). pe_sr_get. cbn [sv_denot].
    unfold w64. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 27%bv HS). pe_sr_get. cbn [sv_denot].
    rewrite ESH', Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 22%bv HS). pe_sr_get. cbn [sv_denot].
    unfold w64. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 21%bv HS). pe_sr_get. cbn [sv_denot].
    unfold w64. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 14%bv HS). pe_sr_get. cbn [sv_denot].
    rewrite E554, H23, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 26%bv HS). pe_sr_get. cbn [sv_denot].
    unfold w64. reflexivity.
  * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 24%bv HS). pe_sr_get. cbn [sv_denot].
    rewrite E555, H24, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
+ pose proof Hobjs as (HTl & HT & HTok & HGl & HG' & HGok & HLl & HL & HLok & HOUR & HHl & HH & HHok & HHfst).
  exists T0, G0, Lk0, H0.
  split; [exact HFrame4|]. split; [exact HShadow4|].
  split.
  { unfold d_objs. split; [exact HTl|]. split.
    { apply (pe_keep_garr W mem3 (ms_mem msF) (d_A cx) _ _ KEEP); [unfold d_obj; cbn [dobj_off]; lia
      | rewrite length_map, HTl; unfold d_obj; cbn [dobj_off]; lia | lia | exact HT]. }
    split; [exact HTok|]. split; [exact HGl|]. split.
    { apply (pe_keep_garr W mem3 (ms_mem msF) (d_A cx) _ _ KEEP); [unfold d_obj; cbn [dobj_off]; lia
      | rewrite length_map, HGl; unfold d_obj; cbn [dobj_off]; lia | lia | exact HG']. }
    split; [exact HGok|]. split; [exact HLl|]. split.
    { apply (pe_keep_garr W mem3 (ms_mem msF) (d_A cx) _ _ KEEP); [unfold d_obj; cbn [dobj_off]; lia
      | rewrite length_map, HLl; unfold d_obj; cbn [dobj_off]; lia | lia | exact HL]. }
    split; [exact HLok|]. split.
    { apply (pe_keep_garr W mem3 (ms_mem msF) (d_A cx) _ _ KEEP); [unfold d_obj; cbn [dobj_off]; lia
      | rewrite length_map; unfold our_of; rewrite length_map, length_seq;
        unfold d_obj; cbn [dobj_off]; lia | lia | exact HOUR]. }
    split; [exact HHl|]. split.
    { apply (pe_keep_garr W mem3 (ms_mem msF) (d_A cx) _ _ KEEP); [lia
      | rewrite length_map, HHl; unfold HUNT_SIZE in *; lia | lia | exact HH]. }
    split; [exact HHok | exact HHfst]. }
  split; [exact Hbl|].
  split.
  { unfold d_input. split; [unfold p_n3; lia|]. split.
    { destruct Hpn as [(Hn0 & _) | (Hnpos & Hinb)].
      - assert (Hnil : c_pl cx = []) by (apply length_zero_iff_nil; lia).
        rewrite Hnil. cbn [map]. apply garr8_nil.
      - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinb) as (_ & Hp4096 & Hpceil & _).
        intros j Hj. rewrite length_map in Hj.
        destruct (Harr j ltac:(rewrite length_map; exact Hj)) as [Hv Hr]. split; [|exact Hr].
        apply (val_mem_kept SEGS (w_H (c_W cx)) (w_H W) (c_mem cx) (ms_mem msF) (c_p cx + Z.of_nat j) 1
          (nth j (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0)); [|exact Hv].
        intros kk Hkk. assert (kk = 0) by lia. subst kk. rewrite Z.add_0_r.
        apply (F2 (c_p cx) (c_n cx) (Z.of_nat j) Hinb (Hin3 _ _ Hinb)).
        + unfold req_size. destruct (c_n cx =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia|]. lia.
        + intros (r & Hr' & _). cbn [In] in Hr'. destruct Hr'. }
    intros Hpos. destruct Hpn as [(Hn0 & _) | (Hnpos & Hinb)]; [lia|].
    assert (Hoi : off_img (c_p cx) (req_size (c_n cx))) by (eapply blk_off_imgP; [exact HAR0 | exact Hinb]).
    unfold req_size in Hoi. destruct (c_n cx =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | exact Hoi]. }
  split.
  { unfold d_img. eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img);
      [exact HJ | exact (HRO _ Harod)]. }
  split; [exact HFo|].
  split.
  { unfold d_geo. split; [lia|]. split; [change (fs_frame_bytes DFRAME_CLASS) with 4096; lia|].
    split; [lia|]. split; [unfold HUNT_SIZE in *; lia|]. split; [lia|].
    split; [lia|]. split.
    { pose proof (sep_block_frame _ _ LAWS ly3 S3 W (ms_mem msF) md4 h HUNT_SIZE DFRAME_CLASS (c_fpos cx)
        HARf Hhin Hfin4) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      rewrite Efa4 in Hd. unfold req_size, HUNT_SIZE in Hd. cbn [Z.eqb] in Hd.
      change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. unfold HUNT_SIZE. lia. }
    intros Hpos. destruct Hpn as [(Hn0 & _) | (Hnpos & Hinb)]; [lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinb) as (_ & Hp4096 & Hpceil & _).
    unfold req_size in Hpceil. destruct (c_n cx =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia|].
    split; [lia|]. split; [lia|]. split.
    { pose proof (sep_block_frame _ _ LAWS ly3 S3 W (ms_mem msF) md4 (c_p cx) (c_n cx) DFRAME_CLASS (c_fpos cx)
        HARf (Hin3 _ _ Hinb) Hfin4) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      rewrite Efa4 in Hd. unfold req_size in Hd. rewrite Ez in Hd.
      change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. lia. }
    assert (Hne : (c_p cx, c_n cx) <> (h, HUNT_SIZE)).
    { intros Heq. destruct Hbl as (_ & Hnin & _). pose proof (Forall_inv Hnin) as Hni.
      apply Hni. rewrite <- Heq. exact Hinb. }
    pose proof (sep_blocks _ _ LAWS ly3 S3 W (ms_mem msF) md4 (c_p cx) (c_n cx) h HUNT_SIZE
      HARf (Hin3 _ _ Hinb) Hhin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size, HUNT_SIZE in Hd. rewrite Ez in Hd.
    cbn [Z.eqb] in Hd. unfold HUNT_SIZE. lia. }
  split; [exact HCANV|].
  split.
  { intros a Ha. left. change DFRAME_SIZE with 3072 in Ha.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. rewrite Elo3. lia. }
  intros a Ha. change DFRAME_SIZE with 3072 in Ha. split.
  { unfold awr_byte. right. right. right. unfold in_frames.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite Efa4.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  apply HFpres4. change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. lia.
Qed.
End h.
End f.
End d.
