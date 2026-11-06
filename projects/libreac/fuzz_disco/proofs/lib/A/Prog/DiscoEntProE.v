(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 481 of its 517 lines of code are new or changed and 1242 lines of the source are left out. *)
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
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntProCuts DiscoEntProSeat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pe_x (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 18%nat => SOff 32 0
  | 20%nat => SOff AT_F 32 | 22%nat => SOff AT_F 2992 | 24%nat => SOff AT_F 0 | 25%nat => SOff AT_F 0
  | 26%nat => SOff AT_F 2128
  | _ => SOff (AT_X + r) 0
  end.
Ltac pe_ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Definition pe_sr : list sv := map pe_x (seq 0 32).
Definition pe_vals (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32).
Definition pe_acs : list YP09.chunk := [YP09.mkChunk 216 (CVal 8 (SOff (AT_X + 19) 0))].
Definition PEspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma pe_w64_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.
Definition pe_shv (o : Z) : sv := SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff AT_F o) (SLit 3)).
Definition pe_fixv (v : sv) : sv :=
  if sv_eqb v (pe_shv 2200) then SOff AT_SH 275
  else if sv_eqb v (pe_shv 2160) then SOff AT_SH 270 else v.
Definition pe_fixc (c : YP09.chunk) : YP09.chunk :=
  match YP09.c_val c with
  | CVal w v => YP09.mkChunk (YP09.c_off c) (CVal w (pe_fixv v))
  | _ => c
  end.
Definition pe_fixr (r : YP09.region) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
    (map pe_fixc (YP09.r_chunks r)).
Lemma pe_sh_denot : forall E (p b s : nat) (pv B o : Z),
  ew E p = Z_to_bv 64 pv -> 0 <= pv -> pv mod 8 = 0 -> 0 <= o -> pv + o < 2 ^ 64 ->
  ew E b = Z_to_bv 64 B -> ew E s = Z_to_bv 64 (B + pv / 8) -> 0 <= B -> B + pv / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff b 0) (SAlu ALU_SRL (SOff p o) (SLit 3))) = sv_denot E (SOff s (o / 8)).
Proof.
intros E p b s pv B o Hp Hpv Hmod Ho Hpo Hb Hs HB0 HBhi. apply U_inj.
assert (Hdp : 0 <= pv / 8) by (apply Z.div_pos; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hp, Hb, Hs.
rewrite (unsigned_lit_small pv) by lia.
rewrite (unsigned_lit_small B) by lia.
rewrite (unsigned_lit_small (B + pv / 8)) by lia.
rewrite Z.add_0_r.
rewrite (zcanon_id B) by (unfold M64; lia).
rewrite (zcanon_id (pv + o)) by (unfold M64; lia).
assert (Hd : (pv + o) / 8 = pv / 8 + o / 8).
{ pose proof (Z.div_mod pv 8 ltac:(lia)) as Hdm. rewrite Hmod, Z.add_0_r in Hdm.
  rewrite Hdm at 1. rewrite (Z.mul_comm 8 (pv / 8)), Z.div_add_l by lia. reflexivity. }
rewrite Hd. f_equal. lia.
Qed.
Lemma pe_fixv_denot : forall E FB,
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E AT_F = Z_to_bv 64 FB -> 0 <= FB -> FB mod 32 = 0 -> FB + 4096 < 2 ^ 64 ->
  ew E AT_SH = Z_to_bv 64 (SHADOW_OFF + FB / 8) ->
  forall v, sv_denot E (pe_fixv v) = sv_denot E v.
Proof.
intros E FB E32 EF HF0 HF32 HFhi ESH v. unfold pe_fixv.
assert (Hm8 : FB mod 8 = 0).
{ pose proof (Z.div_mod FB 32 ltac:(lia)) as Hdm. rewrite HF32, Z.add_0_r in Hdm.
  rewrite Hdm. replace (32 * (FB / 32)) with (4 * (FB / 32) * 8) by lia. apply Z_mod_mult. }
assert (Hdv : 0 <= FB / 8 <= FB) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
destruct (sv_eqb v (pe_shv 2200)) eqn:E1.
{ rewrite (sv_eqb_denot E _ _ E1). unfold pe_shv. symmetry.
  change (SOff AT_SH 275) with (SOff AT_SH (2200 / 8)).
  exact (pe_sh_denot E AT_F 32 AT_SH FB SHADOW_OFF 2200 EF HF0 Hm8 ltac:(lia) ltac:(lia) E32 ESH
    ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)). }
destruct (sv_eqb v (pe_shv 2160)) eqn:E2.
{ rewrite (sv_eqb_denot E _ _ E2). unfold pe_shv. symmetry.
  change (SOff AT_SH 270) with (SOff AT_SH (2160 / 8)).
  exact (pe_sh_denot E AT_F 32 AT_SH FB SHADOW_OFF 2160 EF HF0 Hm8 ltac:(lia) ltac:(lia) E32 ESH
    ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)). }
reflexivity.
Qed.
Lemma pe_fixc_ok : forall segs E m base c, (forall v, sv_denot E (pe_fixv v) = sv_denot E v) ->
  YP09.chunk_ok segs E m base c -> YP09.chunk_ok segs E m base (pe_fixc c).
Proof.
intros segs E m base c Hfix H. destruct c as [off cv]. destruct cv as [w v|l|l|d s l];
  cbn [pe_fixc YP09.c_val YP09.c_off]; try exact H.
intros i Hi. cbn [YP09.c_len YP09.c_val cv_len] in Hi |- *.
destruct (H i ltac:(cbn [YP09.c_len YP09.c_val cv_len]; exact Hi)) as (b & Hb1 & Hb2).
exists b. cbn [YP09.c_off YP09.c_val cbyte] in Hb1 |- *. rewrite Hfix. split; [exact Hb1 | exact Hb2].
Qed.
Lemma pe_fixr_ok : forall segs E m r, (forall v, sv_denot E (pe_fixv v) = sv_denot E v) ->
  region_ok segs E m r -> region_ok segs E m (pe_fixr r).
Proof.
intros segs E m r Hfix (H1 & H2 & H3 & H4). unfold region_ok, pe_fixr. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in H1, H2, H3, H4 |- *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (c0 & <- & Hc0).
exact (pe_fixc_ok segs E m _ c0 Hfix (proj1 (Forall_forall _ _) H4 _ Hc0)).
Qed.
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


Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pe_regs_ok : forall cx E regs, d_E cx E ->
  spZ regs = d_A cx -> getr regs 8 = w64 (d_S cx) -> getr regs 9 = w64 (d_A cx) -> getr regs 18 = w64 SHADOW_OFF ->
  getr regs 20 = w64 (d_FB cx + 32) -> getr regs 22 = w64 (d_obj cx OS) -> getr regs 24 = w64 (d_FB cx) ->
  getr regs 25 = w64 (d_FB cx) -> getr regs 26 = w64 (d_obj cx OOUR) ->
  regs_ok (d_env cx E (pe_vals regs)) pe_sr regs.
Proof.
intros cx E regs HE Hsp H8 H9 H18 H20 H22 H24 H25 H26.
destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
unfold d_obj in H22, H26. cbn [dobj_off] in H22, H26. unfold w64 in *.
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite Z.add_0_r, HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite Z.add_0_r, HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite Z.add_0_r, H32, Z_to_bv_bv_unsigned; exact H18
          | rewrite HF516, pe_w64_add; first [exact H20 | exact H22 | exact H26 | rewrite Z.add_0_r; first [exact H24 | exact H25]] ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth pe_vals map seq Nat.add AT_X AT_FL];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ].
Qed.
Lemma pe_ewx : forall cx E regs (n j : nat), (n = AT_X + j)%nat -> (j < 32)%nat ->
  ew (d_env cx E (pe_vals regs)) n = getr regs (Z_to_bv 5 (Z.of_nat j)).
Proof.
intros cx E regs n j -> Hj.
rewrite (d_env_x cx E (pe_vals regs) j ltac:(unfold pe_vals; rewrite length_map, length_seq; exact Hj)).
unfold pe_vals.
rewrite (nth_indep _ (Z_to_bv 64 0) (getr regs (Z_to_bv 5 (Z.of_nat 0))))
  by (rewrite length_map, length_seq; exact Hj).
rewrite (map_nth (fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) 0%nat j).
rewrite seq_nth by exact Hj. reflexivity.
Qed.
Lemma pe_keep_garr : forall (W : world SEGS) (m m' : word -> option byte) (lo : Z) a l,
  (forall x, 0 <= x < 2 ^ 64 -> x < lo -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + Z.of_nat (length l) <= lo -> lo <= 2 ^ 64 ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
intros W m m' lo a l HK Ha Hal Hlo Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. assert (kk = 0) by lia. subst kk. rewrite Z.add_0_r. apply HK; lia.
Qed.
Lemma pe_bne : forall E k (n : Z), ew E k = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = negb (n =? 0).
Proof.
intros E k n Hk Hn. rewrite branch_ne_U, U_SOff, U_lit by lia.
rewrite Hk, unsigned_lit_small by lia. rewrite Z.add_0_r, zcanon_id by (unfold M64; lia). reflexivity.
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
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis CANH : d_can_hyps B tfib_K.
Let DFACTS := d_facts_ok B MT XM_LIB RLO RHI tfib_K.
Let DLAND := d_land B MT XM_LIB RLO RHI tfib_K.

Theorem pb_proE : pro_segE B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold pro_segE. intros cx h W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan0 & Hr5 & Hpf & Hbl & H216 & (T0 & G0 & Lk0 & H0 & Hobjs)).
pose proof Hr5 as ((Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H22 & H24 & H25 & H26) & H19 & H21 & H27).
destruct Hpf as (E & HdE & HRG & HFL).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (Hh64 : 0 <= h < 2 ^ 64).
{ destruct Hbl as (Hperm & _). assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & H4096 & Hceilb & _).
  unfold req_size, HUNT_SIZE in *. cbn in Hceilb. clear - H4096 Hceilb C1. lia. }
assert (Hregs : regs_ok (d_env cx E (pe_vals regs)) pe_sr regs) by (exact (pe_regs_ok cx E regs HdE Hsp H8 H9 H18 H20 H22 H24 H25 H26)).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E (pe_vals regs)) (rd W mem3) (d_A cx)) pe_acs).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (d_A cx) 216 8%N (SOff (AT_X + 19) 0) h).
  - cbn [sv_denot]. rewrite Z.add_0_r. rewrite (d_env_x cx E (pe_vals regs) 19 ltac:(cbn; lia)).
    cbn [pe_vals map seq nth].
    assert (E19 : getr regs (Z_to_bv 5 (Z.of_nat 19)) = getr regs 19) by (f_equal; vm_compute; reflexivity).
    rewrite E19, H19. unfold w64.
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hh64.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. exact H216. }
pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C5 ly3 S3 W regs mem3 md3 k E POFF_C5 pe_sr
  (pe_vals regs) pe_acs [] [] (d_facts [] []) HctxD HdE HRG HFL Hregs
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (pe_vals regs) [] [] HctxD HdE I I)
  Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_p in HS.
pe_ro_base HS 516%nat. pe_ro_base HS 529%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (pe_vals regs))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (pe_vals regs)) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + POFF_C5)) with (Z_to_bv 64 (BASE + POFF_C5)).
assert (EA60 : bv_unsigned (ew (d_env cx E (pe_vals regs)) 60) = d_A cx).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia).
  destruct HdE as (_ & _ & _ & HA & _). change AT_A with 60%nat in HA. rewrite HA.
  unfold w64. apply unsigned_lit_small. unfold MFRAME, LLVMF_STK in *. lia. }
assert (E32' : ew (d_env cx E (pe_vals regs)) 32 = Z_to_bv 64 SHADOW_OFF).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & H32 & _). exact H32. }
assert (EF' : ew (d_env cx E (pe_vals regs)) 516 = Z_to_bv 64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HF & _).
  unfold w64 in HF. exact HF. }
assert (ESH' : ew (d_env cx E (pe_vals regs)) 529 = Z_to_bv 64 (SHADOW_OFF + d_FB cx / 8)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & _ & HS').
  unfold w64, shadow_addr in HS'. exact HS'. }
assert (HAbove : alloc_ceiling <= d_A cx) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HA64 : 0 <= d_A cx <= 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof Hbase as (Hpre & Hext).
pose proof Hpre as (HPRE & Hra0 & H10 & H11 & Hpn & Hlen & Harr & Hfr0 & Hnev0 & Hbb & Harod & Hsink & Hfd & Hfs & Hmeta & Hmo0).
pose proof HPRE as (HAR0 & _).
assert (Hin3 : forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3)).
{ intros p n Hin. destruct Hbl as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)).
  right. exact Hin. }
assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ destruct Hbl as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & _).
unfold req_size, HUNT_SIZE in Hhceil. cbn [Z.eqb] in Hhceil.
assert (E550 : ew (d_env cx E (pe_vals regs)) 550 = getr regs 19).
{ rewrite (pe_ewx cx E regs 550 19 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (E552 : ew (d_env cx E (pe_vals regs)) 552 = getr regs 21).
{ rewrite (pe_ewx cx E regs 552 21 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (E558 : ew (d_env cx E (pe_vals regs)) 558 = getr regs 27).
{ rewrite (pe_ewx cx E regs 558 27 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (E534 : ew (d_env cx E (pe_vals regs)) 534 = getr regs 3).
{ rewrite (pe_ewx cx E regs 534 3 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (E535 : ew (d_env cx E (pe_vals regs)) 535 = getr regs 4).
{ rewrite (pe_ewx cx E regs 535 4 ltac:(vm_compute; reflexivity) ltac:(lia)). f_equal; vm_compute; reflexivity. }
assert (E2' : ew (d_env cx E (pe_vals regs)) 2 = Z_to_bv 64 (d_S cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (HER & _).
  rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
paj_run_tok RUN HS HJ SHOK PEspan.
{ pe_awr cx EA60. }
rename HFr into HFr1. clear HF HG.
psrr_branch_tok RUN BR HS SHOK PEspan.
- assert (Hn3 : p_n3 cx <> 0).
  { intros Hz. rewrite (pe_bne (d_env cx E (pe_vals regs)) 558 (p_n3 cx)
      ltac:(rewrite E558, H27; reflexivity) ltac:(unfold p_n3 in *; lia)) in Hc.
    rewrite Hz in Hc. cbn in Hc. discriminate Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK PEspan 0x840.
  { pe_awr cx EA60. }
  lazymatch goal with |- SRr _ _ (mkCfg ?msv ?mdv) _ => set (md4 := mdv) in *; set (msF := msv) in * end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a < d_A cx ->
    aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem3 a).
  { intros a Ha Hout.
    assert (Hb : bv_unsigned (Z_to_bv 64 a) = a).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
    etransitivity; [apply aview_eq_of; apply HFr | apply aview_eq_of; apply HFr1];
      rewrite Hb; intros (r & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
      repeat (destruct Hin as [<-|Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
          first [ exfalso; lia | rewrite EA60 in Hr; exfalso; lia ] | ]);
      destruct Hin. }
  pose proof (conj Hbase (conj HJ Hfrs)) as Hctx4.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ Hctx4)
    as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres4 & _ & _ & HARf & Hfin4 & Efa4 & _).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let r := eval vm_compute in (nth 1 (ss_mem ss) got_regionP) in
    pose proof (st_ok_pi_region_nth _ ss _ 1 r HS ltac:(vm_compute; reflexivity)) as RA;
    pose proof (pe_fixr_ok _ _ _ r (pe_fixv_denot _ (d_FB cx) E32' EF' ltac:(lia) HFal ltac:(lia) ESH') RA) as RAX;
    pose proof (ast_ok_pi_set_region _ ss _ 1 r (pe_fixr r) HS ltac:(vm_compute; reflexivity) eq_refl
      ltac:(vm_compute; reflexivity) RAX) as HS3 end.
  clear HS RA RAX. rename HS3 into HS. norm_ss HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss ?msx =>
    let r := eval vm_compute in (nth 1 (ss_mem ss) got_regionP) in
    pose proof (st_ok_pi_region_nth _ ss msx 1 r HS ltac:(vm_compute; reflexivity)) as RFIN end.
  destruct RFIN as (_ & _ & _ & RC).
  cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in RC. rewrite EA60 in RC.
  assert (H216' : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 216) 8 h).
  { apply (val_of_chunk_ok SEGS _ _ (d_A cx) 216 8%N (SOff 550 0) h
      (proj1 (Forall_forall _ _) RC (YP09.mkChunk 216 (CVal 8 (SOff 550 0))) ltac:(cbn [In]; tauto))).
    - cbn [sv_denot]. rewrite E550, H19, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - cbn [Z.of_N]. change (8 * 8) with 64. lia.
    - cbn [Z.of_N]. lia. }
  assert (H152' : val_mem SEGS (rd W (ms_mem msF)) (d_A cx + 152) 8 (h + 440)).
  { apply (val_of_chunk_ok SEGS _ _ (d_A cx) 152 8%N (SOff 550 440) (h + 440)
      (proj1 (Forall_forall _ _) RC (YP09.mkChunk 152 (CVal 8 (SOff 550 440))) ltac:(cbn [In]; tauto))).
    - cbn [sv_denot]. rewrite E550, H19. unfold w64. rewrite pe_w64_add. reflexivity.
    - cbn [Z.of_N]. change (8 * 8) with 64. lia.
    - cbn [Z.of_N]. lia. }
  destruct (DLAND LAWS FFL fq cx h dsh_loop ly3 S3 W md4 k (d_env cx E (pe_vals regs)) _ msF
    Hctx4 (d_E_env cx E _ HdE) (d_env_fl cx E _) HS ltac:(vm_compute; reflexivity) H216' H152')
    as (HFrame4 & HShadow4).
  pose proof HJ as (_ & Hlyf & _ & _ & _ & _ & _ & _ & _ & F2 & _ & _ & _ & _ & Hstkf & _).
  pose proof Hstkf as (_ & _ & Hceil0 & Hslo0 & _).
  pose proof Hlyf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo3 & Ehi3 & _).
  pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ msF HS eq_refl) as Hms. cbn [ss_pc] in Hms.
  apply SRr_ret. left. unfold loop_inv, d_at.
  exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), md4, k, acc.
  split; [unfold cfg_at, w64, HDR_OFF; rewrite <- Hms; reflexivity|]. split; [exact Hf0|].
  split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|].
  split; [unfold EV_HEAD, EV_ITER in *; lia|].
  split; [unfold EV_HEAD, EV_ITER in *; lia|].
  split; [exact Hmo|]. split; [unfold ACC_HEAD; lia|].
  exists (p_n3 cx), 1000000000.
  split; [unfold MAX_OPS; lia|]. split; [unfold p_n3 in *; lia|]. split; [lia|].
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
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 18%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite E32', Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 20%bv HS). pe_sr_get. cbn [sv_denot].
      unfold w64, WS_MASK. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 25%bv HS). pe_sr_get. cbn [sv_denot].
      unfold w64. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 19%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite E550, H19, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 6%bv HS). pe_sr_get. cbn [sv_denot].
      unfold w64. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 7%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite E558, H27, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 11%bv HS). pe_sr_get. cbn [sv_denot].
      unfold w64. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 14%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite EF', pe_w64_add. unfold d_obj, w64. cbn [dobj_off]. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 21%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite E552, H21, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 22%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite EF', pe_w64_add. unfold d_obj, w64. cbn [dobj_off]. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 26%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite EF', pe_w64_add. unfold d_obj, w64. cbn [dobj_off]. reflexivity.
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
        | rewrite length_map, length_our; unfold d_obj; cbn [dobj_off]; lia | lia | exact HOUR]. }
      split; [exact HHl|]. split.
      { apply (pe_keep_garr W mem3 (ms_mem msF) (d_A cx) _ _ KEEP); [lia
        | rewrite length_map, HHl; lia | lia | exact HH]. }
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
      split; [lia|]. split; [unfold HUNT_SIZE; lia|]. split; [lia|].
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
    split.
    { destruct CANH as (AIL & Ecan).
      split; [exact (d_can_of_journal B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msF) _ k AIL Ecan (conj Hbase HJ))|].
      split; [exact Hcan0|].
      intros a Ha. refine (proj1 (ail_env _ _ _ AIL a _)). unfold aenv_addr. left.
      apply (ail_owned_core _ _ _ AIL). unfold aenv_core. right; right; right. rewrite Ecan. exact Ha. }
    split.
    { intros a Ha. left. change DFRAME_SIZE with 3072 in Ha.
      change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. rewrite Elo3. lia. }
    intros a Ha. change DFRAME_SIZE with 3072 in Ha. split.
    { unfold awr_byte. right. right. right. unfold in_frames.
      exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite Efa4.
      change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
    apply HFpres4. change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. lia.
- paj_run_to_tok RUNTO HS HJ SHOK PEspan 0x254c.
  { pe_awr cx EA60. }
  lazymatch goal with |- SRr _ _ (mkCfg ?msv ?mdv) _ => set (md4 := mdv) in *; set (msF := msv) in * end.
  pose proof (conj Hbase (conj HJ Hfrs)) as Hctx4.
  pose proof (d_land_x B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx ly3 S3 W md4 k
    (d_env cx E (pe_vals regs)) _ msF Hctx4 (d_E_env cx E _ HdE) (d_env_fl cx E _) HS
    ltac:(vm_compute; reflexivity)) as HFrameX.
  pose proof (st_ok_pi_restrict_mkst (w_H W) _ _ msF HS eq_refl) as Hms. cbn [ss_pc] in Hms.
  apply SRr_ret. right. unfold exit_pre, d_at.
  exists fq, ly3, S3, (ms_regs msF), (ms_mem msF), md4, k, acc.
  split; [unfold cfg_at, w64, EXIT_OFF; rewrite <- Hms; reflexivity|]. split; [exact Hf0|].
  split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|].
  split; [unfold EV_HEAD, EV_PRO, EV_ITER, MAX_OPS in *; lia|].
  split; [unfold EV_HEAD, EV_PRO, EV_ITER, MAX_OPS in *; lia|].
  split; [exact Hmo|].
  split; [rewrite MT_TRIV in Hacc |- *; unfold ACC_HEAD, ACC_PRO, ACC_ITER, MAX_OPS in *;
          cbn [mo_malloc mo_free ameter_triv] in *; lia|].
  split.
  + unfold d_rX. repeat split.
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
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 18%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite E32', Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * rewrite (st_ok_pi_restrict_reg (w_H W) _ _ msF 19%bv HS). pe_sr_get. cbn [sv_denot].
      rewrite E550, H19, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + unfold d_body_x. split; [exact HFrameX|]. split; [exact Hbl|].
    unfold d_img. eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img);
      [exact HJ | exact (HRO _ Harod)].
Qed.
End h.
End f.
End d.
