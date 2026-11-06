(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 602 of its 653 lines of code are new or changed and 1227 lines of the source are left out. *)
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
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC85 YC88 YCkd YC1g YC1h YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntSeat DiscoYEntProCuts DiscoYEntProSeat DiscoYEntProDCuts DiscoYEntProDLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacHuntPin ReacHuntSilenceProven.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition POFF_D3 : Z := 0x74c.
Definition pd3_rs : smem := map (fun r => set_window r 0 0) (p_kregions dsh_loop (ps_C3 ++ pd_acs) []).
Definition pd3_ss (pc : Z) : sstate := mkSS pc pd_sr pd3_rs None (d_facts [] []).
Definition pd3_sp (lo : nat) (Wb H : list byte) : list byte := firstn lo H ++ Wb ++ skipn (lo + length Wb) H.

Lemma pd3_sp_len : forall lo Wb H, (lo + length Wb <= length H)%nat -> length (pd3_sp lo Wb H) = length H.
Proof. intros lo Wb H Hl. unfold pd3_sp. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma pd3_sp_firstn : forall lo Wb H n, (n <= lo)%nat -> (lo <= length H)%nat ->
  firstn n (pd3_sp lo Wb H) = firstn n H.
Proof.
intros lo Wb H n Hn Hl. unfold pd3_sp. rewrite firstn_app, length_firstn, firstn_firstn.
replace (n - Nat.min lo (length H))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. f_equal. lia.
Qed.

Lemma pd3_sp_skipn : forall lo Wb H n, (lo + length Wb <= n)%nat -> (lo + length Wb <= length H)%nat ->
  skipn n (pd3_sp lo Wb H) = skipn n H.
Proof.
intros lo Wb H n Hn Hl. unfold pd3_sp. rewrite skipn_app, length_firstn.
rewrite (skipn_all2 (firstn lo H)) by (rewrite length_firstn; lia). cbn [app].
rewrite skipn_app, (skipn_all2 Wb) by lia. cbn [app].
rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma pd3_hunt_keep : forall H H' : list byte, length H' = 480%nat ->
  firstn 418 H' = firstn 418 H -> skipn 440 H' = skipn 440 H -> hunt_ok H ->
  hunt_ok H' /\ firstn 6 (skipn 412 H') = firstn 6 (skipn 412 H).
Proof.
intros H H' Hl HF HS (_ & HT & HL & HN).
assert (K : forall (l : list byte) a b, (a + b <= 418)%nat -> firstn b (skipn a l) = firstn b (skipn a (firstn 418 l))).
{ intros l a b Hab. rewrite skipn_firstn_comm, firstn_firstn. f_equal. lia. }
assert (K0 : forall l : list byte, firstn 400 l = firstn 400 (firstn 418 l)) by (intros l; rewrite firstn_firstn; reflexivity).
split; [|rewrite (K H' 412%nat 6%nat), HF, <- (K H 412%nat 6%nat) by lia; reflexivity].
split; [exact Hl|]. split; [rewrite (K0 H'), HF, <- (K0 H); exact HT|].
split; [rewrite (K H' 400%nat 12%nat), HF, <- (K H 400%nat 12%nat) by lia; exact HL|].
unfold s32_at, u_at, sub in HN |- *. change (Z.to_nat 440) with 440%nat in HN |- *. rewrite HS. exact HN.
Qed.

Ltac pd3_ro HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Ltac pd3_awr :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end;
repeat (apply awr_ok_cons_ro; [clear; cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.

Ltac pd3_nw :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]);
destruct Hin.

Ltac pd3_rg HS HROK :=
let r := fresh "r" in let Hr := fresh "Hr" in let Hr2 := fresh "Hr2" in
intros r Hr; unfold acallee_saved in Hr;
assert (Hr2 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
clear Hr;
repeat (destruct Hr2 as [Hr2 | Hr2]; [subst r|]); try subst r;
first [ rewrite (st_ok_pi_restrict_reg _ _ _ _ _ HS) | rewrite (st_ok_restrict_reg _ _ _ _ _ _ HS) ];
match goal with |- _ = getr _ ?rr => rewrite (HROK rr) end;
f_equal; vm_compute; reflexivity.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition pd3_M (cx : dcx) (h : Z) : world SEGS -> (word -> option byte) -> Prop :=
  fun W m => pd_our cx W m /\ pd_objT cx W m /\ pd_objG cx W m /\ pd_objL cx W m /\ pd_objH cx h W m.

Lemma pd3_garr8_sp : forall (Hh Hh' : word -> bool) (m m' : word -> option byte) h lo (Wb H : list byte),
  (lo + length Wb <= length H)%nat ->
  garr8 SEGS (mrestrict Hh m) h (map (fun b : byte => bv_unsigned b) H) ->
  (forall a, h <= a < h + Z.of_nat lo \/ h + Z.of_nat (lo + length Wb) <= a < h + Z.of_nat (length H) ->
     aview SEGS Hh' m' a = aview SEGS Hh m a) ->
  garr8 SEGS (mrestrict Hh' m') (h + Z.of_nat lo) (map (fun b : byte => bv_unsigned b) Wb) ->
  garr8 SEGS (mrestrict Hh' m') h (map (fun b : byte => bv_unsigned b) (pd3_sp lo Wb H)).
Proof.
intros Hh Hh' m m' h lo Wb H Hl G K GW.
pose proof G as G0.
rewrite <- (firstn_skipn lo H), map_app in G0.
apply (proj1 (garr8_app SEGS _ _ _ _)) in G0 as (G1 & _).
pose proof G as G3.
rewrite <- (firstn_skipn (lo + length Wb) H), map_app in G3.
apply (proj1 (garr8_app SEGS _ _ _ _)) in G3 as (_ & G4).
rewrite length_map, length_firstn in G4.
replace (Nat.min (lo + length Wb) (length H)) with (lo + length Wb)%nat in G4 by lia.
unfold pd3_sp. rewrite !map_app.
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
- apply (garr8_aview_kept SEGS Hh Hh' m m'); [|exact G1].
  rewrite length_map, length_firstn. intros a Ha. apply K. left. lia.
- apply (proj2 (garr8_app SEGS _ _ _ _)).
  rewrite length_map, length_firstn. replace (Nat.min lo (length H)) with lo by lia. split; [exact GW|].
  rewrite length_map. rewrite <- Z.add_assoc, <- Nat2Z.inj_add.
  apply (garr8_aview_kept SEGS Hh Hh' m m'); [|exact G4].
  rewrite length_map, length_skipn. intros a Ha. apply K. right. lia.
Qed.

Lemma pd3_rok_tr : forall E (m m' : word -> option byte) r,
  region_ok SEGS E m r -> forallb (chunk_inside r) (YP09.r_chunks r) = true ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> writable_at SEGS m' (base_val E (YP09.r_base r) + o)) ->
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     mbyte SEGS m' a = mbyte SEGS m a) ->
  region_ok SEGS E m' r.
Proof.
intros E m m' r HR Hin Hw Hk. apply (pd_rok_move E m m' r HR Hw).
intros c Hc i Hi. pose proof (proj1 (forallb_forall _ _) Hin c Hc) as Hci. unfold chunk_inside in Hci.
apply andb_prop in Hci as [Hci Hc3]. apply andb_prop in Hci as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. apply Z.leb_le in Hc3.
apply Hk. lia.
Qed.

Lemma pd3_objH_tr : forall cx h (W W' : world SEGS) m m',
  (forall a, h <= a < h + 480 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  pd_objH cx h W m -> pd_objH cx h W' m'.
Proof.
intros cx h W W' m m' K (H & HL & HG & HO & HU). exists H. split; [exact HL|]. split; [|split; [exact HO | exact HU]].
apply (garr8_aview_kept SEGS (w_H W) (w_H W') m m'); [|exact HG].
rewrite length_map, HL. intros a Ha. apply K. lia.
Qed.

Lemma pd3_objH_call : forall cx h (W W' : world SEGS) m m' lo (Wb : list byte),
  (418 <= lo)%nat -> (lo + length Wb <= 440)%nat ->
  pd_objH cx h W m ->
  (forall a, h <= a < h + Z.of_nat lo \/ h + Z.of_nat (lo + length Wb) <= a < h + 480 ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  garr8 SEGS (rd W' m') (h + Z.of_nat lo) (map (fun b : byte => bv_unsigned b) Wb) ->
  pd_objH cx h W' m'.
Proof.
intros cx h W W' m m' lo Wb Hlo Hhi (H & HL & HG & HO & HU) K GW.
exists (pd3_sp lo Wb H).
pose proof (pd3_sp_len lo Wb H ltac:(lia)) as L1. rewrite HL in L1.
destruct (pd3_hunt_keep H (pd3_sp lo Wb H) L1 (pd3_sp_firstn lo Wb H 418 ltac:(lia) ltac:(lia))
  (pd3_sp_skipn lo Wb H 440 ltac:(lia) ltac:(lia)) HO) as (HO' & HU').
split; [exact L1|]. split; [|split; [exact HO' | rewrite HU'; exact HU]].
apply (pd3_garr8_sp (w_H W) (w_H W') m m' h lo Wb H ltac:(lia) HG); [|exact GW].
rewrite HL. intros a Ha. apply K. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis TPIN : ReacHuntPin.treac_hunt_pin_spec B.
Hypothesis TSIL : ReacHuntSilenceProven.treac_hunt_silence_proven_spec B.

Lemma pd3_rC3_pres : forall cx (regs regs' : bvmap 5 word), p_rC3 cx B regs -> aregs_preserved regs regs' ->
  p_rC3 cx B regs'.
Proof.
intros cx regs regs' HR HP.
assert (RF : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 23; 24; 27]%bv -> getr regs' r = getr regs r).
{ intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [match goal with |- getr _ ?rr = _ =>
    let z := eval vm_compute in (bv_unsigned rr) in exact (HP z ltac:(unfold acallee_saved; lia)) end|]).
  destruct Hr. }
destruct HR as ((Hsp & Hgp & Htp & H8 & H9 & H19 & H27) & H18 & H24 & H23).
unfold p_rC3, p_rbase, spZ in *.
rewrite !RF by (cbv; tauto).
repeat split; assumption.
Qed.

Lemma pd3_blocks : forall cx h ly S ly' S', d_blocks B cx h [] ly S ->
  Permutation (ablocks B ly' S') (ablocks B ly S) -> d_blocks B cx h [] ly' S'.
Proof.
intros cx h ly S ly' S' (P1 & P2 & P3 & P4) HP.
split; [exact (Permutation_trans HP P1)|]. split; [exact P2|]. split; [|exact P4].
rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HP), <- (blocks_bytes_bsum B ly S). exact P3.
Qed.

Lemma pd3_tr : forall cx h ly S (W W' : world SEGS) m m' md k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly S W' m' md k ->
  (forall a, d_A cx <= a < d_S cx \/ d_FB cx <= a < d_FB cx + 4096 \/
     shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  p_frame cx dsh_loop ps_C3 W m -> val_mem SEGS (rd W m) (d_A cx + 184) 8 h ->
  pd_our cx W m -> pd_objT cx W m -> pd_objG cx W m -> pd_objL cx W m ->
  p_frame cx dsh_loop ps_C3 W' m' /\ val_mem SEGS (rd W' m') (d_A cx + 184) 8 h /\
  pd_our cx W' m' /\ pd_objT cx W' m' /\ pd_objG cx W' m' /\ pd_objL cx W' m'.
Proof.
intros cx h ly S W W' m m' md k HC K (E & HE & HRG & HFL) H184 Hour (T & HT1 & HT2 & HT3) (G & HG1 & HG2 & HG3)
  (Lk & HL1 & HL2 & HL3).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (Hac & _).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
assert (Hd1 : d_FB cx / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (U2 : base_val E (Some AT_STK) = d_S cx).
{ cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
assert (U60 : base_val E (Some AT_A) = d_A cx).
{ cbn [base_val]. rewrite E60. apply unsigned_lit_small. unfold MFRAME, LLVMF_STK in *. lia. }
assert (U516 : base_val E (Some AT_F) = d_FB cx).
{ cbn [base_val]. rewrite EF. apply unsigned_lit_small. lia. }
assert (U529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
{ cbn [base_val]. rewrite ESH. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
split; [|split; [|split; [|split; [|split]]]].
- exists E. split; [exact HE|]. split.
  + unfold p_regions in HRG |- *.
    pose proof (Forall_inv HRG) as R1. apply Forall_inv_tail in HRG.
    pose proof (Forall_inv HRG) as R2. apply Forall_inv_tail in HRG.
    pose proof (Forall_inv HRG) as R3. apply Forall_inv_tail in HRG.
    pose proof (Forall_inv HRG) as R4. clear HRG.
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (pd3_rok_tr E _ _ _ R1); [vm_compute; reflexivity | |].
      -- intros o Ho. cbn [YP09.r_wlo YP09.r_whi] in Ho. lia.
      -- intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi] in Ha. rewrite U2 in Ha.
         apply (mbyte_of_aview SEGS). apply K. left. unfold MFRAME in *. lia.
    * apply (pd3_rok_tr E _ _ _ R2); [vm_compute; reflexivity | |].
      -- intros o Ho. cbn [YP09.r_wlo YP09.r_whi YP09.r_base] in Ho |- *. rewrite U60.
         apply (apresent_writable SEGS). apply HWpres. unfold MFRAME, LLVMF_STK in *. lia.
      -- intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi] in Ha. rewrite U60 in Ha.
         apply (mbyte_of_aview SEGS). apply K. left. unfold MFRAME in *. lia.
    * apply (pd3_rok_tr E _ _ _ R3); [vm_compute; reflexivity | |].
      -- intros o Ho. cbn [YP09.r_wlo YP09.r_whi YP09.r_base] in Ho |- *. rewrite U516.
         apply (apresent_writable SEGS). apply HFpres. unfold DFRAME_SIZE in Ho. lia.
      -- intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi] in Ha. rewrite U516 in Ha.
         change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha.
         apply (mbyte_of_aview SEGS). apply K. right. left. lia.
    * apply (pd3_rok_tr E _ _ _ R4); [vm_compute; reflexivity | |].
      -- intros o Ho. unfold fshadow_region in Ho |- *. cbn [YP09.r_wlo YP09.r_whi YP09.r_base] in Ho |- *. rewrite U529.
         apply (apresent_writable SEGS). apply HSpres. unfold DFRAME_SH in Ho. lia.
      -- intros a Ha. unfold fshadow_region in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi] in Ha. rewrite U529 in Ha.
         change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
         apply (mbyte_of_aview SEGS). apply K. right. right. lia.
  + rewrite <- HFL. apply rdword_ext. intros kk Hkk. apply K. right. left.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
- apply (pd_val_kept W m W' m'); [|exact H184]. intros x Hx. apply K. left. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  unfold MFRAME in *. lia.
- apply (garr8_aview_kept SEGS (w_H W) (w_H W') m m'); [|exact Hour].
  unfold our_of. rewrite !length_map, length_seq. intros a Ha. apply K. right. left.
  unfold d_obj, dobj_off in Ha. lia.
- exists T. split; [exact HT1|]. split; [|exact HT3].
  apply (garr8_aview_kept SEGS (w_H W) (w_H W') m m'); [|exact HT2].
  rewrite length_map, HT1. intros a Ha. apply K. right. left. unfold d_obj, dobj_off in Ha. lia.
- exists G. split; [exact HG1|]. split; [|exact HG3].
  apply (garr8_aview_kept SEGS (w_H W) (w_H W') m m'); [|exact HG2].
  rewrite length_map, HG1. intros a Ha. apply K. right. left. unfold d_obj, dobj_off in Ha. lia.
- exists Lk. split; [exact HL1|]. split; [|exact HL3].
  apply (garr8_aview_kept SEGS (w_H W) (w_H W') m m'); [|exact HL2].
  rewrite length_map, HL1. intros a Ha. apply K. right. left. unfold d_obj, dobj_off in Ha. lia.
Qed.

Lemma pd3_land_run : forall (fq : YK11.FPState) cx h Q ly3 S3 (W : world SEGS) (regs regs' : bvmap 5 word)
  mem3 mem' md' k acc,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem' md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= k <= EV_PRO -> st_nev S3 <= st_nev (c_S cx) + EV_PRO ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_PRO MT ->
  p_canok cx -> p_rC3 cx B regs -> p_frame cx dsh_loop ps_C3 W mem3 -> d_blocks B cx h [] ly3 S3 ->
  val_mem SEGS (rd W mem3) (d_A cx + 184) 8 h -> pd3_M cx h W mem3 ->
  (forall a, aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem3 a) ->
  aregs_preserved regs regs' ->
  pd_at B MT XM_LIB RLO RHI tfib_K cx h Q (fun _ => True) (pd3_M cx h) W
    (cfg_at (fx := fq) SEGS (BASE + Q) regs' mem' md').
Proof.
intros fq cx h Q ly3 S3 W regs regs' mem3 mem' md' k acc HFRM Hbase HJ Hfrs Hk Hnev Hmo Hacc Hcan HrC3 Hfr Hbl H184
  (Hour & HT & HG & HL & HH) KE HP.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem' md' k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (pd3_tr cx h ly3 S3 W W mem3 mem' md' k HC (fun a _ => KE a) Hfr H184 Hour HT HG HL)
  as (Hfr2 & H1842 & Hour2 & HT2 & HG2 & HL2).
assert (HH2 : pd_objH cx h W mem') by exact (pd3_objH_tr cx h W W mem3 mem' (fun a _ => KE a) HH).
exists fq, ly3, S3, regs', mem', md', k, acc.
split; [reflexivity|]. split; [exact HFRM|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|].
split; [exact Hk|]. split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hcan|]. split; [exact (pd3_rC3_pres cx regs regs' HrC3 HP)|]. split; [exact I|].
split; [exact Hfr2|]. split; [exact Hbl|]. split; [exact H1842|].
exact (conj Hour2 (conj HT2 (conj HG2 (conj HL2 HH2)))).
Qed.

Lemma pd3_land_call : forall (fq : YK11.FPState) cx h Q lo (Wb : list byte) FP1 STK1
  ly3 S3 (W : world SEGS) (regs : bvmap 5 word) mem3 memc mdc k acc ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx -> frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W memc mdc k ->
  0 <= k <= EV_PRO -> acc <= ACC_PRO MT ->
  p_canok cx -> p_rC3 cx B regs -> p_frame cx dsh_loop ps_C3 W mem3 -> d_blocks B cx h [] ly3 S3 ->
  val_mem SEGS (rd W mem3) (d_A cx + 184) 8 h -> pd3_M cx h W mem3 ->
  (forall a, aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem3 a) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  ajournal SEGS B STK1 (d_A cx) FP1 ly3 S3 W memc mdc [] ly2 S2 W2 mem2 md2 0 ->
  (forall a, inFP FP1 a -> h + Z.of_nat lo <= a < h + Z.of_nat (lo + length Wb)) ->
  aregs_preserved regs regs2 ->
  garr8 SEGS (rd W2 mem2) (h + Z.of_nat lo) (map (fun b : byte => bv_unsigned b) Wb) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  (418 <= lo)%nat -> (lo + length Wb <= 440)%nat ->
  pd_at B MT XM_LIB RLO RHI tfib_K cx h Q (fun _ => True) (pd3_M cx h) W2
    (cfg_at (fx := fq) SEGS (BASE + Q) regs2 mem2 md2).
Proof.
intros fq cx h Q lo Wb FP1 STK1 ly3 S3 W regs mem3 memc mdc k acc ly2 S2 W2 regs2 mem2 md2
  HFRM Hbase Hfrs HJ Hk Hacc Hcan HrC3 Hfr Hbl H184 (Hour & HT & HG & HL & HH) KE HJc HJ2 HFP HP HGW HPerm Hlo Hhi.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W memc mdc k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (Hal16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HFal & _ & _ & _ & HAR3 & Hin3 & EFB3 & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & Hfrs2 & _ & _ & K1 & K2 & _ & K4 & _).
assert (Hfrs2' : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfrs2; exact Hfrs).
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
  by (split; [exact Hbase | split; [exact HJc | exact Hfrs2']]).
pose proof asan_consts as (Hac & _).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (Hhin : In (h, 480) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym (proj1 Hbl))). left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & Hhapp & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hhin Hin3) as Hsbf.
unfold zdisjoint in Hsbf. cbn [fst snd] in Hsbf. rewrite EFB3 in Hsbf.
change (req_size 480) with 480 in Hhceil, Hhapp, Hsbf. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hsbf.
assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
assert (FPr : forall a, inFP FP1 a -> h <= a < h + 480) by (intros a Ha; apply HFP in Ha; lia).
assert (KE2 : forall a, d_A cx <= a < d_S cx \/ d_FB cx <= a < d_FB cx + 4096 \/
    shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. rewrite <- (KE a). destruct Ha as [Ha | Ha].
  - apply K1; [unfold MFRAME, LLVMF_STK in *; lia | lia].
  - apply (K4 DFRAME_CLASS (c_fpos cx) a Hin3).
    + unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS) with 4096.
      change (4096 / 8) with 512. lia.
    + intros HF. apply FPr in HF.
      unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
destruct (pd3_tr cx h ly2 S2 W W2 mem3 mem2 md2 k HC2 KE2 Hfr H184 Hour HT HG HL)
  as (Hfr2 & H1842 & Hour2 & HT2 & HG2 & HL2).
assert (HH2 : pd_objH cx h W2 mem2).
{ apply (pd3_objH_call cx h W W2 mem3 mem2 lo Wb Hlo Hhi HH); [|exact HGW].
  intros a Ha. rewrite <- (KE a). replace a with (h + (a - h)) by lia.
  apply (K2 h 480 (a - h) Hhin (Permutation_in _ (Permutation_sym HPerm) Hhin)).
  - change (req_size 480) with 480. lia.
  - intros HF. apply HFP in HF. lia. }
pose proof HJc as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
exists fq, ly2, S2, regs2, mem2, md2, k, acc.
split; [reflexivity|]. split; [exact HFRM|]. split; [exact Hbase|]. split; [exact HJc|]. split; [exact Hfrs2'|].
split; [exact Hk|]. split; [unfold EV_PRO in *; lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
split; [exact Hcan|]. split; [exact (pd3_rC3_pres cx regs regs2 HrC3 HP)|]. split; [exact I|].
split; [exact Hfr2|]. split; [exact (pd3_blocks cx h ly3 S3 ly2 S2 Hbl HPerm)|]. split; [exact H1842|].
exact (conj Hour2 (conj HT2 (conj HG2 (conj HL2 HH2)))).
Qed.

Lemma pd3_seat : forall (fq : YK11.FPState) cx h pc ly3 S3 (W : world SEGS) (regs : bvmap 5 word) mem3 md3 k E,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W mem3)) (p_regions dsh_loop ps_C3) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  p_rC3 cx B regs -> 0 <= h < 2 ^ 64 -> val_mem SEGS (rd W mem3) (d_A cx + 184) 8 h ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (pd_vals regs h)) (pd3_ss pc)
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem3 (YK11.seg_rom SEGS))) /\
  img_env VAL A_LIM (d_env cx E (pd_vals regs h)) /\
  regs_ok (d_env cx E (pd_vals regs h)) pd_sr regs /\
  ew (d_env cx E (pd_vals regs h)) 563 = w64 h.
Proof.
intros fq cx h pc ly3 S3 W regs mem3 md3 k E HC HdE HRG HFL HrC3 Hh H184.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & _ & _ & _ & _ & _ & _ & _).
pose proof asan_consts as (Hac & _).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
pose proof HrC3 as (HrB & _).
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
assert (Hd1 : d_FB cx / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
assert (HSHrange : 0 <= shadow_addr (d_FB cx) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; lia).
pose proof (pd_regs_ok cx E regs h B HdE HrB HArange HSHrange) as HROK.
assert (E563 : ew (d_env cx E (pd_vals regs h)) 563 = w64 h).
{ change 563%nat with (AT_X + 32)%nat.
  rewrite d_env_x by (unfold pd_vals; rewrite length_app, length_map, length_seq; cbn; lia).
  unfold pd_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia). rewrite length_map, length_seq.
  reflexivity. }
assert (CK : YP09.chunk_ok SEGS (d_env cx E (pd_vals regs h)) (rd W mem3) (d_A cx)
  (YP09.mkChunk 184 (CVal 8 (SOff (AT_X + 32) 0)))).
{ apply (chunk_ok_val SEGS (d_env cx E (pd_vals regs h)) (rd W mem3) (d_A cx) 184 8%N (SOff (AT_X + 32) 0) h).
  - cbn [sv_denot]. change (AT_X + 32)%nat with 563%nat. rewrite E563, Z.add_0_r. unfold w64.
    rewrite Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hh.
  - cbn. lia.
  - exact H184. }
pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C3 ly3 S3 W regs mem3 md3 k E pc pd_sr
  (pd_vals regs h) pd_acs [] [] (d_facts [] []) HC HdE HRG HFL HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (pd_vals regs h) [] [] HC HdE I I)
  (@Forall_cons _ _ _ _ CK (@Forall_nil _ _)) (Forall_nil _) (Forall_nil _) I (Forall_nil _)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_p in HS.
pd3_ro HS 60%nat. pd3_ro HS 516%nat. pd3_ro HS 529%nat.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?s ?msx => replace s with (pd3_ss pc) in HS by (vm_compute; reflexivity) end.
split; [exact HS|]. split; [|split; [exact HROK | exact E563]].
pose proof HdE as (_ & _ & HEI0 & _).
intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HEI0 a Ha).
Qed.

Lemma pd3_c5 : forall cx h (W : world SEGS) c,
  pd_at B MT XM_LIB RLO RHI tfib_K cx h POFF_C5 (fun _ => True) (pd3_M cx h) W c ->
  pro_C5 B MT XM_LIB RLO RHI tfib_K cx h W c.
Proof.
intros cx h W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & HFRM & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & (HrB & _ & H24 & H23) & _ & Hfr & Hbl & H184 & Hour & (T & HT1 & HT2 & HT3) & (G & HG1 & HG2 & HG3) &
  (Lk & HL1 & HL2 & HL3) & (H & HH1 & HH2 & HH3 & HH4)).
exists fq, ly3, S3, regs, mem3, md3, k, acc.
split; [exact Hc|]. split; [exact HFRM|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|].
split; [exact Hk|]. split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hcan|]. split; [exact (conj HrB (conj H24 H23))|].
split; [exact Hfr|]. split; [exact Hbl|]. split; [exact H184|].
exists T, G, Lk, H.
exact (conj HT1 (conj HT2 (conj HT3 (conj HG1 (conj HG2 (conj HG3 (conj HL1 (conj HL2 (conj HL3
  (conj Hour (conj HH1 (conj HH2 (conj HH3 HH4))))))))))))).
Qed.

Lemma pd3_w1 : forall cx h (W : world SEGS) c,
  pd_at B MT XM_LIB RLO RHI tfib_K cx h POFF_D2 (fun _ => True) (pd3_M cx h) W c ->
  SRr SEGS W c (pd_at B MT XM_LIB RLO RHI tfib_K cx h POFF_D3 (fun _ => True) (pd3_M cx h)).
Proof.
intros cx h W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & HrC3 & _ & Hfr & Hbl & H184 & HM).
pose proof Hfr as (E & HdE & HRG & HFL).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (HSmod & HSlo & HShi & _ & _ & _ & _ & _ & _ & _ & _ & HAR3 & _ & _ & _).
assert (Hhin : In (h, 480) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym (proj1 Hbl))). left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & _ & _ & _ & _).
pose proof asan_consts as (Hac & _).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
change (req_size 480) with 480 in Hhceil.
assert (Hh64 : 0 <= h < 2 ^ 64) by lia.
destruct (pd3_seat fq cx h POFF_D2 ly3 S3 W regs mem3 md3 k E HC HdE HRG HFL HrC3 Hh64 H184) as (HS & HEI & HROK & E563).
set (Ed := d_env cx E (pd_vals regs h)) in *.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof HrC3 as ((Hsp & Hgp & Htp & _) & _).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + POFF_D2)) with (Z_to_bv 64 (BASE + POFF_D2)).
paj_run_shc RUNP RUNC HS HJ.
{ pd3_awr. }
pose (BR := paj_branch (fx := fq) (PI := PI)).
psrr_branch_pi RUNP BR HS.
- norm_ss HS.
  rename ms into ms1. rename mat into mat1. rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
  paj_run_to_shc RUNTOP HS HJ POFF_D3.
  { pd3_awr. }
  assert (KE : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { intros a. transitivity (aview SEGS (w_H W) (ms_mem ms1) a); apply aview_eq_of; [apply HFr | apply HFr1]; pd3_nw. }
  assert (RG : aregs_preserved regs (ms_regs ms)) by pd3_rg HS HROK.
  pose proof (st_ok_pi_restrict_mkst (w_H W) Ed _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms.
  rewrite Hms at 1. apply SRr_ret.
  exact (pd3_land_run fq cx h POFF_D3 ly3 S3 W regs (ms_regs ms) mem3 (ms_mem ms) _ k acc HFRM Hbase HJ Hfrs Hk Hnev Hmo
    Hacc Hcan HrC3 Hfr Hbl H184 HM KE RG).
- norm_ss HS.
  rename ms into ms1. rename mat into mat1. rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
  paj_run_shc RUNP RUNC HS HJ.
  { pd3_awr. }
  assert (KE : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { intros a. transitivity (aview SEGS (w_H W) (ms_mem ms1) a); apply aview_eq_of; [apply HFr | apply HFr1]; pd3_nw. }
  assert (RG : aregs_preserved regs (ms_regs ms)) by pd3_rg HS HROK.
  assert (RG2 : getr (ms_regs ms) 2%bv = getr regs 2%bv) by exact (RG 2 ltac:(unfold acallee_saved; lia)).
  assert (RG3 : getr (ms_regs ms) 3%bv = getr regs 3%bv) by exact (RG 3 ltac:(unfold acallee_saved; lia)).
  assert (RG4 : getr (ms_regs ms) 4%bv = getr regs 4%bv) by exact (RG 4 ltac:(unfold acallee_saved; lia)).
  assert (Hspc : spZ (ms_regs ms) = d_A cx) by (unfold spZ in Hsp |- *; rewrite RG2; exact Hsp).
  assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 0x74c)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    exact (codeptr_val _ 0x74c HEI). }
  assert (R10 : getr (ms_regs ms) 10%bv = w64 h).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    cbn [sv_denot]. rewrite E563, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  pmkst HS. rewrite pa_sigma_reac_hunt_pin.
  pose proof (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) _ k (regupd (ms_regs ms) 8 (Z_to_bv 64 0))
    ReacHuntPin.REAC_HUNT_PIN_STK (d_A cx - d_S cx) [] HJ) as HPRE1.
  assert (EspC : spZ (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) = spZ (ms_regs ms))
    by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
  specialize (HPRE1 ltac:(rewrite EspC, Hspc; lia) ltac:(lia) ltac:(unfold MFRAME in *; lia)
    ltac:(unfold ReacHuntPin.REAC_HUNT_PIN_STK, ESTACK; lia)
    ltac:(unfold ReacHuntPin.REAC_HUNT_PIN_STK, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])).
  specialize (HPRE1 ltac:(unfold raZ; rewrite getr_other by reg_neq_tac; rewrite R1, unsigned_lit_small by lia; lia)).
  specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite RG3; exact Hgp)).
  specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite RG4; exact Htp)).
  specialize (HPRE1 ltac:(apply achain_low; unfold s0Z; rewrite getr_same by reg_neq_tac;
    rewrite unsigned_lit_small by lia; lia)).
  eapply SRr_bind.
  { pose proof (TPIN fq ly3 S3 W (ms_regs ms) (ms_mem ms) _ [] h h 480 HPRE1) as CALL.
    unfold cfg_at in CALL. apply CALL; clear CALL.
    - exact R10.
    - lia.
    - lia.
    - exact Hhin.
    - lia.
    - change (req_size 480) with 480. lia. }
  cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFRG2 & HCSR2 & HJ2 & HP2 & HG8 & HPerm).
  pose proof (ajournal_sub SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ2) as HJc.
  rewrite Hspc in HJc, HJ2.
  specialize (HJc ltac:(unfold ReacHuntPin.REAC_HUNT_PIN_STK, ESTACK, MFRAME, LLVMF_STK in *; lia)
    ltac:(unfold MFRAME in *; lia)).
  specialize (HJc ltac:(intros a (r & [<- | []] & Ha); cbn [fst snd] in Ha; right; exists h, 480;
    split; [exact Hhin|]; split; [exact (Forall_inv (proj1 (proj2 Hbl))) | change (req_size 480) with 480; lia])).
  cbn [app] in HJc. rewrite Z.add_0_r in HJc.
  assert (RGc : aregs_preserved regs regs2) by (intros r Hr; rewrite (HP2 r Hr); exact (RG r Hr)).
  rewrite R1. apply SRr_ret.
  apply (pd3_land_call fx2 cx h POFF_D3 432 (Mem.le4 (Z_to_bv 64 1) ++ Mem.le4 (getr (ms_regs ms) 11%bv))
    [(h + 432, h + 440)] ReacHuntPin.REAC_HUNT_PIN_STK ly3 S3 W regs mem3 (ms_mem ms) _ k acc ly2 S2 W2 regs2 mem2 md2
    (pd_frm0 fq fx2 HFRM HCSR2) Hbase Hfrs HJ Hk Hacc Hcan HrC3 Hfr Hbl H184 HM KE HJc HJ2).
  + intros a (r & [<- | []] & Ha). cbn [fst snd] in Ha. rewrite length_app, !Mem.length_le4. lia.
  + exact RGc.
  + exact HG8.
  + exact HPerm.
  + lia.
  + rewrite length_app, !Mem.length_le4. lia.
Qed.

Lemma pd3_w2 : forall cx h (W : world SEGS) c,
  pd_at B MT XM_LIB RLO RHI tfib_K cx h POFF_D3 (fun _ => True) (pd3_M cx h) W c ->
  SRr SEGS W c (pd_at B MT XM_LIB RLO RHI tfib_K cx h POFF_C5 (fun _ => True) (pd3_M cx h)).
Proof.
intros cx h W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & HrC3 & _ & Hfr & Hbl & H184 & HM).
pose proof Hfr as (E & HdE & HRG & HFL).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
  as (HSmod & HSlo & HShi & _ & _ & _ & _ & _ & _ & _ & _ & HAR3 & _ & _ & _).
assert (Hhin : In (h, 480) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym (proj1 Hbl))). left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hhin) as (Hh16 & Hh4096 & Hhceil & _ & _ & _ & _).
pose proof asan_consts as (Hac & _).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
change (req_size 480) with 480 in Hhceil.
assert (Hh64 : 0 <= h < 2 ^ 64) by lia.
destruct (pd3_seat fq cx h POFF_D3 ly3 S3 W regs mem3 md3 k E HC HdE HRG HFL HrC3 Hh64 H184) as (HS & HEI & HROK & E563).
set (Ed := d_env cx E (pd_vals regs h)) in *.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof HrC3 as ((Hsp & Hgp & Htp & _) & _).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + POFF_D3)) with (Z_to_bv 64 (BASE + POFF_D3)).
paj_run_shc RUNP RUNC HS HJ.
{ pd3_awr. }
pose (BR := paj_branch (fx := fq) (PI := PI)).
psrr_branch_pi RUNP BR HS.
- norm_ss HS.
  rename ms into ms1. rename mat into mat1. rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
  paj_run_to_shc RUNTOP HS HJ POFF_C5.
  { pd3_awr. }
  assert (KE : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { intros a. transitivity (aview SEGS (w_H W) (ms_mem ms1) a); apply aview_eq_of; [apply HFr | apply HFr1]; pd3_nw. }
  assert (RG : aregs_preserved regs (ms_regs ms)) by pd3_rg HS HROK.
  pose proof (st_ok_pi_restrict_mkst (w_H W) Ed _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms.
  rewrite Hms at 1. apply SRr_ret.
  exact (pd3_land_run fq cx h POFF_C5 ly3 S3 W regs (ms_regs ms) mem3 (ms_mem ms) _ k acc HFRM Hbase HJ Hfrs Hk Hnev Hmo
    Hacc Hcan HrC3 Hfr Hbl H184 HM KE RG).
- norm_ss HS.
  rename ms into ms1. rename mat into mat1. rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
  paj_run_shc RUNP RUNC HS HJ.
  { pd3_awr. }
  assert (KE : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a).
  { intros a. transitivity (aview SEGS (w_H W) (ms_mem ms1) a); apply aview_eq_of; [apply HFr | apply HFr1]; pd3_nw. }
  assert (RG : aregs_preserved regs (ms_regs ms)) by pd3_rg HS HROK.
  assert (RG2 : getr (ms_regs ms) 2%bv = getr regs 2%bv) by exact (RG 2 ltac:(unfold acallee_saved; lia)).
  assert (RG3 : getr (ms_regs ms) 3%bv = getr regs 3%bv) by exact (RG 3 ltac:(unfold acallee_saved; lia)).
  assert (RG4 : getr (ms_regs ms) 4%bv = getr regs 4%bv) by exact (RG 4 ltac:(unfold acallee_saved; lia)).
  assert (Hspc : spZ (ms_regs ms) = d_A cx) by (unfold spZ in Hsp |- *; rewrite RG2; exact Hsp).
  assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 0x75c)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    exact (codeptr_val _ 0x75c HEI). }
  assert (R10 : getr (ms_regs ms) 10%bv = w64 h).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
    match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
    cbn [sv_denot]. rewrite E563, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  pmkst HS. rewrite pa_sigma_reac_hunt_silence_proven.
  pose proof (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) _ k (regupd (ms_regs ms) 8 (Z_to_bv 64 0))
    ReacHuntSilenceProven.REAC_HUNT_SILENCE_PROVEN_STK (d_A cx - d_S cx) [] HJ) as HPRE1.
  assert (EspC : spZ (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) = spZ (ms_regs ms))
    by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
  specialize (HPRE1 ltac:(rewrite EspC, Hspc; lia) ltac:(lia) ltac:(unfold MFRAME in *; lia)
    ltac:(unfold ReacHuntSilenceProven.REAC_HUNT_SILENCE_PROVEN_STK, ESTACK; lia)
    ltac:(unfold ReacHuntSilenceProven.REAC_HUNT_SILENCE_PROVEN_STK, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])).
  specialize (HPRE1 ltac:(unfold raZ; rewrite getr_other by reg_neq_tac; rewrite R1, unsigned_lit_small by lia; lia)).
  specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite RG3; exact Hgp)).
  specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite RG4; exact Htp)).
  specialize (HPRE1 ltac:(apply achain_low; unfold s0Z; rewrite getr_same by reg_neq_tac;
    rewrite unsigned_lit_small by lia; lia)).
  eapply SRr_bind.
  { pose proof (TSIL fq ly3 S3 W (ms_regs ms) (ms_mem ms) _ [] h h 480 HPRE1) as CALL.
    unfold cfg_at in CALL. apply CALL; clear CALL.
    - exact R10.
    - lia.
    - lia.
    - exact Hhin.
    - lia.
    - change (req_size 480) with 480. lia. }
  cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFRG2 & HCSR2 & HJ2 & HP2 & HG4 & HPerm).
  pose proof (ajournal_sub SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ2) as HJc.
  rewrite Hspc in HJc, HJ2.
  specialize (HJc ltac:(unfold ReacHuntSilenceProven.REAC_HUNT_SILENCE_PROVEN_STK, ESTACK, MFRAME, LLVMF_STK in *; lia)
    ltac:(unfold MFRAME in *; lia)).
  specialize (HJc ltac:(intros a (r & [<- | []] & Ha); cbn [fst snd] in Ha; right; exists h, 480;
    split; [exact Hhin|]; split; [exact (Forall_inv (proj1 (proj2 Hbl))) | change (req_size 480) with 480; lia])).
  cbn [app] in HJc. rewrite Z.add_0_r in HJc.
  assert (RGc : aregs_preserved regs regs2) by (intros r Hr; rewrite (HP2 r Hr); exact (RG r Hr)).
  rewrite R1. apply SRr_ret.
  apply (pd3_land_call fx2 cx h POFF_C5 420 (Mem.le4 (Z_to_bv 64 1))
    [(h + 420, h + 424)] ReacHuntSilenceProven.REAC_HUNT_SILENCE_PROVEN_STK ly3 S3 W regs mem3 (ms_mem ms) _ k acc
    ly2 S2 W2 regs2 mem2 md2 (pd_frm0 fq fx2 HFRM HCSR2) Hbase Hfrs HJ Hk Hacc Hcan HrC3 Hfr Hbl H184 HM KE HJc HJ2).
  + intros a (r & [<- | []] & Ha). cbn [fst snd] in Ha. rewrite Mem.length_le4. lia.
  + exact RGc.
  + exact HG4.
  + exact HPerm.
  + lia.
  + rewrite Mem.length_le4. lia.
Qed.

Theorem pb_proD3 : pd_seg3 B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold pd_seg3. intros cx h W c H.
eapply SRr_bind; [exact (pd3_w1 cx h W c H)|].
cbv beta. intros W1 c1 _ H1.
eapply SRr_mono; [exact (pd3_w2 cx h W1 c1 H1)|].
cbv beta. intros W2 c2 _ H2. exact (pd3_c5 cx h W2 c2 H2).
Qed.
End h.
End f.
End d.
