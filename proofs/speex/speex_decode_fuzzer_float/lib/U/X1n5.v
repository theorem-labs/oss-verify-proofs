(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1n4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Ltac wl_unf := try unfold alloc_ceiling in *.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac lia ::= plia_gen ltac:(idtac; lean_lia ltac:(wl_unf)).

Local Ltac xout MU WM H :=
eapply (rw_cells_munch_out _ _ _ _ _ H) in MU; [|exact WM|].

Local Ltac xport MU WM H :=
eapply rw_cells_transport in H; [| exact MU | exact WM |
cbn [cells_size csize Nat.add Nat.mul disjoint_from length]; rewrite ?cells_size_f32, ?length_f32; cbn [cells_size csize Nat.add Nat.mul disjoint_from length]; lia].
Local Ltac xport_mem mo MU WM :=
repeat match goal with H : rw_cells rsegs mo _ _ |- _ => first [xport MU WM H | clear H] end.

Local Ltac solve_munch3 MU1 MU2 MU3 :=
eapply munch_trans; [eapply munch_weaken_to; [exact MU1|] | eapply munch_trans; [eapply munch_weaken_to; [exact MU2|]| eapply munch_weaken_to; [exact MU3|]]].

Lemma sb_bufs_out : forall W (s : sbd_state bptr) S a j m m',
sb_bufs rsegs m a j -> sb_junk_ok s j -> munch W m m' -> wmono rsegs m m' ->
(forall b x, In b (tl (sb_blocks s S a)) -> blk_addr b <= x < blk_addr b + blk_size b -> outside W x) ->
sb_bufs rsegs m' a j.
Proof.
intros W s S a j m m' sfH_; first [ sf_destruct 8%nat sfH_ as B0 B1 B2 B3 B4 B5 B6 B7 | sf_fb; destruct sfH_ as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7) ]; intros sfH2_; first [ sf_destruct 10%nat sfH2_ as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 | sf_fb; destruct sfH2_ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10) ]; intros MU WM OUT.
unfold sb_bufs. repeat match goal with |- _ /\ _ => split end;
(eapply rw_cells_munch_out; [eassumption| exact MU| exact WM|]); rewrite cells_size_f32; intros x Hx;
[ eapply (OUT (sbd_g0_mem s, a_g0 a, 256)) | eapply (OUT (sbd_g1_mem s, a_g1 a, 256)) | eapply (OUT (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s))
| eapply (OUT (sbd_old_qlsp s, a_oq a, 32)) | eapply (OUT (sbd_interp_qlpc s, a_iq a, 32)) | eapply (OUT (sbd_mem_sp s, a_msp a, 64))
| eapply (OUT (sbd_pi_gain s, a_pg a, 16)) | eapply (OUT (sbd_exc_rms s, a_er a, 16)) ];
(cbn; first [tauto | unfold blk_addr, blk_size; cbn [fst snd]; lia | tauto 20]).
Qed.

Local Ltac ih_sides RL1 TP1 BR INL NDL LAPL APB ST1 :=
lazymatch goal with
| |- decst_rep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => first [exact RL1 | idtac]
| |- (dec_depth _ <= _)%nat => lia
| |- creq_ok _ _ _ => first [assumption | exact I]
| |- creq_ptr_ok _ _ => first [assumption | cbn [creq_ptr_ok]; split; lia | idtac]
| |- _ mod 16 = 0 => rewrite ?unsigned_lit by lia; lia
| |- rtables_pristine _ => first [exact TP1 | idtac]
| |- forall b, In b _ -> rblock_range _ _ => intros b Hb; apply BR; apply INL; exact Hb
| |- List.NoDup _ => exact NDL
| |- lbd_apart _ => exact LAPL
| |- forall b, In b _ -> _ => first [intros b Hb; apply APB; apply INL; exact Hb | idtac]
| |- stk _ _ _ _ => rewrite unsigned_lit by lia; first [exact ST1 | idtac]
| |- alloc_ceiling <= _ => unfold alloc_ceiling; lia
| |- mem_inv _ _ => assumption
| |- frm0 _ => assumption
| |- _ = _ => reflexivity
| |- creq_pre _ _ _ _ _ _ => idtac
| |- _ => rewrite ?unsigned_lit by lia; cbn [creq_size]; first [lia | idtac]
end.
Local Ltac ub_ptr_chk := step; if_false_z; step; step; if_false_z.


Lemma shr1_low32 : forall (w : word) (v : Z), bv_unsigned w mod 2^32 = v mod 2^32 -> - 2^31 <= v < 2^31 ->
bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 w)) 1)) mod 2^32 = c_shr1 v mod 2^32 /\ - 2^31 <= c_shr1 v < 2^31.
Proof.
intros w v E R. unfold c_shr1. rewrite !Z.shiftr_div_pow2 by lia. change (2^1) with 2.
assert (SX : bv_unsigned (sx32 w) = v mod 2^64).
{ unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
unfold bv_swrap. change (bv_half_modulus 32) with (2^31). change (bv_wrap 32 (bv_unsigned w + 2^31)) with ((bv_unsigned w + 2^31) mod 2^32).
pose proof (bv_unsigned_in_range 64 w) as RW. change (bv_modulus 64) with (2^64) in RW.
set (u := bv_unsigned w) in *. clearbody u. Z.div_mod_to_equations. nia. }
rewrite SX, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
split; [| Z.div_mod_to_equations; lia].
destruct (Z.lt_ge_cases v 0) as [NEG|NNEG].
- replace (v mod 2^64) with (v + 2^64) by (Z.div_mod_to_equations; lia).
replace ((v + 2^64) / 2) with (v / 2 + 2^63) by (Z.div_mod_to_equations; lia).
rewrite (Z.mod_small (v / 2 + 2^63)) by (Z.div_mod_to_equations; lia).
replace (2^63) with (2^31 * 2^32) by reflexivity. rewrite Z.mod_add by lia. reflexivity.
- rewrite (Z.mod_small v) by lia. rewrite (Z.mod_small (v / 2) (2^64)) by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma ctl_sb_shape : forall (s : sbd_state bptr) low r, exists s' low', snd (speex_decoder_ctl (DecSB s low) r) = DecSB s' low'.
Proof.
intros s low r. destruct r; cbn [speex_decoder_ctl snd]; try (sf_eexists 2%nat; reflexivity);
destruct (speex_decoder_ctl low _) as [v' l']; sf_eexists 2%nat; reflexivity.
Qed.
Ltac exc_sb := intros _; first [ exact I | lazymatch goal with |- dec_exc_ready _ _ _ (snd (speex_decoder_ctl (DecSB ?s0 ?l0) ?q)) =>
let E := fresh "E" in destruct (ctl_sb_shape s0 l0 q) as (? & ? & E); rewrite E; exact I end ].

Theorem rctl_sbA {RCEIL : RunCeiling} : forall s low, rctl_at low -> rctl_atP (fun r => creq_grp1 r = true) (DecSB s low).
Proof.
intros s low IH OUT STEREO S LBD r P lo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
GRP REP DEPTH OK PRE PTR SP16 TP BR NDI LAP AP APB ST CLO LO MI FRM -> -> ->.
cbn [ctl_depth] in LO. fold (ctl_depth low) in LO. cbn [dec_depth] in DEPTH.
cbn [decst_rep] in REP. fold (DREP OUT STEREO m) in REP.
first [ sf_destruct 12%nat REP as a j LBL ELBD AL POS INV JOK X BU OUTL RL | sf_fb; destruct REP as (a & j & LBL & ELBD & AL & POS & INV & JOK & X & BU & OUTL & RL) ].
assert (INL : forall b, In b LBL -> In b LBD) by (intros b Hb; rewrite ELBD; apply in_app_iff; right; exact Hb).
assert (INS : In (sbd_blk s, S, SBSTATE_SIZEOF) LBD) by (rewrite ELBD; left; reflexivity).
pose proof (BR _ INS) as BRS. unfold blk_addr, blk_size in BRS. cbn [fst snd] in BRS. unfold SBSTATE_SIZEOF in BRS.
first [ sf_destruct 5%nat BRS as S0 S16 _ SCE SIMG | sf_fb; destruct BRS as (S0 & S16 & _ & SCE & SIMG) ]. unfold alloc_ceiling in SCE, CLO.
pose proof (APB _ INS) as APS. unfold blk_addr, blk_size, SBSTATE_SIZEOF in APS. cbn [fst snd] in APS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (dec_depth_pos low) as DPOS.
assert (CDP : 64 <= ctl_depth low) by (clear; induction low; cbn; lia).

assert (NDL : List.NoDup (map blk_id LBL)) by (rewrite ELBD in NDI; exact (NoDup_map_app_r _ _ _ NDI)).
assert (LAPL : lbd_apart LBL) by (eapply lbd_apart_sub; [exact LAP| exact INL]).
assert (SAP : forall b, In b (tl (sb_blocks s S a) ++ LBL) -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S).
{ intros b Hb. pose proof NDI as ND0. pose proof LAP as LAP0. rewrite ELBD in ND0, LAP0.
change (sb_blocks s S a ++ LBL) with ([(sbd_blk s, S, SBSTATE_SIZEOF)] ++ (tl (sb_blocks s S a) ++ LBL)) in ND0, LAP0.
destruct (apart_parts _ _ _ _ ND0 LAP0 ltac:(left; reflexivity) Hb) as [D|D]; unfold blk_addr, blk_size, SBSTATE_SIZEOF in D |- *; cbn [fst snd] in D; lia. }
assert (SAPL : forall b, In b LBL -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S) by (intros b Hb; apply SAP; apply in_app_iff; right; exact Hb).
assert (SAPB : forall b, In b (tl (sb_blocks s S a)) -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S) by (intros b Hb; apply SAP; apply in_app_iff; left; exact Hb).
assert (LCE : forall b, In b LBL -> 0 < blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling).
{ intros b Hb. first [ pose proof (BR _ (INL _ Hb)) as sfP_; sf_destruct 5%nat sfP_ as B0 _ _ BC _ | sf_fb; destruct (BR _ (INL _ Hb)) as (B0 & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia. }
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Imo Ifs Iffs Isfs Inbs Ilpc Ifi Isr Ien Ies Isid Iis | sf_fb; destruct sfP_ as (Imo & Ifs & Iffs & Isfs & Inbs & Ilpc & Ifi & Isr & Ien & Ies & Isid & Iis) ].
unfold sb_cells in X.

eapply evt_cut.
{ eapply (sbctl_entry (sbd_mode s) S P (ctl_req_code r) lo _ ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Imo X);
[reflexivity| exact TP| exact ST| lia| lia| lia| lia| lia| lia| | exact MI].
unfold sbctl_code_ok. destruct r; cbn [ctl_req_code]; cbn in OK; clear - OK; tauto. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 12%nat sfH_ as xt1 xa0 xa1 xa4 j0 m1 -> FR MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (xt1 & xa0 & xa1 & xa4 & j0 & m1 & -> & FR & MU1 & WM1 & MI1 & ST1) ]. unfold sbctl_frame in FR.
xport MU1 WM1 X.
assert (RL1 : DREP OUTL STEREO m1 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL| exact MU1| exact WM1|]. intros b x Hb Hx. destruct (LCE _ Hb). cbn. split; [lia| exact I]. }
assert (TP1 : rtables_pristine m1).
{ eapply rtables_pristine_munch; [exact TP| exact MU1|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. split; [lia| exact I]. }
clear RL TP.

assert (SBOUTG : forall usp P' r' b x, In b (sb_blocks s S a) -> blk_addr b <= x < blk_addr b + blk_size b -> usp <= bv_unsigned sp ->
(forall b', In b' (sb_blocks s S a) -> P' + creq_size r' <= blk_addr b' \/ blk_addr b' + blk_size b' <= P') ->
outside (ctlW lo usp P' r' LBL) x).
{ intros usp P' r' b x Hb Hx HU HP. apply outside_ctlW.
assert (HbD : In b LBD) by (rewrite ELBD; apply in_app_iff; left; exact Hb).
first [ pose proof (BR _ HbD) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BR _ HbD) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC.
split; [lia|]. split; [pose proof (HP _ Hb); lia|].
intros b' Hb'. pose proof NDI as ND0. pose proof LAP as LAP0. rewrite ELBD in ND0, LAP0. destruct (apart_parts _ _ _ _ ND0 LAP0 Hb Hb'); lia. }
assert (SBOUT : forall usp b x, In b (sb_blocks s S a) -> blk_addr b <= x < blk_addr b + blk_size b -> usp <= bv_unsigned sp ->
outside (ctlW lo usp P r LBL) x).
{ intros usp b x Hb Hx HU. apply (SBOUTG usp P r b x Hb Hx HU). intros b' Hb'. apply APB. rewrite ELBD. apply in_app_iff. left. exact Hb'. }
assert (SBLO : forall b', In b' (sb_blocks s S a) -> blk_addr b' + blk_size b' <= lo).
{ intros b' Hb'. first [ pose proof (BR b' ltac:(rewrite ELBD; apply in_app_iff; left; exact Hb')) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BR b' ltac:(rewrite ELBD; apply in_app_iff; left; exact Hb')) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia. }
assert (BU1 : sb_bufs rsegs m1 a j).
{ eapply (sb_bufs_out _ s S); [exact BU| exact JOK| exact MU1| exact WM1|]. intros b x Hb Hx.
assert (HbD : In b LBD) by (rewrite ELBD; apply in_app_iff; left; right; exact Hb).
first [ pose proof (BR _ HbD) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BR _ HbD) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. cbn. split; [lia| exact I]. }
clear BU.
destruct r; cbn in OK; try (exfalso; exact OK); try discriminate GRP; cbn [ctl_req_code creq_size] in *; cbn [creq_pre] in PRE; cbn [sbctl_armpc Z.eqb Pos.eqb]; cbn [creq_ptr_ok] in PTR; destruct PTR as [P0 P4].
-
first [ sf_destruct 4%nat PRE as w ARG EQW RV | sf_fb; destruct PRE as (w & ARG & EQW & RV) ]. xport MU1 WM1 ARG. pose proof (rw_cells_bound _ _ _ _ ARG) as PBc. cbn [cells_size csize Nat.add] in PBc.

ub_ptr_chk. step. step. step. step.
eapply evt_cut.
{ eapply (IH OUTL STEREO (a_low a) LBL (CtlSetEnh v) P lo). all: ih_sides RL1 TP1 BR INL NDL LAPL APB ST1.
cbn [creq_pre]. exists w. split; [exact ARG| split; [exact EQW| exact RV]]. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 26%nat sfH_ as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 F2 fc2 m2 -> MU2 WM2 MI2 FRM2 ST2 RL2 CP2 EX2 | sf_fb; destruct sfH_ as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & FRM2 & ST2 & RL2 & CP2 & EX2) ].
rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. rewrite ret_pc_even by lia.
cbn [creq_post] in CP2. destruct CP2 as (w2 & ARG2 & EQW2). clear ARG.

assert (X2 : rw_cells rsegs m2 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rw_cells_munch_out; [exact X| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply (SBOUT _ (sbd_blk s, S, SBSTATE_SIZEOF) x); [left; reflexivity| unfold blk_addr, blk_size, SBSTATE_SIZEOF; cbn [fst snd]; lia| lia]. }
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) (sbctl_frame j0 s1 s0 ra)).
{ unfold sbctl_frame. eapply rw_cells_munch_out; [exact FR| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply outside_ctlW. split; [lia|]. split; [cbn [creq_size]; lia|]. intros b Hb. destruct (LCE _ Hb). lia. }
assert (BU2 : sb_bufs rsegs m2 a j) by (eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU2| exact WM2| intros b x Hb Hx; apply (SBOUT _ b x ltac:(right; exact Hb) Hx); lia]).
clear X FR BU1.
unfold sb_cells in X2.

pose proof (conj MU2 WM2) as MW2. clear MU2 WM2.
pose proof (munch_refl [(S + 44, S + 48)] m2) as MU3. pose proof (wmono_refl rsegs m2) as WM3.
ub_ptr_chk. step. step. step. destruct MW2 as [MU2 WM2].
eapply evt_cut. { eapply (sbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR2| assumption]. }
cbv beta. intros ms3 ->.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m3 := mx) in *; clearbody m3 end.
match goal with H : stk rsegs m3 lo _ |- _ => rename H into ST3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
assert (BU3 : sb_bufs rsegs m3 a j).
{ eapply (sb_bufs_out _ s S); [exact BU2| exact JOK| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I].
pose proof (SAPB _ Hb). lia. }
assert (RL3 : DREP OUTL STEREO m3 (a_low a) (snd (speex_decoder_ctl low (CtlSetEnh v))) LBL).
{ eapply decst_rep_munch; [exact RL2| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (SAPL _ Hb). lia. }
clear BU2 RL2. unfold sbctl_frame in FR2. release_frame FR2 ST3 (bv_unsigned sp).
destruct (speex_decoder_ctl low (CtlSetEnh v)) as [v0 low'] eqn:EC.
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F2) | exact (fc2) | exact (m3) | ] | sf_fb; exists F2, fc2, m3 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ solve_munch3 MU1 MU2 MU3; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3).
- cbn. split; [lia| exact I].
- apply outside_ctlW. split; [lia|]. split; [exact O2|]. intros b Hb. apply O3. apply INL. exact Hb.
- cbn. split; [| exact I]. specialize (O3 _ INS). unfold blk_addr, blk_size, SBSTATE_SIZEOF in O3. cbn [fst snd] in O3. lia. }
split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|]. split; [exact FRM2|]. split; [exact ST3|].
split.
+ change (speex_decoder_ctl (DecSB s low) (CtlSetEnh v)) with (let '(_, low') := speex_decoder_ctl low (CtlSetEnh v) in (0, DecSB (set_sbd_lpc_enh_enabled s v) low')).
rewrite EC. cbn [fst snd decst_rep]. fold (DREP OUT STEREO m3). cbn [snd] in RL3.
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|].
split; [unfold sb_inv in *; cbn; repeat split; try assumption; lia|]. split; [exact JOK|].
split.
{ unfold sb_cells. cbn -[Z.add Z.mul Z_to_bv rsegs]. eapply rw_cells_samebytes; [exact X2| cbn; destruct JOK as (J1 & J2 & _); repeat split; assumption| | reflexivity].
cbn [cells_bytes cbytes app]. rewrite (sx32_cell_eqm w2 v EQW2). reflexivity. }
split; [exact BU3| exists OUTL; exact RL3].
+ split; [cbn [creq_post]; exists w2; split; [assumption| exact EQW2]| exc_sb].
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG. pose proof (rw_cells_bound _ _ _ _ ARG) as PBc. cbn [cells_size csize Nat.add] in PBc.

ub_ptr_chk. ub_ptr_chk. step. rewrite sx32_lit by (rewrite Iffs, Ifs; destruct Imo as [E|E]; rewrite E; cbn; lia). step.
eapply evt_cut. { eapply (sbctl_exit_get (bv_unsigned sp) P w j0); [lia| reflexivity| exact FR| exact ARG| lia| exact MI1]. }
cbv beta. intros ms3 sfH_; first [ sf_destruct 5%nat sfH_ as m3 -> EM3 MI3 ARG3 | sf_fb; destruct sfH_ as (m3 & -> & EM3 & MI3 & ARG3) ]. replace (P + Z.of_nat 0) with P in EM3 by lia.
pose proof (rw_cells_bound _ _ _ _ ARG) as PB. cbn [cells_size csize Nat.add] in PB.
assert (MU3 : munch [(P, P + 4)] m1 m3) by (rewrite EM3; apply munch_write; rewrite ?length_le4; [apply munch_refl| lia| lia| cbn; lia]).
assert (WM3 : wmono rsegs m1 m3) by (rewrite EM3; apply wmono_write; apply wmono_refl).
clear ARG. xport MU3 WM3 X. xport MU3 WM3 FR.
assert (BU3 : sb_bufs rsegs m3 a j).
{ eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I].
pose proof (APB b ltac:(rewrite ELBD; apply in_app_iff; left; right; exact Hb)). lia. }
assert (RL3 : DREP OUTL STEREO m3 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL1| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (APB b (INL _ Hb)). lia. }
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -32)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
release_frame FR ST3 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F) | exact (fc) | exact (m3) | ] | sf_fb; exists F, fc, m3 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU3|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3); cbn; (split; [lia| exact I]). }
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [speex_decoder_ctl fst snd decst_rep]. fold (DREP OUT STEREO m3).
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
split; [unfold sb_cells; exact X|]. split; [exact BU3| exists OUTL; exact RL3].
+ split; [cbn [creq_post speex_decoder_ctl fst]; split; [exact ARG3| rewrite Iffs, Ifs; destruct Imo as [E|E]; rewrite E; cbn; lia]| exc_sb].
-
destruct PRE as (pad & ARG). xport MU1 WM1 ARG.

ub_ptr_chk. step. step. step. step. step.
eapply evt_cut.
{ eapply (IH OUTL STEREO (a_low a) LBL CtlSetHandlerStereo P lo). all: ih_sides RL1 TP1 BR INL NDL LAPL APB ST1.
cbn [creq_pre]. exists pad. exact ARG. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 26%nat sfH_ as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 F2 fc2 m2 -> MU2 WM2 MI2 FRM2 ST2 RL2 CP2 EX2 | sf_fb; destruct sfH_ as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & FRM2 & ST2 & RL2 & CP2 & EX2) ].
rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. rewrite ret_pc_even by lia.
cbn [creq_post] in CP2. destruct CP2 as (pad2 & ARG2). clear ARG.
assert (X2 : rw_cells rsegs m2 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rw_cells_munch_out; [exact X| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply (SBOUT _ (sbd_blk s, S, SBSTATE_SIZEOF) x); [left; reflexivity| unfold blk_addr, blk_size, SBSTATE_SIZEOF; cbn [fst snd]; lia| lia]. }
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) (sbctl_frame j0 s1 s0 ra)).
{ unfold sbctl_frame. eapply rw_cells_munch_out; [exact FR| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply outside_ctlW. split; [lia|]. split; [cbn [creq_size]; lia|]. intros b Hb. destruct (LCE _ Hb). lia. }
assert (BU2 : sb_bufs rsegs m2 a j) by (eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU2| exact WM2| intros b x Hb Hx; apply (SBOUT _ b x ltac:(right; exact Hb) Hx); lia]).
clear X FR BU1.

step. step.
eapply evt_cut. { eapply (sbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR2| exact MI2]. }
cbv beta. intros ms3 ->.
unfold sbctl_frame in FR2. release_frame FR2 ST2 (bv_unsigned sp).
destruct (speex_decoder_ctl low CtlSetHandlerStereo) as [v0 low'] eqn:EC.
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F2) | exact (fc2) | exact (m2) | ] | sf_fb; exists F2, fc2, m2 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU2|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3).
- cbn. split; [lia| exact I].
- apply outside_ctlW. split; [lia|]. split; [exact O2|]. intros b Hb. apply O3. apply INL. exact Hb. }
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact ST2|].
split.
+ change (speex_decoder_ctl (DecSB s low) CtlSetHandlerStereo) with (let '(_, low') := speex_decoder_ctl low CtlSetHandlerStereo in (0, DecSB s low')).
rewrite EC. cbn [fst snd decst_rep]. fold (DREP OUT STEREO m2). cbn [snd] in RL2.
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
split; [exact X2|]. split; [exact BU2| exists OUTL; exact RL2].
+ split; [cbn [creq_post]; exists pad2; exact ARG2| exc_sb].
-
first [ sf_destruct 4%nat PRE as w ARG EQW RV | sf_fb; destruct PRE as (w & ARG & EQW & RV) ]. xport MU1 WM1 ARG. pose proof (rw_cells_bound _ _ _ _ ARG) as PBc. cbn [cells_size csize Nat.add] in PBc.

pose proof (conj MU1 WM1) as MW1. clear MU1 WM1.
pose proof (munch_refl [(S + 40, S + 44); (bv_unsigned sp + -32, bv_unsigned sp + -28)] m1) as MUA. pose proof (wmono_refl rsegs m1) as WMA.
ub_ptr_chk. ub_ptr_chk. step. step. step. step. step. destruct MW1 as [MU1 WM1].
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mA := mx) in *; clearbody mA end.
match goal with H : mem_inv rsegs mA |- _ => rename H into MIA end. match goal with H : stk rsegs mA lo _ |- _ => rename H into STA end.
apply rw_cells_uncons in FR. destruct FR as [TMP FRr]. cbn [csize] in FRr.
pose proof (shr1_low32 w v EQW RV) as [EQT RT].
assert (BUA : sb_bufs rsegs mA a j).
{ eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MUA| exact WMA|]. intros b x Hb Hx. cbn. pose proof (SAPB _ Hb).
assert (HbD : In b LBD) by (rewrite ELBD; apply in_app_iff; left; right; exact Hb). first [ pose proof (BR _ HbD) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BR _ HbD) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC.
repeat split; lia. }
assert (RLA : DREP OUTL STEREO mA (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL1| exact MUA| exact WMA|]. intros b x Hb Hx. cbn. pose proof (SAPL _ Hb). destruct (LCE _ Hb). repeat split; lia. }
clear BU1 RL1.

step. step. step. step.
eapply evt_cut.
{ eapply (IH OUTL STEREO (a_low a) LBL (CtlSetSamplingRate (c_shr1 v)) (bv_unsigned sp + -32) lo). all: ih_sides RLA TP1 BR INL NDL LAPL APB STA.
- cbn [creq_pre]. eexists. split; [exact TMP| split; [exact EQT| exact RT]].
- eapply rtables_pristine_munch; [exact TP1| exact MUA|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. repeat split; lia.
- intros b Hb. destruct (LCE _ Hb). cbn [creq_size]. lia. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 26%nat sfH_ as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 F2 fc2 mC -> MU2 WM2 MI2 FRM2 ST2 RL2 CP2 EX2 | sf_fb; destruct sfH_ as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & mC & -> & MU2 & WM2 & MI2 & FRM2 & ST2 & RL2 & CP2 & EX2) ].
rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. rewrite ret_pc_even by lia.
cbn [creq_post] in CP2. destruct CP2 as (w2 & TMP2 & EQW2). clear TMP.
assert (X2 : rw_cells rsegs mC S (SBCELLS (set_sbd_sampling_rate s v) a OUT j)).
{ unfold sb_cells. cbn -[Z.add Z.mul Z_to_bv rsegs].
match goal with Xa : rw_cells rsegs mA S ?cs |- _ =>
eapply rw_cells_munch_out; [eapply rw_cells_samebytes; [exact Xa| cbn; destruct JOK as (J1 & J2 & _); repeat split; assumption| cbn [cells_bytes cbytes app]; rewrite (sx32_cell_eqm w v EQW); reflexivity| reflexivity] | exact MU2| exact WM2|] end.
cbn [cells_size csize Nat.add]. intros x Hx.
apply (SBOUTG _ _ _ (sbd_blk s, S, SBSTATE_SIZEOF) x); [left; reflexivity| unfold blk_addr, blk_size, SBSTATE_SIZEOF; cbn [fst snd]; lia| lia| intros b' Hb'; pose proof (SBLO _ Hb'); cbn [creq_size]; lia]. }
assert (FRr2 : rw_cells rsegs mC (bv_unsigned sp + -32 + Z.of_nat 4) [CB 4 (skipn 4 j0); C8 s1; C8 s0; C8 ra]).
{ eapply rw_cells_munch_out; [exact FRr| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply outside_ctlW. cbn [creq_size]. split; [lia|]. split; [lia|]. intros b Hb. destruct (LCE _ Hb). lia. }
assert (ARG2 : rw_cells rsegs mC P [C4 w]).
{ eapply rw_cells_munch_out; [eassumption| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply outside_ctlW. cbn [creq_size]. split; [lia|]. split; [lia|]. intros b Hb. pose proof (APB _ (INL _ Hb)). lia. }
assert (BU2 : sb_bufs rsegs mC a j) by (eapply (sb_bufs_out _ s S); [exact BUA| exact JOK| exact MU2| exact WM2| intros b x Hb Hx; apply (SBOUTG _ _ _ b x ltac:(right; exact Hb) Hx); [lia| intros b' Hb'; pose proof (SBLO _ Hb'); cbn [creq_size]; lia]]).

pose proof (rw_cells_merge rsegs mC (bv_unsigned sp + -32) [] [C4 w2; CB 4 (skipn 4 j0)] [C8 s1; C8 s0; C8 ra]) as FR2.
cbn [app cells_size csize Nat.add cells_bytes cbytes] in FR2.
specialize (FR2 ltac:(change ([C4 w2; CB 4 (skipn 4 j0); C8 s1; C8 s0; C8 ra]) with ([C4 w2] ++ [CB 4 (skipn 4 j0); C8 s1; C8 s0; C8 ra]);
apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact TMP2| cbn [cells_size csize Nat.add]; exact FRr2])).
clear FRr FRr2 BUA.

step. step.
eapply evt_cut. { eapply (sbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR2| exact MI2]. }
cbv beta. intros ms3 ->.
release_frame FR2 ST2 (bv_unsigned sp).
destruct (speex_decoder_ctl low (CtlSetSamplingRate (c_shr1 v))) as [v0 low'] eqn:EC.
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F2) | exact (fc2) | exact (mC) | ] | sf_fb; exists F2, fc2, mC ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ solve_munch3 MU1 MUA MU2; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3).
- cbn. split; [lia| exact I].
- cbn. specialize (O3 _ INS). unfold blk_addr, blk_size, SBSTATE_SIZEOF in O3. cbn [fst snd] in O3. repeat split; lia.
- apply outside_ctlW. cbn [creq_size]. split; [lia|]. split; [lia|]. intros b Hb. apply O3. apply INL. exact Hb. }
split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WMA| exact WM2]]|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact ST2|].
split.
+ change (speex_decoder_ctl (DecSB s low) (CtlSetSamplingRate v)) with
(let '(_, low') := speex_decoder_ctl low (CtlSetSamplingRate (c_shr1 v)) in (0, DecSB (set_sbd_sampling_rate s v) low')).
rewrite EC. cbn [fst snd decst_rep]. fold (DREP OUT STEREO mC). cbn [snd] in RL2.
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|].
split; [unfold sb_inv in *; cbn; repeat split; try assumption; lia|]. split; [exact JOK|].
split; [exact X2|]. split; [exact BU2| exists OUTL; exact RL2].
+ split; [cbn [creq_post]; exists w; split; [exact ARG2| exact EQW]| exc_sb].
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG. pose proof (rw_cells_bound _ _ _ _ ARG) as PBc. cbn [cells_size csize Nat.add] in PBc.

ub_ptr_chk. ub_ptr_chk. step. rewrite sx32_lit by lia. step.
eapply evt_cut. { eapply (sbctl_exit_get (bv_unsigned sp) P w j0); [lia| reflexivity| exact FR| exact ARG| lia| exact MI1]. }
cbv beta. intros ms3 sfH_; first [ sf_destruct 5%nat sfH_ as m3 -> EM3 MI3 ARG3 | sf_fb; destruct sfH_ as (m3 & -> & EM3 & MI3 & ARG3) ]. replace (P + Z.of_nat 0) with P in EM3 by lia.
pose proof (rw_cells_bound _ _ _ _ ARG) as PB. cbn [cells_size csize Nat.add] in PB.
assert (MU3 : munch [(P, P + 4)] m1 m3) by (rewrite EM3; apply munch_write; rewrite ?length_le4; [apply munch_refl| lia| lia| cbn; lia]).
assert (WM3 : wmono rsegs m1 m3) by (rewrite EM3; apply wmono_write; apply wmono_refl).
clear ARG. xport MU3 WM3 X. xport MU3 WM3 FR.
assert (BU3 : sb_bufs rsegs m3 a j).
{ eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I].
pose proof (APB b ltac:(rewrite ELBD; apply in_app_iff; left; right; exact Hb)). lia. }
assert (RL3 : DREP OUTL STEREO m3 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL1| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (APB b (INL _ Hb)). lia. }
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -32)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
release_frame FR ST3 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F) | exact (fc) | exact (m3) | ] | sf_fb; exists F, fc, m3 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU3|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3); cbn; (split; [lia| exact I]). }
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [speex_decoder_ctl fst snd decst_rep]. fold (DREP OUT STEREO m3).
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
split; [unfold sb_cells; exact X|]. split; [exact BU3| exists OUTL; exact RL3].
+ split; [cbn [creq_post speex_decoder_ctl fst]; split; [exact ARG3| exact Isr]| exc_sb].
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG. pose proof (rw_cells_bound _ _ _ _ ARG) as PBc. cbn [cells_size csize Nat.add] in PBc.

ub_ptr_chk. step. step. step. step.
eapply evt_cut.
{ eapply (IH OUTL STEREO (a_low a) LBL CtlGetLookahead P lo). all: ih_sides RL1 TP1 BR INL NDL LAPL APB ST1.
cbn [creq_pre]. exists w. exact ARG. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 26%nat sfH_ as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 F2 fc2 m2 -> MU2 WM2 MI2 FRM2 ST2 RL2 CP2 EX2 | sf_fb; destruct sfH_ as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & FRM2 & ST2 & RL2 & CP2 & EX2) ].
rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. rewrite ret_pc_even by lia.
cbn [creq_post] in CP2. destruct CP2 as [ARG2 _]. clear ARG.
assert (X2 : rw_cells rsegs m2 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rw_cells_munch_out; [exact X| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply (SBOUT _ (sbd_blk s, S, SBSTATE_SIZEOF) x); [left; reflexivity| unfold blk_addr, blk_size, SBSTATE_SIZEOF; cbn [fst snd]; lia| lia]. }
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) (sbctl_frame j0 s1 s0 ra)).
{ unfold sbctl_frame. eapply rw_cells_munch_out; [exact FR| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply outside_ctlW. cbn [creq_size]. split; [lia|]. split; [lia|]. intros b Hb. destruct (LCE _ Hb). lia. }
assert (BU2 : sb_bufs rsegs m2 a j) by (eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU2| exact WM2| intros b x Hb Hx; apply (SBOUT _ b x ltac:(right; exact Hb) Hx); lia]).
clear X FR BU1. unfold sb_cells in X2.
destruct (speex_decoder_ctl low CtlGetLookahead) as [vl low'] eqn:EC. cbn [fst snd] in ARG2, RL2.
pose proof (lookahead_val low ltac:(lia)) as VL. rewrite EC in VL. cbn [fst] in VL.

ub_ptr_chk. step. rewrite sx32_lit by lia. step. step. step. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. if_false_z. step. step. rewrite ?unsigned_lit by lia. step.
unfold sbctl_frame in FR2.
eapply evt_cut. { eapply (sbctl_exit_get (bv_unsigned sp) P (Z_to_bv 64 vl) j0); [lia| reflexivity| exact FR2| exact ARG2| lia| exact MI2]. }
cbv beta. intros ms3 sfH_; first [ sf_destruct 5%nat sfH_ as m3 -> EM3 MI3 ARG3 | sf_fb; destruct sfH_ as (m3 & -> & EM3 & MI3 & ARG3) ]. replace (P + Z.of_nat 0) with P in EM3 by lia.
pose proof (rw_cells_bound _ _ _ _ ARG2) as PB. cbn [cells_size csize Nat.add] in PB.
assert (MU3 : munch [(P, P + 4)] m2 m3) by (rewrite EM3; apply munch_write; rewrite ?length_le4; [apply munch_refl| lia| lia| cbn; lia]).
assert (WM3 : wmono rsegs m2 m3) by (rewrite EM3; apply wmono_write; apply wmono_refl).
clear ARG2. xport MU3 WM3 X2. xport MU3 WM3 FR2.
assert (BU3 : sb_bufs rsegs m3 a j).
{ eapply (sb_bufs_out _ s S); [exact BU2| exact JOK| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I].
pose proof (APB b ltac:(rewrite ELBD; apply in_app_iff; left; right; exact Hb)). lia. }
assert (RL3 : DREP OUTL STEREO m3 (a_low a) low' LBL).
{ eapply decst_rep_munch; [exact RL2| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (APB b (INL _ Hb)). lia. }
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -32)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]).
release_frame FR2 ST3 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F2) | exact (fc2) | exact (m3) | ] | sf_fb; exists F2, fc2, m3 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ solve_munch3 MU1 MU2 MU3; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3).
- cbn. split; [lia| exact I].
- apply outside_ctlW. cbn [creq_size]. split; [lia|]. split; [lia|]. intros b Hb. apply O3. apply INL. exact Hb.
- cbn. split; [lia| exact I]. }
split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|]. split; [exact FRM2|]. split; [exact ST3|].
split.
+ change (speex_decoder_ctl (DecSB s low) CtlGetLookahead) with (let '(v, low') := speex_decoder_ctl low CtlGetLookahead in (2 * v, DecSB s low')).
rewrite EC. cbn [fst snd decst_rep]. fold (DREP OUT STEREO m3).
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
split; [exact X2|]. split; [exact BU3| exists OUTL; exact RL3].
+ change (speex_decoder_ctl (DecSB s low) CtlGetLookahead) with (let '(v, low') := speex_decoder_ctl low CtlGetLookahead in (2 * v, DecSB s low')).
pose proof (lookahead_val (DecSB s low) ltac:(cbn [dec_depth]; lia)) as VL2.
change (speex_decoder_ctl (DecSB s low) CtlGetLookahead) with (let '(v, low') := speex_decoder_ctl low CtlGetLookahead in (2 * v, DecSB s low')) in VL2 |- *.
rewrite EC in VL2 |- *. cbn [creq_post fst snd] in VL2 |- *. split; [| exc_sb]. split; [| lia].
replace (2 * vl) with (vl * 2) by lia. first [exact ARG3 | replace (vl * 2) with (Z.shiftl vl 1) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity); exact ARG3 | idtac "GLFIX"].
-
first [ sf_destruct 4%nat PRE as w ARG EQW RV | sf_fb; destruct PRE as (w & ARG & EQW & RV) ]. xport MU1 WM1 ARG.

ub_ptr_chk. step. step. step. step.
eapply evt_cut.
{ eapply (IH OUTL STEREO (a_low a) LBL (CtlSetWideband v) P lo). all: ih_sides RL1 TP1 BR INL NDL LAPL APB ST1.
cbn [creq_pre]. exists w. split; [exact ARG| split; [exact EQW| exact RV]]. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 26%nat sfH_ as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 F2 fc2 m2 -> MU2 WM2 MI2 FRM2 ST2 RL2 CP2 EX2 | sf_fb; destruct sfH_ as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & FRM2 & ST2 & RL2 & CP2 & EX2) ].
rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. rewrite ret_pc_even by lia.
cbn [creq_post] in CP2. destruct CP2 as (w2 & ARG2 & EQW2). clear ARG.
assert (X2 : rw_cells rsegs m2 S (SBCELLS s a OUT j)).
{ unfold sb_cells. eapply rw_cells_munch_out; [exact X| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply (SBOUT _ (sbd_blk s, S, SBSTATE_SIZEOF) x); [left; reflexivity| unfold blk_addr, blk_size, SBSTATE_SIZEOF; cbn [fst snd]; lia| lia]. }
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) (sbctl_frame j0 s1 s0 ra)).
{ unfold sbctl_frame. eapply rw_cells_munch_out; [exact FR| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add]. intros x Hx.
apply outside_ctlW. cbn [creq_size]. split; [lia|]. split; [lia|]. intros b Hb. destruct (LCE _ Hb). lia. }
assert (BU2 : sb_bufs rsegs m2 a j) by (eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU2| exact WM2| intros b x Hb Hx; apply (SBOUT _ b x ltac:(right; exact Hb) Hx); lia]).
clear X FR BU1.

step. step.
eapply evt_cut. { eapply (sbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR2| exact MI2]. }
cbv beta. intros ms3 ->.
unfold sbctl_frame in FR2. release_frame FR2 ST2 (bv_unsigned sp).
destruct (speex_decoder_ctl low (CtlSetWideband v)) as [v0 low'] eqn:EC.
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F2) | exact (fc2) | exact (m2) | ] | sf_fb; exists F2, fc2, m2 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU2|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3).
- cbn. split; [lia| exact I].
- apply outside_ctlW. cbn [creq_size]. split; [lia|]. split; [exact O2|]. intros b Hb. apply O3. apply INL. exact Hb. }
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact ST2|].
split.
+ change (speex_decoder_ctl (DecSB s low) (CtlSetWideband v)) with (let '(_, low') := speex_decoder_ctl low (CtlSetWideband v) in (0, DecSB s low')).
rewrite EC. cbn [fst snd decst_rep]. fold (DREP OUT STEREO m2). cbn [snd] in RL2.
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
split; [exact X2|]. split; [exact BU2| exists OUTL; exact RL2].
+ split; [cbn [creq_post]; exists w2; split; [exact ARG2| exact EQW2]| exc_sb].
Qed.
