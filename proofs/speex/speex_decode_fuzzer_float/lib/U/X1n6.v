(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1n4 X1n5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Local Ltac xout MU WM H :=
eapply (rw_cells_munch_out _ _ _ _ _ H) in MU; [|exact WM|].

Local Ltac xport MU WM H :=
eapply rw_cells_transport in H; [| exact MU | exact WM |
cbn [cells_size csize Nat.add Nat.mul disjoint_from length]; rewrite ?cells_size_f32, ?length_f32; cbn [cells_size csize Nat.add Nat.mul disjoint_from length]; lia].
Local Ltac xport_mem mo MU WM :=
repeat match goal with H : rw_cells rsegs mo _ _ |- _ => first [xport MU WM H | clear H] end.

Local Ltac solve_munch3 MU1 MU2 MU3 :=
eapply munch_trans; [eapply munch_weaken_to; [exact MU1|] | eapply munch_trans; [eapply munch_weaken_to; [exact MU2|]| eapply munch_weaken_to; [exact MU3|]]].

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

Lemma land64_small : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac land_cases K :=
repeat match type of K with context [Z.land ?x 18446744073709551615] =>
let E := fresh "E" in
destruct (Z.eq_dec x (2^64)) as [E|E];
[ rewrite E in K; change (Z.land (2^64) 18446744073709551615) with 0 in K
| rewrite (land64_small x) in K by lia ] end.
Ltac kill_branch K := zify_cond K; try (rewrite ?unsigned_lit in K by lia); try (exfalso; first [lia | congruence | (land_cases K; first [lia | congruence])]).
Local Ltac ub_ptr_chk := step; if_false_z; step; step; if_false_z.
Local Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => idtac end.
Local Ltac at_if := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.
Local Ltac walk_to p := repeat (tryif at_pc p then fail else (tryif at_if then first [if_false_z | if_true_z] else zstep));
first [at_pc p | lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 1 "walk_to stuck at" pc end].

Section COPY4.
Context {RCEIL : RunCeiling}.
Variables (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) (S P c : Z).
Variables (ra sp gp tp t0 t1 t2 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Hypothesis MI : mem_inv rsegs m.
Hypothesis X : rw_cells rsegs m S (SBCELLS s a OUT j).
Hypothesis NBS : sbd_nbSubframes s = 4.
Hypothesis SB : 0 < S /\ S + 160 < 2^63.
Hypothesis APS : P + 16 <= S \/ S + 160 <= P.

Definition copy4_post (G : Z) (pg : list word) : machine_state -> Prop :=
fun ms' => exists m' F' ws' (xt0 xt1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 : word),
ms' = MS (mkR ra sp gp tp xt0 xt1 t2 (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x2ed88) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' P (f32 ws') /\ length ws' = 4%nat /\ rw_cells rsegs m' S (SBCELLS s a OUT j) /\ rw_cells rsegs m' G (f32 pg)
/\ munch [(P, P + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

#[using="MI X NBS SB APS"] Lemma sbarm_copy4 : forall (pc G : Z) (ws pg : list word),
(pc = 0x2e7ac /\ G = a_pg a) \/ (pc = 0x2ec90 /\ G = a_er a) ->
rw_cells rsegs m P (f32 ws) -> length ws = 4%nat -> rw_cells rsegs m G (f32 pg) -> length pg = 4%nat ->
(P + 16 <= G \/ G + 16 <= P) ->
S mod 8 = 0 -> 0 < P -> P mod 4 = 0 -> 0 < G -> G mod 4 = 0 ->
evt rsegs (copy4_post G pg)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 S) a0 a1 (Z_to_bv 64 P) (Z_to_bv 64 c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
intros pc G ws pg PCG ARG LW PG LP APG S8 P0 P4 G0 G4. unfold sb_cells in X.
pose proof (rw_cells_bound _ _ _ _ ARG) as B. rewrite cells_size_f32, LW in B.
pose proof (rw_cells_bound _ _ _ _ PG) as BG. rewrite cells_size_f32, LP in BG.
destruct ws as [|w0 [|w1 [|w2 [|w3 [|]]]]]; try discriminate LW. destruct pg as [|g0 [|g1 [|g2 [|g3 [|]]]]]; try discriminate LP.
rewrite !f32_cons, ?f32_nil in ARG. rewrite !f32_cons, ?f32_nil in PG. cbn [f32 map] in ARG, PG.
pose proof (munch_refl [(P, P + 16)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct PCG as [[-> ->]|[-> ->]].
all: ub_ptr_chk.
all: step; rewrite NBS; rewrite ?sx32_lit by lia.
all: walk_to 0x2ed88.
all: apply evt_done; unfold copy4_post; eexists _, _, [_; _; _; _]; do 9 eexists; rewrite ?unsigned_lit by lia.
all: split; [reflexivity|].
all: rewrite !f32_cons, ?f32_nil; cbn [f32 map]; split; [eassumption|]; split; [reflexivity|]; split; [unfold sb_cells; eassumption|]; split; [eassumption|].
all: repeat (split; [assumption|]); assumption.
Qed.
End COPY4.

Ltac exc_sb := intros _; first [ exact I | lazymatch goal with |- dec_exc_ready _ _ _ (snd (speex_decoder_ctl (DecSB ?s0 ?l0) ?q)) =>
let E := fresh "E" in destruct (ctl_sb_shape s0 l0 q) as (? & ? & E); rewrite E; exact I end ].

Theorem rctl_sbB {RCEIL : RunCeiling} : forall s low, rctl_at low -> rctl_atP (fun r => creq_grp1 r = false) (DecSB s low).
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
destruct r; cbn in OK; try (exfalso; exact OK); try discriminate GRP; cbn [ctl_req_code creq_size] in *; cbn [creq_pre] in PRE; cbn [sbctl_armpc Z.eqb Pos.eqb]; cbn [creq_ptr_ok] in PTR; try destruct PTR as [P0 P4].
-
destruct PRE as (ws & ARG & LWS). xport MU1 WM1 ARG.
pose proof BU1 as sfP_; first [ sf_destruct 8%nat sfP_ as Bg0 Bg1 Bex Boq Biq Bmsp Bpg Ber | sf_fb; destruct sfP_ as (Bg0 & Bg1 & Bex & Boq & Biq & Bmsp & Bpg & Ber) ]. pose proof JOK as sfP_; first [ sf_destruct 10%nat sfP_ as J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 | sf_fb; destruct sfP_ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10) ].
assert (INPG : In (sbd_pi_gain s, a_pg a, 16) LBD) by (rewrite ELBD; apply in_app_iff; left; cbn; tauto).
pose proof (APB _ INPG) as APG. cbn [blk_addr blk_size fst snd] in APG.
pose proof (BR _ INPG) as BRG. cbn [blk_addr blk_size fst snd] in BRG. unfold rblock_range in BRG. destruct BRG as (G0 & G16 & _).
eapply evt_cut.
{ eapply (sbarm_copy4 s a OUT j S P _ _ _ gp tp t0 xt1 t2 xa0 xa1 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 MI1 X Inbs ltac:(lia) ltac:(lia) 0x2e7ac (a_pg a) ws (sj_pg j));
[left; split; reflexivity| exact ARG| exact LWS| exact Bpg| exact J9| exact APG| exact AL| exact P0| exact P4| exact G0| lia]. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 20%nat sfH_ as m3 F3 ws' xt0' xt1' xa1' xa2' xa3' xa4' xa5' xa6' xa7' -> ARG3 LWS' X3 PG3 MU3 WM3 MI3 | sf_fb; destruct sfH_ as (m3 & F3 & ws' & xt0' & xt1' & xa1' & xa2' & xa3' & xa4' & xa5' & xa6' & xa7' & -> & ARG3 & LWS' & X3 & PG3 & MU3 & WM3 & MI3) ]. clear ARG.
xport MU3 WM3 FR.
assert (BU3 : sb_bufs rsegs m3 a j).
{ eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I].
pose proof (APB b ltac:(rewrite ELBD; apply in_app_iff; left; right; exact Hb)). lia. }
assert (RL3 : DREP OUTL STEREO m3 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL1| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (APB b (INL _ Hb)). lia. }
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -32)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
clear X BU1.
eapply evt_cut. { eapply (sbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR| exact MI3]. }
cbv beta. intros ms3 ->.
release_frame FR ST3 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F3) | exact (fc) | exact (m3) | ] | sf_fb; exists F3, fc, m3 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU3|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3); cbn; (split; [lia| exact I]). }
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [speex_decoder_ctl fst snd decst_rep]. fold (DREP OUT STEREO m3).
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
split; [exact X3|]. split; [exact BU3| exists OUTL; exact RL3].
+ split; [cbn [creq_post speex_decoder_ctl fst]; exists ws'; split; [exact ARG3| exact LWS']| exc_sb].
-
destruct PRE as ((ws & ARG & LWS) & _). xport MU1 WM1 ARG.
pose proof BU1 as sfP_; first [ sf_destruct 8%nat sfP_ as Bg0 Bg1 Bex Boq Biq Bmsp Bpg Ber | sf_fb; destruct sfP_ as (Bg0 & Bg1 & Bex & Boq & Biq & Bmsp & Bpg & Ber) ]. pose proof JOK as sfP_; first [ sf_destruct 10%nat sfP_ as J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 | sf_fb; destruct sfP_ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10) ].
assert (INER : In (sbd_exc_rms s, a_er a, 16) LBD) by (rewrite ELBD; apply in_app_iff; left; cbn; tauto).
pose proof (APB _ INER) as APG. cbn [blk_addr blk_size fst snd] in APG.
pose proof (BR _ INER) as BRG. cbn [blk_addr blk_size fst snd] in BRG. unfold rblock_range in BRG. destruct BRG as (G0 & G16 & _).
eapply evt_cut.
{ eapply (sbarm_copy4 s a OUT j S P _ _ _ gp tp t0 xt1 t2 xa0 xa1 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 MI1 X Inbs ltac:(lia) ltac:(lia) 0x2ec90 (a_er a) ws (sj_er j));
[right; split; reflexivity| exact ARG| exact LWS| exact Ber| exact J10| exact APG| exact AL| exact P0| exact P4| exact G0| lia]. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 20%nat sfH_ as m3 F3 ws' xt0' xt1' xa1' xa2' xa3' xa4' xa5' xa6' xa7' -> ARG3 LWS' X3 PG3 MU3 WM3 MI3 | sf_fb; destruct sfH_ as (m3 & F3 & ws' & xt0' & xt1' & xa1' & xa2' & xa3' & xa4' & xa5' & xa6' & xa7' & -> & ARG3 & LWS' & X3 & PG3 & MU3 & WM3 & MI3) ]. clear ARG.
xport MU3 WM3 FR.
assert (BU3 : sb_bufs rsegs m3 a j).
{ eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I].
pose proof (APB b ltac:(rewrite ELBD; apply in_app_iff; left; right; exact Hb)). lia. }
assert (RL3 : DREP OUTL STEREO m3 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL1| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (APB b (INL _ Hb)). lia. }
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -32)) by (eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3| cbn; lia]).
clear X BU1.
eapply evt_cut. { eapply (sbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR| exact MI3]. }
cbv beta. intros ms3 ->.
release_frame FR ST3 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F3) | exact (fc) | exact (m3) | ] | sf_fb; exists F3, fc, m3 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU3|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3); cbn; (split; [lia| exact I]). }
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [speex_decoder_ctl fst snd decst_rep]. fold (DREP OUT STEREO m3).
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
split; [exact X3|]. split; [exact BU3| exists OUTL; exact RL3].
+ split; [cbn [creq_post speex_decoder_ctl fst]; exists ws'; split; [exact ARG3| exact LWS']| exc_sb].
-
destruct PRE as (w & ARG). xport MU1 WM1 ARG.

ub_ptr_chk. step. step. step. step. step.
eapply evt_cut.
{ eapply (IH OUTL STEREO (a_low a) LBL CtlGetDtxStatus P lo). all: ih_sides RL1 TP1 BR INL NDL LAPL APB ST1.
cbn [creq_pre]. exists w. exact ARG. }
cbv beta. intros ms2 sfH_; first [ sf_destruct 26%nat sfH_ as y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 F2 fc2 m2 -> MU2 WM2 MI2 FRM2 ST2 RL2 CP2 EX2 | sf_fb; destruct sfH_ as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & FRM2 & ST2 & RL2 & CP2 & EX2) ].
rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in ST2 by lia. rewrite ret_pc_even by lia.
cbn [creq_post] in CP2. destruct CP2 as (ARG2 & V01). clear ARG.
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
destruct (speex_decoder_ctl low CtlGetDtxStatus) as [v0 low'] eqn:EC.
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F2) | exact (fc2) | exact (m2) | ] | sf_fb; exists F2, fc2, m2 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU2|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3).
- cbn. split; [lia| exact I].
- apply outside_ctlW. cbn [creq_size]. split; [lia|]. split; [exact O2|]. intros b Hb. apply O3. apply INL. exact Hb. }
split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact ST2|].
change (speex_decoder_ctl (DecSB s low) CtlGetDtxStatus) with (let '(v, low') := speex_decoder_ctl low CtlGetDtxStatus in (v, DecSB s low')).
rewrite EC. cbn [fst snd] in RL2, ARG2, V01 |- *.
split.
+ cbn [decst_rep]. fold (DREP OUT STEREO m2).
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
split; [exact X2|]. split; [exact BU2| exists OUTL; exact RL2].
+ split; [cbn [creq_post]; split; [exact ARG2| exact V01]| exc_sb].
-
destruct OK as [EP HOFF].

pose proof (conj MU1 WM1) as MW1. clear MU1 WM1.
pose proof (munch_refl [(S + 120, S + 128)] m1) as MU3. pose proof (wmono_refl rsegs m1) as WM3.
ub_ptr_chk. step. step. destruct MW1 as [MU1 WM1].
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m3 := mx) in *; clearbody m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
assert (BU3 : sb_bufs rsegs m3 a j).
{ eapply (sb_bufs_out _ s S); [exact BU1| exact JOK| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I].
pose proof (SAPB _ Hb). lia. }
assert (RL3 : DREP OUTL STEREO m3 (a_low a) low LBL).
{ eapply decst_rep_munch; [exact RL1| exact MU3| exact WM3|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (SAPL _ Hb). lia. }
match goal with H : stk rsegs m3 lo _ |- _ => rename H into ST3 end.
clear BU1 RL1.
eapply evt_cut. { eapply (sbctl_exit (bv_unsigned sp)); [lia| reflexivity| exact FR| exact MI3]. }
cbv beta. intros ms3 ->.
release_frame FR ST3 (bv_unsigned sp).
apply evt_done. unfold rctl_post. sf_eexists 14%nat. first [ unshelve sf_eexists 3%nat; [ exact (F) | exact (fc) | exact (m3) | ] | sf_fb; exists F, fc, m3 ].
split; [rewrite ?P4, ?AL, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply munch_trans; [eapply munch_weaken_to; [exact MU1|]| eapply munch_weaken_to; [exact MU3|]]; intros x OX; apply outside_ctlW in OX; cbn [creq_size] in OX; destruct OX as (O1 & O2 & O3); cbn; (split; [| exact I]).
- lia.
- specialize (O3 _ INS). unfold blk_addr, blk_size, SBSTATE_SIZEOF in O3. cbn [fst snd] in O3. lia. }
split; [eapply wmono_trans; [exact WM1| exact WM3]|]. split; [exact MI3|]. split; [exact FRM|]. split; [exact ST3|].
split.
+ cbn [speex_decoder_ctl fst snd decst_rep]. fold (DREP OUT STEREO m3).
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [exact ELBD|]. split; [exact AL|]. split; [exact POS|].
split; [unfold sb_inv in *; cbn; repeat split; try assumption; lia|]. split; [exact JOK|].
split; [| split; [exact BU3| exists OUTL; exact RL3]].
unfold sb_cells. cbn -[Z.add Z.mul Z_to_bv rsegs]. unfold sb_isave_ptr. cbn [sbd_innov_save set_sbd_innov_save]. rewrite <- EP.
rewrite ?unsigned_lit in X by lia. first [exact X | rewrite Z_to_bv_bv_unsigned in X; exact X | idtac "ISVFIX"].
+ split; [cbn [creq_post]; exact I| exc_sb].
Qed.

Theorem rctl_sb {RCEIL : RunCeiling} : forall s low, rctl_at low -> rctl_at (DecSB s low).
Proof. intros s low IH. apply rctl_at_join; [apply rctl_sbA| apply rctl_sbB]; exact IH. Qed.
