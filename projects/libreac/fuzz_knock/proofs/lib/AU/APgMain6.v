(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgMain6.v of this library: SEGMENT S6 CHECKS of
   libreac/fuzz_knock's ASan harness walk of LLVMFuzzerTestOneInput in fuzz_knock.asan-ubsan (sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82), pc 0x7f270-0x7f29c (12 instructions) plus the
   loop-head test 0x7f150, from ss_C to ss_L (the back edge, 0x7f154) or ss_X (the exit, 0x7f2c4).
   The proof is lib/A/APgMain6.v's (donor proofs/cgif/cgif_file_fuzzer/lib/A/ACfe.v at c8557374ad2e: :41-45, :67-140,
   :340-352, :383-388, :389-395), with the module paths of the lib/AU twins and the asan-ubsan pcs.  The asan-ubsan
   code differs from the asan code (internal path, sections 2 and 4):
   - d is in s8 (asan s11): the two aborts compare against s8, and the back edge pins x24 to N_d;
   - the trip counter counts DOWN: `addiw s10,s10,-1` at 0x7f294 then `bnez s10,0x7f150` at 0x7f298 (asan: `bltu s8,s10`
     exit at 0x7f240 before `addiw s10,s10,1`).  The engine folds the addiw over the countdown's atom 302 (range
     [1,4096]) into s10 = SOff 302 (-1), so U_atom_off reads it as 4096 - i - 1 (s6_cnt; the rreg of x26); the exit
     is taken when it is 0, i.e. at i = 4095, as the asan `bltu s8,s10` is;
   - the back edge goes to the loop-head test `beqz s9,0x7f2c4` at 0x7f150 (asan `bnez s9,0x7f10c` at 0x7f248): its
     taken arm is the second exit, its fall-through is ss_L at 0x7f154 with 1 <= rem.
   The back edge rebinds the fourteen slots 300-313 as the asan walk does, with the countdown 4096 - (i + 1) in slot
   302 (range [1,4096]) where the asan walk has i + 1 (range [0,4095]).

   THE CODE (asan-ubsan image; the 12 words + 0x7f150 agree with fuzz_knock.objdump.txt)
     0x7f270  lw   a0,32(s4)        a0 = k.granted      (s4 = F + 32, so the field is F + 64)
     0x7f274  bne  a0,s8,0x7f3fc    ABORT  granted <> d
     0x7f278  beqz s8,0x7f284
     0x7f27c  li   a0,1             d = 1 -> the expected state is 1
     0x7f280  j    0x7f28c
     0x7f284  snez a0,s2            d = 0 -> the expected state is 2 * (h <> 0)
     0x7f288  slli a0,a0,1
     0x7f28c  lw   a1,0(s4)         a1 = k.state
     0x7f290  bne  a1,a0,0x7f3fc    ABORT  state <> st_of d h
     0x7f294  addiw s10,s10,-1      countdown := 4096 - (i + 1)
     0x7f298  bnez s10,0x7f150      the back edge
     0x7f29c  j    0x7f2c4          leave (i = 4095)
     0x7f150  beqz s9,0x7f2c4       leave when rem = 0; else ss_L at 0x7f154

   THE TWO ABORTS, AND THE FACT THAT KILLS EACH (as in the asan walk)
     0x7f274  granted <> d : INV_C's inv_knock carries g = d and both are in {0,1}.  PLAIN:147.
     0x7f290  state <> (d ? 1 : h ? 2 : 0) : inv_knock carries st = st_ofZ d h.  PLAIN:148-149.
   The `__asan_handle_no_return; abort` block at 0x7f3fc is never entered and needs no walk.

   rule 24: no function proved. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgBase APgCSpec.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import APgMain7 APgStates APgLoop0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Set Hyps Limit 8. Set Printing Depth 14. Set Printing Width 250.

(* [DONOR A/ACfe.v:41-45]: read register r of the state as the given value v, proved by tac *)
Ltac rreg_tacG HS r v tac H :=
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); tac) end.
(* one windowed havoc of the env with the words ws at slots k, k+1, ...  [DONOR A/ACfe.v:340-352, generalised] *)
Ltac s6_havoc HS k ws :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win tfibsegs k Ev ssv msv ws HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
(* the equation of slot k + j after s6_havoc *)
Ltac s6_heq HS k j H :=
lazymatch type of HS with st_ok _ (havoc ?Ev k ?ws) _ _ =>
let n := eval vm_compute in (k + j)%nat in
let v := eval cbn [nth] in (nth j ws (Z_to_bv 64 0)) in
assert (H : ew (havoc Ev k ws) n = v) by (exact (ew_havoc_new Ev k ws j (Z_to_bv 64 0) ltac:(cbn [length]; lia))) end.
(* point register r at atom n: Eold gives the value of r's current atom, Enew the same value at n *)
Ltac s6_pin HS r n Eold Enew :=
lazymatch type of Enew with _ = ?v =>
let Q := fresh "Q" in
rreg_tacG HS r v ltac:(rewrite sv_denot_SOff0; ewpeel; exact Eold) Q;
ws_pin HS r (SOff n 0) Q ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Enew); clear Q end.
(* point the chunk at base b, offset off at atom n: Enew is the equation of n in the current env, Eold the
   equation of the chunk's current atom in an earlier one *)
Ltac s6_rechunk HS b off n Enew Eold :=
rechunk_at HS b off (SOff n 0) ltac:(rewrite !sv_denot_SOff0, Enew; ewpeel; symmetry; exact Eold).
(* the two exits: run to 0x7f2c4, join ss_X, hand over to the exit segment and discharge INV_X
   [DONOR A/ACfe.v:119-140] *)
Ltac s6_exit RX HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n Hk Hacc HPerm3 :=
pl_run_to HS HJ3 AG fpos F EFA3 0x7f2c4;
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac);
let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv;
relowRT HS AG E10 E11 E32 E10n E11n E32n;
rt_hand RX HS;
unfold INV_XP; cbv beta; cbn [c_T c_ly c_S];
split; [lia|]; split; [unfold ACC0 in Hacc; lia|]; split; [exact HPerm3 | exact I].

(* the countdown after `addiw s10,s10,-1`, s10 = SOff 302 c, read as 4096 - i + c from the countdown's equation *)
Ltac s6_cnt H Ei :=
lazymatch type of H with context [U ?Ev (SOff 302 ?cc)] =>
lazymatch type of Ei with _ = Z_to_bv 64 ?v =>
rewrite (U_atom_off Ev 302 v cc ltac:(ewpeel; exact Ei) ltac:(lia) ltac:(lia)) in H end end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
(* 0x7f284 snez a0,s2 / 0x7f288 slli a0,a0,1 over h in {0,1}: a0 = 2 * h *)
Lemma U_snez_sll1 : forall E n h, ew E n = Z_to_bv 64 h -> (h = 0 \/ h = 1) ->
U E (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff n 0)) (SLit 1)) = 2 * h.
Proof.
intros E n h Hn Hh. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, (U_atom E n h Hn) by lia. rewrite U_SLit.
destruct Hh as [-> | ->]; vm_compute; reflexivity.
Qed.
(* one atom fact of a state holds in its env *)
Lemma s6_atoms_ok_in : forall E l n f, atoms_ok E l -> In (n, f) l -> afact_ok E n f.
Proof.
intros E l n f. induction l as [|[m g] l IH]; cbn [atoms_ok In]; [tauto|].
intros [Hg Hl] [Heq | Hin]; [injection Heq as -> ->; exact Hg | exact (IH Hl Hin)].
Qed.
Lemma s6_st_ok_atom : forall E ss ms n f, st_ok tfibsegs E ss ms -> In (n, f) (f_atoms (ss_facts ss)) -> afact_ok E n f.
Proof. intros E ss ms n f HS Hin. apply st_ok_facts_ok in HS. exact (s6_atoms_ok_in E _ n f (proj1 HS) Hin). Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

Lemma rt_S6 : forall fuel : nat,
rt_from B MT FP POST ss_X (INV_X B MT) ->
rt_from B MT FP POST ss_L (INV_L B MT fuel) ->
rt_from B MT FP POST ss_C (INV_C B MT fuel).
Proof.
intros fuel RX RL. rt_prelude.
pose proof HINV as (Hk & Hacc & HPerm3 & rem & cur & i & d & h & now & quiet & op & due & hns & st & g &
p1 & p2 & c & Erem & Ecur & Ei & Ed & Eh & Enow & Equiet & HCELL & HKN & HCUR & Hfuel & Hi & Hnow).
cbn [c_ly c_S c_p c_n] in HPerm3.
unfold N_remT, N_curT, N_cnt, N_dC, N_hM, N_nowM, N_quietM, N_stC, N_p1, N_op, N_dueC, N_hnsM, N_gC, N_p2 in Erem, Ecur, Ei, Ed, Eh, Enow, Equiet, HCELL.
(* quiet's range, from ss_C's own fact on slot 333: INV_C bounds quiet only from above *)
assert (Qw : afact_ok E 333%nat (mkAF 0 9223406396593514176 0))
by (apply (s6_st_ok_atom E ss_C _ 333%nat _ HS); vm_compute; repeat (first [left; reflexivity | right])).
destruct Qw as (Qw & _ & _). cbn [af_lo af_hi] in Qw. rewrite Equiet in Qw.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
pl_run_to HS HJ3 AG fpos F EFA3 0x7f274.
pose proof HKN as HKN0. pose proof HCUR as HCUR0.
destruct HCELL as (Est & Ep1 & Eop & Edue & Ehns & Eg & Ep2 & Rp1 & Rp2 & Rop & Rdue & Rhns).
destruct HKN as (Hd & Hh & Hst & Hg & KI0 & KI1 & Hqn).
destruct HCUR as (Hcur & Hc0 & Hcn & Hrem0 & Hcur4096 & HcurHi). cbn [c_p c_n] in Hcur, Hcn.
assert (Rst : 0 <= st <= 2) by (rewrite Hst; unfold st_ofZ; destruct (Z.eqb d 1), (Z.eqb h 1); lia).
(* 0x7f274 bne a0,s8: a0 is g's atom, s8 is d's *)
br_split HS Hc1.
{ exfalso.
  hc_bool Hc1 ltac:(fun H => hc_atom H 343%nat g Eg ltac:(lia); hc_atom H 340%nat d Ed ltac:(lia)); hc_prop Hc1.
  lia. }
clear Hc1.
pl_run_to HS HJ3 AG fpos F EFA3 0x7f278.
(* 0x7f278 beqz s8: goal 1 is d = 0, goal 2 is d = 1; the two run in lock-step from here *)
br_split HS Hc2.
all: hc_bool Hc2 ltac:(fun H => hc_atom H 340%nat d Ed ltac:(lia)); hc_prop Hc2.
all: pl_run_to HS HJ3 AG fpos F EFA3 0x7f290.
(* 0x7f290 bne a1,a0: [d = 0 abort; d = 0 on; d = 1 abort; d = 1 on] *)
all: br_split HS Hc3.
1: { exfalso.
  hc_bool Hc3 ltac:(fun H => hc_atom H 341%nat st Est ltac:(lia);
    lazymatch type of H with context [U ?Ev (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 332 0)) (SLit 1))] =>
    rewrite (U_snez_sll1 Ev 332 h ltac:(ewpeel; exact Eh) Hh) in H end).
  hc_prop Hc3.
  assert (st = 2 * h) by (rewrite Hst, Hc2; unfold st_ofZ; destruct Hh as [-> | ->]; reflexivity). lia. }
2: { exfalso.
  hc_bool Hc3 ltac:(fun H => hc_atom H 341%nat st Est ltac:(lia)); hc_prop Hc3.
  assert (st = 1) by (rewrite Hst; replace d with 1 by lia; reflexivity). lia. }
all: clear Hc2 Hc3.
(* 0x7f294 addiw s10,s10,-1; the engine folds it over the countdown's atom (range [1,4096]) into s10 = SOff 302 (-1) *)
all: pl_run_to HS HJ3 AG fpos F EFA3 0x7f298.
(* 0x7f298 bnez s10,0x7f150: [d = 0 back; d = 0 exit; d = 1 back; d = 1 exit] *)
all: br_split HS Hc4.
2,4: s6_exit RX HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n Hk Hacc HPerm3.
all: hc_bool Hc4 ltac:(fun H => s6_cnt H Ei); hc_prop Hc4.
all: pl_run_to HS HJ3 AG fpos F EFA3 0x7f150.
(* 0x7f150 beqz s9,0x7f2c4, the loop-head test: [d = 0 exit; d = 0 back; d = 1 exit; d = 1 back] *)
all: br_split HS Hc5.
1,3: s6_exit RX HS HJ3 AG fpos F EFA3 E10 E11 E32 E10n E11n E32n Hk Hacc HPerm3.
all: hc_bool Hc5 ltac:(fun H => hc_atom H 323%nat rem Erem ltac:(lia)); hc_prop Hc5.
all: pl_run_to HS HJ3 AG fpos F EFA3 0x7f154.
(* THE BACK EDGE.  1: the four values inside [300,314) to scratch slots 900-903 *)
all: s6_havoc HS 900%nat [Z_to_bv 64 (4096 - (i + 1)); Z_to_bv 64 op; Z_to_bv 64 p1; Z_to_bv 64 p2].
all: s6_heq HS 900%nat 0%nat E900.
all: s6_heq HS 900%nat 1%nat E901.
all: s6_heq HS 900%nat 2%nat E902.
all: s6_heq HS 900%nat 3%nat E903.
all: rreg_tacG HS (@BV 5 26 I) (Z_to_bv 64 (4096 - (i + 1))) ltac:(rewrite denot_lit_U; f_equal;
  lazymatch goal with |- U ?Ev (SOff 302 ?cc) = _ =>
  rewrite (U_atom_off Ev 302 (4096 - i) cc); [lia | ewpeel; exact Ei | lia | lia] end) Q26.
all: ws_pin HS (@BV 5 26 I) (SOff 900 0) Q26 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E900).
all: clear Q26.
all: s6_rechunk HS 75%nat 40 901%nat E901 Eop.
all: s6_rechunk HS 75%nat 36 902%nat E902 Ep1.
all: s6_rechunk HS 75%nat 68 903%nat E903 Ep2.
(* 2: the facts on [300,314) dropped *)
all: lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let fa := eval vm_compute in (List.filter (fun p : nat * afact => win_free 300 14 (fst p)) (f_atoms (ss_facts ssx))) in
  let cs := eval vm_compute in (List.filter (cond_atoms_on (win_free 300 14)) (f_conds (ss_facts ssx))) in
  let al := eval vm_compute in (f_alias (ss_facts ssx)) in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
  clear HS; rename HS3 into HS end.
all: norm_ss HS.
all: clear Ei Eop Ep1 Ep2.
(* 3: the fourteen values of ss_L at 300-313 *)
all: s6_havoc HS 300%nat [Z_to_bv 64 rem; Z_to_bv 64 cur; Z_to_bv 64 (4096 - (i + 1)); Z_to_bv 64 d; Z_to_bv 64 h;
  Z_to_bv 64 now; Z_to_bv 64 quiet; Z_to_bv 64 op; Z_to_bv 64 due; Z_to_bv 64 hns; Z_to_bv 64 st; Z_to_bv 64 g;
  Z_to_bv 64 p1; Z_to_bv 64 p2].
all: s6_heq HS 300%nat 0%nat L300.
all: s6_heq HS 300%nat 1%nat L301.
all: s6_heq HS 300%nat 2%nat L302.
all: s6_heq HS 300%nat 3%nat L303.
all: s6_heq HS 300%nat 4%nat L304.
all: s6_heq HS 300%nat 5%nat L305.
all: s6_heq HS 300%nat 6%nat L306.
all: s6_heq HS 300%nat 7%nat L307.
all: s6_heq HS 300%nat 8%nat L308.
all: s6_heq HS 300%nat 9%nat L309.
all: s6_heq HS 300%nat 10%nat L310.
all: s6_heq HS 300%nat 11%nat L311.
all: s6_heq HS 300%nat 12%nat L312.
all: s6_heq HS 300%nat 13%nat L313.
(* 4: the registers, the k chunks and the quiet spill pointed at 300-313; d is in s8 (x24) *)
all: s6_pin HS (@BV 5 25 I) 300%nat Erem L300.
all: s6_pin HS (@BV 5 19 I) 301%nat Ecur L301.
all: s6_pin HS (@BV 5 26 I) 302%nat E900 L302.
all: s6_pin HS (@BV 5 24 I) 303%nat Ed L303.
all: s6_pin HS (@BV 5 18 I) 304%nat Eh L304.
all: s6_pin HS (@BV 5 21 I) 305%nat Enow L305.
all: s6_rechunk HS 75%nat 32 310%nat L310 Est.
all: s6_rechunk HS 75%nat 36 312%nat L312 E902.
all: s6_rechunk HS 75%nat 40 307%nat L307 E901.
all: s6_rechunk HS 75%nat 48 308%nat L308 Edue.
all: s6_rechunk HS 75%nat 56 309%nat L309 Ehns.
all: s6_rechunk HS 75%nat 64 311%nat L311 Eg.
all: s6_rechunk HS 75%nat 68 313%nat L313 E903.
all: s6_rechunk HS 70%nat 48 306%nat L306 Equiet.
all: clear Erem Ecur Ed Eh Enow Equiet Est Edue Ehns Eg E900 E901 E902 E903.
(* 5: the fourteen ranges ss_L carries (rl_atomsR, rl_atomsK); the countdown's is [1,4096] *)
all: add_fact HS 300%nat 0 67108863 L300 ltac:(lia).
all: add_fact HS 301%nat 4096 140737479966720 L301 ltac:(lia).
all: add_fact HS 302%nat 1 4096 L302 ltac:(lia).
all: add_fact HS 303%nat 0 1 L303 ltac:(lia).
all: add_fact HS 304%nat 0 1 L304 ltac:(lia).
all: add_fact HS 305%nat 0 9223406396593514176 L305 ltac:(lia).
all: lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  let HS3 := fresh "HS3" in
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 306%nat (mkAF 0 9223406396593514176 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite L306, Z.pow_0_r, Z.mod_1_r; split; [exact Qw | split; [reflexivity | lia]])) as HS3;
  clear HS; rename HS3 into HS end.
all: add_fact HS 307%nat 0 9223372036854775807 L307 ltac:(lia).
all: add_fact HS 308%nat 0 18446744073709551615 L308 ltac:(lia).
all: add_fact HS 309%nat 0 9223406396593514176 L309 ltac:(lia).
all: add_fact HS 310%nat 0 2 L310 ltac:(lia).
all: add_fact HS 311%nat 0 1 L311 ltac:(lia).
all: add_fact HS 312%nat 0 4294967295 L312 ltac:(lia).
all: add_fact HS 313%nat 0 4294967295 L313 ltac:(lia).
(* 6: the join to the loop head, and INV_L *)
all: ra_join_win HS ss_L 760%nat rt_loop_deads7_bv ltac:(idtac).
all: rebaseE HS AG HEv.
all: clear HEv.
all: relowRT HS AG E10 E11 E32 E10n E11n E32n.
all: rt_hand RL HS.
all: split; [exact Hk|].
all: split; [exact Hacc|].
all: split; [exact HPerm3|].
all: exists rem, cur, (i + 1), d, h, now, quiet, op, due, hns, st, g, p1, p2, c.
all: split; [exact L300|].
all: split; [exact L301|].
all: split; [exact L302|].
all: split; [exact L303|].
all: split; [exact L304|].
all: split; [exact L305|].
all: split; [exact L306|].
all: split; [exact (conj L310 (conj L312 (conj L307 (conj L308 (conj L309 (conj L311 (conj L313
  (conj Rp1 (conj Rp2 (conj Rop (conj Rdue Rhns)))))))))))|].
all: split; [exact HKN0|].
all: split; [exact HCUR0|].
all: split; [exact Hfuel|].
all: split; [lia|].
all: split; [lia|].
all: exact Hnow.
Qed.

End d.
End c.
