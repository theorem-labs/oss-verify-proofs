(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan harness walk of LLVMFuzzerTestOneInput
   (fuzz_knock.asan, sha256 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118): SEGMENT S5 MID,
   pc 0x7f1c4-0x7f218, from ss_M to ss_C (both lib/A/APgLoop0.v).  Modelled on proofs/cgif/cgif_file_fuzzer/lib/A at
   c8557374ad2e: ACfe.v:67-70 (the segment lemma), :155-212 (the call site: the ra / s0 words of the stack region, the
   frame chain through rt_chain, the zero shadow bytes of the callee's object), :228-273 (the call through SRr_bind and
   the callee contract), :274-316 (its post, reseatL and the kept-region cases); ACf6.v:52-62 (rt_region_kept_eq);
   ACf9.v:252-282 (the dead-register havoc of ra_join_win, reused as havoc_deads). *)

(* THE CODE (A image)
     0x7f1c4 andi a0,s7,2; beqz a0,0x7f21c                     (no STEP call)
     0x7f1cc mv a0,s4; mv a1,s5; jal reac_knock_step (0x7f570)  (r := reac_knock_step(&k, now))
     0x7f1d8 beqz a0,0x7f208
     0x7f1dc li a1,1; bne a0,a1 -> ABORT A1; bnez s11 -> ABORT A2; lw a0,32(s4); beqz a0 -> ABORT A3;
             ld a0,48(s1); sub a0,s5,a0; ld a1,40(s1); bgeu a1,a0 -> ABORT A4; li s11,1; j 0x7f21c
     0x7f208 bnez s11,0x7f21c; ld a0,48(s1); sub a0,s5,a0; ld a1,32(s1); bgeu a0,a1 -> ABORT A5
     0x7f21c (ss_C)

   Knock-specific changes:
   - the callee is reac_knock_step at 0x7f570 through a Theorem Labs lane's tknock_step_specX (lib/A/APgCSpec.v:142-158) at
     segs := tfibsegs, in place of read_frameconfig through trfc_specX;
   - its object is k = F+32 (40 bytes) in the class-1 harness frame: afobj comes from the frame and the 5 zero shadow
     bytes of k (chunks 4-8 of the frame's shadow region), obj_at from the 7 chunks of the k region (s5_kf);
   - the k region is the one region not kept over the call; after it, it is rebuilt from kn_post_step's obj_at with
     fresh atoms N_stC / N_dueC / N_gC (341-343) for state / due / granted;
   - s5_step_facts reads knock_step_f (APgCSpec.v:26-31) against inv_knock and gives the facts that kill the five
     aborts to 0x7f3cc (A1 r not in {0,1}; A2 r = 1 with d <> 0; A3 r = 1 with granted = 0; A4 r = 1 with
     now - quiet <= 499999999; A5 r = 0, d = 0 with now - quiet >= 500000000; plain proof
     lib/Prog/LLVMFuzzerTestOneInput.v:207-240, lib/Prog/reac_knock_step_c.v:11-18); U_sub_atoms reads `sub` in the
     executor's linear form;
   - every live path (no call; r = 0 with d <> 0; r = 0 with d = 0; r = 1) joins ss_C with d' in N_dC (340) and the
     same atoms 340-343.  On the call paths the branch conditions are dropped and the dead registers re-havocked at
     window 800 first (drop_conds, havoc_deads): the call's clobber havoc puts the caller-saved registers at atoms
     736-751, inside ss_C's window 740.

   Section hypotheses: MTL, TL, LAWS, ML (as every segment) and STEP : tknock_step_specX tfibsegs B MT
   A_reac_knock_step (a Theorem Labs lane's contract).  rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm APgRt APgBase APgCSpec APgLoop0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the dead registers again, at a window of our choice (the middle part of ra_join_win, APgLoop0.v) *)
Ltac havoc_deads HS N deads :=
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let dl := eval cbv in deads in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win tfibsegs N Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set_regs_rec HS N vals' 0%nat dl end;
norm_ss HS.
(* forget the branch conditions (the join drops them anyway; this drops them before a havoc window check) *)
Ltac drop_conds HS :=
norm_ss HS;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval vm_compute in (f_atoms (ss_facts ssx)) in
let al := eval vm_compute in (f_alias (ss_facts ssx)) in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa [] al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS.

(* one field of k, read out of the k region's chunk [A/ACep.v field_of_region] *)
Ltac s5_kf HRK B75 F fo off w e v Hv :=
lazymatch type of HRK with region_ok _ ?Ex _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
replace (F + 32 + fo) with (F + off) by (clear; lia);
split; [ apply (field_of_region Ex _ 75 F cs lo hi wlo whi off w e v HRK B75);
         [ cbn [In]; repeat (first [left; reflexivity | right])
         | rewrite sv_denot_SOff0; exact Hv
         | cbn; lia | cbn; lia ]
       | cbn; lia ] end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.

Lemma rt_region_kept_eq : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview tfibsegs H2 m2 a = aview tfibsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- intros _. apply (apresent_writable tfibsegs). apply Hp. exact Ha.
Qed.

(* `sub a0,s5,a0` (now - quiet) in the executor's linear form now + quiet * (-1) *)
Lemma U_sub_atoms : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= y <= x -> x < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff a 0) (SMd M_MUL (SOff b 0) (SLit (-1)))) = x - y.
Proof.
intros E a b x y Ha Hb Hxy Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E a x Ha), (U_atom E b y Hb), U_SLit by lia. unfold zcanon, M64.
replace ((-1) mod 2 ^ 64) with 18446744073709551615 by reflexivity. rewrite Zplus_mod_idemp_r.
replace (x + y * 18446744073709551615) with ((x - y) + y * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma s5_step_facts : forall d h st g op due hns quiet now r st' due' g',
inv_knock d h st g op due hns quiet now -> 0 <= due <= 18446744073709551615 -> 0 <= hns <= 9223406396593514176 ->
knock_step_f st g due hns now = (r, st', due', g') ->
0 <= st' <= 2 /\ 0 <= g' <= 1 /\ 0 <= due' <= 18446744073709551615 /\
((r = 0 /\ st' = st /\ due' = due /\ g' = g /\ (d = 0 -> now - quiet < L_NS)) \/
 (r = 1 /\ d = 0 /\ st' = 1 /\ g' = 1 /\ L_NS <= now - quiet)).
Proof.
intros d h st g op due hns quiet now r st' due' g' (Hd & Hh & Hst & Hg & K0 & K1 & Hq) Rdue Rhns Hs.
unfold knock_step_f in Hs. subst st g. unfold st_ofZ in *.
destruct Hd as [-> | ->]; destruct Hh as [-> | ->]; cbn [Z.eqb Pos.eqb] in *.
- destruct (K0 eq_refl eq_refl) as [-> ->]. destruct (now <? op + L_NS) eqn:Hlt; injection Hs as <- <- <- <-.
  + apply Z.ltb_lt in Hlt. split; [lia|]. split; [lia|]. split; [lia|]. left. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros _. lia.
  + apply Z.ltb_ge in Hlt. unfold L_NS in *. split; [lia|]. split; [lia|]. split; [lia|]. right. lia.
- specialize (K1 eq_refl eq_refl). subst hns.
  destruct ((now <=? quiet) || (now - quiet <? L_NS)) eqn:Hlt; injection Hs as <- <- <- <-.
  + split; [lia|]. split; [lia|]. split; [lia|]. left. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros _.
    apply orb_true_iff in Hlt. destruct Hlt as [Hlt | Hlt]; [apply Z.leb_le in Hlt | apply Z.ltb_lt in Hlt]; unfold L_NS in *; lia.
  + apply orb_false_iff in Hlt. destruct Hlt as [Hl1 Hl2]. apply Z.leb_gt in Hl1. apply Z.ltb_ge in Hl2.
    rewrite Z.mod_small by (unfold L_NS; lia).
    unfold L_NS in *. split; [lia|]. split; [lia|]. split; [lia|]. right. lia.
- injection Hs as <- <- <- <-. split; [lia|]. split; [lia|]. split; [lia|]. left. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros H; discriminate H.
- injection Hs as <- <- <- <-. split; [lia|]. split; [lia|]. split; [lia|]. left. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros H; discriminate H.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis STEP : tknock_step_specX (SK := SK) tfibsegs B MT A_reac_knock_step.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.

Lemma rt_S5 : forall fuel : nat,
  rt_from B MT FP POST ss_C (INV_C B MT fuel) ->
  rt_from B MT FP POST ss_M (INV_M B MT fuel).
Proof.
intros fuel RC. rt_prelude.
pose proof HINV as (Hk & Hacc & HPerm3 & rem & cur & i & d & h & now & quiet & op & due & hns & st & g & p1 & p2 & c & ev &
Erem & Ecur & Ei & Ed & Eh & Enow & Equiet & Eev & Rev & HCELL & HKN & HCUR & Hfuel & Hi & Hnow).
cbn [c_ly c_S c_p c_n] in HPerm3, HCUR.
pose proof HCELL as (Est & Ep1 & Eop & Edue & Ehns & Eg & Ep2 & Rp1 & Rp2 & Rop & Rdue & Rhns).
pose proof HKN as (Hd & Hh & Hst & Hg & KI0 & KI1 & Hqn).
cbv [N_remT N_curT N_i N_d N_hM N_nowM N_quietM N_ev N_stM N_p1 N_op N_due N_hnsM N_g N_p2] in Erem, Ecur, Ei, Ed, Eh, Enow, Equiet, Eev, Est, Ep1, Eop, Edue, Ehns, Eg, Ep2.
assert (Rst : 0 <= st <= 2) by (rewrite Hst; unfold st_ofZ; destruct (Z.eqb d 1), (Z.eqb h 1); lia).
assert (Rg : 0 <= g <= 1) by lia.
assert (Rd : 0 <= d <= 1) by lia.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* 0x7f1c4 andi a0,s7,2 *)
pl_run_to HS HJ3 AG fpos F EFA3 0x7f1c8.
upd_aboveW HUP HFr AG. clear_frames.
(* 0x7f1c8 beqz a0,0x7f21c *)
br_split HS Hc0.
{ (* ev & 2 = 0: no STEP call; d, state, due, granted are kept *)
  pl_run_to HS HJ3 AG fpos F EFA3 0x7f21c.
  clear_frames.
  add_atom_win HS 340%nat (Z_to_bv 64 d) E340.
  add_atom_win HS 341%nat (Z_to_bv 64 st) E341.
  add_atom_win HS 342%nat (Z_to_bv 64 due) E342.
  add_atom_win HS 343%nat (Z_to_bv 64 g) E343.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  add_fact HS 340%nat 0 1 E340 ltac:(lia).
  add_fact HS 341%nat 0 2 E341 ltac:(lia).
  add_fact HS 342%nat 0 18446744073709551615 E342 ltac:(lia).
  add_fact HS 343%nat 0 1 E343 ltac:(lia).
  rechunk_at HS 75%nat 32 (SOff 341 0) ltac:(rewrite !sv_denot_SOff0, E341, Est; reflexivity).
  rechunk_at HS 75%nat 48 (SOff 342 0) ltac:(rewrite !sv_denot_SOff0, E342, Edue; reflexivity).
  rechunk_at HS 75%nat 64 (SOff 343 0) ltac:(rewrite !sv_denot_SOff0, E343, Eg; reflexivity).
  rreg HS (27%bv : bv 5) R27.
  ws_pin HS (27%bv : bv 5) (SOff 340 0) R27 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E340, Ed; reflexivity).
  clear R27.
  ra_join_win HS ss_C 740%nat rt_loop_deads7_bv ltac:(idtac).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RC HS.
  split; [exact Hk|]. split; [exact Hacc|]. split; [exact HPerm3|].
  exists rem, cur, i, d, h, now, quiet, op, due, hns, st, g, p1, p2, c.
  split; [exact Erem|]. split; [exact Ecur|]. split; [exact Ei|]. split; [exact E340|]. split; [exact Eh|].
  split; [exact Enow|]. split; [exact Equiet|].
  split; [unfold inv_cells; split; [exact E341|]; split; [exact Ep1|]; split; [exact Eop|]; split; [exact E342|];
    split; [exact Ehns|]; split; [exact E343|]; split; [exact Ep2|]; lia|].
  split; [exact HKN|]. split; [exact HCUR|]. split; [exact Hfuel|]. split; [exact Hi|]. exact Hnow. }
(* ev & 2 <> 0: 0x7f1cc-0x7f1d4 mv a0,s4; mv a1,s5; jal reac_knock_step *)
pl_run_to HS HJ3 AG fpos F EFA3 0x7f570.
upd_aboveW HUP HFr AG. clear_frames.
rebv HS E70 RF B70 B75.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (8%bv : bv 5) Rs0. rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
  assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp; exact B70);
  assert (EraX : raZ rg = 0x7f1d8) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
  assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0; exact Usp3);
  assert (Ea0X : getr rg 10 = w64 (F + 32)) by (rewrite Ra0, B75; reflexivity);
  assert (Ea1X : getr rg 11 = w64 now) by (rewrite Ra1, Enow; reflexivity) end.
clear Ra0 Ra1.
(* the call's frame-chain premise [A/ACfe.v:164-185] *)
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
(* the 5 shadow bytes of k are 0: range_addressable (F+32) 40 [A/ACfe.v:186-207, A/ACf0.v:56-78] *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 88%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew Ex 88) = SB + F / 8) by (first [rewrite E88 | ewpeel; rewrite E88]; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia);
assert (ZS : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) (YP09.r_chunks rS) -> aview tfibsegs (w_H W3) (ms_mem msX) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 88 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ] end.
lazymatch type of HS with st_ok _ _ _ (restrict (w_H ?Wx) ?msX) =>
assert (RAk : range_addressable (aview tfibsegs (w_H Wx) (ms_mem msX)) SHADOW_OFF (F + 32) 40) end.
{ apply zero_shadow_of_bytes; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); apply Z_mod_mult | reflexivity | clear; lia |].
intros j Hj. change (40 / 8) with 5 in Hj. rewrite <- SB_SHADOW_OFF.
replace ((F + 32) / 8) with (F / 8 + 4) by (rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia);
replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); rewrite Z_div_mult by (clear; lia); clear; lia).
replace (SB + (F / 8 + 4) + j) with (SB + F / 8 + (4 + j)) by (clear; lia).
assert (Hj5 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by (clear - Hj; lia).
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]]; apply ZS; cbn; tauto. }
clear ZS.
(* the seven cells of k, read out of the k region *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rk := eval vm_compute in (nth 0 rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wx) msX) 0 rk HS ltac:(vm_compute; reflexivity)) as HRK; cbn [ms_mem restrict] in HRK;
assert (HOBJ0 : obj_at tfibsegs (mrestrict (w_H Wx) (ms_mem msX)) (F + 32) LAY_Knock [st; p1; op; due; hns; g; p2]) end.
{ unfold LAY_Knock. cbn [obj_at]. unfold field_ok. cbn [fst snd].
  split; [s5_kf HRK B75 F 0 32 4%N (SOff 334 0) st Est|].
  split; [s5_kf HRK B75 F 4 36 4%N (SOff 312 0) p1 Ep1|].
  split; [s5_kf HRK B75 F 8 40 8%N (SOff 307 0) op Eop|].
  split; [s5_kf HRK B75 F 16 48 8%N (SOff 308 0) due Edue|].
  split; [s5_kf HRK B75 F 24 56 8%N (SOff 335 0) hns Ehns|].
  split; [s5_kf HRK B75 F 32 64 4%N (SOff 311 0) g Eg|].
  split; [s5_kf HRK B75 F 36 68 4%N (SOff 313 0) p2 Ep2|].
  exact I. }
clear HRK.
(* 0x7f1d4 jal reac_knock_step, through a Theorem Labs lane's contract [A/ACfe.v:228-273] *)
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
eapply SRr_bind;
[ eapply (STEP LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
(F + 32) now 1 fpos (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) st p1 op due hns g p2 HJ3);
[ rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
| rewrite EraX; clear; lia
| rewrite Rgp; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
| rewrite Rtp; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
| exact Ea0X
| exact Ea1X
| clear - Hnow Hi; lia
| rewrite EspX, Es0X; exact Hch1
| rewrite EspX; exact Hsp1al16
| rewrite EspX; unfold T_step_STK; rewrite FFS; clear - Hsp1; lia
| rewrite EspX; clear - Hsp1; lia
| left; reflexivity
| clear; lia
| rewrite EFA3; fold F; rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult
| rewrite EFA3; fold F; clear; lia
| rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
| rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); apply Z_mod_mult
| clear - HF4096; lia
(* a Theorem Labs lane's R1 premise (APgCSpec.v): k is not on the callee's stack.  k = F + 32 lies in the class-1
   fake frame, whose end is <= alloc_ceiling (HFceil); alloc_ceiling <= ly_stk_lo ly (Hceil) <= the bottom of
   the harness's stack allowance (Hslo, Hstk0, FFS); and the callee's sp is sp1 >= sp0 - 208 (Hsp1). *)
| right; rewrite EspX; unfold T_step_STK; clear - HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; lia
| split; [exists 1, fpos; split; [exact Hfin3|]; split; [clear; lia|]; rewrite EFA3; fold F;
          split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult|];
          split; [clear; lia | change (fs_frame_bytes 1) with 128; clear; lia]|];
  split; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); apply Z_mod_mult | exact RAk]
| exact HOBJ0
| unfold EV_step; rewrite HEV in Hev, Hk; clear - Hev Hk; lia ]
| ] end end.
(* the post of reac_knock_step *)
cbv beta. intros W4 c4 Hwle4 HPOST.
destruct (knock_step_f st g due hns now) as [[[r st'] due'] g'] eqn:Estep.
unfold kn_post_step in HPOST.
destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & HPerm4 & HIO4 & HMLE4 & K1 & K2 & K3 & K4 & HLAST).
rewrite Estep in HLAST. destruct HLAST as (Ha04 & HOBJ).
rewrite EspX in K1. rewrite Rra.
pose proof (mle_station MT S S3 S4 acc 0 MTL HMLE HMLE4) as HMLE4c.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(1, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
(* every region but k (index 0) is kept: k is the callee's to write *)
reseatL HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ evalE AG
| intros a Ha; apply (K3 1 fpos a Hfin3);
  [ right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; clear - Ha; unfold SB in *; lia
  | clear - Ha HF8c HF8lo HFhigh C3; unfold SB in *; zone_lia ]
| intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ evalE AG
| intros a Ha; apply (K3 1 fpos a Hfin3);
  [ left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear - Ha; lia | clear - Ha; lia ]
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some ?nb) _ _ _ _ _) =>
eapply rt_region_kept_eq; [ evalE AG
| intros a Ha; apply K1; clear - Ha Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HFceil; unfold T_step_STK in *; lia
| intros a Ha; apply Hpres4; clear - Ha Hsp1 FFS Hslo Hshi; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
rreg HS (10%bv : bv 5) Rres. rewrite Ha04 in Rres. symmetry in Rres.
destruct (s5_step_facts d h st g op due hns quiet now r st' due' g' HKN ltac:(lia) ltac:(lia) Estep) as (Rst' & Rg' & Rdue' & HSTEP).
(* k back, with the post's cells: state, due and granted are new atoms *)
add_atom_win HS 341%nat (Z_to_bv 64 st') E341.
add_atom_win HS 342%nat (Z_to_bv 64 due') E342.
add_atom_win HS 343%nat (Z_to_bv 64 g') E343.
rb HS AG E10 E11 E32 E10n E11n E32n.
add_fact HS 341%nat 0 2 E341 ltac:(lia).
add_fact HS 342%nat 0 18446744073709551615 E342 ltac:(lia).
add_fact HS 343%nat 0 1 E343 ltac:(lia).
rebv HS E70 RF B70 B75.
unfold LAY_Knock in HOBJ. cbn [obj_at] in HOBJ. unfold field_ok in HOBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in HOBJ.
destruct HOBJ as ((Vk0 & _) & (Vk1 & _) & (Vk2 & _) & (Vk3 & _) & (Vk4 & _) & (Vk5 & _) & (Vk6 & _) & _).
lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _
(YP09.mkRegion (Some 75%nat) 32 72 32 72
[YP09.mkChunk 32 (CVal 4 (SOff 341 0)); YP09.mkChunk 36 (CVal 4 (SOff 312 0)); YP09.mkChunk 40 (CVal 8 (SOff 307 0));
 YP09.mkChunk 48 (CVal 8 (SOff 342 0)); YP09.mkChunk 56 (CVal 8 (SOff 335 0));
 YP09.mkChunk 64 (CVal 4 (SOff 343 0)); YP09.mkChunk 68 (CVal 4 (SOff 313 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite B75; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 32 4 (SOff 341 0) st'); [rewrite sv_denot_SOff0; exact E341 | zside | zside | replace (F + 32) with (F + 32 + 0) by lia; exact Vk0]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 36 4 (SOff 312 0) p1); [rewrite sv_denot_SOff0; exact Ep1 | zside | zside | replace (F + 36) with (F + 32 + 4) by lia; exact Vk1]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 40 8 (SOff 307 0) op); [rewrite sv_denot_SOff0; exact Eop | zside | zside | replace (F + 40) with (F + 32 + 8) by lia; exact Vk2]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 48 8 (SOff 342 0) due'); [rewrite sv_denot_SOff0; exact E342 | zside | zside | replace (F + 48) with (F + 32 + 16) by lia; exact Vk3]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 56 8 (SOff 335 0) hns); [rewrite sv_denot_SOff0; exact Ehns | zside | zside | replace (F + 56) with (F + 32 + 24) by lia; exact Vk4]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 64 4 (SOff 343 0) g'); [rewrite sv_denot_SOff0; exact E343 | zside | zside | replace (F + 64) with (F + 32 + 32) by lia; exact Vk5]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 68 4 (SOff 313 0) p2); [rewrite sv_denot_SOff0; exact Ep2 | zside | zside | replace (F + 68) with (F + 32 + 36) by lia; exact Vk6]|];
  apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite B75; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 HF8c; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
clear Vk0 Vk1 Vk2 Vk3 Vk4 Vk5 Vk6.
destruct HSTEP as [(Hr0 & Hst' & Hdue' & Hg' & Hq0) | (Hr1 & Hd0 & Hst' & Hg' & Hq1)].
- (* r = 0: nothing of k moved *)
  subst r st' due' g'.
  br_split HS Hc1.
  2: { exfalso. lazymatch type of Rres with ew _ ?na = _ => hc_bool Hc1 ltac:(fun H => hc_atom H na 0 Rres ltac:(lia)) end. hc_prop Hc1. lia. }
  pl_run_to HS HJ4 AG fpos F EFA4 0x7f208. clear_frames.
  br_split HS Hc2.
  + (* d <> 0: 0x7f208 bnez s11 -> 0x7f21c *)
    pl_run_to HS HJ4 AG fpos F EFA4 0x7f21c. clear_frames.
    add_atom_win HS 340%nat (Z_to_bv 64 d) E340.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    add_fact HS 340%nat 0 1 E340 ltac:(lia).
    rreg HS (27%bv : bv 5) R27.
    ws_pin HS (27%bv : bv 5) (SOff 340 0) R27 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E340, Ed; reflexivity).
    clear R27.
    drop_conds HS.
    havoc_deads HS 800%nat rt_loop_deads7_bv.
    ra_join_win HS ss_C 740%nat rt_loop_deads7_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RC HS.
    split; [unfold EV_step; lia|]. split; [unfold ACC0 in *; lia|]. split; [exact (Permutation_trans HPerm4 HPerm3)|].
    exists rem, cur, i, d, h, now, quiet, op, due, hns, st, g, p1, p2, c.
    split; [exact Erem|]. split; [exact Ecur|]. split; [exact Ei|]. split; [exact E340|]. split; [exact Eh|].
    split; [exact Enow|]. split; [exact Equiet|].
    split; [unfold inv_cells; split; [exact E341|]; split; [exact Ep1|]; split; [exact Eop|]; split; [exact E342|];
      split; [exact Ehns|]; split; [exact E343|]; split; [exact Ep2|]; lia|].
    split; [exact HKN|]. split; [exact HCUR|]. split; [exact Hfuel|]. split; [exact Hi|]. exact Hnow.
  + hc_bool Hc2 ltac:(fun H => hc_atom H 303%nat d Ed ltac:(lia)). hc_prop Hc2.
    assert (Rq0 : 0 <= quiet) by (destruct Hh as [Hh0 | Hh1]; [destruct (KI0 Hc2 Hh0) as [-> _]; lia | rewrite <- (KI1 Hc2 Hh1); lia]).
    pl_run_to HS HJ4 AG fpos F EFA4 0x7f218. clear_frames.
    br_split HS Hc3.
    * exfalso. hc_bool Hc3 ltac:(fun H => lazymatch type of H with context [U ?E' (SAlu ALU_ADD (SOff 331 0) (SMd M_MUL (SOff 333 0) (SLit (-1))))] =>
        rewrite (U_sub_atoms E' 331 333 now quiet ltac:(ewpeel; exact Enow) ltac:(ewpeel; exact Equiet) ltac:(lia) ltac:(lia)) in H end).
      hc_prop Hc3. specialize (Hq0 Hc2). unfold L_NS in Hq0. lia.
    * pl_run_to HS HJ4 AG fpos F EFA4 0x7f21c. clear_frames.
      add_atom_win HS 340%nat (Z_to_bv 64 d) E340.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      add_fact HS 340%nat 0 1 E340 ltac:(lia).
      rreg HS (27%bv : bv 5) R27.
      ws_pin HS (27%bv : bv 5) (SOff 340 0) R27 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E340, Ed; reflexivity).
      clear R27.
      drop_conds HS.
      havoc_deads HS 800%nat rt_loop_deads7_bv.
      ra_join_win HS ss_C 740%nat rt_loop_deads7_bv ltac:(idtac).
      rb HS AG E10 E11 E32 E10n E11n E32n.
      rt_hand RC HS.
      split; [unfold EV_step; lia|]. split; [unfold ACC0 in *; lia|]. split; [exact (Permutation_trans HPerm4 HPerm3)|].
      exists rem, cur, i, d, h, now, quiet, op, due, hns, st, g, p1, p2, c.
      split; [exact Erem|]. split; [exact Ecur|]. split; [exact Ei|]. split; [exact E340|]. split; [exact Eh|].
      split; [exact Enow|]. split; [exact Equiet|].
      split; [unfold inv_cells; split; [exact E341|]; split; [exact Ep1|]; split; [exact Eop|]; split; [exact E342|];
        split; [exact Ehns|]; split; [exact E343|]; split; [exact Ep2|]; lia|].
      split; [exact HKN|]. split; [exact HCUR|]. split; [exact Hfuel|]. split; [exact Hi|]. exact Hnow.
- (* r = 1: the DRIVE arm *)
  subst r st' g'.
  assert (Rq0 : 0 <= quiet) by (destruct Hh as [Hh0 | Hh1]; [destruct (KI0 Hd0 Hh0) as [-> _]; lia | rewrite <- (KI1 Hd0 Hh1); lia]).
  br_split HS Hc1.
  { exfalso. lazymatch type of Rres with ew _ ?na = _ => hc_bool Hc1 ltac:(fun H => hc_atom H na 1 Rres ltac:(lia)) end. hc_prop Hc1. lia. }
  pl_run_to HS HJ4 AG fpos F EFA4 0x7f1e0. clear_frames.
  br_split HS Hc4.
  { exfalso. lazymatch type of Rres with ew _ ?na = _ => hc_bool Hc4 ltac:(fun H => hc_atom H na 1 Rres ltac:(lia)) end. hc_prop Hc4. lia. }
  pl_run_to HS HJ4 AG fpos F EFA4 0x7f1e4. clear_frames.
  br_split HS Hc5.
  { exfalso. hc_bool Hc5 ltac:(fun H => hc_atom H 303%nat d Ed ltac:(lia)). hc_prop Hc5. lia. }
  pl_run_to HS HJ4 AG fpos F EFA4 0x7f1ec. clear_frames.
  br_split HS Hc6.
  { exfalso. hc_bool Hc6 ltac:(fun H => hc_atom H 343%nat 1 E343 ltac:(lia)). hc_prop Hc6. lia. }
  pl_run_to HS HJ4 AG fpos F EFA4 0x7f1fc. clear_frames.
  br_split HS Hc7.
  { exfalso. hc_bool Hc7 ltac:(fun H => lazymatch type of H with context [U ?E' (SAlu ALU_ADD (SOff 331 0) (SMd M_MUL (SOff 333 0) (SLit (-1))))] =>
      rewrite (U_sub_atoms E' 331 333 now quiet ltac:(ewpeel; exact Enow) ltac:(ewpeel; exact Equiet) ltac:(lia) ltac:(lia)) in H end).
    hc_prop Hc7. unfold L_NS in Hq1. lia. }
  pl_run_to HS HJ4 AG fpos F EFA4 0x7f21c. clear_frames.
  add_atom_win HS 340%nat (Z_to_bv 64 1) E340.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  add_fact HS 340%nat 0 1 E340 ltac:(lia).
  rreg HS (27%bv : bv 5) R27.
  ws_pin HS (27%bv : bv 5) (SOff 340 0) R27 ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E340; reflexivity).
  clear R27.
  drop_conds HS.
  havoc_deads HS 800%nat rt_loop_deads7_bv.
  ra_join_win HS ss_C 740%nat rt_loop_deads7_bv ltac:(idtac).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RC HS.
  split; [unfold EV_step; lia|]. split; [unfold ACC0 in *; lia|]. split; [exact (Permutation_trans HPerm4 HPerm3)|].
  exists rem, cur, i, 1, h, now, quiet, op, due', hns, 1, 1, p1, p2, c.
  split; [exact Erem|]. split; [exact Ecur|]. split; [exact Ei|]. split; [exact E340|]. split; [exact Eh|].
  split; [exact Enow|]. split; [exact Equiet|].
  split; [unfold inv_cells; split; [exact E341|]; split; [exact Ep1|]; split; [exact Eop|]; split; [exact E342|];
    split; [exact Ehns|]; split; [exact E343|]; split; [exact Ep2|]; lia|].
  split; [unfold inv_knock; split; [right; reflexivity|]; split; [exact Hh|]; split; [reflexivity|]; split; [reflexivity|];
    split; [intros Hx; discriminate Hx|]; split; [intros Hx; discriminate Hx|]; exact Hqn|].
  split; [exact HCUR|]. split; [exact Hfuel|]. split; [exact Hi|]. exact Hnow.
Qed.

End d.
End c.
