(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgMain4.v of this library: SEGMENT S4 TAIL of
   libreac/fuzz_knock's ASan harness walk of LLVMFuzzerTestOneInput in fuzz_knock.asan-ubsan (sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82), pc 0x7f1ec-0x7f218, from ss_T to ss_M
   (lib/AU/APgStates.v; invariants lib/AU/APgLoop0.v), with the optional call of reac_knock_heard at 0x7f210.
   The proof is lib/A/APgMain4.v's (donor model
   proofs/cgif/cgif_file_fuzzer/lib/A at c8557374ad2e: ACfe.v:228-285, ACfc.v:110-183, ACfe.v:181-208, :294-318,
   ACf9.v:364-388, ACf6.v:52-61), with the module paths of the lib/AU twins and the asan-ubsan pcs.  The twelve words
   of the segment are the asan words up to the call (internal path,
   section 2, row S4): only the pcs move (+0x58) and the callee entry is reac_knock_heard at 0x7f520 (RA 0x7f214).
   s8 / s10 / s11 (d / the countdown / 1 in this image) are not touched by the segment and pass through the join.

   THE CODE (asan-ubsan image)
     0x7f1ec or a1,a2,a1; slli a0,s7,57; srli a0,a0,61; sll a0,a1,a0; andi a1,s7,1; add s5,a0,s5
                                            now' = now + ((256 * hib | lo) << ((ev >> 4) & 7))
     0x7f204 beqz a1,0x7f21c                (no HEARD call when ev & 1 = 0)
     0x7f208 mv a0,s4; mv a1,s5; jal reac_knock_heard (0x7f520)
     0x7f214 li s2,1; sd s5,48(s1)          h := 1, quiet := now'
     0x7f21c (ss_M)

   Section hypotheses: MTL, TL, LAWS, ML (as every segment) and HEARD : tknock_heard_specX (SK := SK) tfibsegs B MT
   A_reac_knock_heard (a Theorem Labs lane's contract lib/A/APgCSpec.v at segs := tfibsegs of lib/AU/AWalkFw0.v and the
   asan-ubsan entry 0x7f520).  rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import APgStates APgLoop0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Set Hyps Limit 8. Set Printing Depth 14. Set Printing Width 250.

(* the three values the body computes at 0x7f1ec-0x7f200, as the engine leaves them in a0 / s5 *)
Definition S4_dt : sv := SAlu ALU_OR (SOff 322 0) (SOff 321 0).
Definition S4_sh : sv := SAlu ALU_SRL (SAlu ALU_SLL (SOff 320 0) (SLit 57)) (SLit 61).
Definition S4_now : sv := SAlu ALU_ADD (SAlu ALU_SLL S4_dt S4_sh) (SOff 305 0).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* `now += (256 * hib | lo) << ((ev >> 4) & 7)`: the shift is below 8, so the delay is below 2 ^ 23 (dt_boundZ),
   which is lib/Prog/LLVMFuzzerTestOneInput.v:284-292 of the plain proof *)
Lemma S4_now_den : forall E lo hib now,
ew E 321 = Z_to_bv 64 lo -> ew E 322 = Z_to_bv 64 (256 * hib) -> ew E 305 = Z_to_bv 64 now ->
0 <= lo < 256 -> 0 <= hib < 256 -> 0 <= now -> now + 2 ^ 23 <= 2 ^ 64 ->
exists shl, 0 <= shl < 2 ^ 23 /\ sv_denot E S4_now = Z_to_bv 64 (now + shl).
Proof.
intros E lo hib now Elo Ehi Enow Rlo Rhib Rn0 Rn1.
assert (Hsh : 0 <= U E S4_sh < 8).
{ unfold S4_sh. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 61) 63) with 61.
  pose proof (U_range E (SAlu ALU_SLL (SOff 320 0) (SLit 57))) as R. unfold M64 in R.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hd : 0 <= U E (SAlu ALU_SLL (SOff 320 0) (SLit 57)) / 2 ^ 61 < 8)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite zcanon_id by (unfold M64; lia). exact Hd. }
exists (Z.shiftl (256 * hib + lo) (U E S4_sh)).
pose proof (dt_boundZ (256 * hib + lo) (U E S4_sh) ltac:(lia) Hsh) as Hb.
split; [exact Hb|].
rewrite denot_lit_U. f_equal. unfold S4_now.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 305 now Enow) by lia.
rewrite U_SAlu. cbn [zalu_raw].
assert (Hdt : U E S4_dt = 256 * hib + lo).
{ unfold S4_dt. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 322 (256 * hib) Ehi) by lia. rewrite (U_atom E 321 lo Elo) by lia.
  rewrite Z.mul_comm, lor_byte_pair by lia. apply zcanon_id. unfold M64. lia. }
rewrite Hdt.
replace (Z.land (U E S4_sh) 63) with (U E S4_sh) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
rewrite (zcanon_id (Z.shiftl (256 * hib + lo) (U E S4_sh))) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* [DONOR A/ACf6.v:52-61] *)
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
(* the fact the state already carries for an atom  [as lib/Reusable/YL09.v:51-55 atoms_ok_In, which this module does
   not import] *)
Lemma rt_atoms_ok_In : forall E l n f, atoms_ok E l -> In (n, f) l -> afact_ok E n f.
Proof.
induction l as [|[n' f'] l IH]; cbn; intros n f H Hin; [destruct Hin|].
destruct H as [H1 H2]. destruct Hin as [Heq|Hin]; [injection Heq as -> ->; exact H1 | apply IH; assumption].
Qed.
End a.

(* point register r at the fresh atom n (whose value is pinned by Hn), dtac proving the old expression has that value *)
Ltac pin_den HS r n Hn dtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev ssx msv r (SOff n 0) HS ltac:(intros X; discriminate X)
  ltac:(rewrite (st_ok_reg tfibsegs Ev ssx msv r HS); rewrite sv_denot_SOff0, Hn;
        lazymatch goal with |- _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' end;
        symmetry; dtac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* give the fresh atom n the fact f that the state carries for atom m, vtac proving ew E m = ew E n.  INV_T bounds
   `quiet` only through its atom's fact (no Z lower bound when d = 1), so N_quietM takes N_quiet's fact this way. *)
Ltac add_fact_of HS n f m vtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in let Hf := fresh "Hf" in let Hm := fresh "Hm" in
assert (Hf : afact_ok Ev n f) by
  (pose proof (rt_atoms_ok_In Ev _ m f (proj1 (st_ok_facts_ok tfibsegs Ev ssx msx HS))
     ltac:(vm_compute; repeat (first [left; reflexivity | right]))) as Hm;
   unfold afact_ok in Hm |- *; replace (ew Ev n) with (ew Ev m) by vtac; exact Hm);
pose proof (st_ok_add_fact tfibsegs Ev ssx msx n f HS Hf) as HS3; clear HS Hf; rename HS3 into HS end.
(* [DONOR A/ACf9.v:364-388 reseatL, as lib/A/AWalkFw2.v:190-214 carries it], with the junk-atom floor K a parameter
   instead of the state's atom bound: the call's clobbered registers get atoms K.., which must stay clear of the
   ss_M havoc window 720..735 that the join writes.  The re-based facts' side conditions are closed numerals, so
   nat_side closes them (as rebaseE, lib/AU/AWalkFw1.v:56); AG2's need only Hnn.  A whole-context lia there took
   about 8 minutes of rt_S4. *)
Ltac reseatK HS K HJ2 HP2 keep AG kept_tac :=
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by (clear - Hnn; lia); rewrite ?ew_ewset_other by (clear - Hnn; lia); rewrite ?ew_havoc_old by (clear - Hnn; lia); rewrite ?ew_ewset_other by (clear - Hnn; lia); apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other by nat_side; rewrite ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG end end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HEARD : tknock_heard_specX (SK := SK) tfibsegs B MT A_reac_knock_heard.

Lemma rt_S4 : forall fuel : nat,
rt_from B MT FP POST ss_M (INV_M B MT fuel) ->
rt_from B MT FP POST ss_T (INV_T B MT fuel).
Proof.
intros fuel RM. rt_prelude.
pose proof HINV as (Hk & Hacc & HPerm3 & rem & cur & i & d & h & now & quiet & op & due & hns & st & g &
p1 & p2 & c & ev & lo & hib & Erem & Ecur & Ei & Ed & Eh & Enow & Equiet & Eev & Elo & Ehi & Rev & Rlo & Rhib &
HCELL & HKN & HCUR & Hfuel & Hi & Hnow).
cbn [c_ly c_S c_p c_n] in HPerm3, HCUR.
destruct HCELL as (Est & Ep1 & Eop & Edue & Ehns & Eg & Ep2 & Rp1 & Rp2 & Rop & Rdue & Rhns).
destruct HKN as (Hd & Hh & Hst & Hg & KI0 & KI1 & Hqn).
destruct HCUR as (Hcur & Hc0 & Hcn & Hrem0 & Hcur4096 & HcurHi).
assert (HF8m : F mod 8 = 0) by (rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult).
assert (HFk8 : (F + 32) mod 8 = 0) by (rewrite <- Zplus_mod_idemp_l, HF8m; reflexivity).
assert (Rst : 0 <= st <= 2) by (rewrite Hst; unfold st_ofZ; destruct (Z.eqb d 1), (Z.eqb h 1); lia).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
pl_run_to HS HJ3 AG fpos F EFA3 0x7f204. clear_frames.
(* now' = now + dt << sh, into the fresh atom N_nowM, pinned in s5 on both paths *)
lazymatch type of HS with st_ok _ ?Ex _ _ =>
destruct (S4_now_den Ex lo hib now ltac:(ewpeel; exact Elo) ltac:(ewpeel; exact Ehi) ltac:(ewpeel; exact Enow) Rlo Rhib ltac:(lia) ltac:(lia))
as (shl & Hshl & Hden) end.
add_atom_win HS 331%nat (Z_to_bv 64 (now + shl)) E331.
pin_den HS (21%bv : bv 5) 331%nat E331 ltac:(rewrite denot_havoc_win by (vm_compute; reflexivity); exact Hden).
add_fact HS 331%nat 0 9223406396593514176 E331 ltac:(lia).
br_split HS Hc.
{ (* ev & 1 = 0: beqz a1 is taken, no call *)
  pl_run_to HS HJ3 AG fpos F EFA3 0x7f21c. clear_frames.
  add_atom_win HS 332%nat (Z_to_bv 64 h) E332.
  pin_den HS (18%bv : bv 5) 332%nat E332 ltac:(rewrite sv_denot_SOff0; ewpeel; exact Eh).
  add_fact HS 332%nat 0 1 E332 ltac:(lia).
  add_atom_win HS 333%nat (Z_to_bv 64 quiet) E333.
  rechunk_at HS 70%nat 48 (SOff 333 0) ltac:(rewrite !sv_denot_SOff0, E333; ewpeel; symmetry; exact Equiet).
  add_fact_of HS 333%nat (mkAF 0 9223406396593514176 0) 306%nat ltac:(rewrite E333; ewpeel; exact Equiet).
  add_atom_win HS 334%nat (Z_to_bv 64 st) E334.
  rechunk_at HS 75%nat 32 (SOff 334 0) ltac:(rewrite !sv_denot_SOff0, E334; ewpeel; symmetry; exact Est).
  add_fact HS 334%nat 0 2 E334 ltac:(lia).
  add_atom_win HS 335%nat (Z_to_bv 64 hns) E335.
  rechunk_at HS 75%nat 56 (SOff 335 0) ltac:(rewrite !sv_denot_SOff0, E335; ewpeel; symmetry; exact Ehns).
  add_fact HS 335%nat 0 9223406396593514176 E335 ltac:(lia).
  ra_join_win HS ss_M 720%nat rt_loop_deads_bv ltac:(idtac).
  rebaseE HS AG HEv. clear HEv. relowRT HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RM HS.
  split; [lia|]. split; [lia|]. split; [exact HPerm3|].
  exists rem, cur, i, d, h, (now + shl), quiet, op, due, hns, st, g, p1, p2, c, ev.
  unfold inv_cells, inv_knock, inv_cursor.
  repeat split; first [eassumption | lia]. }
(* ev & 1 <> 0: the call to reac_knock_heard *)
pl_run_to HS HJ3 AG fpos F EFA3 0x7f520. clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok _ ?e _ (restrict _ ?m) => rename e into EC; rename m into msC end.
try clear HUP.
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem msC) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _); apply F1; clear - Ha Hceil Hslo Hstk0 FFS C1; lia).
try clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (8%bv : bv 5) Rs0. rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1.
assert (Usp3 : bv_unsigned (ew EC 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (UF : bv_unsigned (ew EC 75) = F) by (rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia).
assert (U70 : bv_unsigned (ew EC 70) = sp1) by (rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
assert (EspX : spZ (ms_regs msC) = sp1) by (unfold spZ; rewrite Rsp; exact U70).
assert (EraX : raZ (ms_regs msC) = 0x7f214) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia).
assert (Es0X : s0Z (ms_regs msC) = spZ regs) by (unfold s0Z; rewrite Rs0; exact Usp3).
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
(* the caller's saved ra / s0 at sp0-8 / sp0-16, for the call chain  [DONOR A/ACfc.v:110-127] *)
lazymatch type of HS with st_ok _ _ ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth EC ssx (restrict (w_H W3) msC) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region EC _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region EC _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end end.
clear HRstk.
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) (ms_mem msC)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T))).
{ unfold rt_ch; cbn [c_regs c_ly]. apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|].
  exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
  ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia)). }
(* the five zero shadow bytes over k, for afobj  [DONOR A/ACfc.v:128-155, A/ACfe.v:199-208] *)
lazymatch type of HS with st_ok _ _ ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let iS := idx_of_base rs 88%nat in let iS := eval vm_compute in iS in
let rS := eval vm_compute in (nth iS rs got_region) in
pose proof (st_ok_region_nth EC ssx (restrict (w_H W3) msC) iS rS HS ltac:(vm_compute; reflexivity)) as HRS; cbn [ms_mem restrict] in HRS;
assert (US : bv_unsigned (ew EC 88) = SB + F / 8) by (rewrite E88; apply unsigned_lit_small; unfold SB; clear - HF8lo HF8hi; lia);
assert (ZS : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) (YP09.r_chunks rS) -> aview tfibsegs (w_H W3) (ms_mem msC) (SB + F / 8 + od) = Some 0);
[ let od := fresh "od" in let Hod := fresh "Hod" in intros od Hod;
lazymatch type of HRS with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region EC _ 88 (SB + F / 8) cs lo hi wlo whi od 1%N (SLit 0) 0 HRS US Hod eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Vz end;
pose proof (Vz 0%nat ltac:(lia)) as Vz0; cbn [Z.of_nat] in Vz0; rewrite Z.add_0_r in Vz0;
unfold aview; rewrite Vz0; reflexivity
| clear HRS ] end.
assert (EF32 : (F + 32) / 8 = F / 8 + 4) by (rewrite HF8; replace (F + 32) with ((4 * (F / 32) + 4) * 8) by lia; rewrite Z_div_mult by lia; lia).
assert (AF : afobj tfibsegs B ly3 S3 W3 (ms_mem msC) (F + 32) 40).
{ split; [|split].
  - exists 1, fpos. split; [exact Hfin3|]. split; [lia|]. rewrite EFA3. fold F. split; [exact HF8m|].
    change (fs_frame_bytes 1) with 128. lia.
  - exact HFk8.
  - apply zero_shadow_of_bytes; [exact HFk8 | reflexivity | lia |].
    intros j Hj. change (40 / 8) with 5 in Hj. rewrite <- SB_SHADOW_OFF, EF32.
    replace (SB + (F / 8 + 4) + j) with (SB + F / 8 + (4 + j)) by lia.
    assert (Hj5 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia.
    destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]]; apply ZS; cbn; tauto. }
clear ZS.
(* k's seven fields, from the k region, for obj_at *)
lazymatch type of HS with st_ok _ _ ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let ik := idx_of_base_off rs 75%nat 32 in let ik := eval vm_compute in ik in
let rk := eval vm_compute in (nth ik rs got_region) in
pose proof (st_ok_region_nth EC ssx (restrict (w_H W3) msC) ik rk HS ltac:(vm_compute; reflexivity)) as HRK; cbn [ms_mem restrict] in HRK end.
lazymatch type of HRK with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region EC _ 75 F cs lo hi wlo whi 32 4%N (SOff 310 0) st HRK UF ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact Est) ltac:(cbn; lia) ltac:(cbn; lia)) as V1;
pose proof (field_of_region EC _ 75 F cs lo hi wlo whi 36 4%N (SOff 312 0) p1 HRK UF ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact Ep1) ltac:(cbn; lia) ltac:(cbn; lia)) as V2;
pose proof (field_of_region EC _ 75 F cs lo hi wlo whi 40 8%N (SOff 307 0) op HRK UF ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact Eop) ltac:(cbn; lia) ltac:(cbn; lia)) as V3;
pose proof (field_of_region EC _ 75 F cs lo hi wlo whi 48 8%N (SOff 308 0) due HRK UF ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact Edue) ltac:(cbn; lia) ltac:(cbn; lia)) as V4;
pose proof (field_of_region EC _ 75 F cs lo hi wlo whi 56 8%N (SOff 309 0) hns HRK UF ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact Ehns) ltac:(cbn; lia) ltac:(cbn; lia)) as V5;
pose proof (field_of_region EC _ 75 F cs lo hi wlo whi 64 4%N (SOff 311 0) g HRK UF ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact Eg) ltac:(cbn; lia) ltac:(cbn; lia)) as V6;
pose proof (field_of_region EC _ 75 F cs lo hi wlo whi 68 4%N (SOff 313 0) p2 HRK UF ltac:(cbn; tauto) ltac:(rewrite sv_denot_SOff0; exact Ep2) ltac:(cbn; lia) ltac:(cbn; lia)) as V7 end.
clear HRK.
assert (OKk : obj_at tfibsegs (mrestrict (w_H W3) (ms_mem msC)) (F + 32) LAY_Knock [st; p1; op; due; hns; g; p2]).
{ cbn [obj_at LAY_Knock]. unfold field_ok. cbn [fst snd].
  rewrite <- !Z.add_assoc. cbn [Z.add Pos.add].
  split; [split; [exact V1 | cbn; lia]|]. split; [split; [exact V2 | cbn; lia]|].
  split; [split; [exact V3 | cbn; lia]|]. split; [split; [exact V4 | cbn; lia]|].
  split; [split; [exact V5 | cbn; lia]|]. split; [split; [exact V6 | cbn; lia]|].
  split; [split; [exact V7 | cbn; lia]|]. exact I. }
clear V1 V2 V3 V4 V5 V6 V7.
(* the call  [DONOR A/ACfe.v:228-285] *)
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
change (Z_to_bv 64 521504) with (w64 A_reac_knock_heard);
eapply SRr_bind;
[ eapply (HEARD LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
    (F + 32) (now + shl) 1 fpos (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) st p1 op due hns g p2 HJ3);
  [ rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
  | rewrite EraX; clear; lia
  | rewrite Rgp, (AG 3%nat) by lia; rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
  | rewrite Rtp, (AG 4%nat) by lia; rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
  | rewrite Ra0, UF; reflexivity
  | rewrite Ra1; exact E331
  | lia
  | rewrite EspX, Es0X; exact Hch1
  | rewrite EspX; exact Hsp1al16
  | rewrite EspX; unfold T_heard_STK; rewrite FFS; clear - Hsp1; lia
  | rewrite EspX; clear - Hsp1; lia
  | left; reflexivity
  | clear; lia
  | rewrite EFA3; fold F; exact HF8m
  | rewrite EFA3; fold F; clear; lia
  | rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
  | exact HFk8
  | clear - HF4096; lia
  | right; rewrite EspX; unfold T_heard_STK; clear - HFceil Hceil Hslo Hstk0 Hsp1 FFS C1; lia
  | exact AF
  | exact OKk
  | unfold EV_heard; rewrite HEV in Hev, Hk; clear - Hev Hk; lia ]
| ] end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & HPerm4 & HIO4 & HMLE4 & K1 & K2 & K3 & K4 & OK4).
rewrite EspX in K1. unfold T_heard_STK in K1. rewrite Rra.
pose proof (mle_station MT S S3 S4 acc 0 MTL HMLE HMLE4) as HMLE4c.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(1, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & _).
change (fs_frame_bytes 1) with 128 in HFpres4. rewrite !EFA4 in HFpres4. fold F in HFpres4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
clear Hch1 AF OKk Vra Vs0.
reseatK HS 800%nat HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
  eapply rt_region_kept_eq; [ evalE AG
  | intros a Ha; apply (K3 1 fpos a Hfin3);
    [ right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; clear - Ha; unfold SB in *; lia
    | clear - Ha HF8c HF8lo HFhigh HFq HF8 C1 C2 C3 C4 C5; unfold SB in *; zone_lia ]
  | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
  eapply rt_region_kept_eq; [ evalE AG
  | intros a Ha; apply (K3 1 fpos a Hfin3);
    [ left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear - Ha; lia
    | clear - Ha; lia ]
  | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 70%nat) _ _ _ _ _) =>
  eapply rt_region_kept_eq; [ evalE AG
  | intros a Ha; apply K1;
    [ clear - Ha Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; lia | clear - Ha; lia | clear - Ha HFceil Hsp1 Hceil Hslo Hstk0 FFS C1; lia ]
  | intros a Ha; apply Hpres4; clear - Ha Hsp1 FFS; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
  eapply rt_region_kept_eq; [ evalE AG
  | intros a Ha; apply K1;
    [ clear - Ha Hceil Hslo Hstk0 Hshi H47 FFS C1; lia | clear - Ha Hsp1; lia | clear - Ha HFceil Hceil Hslo Hstk0 FFS C1; lia ]
  | intros a Ha; apply Hpres4; clear - Ha FFS; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
  first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
  | change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
  | change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
  | change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* k after the call (kn_post_heard's obj_at): the state is `st = 0 ? 2 : st`, heard is now', the other five fields
   are unchanged.  k is re-seated as a fresh region over the two new atoms N_stM / N_hnsM. *)
cbn [obj_at LAY_Knock] in OK4. unfold field_ok in OK4. cbn [fst snd] in OK4.
destruct OK4 as ((V1 & _) & (V2 & _) & (V3 & _) & (V4 & _) & (V5 & _) & (V6 & _) & (V7 & _) & _).
set (st' := if st =? 0 then 2 else st) in V1.
assert (Rst' : 0 <= st' <= 2) by (subst st'; destruct (Z.eqb_spec st 0); lia).
assert (Hst' : st' = st_ofZ d 1) by (subst st'; rewrite Hst; unfold st_ofZ; destruct Hd as [-> | ->]; destruct Hh as [-> | ->]; reflexivity).
clearbody st'.
rewrite <- !Z.add_assoc in V1, V2, V3, V4, V5, V6, V7. cbn [Z.add Pos.add] in V1, V2, V3, V4, V5, V6, V7.
add_atom_win HS 334%nat (Z_to_bv 64 st') E334.
add_fact HS 334%nat 0 2 E334 ltac:(lia).
add_atom_win HS 335%nat (Z_to_bv 64 (now + shl)) E335.
add_fact HS 335%nat 0 9223406396593514176 E335 ltac:(lia).
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv (rl_k N_stM N_p1 N_op N_due N_hnsM N_g N_p2) HS eq_refl) as HS3;
specialize (HS3 ltac:(
  unfold region_ok, rl_k; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  replace (bv_unsigned (ew Ev 75)) with F by (symmetry; ewpeel; rewrite RF; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia);
  split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|];
  split; [intros oo Hoo; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + oo) ltac:(clear - Hoo; lia)))|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 32 4%N (SOff 334 0) st'); [rewrite sv_denot_SOff0; ewpeel; exact E334 | cbn; lia | cbn; lia | exact V1] |];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 36 4%N (SOff 312 0) p1); [rewrite sv_denot_SOff0; ewpeel; exact Ep1 | cbn; lia | cbn; lia | exact V2] |];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 40 8%N (SOff 307 0) op); [rewrite sv_denot_SOff0; ewpeel; exact Eop | cbn; lia | cbn; lia | exact V3] |];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 48 8%N (SOff 308 0) due); [rewrite sv_denot_SOff0; ewpeel; exact Edue | cbn; lia | cbn; lia | exact V4] |];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 56 8%N (SOff 335 0) (now + shl)); [rewrite sv_denot_SOff0; ewpeel; exact E335 | cbn; lia | cbn; lia | exact V5] |];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 64 4%N (SOff 311 0) g); [rewrite sv_denot_SOff0; ewpeel; exact Eg | cbn; lia | cbn; lia | exact V6] |];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs _ _ _ 68 4%N (SOff 313 0) p2); [rewrite sv_denot_SOff0; ewpeel; exact Ep2 | cbn; lia | cbn; lia | exact V7] |];
  apply Forall_nil));
specialize (HS3 ltac:(
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let ry2 := eval vm_compute in ry in let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry2 rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
  repeat split; clear - HF4096 HFceil HFhigh HFhigh_img HF8c HF8lo HF8hi HFq HF8 Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1; zone_lia));
clear HS; rename HS3 into HS; norm_ss HS end.
clear V1 V2 V3 V4 V5 V6 V7.
(* 0x7f214 li s2,1 ; 0x7f218 sd s5,48(s1) *)
pl_run_to HS HJ4 AG fpos F EFA4 0x7f21c. clear_frames.
add_atom_win HS 332%nat (Z_to_bv 64 1) E332.
pin_den HS (18%bv : bv 5) 332%nat E332 ltac:(first [reflexivity | rewrite denot_lit_U, U_lit by lia; reflexivity]).
add_fact HS 332%nat 0 1 E332 ltac:(lia).
add_atom_win HS 333%nat (Z_to_bv 64 (now + shl)) E333.
rechunk_at HS 70%nat 48 (SOff 333 0) ltac:(rewrite !sv_denot_SOff0, E333; ewpeel; symmetry; exact E331).
add_fact HS 333%nat 0 9223406396593514176 E333 ltac:(lia).
ra_join_win HS ss_M 720%nat rt_loop_deads_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. relowRT HS AG E10 E11 E32 E10n E11n E32n.
rt_hand RM HS.
split; [unfold EV_heard; lia|]. split; [lia|]. split; [exact (Permutation_trans HPerm4 HPerm3)|].
exists rem, cur, i, d, 1, (now + shl), (now + shl), op, due, (now + shl), st', g, p1, p2, c, ev.
unfold inv_cells, inv_knock, inv_cursor.
repeat split; first [eassumption | lia].
Qed.

End d.
End c.
