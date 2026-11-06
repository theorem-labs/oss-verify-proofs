(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc's ASan harness walk (LLVMFuzzerTestOneInput 0x7e68c,
   fuzz_qdisc.asan sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgMain4.v at origin/ossv/recipes 6ebe35ba632 (the call through a callee contract with
   SRr_bind, the destructuring of its post, reseatK as reseatQ, rt_region_kept_eq and the kept-region cases), with the
   back edge and exit of knock's lib/A/APgMain6.v at the same revision (the atoms moved to the loop head's slots, the facts
   on the reused slot dropped with st_ok_facts_incl3, ra_join_win to ss_L / ss_X, rt_hand), its module paths changed and
   knock's fake-frame parts removed: qdisc's harness owns no frame and hands its callees no object, so there is no call
   chain, no afobj / obj_at and no object region to rebuild (h-small-a3).
   rule 24 (reuse): no function is proved here; this is SEGMENT S3, the two calls and the back edge of
   LLVMFuzzerTestOneInput's walk, from ss_C (pc 0x7e7c4) to ss_L (0x7e710) or ss_X (0x7e81c), all lib/A/QPgLoop0.v.

   THE CODE (capstone 5.0.7 over the pinned image)
     0x7e7c4  mv a0,s1 / mv a1,s2 / jal 0x7e94c   reac_qdisc_etf_catchup_slots(lead, fps), ra = 0x7e7d0
     0x7e7d0  mv a1,s1 / mv a2,s2 / jal 0x7e870   check_slots(got, lead, fps), ra = 0x7e7dc
     0x7e7dc  addiw s4,s4,-1                       the engine folds it to s4 = SOff N_bud (-1)
     0x7e7e0  bnez s4 -> 0x7e710                   the back edge
     0x7e7e4  j 0x7e81c                            the exit block

   THE CALLEE PREMISES, and where each comes from (QPgCSpec.qdisc_slots_specX / qdisc_check_specX):
   - the journal: catchup takes rt_from's journal as the runs carry it (STK = LLVMF_STK, sp0 = the entry sp, own = []);
     check_slots takes catchup's post journal at k + EV_slots.
   - YK0s.ret_ok and 4096 <= raZ: ra is the literal return site 0x7e7d0 / 0x7e7dc (even: ret_ok_even).
   - gp = w64 (as_gp B), tp = w64 (as_tp B): x3 / x4 are the entry's (rt_E, rt_base's register agreement) and afn_pre's
     Hgp / Htp (rt_prelude).
   - catchup's a0 = w64 lead and a1 = w64 fps: `mv a0,s1` / `mv a1,s2` copy the atoms N_lead / N_fps, INV_C's
     ew E N_lead / ew E N_fps; 0 <= lead <= 65535 from INV_C, -2^31 <= fps < 2^31 from QPgLoop0.qd_fps_range.
   - check_slots' a0 = w64 (slots_spec lead fps): catchup's post pins regs2's a0 to it; the re-seat puts a0 at the junk
     atom 804 (= 800 + the index of x10 in CLOB, ew_havoc_new). a1 = w64 lead and a2 = w64 fps as above.
   - sp mod 16 = 0: sp = sp0 - 96 (the prologue's `addi sp,sp,-0x60`) and astk_ok's sp0 mod 16 = 0 (Hal16).
   - the stack window: sp0 - LLVMF_STK <= sp - T_slots_STK (0) and <= sp - T_check_STK (16), LLVMF_STK = 32768; sp <= sp0.
   - the divisor cell: val_mem A_QD_MAGIC 8 QD_MAGIC is PROVED here (qd_magic_rom), not assumed: rt_base's arodata_ok,
     carried to the current memory by arodata_ok_journal, TfibLib's tl_lib_consts at lib_const_addr's first range
     [0x10350, 0x10358), and the eight image bytes db 34 b6 d7 82 de 1b 43 (QPgMain2.qd_val_rom, vm_compute).
   - the event budget: rt_base's st_nev S + EV_LIB <= EV_MAX with EV_LIB = 0, INV_C's k <= EV_LIB, EV_slots = EV_check = 0.

   THE RE-SEAT after each call keeps ss_C's three regions: the 96-byte save area (region 2, [sp0-96, sp0)) by the post's
   memory clause (catchup: every address unchanged; check_slots: unchanged outside [sp0-112, sp0-96)) and the post
   journal's present-stack clause; the .got slot of the shadow base and the shadow cell by region_kept_val over al_const
   before and after (aconstsF). The clobbered caller-saved registers get junk atoms 800.. / 820.., clear of ss_L's havoc
   window 760..777 and ss_X's 600..625.

   THE BRANCHES, and the fact that decides each:
   - 0x7e7e0 `bnez s4` taken (bud - 1 <> 0, the branch condition through hc_off over INV_C's ew E N_bud): the back edge
     to 0x7e710. s0 / s9 / s4 are moved to the loop head's atoms N_cur / N_rem / N_bud with cur, rem and bud - 1 (N_bud
     through the scratch atom 308, its old fact and the branch condition dropped first), and INV_L holds with
     bud' = bud - 1: 1 <= bud' from the branch condition and INV_C's 1 <= bud, Z.to_nat bud' <= fuel from
     Z.to_nat bud <= S fuel.
   - not taken (bud - 1 = 0): `j 0x7e81c`, the exit ss_X; INV_X from k + 0 + 0 <= EV_LIB, acc + 0 + 0 <= ACC0 <= c_T
     (rt_base) and the Permutation chain of the two posts and INV_C.

   Section hypotheses: MTL : ameter_laws MT (mle_station over the two posts' meters), TL : TfibLib B, LAWS : AR_laws
   tfibsegs B, SLOTS : qdisc_slots_specX tfibsegs B MT A_QD_SLOTS A_QD_MAGIC and CHECK : qdisc_check_specX tfibsegs B MT
   A_QD_CHECK A_QD_MAGIC (the two callee contracts, lib/A/QPgCSpec.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw1 AWalkFw2 ACfm QPgRt QPgBase QPgCSpec QPgLoop0 QPgMain2.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Prog Require Import qdisc_spec.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* [knock A/APgMain4.v:84-94, the donor's A/ACf6.v:52-61] *)
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
End a.

(* [knock A/APgMain4.v:149-178 reseatK], with the junk-atom floor K a parameter and the equation of the re-seated
   environment kept as HEv: check_slots' a0 is catchup's result, which only that equation names. *)
Ltac reseatQ HS K HJ2 HP2 keep AG kept_tac HEv :=
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by (clear - Hnn; lia); rewrite ?ew_ewset_other by (clear - Hnn; lia); apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis SLOTS : qdisc_slots_specX tfibsegs B MT A_QD_SLOTS A_QD_MAGIC.
Hypothesis CHECK : qdisc_check_specX tfibsegs B MT A_QD_CHECK A_QD_MAGIC.
(* the divisor cell both callees load (0x10350, 8 bytes 0x431BDE82D7B634DB), from arodata_ok and the image *)
Lemma qd_magic_rom : forall (W : world tfibsegs) (m : word -> option byte),
  arodata_ok B (aview tfibsegs (w_H W) m) -> val_mem tfibsegs (mrestrict (w_H W) m) A_QD_MAGIC 8 QD_MAGIC.
Proof.
intros W m HR. apply (qd_val_rom B _ _ _ _ _ TL HR); [intros kk Hkk; unfold lib_const_addr, A_QD_MAGIC; lia | vm_compute; reflexivity].
Qed.
Lemma rt_S3 : forall fuel : nat,
  rt_from B MT FP POST ss_L (INV_L B MT fuel) ->
  rt_from B MT FP POST ss_X (INV_X B MT) ->
  rt_from B MT FP POST ss_C (INV_C B MT (S fuel)).
Proof.
intros fuel RL RX. rt_prelude.
pose proof HINV as (Hk & Hacc & HPerm3 & Hin0 & Hrq & cur & rem & bud & c & lead & sel & Ecur & Erem & Ebud & Elead & Efps &
HCUR & Hbud & Hfuel & Hlead & Hsel).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* 0x7e7c4 .. 0x7e7cc: to catchup's entry *)
pl_run_to HS HJ3 AG 0x7e94c. clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok _ ?e _ (restrict _ ?m) => rename e into EC; rename m into msC end.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1.
assert (Usp3 : bv_unsigned (ew EC 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (EspX : spZ (ms_regs msC) = spZ regs - 96)
by (unfold spZ at 1; rewrite Rsp, Usp3; apply unsigned_lit_small; clear - Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
try clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
pose proof (arodata_ok_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROD) as HROD3.
(* the call of reac_qdisc_etf_catchup_slots  [knock A/APgMain4.v:316-345] *)
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
change (Z_to_bv 64 518476) with (w64 A_QD_SLOTS);
eapply SRr_bind;
[ eapply (SLOTS LLVMF_STK (spZ regs) FP ly S W mem md [] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX) lead (qd_fps sel) HJ3);
  [ rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
  | unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia
  | rewrite Rgp, (AG 3%nat) by lia; rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
  | rewrite Rtp, (AG 4%nat) by lia; rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
  | rewrite Ra0; exact Elead
  | lia
  | rewrite Ra1; exact Efps
  | apply qd_fps_range
  | rewrite EspX, Zminus_mod, Hal16; reflexivity
  | rewrite EspX; unfold T_slots_STK; rewrite FFS; lia
  | rewrite EspX; lia
  | exact (qd_magic_rom W3 (ms_mem msX) HROD3)
  | unfold EV_slots; rewrite HEV in Hev, Hk; clear - Hev Hk; lia ]
| ] end.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & HPerm4 & HIO4 & HMLE4 & Hmem4 & Ha04).
rewrite Rra.
pose proof (mle_station MT S S3 S4 acc 0 MTL HMLE HMLE4) as HMLE4c.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
reseatQ HS 800%nat HJ4 HP4 [0; 1; 2]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
  eapply rt_region_kept_eq; [ evalE AG
  | intros a Ha; apply Hmem4; [clear - Ha Hceil Hslo Hstk0 Hshi H47 FFS C1; lia | unfold T_slots_STK; clear; lia]
  | intros a Ha; apply Hpres4; clear - Ha FFS; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
  first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
  | change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia] ] end ]) HE4.
(* catchup's result, in the junk atom of a0 *)
assert (E804 : ew E1 804 = Z_to_bv 64 (slots_spec lead (qd_fps sel))).
{ rewrite HE4. change 804%nat with (800 + 4)%nat. rewrite (ew_havoc_new EC 800 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
  cbn [nth map CLOB]. exact Ha04. }
clear HE4 Ha04 Rra Rsp Rgp Rtp Ra0 Ra1 Usp3 EspX Hmem4 Hpres4 Kgot3 Kcell3 Kguar3 Kuar3 HROD3.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* 0x7e7d0 .. 0x7e7d8: to check_slots' entry *)
pl_run_to HS HJ4 AG 0x7e870. clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok _ ?e _ (restrict _ ?m) => rename e into ED; rename m into msD end.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2.
assert (Usp3 : bv_unsigned (ew ED 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (EspX : spZ (ms_regs msD) = spZ regs - 96)
by (unfold spZ at 1; rewrite Rsp, Usp3; apply unsigned_lit_small; clear - Hceil Hslo Hstk0 Hshi H47 FFS C1; lia).
try clear Kgot4 Kcell4 Kguar4 Kuar4. aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
pose proof (arodata_ok_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 HROD) as HROD4.
(* the call of check_slots *)
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
change (Z_to_bv 64 518256) with (w64 A_QD_CHECK);
eapply SRr_bind;
[ eapply (CHECK LLVMF_STK (spZ regs) FP ly S W mem md [] ly4 S4 W4 (ms_mem msX) mdX (k + EV_slots) (ms_regs msX) lead (qd_fps sel) HJ4);
  [ rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
  | unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia
  | rewrite Rgp, (AG 3%nat) by lia; rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
  | rewrite Rtp, (AG 4%nat) by lia; rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
  | rewrite Ra0; exact E804
  | rewrite Ra1; exact Elead
  | lia
  | rewrite Ra2; exact Efps
  | apply qd_fps_range
  | rewrite EspX, Zminus_mod, Hal16; reflexivity
  | rewrite EspX; unfold T_check_STK; rewrite FFS; lia
  | rewrite EspX; lia
  | exact (qd_magic_rom W4 (ms_mem msX) HROD4)
  | unfold EV_slots, EV_check; rewrite HEV in Hev, Hk; clear - Hev Hk; lia ]
| ] end.
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hfrs5 & HPerm5 & HIO5 & HMLE5 & Hmem5).
rewrite Rra. rewrite EspX in Hmem5. unfold T_check_STK in Hmem5.
pose proof (mle_station MT S S4 S5 (acc + 0) 0 MTL HMLE4c HMLE5) as HMLE5c.
pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
reseatQ HS 820%nat HJ5 HP5 [0; 1; 2]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
  eapply rt_region_kept_eq; [ evalE AG
  | intros a Ha; apply Hmem5; [clear - Ha Hceil Hslo Hstk0 Hshi H47 FFS C1; lia | clear - Ha; lia]
  | intros a Ha; apply Hpres5; clear - Ha FFS; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
  first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot4 | exact Kgot5 | clear; lia]
  | change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell4 | exact Kcell5 | clear; lia] ] end ]) HE5.
clear HE5 E804 Rra Rsp Rgp Rtp Ra0 Ra1 Ra2 Usp3 EspX Hmem5 Hpres5 Kgot4 Kcell4 Kguar4 Kuar4 HROD4.
assert (Hfrs5' : frames S5 = []) by (rewrite Hfrs5, Hfrs4; exact Hfrs3).
assert (HPerm5' : Permutation (ablocks B ly5 S5) (ablocks B ly S)) by exact (Permutation_trans HPerm5 (Permutation_trans HPerm4 HPerm3)).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* 0x7e7dc addiw s4,s4,-1 ; 0x7e7e0 bnez s4 *)
pl_run_to HS HJ5 AG 0x7e7e0.
br_split HS Hc.
{ (* taken, bud - 1 <> 0: the back edge to 0x7e710 *)
  hc_bool Hc ltac:(fun H => hc_off H 302%nat bud (-1) Ebud). hc_prop Hc.
  rewrite Z.mod_small in Hc by lia.
  pl_run_to HS HJ5 AG 0x7e710.
  pose proof HCUR as (Hcur & Hc0 & Hcn & Hrem0 & Hcur4096 & HcurHi). cbn [c_p c_n] in Hcur, Hcn.
  (* s0 := N_cur (cur), s9 := N_rem (rem) *)
  add_atom_win HS 300%nat (Z_to_bv 64 cur) E300.
  pin_by HS (8%bv : bv 5) (SOff 300 0) ltac:(rewrite !sv_denot_SOff0, E300; ewpeel; rewrite Ecur; reflexivity).
  add_fact HS 300%nat 4096 140737479966720 E300 ltac:(lia).
  add_atom_win HS 301%nat (Z_to_bv 64 rem) E301.
  pin_by HS (25%bv : bv 5) (SOff 301 0) ltac:(rewrite !sv_denot_SOff0, E301; ewpeel; rewrite Erem; reflexivity).
  add_fact HS 301%nat 0 67108863 E301 ltac:(lia).
  (* s4 := bud - 1 through the scratch atom 308, then N_bud's old fact and the branch condition dropped *)
  add_atom_win HS 308%nat (Z_to_bv 64 (bud - 1)) E308.
  pin_by HS (20%bv : bv 5) (SOff 308 0)
    ltac:(rewrite sv_denot_SOff0, E308; cbn [sv_denot]; ewpeel; rewrite Ebud, unsigned_lit_small by lia; f_equal; lia).
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let fa := eval vm_compute in (List.filter (fun p : nat * afact => win_free 302 1 (fst p)) (f_atoms (ss_facts ssx))) in
    let cs := eval vm_compute in (List.filter (cond_atoms_on (win_free 302 1)) (f_conds (ss_facts ssx))) in
    let al := eval vm_compute in (f_alias (ss_facts ssx)) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end.
  norm_ss HS.
  clear Ebud.
  add_atom_win HS 302%nat (Z_to_bv 64 (bud - 1)) E302.
  pin_by HS (20%bv : bv 5) (SOff 302 0) ltac:(rewrite !sv_denot_SOff0, E302; ewpeel; rewrite E308; reflexivity).
  add_fact HS 302%nat 0 7 E302 ltac:(lia).
  clear E308.
  ra_join_win HS ss_L 760%nat ql_deads_bv ltac:(idtac).
  rebaseE HS AG HEv. clear HEv. relowRT HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RL HS.
  split; [unfold EV_slots, EV_check; lia|]. split; [lia|]. split; [exact HPerm5'|]. split; [exact Hin0|]. split; [exact Hrq|].
  exists cur, rem, (bud - 1), c.
  split; [exact E300|]. split; [exact E301|]. split; [exact E302|]. split; [exact HCUR|]. split; [lia|]. lia. }
(* not taken, bud - 1 = 0: 0x7e7e4 j 0x7e81c, the exit *)
pl_run_to HS HJ5 AG 0x7e81c.
ra_join_win HS ss_X 600%nat ql_deadsX_bv ltac:(idtac).
rebaseE HS AG HEv. clear HEv. relowRT HS AG E10 E11 E32 E10n E11n E32n.
rt_hand RX HS.
split; [unfold EV_slots, EV_check; lia|]. split; [cbn [c_T]; unfold ACC0 in *; lia|]. exact HPerm5'.
Qed.
End c.
End b.
