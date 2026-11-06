(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the
   theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc image A (fuzz_qdisc.asan, sha256
   980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e) from
   proofs/libreac/fuzz_knock/lib/A/APgMain0.v (its harness entry segment knock_lib_A_seg, lines 162-382)
   at origin/ossv/recipes 6ebe35ba632, with its module paths changed and knock's fake-frame block removed.
   rule 24 (reuse): no function is proved here; this is SEGMENT S0, the entry of
   LLVMFuzzerTestOneInput's walk. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/QPgMain0.v of this library, for fuzz_qdisc's
   ASan-UBSan image (fuzz_qdisc.asan-ubsan, sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062),
   LLVMFuzzerTestOneInput at 0x7e694. The framework imports move to the lib/AU twins (AWalkFw0 YCef YF0l YCej YCeh
   YCem YCep AWalkFw1 AWalkFw2 YCfm), the walk's context and states to lib/AU/APgRt.v / lib/AU/APgLoop0.v, every
   pc is the asan-ubsan one, and the loop head pins s10 (x26) where the A image pins s9 (x25).

   THE CODE, 0x7e694-0x7e724 (capstone 5.0.7 over the pinned image):
     0x7e694  addi sp,sp,-0x60; 12 x `sd` of ra and s0..s10 at 0x58(sp)..0(sp) (s10 at 0(sp) last, 0x7e6c4)
     0x7e6c8  lui a2,0xfc000 / add a3,a1,a2 / addiw a2,a2,1
     0x7e6d4  bltu a3,a2 -> 0x7e848   THE SIZE REFUSAL (branch 1)
     0x7e6d8  addi s0,a0,1 / addi a2,zero,1
     0x7e6e0  bgeu a2,s0 -> 0x7e884   THE UBSan POINTER-OVERFLOW TEST of data + 1 (0x7e884 is an `unimp` word)
     0x7e6e4  auipc a2,0x17 / ld a2,0x21c(a2) (the .got slot 0x95900) / ld s3,0(a2)   s3 = SB
     0x7e6f0  srli a2,a0,3 / add a2,a2,s3 / lb a2,0(a2) / bnez a2 -> 0x7e888  the shadow check of data[0]
              (slow path 0x7e888-0x7e88c, report call 0x7e890)
     0x7e700  lbu a0,0(a0) / andi s4,a0,7                              budgets = data[0] & 7
     0x7e708  beqz s4 -> 0x7e848      NO BUDGET (branch 2)
     0x7e70c  addi s10,a1,-1 / auipc a0,0xfffa2 / li s5,1 / li s6,2 /
              addi s7,a0,0x570 (= 0x20c80, the frame-rate table) / li s8,0xab
     0x7e724  not s9,s7               s9 = APgLoop0.QD_NFPS, which the engine folds to a literal
     0x7e728  the loop head, ss_L
   What differs from the A image (0x7e68c-0x7e710): twelve saves, not eleven; s0 = p + 1 is formed BEFORE
   the read (0x7e6d8) and tested by the UBSan check 0x7e6e0; the .got slot is 0x95900 (A: 0x958c8); the
   remaining count lives in s10 (A: s9) and s9 holds `not s7`; the exits go to 0x7e848 (A: 0x7e81c) and the
   head is 0x7e728 (A: 0x7e710).

   THE TWO BRANCHES the walk splits, and what decides each.
   (1) 0x7e6d4 `bltu a3,a2` with a3 = n - 2 ^ 26 and a2 = 1 - 2 ^ 26, both wrapped to 64 bits. The engine
       cannot decide it, so the walk splits it. The contract already gives 0 <= n < 2 ^ 26 (the C test is
       `size >= FUZZ_INPUT_MAX` with FUZZ_INPUT_MAX = 64 << 20 = 2 ^ 26), so on that range the wrapped a3
       is n - 2 ^ 26 + 2 ^ 64 (lib/AU/APgRt.v qd_size_wrap) and the branch is taken exactly when n = 0.
       TAKEN goes to the exit block ss_X; FALL-THROUGH gives 1 <= n, hence the block fact
       In (p, n) (ablocks B ly S) and req_size n = n.
   (2) 0x7e708 `beqz s4` on budgets = data[0] & 7: undecided, split. TAKEN goes to ss_X; FALL-THROUGH
       gives 1 <= budgets, and APgLoop0.qd_land7 gives budgets <= 7, so the loop runs at most 7 times and
       the loop closure's fuel is 7.
   THE SITES THE ENGINE REFUTES ITSELF.
   - 0x7e6e0 `bgeu a2,s0` (a2 = 1, s0 = p + 1) traps iff p + 1 <=u 1. Right after the fall-through of (1)
     the walk adds atom 10's (= p) fact [4096, 140737479966720] (from AR_blocks_law's 4096 <= p and
     p + n <= alloc_ceiling over the block fact), and with it the executor decides the test not taken
     (decide_cond BC_GEU over the atom ranges), so the trap word 0x7e884 is never reached.
   - the shadow check of data[0] at 0x7e6f0-0x7e6fc is paid by obl_pay from the block fact, so its slow
     path 0x7e888 and the report call at 0x7e890 are never reached.
   The only writes of the segment are the twelve `sd` of the prologue, all inside [sp0-96, sp0), paid by
   APgRt.awrRT's stack case. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm APgRt APgLoop0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Variable FP : list (Z * Z).
Hypothesis FP0 : FP = [].
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis RL : rt_from B MT FP POST ss_L (INV_L B MT 7).
Hypothesis RX : rt_from B MT FP POST ss_X (INV_X B MT).
Theorem qdisc_lib_A_seg : forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n T,
afn_pre tfibsegs B LLVMF_STK ly S W regs mem md [] ->
raZ regs = RA_LLVMF ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> st_nev S + EV_LIB <= EV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
mo_ok MT S T -> 0 <= T ->
SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md)
(POST (mkRTCX ly S W regs mem md p n (Ereg regs rt_extra) T)).
Proof.
intros ly S W regs mem md p n T HPRE Hra Hp Hn Hpn Hfr0 Hev Hlive HROD HMOK HT0.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof (rt_entry B TL LAWS W ly S regs mem md p n HPRE Hp Hn Hpn) as HS.
pose proof (ajournal_init tfibsegs B LLVMF_STK FP ly S W regs mem md [] HPRE) as HJ.
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (HEV : EV_LIB = 0) by reflexivity.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn' _]]; lia).
remember (Ereg regs rt_extra) as E eqn:HE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact Hp).
assert (E11 : ew E 11 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
by (intros mm r Hmm; rewrite HE; apply ew_Ereg_nat; exact Hmm).
clear HE.
(* the context record and the two facts rt_hand reads out of the goal's shape *)
assert (HBASE0 : rt_base B MT (mkRTCX ly S W regs mem md p n E T)).
{ unfold rt_base. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_E0 c_T].
  repeat match goal with |- _ /\ _ => split end;
  try (unfold ACC0; exact HT0); try assumption; try reflexivity. }
assert (AGb : rt_E (mkRTCX ly S W regs mem md p n E T) E)
by (unfold rt_E; cbn [c_E0]; intros; reflexivity).
unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 A_LLVMF).
shok_auto SHOK RTBx E (mrestrict (w_H W) mem).
assert (AG : forall m, (m < 33)%nat -> ew E m = ew E m) by (intros; reflexivity).
(* 0x7e694 .. 0x7e6d4: the prologue and the size test *)
aj_run_tok tfibtbl_lib_ok HS HJ SHOK RTBspan. { awrRT AG. }
upd_aboveW_init HFr AG HUP. clear_frames.
br_split HS Hc0.
- (* (1) TAKEN: n = 0, the harness returns 0 at once *)
  rb HS AG E10 E11 E32 E10n E11n E32n.
  pl_run_to HS HJ AG 0x7e848. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  assert (Hfrs3 : frames S = []) by exact Hfr0.
  assert (HML0 : mo_le MT S S 0) by (apply (mo_le_refl MT MTL)).
  ra_join_win HS ss_X 600%nat ql_deadsX_bv ltac:(idtac).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RX HS.
  split; [rewrite HEV; clear; lia|]. split; [cbn [c_T]; exact HT0|].
  cbn [c_ly c_S]. apply Permutation_refl.
- (* (1) FALL-THROUGH: 1 <= n, so the input block is real *)
  rb HS AG E10 E11 E32 E10n E11n E32n.
  assert (Hn1 : 1 <= n).
  { destruct Hpn as [[Hn0 _] | [Hgt _]]; [|lia].
    exfalso. hc_bool Hc0 ltac:(fun H => hc_off H 11%nat n (-67108864) E11).
    rewrite (qd_size_wrap n Hn26) in Hc0. hc_prop Hc0. lia. }
  assert (Hpin : In (p, n) (ablocks B ly S)) by (destruct Hpn as [[Hn0 _] | [_ Hin]]; [exfalso; lia | exact Hin]).
  assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [exfalso; lia | reflexivity]).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpin) as (_ & Hp4096 & Hpceil & HinApp & _).
  rewrite Hrq in Hpceil, HinApp.
  pose proof YM05.alloc_ceiling_val as Hceilv.
  pose proof (blk_off_img B _ _ _ _ _ p n HAR Hpin) as HoffImg. rewrite Hrq in HoffImg.
  assert (HpR : 4096 <= p /\ p + n <= alloc_ceiling) by (clear - Hp4096 Hpceil Hrq Hn1; lia).
  (* atom 10 (= p) in [4096, 2^47 - 2^23]: what decides the UBSan test 0x7e6e0 `bgeu a2,s0` (a2 = 1,
     s0 = p + 1) not taken, so its trap word 0x7e884 is never reached *)
  add_fact HS 10%nat 4096 140737479966720 E10n ltac:(clear - HpR C1 Hn26; lia).
  (* 0x7e6d8 .. 0x7e708: s0 = p + 1, the UBSan test (decided), s3 = SB, the shadow-checked read of data[0]
     (report call 0x7e890 not reached), budgets = data[0] & 7 *)
  in_bytes HJ (mkRTCX ly S W regs mem md p n E T) LAWS HAR Hpin Hpin Hrq FP0 0 1%nat.
  add_atom_win HS 200%nat (Z_to_bv 64 b) E200.
  in_region HS (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 200 0))]) E10n AG.
  rd_run HS HJ AG E10n E32n Hpin Hrq. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  (* budgets into its own atom, before the test that reads it *)
  pin_reg HS (20%bv : bv 5) 302%nat bud Hbud E302.
  assert (Hbud7 : 0 <= bud <= 7).
  { rewrite Hbud. rewrite U_and_lit by lia. apply qd_land7.
    lazymatch goal with |- 0 <= U ?Ev _ => pose proof (U_zext8_lt Ev (SOff 200 0)) end. lia. }
  add_fact HS 302%nat 0 7 E302 ltac:(clear - Hbud7; lia).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  br_split HS Hc1.
  + (* (2) TAKEN: no budget, the harness returns 0 *)
    rb HS AG E10 E11 E32 E10n E11n E32n.
    pl_run_to HS HJ AG 0x7e848. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    assert (Hfrs3 : frames S = []) by exact Hfr0.
    assert (HML0 : mo_le MT S S 0) by (apply (mo_le_refl MT MTL)).
    ra_join_win HS ss_X 600%nat ql_deadsX_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RX HS.
    split; [rewrite HEV; clear; lia|]. split; [cbn [c_T]; exact HT0|].
    cbn [c_ly c_S]. apply Permutation_refl.
  + (* (2) FALL-THROUGH: 1 <= budgets <= 7, the loop head *)
    assert (Hbud1 : 1 <= bud).
    { destruct (Z.eq_dec bud 0) as [Hb0|]; [|lia]. exfalso.
      hc_bool Hc1 ltac:(fun H => hc_atom H 302%nat bud E302 ltac:(clear - Hbud7; lia)). hc_prop Hc1. lia. }
    rb HS AG E10 E11 E32 E10n E11n E32n.
    (* 0x7e70c .. 0x7e724: s10 = n - 1, s5 = 1, s6 = 2, s7 = 0x20c80, s8 = 171, s9 = not s7 *)
    pl_run_to HS HJ AG 0x7e728. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    (* the cursor (s0 = p + 1) and the remaining byte count (s10 = n - 1) into their own atoms *)
    add_atom_win HS 300%nat (Z_to_bv 64 (p + 1)) E300.
    pin_by HS (8%bv : bv 5) (SOff N_cur 0)
      ltac:(rewrite sv_denot_SOff0, E300; cbn [sv_denot]; ewpeel; rewrite E10n;
            rewrite ?unsigned_lit_small by (clear - HpR C1 Hn26; lia); first [reflexivity | f_equal; lia]).
    add_fact HS 300%nat 4096 140737479966720 E300 ltac:(clear - HpR C1 Hn1; lia).
    add_atom_win HS 301%nat (Z_to_bv 64 (n - 1)) E301.
    pin_by HS (26%bv : bv 5) (SOff N_rem 0)
      ltac:(rewrite sv_denot_SOff0, E301; cbn [sv_denot]; ewpeel; rewrite E11n;
            rewrite ?unsigned_lit_small by (clear - Hn26 Hn1; lia); first [reflexivity | f_equal; lia]).
    add_fact HS 301%nat 0 (2 ^ 26 - 1) E301 ltac:(clear - Hn26 Hn1; lia).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    assert (Hfrs3 : frames S = []) by exact Hfr0.
    assert (HML0 : mo_le MT S S 0) by (apply (mo_le_refl MT MTL)).
    ra_join_win HS ss_L 760%nat ql_deads_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RL HS.
    split; [rewrite HEV; clear; lia|]. split; [unfold ACC0; clear; lia|].
    cbn [c_ly c_S c_p c_n]. split; [apply Permutation_refl|]. split; [exact Hpin|]. split; [exact Hrq|].
    exists (p + 1), (n - 1), bud, 1.
    split; [exact E300|]. split; [exact E301|]. split; [exact E302|].
    unfold inv_cursor. cbn [c_p c_n].
    split; [clear - HpR Hn1 Hn26 C1; repeat split; lia|].
    split; [clear - Hbud1 Hbud7; lia|].
    clear - Hbud1 Hbud7; lia.
Qed.
End d.
End b.
