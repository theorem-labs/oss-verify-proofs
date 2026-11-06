(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan harness walk (LLVMFuzzerTestOneInput 0x7eed0 in
   fuzz_knock.asan, sha256 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118): segment S2 PARSED, from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfe.v (the journal-threaded callee call, lines 159-330) and A/ACf0.v (the
   addressable range of a frame object from its zero shadow bytes, lines 56-78) at c8557374ad2e, with their module paths
   changed and the names of a Theorem Labs lane's framework (a working branch). The S2 -> S7 boundary ss_X / INV_X is
   a Theorem Labs lane's lib/A/APgMain7.v (a working branch); the S2 -> S3 boundary ss_L / INV_L and the loop
   rt_L are a Theorem Labs lane's lib/A/APgLoop0.v / APgMainL.v (a working branch).
   rule 24: no function proved (a port of the released cgif_file_fuzzer harness walk structure). *)

(* SEGMENT S2 PARSED, pc 0x7f088-0x7f108 (33 insns), ending at ss_L (0x7f10c) or ss_X (0x7f274)
   (internal path row S2). The code (capstone 5.0.7 over the
   pinned image bytes):
     0x7f088 sd a6,16(s1); s4 = a6 + 32 (= &k); a1 = a2 | a1; a3 = a4 | a3; sb zero,4..7(s6) (unpoison k's shadow);
     a1 <<= 31; a3 <<= 47; s5 = a3 | a1 (now); sb zero,8(s6); a0 = s4; a1 = s5; 0x7f0c0 jal reac_knock_init (RA 0x7f0c4)
     0x7f0c4 lw a0,0(s4); bnez -> abort      (k.state <> 0)
     0x7f0cc lw a0,32(s4); bnez -> abort     (k.granted <> 0)
     0x7f0d4 ld a0,8(s4); bne a0,s5 -> abort (k.opened <> now)
     0x7f0dc beqz s9 -> 0x7f274 (S7)
     0x7f0e0 s10 = s11 = s2 = 0; s8 = 4094; 32(s1) = 500000000; 40(s1) = 499999999; 48(s1) = now -> 0x7f10c.
   The three aborts are killed by init's post (knock_cells 0 0 a1 (a1 + L_NS) 0 0 0, plain proof
   lib/Prog/reac_knock_init_c.v:30-31, LLVMFuzzerTestOneInput.v:391): the k region is rebuilt after the call with the
   post's values as literal chunks, so the executor decides the three branches itself.

   Changes from the donor, and why:
   - the callee is knock's reac_knock_init through a Theorem Labs lane's tknock_init_specX (lib/A/APgCSpec.v, at knock's
     instance: SEGS = tfibsegs, entry BASE + AF_asan_reac_knock_init = 0x7f44c, own-threaded journal, mo_le MT Sc S2 0,
     obj_at kp LAY_Knock [0; 0; now; (now + L_NS) mod 2^64; 0; 0; 0]); the donor called read_frameconfig (A/ACfe.v:233).
   - k lives at F+32 in the class-1 frame (128 bytes); its 5 shadow bytes are unpoisoned by the segment itself
     (0x7f098-0x7f0b4) with the shadow region writable (fs_rwF) for a run without the shadow-check table
     (aj_run_sh), then made read-only again (fs_roF) for the call.
   - the frame region is trimmed to [72,128) for the call (A/ACf0.v:50 trims to [80,256)) and [0,32) / [32,72) are
     added back after it (A/ACf0.v:136-169).

   Section hypotheses (all named; no Axiom / Admitted / Parameter): MTL : ameter_laws MT; TL : TfibLib B;
   LAWS : AR_laws tfibsegs B; TKINIT : tknock_init_specX (SK := SK) tfibsegs B MT A_reac_knock_init
   (a Theorem Labs lane's contract, lib/A/APgCSpec.v, at knock's instance); rt_S2's premises are the loop (APgMainL.rt_L) and
   S7 (APgMain7.rt_X). rt_H, the harness walk S1 .. S7 from ss_H (the statement a Theorem Labs lane's APgLib takes as RH),
   adds S7's laws (ML, ASF, FFL, MTF) and the two callee contracts the loop calls, TKHEARD / TKSTEP (a Theorem Labs lane's
   tknock_heard_specX / tknock_step_specX at knock's entries), which APgMainL.rt_loop turns into the loop through
   the four proved segments lib/A/APgMain3..6.v.  (a Theorem Labs lane, 2026-10-28: RS3..RS6 replaced by
   TKHEARD / TKSTEP; nothing else of this file changed.) *)
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
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm APgRt.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgBase APgCSpec APgMain0 APgMain7 APgMain1 APgLoop0 APgMainL.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== Part 1: the init call site ============================== *)
(* ss_X / INV_X (the S2 -> S7 boundary) are a Theorem Labs lane's, lib/A/APgMain7.v; the init contract tknock_init_specX and
   LAY_Knock / L_NS / T_init_STK / EV_init are a Theorem Labs lane's, lib/A/APgCSpec.v. The callee's entry at knock's instance:
   BASE + AF_asan_reac_knock_init = 0x7eed0 + 0x57c (a Theorem Labs lane's generated listing lib/Reusable/YI0x.v). *)
Definition A_reac_knock_init : Z := 0x7f44c.

(* ============================== Part 2: the segment ============================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
(* [A/ACf6.v:52-62] *)
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
(* knock: `mv a1, s5` is addi a1, s5, 0 *)
Lemma U_add0 : forall E e, U E (SAlu ALU_ADD e (SLit 0)) = U E e.
Proof. intros E e. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range. Qed.
(* knock: now = ((b3 << 8 | b2) << 47) | ((b1 << 8 | b0) << 31) < 2 ^ 63 from the four header registers < 2 ^ 16
   (plain proof lib/Prog/LLVMFuzzerTestOneInput.v:367-377, Ht0) *)
Lemma now_lt : forall va vb vc vd, 0 <= va < 2 ^ 16 -> 0 <= vb < 2 ^ 16 -> 0 <= vc < 2 ^ 16 -> 0 <= vd < 2 ^ 16 ->
0 <= Z.lor (Z.lor vd vc * 2 ^ 47) (Z.lor vb va * 2 ^ 31) < 2 ^ 63.
Proof.
intros va vb vc vd Ra Rb Rc Rd.
pose proof (Z_lor_bound vd vc 16 ltac:(lia) Rd Rc) as L1. pose proof (Z_lor_bound vb va 16 ltac:(lia) Rb Ra) as L2.
apply (Z_lor_bound _ _ 63); lia.
Qed.
Lemma U_now_eq : forall E a b c d va vb vc vd,
ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb -> ew E c = Z_to_bv 64 vc -> ew E d = Z_to_bv 64 vd ->
0 <= va < 2 ^ 16 -> 0 <= vb < 2 ^ 16 -> 0 <= vc < 2 ^ 16 -> 0 <= vd < 2 ^ 16 ->
U E (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_OR (SOff d 0) (SOff c 0)) (SLit 47))
  (SAlu ALU_SLL (SAlu ALU_OR (SOff b 0) (SOff a 0)) (SLit 31))) = Z.lor (Z.lor vd vc * 2 ^ 47) (Z.lor vb va * 2 ^ 31).
Proof.
intros E a b c d va vb vc vd Ha Hb Hc Hd Ra Rb Rc Rd.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom E a va Ha), (U_atom E b vb Hb), (U_atom E c vc Hc), (U_atom E d vd Hd) by lia.
change (Z.land (zcanon 47) 63) with 47. change (Z.land (zcanon 31) 63) with 31.
pose proof (Z_lor_bound vd vc 16 ltac:(lia) Rd Rc) as L1. pose proof (Z_lor_bound vb va 16 ltac:(lia) Rb Ra) as L2.
rewrite (zcanon_id (Z.lor vd vc)), (zcanon_id (Z.lor vb va)) by (unfold M64; lia).
rewrite !Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (Z.lor vd vc * 2 ^ 47)), (zcanon_id (Z.lor vb va * 2 ^ 31)) by (unfold M64; lia).
pose proof (now_lt va vb vc vd Ra Rb Rc Rd) as L3.
apply zcanon_id. unfold M64. lia.
Qed.
(* k.due = now + L_NS (init's post, plain lib/Prog/reac_knock_init_c.v:31), as s5's expression + 500000000 *)
Lemma denot_due : forall E a b c d va vb vc vd,
ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb -> ew E c = Z_to_bv 64 vc -> ew E d = Z_to_bv 64 vd ->
0 <= va < 2 ^ 16 -> 0 <= vb < 2 ^ 16 -> 0 <= vc < 2 ^ 16 -> 0 <= vd < 2 ^ 16 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_OR (SOff d 0) (SOff c 0)) (SLit 47))
  (SAlu ALU_SLL (SAlu ALU_OR (SOff b 0) (SOff a 0)) (SLit 31))) (SLit 500000000))
= Z_to_bv 64 (Z.lor (Z.lor vd vc * 2 ^ 47) (Z.lor vb va * 2 ^ 31) + L_NS).
Proof.
intros E a b c d va vb vc vd Ha Hb Hc Hd Ra Rb Rc Rd.
pose proof (now_lt va vb vc vd Ra Rb Rc Rd) as L3.
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_now_eq E a b c d va vb vc vd Ha Hb Hc Hd Ra Rb Rc Rd). rewrite U_SLit.
rewrite (zcanon_id 500000000) by (unfold M64; lia). apply zcanon_id. unfold M64, L_NS. lia.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TKINIT : tknock_init_specX (SK := SK) tfibsegs B MT A_reac_knock_init.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_S2_aux : (forall fuel, rt_from B MT FP POST ss_L (INV_L B MT fuel)) -> rt_from B MT FP POST ss_X (INV_X B MT) ->
rt_from B MT FP POST ss_P (INV_P B MT).
Proof.
intros RL RX. rt_prelude.
destruct HINV as (Hk0 & Hacc & Eab3 & c & rem & v1 & v2 & v3 & v4 & E100 & E101 & E102 & E103 & E104 & E105 &
  Hc04 & Hrem0 & Hcrem & Hremc & Bv1 & Bv2 & Bv3 & Bv4).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* 0x7f088-0x7f0c0: the spill of F, &k, now, the unpoison of k's 5 shadow bytes, the call *)
fs_rwF HS E88 HFSpres3.
aj_run_to_sh tfibtbl_lib_ok HS HJ3 0x7f44c.
1: awrRT AG fpos F EFA3.
upd_aboveW HUP HFr AG. clear_frames.
fs_roF HS. trim_base HS 75%nat 72 128.
rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
(* now: the value of s5 (0x7f0b0), below 2 ^ 63 *)
set (now0 := Z.lor (Z.lor v4 v3 * 2 ^ 47) (Z.lor v2 v1 * 2 ^ 31)).
assert (Rnow : 0 <= now0 < 2 ^ 63) by (apply now_lt; assumption).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (8%bv : bv 5) Rs0. rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
clear Ra1.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let e := eval vm_compute in (sr_get (ss_regs ssx) (11%bv : bv 5)) in
  assert (Ea1X : getr (ms_regs msx) (11%bv : bv 5) = w64 now0)
  by (refine (eq_trans (st_ok_restrict_reg tfibsegs Hh Ex ssx msx (11%bv : bv 5) HS) _); change (sv_denot Ex e = w64 now0);
      rewrite denot_lit_U, U_add0; unfold w64; f_equal;
      apply (U_now_eq _ 102 103 104 105 v1 v2 v3 v4); first [ewpeel; eassumption | lia]) end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
  assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp; exact B70);
  assert (EraX : raZ rg = 0x7f0c4) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
  assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0; exact Usp3);
  assert (Ea0X : getr rg 10 = w64 (F + 32)) by (rewrite Ra0, B75; reflexivity) end.
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
(* the 5 shadow bytes of k (F+32 .. F+72) are 0 after the unpoison: range_addressable (F+32) 40 [A/ACfe.v:186-207, A/ACf0.v:56-78] *)
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
(* 0x7f0c0 jal reac_knock_init, through a Theorem Labs lane's contract [A/ACfe.v:228-273] *)
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssX _ =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
eapply SRr_bind;
[ eapply (TKINIT LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
(F + 32) now0 1 fpos (rt_ch (mkRTCX ly S W regs mem md p n fpos sp1 E0 T)) HJ3);
[ rewrite Rra; apply ret_ok_even; vm_compute; reflexivity
| rewrite EraX; clear; lia
| rewrite Rgp; rewrite (AG 3%nat) by (clear; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
| rewrite Rtp; rewrite (AG 4%nat) by (clear; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
| exact Ea0X
| exact Ea1X
| clear - Rnow; lia
| rewrite EspX, Es0X; exact Hch1
| rewrite EspX; exact Hsp1al16
| rewrite EspX; unfold T_init_STK, ESTACK; rewrite FFS; clear - Hsp1; lia
| rewrite EspX; clear - Hsp1; lia
| left; reflexivity
| clear; lia
| rewrite EFA3; fold F; rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult
| rewrite EFA3; fold F; clear; lia
| rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear; lia
| rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); apply Z_mod_mult
| clear - HF4096; lia
| right; rewrite EspX; unfold T_init_STK, ESTACK in *; clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HFceil HF4096 HFhigh; lia
| split; [exists 1, fpos; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128;
    split; [exact Hfin3|]; split; [clear; lia|]; split; [rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by (clear; lia); apply Z_mod_mult|]; clear; lia
  | split; [rewrite HFq; replace (32 * (F / 32) + 32) with ((4 * (F / 32) + 4) * 8) by (clear; lia); apply Z_mod_mult | exact RAk]]
| unfold EV_init; rewrite HEV in Hev; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & Hk0' & _); clear - Hev Hk0 Hk0'; lia ]
| ] end end.
(* the post of reac_knock_init *)
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & HPerm4 & HIO4 & HMLE4 & K1 & K2 & K3 & K4 & HOBJ).
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
reseatL HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
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
| intros a Ha; apply K1; clear - Ha Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 HFceil; unfold T_init_STK, ESTACK in *; lia
| intros a Ha; apply Hpres4; clear - Ha Hsp1 FFS Hslo Hshi; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val tfibsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val tfibsegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
(* F[0,32) back, without chunks (nothing reads the header) [A/ACf0.v:157-168] *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 75%nat) 0 32 0 32 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite B75; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite B75; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 HF8c; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* k = F+32 .. F+72 back, with init's post as its chunks: state 0, pad 0, opened = now (s5's expression), due =
   now + L_NS, heard 0, granted 0, pad 0 (plain lib/Prog/reac_knock_init_c.v:30-31) *)
unfold LAY_Knock in HOBJ. cbn [obj_at] in HOBJ. unfold field_ok in HOBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in HOBJ.
destruct HOBJ as ((Vk0 & _) & (Vk1 & _) & (Vk2 & _) & (Vk3 & _) & (Vk4 & _) & (Vk5 & _) & (Vk6 & _) & _).
rewrite (Z.mod_small (now0 + L_NS)) in Vk3 by (unfold L_NS; lia).
lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
let e5 := eval vm_compute in (sr_get (ss_regs ssv) (21%bv : bv 5)) in
assert (D5 : sv_denot Ev e5 = Z_to_bv 64 now0)
by (rewrite denot_lit_U; f_equal; apply (U_now_eq _ 102 103 104 105 v1 v2 v3 v4); first [ewpeel; eassumption | lia]);
assert (D5d : sv_denot Ev (SAlu ALU_ADD e5 (SLit 500000000)) = Z_to_bv 64 (now0 + L_NS))
by (rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SLit;
    rewrite (U_now_eq _ 102 103 104 105 v1 v2 v3 v4) by first [ewpeel; eassumption | lia];
    rewrite (zcanon_id 500000000) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; unfold L_NS in *; lia); reflexivity);
pose proof (ast_ok_add_region tfibsegs Ev _ _
(YP09.mkRegion (Some 75%nat) 32 72 32 72
[YP09.mkChunk 32 (CVal 4 (SLit 0)); YP09.mkChunk 36 (CVal 4 (SLit 0)); YP09.mkChunk 40 (CVal 8 e5);
 YP09.mkChunk 48 (CVal 8 (SAlu ALU_ADD e5 (SLit 500000000))); YP09.mkChunk 56 (CVal 8 (SLit 0));
 YP09.mkChunk 64 (CVal 4 (SLit 0)); YP09.mkChunk 68 (CVal 4 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite B75; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
| apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 32 4 (SLit 0) 0); [reflexivity | zside | zside | replace (F + 32) with (F + 32 + 0) by lia; exact Vk0]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 36 4 (SLit 0) 0); [reflexivity | zside | zside | replace (F + 36) with (F + 32 + 4) by lia; exact Vk1]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 40 8 e5 now0); [exact D5 | lia | zside | replace (F + 40) with (F + 32 + 8) by lia; exact Vk2]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 48 8 _ (now0 + L_NS)); [exact D5d | unfold L_NS; lia | zside | replace (F + 48) with (F + 32 + 16) by lia; exact Vk3]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 56 8 (SLit 0) 0); [reflexivity | zside | zside | replace (F + 56) with (F + 32 + 24) by lia; exact Vk4]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 64 4 (SLit 0) 0); [reflexivity | zside | zside | replace (F + 64) with (F + 32 + 32) by lia; exact Vk5]|];
  apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 68 4 (SLit 0) 0); [reflexivity | zside | zside | replace (F + 68) with (F + 32 + 36) by lia; exact Vk6]|];
  apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite B75; evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HFq HF8 HF8c; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
(* 0x7f0c4-0x7f0d8: the three aborts, decided by the literal chunks; the run stops at beqz s9 (0x7f0dc) *)
aj_run_sh tfibtbl_lib_ok HS HJ4.
1: awrRT AG fpos F EFA4.
clear HUP. clear_frames.
(* 0x7f0dc beqz s9 (s9 = rem) *)
reshok HS.
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end.
all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc5 end.
all: hc_bool Hc5 ltac:(fun H => hc_atom H 100%nat rem E100 ltac:(lia)); hc_prop Hc5.
- (* rem = 0: to S7 at 0x7f274 *)
  aj_run_to_sh tfibtbl_lib_ok HS HJ4 0x7f274.
  1: awrRT AG fpos F EFA4.
  clear_frames.
  ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv. rt_hand RX HS.
  unfold INV_XP. cbn [c_T c_ly c_S].
  split; [unfold EV_init, EV_LIB; clear - Hk0; lia|].
  split; [unfold ACC0 in *; clear - Hacc HT0; lia|].
  split; [rewrite <- Eab3; exact HPerm4 | exact I].
- (* rem <> 0: 0x7f0e0-0x7f108, the loop constants and spills, to 0x7f10c *)
  aj_run_to_sh tfibtbl_lib_ok HS HJ4 0x7f10c.
  1: awrRT AG fpos F EFA4.
  clear_frames.
  assert (Hc4 : c = 4) by (clear - Hremc Hc5; lia).
  assert (Hpin : In (p, n) (ablocks B ly S)) by (destruct Hpn as [[Hn0 _] | [_ Hin]]; [exfalso; clear - Hn0 Hcrem Hc4 Hc5 Hrem0; lia | exact Hin]).
  assert (Hpin3 : In (p, n) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n (proj1 HJ3) Hpin3) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos n ltac:(clear - Hcrem Hc4 Hrem0; lia)) as [_ Hrq].
  (* the loop's slots 300-313 (the N_ names of a Theorem Labs lane's lib/A/APgLoop0.v), in increasing order *)
  rb HS AG E10 E11 E32 E10n E11n E32n.
  pin_reg HS (25%bv : bv 5) 300%nat rem' Hrem' E300.
  rewrite (U_atom _ 100 rem) in Hrem' by first [ewpeel; exact E100 | clear - Hrem0 Hcrem Hn26 Hc04; lia]. subst rem'.
  pin_reg HS (19%bv : bv 5) 301%nat cur' Hcur' E301.
  rewrite (U_atom _ 101 (p + c)) in Hcur' by first [ewpeel; exact E101 | clear - Hp4096 Hpceil Hrq C1 Hc04 Hcrem Hrem0; lia]. subst cur'.
  pin_reg HS (26%bv : bv 5) 302%nat i' Hi' E302. try rewrite U_lit0 in Hi'. subst i'.
  pin_reg HS (27%bv : bv 5) 303%nat d' Hd' E303. try rewrite U_lit0 in Hd'. subst d'.
  pin_reg HS (18%bv : bv 5) 304%nat h' Hh' E304. try rewrite U_lit0 in Hh'. subst h'.
  pin_reg HS (21%bv : bv 5) 305%nat now' Hnow' E305.
  rewrite (U_now_eq _ 102 103 104 105 v1 v2 v3 v4) in Hnow' by first [ewpeel; eassumption | lia]. fold now0 in Hnow'. subst now'.
  add_atom_win HS 306%nat (Z_to_bv 64 now0) E306.
  rechunk_at HS 70%nat 48 (SOff 306 0) ltac:(rewrite sv_denot_SOff0, E306; rewrite denot_lit_U; f_equal; symmetry;
    apply (U_now_eq _ 102 103 104 105 v1 v2 v3 v4); first [ewpeel; eassumption | lia]).
  add_atom_win HS 307%nat (Z_to_bv 64 now0) E307.
  rechunk_at HS 75%nat 40 (SOff 307 0) ltac:(rewrite sv_denot_SOff0, E307; rewrite denot_lit_U; f_equal; symmetry;
    apply (U_now_eq _ 102 103 104 105 v1 v2 v3 v4); first [ewpeel; eassumption | lia]).
  add_atom_win HS 308%nat (Z_to_bv 64 (now0 + L_NS)) E308.
  rechunk_at HS 75%nat 48 (SOff 308 0) ltac:(rewrite sv_denot_SOff0, E308; symmetry;
    apply (denot_due _ 102 103 104 105 v1 v2 v3 v4); first [ewpeel; eassumption | lia]).
  add_atom_win HS 309%nat (Z_to_bv 64 0) E309.
  rechunk_at HS 75%nat 56 (SOff 309 0) ltac:(rewrite sv_denot_SOff0, E309; reflexivity).
  add_atom_win HS 310%nat (Z_to_bv 64 0) E310.
  rechunk_at HS 75%nat 32 (SOff 310 0) ltac:(rewrite sv_denot_SOff0, E310; reflexivity).
  add_atom_win HS 311%nat (Z_to_bv 64 0) E311.
  rechunk_at HS 75%nat 64 (SOff 311 0) ltac:(rewrite sv_denot_SOff0, E311; reflexivity).
  add_atom_win HS 312%nat (Z_to_bv 64 0) E312.
  rechunk_at HS 75%nat 36 (SOff 312 0) ltac:(rewrite sv_denot_SOff0, E312; reflexivity).
  add_atom_win HS 313%nat (Z_to_bv 64 0) E313.
  rechunk_at HS 75%nat 68 (SOff 313 0) ltac:(rewrite sv_denot_SOff0, E313; reflexivity).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  (* the loop's atom facts (APgLoop0 rl_atomsK / rl_atomsR) *)
  add_fact HS 310%nat 0 2 E310 ltac:(clear; lia). add_fact HS 311%nat 0 1 E311 ltac:(clear; lia).
  add_fact HS 312%nat 0 4294967295 E312 ltac:(clear; lia). add_fact HS 313%nat 0 4294967295 E313 ltac:(clear; lia).
  add_fact HS 307%nat 0 9223372036854775807 E307 ltac:(clear - Rnow; lia).
  add_fact HS 308%nat 0 18446744073709551615 E308 ltac:(clear - Rnow; unfold L_NS; lia).
  add_fact HS 309%nat 0 9223406396593514176 E309 ltac:(clear; lia).
  add_fact HS 300%nat 0 67108863 E300 ltac:(clear - Hrem0 Hcrem Hn26 Hc04; lia).
  add_fact HS 301%nat 4096 140737479966720 E301 ltac:(clear - Hp4096 Hpceil Hrq C1 Hc04 Hc4 Hcrem Hc5 Hrem0; lia).
  add_fact HS 302%nat 0 4095 E302 ltac:(clear; lia). add_fact HS 303%nat 0 1 E303 ltac:(clear; lia). add_fact HS 304%nat 0 1 E304 ltac:(clear; lia).
  add_fact HS 305%nat 0 9223406396593514176 E305 ltac:(clear - Rnow; lia). add_fact HS 306%nat 0 9223406396593514176 E306 ltac:(clear - Rnow; lia).
  ra_join_win HS ss_L 760%nat rt_loop_deads7_bv ltac:(idtac).
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv. rt_hand (RL (Z.to_nat rem)) HS.
  (* INV_L (a Theorem Labs lane's lib/A/APgLoop0.v) at fuel = rem: rem = n - 4 >= 1, cur = p + 4, i = 0, d = h = 0,
     now = quiet = opened = now0, due = now0 + L_NS, heard = state = granted = pads = 0 (plain proof
     lib/Prog/LLVMFuzzerTestOneInput.v:401-404, the knock_loop call with d = h = 0) *)
  split; [unfold EV_init, EV_LIB; clear - Hk0; lia|].
  split; [unfold ACC0 in *; clear - Hacc; lia|].
  split; [rewrite <- Eab3; exact HPerm4|].
  exists rem, (p + c), 0, 0, 0, now0, now0, now0, (now0 + L_NS), 0, 0, 0, 0, 0, c.
  unfold inv_cells, inv_knock, inv_cursor, st_ofZ; cbn [c_p c_n c_T].
  repeat match goal with |- _ /\ _ => split end;
  first [ assumption | reflexivity | (left; reflexivity) | (intros; split; reflexivity) | (intros _ Hx; discriminate Hx)
        | (unfold ACC0 in *; clear - HT0; lia) | (clear - Rnow; unfold L_NS; lia)
        | (clear - Hp4096 Hpceil Hrq C1 Hc04 Hcrem Hrem0 Hc4 Hc5; lia) | (clear; lia) ].
Qed.
(* S2 PARSED: ss_P (0x7f088) -> ss_L (0x7f10c) or ss_X (0x7f274) *)
Lemma rt_S2 : (forall fuel, rt_from B MT FP POST ss_L (INV_L B MT fuel)) -> rt_from B MT FP POST ss_X (INV_X B MT) ->
rt_from B MT FP POST ss_P (INV_P B MT).
Proof. exact rt_S2_aux. Qed.
End e.
(* ============================== Part 3: the harness walk from ss_H ============================== *)
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable FP : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis FP0 : FP = [].
Hypothesis TKINIT : tknock_init_specX (SK := SK) tfibsegs B MT A_reac_knock_init.
(* the two callees the loop calls (lib/A/APgMain4.v S4 TAIL, lib/A/APgMain5.v S5 MID), at knock's entries *)
Hypothesis TKHEARD : tknock_heard_specX (SK := SK) tfibsegs B MT A_reac_knock_heard.
Hypothesis TKSTEP : tknock_step_specX (SK := SK) tfibsegs B MT A_reac_knock_step.
Theorem rt_H : rt_from B MT FP (rt_post B MT FP) ss_H (INV_0 B MT 0).
Proof.
refine (rt_S1 (SK := SK) B MT FP (rt_post B MT FP) TL LAWS FP0 _).
apply (rt_S2 B MT MTL FP (rt_post B MT FP) TL LAWS TKINIT).
- intros fuel. eapply (rt_loop (SK := SK)); eassumption.
- exact (rt_X (SK := SK) B MT FP MTL TL LAWS ML ASF FFL MTF).
Qed.
End h.
End c.
