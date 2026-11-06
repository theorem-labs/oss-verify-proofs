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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgMain2.v, with its module paths, module names and addresses changed; 709 of its 800 lines of code are new or changed and 292 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgMain4.v of this library, for reac-pw/fuzz_pin's
   image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f). What
   differs: the imports are image B's lib/AU twins (the core's Y files, lib/AU/PPgSat.v, PPgMainCall.v, PPgMainRt.v,
   PPgMainSt.v, PPgMain4b.v; the shared texts lib/A/PPgBase.v, PPgCSpec.v and lib/A/Prog/PinBlkTail.v are the
   same); the four callees are taken at image B's entry addresses (reac_box_pin_parse 0x80ba4, check_known 0x80af8,
   check_row 0x80b24, check_label 0x80b48) and the runs stop there; the segment is image B's 0x808f0 .. 0x80960
   (ss_D at 0x808f0, the parse call at 0x80934, check_known at 0x80940, `bnez s6` 0x80944, the cell loads and
   check_row / check_label at 0x80950 / 0x8095c, ss_F at 0x80960): image A's words of 0x808bc .. 0x8092c with the
   label cell in s9 and the flags byte in s10 (image A: s10 and s9), which the proof text does not name (the
   argument words are a0 = ((fl & 1) - 1) & q, a1 = (((fl << 62) >> 63) - 1) & (F + 32), a2 = (((fl << 61) >> 63)
   - 1) & (F + 64) in both images: `andi a0,s10,1` 0x808fc, `slli a1,s10,62` 0x80900, `slli s10,s10,61` 0x80904,
   `and a2,a2,s9` 0x80930). The trap branches of image B are not in this segment. The text below is the A file's;
   where its comments name image A's addresses, image B's are 0x34 higher (0x808bc -> 0x808f0, ..., 0x8092c ->
   0x80960). *)
(* Segment S4 of reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4, fuzz_pin.asan sha256
   3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16), pc 0x808bc .. 0x80930, from the cut state ss_D
   (INV_D) to ss_X (INV_X), lib/A/PPgMainSt.v:
     0x808bc-0x808fc  s11 = F + 32 (the model cell), s10 = F + 64 (the label cell); their shadow bytes s7 + 4 and
                      s7 + 8 := 0; both cells := 0; a0 / a1 / a2 = q / F + 32 / F + 64, each 0 when its flag bit
                      (bit 0 / 1 / 2 of the flags byte) is set (PPgMain4b.pm_arg);
     0x80900          reac_box_pin_parse through tpin_parse_specX (call-site lemma pin_parse_site); the frame
                      region is cut to [72, 128) for the call and rebuilt whole from the post (knock
                      lib/A/APgMain2.v's pattern), the cells as chunks when the pin is accepted;
     0x8090c          check_known(rc, want) through tpin_check_known_specX (pin_known_site);
     rc = 0:          the two cell loads (no instrumented check: the harness's own frame) and check_row /
                      check_label at 0x8091c / 0x80928 through tpin_check_row_specX / tpin_check_label_specX
                      (pin_row_chk_site, pin_label_site);
     0x8092c          the join into lib/A/PPgMain4b.v's ss_F, whose run through free at 0x80930 into ss_X is
                      PPgMain4b.pm_S4F (call-site lemma pin_free_site).
   The register values come from PPgMain4b's bridge: pin_parse_res at the flag-masked words is the harness's
   want / want_label (pm_parse_res_harness, pm_parse_known, pm_parse_row_label).
   This file proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk, S4). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgSat PPgMainCall PPgMainRt PPgMainSt PPgMain4b.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Prog Require Import PinBlkTail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* ------------------------------ the flag masks of 0x808c8 .. 0x808fc ------------------------------
   a0 = ((fl & 1) - 1) & q, a1 = (((fl << 62) >> 63) - 1) & (F + 32), a2 = (((fl << 61) >> 63) - 1) & (F + 64):
   each word is 0 when its flag bit is set and the pointer otherwise (PPgMain4b.pm_arg). *)
Lemma fl_bit0 : forall fl, 0 <= fl < 256 -> zcanon (Z.land fl (zcanon 1)) = (if Z.testbit fl 0 then 1 else 0).
Proof.
intros fl Hfl.
assert (H : forallb (fun z => zcanon (Z.land z (zcanon 1)) =? (if Z.testbit z 0 then 1 else 0)) (map Z.of_nat (seq 0 256)) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat fl). split; [lia | apply in_seq; lia].
Qed.
Lemma fl_bitk : forall fl sh bit, 0 <= fl < 256 -> (sh = 62 /\ bit = 1) \/ (sh = 61 /\ bit = 2) ->
zcanon (Z.shiftr (zcanon (Z.shiftl fl (Z.land (zcanon sh) 63))) (Z.land (zcanon 63) 63)) = (if Z.testbit fl bit then 1 else 0).
Proof.
intros fl sh bit Hfl Hsb.
assert (H : forallb (fun z => (zcanon (Z.shiftr (zcanon (Z.shiftl z (Z.land (zcanon 62) 63))) (Z.land (zcanon 63) 63)) =? (if Z.testbit z 1 then 1 else 0)) &&
(zcanon (Z.shiftr (zcanon (Z.shiftl z (Z.land (zcanon 61) 63))) (Z.land (zcanon 63) 63)) =? (if Z.testbit z 2 then 1 else 0))) (map Z.of_nat (seq 0 256)) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H fl ltac:(apply in_map_iff; exists (Z.to_nat fl); split; [lia | apply in_seq; lia])).
apply andb_prop in H as [H1 H2]. destruct Hsb as [[-> ->] | [-> ->]]; apply Z.eqb_eq; assumption.
Qed.
Section u. Context {fx : YK11.FPState}.
Lemma U_flag_bit0 : forall E fl, ew E 103 = Z_to_bv 64 fl -> 0 <= fl < 256 ->
U E (SAlu ALU_AND (SOff 103 0) (SLit 1)) = (if Z.testbit fl 0 then 1 else 0).
Proof. intros E fl H Hfl. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E 103 fl H) by lia. apply fl_bit0; exact Hfl. Qed.
Lemma U_flag_bitk : forall E fl sh bit, ew E 103 = Z_to_bv 64 fl -> 0 <= fl < 256 -> (sh = 62 /\ bit = 1) \/ (sh = 61 /\ bit = 2) ->
U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 103 0) (SLit sh)) (SLit 63)) = (if Z.testbit fl bit then 1 else 0).
Proof. intros E fl sh bit H Hfl Hsb. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom E 103 fl H) by lia. apply fl_bitk; assumption. Qed.
Lemma denot_flag_arg : forall E c e fl bit x, U E c = (if Z.testbit fl bit then 1 else 0) -> U E e = x ->
sv_denot E (SAlu ALU_AND (SAlu ALU_ADD c (SLit (-1))) e) = Z_to_bv 64 (pm_arg fl bit x).
Proof.
intros E c e fl bit x Hc He. rewrite denot_lit_U. f_equal. rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Hc, He.
pose proof (U_range E e) as Hr. rewrite He in Hr. unfold M64 in Hr. unfold pm_arg.
destruct (Z.testbit fl bit).
- change (zcanon (1 + zcanon (-1))) with 0. rewrite Z.land_0_l. reflexivity.
- change (zcanon (0 + zcanon (-1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia.
  apply zcanon_id. unfold M64. lia.
Qed.
End u.
Lemma mod8_of_mod32 : forall x c, x mod 32 = 0 -> c mod 8 = 0 -> (x + c) mod 8 = 0.
Proof.
intros x c Hx Hc. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
replace (x + c) with (c + (4 * (x / 32)) * 8) by lia. rewrite Z_mod_plus_full. exact Hc.
Qed.
(* the value of register r in the state HS is v, by the register's symbolic expression *)
Ltac reg_is HS r v H tac :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
assert (H : getr (ms_regs msx) r = v)
by (refine (eq_trans (st_ok_restrict_reg tfibsegs Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac) end.
(* the regions of a symbolic memory without the ones on base n *)
Definition rm_base (rs : smem) (n : nat) : smem :=
List.filter (fun r => match YP09.r_base r with Some b => negb (Nat.eqb b n) | None => true end) rs.
Ltac drop_base HS n :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in (rm_base (ss_mem ssx) n) in
let HS3 := fresh "HS3" in
pose proof (st_ok_submem tfibsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
(* the frame chain from sp1 at a call of the harness, from the saved ra / s0 of region 2 [knock A/APgMain2.v:177-199] *)
Ltac pm_chain cx HS HJx HUPx Hchn AG Usp EE Hch Qtop64 Qra Qs0 Hra4 Hceil Hslo Hstk0 FFS Qal8 Hsp1 :=
lazymatch cx with mkRTCX ?ly ?S0 ?W0 ?regs ?mem0 ?md0 ?p0 ?n0 ?pl0 ?fpos0 ?sp1 ?E00 ?T0 =>
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let Uspx := fresh "Uspx" in
assert (Uspx : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp);
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
let HRstk := fresh "HRstk" in let Vra := fresh "Vra" in let Vs0 := fresh "Vs0" in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wx) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Uspx ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Uspx ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
lazymatch type of HJx with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx _ _ _ _ _ =>
assert (Hchn : achain lyx (aview tfibsegs (w_H Wx) (ms_mem msX)) sp1 (spZ regs) (rt_ch cx));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJx)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUPx (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| clear Vra Vs0 Uspx ] end end end.
(* the frame part of the registers at a call: ra, sp = sp1, s0 = sp0, gp, tp *)
Ltac pm_regs cx HS ra Rra Rsp Rs0 Rgp Rtp AG E70 E2 EE :=
reg_is HS (1%bv : bv 5) (Z_to_bv 64 ra) Rra ltac:(reflexivity);
reg_is HS (2%bv : bv 5) (Z_to_bv 64 (c_sp1 cx)) Rsp ltac:(rewrite sv_denot_SOff0; exact E70);
reg_is HS (8%bv : bv 5) (getr (c_regs cx) 2) Rs0 ltac:(rewrite sv_denot_SOff0, (AG 2%nat) by lia; exact E2);
reg_is HS (3%bv : bv 5) (getr (c_regs cx) 3) Rgp ltac:(rewrite sv_denot_SOff0, (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
reg_is HS (4%bv : bv 5) (getr (c_regs cx) 4) Rtp ltac:(rewrite sv_denot_SOff0, (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl)).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis FP0 : FP = [].
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE4 : afree04_rule tfibsegs B MT.
Hypothesis FCAT : pin_ro_law tfibsegs B PM_RLO PM_RHI PM_CAT PM_TP PM_DP PM_COLONP.
Hypothesis TPARSE : tpin_parse_specX (SK := SK) tfibsegs B MT PM_RLO PM_RHI 0x80ba4 PM_CAT PM_COLONP PM_TP PM_DP.
Hypothesis TKNOWN : tpin_check_known_specX (SK := SK) tfibsegs B MT 0x80af8.
Hypothesis TCROW : tpin_check_row_specX (SK := SK) tfibsegs B MT 0x80b24.
Hypothesis TCLAB : tpin_check_label_specX (SK := SK) tfibsegs B MT 0x80b48.
(* ------------------------------ the facts of rt_base the call sites use ------------------------------ *)
Lemma pm_base_sp : forall cx, rt_base B MT cx ->
spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
spZ (c_regs cx) - 144 <= c_sp1 cx <= spZ (c_regs cx) - 128 /\ c_sp1 cx mod 32 = 0 /\
getr (c_regs cx) 3 = w64 (as_gp B) /\ getr (c_regs cx) 4 = w64 (as_tp B) /\
st_nev (c_S cx) + RT_EV <= EV_MAX /\ frames (c_S cx) = [] /\ arodata_ok B (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) /\
AR tfibsegs B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx).
Proof.
intros [ly S W regs mem md p n pl fpos sp1 E0 T] HB. unfold rt_base in HB.
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T] in HB |- *.
destruct HB as (HPRE & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROD & Esp1 & EE & EX32 & Usp & HMOK & HT0).
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hs1 & Hs2 & Hs3).
rewrite <- Esp1 in Hs1, Hs2, Hs3.
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hs2|]. split; [exact Hgp|].
split; [exact Htp|]. split; [exact Hev|]. split; [exact Hfr0|]. split; [exact HROD | exact HAR].
Qed.
(* PIN-KIT at a call of the harness: the journal, ra, gp, tp, the frame chain from sp1, the stack bound *)
Lemma pm_kit : forall (cx : rtcx) ly3 S3 W3 memc mdc k (regs : bvmap 5 word) ra STK_f EV,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 memc mdc k ->
getr regs 1 = Z_to_bv 64 ra -> ra mod 2 = 0 -> 4096 <= ra < 2 ^ 64 ->
getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 -> spZ regs = c_sp1 cx ->
achain ly3 (aview tfibsegs (w_H W3) memc) (spZ regs) (s0Z regs) (rt_ch cx) ->
0 <= STK_f <= T_parse_STK -> st_nev (c_S cx) + k + EV <= EV_MAX ->
pin_pre_kit tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 memc mdc k regs (rt_ch cx) STK_f EV.
Proof.
intros cx ly3 S3 W3 memc mdc k regs ra STK_f EV HB HJ Hra Hra2 Hra4 Hgp Htp Hsp Hch HSTK HEV.
destruct (pm_base_sp cx HB) as (Hal16 & Hlo & Hhi & Hsp1 & Hsp1al & Egp & Etp & _).
assert (Hes : ESTACK = 4096) by reflexivity. assert (FFS : LLVMF_STK = 32768) by reflexivity.
unfold pin_pre_kit. split; [exact HJ|].
assert (Rra : raZ regs = ra) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
split; [apply ret_ok_even; rewrite Hra, unsigned_lit_small by lia; exact Hra2|].
split; [rewrite Rra; lia|]. split; [rewrite Hgp; exact Egp|]. split; [rewrite Htp; exact Etp|].
split; [exact Hch|]. rewrite Hsp. unfold T_parse_STK in HSTK.
split; [pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as D; rewrite Hsp1al, Z.add_0_r in D; rewrite D;
  replace (32 * (c_sp1 cx / 32)) with ((2 * (c_sp1 cx / 32)) * 16) by lia; apply Z_mod_mult|].
split; [lia|]. split; [lia|]. exact HEV.
Qed.
(* ------------------------------ call site 0x80900: reac_box_pin_parse (CP1) ------------------------------
   The state at the call gives every premise of tpin_parse_specX at a0 = sa, a1 = mo, a2 = lb (the flag-masked
   words), s = the spec string, the two cells in the harness's class-1 frame (1, fpos). *)
Lemma pin_parse_site : forall (cx : rtcx) ly3 S3 W3 memc mdc k (regs : bvmap 5 word) q fl sa mo lb,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 memc mdc k ->
frames S3 = [(1, c_fpos cx)] -> k = 1 ->
getr regs 1 = Z_to_bv 64 RT_parse_ra -> getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
spZ regs = c_sp1 cx -> achain ly3 (aview tfibsegs (w_H W3) memc) (spZ regs) (s0Z regs) (rt_ch cx) ->
fl = pin_flags (c_pl cx) ->
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(q, Z.of_nat (pin_k (c_pl cx)) + 1)]) ->
garr8 tfibsegs (mrestrict (w_H W3) memc) q (pin_zbytes (pm_s cx) ++ [0]) ->
aview tfibsegs (w_H W3) memc (SB + rt_F cx / 8 + 4) = Some 0 ->
aview tfibsegs (w_H W3) memc (SB + rt_F cx / 8 + 8) = Some 0 ->
sa = pm_arg fl 0 q -> mo = pm_arg fl 1 (rt_F cx + 32) -> lb = pm_arg fl 2 (rt_F cx + 64) ->
pin_pre_kit tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 memc mdc k regs (rt_ch cx) T_parse_STK EV_parse /\
0 <= sa < 2 ^ 64 /\ 0 <= mo < 2 ^ 64 /\ 0 <= lb < 2 ^ 64 /\
(sa <> 0 -> pin_spec_str tfibsegs (mrestrict (w_H W3) memc) (aview tfibsegs (w_H W3) memc) regs T_parse_STK sa (pm_s cx) /\
 exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= sa /\ sa + Z.of_nat (length (pm_s cx)) + 1 <= b + req_size m) /\
(pin_parse_live sa mo lb = true ->
 mo mod 8 = 0 /\ lb mod 8 = 0 /\ (mo + 8 <= lb \/ lb + 8 <= mo) /\
 In (1, c_fpos cx) [(1, c_fpos cx)] /\ 0 <= 1 /\ frame_addr ly3 1 (c_fpos cx) mod 8 = 0 /\
 frame_addr ly3 1 (c_fpos cx) <= mo /\ mo + 8 <= frame_addr ly3 1 (c_fpos cx) + fs_frame_bytes 1 /\
 In (1, c_fpos cx) [(1, c_fpos cx)] /\ 0 <= 1 /\ frame_addr ly3 1 (c_fpos cx) mod 8 = 0 /\
 frame_addr ly3 1 (c_fpos cx) <= lb /\ lb + 8 <= frame_addr ly3 1 (c_fpos cx) + fs_frame_bytes 1 /\
 afobj tfibsegs B ly3 S3 W3 memc mo 8 /\ afobj tfibsegs B ly3 S3 W3 memc lb 8 /\
 (forall x, pin_out_cell mo lb x -> ~ (spZ regs - T_parse_STK <= x < spZ regs)) /\
 (forall x, pin_out_cell mo lb x -> ~ (sa <= x <= sa + Z.of_nat (length (pm_s cx))))) /\
pin_ro_str tfibsegs (mrestrict (w_H W3) memc) (aview tfibsegs (w_H W3) memc) PM_COLONP pin_colon_bytes /\
(forall x, PM_COLONP <= x <= PM_COLONP + 1 -> ~ (spZ regs - T_parse_STK <= x < spZ regs)) /\
pin_cat_ok tfibsegs (mrestrict (w_H W3) memc) (aview tfibsegs (w_H W3) memc) PM_CAT PM_TP PM_DP /\
pin_cat_off_stack PM_CAT PM_TP regs T_parse_STK /\
arodata_okP tfibsegs PM_RLO PM_RHI B (aview tfibsegs (w_H W3) memc) /\
count_cid 0 (frames S3) < fs_frames 0.
Proof.
intros cx ly3 S3 W3 memc mdc k regs q fl sa mo lb HB HJ Hfrs3 Hk Hra Hgp Htp Hsp Hch Hfl Eab3 HG Z4 Z8 Esa Emo Elb.
pose proof (pm_base_sp cx HB) as (Hal16 & Hlo & Hhi & Hsp1 & Hsp1al & Egp & Etp & Hev & Hfr0 & HROD & HAR).
assert (Hes : ESTACK = 4096) by reflexivity. assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (KIT : pin_pre_kit tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 memc mdc k regs (rt_ch cx) T_parse_STK EV_parse).
{ apply (pm_kit cx ly3 S3 W3 memc mdc k regs RT_parse_ra T_parse_STK EV_parse HB HJ Hra); try assumption;
  unfold RT_parse_ra, T_parse_STK, EV_parse, RT_EV in *; first [reflexivity | lia]. }
destruct cx as [ly S W regs0 mem md p n pl fpos sp1 E0 T].
unfold rt_F, pm_s in *. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_fpos c_sp1 c_E0 c_T] in *.
pose proof (proj1 HJ) as HAR3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ))) as (_ & EFA3 & _).
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HFal & HFapp & HFpres3 & HFSpres3).
destruct (frames_bounds tfibsegs _ LAWS _ _ _ _ _ 1 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *. rewrite !EFA3 in *.
set (F := frame_addr ly 1 fpos) in *.
set (kk := pin_k pl) in *.
assert (Hlen : length (pin_str pl) = kk) by (apply pin_str_length).
assert (Hq3 : In (q, Z.of_nat kk + 1) (ablocks B ly3 S3))
by (apply (Permutation_in _ (Permutation_sym Eab3)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q (Z.of_nat kk + 1) HAR3 Hq3) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _ & HqMAX).
assert (Hrq : req_size (Z.of_nat kk + 1) = Z.of_nat kk + 1) by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat kk + 1) 0); lia).
rewrite Hrq in *.
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ q (Z.of_nat kk + 1) 1 fpos HAR3 Hq3 Hfin3) as HdQF.
unfold zdisjoint in HdQF. cbn [fst snd] in HdQF. change (fs_frame_bytes 1) with 128 in HdQF. rewrite EFA3, Hrq in HdQF. fold F in HdQF.
assert (HRO : arodata_okP tfibsegs PM_RLO PM_RHI B (aview tfibsegs (w_H W3) memc))
by (apply pm_arodataP; exact (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD)).
destruct (pin_ro_law_at tfibsegs B PM_RLO PM_RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FCAT HJ HRO) as (HCAT & HCOL).
assert (HMAX : MALLOC_MAX = 2 ^ 28) by reflexivity.
split; [exact KIT|].
split; [subst sa; unfold pm_arg; destruct (Z.testbit fl 0); lia|].
split; [subst mo; unfold pm_arg; destruct (Z.testbit fl 1); lia|].
split; [subst lb; unfold pm_arg; destruct (Z.testbit fl 2); lia|].
split.
{ subst sa. unfold pm_arg. destruct (Z.testbit fl 0); [intros H; exfalso; apply H; reflexivity | intros _].
  apply (pm_spec_str_blk tfibsegs B LAWS ly3 S3 W3 memc mdc regs q (pin_str pl) HAR3); [rewrite Hlen; exact Hq3 | apply pin_str_no_nul | exact HG |].
  intros x Hx. rewrite Hlen in Hx. rewrite Hsp. unfold T_parse_STK. lia. }
split.
{ subst sa mo lb. rewrite (pm_parse_live_eq q (F + 32) (F + 64) fl) by (try lia; subst fl; apply pin_flags_range).
  unfold fl_live, pm_arg. destruct (Z.testbit fl 0), (Z.testbit fl 1), (Z.testbit fl 2); cbn; intros H; try discriminate H.
  assert (HF8 : F mod 8 = 0) by (rewrite <- (Z.add_0_r F); apply mod8_of_mod32; [exact HFal | reflexivity]).
  assert (HRA : forall c, c mod 8 = 0 -> 0 <= c <= 120 -> aview tfibsegs (w_H W3) memc (SB + F / 8 + c / 8) = Some 0 ->
    afobj tfibsegs B ly3 S3 W3 memc (F + c) 8).
  { intros c Hc8 Hcr Hz. split; [exists 1, fpos; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128;
      split; [exact Hfin3|]; split; [lia|]; split; [exact HF8|]; lia|].
    split; [apply mod8_of_mod32; assumption|].
    apply zero_shadow_of_bytes; [apply mod8_of_mod32; assumption | reflexivity | lia |].
    intros i Hi. change (8 / 8) with 1 in Hi. assert (i = 0) as -> by lia. rewrite <- SB_SHADOW_OFF.
    pose proof (Z.div_mod c 8 ltac:(lia)) as Dc. rewrite Hc8, Z.add_0_r in Dc.
    replace ((F + c) / 8) with (F / 8 + c / 8) by (replace (F + c) with (F + (c / 8) * 8) by lia; rewrite Z.div_add by lia; reflexivity).
    rewrite Z.add_0_r, Z.add_assoc. exact Hz. }
  split; [apply mod8_of_mod32; [exact HFal | reflexivity]|].
  split; [apply mod8_of_mod32; [exact HFal | reflexivity]|].
  split; [lia|]. split; [left; reflexivity|]. split; [lia|]. split; [exact HF8|]. split; [lia|]. split; [lia|].
  split; [left; reflexivity|]. split; [lia|]. split; [exact HF8|]. split; [lia|]. split; [lia|].
  split; [apply HRA; [reflexivity | lia | exact Z4]|].
  split; [apply HRA; [reflexivity | lia | exact Z8]|].
  split; [intros x Hx; unfold pin_out_cell in Hx; rewrite Hsp; unfold T_parse_STK; lia|].
  intros x Hx; unfold pin_out_cell in Hx; rewrite Hlen; lia. }
split; [exact HCOL|].
split; [intros x Hx; rewrite Hsp; unfold PIN_COLONP, T_parse_STK in *; lia|].
split; [exact HCAT|].
split; [apply pin_sat_cat_off_stack; [unfold T_parse_STK; lia | rewrite Hsp; unfold T_parse_STK; lia]|].
split; [exact HRO|].
rewrite Hfrs3. apply pin_sat_fs0.
Qed.
(* a 64-bit word of a value below 2 ^ 64 is 0 exactly when the value is *)
Lemma w64_eq0 : forall v, 0 <= v < 2 ^ 64 -> (w64 v = w64 0 <-> v = 0).
Proof.
intros v Hv. split; [|intros ->; reflexivity]. intros H.
apply (f_equal (@bv_unsigned 64)) in H. unfold w64 in H. rewrite !unsigned_lit_small in H by lia. exact H.
Qed.
Lemma w64_m1_ne0 : w64 (-1) <> w64 0.
Proof. intros H. apply (f_equal (@bv_unsigned 64)) in H. vm_compute in H. discriminate H. Qed.
(* ------------------------------ call site 0x8090c: check_known (CK1) ------------------------------
   a0 = rc (reac_box_pin_parse's result, 0 or -1), a1 = want: CK1.1 is rc = 0 <-> want <> 0 *)
Lemma pin_known_site : forall (cx : rtcx) ly3 S3 W3 memc mdc k (regs : bvmap 5 word) rcv want,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 memc mdc k ->
k <= 1 ->
getr regs 1 = Z_to_bv 64 RT_known_ra -> getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
spZ regs = c_sp1 cx -> achain ly3 (aview tfibsegs (w_H W3) memc) (spZ regs) (s0Z regs) (rt_ch cx) ->
getr regs 10 = w64 rcv -> getr regs 11 = w64 want -> (rcv = 0 \/ rcv = -1) -> 0 <= want < 2 ^ 64 ->
(rcv = 0 <-> want <> 0) ->
pin_pre_kit tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 memc mdc k regs (rt_ch cx) T_leaf_STK EV_leaf /\
(getr regs 10 = w64 0 <-> getr regs 11 <> w64 0).
Proof.
intros cx ly3 S3 W3 memc mdc k regs rcv want HB HJ Hk Hra Hgp Htp Hsp Hch Ha0 Ha1 Hrc Hw Hiff.
pose proof (pm_base_sp cx HB) as (_ & _ & _ & _ & _ & _ & _ & Hev & _).
split.
- apply (pm_kit cx ly3 S3 W3 memc mdc k regs RT_known_ra T_leaf_STK EV_leaf HB HJ Hra); try assumption;
  unfold RT_known_ra, T_leaf_STK, T_parse_STK, EV_leaf, RT_EV, ESTACK in *; first [reflexivity | lia].
- rewrite Ha0, Ha1. rewrite (w64_eq0 want Hw).
  destruct Hrc as [-> | ->]; [split; [intros _; apply Hiff; reflexivity | intros _; reflexivity]|].
  split; [intros H; exfalso; exact (w64_m1_ne0 H)|]. intros Hne. exfalso. apply Hne. destruct (Z.eq_dec want 0) as [E|E]; [exact E|].
  apply Hiff in E. discriminate E.
Qed.
(* ------------------------------ call sites 0x8091c and 0x80928: check_row, check_label (CR1) ------------------------------
   a0 = the cell the parse stored (the row, the label), a1 = the harness's want / want_label: CR1.1 is a0 = a1 *)
Lemma pin_eq_site : forall (cx : rtcx) ly3 S3 W3 memc mdc k (regs : bvmap 5 word) ra v w,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 memc mdc k ->
k <= 1 -> (ra = RT_chkrow_ra \/ ra = RT_label_ra) ->
getr regs 1 = Z_to_bv 64 ra -> getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
spZ regs = c_sp1 cx -> achain ly3 (aview tfibsegs (w_H W3) memc) (spZ regs) (s0Z regs) (rt_ch cx) ->
getr regs 10 = w64 v -> getr regs 11 = w64 w -> v = w ->
pin_pre_kit tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 memc mdc k regs (rt_ch cx) T_leaf_STK EV_leaf /\
getr regs 10 = getr regs 11.
Proof.
intros cx ly3 S3 W3 memc mdc k regs ra v w HB HJ Hk Hra0 Hra Hgp Htp Hsp Hch Ha0 Ha1 Hvw.
pose proof (pm_base_sp cx HB) as (_ & _ & _ & _ & _ & _ & _ & Hev & _).
split; [|rewrite Ha0, Ha1, Hvw; reflexivity].
apply (pm_kit cx ly3 S3 W3 memc mdc k regs ra T_leaf_STK EV_leaf HB HJ Hra); try assumption;
destruct Hra0 as [-> | ->]; unfold RT_chkrow_ra, RT_label_ra, T_leaf_STK, T_parse_STK, EV_leaf, RT_EV, ESTACK in *; first [reflexivity | lia].
Qed.
Lemma pin_row_chk_site : forall (cx : rtcx) ly3 S3 W3 memc mdc k (regs : bvmap 5 word) row want,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 memc mdc k ->
k <= 1 -> getr regs 1 = Z_to_bv 64 RT_chkrow_ra -> getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
spZ regs = c_sp1 cx -> achain ly3 (aview tfibsegs (w_H W3) memc) (spZ regs) (s0Z regs) (rt_ch cx) ->
getr regs 10 = w64 row -> getr regs 11 = w64 want -> row = want ->
pin_pre_kit tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 memc mdc k regs (rt_ch cx) T_leaf_STK EV_leaf /\
getr regs 10 = getr regs 11.
Proof.
intros cx ly3 S3 W3 memc mdc k regs row want HB HJ Hk Hra Hgp Htp Hsp Hch Ha0 Ha1 He.
exact (pin_eq_site cx ly3 S3 W3 memc mdc k regs RT_chkrow_ra row want HB HJ Hk (or_introl eq_refl) Hra Hgp Htp Hsp Hch Ha0 Ha1 He).
Qed.
Lemma pin_label_site : forall (cx : rtcx) ly3 S3 W3 memc mdc k (regs : bvmap 5 word) lab wl,
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly3 S3 W3 memc mdc k ->
k <= 1 -> getr regs 1 = Z_to_bv 64 RT_label_ra -> getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
spZ regs = c_sp1 cx -> achain ly3 (aview tfibsegs (w_H W3) memc) (spZ regs) (s0Z regs) (rt_ch cx) ->
getr regs 10 = w64 lab -> getr regs 11 = w64 wl -> lab = wl ->
pin_pre_kit tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(1, c_fpos cx)] ly3 S3 W3 memc mdc k regs (rt_ch cx) T_leaf_STK EV_leaf /\
getr regs 10 = getr regs 11.
Proof.
intros cx ly3 S3 W3 memc mdc k regs lab wl HB HJ Hk Hra Hgp Htp Hsp Hch Ha0 Ha1 He.
exact (pin_eq_site cx ly3 S3 W3 memc mdc k regs RT_label_ra lab wl HB HJ Hk (or_intror eq_refl) Hra Hgp Htp Hsp Hch Ha0 Ha1 He).
Qed.
(* knock lib/A/APgMain2.v rt_region_kept_eq (cgif A/ACf6.v:52-62): a region is kept when its bytes read the same and
   its writable bytes stay present *)
Lemma pm_region_kept_eq : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
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
Lemma pm_S4 : rt_from B MT FP POST ss_X (INV_X B MT) -> rt_from B MT FP POST ss_D (INV_D B MT).
Proof.
intros RX. rt_prelude.
destruct HINV as (Hk1 & Hacc & q & fl & want & wl & E100 & E103 & E104 & E105 & Efl & Eab3 & HG3 & Ewant & Ewl).
unfold pm_s in HG3, Ewant, Ewl. cbn [c_pl] in HG3, Ewant, Ewl.
set (kk := pin_k pl) in *.
assert (Hlen : length (pin_str pl) = kk) by (apply pin_str_length).
assert (Hfl : 0 <= fl < 256) by (rewrite Efl; apply pin_flags_range).
assert (Hq3 : In (q, Z.of_nat kk + 1) (ablocks B ly3 S3))
by (apply (Permutation_in _ (Permutation_sym Eab3)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q (Z.of_nat kk + 1) HAR3 Hq3) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _ & HqMAX).
assert (Hrq : req_size (Z.of_nat kk + 1) = Z.of_nat kk + 1) by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat kk + 1) 0); lia).
rewrite Hrq in Hqceil, Hqapp, Hqpres.
pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 _ _ _ q (Z.of_nat kk + 1) 1 fpos HAR3 Hq3 Hfin3) as HdQF.
unfold zdisjoint in HdQF. cbn [fst snd] in HdQF. change (fs_frame_bytes 1) with 128 in HdQF. rewrite EFA3, Hrq in HdQF. fold F in HdQF.
relowRT HS AG E10 E11 E32 E10n E11n E32n.
(* 0x808bc-0x80900: the two cells, their shadow bytes, the three argument words, jal reac_box_pin_parse *)
fs_rwF HS E88 HFSpres3.
aj_run_to_sh tfibtbl_lib_ok HS HJ3 0x80ba4.
1: awrRT AG fpos F EFA3.
upd_aboveW HUP HFr AG.
(* the string's bytes are not in any window the run wrote *)
assert (HKq : forall a, q <= a < q + (Z.of_nat kk + 1) ->
  aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (aview_eq_of tfibsegs). apply HFr. rewrite unsigned_lit_small by lia.
  intros (rg & Hin & Hrg).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
    clear - Ha Hrg HdQF Hqapp Hqceil HF8c HF8lo HFceil HFhigh C1 C3 Hceil Hslo Hstk0 FFS; unfold SB, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|]).
  destruct Hin. }
assert (HG4 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms)) q (pin_zbytes (pin_str pl) ++ [0])).
{ apply (garr8_frame tfibsegs _ _ _ _ HG3). intros a Ha. apply (mbyte_of_aview tfibsegs). apply HKq.
  unfold pin_zbytes in Ha. rewrite length_app, length_map, Hlen in Ha. cbn [length] in Ha. lia. }
clear_frames. clear HKq HG3.
fs_roF HS.
rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
(* the cells' shadow bytes are 0: the two chunks the run wrote into region 88 *)
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
pose proof (ZS 4 ltac:(cbn; tauto)) as Z4. pose proof (ZS 8 ltac:(cbn; tauto)) as Z8. clear ZS US.
trim_base HS 75%nat 72 128.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (8%bv : bv 5) Rs0.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
  assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp; exact B70);
  assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0; exact Usp3);
  assert (RraX : getr rg 1 = Z_to_bv 64 RT_parse_ra) by (rewrite Rra; reflexivity);
  assert (RgpX : getr rg 3 = getr regs 3) by (rewrite Rgp, (AG 3%nat) by lia; exact (EE 3%nat (@BV 5 3 I) eq_refl));
  assert (RtpX : getr rg 4 = getr regs 4) by (rewrite Rtp, (AG 4%nat) by lia; exact (EE 4%nat (@BV 5 4 I) eq_refl));
  reg_is HS (10%bv : bv 5) (w64 (pm_arg fl 0 q)) Ea0X
  ltac:(unfold w64; apply denot_flag_arg; [apply U_flag_bit0; [ewpeel; exact E103 | exact Hfl] | apply U_atom; [ewpeel; exact E100 | lia]]);
  reg_is HS (11%bv : bv 5) (w64 (pm_arg fl 1 (F + 32))) Ea1X
  ltac:(unfold w64; apply denot_flag_arg; [apply (U_flag_bitk _ fl 62 1); [ewpeel; exact E103 | exact Hfl | left; split; reflexivity] | apply U_atom_off; [ewpeel; exact RF | lia | lia]]);
  reg_is HS (12%bv : bv 5) (w64 (pm_arg fl 2 (F + 64))) Ea2X
  ltac:(unfold w64; apply denot_flag_arg; [apply (U_flag_bitk _ fl 61 2); [ewpeel; exact E103 | exact Hfl | right; split; reflexivity] | apply U_atom_off; [ewpeel; exact RF | lia | lia]]) end.
clear Rgp Rtp.
(* the call's frame-chain premise [knock A/APgMain2.v:177-199] *)
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
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)));
[ unfold rt_ch; cbn [c_regs c_ly]; apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
exact (rt_chain ly _ _ regs sp1 Hch Qtop64 HUP (rdword_of_val_mem tfibsegs _ _ _ _ Vra Qra) (rdword_of_val_mem tfibsegs _ _ _ _ Vs0 Qs0) Hra4
ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8 ltac:(clear - Hsp1; lia))
| ] end.
clear Vra Vs0.
(* 0x80900 jal reac_box_pin_parse, through tpin_parse_specX at the call-site lemma pin_parse_site *)
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
destruct (pin_parse_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX) q fl
  (pm_arg fl 0 q) (pm_arg fl 1 (F + 32)) (pm_arg fl 2 (F + 64)) HBASE0 HJ3 Hfrs3 Hk1 RraX RgpX RtpX EspX
  ltac:(rewrite EspX, Es0X; exact Hch1) Efl Eab3 HG4 Z4 Z8 eq_refl eq_refl eq_refl)
  as (KIT & R1 & R2 & R3 & PS & PL & PC & PCo & PK & PKo & PRO & PF0);
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
eapply SRr_bind;
[ eapply (TPARSE LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) mdX k (ms_regs msX)
  (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) (pm_arg fl 0 q) (pm_arg fl 1 (F + 32)) (pm_arg fl 2 (F + 64))
  (pm_s (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) 1 fpos 1 fpos KIT Ea0X Ea1X Ea2X R1 R2 R3 PS PL PC PCo PK PKo PRO FCAT PF0)
| ] end.
clear KIT R1 R2 R3 PS PL PC PCo PK PKo PRO PF0.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & HPerm4 & HIO4 & HMLE4 & K1 & K2 & K3 & K4 & Hrc4 & Hout4).
rewrite EspX in K1. rewrite RraX.
pose proof (mle_station MT S S3 S4 acc 0 MTL HMLE HMLE4) as HMLE4c.
pose proof (proj1 HJ4) as HAR4.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = [(1, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
assert (HOC : forall a, pin_out_cell (pm_arg fl 1 (F + 32)) (pm_arg fl 2 (F + 64)) a -> (F + 32 <= a < F + 72) \/ (0 <= a < 8))
by (intros a Ha; unfold pin_out_cell, pm_arg in Ha; destruct (Z.testbit fl 1), (Z.testbit fl 2); lia).
reseatL HS HJ4 HP4 [0; 1; 2]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
  eapply pm_region_kept_eq; [ evalE AG
  | intros a Ha; apply (K3 1 fpos a Hfin3);
    [ right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 1 / 8) with 16; clear - Ha; unfold SB in *; lia
    | intros Hx; destruct (HOC a Hx) as [Hx'|Hx']; clear - Ha Hx' HF8c HF8lo HFhigh HFceil C1 C3; unfold SB, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia ]
  | intros a Ha; exfalso; clear - Ha; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
  eapply pm_region_kept_eq; [ evalE AG
  | intros a Ha; apply (K3 1 fpos a Hfin3);
    [ left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3; fold F; change (fs_frame_bytes 1) with 128; clear - Ha; lia
    | intros Hx; destruct (HOC a Hx) as [Hx'|Hx']; clear - Ha Hx' HF4096; lia ]
  | intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
  eapply pm_region_kept_eq; [ evalE AG
  | intros a Ha; apply K1;
    [ clear - Ha Hceil Hslo Hshi H47 Hstk0 FFS C1; lia
    | clear - Ha Hsp1; unfold T_parse_STK, ESTACK in *; lia
    | intros Hx; destruct (HOC a Hx) as [Hx'|Hx']; clear - Ha Hx' HFceil Hceil Hslo Hstk0 FFS C1; lia ]
  | intros a Ha; apply Hpres4; clear - Ha FFS; lia ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
clear Hch1 RraX RgpX RtpX Ea0X Ea1X Ea2X Rra Rsp Rs0 Z4 Z8 HG4.
(* the bytes above sp after the call *)
assert (HUP4 : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W4) mem4 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. rewrite K1; [apply HUP; exact Ha | lia | unfold T_parse_STK, ESTACK in *; lia | intros Hx; destruct (HOC a Hx); lia]. }
clear HUP K1 K2 K4. rename HUP4 into HUP.
assert (Hq0 : q <> 0) by lia. assert (HF32 : F + 32 <> 0) by lia. assert (HF64 : F + 64 <> 0) by lia.
change (pm_s (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) with (pin_str pl) in Hrc4, Hout4.
pose proof (pm_parse_known q (F + 32) (F + 64) fl (pin_str pl) Hfl (pin_str_no_nul pl) Hq0 HF32 HF64) as Hknw.
pose proof (pm_parse_row_label q (F + 32) (F + 64) fl (pin_str pl)) as Hrl.
destruct (pin_parse_res PM_CAT PM_DP (pm_arg fl 0 q) (pm_arg fl 1 (F + 32)) (pm_arg fl 2 (F + 64)) (pin_str pl)) as [[row lab]|] eqn:Eres.
- (* the pin is accepted: rc = 0, the two cells hold the row and the label *)
  try rewrite Eres in Hrc4; try rewrite Eres in Hout4; try rewrite Eres in Hknw. cbn [parse_rc] in Hrc4, Hknw.
  pose proof Eres as Hsome. unfold pin_parse_res in Hsome. rewrite (pm_parse_live_eq q (F + 32) (F + 64) fl Hfl Hq0 HF32 HF64) in Hsome.
  assert (HBt : Z.testbit fl 1 = false /\ Z.testbit fl 2 = false)
  by (unfold fl_live in Hsome; destruct (Z.testbit fl 0), (Z.testbit fl 1), (Z.testbit fl 2); cbv beta iota delta [negb andb] in Hsome; first [discriminate Hsome | split; reflexivity]).
  destruct HBt as (B1 & B2). clear Hsome.
  assert (Emo : pm_arg fl 1 (F + 32) = F + 32) by (unfold pm_arg; rewrite B1; reflexivity).
  assert (Elb : pm_arg fl 2 (F + 64) = F + 64) by (unfold pm_arg; rewrite B2; reflexivity).
  destruct (Hout4 row lab eq_refl) as (Vrow & Vlab). rewrite Emo in Vrow. rewrite Elb in Vlab. clear Hout4.
  destruct (Hrl row lab Hfl (pin_str_no_nul pl) Hq0 HF32 HF64 eq_refl) as (Erow & Elab). clear Hrl.
  rewrite <- Ewant in Erow. rewrite <- Ewl in Elab.
  assert (Rrow : 0 <= row < 2 ^ 64) by (rewrite Erow, Ewant; apply pm_want_range).
  assert (Rlab : 0 <= lab < 2 ^ 64) by (rewrite Elab, Ewl; apply pm_wlab_range; [lia | rewrite Hlen; lia]).
  assert (Hwne : want <> 0) by (rewrite Ewant; apply Hknw; reflexivity).
  ws_pin HS (10%bv : bv 5) (SLit 0) Hrc4 ltac:(reflexivity).
  add_atom_win HS 735%nat (Z_to_bv 64 row) E735. add_atom_win HS 736%nat (Z_to_bv 64 lab) E736.
  rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
  (* the frame region whole again, with the two cells as chunks [knock A/APgMain2.v:290-335] *)
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs 75%nat in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_region) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) i r HS ltac:(vm_compute; reflexivity)) as HR75; cbn [ms_mem restrict mkst] in HR75;
  lazymatch type of HR75 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region_any Ex _ 75 F cs lo hi wlo whi 120 8%N (SOff 87 0) HR75 B75 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vfl end; clear HR75 end.
  drop_base HS 75%nat.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _
  (YP09.mkRegion (Some 75%nat) 0 128 0 128 [YP09.mkChunk 32 (CVal 8 (SOff 735 0)); YP09.mkChunk 64 (CVal 8 (SOff 736 0)); YP09.mkChunk 120 (CVal 8 (SOff 87 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
  rewrite B75; split; [lia|]; split; [lia|]; split;
  [ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
  | apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 32 8 _ row); [rewrite sv_denot_SOff0; exact E735 | zside | zside | exact Vrow]|];
    apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 64 8 _ lab); [rewrite sv_denot_SOff0; exact E736 | zside | zside | exact Vlab]|];
    apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 120 8 _ (bv_unsigned (sv_denot Ev (SOff 87 0)) mod 2 ^ (8 * Z.of_N 8)));
      [ let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (sv_denot Ev (SOff 87 0))) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq;
        rewrite (Z.mod_small _ _ Hq); symmetry; apply Z_to_bv_bv_unsigned
      | apply Z.mod_pos_bound; cbn; lia | zside | exact Vfl ]|];
    apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite B75; evalE AG;
  clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c;
  unfold SB, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  clear Vfl. move_region HS 1%nat.
  (* 0x80904-0x8090c: s6 = rc, a1 = want, jal check_known *)
  aj_run_to_sh tfibtbl_lib_ok HS HJ4 0x80af8.
  1: awrRT AG fpos F EFA4.
  upd_aboveW HUP HFr AG. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
  (* 0x8090c jal check_known, through tpin_check_known_specX at the call-site lemma pin_known_site *)
  pm_regs (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) HS RT_known_ra Rra5 Rsp5 Rs05 Rgp5 Rtp5 AG E70 E2 EE.
  reg_is HS (10%bv : bv 5) (w64 0) Ra05 ltac:(reflexivity).
  reg_is HS (11%bv : bv 5) (w64 want) Ra15 ltac:(rewrite sv_denot_SOff0; exact E104).
  lazymatch type of Rsp5 with getr ?rg 2 = _ =>
    assert (EspX5 : spZ rg = sp1) by (unfold spZ; rewrite Rsp5; apply unsigned_lit_small; lia);
    assert (Es0X5 : s0Z rg = spZ regs) by (unfold s0Z, spZ; rewrite Rs05; reflexivity) end.
  pm_chain (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) HS HJ4 HUP Hch5 AG Usp EE Hch Qtop64 Qra Qs0 Hra4 Hceil Hslo Hstk0 FFS Qal8 Hsp1.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
  destruct (pin_known_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly4 S4 W4 (ms_mem msX) mdX (k + EV_parse) (ms_regs msX) 0 want
    HBASE0 HJ4 ltac:(unfold EV_parse; lia) Rra5 Rgp5 Rtp5 EspX5 ltac:(rewrite EspX5, Es0X5; exact Hch5) Ra05 Ra15 (or_introl eq_refl)
    ltac:(rewrite Ewant; apply pm_want_range) (conj (fun _ => Hwne) (fun _ => eq_refl))) as (KIT5 & PRE5);
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
  eapply SRr_bind;
  [ eapply (TKNOWN LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly4 S4 W4 (ms_mem msX) mdX (k + EV_parse) (ms_regs msX)
    (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) KIT5 PRE5) | ] end.
  clear KIT5 PRE5 Hch5 Ra05 Ra15 Rgp5 Rtp5 Rsp5 Rs05 Es0X5.
  cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hfrs5 & HPerm5 & HIO5 & HMLE5 & K5 & _).
  rewrite Rra5. rewrite EspX5 in K5. clear Rra5 EspX5.
  pose proof (mle_station MT S S4 S5 (acc + 0) 0 MTL HMLE4c HMLE5) as HMLE5c.
  pose proof (proj1 HJ5) as HAR5.
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
  assert (Hfrs5' : frames S5 = [(1, fpos)]) by (rewrite Hfrs5; exact Hfrs4').
  assert (Hfin5 : In (1, fpos) (frames S5)) by (rewrite Hfrs5'; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & _).
  change (fs_frame_bytes 1) with 128 in HFpres5. rewrite !EFA5 in HFpres5. fold F in HFpres5.
  pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
  assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; rewrite K5; [apply HUP; exact Ha | lia | unfold T_leaf_STK; lia | tauto]).
  clear HUP. rename HUP5 into HUP.
  reseatL HS HJ5 HP5 [0; 1; 2]%nat AG
  ltac:(idtac; first
  [ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K5; [clear - Ha HF8lo HF8hi; unfold SB in *; lia | clear - Ha HF8hi Hsp1 Hceil Hslo Hstk0 FFS C1; unfold SB, T_leaf_STK in *; lia | tauto]
    | intros a Ha; exfalso; clear - Ha; lia ] end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K5; [clear - Ha HF4096 HFceil C1; lia | clear - Ha HFceil Hsp1 Hceil Hslo Hstk0 FFS C1; unfold T_leaf_STK in *; lia | tauto]
    | intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha; lia))) ] end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K5; [clear - Ha Hshi H47 Hceil Hslo Hstk0 FFS C1; lia | clear - Ha Hsp1; unfold T_leaf_STK in *; lia | tauto]
    | intros a Ha; apply Hpres5; clear - Ha FFS; lia ] end
  | match goal with |- ?g => idtac "KEPTFAIL" g end ]).
  relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
  clear K5 HFpres5 Hpres5.
  (* 0x80910-0x8091c: rc = 0, a0 = the model cell, a1 = want, jal check_row *)
  aj_run_to_sh tfibtbl_lib_ok HS HJ5 0x80b24.
  1: awrRT AG fpos F EFA5.
  upd_aboveW HUP HFr AG. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
  (* 0x8091c jal check_row, through tpin_check_row_specX at the call-site lemma pin_row_chk_site *)
  pm_regs (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) HS RT_chkrow_ra Rra6 Rsp6 Rs06 Rgp6 Rtp6 AG E70 E2 EE.
  reg_is HS (10%bv : bv 5) (w64 row) Ra06 ltac:(rewrite sv_denot_SOff0; exact E735).
  reg_is HS (11%bv : bv 5) (w64 want) Ra16 ltac:(rewrite sv_denot_SOff0; exact E104).
  lazymatch type of Rsp6 with getr ?rg 2 = _ =>
    assert (EspX6 : spZ rg = sp1) by (unfold spZ; rewrite Rsp6; apply unsigned_lit_small; lia);
    assert (Es0X6 : s0Z rg = spZ regs) by (unfold s0Z, spZ; rewrite Rs06; reflexivity) end.
  pm_chain (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) HS HJ5 HUP Hch6 AG Usp EE Hch Qtop64 Qra Qs0 Hra4 Hceil Hslo Hstk0 FFS Qal8 Hsp1.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
  destruct (pin_row_chk_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly5 S5 W5 (ms_mem msX) mdX (k + EV_parse + EV_leaf) (ms_regs msX) row want
    HBASE0 HJ5 ltac:(unfold EV_parse, EV_leaf; lia) Rra6 Rgp6 Rtp6 EspX6 ltac:(rewrite EspX6, Es0X6; exact Hch6) Ra06 Ra16 Erow) as (KIT6 & PRE6);
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
  eapply SRr_bind;
  [ eapply (TCROW LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly5 S5 W5 (ms_mem msX) mdX (k + EV_parse + EV_leaf) (ms_regs msX)
    (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) KIT6 PRE6) | ] end.
  clear KIT6 PRE6 Hch6 Ra06 Ra16 Rgp6 Rtp6 Rsp6 Rs06 Es0X6.
  cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hfrs6 & HPerm6 & HIO6 & HMLE6 & K6 & _).
  rewrite Rra6. rewrite EspX6 in K6. clear Rra6 EspX6.
  pose proof (mle_station MT S S5 S6 (acc + 0 + 0) 0 MTL HMLE5c HMLE6) as HMLE6c.
  pose proof (proj1 HJ6) as HAR6.
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly6 HAR (proj1 (proj2 HJ6))) as (_ & EFA6 & _).
  assert (Hfrs6' : frames S6 = [(1, fpos)]) by (rewrite Hfrs6; exact Hfrs5').
  assert (Hfin6 : In (1, fpos) (frames S6)) by (rewrite Hfrs6'; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR6 Hfin6) as (_ & _ & HFpres6 & _).
  change (fs_frame_bytes 1) with 128 in HFpres6. rewrite !EFA6 in HFpres6. fold F in HFpres6.
  pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _).
  assert (HUP6 : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; rewrite K6; [apply HUP; exact Ha | lia | unfold T_leaf_STK; lia | tauto]).
  clear HUP. rename HUP6 into HUP.
  reseatL HS HJ6 HP6 [0; 1; 2]%nat AG
  ltac:(idtac; first
  [ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K6; [clear - Ha HF8lo HF8hi; unfold SB in *; lia | clear - Ha HF8hi Hsp1 Hceil Hslo Hstk0 FFS C1; unfold SB, T_leaf_STK in *; lia | tauto]
    | intros a Ha; exfalso; clear - Ha; lia ] end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K6; [clear - Ha HF4096 HFceil C1; lia | clear - Ha HFceil Hsp1 Hceil Hslo Hstk0 FFS C1; unfold T_leaf_STK in *; lia | tauto]
    | intros a Ha; apply (proj1 (HFpres6 a ltac:(clear - Ha; lia))) ] end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K6; [clear - Ha Hshi H47 Hceil Hslo Hstk0 FFS C1; lia | clear - Ha Hsp1; unfold T_leaf_STK in *; lia | tauto]
    | intros a Ha; apply Hpres6; clear - Ha FFS; lia ] end
  | match goal with |- ?g => idtac "KEPTFAIL" g end ]).
  relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
  clear K6 HFpres6 Hpres6.
  (* 0x80920-0x80928: a0 = the label cell, a1 = want_label, jal check_label *)
  aj_run_to_sh tfibtbl_lib_ok HS HJ6 0x80b48.
  1: awrRT AG fpos F EFA6.
  upd_aboveW HUP HFr AG. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
  (* 0x80928 jal check_label, through tpin_check_label_specX at the call-site lemma pin_label_site *)
  pm_regs (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) HS RT_label_ra Rra7 Rsp7 Rs07 Rgp7 Rtp7 AG E70 E2 EE.
  reg_is HS (10%bv : bv 5) (w64 lab) Ra07 ltac:(rewrite sv_denot_SOff0; exact E736).
  reg_is HS (11%bv : bv 5) (w64 wl) Ra17 ltac:(rewrite sv_denot_SOff0; exact E105).
  lazymatch type of Rsp7 with getr ?rg 2 = _ =>
    assert (EspX7 : spZ rg = sp1) by (unfold spZ; rewrite Rsp7; apply unsigned_lit_small; lia);
    assert (Es0X7 : s0Z rg = spZ regs) by (unfold s0Z, spZ; rewrite Rs07; reflexivity) end.
  pm_chain (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) HS HJ6 HUP Hch7 AG Usp EE Hch Qtop64 Qra Qs0 Hra4 Hceil Hslo Hstk0 FFS Qal8 Hsp1.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
  destruct (pin_label_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly6 S6 W6 (ms_mem msX) mdX (k + EV_parse + EV_leaf + EV_leaf) (ms_regs msX) lab wl
    HBASE0 HJ6 ltac:(unfold EV_parse, EV_leaf; lia) Rra7 Rgp7 Rtp7 EspX7 ltac:(rewrite EspX7, Es0X7; exact Hch7) Ra07 Ra17 Elab) as (KIT7 & PRE7);
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
  eapply SRr_bind;
  [ eapply (TCLAB LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly6 S6 W6 (ms_mem msX) mdX (k + EV_parse + EV_leaf + EV_leaf) (ms_regs msX)
    (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) KIT7 PRE7) | ] end.
  clear KIT7 PRE7 Hch7 Ra07 Ra17 Rgp7 Rtp7 Rsp7 Rs07 Es0X7.
  cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Hfrs7 & HPerm7 & HIO7 & HMLE7 & K7 & _).
  rewrite Rra7. rewrite EspX7 in K7. clear Rra7 EspX7.
  pose proof (mle_station MT S S6 S7 (acc + 0 + 0 + 0) 0 MTL HMLE6c HMLE7) as HMLE7c.
  pose proof (proj1 HJ7) as HAR7.
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly7 HAR (proj1 (proj2 HJ7))) as (_ & EFA7 & _).
  assert (Hfrs7' : frames S7 = [(1, fpos)]) by (rewrite Hfrs7; exact Hfrs6').
  assert (Hfin7 : In (1, fpos) (frames S7)) by (rewrite Hfrs7'; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR7 Hfin7) as (_ & _ & HFpres7 & _).
  change (fs_frame_bytes 1) with 128 in HFpres7. rewrite !EFA7 in HFpres7. fold F in HFpres7.
  pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres7 & _).
  reseatL HS HJ7 HP7 [0; 1; 2]%nat AG
  ltac:(idtac; first
  [ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K7; [clear - Ha HF8lo HF8hi; unfold SB in *; lia | clear - Ha HF8hi Hsp1 Hceil Hslo Hstk0 FFS C1; unfold SB, T_leaf_STK in *; lia | tauto]
    | intros a Ha; exfalso; clear - Ha; lia ] end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K7; [clear - Ha HF4096 HFceil C1; lia | clear - Ha HFceil Hsp1 Hceil Hslo Hstk0 FFS C1; unfold T_leaf_STK in *; lia | tauto]
    | intros a Ha; apply (proj1 (HFpres7 a ltac:(clear - Ha; lia))) ] end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K7; [clear - Ha Hshi H47 Hceil Hslo Hstk0 FFS C1; lia | clear - Ha Hsp1; unfold T_leaf_STK in *; lia | tauto]
    | intros a Ha; apply Hpres7; clear - Ha FFS; lia ] end
  | match goal with |- ?g => idtac "KEPTFAIL" g end ]).
  relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
  clear K7 HFpres7 Hpres7.
  (* 0x8092c: the join into ss_F (a0 = q, then free) *)
  ra_join_win HS ss_F 860%nat pm_F_deads_bv ltac:(idtac).
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv.
  rt_hand (pm_S4F B MT MTL FP POST FP0 TL LAWS AFREE4 RX) HS.
  unfold INV_F. cbn [c_ly c_S c_pl c_T].
  split; [unfold EV_parse, EV_leaf; lia|].
  split; [lia|].
  exists q. split; [exact E100|].
  eapply Permutation_trans; [exact HPerm7|]. eapply Permutation_trans; [exact HPerm6|].
  eapply Permutation_trans; [exact HPerm5|]. eapply Permutation_trans; [exact HPerm4|]. exact Eab3.
- (* the pin is refused: rc = -1, and want = 0 *)
  try rewrite Eres in Hrc4; try rewrite Eres in Hknw. cbn [parse_rc] in Hrc4, Hknw. clear Hout4 Hrl.
  assert (Hw0 : want = 0) by (destruct (Z.eq_dec want 0) as [Ew|Ew]; [exact Ew | exfalso; rewrite Ewant in Ew; apply Hknw in Ew; discriminate Ew]).
  ws_pin HS (10%bv : bv 5) (SLit (-1)) Hrc4 ltac:(reflexivity).
  rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
  (* the frame region whole again, without the cells *)
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let i := idx_of_base rs 75%nat in let i := eval vm_compute in i in
  let r := eval vm_compute in (nth i rs got_region) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W4) msX) i r HS ltac:(vm_compute; reflexivity)) as HR75; cbn [ms_mem restrict mkst] in HR75;
  lazymatch type of HR75 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region_any Ex _ 75 F cs lo hi wlo whi 120 8%N (SOff 87 0) HR75 B75 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vfl end; clear HR75 end.
  drop_base HS 75%nat.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _
  (YP09.mkRegion (Some 75%nat) 0 128 0 128 [YP09.mkChunk 120 (CVal 8 (SOff 87 0))]) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
  rewrite B75; split; [lia|]; split; [lia|]; split;
  [ intros o Ho; apply (apresent_writable tfibsegs); apply (proj1 (HFpres4 (F + o) ltac:(lia)))
  | apply Forall_cons; [apply (chunk_ok_val tfibsegs Ev _ F 120 8 _ (bv_unsigned (sv_denot Ev (SOff 87 0)) mod 2 ^ (8 * Z.of_N 8)));
      [ let Hq := fresh "Hq" in pose proof (bv_unsigned_in_range 64 (sv_denot Ev (SOff 87 0))) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq;
        rewrite (Z.mod_small _ _ Hq); symmetry; apply Z_to_bv_bv_unsigned
      | apply Z.mod_pos_bound; cbn; lia | zside | exact Vfl ]|];
    apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite B75; evalE AG;
  clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c;
  unfold SB, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  clear Vfl. move_region HS 1%nat.
  (* 0x80904-0x8090c: s6 = rc, a1 = want, jal check_known *)
  aj_run_to_sh tfibtbl_lib_ok HS HJ4 0x80af8.
  1: awrRT AG fpos F EFA4.
  upd_aboveW HUP HFr AG. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
  (* 0x8090c jal check_known, through tpin_check_known_specX at the call-site lemma pin_known_site *)
  pm_regs (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) HS RT_known_ra Rra5 Rsp5 Rs05 Rgp5 Rtp5 AG E70 E2 EE.
  reg_is HS (10%bv : bv 5) (w64 (-1)) Ra05 ltac:(reflexivity).
  reg_is HS (11%bv : bv 5) (w64 want) Ra15 ltac:(rewrite sv_denot_SOff0; exact E104).
  lazymatch type of Rsp5 with getr ?rg 2 = _ =>
    assert (EspX5 : spZ rg = sp1) by (unfold spZ; rewrite Rsp5; apply unsigned_lit_small; lia);
    assert (Es0X5 : s0Z rg = spZ regs) by (unfold s0Z, spZ; rewrite Rs05; reflexivity) end.
  pm_chain (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) HS HJ4 HUP Hch5 AG Usp EE Hch Qtop64 Qra Qs0 Hra4 Hceil Hslo Hstk0 FFS Qal8 Hsp1.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
  destruct (pin_known_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly4 S4 W4 (ms_mem msX) mdX (k + EV_parse) (ms_regs msX) (-1) want
    HBASE0 HJ4 ltac:(unfold EV_parse; lia) Rra5 Rgp5 Rtp5 EspX5 ltac:(rewrite EspX5, Es0X5; exact Hch5) Ra05 Ra15 (or_intror eq_refl)
    ltac:(rewrite Ewant; apply pm_want_range) ltac:(split; intros Hx; [discriminate Hx | exfalso; exact (Hx Hw0)])) as (KIT5 & PRE5);
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
  eapply SRr_bind;
  [ eapply (TKNOWN LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly4 S4 W4 (ms_mem msX) mdX (k + EV_parse) (ms_regs msX)
    (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) KIT5 PRE5) | ] end.
  clear KIT5 PRE5 Hch5 Ra05 Ra15 Rgp5 Rtp5 Rsp5 Rs05 Es0X5.
  cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hfrs5 & HPerm5 & HIO5 & HMLE5 & K5 & _).
  rewrite Rra5. rewrite EspX5 in K5. clear Rra5 EspX5.
  pose proof (mle_station MT S S4 S5 (acc + 0) 0 MTL HMLE4c HMLE5) as HMLE5c.
  pose proof (proj1 HJ5) as HAR5.
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR (proj1 (proj2 HJ5))) as (_ & EFA5 & _).
  assert (Hfrs5' : frames S5 = [(1, fpos)]) by (rewrite Hfrs5; exact Hfrs4').
  assert (Hfin5 : In (1, fpos) (frames S5)) by (rewrite Hfrs5'; left; reflexivity).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR5 Hfin5) as (_ & _ & HFpres5 & _).
  change (fs_frame_bytes 1) with 128 in HFpres5. rewrite !EFA5 in HFpres5. fold F in HFpres5.
  pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
  reseatL HS HJ5 HP5 [0; 1; 2]%nat AG
  ltac:(idtac; first
  [ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 88%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K5; [clear - Ha HF8lo HF8hi; unfold SB in *; lia | clear - Ha HF8hi Hsp1 Hceil Hslo Hstk0 FFS C1; unfold SB, T_leaf_STK in *; lia | tauto]
    | intros a Ha; exfalso; clear - Ha; lia ] end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 75%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K5; [clear - Ha HF4096 HFceil C1; lia | clear - Ha HFceil Hsp1 Hceil Hslo Hstk0 FFS C1; unfold T_leaf_STK in *; lia | tauto]
    | intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha; lia))) ] end
  | lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
    eapply pm_region_kept_eq; [ evalE AG
    | intros a Ha; apply K5; [clear - Ha Hshi H47 Hceil Hslo Hstk0 FFS C1; lia | clear - Ha Hsp1; unfold T_leaf_STK in *; lia | tauto]
    | intros a Ha; apply Hpres5; clear - Ha FFS; lia ] end
  | match goal with |- ?g => idtac "KEPTFAIL" g end ]).
  relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
  clear K5 HFpres5 Hpres5.
  (* 0x80944 bnez s6 (rc = -1): taken, to 0x80960 *)
  aj_run_to_sh tfibtbl_lib_ok HS HJ5 0x80960.
  1: awrRT AG fpos F EFA5.
  clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n. rebv HS E70 RF B70 B75.
  (* 0x8092c: the join into ss_F (a0 = q, then free) *)
  ra_join_win HS ss_F 860%nat pm_F_deads_bv ltac:(idtac).
  let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv.
  rt_hand (pm_S4F B MT MTL FP POST FP0 TL LAWS AFREE4 RX) HS.
  unfold INV_F. cbn [c_ly c_S c_pl c_T].
  split; [unfold EV_parse, EV_leaf; lia|].
  split; [lia|].
  exists q. split; [exact E100|].
  eapply Permutation_trans; [exact HPerm5|]. eapply Permutation_trans; [exact HPerm4|]. exact Eab3.
Qed.
End e.
End c.
