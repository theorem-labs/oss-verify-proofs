(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v (a walk) and ACa2.v (a class-1 side-stack frame): tnumber_spec of lib/A/Prog/number_c.v, from number's entry (0x8e430) through __asan_stack_malloc_0 and strtol to strtol's return, then numberB.v's n_segB. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberA.v, with its module paths, module names and numbers changed; 1350 of its 1544 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: refuse's walk on reac-pw/fuzz_segconf's ASan image A (fuzz_segconf.asan,
   refuse at 0x88da4), in the form of plugin-hostd/fuzz_command's lib/A/Prog/numberA.v at origin/ossv/recipes
   501c0d516c69 (number: a class-0 side-stack frame released inline): the entry to the call of
   __asan_stack_malloc_0 (0x88e30), the frame and its poisoning, the inline checks of c->refused, c->n_refusals
   and c->reading[0], and the branches up to the snprintf calls (0x88f5c, 0x88f74) and the n_refusals >= 8 exit
   (0x88efc -> 0x88fc4). The refuse walk, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c refuse_e.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require refuse_f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require refuse_r.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require refuse_pft PaFx SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtDefs RtPFShared RtPFCmd RtFormat RtPFSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* numberB.v's n_val1: a byte through the reader as a 1-byte chunk *)
Lemma r_val1 : forall {fx : YK11.FPState} segs H (m : word -> option byte) a v,
aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros fx segs H m a v Hv j Hj. replace j with 0%nat by lia. rewrite Z.add_0_r.
destruct (aview_byte segs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 8 b) as R8. change (bv_modulus 8) with 256 in R8.
unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
(* numberB.v's n_chunk4_aval and n_region_aval4 (plugin-hostd/fuzz_command lib/A/Prog/numberB.v:75-99 at
   origin/ossv/recipes 501c0d516c69), with SegRep's aval_mem written out: a 4-byte chunk of a value v (sw stores the
   low 4 bytes of the register) holds le_byte v 4 k in its 4 bytes *)
Lemma r_chunk4_aval : forall {fx : YK11.FPState} segs E H (m : word -> option byte) base off e (v : Z),
YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
forall k, (k < 4)%nat -> aview segs H m (base + off + Z.of_nat k) = Some (YG0f.le_byte v 4 k).
Proof.
intros fx segs E H m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len; cbn [YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite He, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64).
unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros j Hj.
destruct (Z_lt_le_dec j 8) as [Hj8|Hj8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma r_region_aval4 : forall {fx : YK11.FPState} segs E H (m : word -> option byte) n b cs lo hi wlo whi od e v,
region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
forall k, (k < 4)%nat -> aview segs H m (b + od + Z.of_nat k) = Some (YG0f.le_byte v 4 k).
Proof.
intros fx segs E H m n b cs lo hi wlo whi od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (r_chunk4_aval segs E H m b od e v Hck He).
Qed.
(* the value c->refused++ stores (lw, addi 1, sw at 0x88ee4): sext32 of the loaded word plus 1, in the form
   refuse_f.rf_sw_inc reads *)
Lemma r_inc_denot : forall E n r, ew E n = Z_to_bv 64 r -> 0 <= r < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)) =
Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (r + 2 ^ 31) (2 ^ 32 - 1) - 2 ^ 31 + 1))).
Proof.
intros E n r He Hr. rewrite Z_to_bv_bv_unsigned. cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (zext_low_sound true 32 r), zalu64_sound. apply Z_to_bv64_eq_mod.
change (2 ^ 32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia.
unfold zalu64, zext_low, zalu_raw, zcanon, M64. cbv beta iota zeta.
unfold bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (2 ^ Z.of_N 32) with (2 ^ 32).
try rewrite (Z.mod_small r (2 ^ 64)) by lia.
try rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
rewrite ?Zmod_mod.
Z.div_mod_to_equations. lia.
Qed.
(* The canonical state of the n < 8 body after the k test (image A 0x88f80, listing offset 16968), which all four
   where / line leaves reach: the registers and regions the address snprintf left, the atoms' range facts and the
   two aliases; the branch conditions of the n < 8 test and the k test (each leaf drops its where / line ones) *)
Definition ss_tl : sstate := Eval vm_compute in
mkSS 16968
  [SLit 0; SOff 1100 0; SOff 33 0; SOff 3 0; SOff 4 0; SOff 1101 0; SOff 1102 0; SOff 1103 0;
   SOff 2 (-48); SOff 33 0; SOff 1104 0; SLit 199; SOff 1106 0; SOff 1107 0; SOff 1108 0; SOff 1109 0;
   SOff 1110 0; SOff 1111 0; SOff 1028 0; SOff 12 0; SOff 10 13512; SOff 11 0;
   SAlu ALU_ADD (SOff 10 11912) (SMd M_MUL (SOff 1042 0) (SLit 200));
   SOff 1028 0; SOff 1041 0; SOff 32 0;
   SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 13512) (SLit 3)) (SOff 32 0);
   SOff 27 0; SOff 1112 0; SOff 1113 0; SOff 1114 0; SOff 1115 0]
  [ YP09.mkRegion (Some 10%nat) 13512 13520 13516 13516
      [YP09.mkChunk 13516 (CVal 4 (SAlu ALU_ADD (SExt true 32 (SOff 1043 0)) (SLit 1)));
       YP09.mkChunk 13512 (CVal 4 (SOff 1042 0))];
    YP09.mkRegion (Some 1041%nat) 0 8 0 0
      [YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601));
       YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601));
       YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551603));
       YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608))];
    YP09.mkRegion (Some 1028%nat) 0 32 0 0
      [YP09.mkChunk 16 (CVal 8 (SOff 311 0)); YP09.mkChunk 8 (CVal 8 (SOff 310 0));
       YP09.mkChunk 0 (CVal 8 (SLit 1102416563))];
    YP09.mkRegion (Some 1028%nat) 32 40 32 32 [];
    YP09.mkRegion (Some 1028%nat) 40 64 40 40 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))];
    YP09.mkRegion (Some 2%nat) (-144) 0 (-144) (-144)
      [YP09.mkChunk (-16) (CVal 8 (SOff 16 0)); YP09.mkChunk (-24) (CVal 8 (SOff 15 0));
       YP09.mkChunk (-32) (CVal 8 (SOff 14 0)); YP09.mkChunk (-40) (CVal 8 (SOff 13 0));
       YP09.mkChunk (-8) (CVal 8 (SOff 17 0)); YP09.mkChunk (-144) (CVal 8 (SOff 26 0));
       YP09.mkChunk (-136) (CVal 8 (SOff 25 0)); YP09.mkChunk (-128) (CVal 8 (SOff 24 0));
       YP09.mkChunk (-120) (CVal 8 (SOff 23 0)); YP09.mkChunk (-112) (CVal 8 (SOff 22 0));
       YP09.mkChunk (-104) (CVal 8 (SOff 21 0)); YP09.mkChunk (-96) (CVal 8 (SOff 20 0));
       YP09.mkChunk (-88) (CVal 8 (SOff 19 0)); YP09.mkChunk (-80) (CVal 8 (SOff 18 0));
       YP09.mkChunk (-72) (CVal 8 (SOff 9 0)); YP09.mkChunk (-64) (CVal 8 (SOff 8 0));
       YP09.mkChunk (-56) (CVal 8 (SOff 1 0))] ]
  None
  (mkFacts
    [(1044%nat, mkAF 0 255 0); (1043%nat, mkAF 0 4294967294 0); (1042%nat, mkAF 0 8 0);
     (1041%nat, mkAF 2147451392 17594333495296 3); (1040%nat, mkAF 4096 140737488355328 0);
     (1028%nat, mkAF 4096 140737488355328 6); (2%nat, mkAF 70368744177664 140737488355328 4);
     (33%nat, mkAF 70368744177664 140737488355328 5); (32%nat, mkAF 2147450880 2147450880 0);
     (34%nat, mkAF 65536 6295552 2); (10%nat, mkAF 4096 140737488338712 4); (11%nat, mkAF 0 2147483647 0)]
    [ {| ac_c := neg_bc BC_LTU; ac_a := SLit 199; ac_b := SOff 1104 0 |};
      {| ac_c := BC_GE; ac_a := SLit 7; ac_b := SOff 1042 0 |} ]
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0), SOff 1041 0);
     (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32)), SOff 33 0)]).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis SM0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
(* the n < 8 body: the snprintf row at its trampoline, the vsnprintf row (lib/A/Rt/RtPFSeg.v), the
   listing's object addresses (the three literals refuse forms), and the stack-protector cells at an AR state
   (SSPX: the __asan_stack_malloc_0 call keeps an image byte only outside as_owned_static, and whether the GOT
   word gotwA and the guard guardA are owned statics is a record fact) *)
Hypothesis SNP : forall fx0 : YK11.FPState, @RtFormat.asnprintf_realizes fx0 rc SEGS B
  (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis VSNP : forall fx0 : YK11.FPState, @RtPFSeg.seg_avsnprintf_realizes fx0 rc SEGS B
  RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
  (SIGMA SS___interceptor_trampoline_vsnprintf) gotwA guardA.
Hypothesis OBJ : SegObj.seg_val_objs (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma STK_values_r : STK_refuse = 12464. Proof. reflexivity. Qed.
(* every writable window of a run's state is a byte the journal allows: the real frame (atom 2 at offset 0, atom
   33 the realigned sp), the side-stack frame and its shadow (INF), c's fields in the footprint (INFP) *)
Ltac r_awr U2 U33 U1028 U1041 U10 INF INFP sp0 F c :=
lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own => let rs' := eval vm_compute in rs in change rs with rs' end;
repeat first
[ apply awr_ok_nil
| (apply awr_ok_cons_ro; [cbn; lia|])
| (eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; rewrite ?STK_values_r; lia | cbn; lia |])
| (eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (rsp1 sp0 - sp0)); [reflexivity | rewrite U33; lia | cbn; rewrite ?STK_values_r; lia | cbn; lia |])
| (eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 1028%nat F); [reflexivity | exact U1028 | intros ?a ?Ha; cbn [YP09.r_wlo YP09.r_whi] in *; right; right; right; left; apply INF; lia |])
| (eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 1041%nat (SB + F / 8)); [reflexivity | exact U1041 | intros ?a ?Ha; cbn [YP09.r_wlo YP09.r_whi] in *; right; right; right; left; apply INF; lia |])
| (eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 10%nat c); [reflexivity | exact U10 | intros ?a ?Ha; cbn [YP09.r_wlo YP09.r_whi] in *; apply INFP; lia |]) ].
Theorem r_walk : refuse_contract SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Proof.
unfold refuse_contract.
intros ly S W regs mem md ch c line fp ln rcs f args HPRE HROD H10 Hc64 H11 Hl64 H12 Hf64 HRP HROOM HEV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (LT : ly_stk_lo ly mod 4096 = 0 /\ ly_stk_hi ly mod 4096 = 0 /\ kHighMemBeg <= ly_stk_lo ly).
{ pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & L1 & L2 & L3).
  unfold page_aligned in L1, L2. exact (conj L1 (conj L2 L3)). }
destruct LT as (Llo & Lhi & Lhm).
assert (FFS : STK_refuse = 12464) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HRP as (Hc0 & Hc16 & HRC & HHEAP & HCADDR & Hrf32 & Hln & Hline & Hf & Hkinds & Hfp0 & Hfplit & HFLIT &
  HVA & HVLOC & HFRM & HSSP & HLITS).
subst line.
(* the block c lies in *)
destruct HHEAP as (pb & kb & Hpbin & Hpb1 & Hpb2).
destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hpbin) as (Hpb16 & Hpb4096 & Hpbceil & Hpbapp & Hpbpres & _ & Hkb).
pose proof (req_size_pos0 kb ltac:(lia)) as [Hkb0 Hkbr].
unfold seg_spec.SEG_C_SIZE in Hpb2.
assert (Hcb : 4096 <= c <= 2 ^ 47 - 16616) by lia.
pose proof (r_entry B LAWS TL TLF STK_refuse W ly S regs mem md ch c ln HPRE ltac:(rewrite FFS; lia) H10 H11
  Hcb Hc16 ltac:(lia)) as HS.
pose proof (ajournal_init SEGS B STK_refuse (refuse_W c rcs) ly S W regs mem md ch HPRE) as HJ.
set (E := Eimg (Ereg regs (r_extra (spZ regs) (as_uar_cell B)))) in HS. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 (rsp1 (spZ regs))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
set (sp0 := spZ regs) in *.
destruct (rsp1_facts sp0 Hal16) as (Hs1al & Hs1).
assert (Hs1b : sp0 - 176 <= rsp1 sp0 <= sp0 - 160) by lia.
lazymatch type of Hs1 with ?T => change (rnam T) in Hs1 end.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (Usp1 : bv_unsigned (ew E 33) = rsp1 sp0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor.
unfold cfg_at. change (w64 (BASE + AF_refuse)) with (Z_to_bv 64 (BASE + AF_refuse)).
(* R1: from the entry to the call of __asan_stack_malloc_0 (0x88e30): the prologue, the variadic spills, the shadow
   base and the use-after-return flag (the record's constant 1: the side-stack branch) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ unfold ss_r0, r_regions0, r_stk_lo, r_stk_hi, r_stk_s1; cbn [ss_mem].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; rewrite ?FFS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; rewrite ?FFS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (rsp1 sp0 - sp0)); [reflexivity | rewrite Usp1; lia | cbn; rewrite ?FFS; lia | cbn; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the entry run writes its stack slots only *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 176 <= a < sp0) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Usp1 in Hrr; clear - Hrr Hs1b; lia |]);
  destruct Hin)) as UNa.
clear HF HFr. rename HG into HGa.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
pose proof (palf_sm B TLF 0 ltac:(clear; cbn; tauto)) as SM0e. change (cs_stack_malloc 0) with SS___asan_stack_malloc_0 in SM0e.
rewrite SM0e.
pose proof (count_cid_le_length 0 (frames S)) as Hcnt.
unfold sa_room in HROOM.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 (SM0 fx) ltac:(lia) W (ms_regs msX) (ms_mem msX) STK_refuse sp0 (refuse_W c rcs) ly S W mem md [] ly S _ 0 (rsp1 sp0 - sp0) _ HJ) end.
- (unfold spZ; rewrite R2, E33, unsigned_lit_small by lia; lia).
- (unfold rnam in Hs1; destruct Hs1 as [Hq|Hq]; rewrite Hq; [replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity).
- (lia). - (rewrite FFS, Hes; lia).
- (rewrite R3, E3; exact Hgp). - (rewrite R4, E4; exact Htp).
- (exact R1). - (apply ret_ok_codeptr_v; [lia | reflexivity]).
- (change (fs_frames 0) with 16384; lia). }
cbv beta. clear R2 R3 R4 R1 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJc & (fS2 & ES2)).
pose proof (proj1 HJ) as HAR1. pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & Kuar1 & Kgot1 & Kguar1).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & Kuar2 & Kgot2 & Kguar2).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot1, Kgot2. rewrite (pal_cell B TL) in Kcell1, Kcell2. rewrite (palf_got_uar B TLF) in Kguar1, Kguar2.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E34 : ew E 34 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
pose proof (palf_uar_img B TLF) as Huar. unfold kImgEnd in Huar.
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2;3;4;5;6]%nat HS2.
match type of HS2 with ?A -> _ => assert (HQ : A); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | rewrite FFS; lia | lia | lia | lia].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | rewrite FFS; lia | lia | lia | lia].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp1 | lia | rewrite FFS; lia | lia | lia | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
[exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kguar1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kguar2) | lia].
- apply (region_kept_val_at E _ _ 34 (as_uar_cell B) 4 1);
[rewrite E34; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar2) | lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
(* the frame of class 0 the call returned, its flag cell and its shadow *)
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg.
destruct (frame_al64 SEGS B ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFal32, HFapp, HFpres, HFSpres, HF4096, HFceil, HFimg, HF64, HFLpres, HFLown, HFLrng, Hz, Hflag.
set (Ev1 := YN3v.havoc E 1024 (map (getr regs2) CLOB)) in HS.
assert (AG1 : forall n, (n < 1024)%nat -> ew Ev1 n = ew E n) by (intros n Hn; subst Ev1; apply ew_havoc_old; exact Hn).
assert (E1028 : ew Ev1 1028 = Z_to_bv 64 F) by (subst Ev1; change 1028%nat with (1024 + 4)%nat; rewrite (ew_havoc_new E 1024 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map CLOB]; exact Ha0).
assert (HEI1 : img_env VAL A_LIM Ev1) by (subst Ev1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
pose proof (st_ok_pi_havoc_hi 1040 Ev1 _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS; rename HS3 into HS.
set (Ev2 := YN3v.havoc Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) in HS.
assert (AG2 : forall n, (n < 1024)%nat -> ew Ev2 n = ew E n) by (intros n Hn; subst Ev2; rewrite ew_havoc_old by lia; apply AG1; exact Hn).
assert (E2_1028 : ew Ev2 1028 = Z_to_bv 64 F) by (subst Ev2; rewrite ew_havoc_old by lia; exact E1028).
assert (E2_1040 : ew Ev2 1040 = Z_to_bv 64 FL) by (subst Ev2; exact (ew_havoc_new Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2_1041 : ew Ev2 1041 = Z_to_bv 64 (SB + F / 8)) by (subst Ev2; exact (ew_havoc_new Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env VAL A_LIM Ev2) by (subst Ev2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U2 : bv_unsigned (ew Ev2 2) = sp0) by (rewrite AG2 by lia; exact Usp).
assert (U33 : bv_unsigned (ew Ev2 33) = rsp1 sp0) by (rewrite AG2 by lia; exact Usp1).
assert (U32 : bv_unsigned (ew Ev2 32) = SB) by (rewrite AG2, E32 by lia; apply unsigned_lit_small; unfold SB; lia).
assert (U34 : bv_unsigned (ew Ev2 34) = as_uar_cell B) by (rewrite AG2, E34 by lia; apply unsigned_lit_small; lia).
assert (U1028 : bv_unsigned (ew Ev2 1028) = F) by (rewrite E2_1028; apply unsigned_lit_small; lia).
assert (U1040 : bv_unsigned (ew Ev2 1040) = FL) by (rewrite E2_1040; apply unsigned_lit_small; unfold in_app, kLowShadowBeg, kHighMemBeg in HFLrng; lia).
assert (U1041 : bv_unsigned (ew Ev2 1041) = SB + F / 8).
{ rewrite E2_1041; apply unsigned_lit_small. assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SB; lia. }
assert (UO0 : bv_unsigned (ew Ev2 241) = VAL (A_OBJ 0)) by exact (HEI2 (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (UO1 : bv_unsigned (ew Ev2 242) = VAL (A_OBJ 1)) by exact (HEI2 (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (UO12 : bv_unsigned (ew Ev2 253) = VAL (A_OBJ 12)) by exact (HEI2 (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
unfold kImgEnd in Hob0, Hob1, Hob12.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
lazymatch type of Hsep with ?T => change (rnam T) in Hsep end.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; rewrite HF64, Z.add_0_r in D; exact D).
assert (HF8d : F / 8 = 8 * (F / 64)) by (rewrite HFq at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8 : F / 8 * 8 = F) by lia.
assert (HF8m : (F / 8) mod 8 = 0) by (rewrite HF8d, Z.mul_comm; apply Z_mod_mult).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44) by lia.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 1028 (mkAF 4096 (2 ^ 47) 6) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1028; change (2 ^ 6) with 64; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1040 (mkAF 4096 (2 ^ 47) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1040; rewrite Z.pow_0_r, Z.mod_1_r; unfold in_app, kLowShadowBeg, kHighMemBeg in HFLrng; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1041 (mkAF (SB + 512) (SB + 2 ^ 44) 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1041; change (2 ^ 3) with 8;
split; [lia|]; split; [unfold SB; rewrite Zplus_mod, HF8m; reflexivity | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 1028 32 1041 F SB E2_1028 ltac:(lia)
ltac:(rewrite AG2 by lia; exact E32) E2_1041)) as HS3;
clear HS; rename HS3 into HS end.
rnorm HS.
assert (Hz8 : forall i, 0 <= i < 8 -> aview SEGS (w_H W) mem2 (SB + F / 8 + i) = Some 0).
{ intros i Hi. pose proof (Hz i Hi) as Q. unfold shadow_of_addr in Q. exact Q. }
assert (HFS8 : forall i, 0 <= i < 8 -> apresent (w_H W) mem2 (SB + F / 8 + i)).
{ intros i Hi. exact (proj1 (HFSpres i Hi)). }
pose proof (conj Hob0 (conj Hob1 (conj Hob12 (conj Huar (conj Hsep (conj HFimg (conj HF4096 (conj HFceil (conj HFapp
(conj Hceil (conj Hslo (conj Hshi (conj H47 (conj Hs1 (conj C1 (conj HF8b (conj HF8 FFS))))))))))))))))) as AM.
lazymatch type of AM with ?T => change (rnam T) in AM end.
raddreg HS (YP09.mkRegion (Some 1028%nat) 40 64 40 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ F 56 8 _ FL);
[cbn [sv_denot]; rewrite E2_1040, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold in_app, kLowShadowBeg, kHighMemBeg in HFLrng; zside | zside |
replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ]).
raddreg HS (YP09.mkRegion (Some 1028%nat) 32 40 32 40 [])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | apply Forall_nil ]).
raddreg HS (YP09.mkRegion (Some 1028%nat) 0 32 0 32 [])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | apply Forall_nil ]).
raddreg HS (YP09.mkRegion (Some 1041%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))])
ltac:(rewrite U1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (HFS8 o ltac:(lia))
| apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ (SB + F / 8) 0 8 _ 0);
[reflexivity | zside | zside | rewrite Z.add_0_r; apply val_mem_zero8; exact Hz8] ]).
assert (INF : forall a, F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 -> in_frames ly [(0, fpos)] a).
{ intros a Ha. exists 0, fpos. split; [left; reflexivity|]. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. fold F. unfold SB in Ha. lia. }
(* R2: the frame's header words and its shadow f1 f1 f1 f1 f8 f3 f3 f3 (0x88e34-0x88ec0), a plain run because it
   writes shadow bytes; it stops at the first inline check (0x88ec4) *)
paj_run_to_sh RUNTOP HS HJ2 16784.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own => let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 1041%nat (SB + F / 8)); [reflexivity | exact U1041 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; apply INF; lia |].
do 3 (eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 1028%nat F); [reflexivity | exact U1028 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; apply INF; lia |]).
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; rewrite ?FFS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; rewrite ?FFS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (rsp1 sp0 - sp0)); [reflexivity | rewrite U33; lia | cbn; rewrite ?FFS; lia | cbn; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the run wrote the frame, its shadow and its stack slots only *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (SB + F / 8 <= a < SB + F / 8 + 8) \/ (F <= a < F + 64) \/ (sp0 - 176 <= a < sp0)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U33, ?U1028, ?U1041 in Hrr; clear - Hrr Hs1b; lia |]);
  destruct Hin)) as UNb.
clear HF HFr. rename HG into HGb.
(* c's block: disjoint from the frame, off the image, below the stack *)
pose proof (proj1 HJ2) as HAR3.
assert (HpbT : In (pb, kb) (ablocks B ly S2)) by (rewrite Eab; exact Hpbin).
pose proof (sep_block_frame SEGS B LAWS ly S2 W _ _ pb kb 0 fpos HAR3 HpbT Hfin2) as HWF.
unfold zdisjoint in HWF. cbn [fst snd] in HWF. change (fs_frame_bytes 0) with 64 in HWF. fold F in HWF.
pose proof (blk_off_imgP B ly S W mem md pb kb HAR Hpbin) as HPBI. unfold off_img in HPBI.
unfold in_app in Hpbapp.
(* the bytes of c's block at this state are the entry's *)
assert (CK : forall a, c <= a < c + 16616 -> rdW W (ms_mem ms0) a = rdW W mem a).
{ intros a Ha.
  rewrite (UNb a ltac:(lia)); [| unfold SB, kLowShadowBeg, kHighMemBeg in *; intros [Q|[Q|Q]]; lia].
  destruct HK as (KK1 & KK2 & _).
  cbn [ms_mem restrict mkst].
  pose proof (KK2 pb kb (a - pb) Hpbin ltac:(lia) (fun q => q)) as KQ.
  replace (pb + (a - pb)) with a in KQ by lia.
  rewrite KQ. apply UNa; [lia | lia]. }
(* c->n_refusals, c->refused and c->reading[0] *)
set (nr := Z.of_nat (length (rc_refusal rcs))) in *.
pose proof (refuse_f.rf_rd_nref _ _ _ HRC) as RN0. pose proof (refuse_f.rf_rd_refd _ _ _ HRC) as RR0.
pose proof (refuse_f.rf_rd_rd0 _ _ _ HRC) as RD0.
pose proof HRC as (bs0 & _ & HENC).
pose proof HENC as (_ & _ & _ & _ & Hnr8 & _ & _ & (Hrf0 & _) & _).
set (rd0 := hd0 (rc_reading rcs)) in *.
assert (Hrd0 : 0 <= rd0 < 256).
{ destruct (refuse_f.rf_rd_byte _ _ _ seg_spec.RC_READING HRC ltac:(unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE; lia)) as (v & Hv & Hvr).
  rewrite RD0 in Hv. injection Hv as <-. exact Hvr. }
assert (RN : rd32 (rdW W (ms_mem ms0)) (c + 0x34c8) nr).
{ intros k Hk. rewrite CK by (unfold seg_spec.RC_NREF; lia). exact (RN0 k Hk). }
assert (RR : rd32 (rdW W (ms_mem ms0)) (c + 0x34cc) (rc_refused rcs)).
{ intros k Hk. rewrite CK by (unfold seg_spec.RC_REFUSED; lia). exact (RR0 k Hk). }
assert (RD : rdW W (ms_mem ms0) (c + 0x4080) = Some rd0).
{ rewrite CK by lia. exact RD0. }
pose proof (st_ok_pi_havoc_hi 1042 Ev2 _ _ [Z_to_bv 64 nr; Z_to_bv 64 (rc_refused rcs); Z_to_bv 64 rd0] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS; rename HS3 into HS.
set (Ev3 := YN3v.havoc Ev2 1042 [Z_to_bv 64 nr; Z_to_bv 64 (rc_refused rcs); Z_to_bv 64 rd0]) in HS.
assert (AG3 : forall n, (n < 1042)%nat -> ew Ev3 n = ew Ev2 n) by (intros n Hn; subst Ev3; apply ew_havoc_old; exact Hn).
assert (E3_1042 : ew Ev3 1042 = Z_to_bv 64 nr) by (subst Ev3; exact (ew_havoc_new Ev2 1042 [Z_to_bv 64 nr; Z_to_bv 64 (rc_refused rcs); Z_to_bv 64 rd0] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E3_1043 : ew Ev3 1043 = Z_to_bv 64 (rc_refused rcs)) by (subst Ev3; exact (ew_havoc_new Ev2 1042 [Z_to_bv 64 nr; Z_to_bv 64 (rc_refused rcs); Z_to_bv 64 rd0] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E3_1044 : ew Ev3 1044 = Z_to_bv 64 rd0) by (subst Ev3; exact (ew_havoc_new Ev2 1042 [Z_to_bv 64 nr; Z_to_bv 64 (rc_refused rcs); Z_to_bv 64 rd0] 2 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI3 : img_env VAL A_LIM Ev3) by (subst Ev3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
assert (V2 : bv_unsigned (ew Ev3 2) = sp0) by (rewrite AG3 by lia; exact U2).
assert (V33 : bv_unsigned (ew Ev3 33) = rsp1 sp0) by (rewrite AG3 by lia; exact U33).
assert (V32 : bv_unsigned (ew Ev3 32) = SB) by (rewrite AG3 by lia; exact U32).
assert (V1028 : bv_unsigned (ew Ev3 1028) = F) by (rewrite AG3 by lia; exact U1028).
assert (V1040 : bv_unsigned (ew Ev3 1040) = FL) by (rewrite AG3 by lia; exact U1040).
assert (V1041 : bv_unsigned (ew Ev3 1041) = SB + F / 8) by (rewrite AG3 by lia; exact U1041).
assert (VO0 : bv_unsigned (ew Ev3 241) = VAL (A_OBJ 0)) by (rewrite AG3 by (unfold A_OBJ; lia); exact UO0).
assert (VO1 : bv_unsigned (ew Ev3 242) = VAL (A_OBJ 1)) by (rewrite AG3 by (unfold A_OBJ; lia); exact UO1).
assert (VO12 : bv_unsigned (ew Ev3 253) = VAL (A_OBJ 12)) by (rewrite AG3 by (unfold A_OBJ; lia); exact UO12).
assert (V34 : bv_unsigned (ew Ev3 34) = as_uar_cell B) by (rewrite AG3 by lia; exact U34).
assert (V10 : bv_unsigned (ew Ev3 10) = c) by (rewrite AG3, AG2 by lia; rewrite E10, H10; unfold w64; apply unsigned_lit_small; lia).
assert (V1042 : bv_unsigned (ew Ev3 1042) = nr) by (rewrite E3_1042; apply unsigned_lit_small; lia).
assert (V1043 : bv_unsigned (ew Ev3 1043) = rc_refused rcs) by (rewrite E3_1043; apply unsigned_lit_small; lia).
assert (V1044 : bv_unsigned (ew Ev3 1044) = rd0) by (rewrite E3_1044; apply unsigned_lit_small; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 1042 (mkAF 0 8 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite V1042; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1043 (mkAF 0 (2 ^ 32 - 2) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite V1043; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1044 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite V1044; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS end.
rnorm HS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb kb HAR3 HpbT) as (_ & _ & _ & _ & Hpbpres3 & _).
clear AM.
pose proof (conj Hob0 (conj Hob1 (conj Hob12 (conj Huar (conj HF4096 (conj HFceil (conj HFapp (conj HWF (conj HPBI
  (conj Hpbapp (conj Hpb1 (conj Hpb2 (conj Hkbr (conj Hpbceil (conj Hpb4096 (conj Hceil (conj Hslo (conj Hs1
  (conj C1 (conj HF8b (conj HF8 FFS))))))))))))))))))))) as AM.
lazymatch type of AM with ?T => change (rnam T) in AM end.
raddreg HS (YP09.mkRegion (Some 10%nat) 0x34c8 0x34d0 0x34cc 0x34d0
  [YP09.mkChunk 0x34c8 (CVal 4 (SOff 1042 0)); YP09.mkChunk 0x34cc (CVal 4 (SOff 1043 0))])
ltac:(rewrite V10; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hpbpres3 (c + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  [ eapply (chunk_ok_val SEGS _ _ c 0x34c8 4 _ nr);
    [cbn [sv_denot]; rewrite E3_1042, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
     exact (val_mem_of_rd32 SEGS _ _ _ _ RN)]
  | eapply (chunk_ok_val SEGS _ _ c 0x34cc 4 _ (rc_refused rcs));
    [cbn [sv_denot]; rewrite E3_1043, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
     exact (val_mem_of_rd32 SEGS _ _ _ _ RR)] ] ]).
raddreg HS (YP09.mkRegion (Some 10%nat) 0x4080 0x4081 0x4080 0x4080 [YP09.mkChunk 0x4080 (CVal 1 (SOff 1044 0))])
ltac:(rewrite V10; split; [lia|]; split; [lia|]; split;
[ intros o Ho; lia
| apply Forall_cons; [|apply Forall_nil];
  eapply (chunk_ok_val SEGS _ _ c 0x4080 1 _ rd0);
  [cbn [sv_denot]; rewrite E3_1044, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
   exact (r_val1 SEGS _ _ _ _ RD)] ]).
(* the token runs read the frame and its shadow only: their regions are read-only from here to the next store into
   them (a token run takes no writable window whose atom's range meets the shadow band, YCbn.v cells_safe_b) *)
rrewin HS 1041%nat 0 0 0 ltac:(intros o Ho; lia).
rrewin HS 1028%nat 0 0 0 ltac:(intros o Ho; lia).
rrewin HS 1028%nat 32 32 32 ltac:(intros o Ho; lia).
rrewin HS 1028%nat 40 40 40 ltac:(intros o Ho; lia).
(* the shadow entries of checks 1-3: c->n_refusals, c->refused and c->reading[0], in the live block c *)
assert (UB : U Ev3 (SOff 32 0) = SHADOW_OFF) by (rewrite (U_atom Ev3 32 SB); [reflexivity | rewrite AG3, AG2, E32 by lia; reflexivity | unfold SB; lia]).
assert (UC : U Ev3 (SOff 10 0) = c) by (apply U_atom; [rewrite AG3, AG2, E10, H10 by lia; reflexivity | lia]).
assert (ZSHC : range_addressable (rdW W (ms_mem ms0)) SHADOW_OFF c 16616)
  by exact (range_addressable_of_block SEGS B LAWS ly S2 W (ms_mem ms0) _ pb kb c 16616 HAR3 HpbT Hpb1 ltac:(lia)).
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 10 0x34c8 0x34d0; mkSHE 10 0x4080 0x4081] Ev3 (mrestrict (w_H W) (ms_mem ms0))).
{ unfold sh_ok. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (shent_ok_of_range SEGS (w_H W) (ms_mem ms0) Ev3 (SOff 32 0) 10%nat c 16616 c 0x34c8 0x34d0 ZSHC UB UC);
    [lia | lia | intros x Hx; unfold SHADOW_OFF; unfold kLowShadowBeg, kHighMemBeg in Hpbapp; lia].
  - eapply (shent_ok_of_range SEGS (w_H W) (ms_mem ms0) Ev3 (SOff 32 0) 10%nat c 16616 c 0x4080 0x4081 ZSHC UB UC);
    [lia | lia | intros x Hx; unfold SHADOW_OFF; unfold kLowShadowBeg, kHighMemBeg in Hpbapp; lia]. }
(* R3: checks 1 and 2, c->refused++, the n_refusals test (0x88ec4-0x88efc) *)
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ _ _ ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    assert (INFP : forall a, c + 0x34cc <= a < c + 0x34d0 -> awr_byte SEGS B stk spx fp b0 bc fr0 lyx own a) end.
  { intros a Ha. right; left. split.
    - exists (c + seg_spec.RC_REFUSED, c + seg_spec.RC_REFUSED + 4).
      split; [unfold refuse_W; apply in_or_app; left; left; reflexivity | cbn [fst snd]; unfold seg_spec.RC_REFUSED; lia].
    - exists pb, kb. split; [first [exact HpbT | exact Hpbin | rewrite Eab; exact Hpbin] | lia]. }
  r_awr V2 V33 V1028 V1041 V10 INF INFP sp0 F c. }
(* the n_refusals test (0x88efc `blt 7, n`): n >= 8 goes to the release (0x88fc4), n < 8 to the slot *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n >= 8 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (r_branch_lt7 Ex 1042 nr ltac:(r_evE; exact E3_1042) ltac:(lia)) in Hc end.
  apply Z.ltb_lt in Hc.
  assert (Hn8 : (8 <= length (rc_refusal rcs))%nat)
    by (change nr with (Z.of_nat (length (rc_refusal rcs))) in Hc; lia).
  (* the run R3 wrote c->refused and its stack slots only *)
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => (c + 0x34cc <= a < c + 0x34d0) \/ (sp0 - 176 <= a < sp0)) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?V2, ?V33, ?V10, ?V1028, ?V1041 in Hrr; clear - Hrr Hs1b; lia |]);
    destruct Hin)) as UNc.
  clear HF HFr HG.
  (* the taken branch, 0x88efc -> 0x88fc4 (R_REL), with every window read-only: a run that writes nothing *)
  rrewin HS 10%nat 13512 13516 13516 ltac:(intros o Ho; lia).
  rrewin HS 2%nat (-160) (-160) (-160) ltac:(intros o Ho; lia).
  rrewin HS 2%nat (-144) (-144) (-144) ltac:(intros o Ho; lia).
  rrewin HS 33%nat 8 8 8 ltac:(intros o Ho; lia).
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 17040.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ =>
    lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil end).
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msR end.
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
    destruct Hin)) as UN4.
  clear HF HFr HG.
  (* the bytes of c's block at the release are the entry's, except c->refused *)
  assert (CK2 : forall a, c <= a < c + 16616 -> ~ (c + seg_spec.RC_REFUSED <= a < c + seg_spec.RC_REFUSED + 4) ->
    rdW W (ms_mem msR) a = rdW W mem a).
  { intros a Ha Hna. unfold seg_spec.RC_REFUSED in Hna.
    rewrite (UN4 a ltac:(lia) (fun q => q)).
    rewrite (UNc a ltac:(lia)); [apply CK; lia |].
    unfold SB, kLowShadowBeg, kHighMemBeg in *; intros [Q|Q]; lia. }
  (* the new c->refused: the chunk of atom 10's region, sext32 (c->refused) + 1 *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let i := eval vm_compute in (r_find (ss_mem ssx) 10%nat 13512 0) in
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS ltac:(vm_compute; reflexivity)) as HR10;
  cbn [ms_mem restrict] in HR10 end.
  lazymatch type of HR10 with region_ok _ ?Ex _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (r_region_aval4 SEGS Ex _ _ 10%nat c cs lo hi wlo whi 13516 (SAlu ALU_ADD (SExt true 32 (SOff 1043 0)) (SLit 1))
    (bv_unsigned (Z_to_bv 64 (Z.land (rc_refused rcs + 2 ^ 31) (2 ^ 32 - 1) - 2 ^ 31 + 1))) HR10
    ltac:(r_evE; exact V10) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    ltac:(apply r_inc_denot; [r_evE; exact E3_1043 | lia])) as VR end.
  clear HR10.
  assert (RR1 : rd32 (rdW W (ms_mem msR)) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1)).
  { intros k Hk.
    transitivity (Some (YG0f.le_byte (bv_unsigned (Z_to_bv 64 (Z.land (rc_refused rcs + 2 ^ 31) (2 ^ 32 - 1) - 2 ^ 31 + 1))) 4 k)).
    - exact (VR k Hk).
    - f_equal. exact (refuse_f.rf_sw_inc (rc_refused rcs) ltac:(lia) k Hk). }
  (* the reader at the release holds SegModel.refuse rcs ln f args at c: the counting-only arm *)
  assert (HRC1 : sa_rconf (rdW W (ms_mem msR)) c (SegModel.refuse rcs ln f args)).
  { rewrite (refuse_f.rf_refuse_ge8 rcs ln f args Hn8).
    apply (refuse_f.rf_upd_refd (rdW W mem) (rdW W (ms_mem msR)) c rcs HRC Hrf32); [| exact RR1].
    intros i Hi Hni. unfold seg_spec.SEG_C_SIZE in Hi. apply CK2; [lia | intros Q; apply Hni; lia]. }
  (* to the release state ss_rel, and refuse_r's release *)
  r_to_rel HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (EvR := Ex) in HS end.
  assert (HEIR : img_env VAL A_LIM EvR).
  { subst EvR. apply img_env_havoc_hi; [| unfold A_LIM; lia]. apply img_env_ewset_hi; [| unfold A_LIM; lia].
    apply img_env_ewset_hi; [exact HEI3 | unfold A_LIM; lia]. }
  assert (AGR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EvR n = getr regs r).
  { intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    subst EvR. rewrite ew_havoc_old by lia. rewrite !ew_ewset_other by lia. rewrite AG3, AG2 by lia.
    subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
  assert (R32 : ew EvR 32 = Z_to_bv 64 SB)
    by (subst EvR; rewrite ew_havoc_old by lia; rewrite !ew_ewset_other by lia; rewrite AG3, AG2 by lia; exact E32).
  assert (R2 : ew EvR 2 = getr regs 2)
    by (subst EvR; rewrite ew_havoc_old by lia; rewrite !ew_ewset_other by lia; rewrite AG3, AG2 by lia; exact E2).
  assert (R1028 : ew EvR 1028 = Z_to_bv 64 (frame_addr ly 0 fpos))
    by (subst EvR; rewrite ew_havoc_old by lia; rewrite !ew_ewset_other by lia; rewrite AG3 by lia; exact E2_1028).
  assert (R1040 : ew EvR 1040 = Z_to_bv 64 (flag_addr ly 0 fpos))
    by (subst EvR; rewrite ew_havoc_old by lia; rewrite !ew_ewset_other by lia; rewrite AG3 by lia; exact E2_1040).
  assert (R1041 : ew EvR 1041 = Z_to_bv 64 (SB + frame_addr ly 0 fpos / 8))
    by (subst EvR; rewrite ew_havoc_old by lia; rewrite !ew_ewset_other by lia; rewrite AG3 by lia; exact E2_1041).
  assert (HBLK : exists pb kb, In (pb, kb) (ablocks B ly S) /\ pb <= c /\ c + seg_spec.SEG_C_SIZE <= pb + req_size kb)
    by (exists pb, kb; split; [exact Hpbin | split; [lia | unfold seg_spec.SEG_C_SIZE; lia]]).
  assert (HS2f : exists f0, S2 = set_fs f0 S) by (exists fS2; first [exact ES2 | exact (eq_sym ES2)]).
  eapply refuse_r.r_release with (B := B) (ly := ly) (S := S) (W := W) (regs := regs) (mem := mem) (md := md)
    (ch := ch) (c := c) (rcs' := SegModel.refuse rcs ln f args) (FP := refuse_W c rcs) (S2 := S2) (fpos := fpos)
    (Ev := EvR);
  [ assumption .. | exact HPRE | exact HEIR | exact HS | exact HJ2 | exact Hfrs2 | exact Eab | exact HS2f
  | exact AGR | exact R32 | exact R2 | exact R1028 | exact R1040 | exact R1041 | exact HBLK | exact HRC1 ].
  Unshelve.
- (* n < 8 (0x88f00-0x88fc0): check 3 and c->reading[0], the address prefix by snprintf (0x88f5c / 0x88f74), the k
     test, va_start, the text by vsnprintf (0x88fa4), check 4 and c->n_refusals++, to the release 0x88fc4 *)
  (* r_evE with its side conditions first tried in an empty context (they are numeral comparisons) *)
  Ltac rb_evE := repeat first [rewrite ew_ewset_other by (first [solve [clear; lia] | lia])
                              | rewrite ew_havoc_old by (first [solve [clear; lia] | lia])].
  (* an address goal decided from the bundle AMB alone (refuse_e.v's rzl, over this bullet's bundle) *)
  Ltac rb_zl AMB := revert AMB; clear; unfold rnam, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd,
    ASAN_CEIL, SB, SHADOW_OFF, kImgEnd, off_img, RtPFCmd.CMD_SNP_K, RtPFSeg.SEG_VSN_K;
    intros; repeat match goal with H : _ /\ _ |- _ => destruct H end; lia.
  Ltac rb_env HS := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => Ex | st_ok _ ?Ex _ _ => Ex end.
  Ltac rb_lia AMB := first [solve [clear; lia] | solve [rb_zl AMB] | lia].
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (r_branch_lt7 Ex 1042 nr ltac:(rb_evE; exact E3_1042) ltac:(lia)) in Hc end.
  apply Z.ltb_ge in Hc.
  (* lia's cost grows with every disjunction in the context: the disjunctive facts stay under rnam and each proof
     that needs one opens it *)
  lazymatch type of HPBI with ?T => change (rnam T) in HPBI end.
  lazymatch type of Hpbapp with ?T => change (rnam T) in Hpbapp end.
  lazymatch type of HWF with ?T => change (rnam T) in HWF end.
  lazymatch type of HFapp with ?T => change (rnam T) in HFapp end.
  lazymatch type of HFLrng with ?T => change (rnam T) in HFLrng end.
  lazymatch type of Hc0 with ?T => change (rnam T) in Hc0 end.
  lazymatch type of Hfp0 with ?T => change (rnam T) in Hfp0 end.
  assert (Enr : nr = Z.of_nat (length (rc_refusal rcs))) by reflexivity.
  assert (Hn7 : (length (rc_refusal rcs) < 8)%nat) by lia.
  assert (Hnr0 : 0 <= nr) by lia.
  assert (Hn8b : (length (rc_refusal rcs) <? 8)%nat = true) by (apply Nat.ltb_lt; exact Hn7).
  set (T1 := SegModel.fmt (SegModel.r_addr_fmt ln) (SegModel.r_addr_args rcs ln)).
  destruct (refuse_f.rf_T1 rcs bs0 ln HENC Hln) as (HT1l & HT1z & HT1b).
  fold T1 in HT1l, HT1z, HT1b.
  (* the run R3 wrote c->refused and its stack slots only *)
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => (c + 0x34cc <= a < c + 0x34d0) \/ (sp0 - 176 <= a < sp0)) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?V2, ?V33, ?V10, ?V1028, ?V1041 in Hrr; clear - Hrr Hs1b; lia |]);
    destruct Hin)) as UNc.
  clear HF HFr HG.
  (* the bytes of c's block at R4 (machine ms1) are the entry's, except c->refused *)
  assert (KC1 : forall a, c <= a < c + 16616 -> ~ (c + 0x34cc <= a < c + 0x34d0) ->
    rdW W (ms_mem ms1) a = rdW W mem a).
  { intros a Ha Hna. rewrite (UNc a ltac:(lia)); [apply CK; lia |].
    unfold SB, kLowShadowBeg, kHighMemBeg in *; intros [Q|Q]; lia. }
  (* facts at R4 the snprintf call reads (the memory at the call is ms1's: B1-B3 store nothing) *)
  (* what the call's journal keeps at a later memory mm: the image bytes refuse reads (its literals, the read-only
     bytes), since the footprint refuse_W lies in c's block, off the image *)
  assert (HSNK : ~ YI16.sink_open_fp (refuse_W c rcs)).
  { apply sink_closed_pos. unfold refuse_W. rewrite Hn8b.
    repeat constructor; cbn [fst]; unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
      seg_spec.RC_REFUSED, seg_spec.RC_NREF; lia. }
  assert (NINFP : forall a, in_img SEGS a -> ~ inFP (refuse_W c rcs) a).
  { intros a Hi (r & Hr & Hrr2). unfold refuse_W in Hr. rewrite Hn8b in Hr.
    apply (blk_img SEGS B LAWS ly S W mem md pb kb a HAR Hpbin); [| exact Hi].
    cbn [In app] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrr2;
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_REFUSED,
      seg_spec.RC_NREF in Hrr2; lia. }
  assert (KIMGJ : forall mm mdd,
    ajournal SEGS B STK_refuse sp0 (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 W mm mdd 0 ->
    forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    rdW W mm a = rdW W mem a).
  { intros mm mdd HJx a Hi Ho He. pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JI & _).
    apply JI; [exact Hi | exact Ho | exact He |]. apply fp_spares_closed; [exact HSNK | exact (NINFP a Hi)]. }
  assert (ROMJ : forall mm mdd,
    ajournal SEGS B STK_refuse sp0 (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 W mm mdd 0 ->
    RtDefs.rt_rom_view SEGS B W mm).
  { intros mm mdd HJx a (sg & Hsg & Hw & Hr) Ho He.
    rewrite (KIMGJ mm mdd HJx); [| exists sg; split; [exact Hsg | exact Hr] | exact Ho | exact He].
    apply HROD; [left; exists sg; split; [exact Hsg | split; [exact Hw | exact Hr]] | exact Ho | exact He]. }
  assert (LITJ : forall mm mdd,
    ajournal SEGS B STK_refuse sp0 (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 W mm mdd 0 ->
    forall a x, sa_lit SEGS B (rdW W mem) a x ->
    sa_str (rdW W mm) a x /\ sa_addr (rdW W mm) a (Z.of_nat (length x) + 1)).
  { intros mm mdd HJx a x (Hpos & ((Hzs & Hn0) & Htl) & Hpin & Hrt & Himg).
    split; [split; [split; [| exact Hn0] | exact (sa_tail_of_romtail SEGS _ _ _ Hrt)] | exact (Hpin _ _ _ _ _ (proj1 HJx))].
    intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
    destruct (Himg (a + Z.of_nat i) ltac:(lia)) as (Hi1 & Hi2 & Hi3).
    rewrite (KIMGJ mm mdd HJx) by assumption. exact (Hzs i Hi). }
  pose proof (proj1 HJ2) as HARm.
  pose proof (ROMJ _ _ HJ2) as ROM1.
  pose proof (SSPX _ _ _ _ _ HARm) as (SSP1 & gcan & SSP2).
  (* refuse's three literals at R4 *)
  assert (LITX : forall x, In x REFUSE_LITS ->
    sa_str (rdW W (ms_mem ms1)) (seg_litA_rc x) x /\
    sa_addr (rdW W (ms_mem ms1)) (seg_litA_rc x) (Z.of_nat (length x) + 1) /\
    sa_img SEGS B (seg_litA_rc x) (Z.of_nat (length x) + 1) /\
    0x10000 <= seg_litA_rc x /\ seg_litA_rc x + Z.of_nat (length x) + 8 <= RtPFCmd.CMD_GOTW /\
    Forall (fun v => 0 < v < 256) x /\ (length x <= 65535)%nat).
  { intros x Hx. destruct (LITJ _ _ HJ2 _ _ (HLITS x Hx)) as (Hs & Ha).
    destruct (HLITS x Hx) as (_ & _ & _ & _ & Himg).
    split; [exact Hs |]. split; [exact Ha |]. split; [exact Himg |].
    unfold REFUSE_LITS in Hx.
    destruct Hx as [<- | [<- | [<- | []]]];
      (split; [apply Z.leb_le; vm_compute; reflexivity |]); (split; [apply Z.leb_le; vm_compute; reflexivity |]);
      (split; [apply refuse_f.rf_pos_forallb; vm_compute; reflexivity | apply Nat.leb_le; vm_compute; reflexivity]). }
  assert (OFFI : forall a n, c <= a -> a + n <= c + 16616 -> 0 <= n -> a + n <= 0x10000 \/ kImgEnd <= a).
  { intros a n H1 H2 H3. unfold rnam in HPBI. unfold kImgEnd. lia. }
  (* the object addresses the code forms: "reac-pw.conf", "%s:%d: ", "%s: " *)
  assert (LA34 : VAL (A_OBJ 34) = seg_litA_rc SegModel.S_base)
    by (rewrite (OBJ 34%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)); vm_compute; reflexivity).
  assert (LA71 : VAL (A_OBJ 71) = seg_litA_rc SegModel.F_addr_line)
    by (rewrite (OBJ 71%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)); vm_compute; reflexivity).
  assert (LA72 : VAL (A_OBJ 72) = seg_litA_rc SegModel.F_addr)
    by (rewrite (OBJ 72%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)); vm_compute; reflexivity).
  (* the value of dst (s6, a0 at the calls) *)
  assert (DSLOT : forall Ex, ew Ex 10 = Z_to_bv 64 c -> ew Ex 1042 = Z_to_bv 64 nr ->
    sv_denot Ex (SAlu ALU_ADD (SOff 10 11912) (SMd M_MUL (SOff 1042 0) (SLit 200))) = Z_to_bv 64 (c + 11912 + 200 * nr)).
  { intros Ex H10' H1042'. rewrite denot_lit_U. f_equal.
    rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
    rewrite (U_atom_off Ex 10 c 11912 H10') by lia. rewrite (U_atom Ex 1042 nr H1042') by lia. rewrite U_SLit.
    rewrite (zcanon_id 200) by (unfold M64; lia). rewrite (zcanon_id (nr * 200)) by (unfold M64; lia).
    rewrite zcanon_id by (unfold M64; lia). lia. }
  assert (E11 : ew E 11 = Z_to_bv 64 ln)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (BGE : forall Ex, ew Ex 11 = Z_to_bv 64 ln ->
    branch_taken BC_GE (sv_denot Ex (SLit 0)) (sv_denot Ex (SOff 11 0)) = negb (0 <? ln)).
  { intros Ex HE.
    assert (HU : U Ex (SOff 11 0) = ln) by (apply U_atom; [exact HE | lia]).
    assert (H0 : U Ex (SLit 0) = 0) by (apply U_lit; lia).
    unfold U in HU, H0. cbn [branch_taken]. rewrite bv_lts_signed, !signed_of_small by (unfold half64; lia).
    rewrite HU, H0. reflexivity. }
  (* the slot dst = c + 0x2e88 + 200 n and what the address snprintf writes there *)
  assert (Hc8 : c mod 8 = 0) by (clear - Hc16; Z.div_mod_to_equations; lia).
  assert (SNL1 : RtPFShared.sn_len (200 - 1) T1 = Z.of_nat (length T1) + 1).
  { unfold RtPFShared.sn_len, RtPFShared.sn_bytes. change (Z.to_nat (200 - 1)) with 199%nat.
    rewrite length_app, firstn_all2 by lia. cbn [length]. lia. }
  assert (Ho16 : (rsp1 sp0 - sp0) mod 16 = 0).
  { unfold rnam in Hs1. destruct Hs1 as [Hq|Hq]; rewrite Hq;
    [replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity. }
  assert (Hneg : rsp1 sp0 - sp0 <= 0) by lia.
  assert (HKe : ESTACK <= RtPFCmd.CMD_SNP_K) by (unfold RtPFCmd.CMD_SNP_K; lia).
  assert (Hbud : RtPFCmd.CMD_SNP_K - (rsp1 sp0 - sp0) <= STK_refuse) by (unfold RtPFCmd.CMD_SNP_K; rewrite FFS, Hes; lia).
  pose proof (conj AM (conj Hcb (conj Hs1b (conj Hbud (conj Hstk0 (conj Hes (conj Enr
    (conj Hn7 (conj HT1l (conj Hshi H47)))))))))) as AMB.
  lazymatch type of AMB with ?T => change (rnam T) in AMB end.
  assert (HADDR : forall q nq, c <= q -> q + nq <= c + 16616 -> 0 < nq -> sa_addr (rdW W (ms_mem ms1)) q nq).
  { intros q nq H1 H2 H3.
    pose proof (amem8_of_block SEGS B LAWS ly S2 W (ms_mem ms1) _ pb kb q nq HARm HpbT ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB)) as HA8.
    split; [rb_lia AMB |]. split; [rb_lia AMB |]. split; [unfold amem_range in *; rb_lia AMB |]. split.
    - exact (range_addressable_of_block SEGS B LAWS ly S2 W (ms_mem ms1) _ pb kb q nq HARm HpbT ltac:(rb_lia AMB) ltac:(rb_lia AMB)).
    - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S2 W (ms_mem ms1) _ pb kb q nq HARm HpbT ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB)). }
  assert (HADDRJ : forall mm mdd q nq, AR SEGS B ly S2 W mm mdd -> c <= q -> q + nq <= c + 16616 -> 0 < nq ->
    sa_addr (rdW W mm) q nq).
  { intros mm mdd q nq HARx H1 H2 H3.
    pose proof (amem8_of_block SEGS B LAWS ly S2 W mm mdd pb kb q nq HARx HpbT ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB)) as HA8.
    split; [rb_lia AMB |]. split; [rb_lia AMB |]. split; [unfold amem_range in *; rb_lia AMB |]. split.
    - exact (range_addressable_of_block SEGS B LAWS ly S2 W mm mdd pb kb q nq HARx HpbT ltac:(rb_lia AMB) ltac:(rb_lia AMB)).
    - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S2 W mm mdd pb kb q nq HARx HpbT ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB)). }
  pose proof (HADDR (c + 11912 + 200 * nr) 200 ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB)) as (_ & _ & _ & RAD1 & HUL1').
  pose proof (HUL1' ltac:(rb_lia AMB)) as HUL1. clear HUL1'.
  assert (AMR1 : amem_range (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1 + 8)).
  { rewrite SNL1. exact (amem8_of_block SEGS B LAWS ly S2 W (ms_mem ms1) _ pb kb (c + 11912 + 200 * nr)
      (Z.of_nat (length T1) + 1) HARm HpbT ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB)). }
  assert (DST1 : forall a, c + 11912 + 200 * nr <= a < c + 11912 + 200 * nr + 200 ->
    awr_byte SEGS B STK_refuse sp0 (refuse_W c rcs) (ablocks B ly S) (ablocks B ly S2) (frames S) ly [(0, fpos)] a /\
    ~ (sp0 + (rsp1 sp0 - sp0) - RtPFCmd.CMD_SNP_K <= a < sp0 + (rsp1 sp0 - sp0))).
  { intros a Ha. split.
    - right; left. split.
      + exists (seg_spec.refusal_addr c (length (rc_refusal rcs)),
          seg_spec.refusal_addr c (length (rc_refusal rcs)) + seg_spec.RC_REFUSAL_LEN).
        split; [unfold refuse_W; apply in_or_app; right; rewrite Hn8b; left; reflexivity |].
        cbn [fst snd]. unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN. rb_lia AMB.
      + exists pb, kb. split; [exact HpbT | rb_lia AMB].
    - unfold RtPFCmd.CMD_SNP_K. rb_lia AMB. }
  assert (PWR1 : forall a, c + 11912 + 200 * nr <= a < c + 11912 + 200 * nr + 200 -> inFP (refuse_W c rcs) a ->
    (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ sp0 <= a < ly_top ly ->
    writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) a).
  { intros a Ha _ [[_ Hi] | Hs]; exfalso; [exact (blk_img SEGS B LAWS ly S W mem md pb kb a HAR Hpbin ltac:(rb_lia AMB) Hi) | rb_lia AMB]. }
  (* the strings the address snprintf reads: the format literal, c->reading or the default literal *)
  assert (FLIT : forall x rs, In x [SegModel.F_addr_line; SegModel.F_addr] ->
    Forall (fun r => fst r + snd r <= 0x10000 \/ kImgEnd <= fst r) rs ->
    refuse_pft.ffr_fmt SEGS B RtPFCmd.CMD_GOTW (rdW W (ms_mem ms1)) rs (seg_litA_rc x) x).
  { intros x rs Hx Hrs.
    assert (Hx' : In x REFUSE_LITS) by (unfold REFUSE_LITS; destruct Hx as [<- | [<- | []]]; cbn; tauto).
    destruct (LITX x Hx') as (Hs & Ha & Hi & Hlo & Hhi & _ & _).
    split; [exact Hlo |]. split; [rb_lia AMB |]. split; [exact Hs |]. split; [exact Ha |]. split; [exact Hi |].
    split; [unfold amem_range, kLowMemEnd, RtPFCmd.CMD_GOTW in *; rb_lia AMB |].
    eapply Forall_impl; [| exact Hrs]. intros [x0 y0] Hxy. unfold zdisjoint, seg_spec.cstr_span in *. cbn [fst snd] in *.
    pose proof (Z.mod_pos_bound (- (seg_litA_rc x + Z.of_nat (length x) + 1)) 8 ltac:(rb_lia AMB)).
    unfold RtPFCmd.CMD_GOTW, kImgEnd in *. rb_lia AMB. }
  assert (WLIT : forall rs, Forall (fun r => fst r + snd r <= 0x10000 \/ kImgEnd <= fst r) rs ->
    refuse_pft.ffr_arg (rdW W (ms_mem ms1)) rs (seg_litA_rc SegModel.S_base) (SegModel.AS SegModel.S_base)).
  { intros rs Hrs. destruct (LITX SegModel.S_base ltac:(unfold REFUSE_LITS; cbn; tauto)) as (Hs & Ha & Hi & Hlo & Hhi & Hb & Hl).
    split; [rb_lia AMB |]. split; [exact Hs |]. split; [exact Hb |]. split; [exact Hl |]. split; [exact Ha |].
    split; [unfold amem_range, kLowMemEnd, RtPFCmd.CMD_GOTW in *; rb_lia AMB |].
    eapply Forall_impl; [| exact Hrs]. intros [x0 y0] Hxy. unfold zdisjoint, seg_spec.cstr_span in *. cbn [fst snd] in *.
    pose proof (Z.mod_pos_bound (- (seg_litA_rc SegModel.S_base + Z.of_nat (length SegModel.S_base) + 1)) 8 ltac:(rb_lia AMB)).
    unfold RtPFCmd.CMD_GOTW, kImgEnd in *. rb_lia AMB. }
  assert (WREAD : forall rs, Forall (fun r => fst r + snd r <= c + 0x34c8 \/ c + 0x4080 + 104 <= fst r) rs ->
    SegModel.hd0 (rc_reading rcs) <> 0 ->
    refuse_pft.ffr_arg (rdW W (ms_mem ms1)) rs (c + 0x4080) (SegModel.AS (rc_reading rcs))).
  { intros rs Hrs Hrd.
    destruct (refuse_f.rf_reading (rdW W mem) c rcs HRC Hc8 Hrd) as (((Hz0 & Hn) & Ht) & Hl95 & Hb).
    unfold seg_spec.RC_READING in Hz0, Ht.
    assert (Hl : Z.of_nat (length (rc_reading rcs)) <= 95) by rb_lia AMB.
    split; [rb_lia AMB |]. split.
    { split; [split; [| exact Hn] |].
      - intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
        rewrite KC1 by rb_lia AMB. exact (Hz0 i Hi).
      - intros x Hx. pose proof (Z.mod_pos_bound (c + 16512 + Z.of_nat (length (rc_reading rcs))) 8 ltac:(rb_lia AMB)).
        rewrite KC1 by rb_lia AMB. exact (Ht x Hx). }
    split; [exact Hb |]. split; [eapply Nat.le_trans; [exact Hl95 | apply Nat.leb_le; vm_compute; reflexivity] |].
    split; [apply HADDR; rb_lia AMB |].
    split; [exact (amem8_of_block SEGS B LAWS ly S2 W (ms_mem ms1) _ pb kb (c + 0x4080) (Z.of_nat (length (rc_reading rcs)))
      HARm HpbT ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB)) |].
    eapply Forall_impl; [| exact Hrs]. intros [x0 y0] Hxy. unfold zdisjoint, seg_spec.cstr_span in *. cbn [fst snd] in *.
    pose proof (Z.mod_pos_bound (- (c + 16512 + Z.of_nat (length (rc_reading rcs)) + 1)) 8 ltac:(rb_lia AMB)). rb_lia AMB. }
  (* the bytes of the entry's live blocks, frames and frames' shadow at R4 are the entry's, except c->refused:
     the entry run wrote its stack slots, __asan_stack_malloc_0 keeps blocks and frames (fun _ => False), R2 wrote
     the new frame, its shadow and stack slots, R3 c->refused and stack slots *)
  assert (LOCB : forall a,
    ((exists p k, In (p, k) (ablocks B ly S) /\ p <= a < p + req_size k) \/
     (exists cid pos, In (cid, pos) (frames S) /\ (in_zr a (frame_rng ly (cid, pos)) \/
        in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)))) ->
    4096 <= a < alloc_ceiling /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ ~ (F <= a < F + 64)).
  { intros a Hloc. destruct Hloc as [(p & k & Hpk & Ha) | (cid & pos & Hin & Ha)].
    - destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (_ & Hp4096 & Hpceil & Happ & _).
      pose proof (sep_block_frame SEGS B LAWS ly S2 W _ _ p k 0 fpos HAR3 ltac:(rewrite Eab; exact Hpk) Hfin2) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
      revert Ha Hp4096 Hpceil Happ Hd. rb_zl AMB.
    - destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
      destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb).
      destruct (in_split _ _ Hin) as (l1 & l2 & Hsp).
      pose proof (sep_frames_pos SEGS B LAWS ly S2 W _ _ (0, fpos) (cid, pos) [] l1 l2 HAR3
        ltac:(rewrite Hfrs2, Hsp; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
      unfold in_app in Hfapp. unfold in_zr, frame_rng, shadow_addr in Ha. cbn [fst snd] in Ha.
      pose proof asan_consts as (AC1 & _). pose proof HFapp as HFapp'. unfold rnam, in_app in HFapp'.
      clear - Ha Hd Hfapp Hf4096 Hfceil Hfa64 Hfb64 Hfb HF4096 HFceil HF64 AC1 HFapp'.
      unfold SB, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      Z.div_mod_to_equations. lia. }
  assert (KS1 : forall a,
    ((exists p k, In (p, k) (ablocks B ly S) /\ p <= a < p + req_size k) \/
     (exists cid pos, In (cid, pos) (frames S) /\ (in_zr a (frame_rng ly (cid, pos)) \/
        in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)))) ->
    ~ (c + 0x34cc <= a < c + 0x34d0) -> rdW W (ms_mem ms1) a = rdW W mem a).
  { intros a Hloc Hnr.
    destruct HK as (KK1 & KK2 & _ & KK4 & _).
    destruct (LOCB a Hloc) as (Hb1 & Hb2 & Hb3).
    assert (Ha64 : 0 <= a < 2 ^ 64) by (revert Hb1; rb_zl AMB).
    rewrite (UNc a Ha64); [| intros [Q|Q]; [exact (Hnr Q) | revert Hb1 Q; rb_zl AMB]].
    rewrite (UNb a Ha64); [| intros [Q|[Q|Q]]; [exact (Hb2 Q) | exact (Hb3 Q) | revert Hb1 Q; rb_zl AMB]].
    cbn [ms_mem mkst].
    destruct Hloc as [(p & k & Hpk & Ha) | (cid & pos & Hin & Ha)].
    - pose proof (KK2 p k (a - p) Hpk ltac:(revert Ha; clear; lia) (fun q => q)) as KQ.
      replace (p + (a - p)) with a in KQ by (clear; lia). rewrite KQ. apply UNa; [exact Ha64 | revert Hb1; rb_zl AMB].
    - rewrite (KK4 cid pos a Hin Ha (fun q => q)). apply UNa; [exact Ha64 | revert Hb1; rb_zl AMB]. }
  (* the variadic arguments as FFR's ffr_args, at a later memory mm that keeps them: from refuse_pre's sa_va_args
     and refuse_va_locs (each string in a live block or a live side-stack frame of the entry) *)
  assert (VARGS : forall mm mdd rs, AR SEGS B ly S2 W mm mdd ->
    (forall a,
      ((exists p k, In (p, k) (ablocks B ly S) /\ p <= a < p + req_size k) \/
       (exists cid pos, In (cid, pos) (frames S) /\ (in_zr a (frame_rng ly (cid, pos)) \/
          in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)))) ->
      ~ (c + 0x34cc <= a < c + 0x34d0) -> ~ (c + 11912 + 200 * nr <= a < c + 11912 + 200 * nr + 200) ->
      rdW W mm a = rdW W mem a) ->
    Forall (fun r => (ly_stk_lo ly <= fst r /\ fst r + snd r <= sp0) \/
      (c + 11912 + 200 * nr <= fst r /\ fst r + snd r <= c + 11912 + 200 * nr + 200)) rs ->
    forall xs vs,
    sa_va_args (rdW W mem) [(ly_stk_lo ly, sp0);
      (seg_spec.refusal_addr c (length (rc_refusal rcs)),
       seg_spec.refusal_addr c (length (rc_refusal rcs)) + seg_spec.RC_REFUSAL_LEN);
      (c + seg_spec.RC_REFUSED, c + seg_spec.RC_REFUSED + 4)] vs xs ->
    refuse_va_locs (fun q n => sa_heap B ly S q n \/ sa_fframe ly S q n) vs xs ->
    refuse_pft.ffr_args (rdW W mm) rs (map (fun r : word => bv_unsigned r) vs) xs).
  { clear - LAWS HAR Eab Hfrs2 Hpbapp Hpb1 Hpb2 C1 C2 C3 C4 C5 Hceil Hslo Hshi H47 Hstk0 Enr Hn7 Hnr0 Hkb0 Hkbr.
    intros mm mdd rs HARx KSx Hrs xs. induction xs as [|x xs IH]; intros vs Hva Hloc; [destruct vs; exact I |].
    destruct vs as [|r vs]; [destruct Hva |].
    cbn [sa_va_args] in Hva. destruct Hva as (Hx & Hva).
    cbn [map refuse_pft.ffr_args].
    destruct x as [s | z]; cbn [sa_va_arg refuse_va_locs] in Hx, Hloc.
    2: { split; [exact Hx | exact (IH vs Hva Hloc)]. }
    destruct Hloc as (Hloc & Hloc'). split; [| exact (IH vs Hva Hloc')].
    destruct Hx as (Hr0 & ((Hzs & Hn0) & Htl) & Hlen & (Hsa0 & Hsa1 & Hsam & Hsra & Hshv) & Hap).
    set (wq := bv_unsigned r) in *.
    pose proof (bv_unsigned_in_range 64 r) as Hwr. change (bv_modulus 64) with (2 ^ 64) in Hwr. fold wq in Hwr.
    unfold sa_apart_all, seg_spec.cstr_span in Hap.
    pose proof (proj1 (Forall_forall _ _) Hap) as Hapf.
    pose proof (Hapf _ (or_introl eq_refl)) as Ap1. pose proof (Hapf _ (or_intror (or_introl eq_refl))) as Ap2.
    pose proof (Hapf _ (or_intror (or_intror (or_introl eq_refl)))) as Ap3. clear Hapf.
    cbv beta in Ap1, Ap2, Ap3. cbn [fst snd] in Ap1, Ap2, Ap3.
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_REFUSED in Ap2, Ap3.
    pose proof (Z.mod_pos_bound (- (wq + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hsp8.
    (* the string, its NUL: bytes of its block or frame, apart from c->refused and the slot *)
    assert (KSs : forall a, wq <= a <= wq + Z.of_nat (length s) -> rdW W mm a = rdW W mem a).
    { intros a Ha. apply KSx; [| lia | lia].
      destruct Hloc as [(b & m & Hbm & Hb1 & Hb2) | (cid & pos & Hin & _ & Hf1 & Hf2)]; [left | right].
      - exists b, m. split; [exact Hbm |].
        destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (_ & _ & _ & _ & _ & _ & Hm).
        pose proof (req_size_pos m (proj1 Hm)). lia.
      - exists cid, pos. split; [exact Hin |]. left. unfold in_zr, frame_rng. cbn [fst snd]. lia. }
    assert (Hbyte : Forall (fun v => 0 <= v < 256) s).
    { apply Forall_forall. intros v Hv. destruct (In_nth s v 0 Hv) as (i & Hi & Hni).
      pose proof (Hzs i ltac:(rewrite length_app; cbn [length]; lia)) as Ebz.
      rewrite app_nth1 in Ebz by exact Hi. rewrite Hni in Ebz. exact (sa_aview_rng _ _ _ _ _ Ebz). }
    split; [lia |].
    split.
    { split; [split; [| exact Hn0] |].
      - intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
        rewrite KSs by lia. exact (Hzs i Hi).
      - intros x Hx. pose proof (Z.mod_pos_bound (wq + Z.of_nat (length s)) 8 ltac:(lia)) as Hm8.
        assert (Hxs : wq <= x < wq + Z.of_nat (length s) + 1 + (- (wq + Z.of_nat (length s) + 1)) mod 8)
          by (clear - Hx; Z.div_mod_to_equations; lia).
        destruct Hloc as [(b & m & Hbm & Hb1 & Hb2) | (cid & pos & Hin & _ & Hf1 & Hf2)].
        + exact (YG0d_tail.AR_block_word_vis SEGS B ly S2 W mm mdd b m (wq + Z.of_nat (length s)) x HARx
            ltac:(rewrite Eab; exact Hbm) ltac:(destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (_ & _ & _ & _ & _ & _ & Hm);
                    pose proof (req_size_pos m (proj1 Hm)); lia) ltac:(lia)).
        + destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb).
          assert (Hx' : x < frame_addr ly cid pos + fs_frame_bytes cid)
            by (clear - Hx Hf2 Hfa64 Hfb64; Z.div_mod_to_equations; lia).
          rewrite KSx; [exact (Htl x Hx) | right; exists cid, pos; split; [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; lia]
            | lia | lia]. }
    split; [exact (refuse_f.rf_pos s Hbyte Hn0) |].
    split; [exact Hlen |].
    destruct Hloc as [(b & m & Hbm & Hb1 & Hb2) | (cid & pos & Hin & Hcid & Hf1 & Hf2)].
    - (* a string in a live block: its shadow and slack from AR at mm *)
      destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (_ & _ & _ & _ & _ & _ & Hm).
      pose proof (req_size_pos m (proj1 Hm)) as Hreq.
      assert (Hbm2 : In (b, m) (ablocks B ly S2)) by (rewrite Eab; exact Hbm).
      split; [split; [exact Hsa0 |]; split; [exact Hsa1 |]; split; [exact Hsam |]; split |].
      + exact (range_addressable_of_block SEGS B LAWS ly S2 W mm mdd b m wq (Z.of_nat (length s) + 1) HARx Hbm2 ltac:(lia) ltac:(lia)).
      + intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S2 W mm mdd b m wq (Z.of_nat (length s) + 1) HARx Hbm2 ltac:(lia) ltac:(lia) ltac:(lia)).
      + split; [exact (amem8_of_block SEGS B LAWS ly S2 W mm mdd b m wq (Z.of_nat (length s)) HARx Hbm2 ltac:(lia) ltac:(lia) ltac:(lia)) |].
        eapply Forall_impl; [| exact Hrs]. intros [x0 y0] Hxy. unfold zdisjoint, seg_spec.cstr_span. cbn [fst snd] in *. lia.
    - (* a string in a live side-stack frame: its shadow kept with the frame *)
      destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf4096 & Hfceil & Hfapp).
      destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hfa64 & Hfb64 & Hfb).
      assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
      split; [split; [exact Hsa0 |]; split; [exact Hsa1 |]; split; [exact Hsam |]; split |].
      + intros x Hx. destruct (Hsra x Hx) as (sv & Hsv & Hok). exists sv. split; [| exact Hok].
        rewrite KSx; [exact Hsv | | |].
        * right. exists cid, pos. split; [exact Hin |]. right. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
          clear - Hx Hf1 Hf2 Hfa64 Hfb64 Hfb. Z.div_mod_to_equations. lia.
        * unfold shadow_of_addr, SHADOW_OFF. unfold rnam, kLowShadowBeg, kHighMemBeg in Hpbapp.
          pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
          lia.
        * unfold shadow_of_addr, SHADOW_OFF. unfold rnam, kLowShadowBeg, kHighMemBeg in Hpbapp.
          pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
      + intros _. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W mm mdd cid pos wq (Z.of_nat (length s) + 1) HARx Hin2 ltac:(lia) ltac:(lia) ltac:(lia)).
      + split; [unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *;
                pose proof asan_consts as (AC1 & _); lia |].
        eapply Forall_impl; [| exact Hrs]. intros [x0 y0] Hxy. unfold zdisjoint, seg_spec.cstr_span. cbn [fst snd] in *. lia. }
  (* the format f: one of the 17, at its literal address below the GOT word *)
  assert (FPB : 0x10000 <= fp /\ fp + Z.of_nat (length f) + 1 <= gotwA).
  { rewrite Hfplit. clear - Hf. unfold seg_spec.REFUSE_FORMATS in Hf.
    repeat (destruct Hf as [<- | Hf]; [split; apply Z.leb_le; vm_compute; reflexivity |]). destruct Hf. }
  (* B1-B3 store nothing: every window read-only *)
  rrewin HS 10%nat 13512 13516 13516 ltac:(intros o Ho; rb_lia AMB).
  rrewin HS 2%nat (-160) (-160) (-160) ltac:(intros o Ho; rb_lia AMB).
  rrewin HS 2%nat (-144) (-144) (-144) ltac:(intros o Ho; rb_lia AMB).
  rrewin HS 33%nat 8 8 8 ltac:(intros o Ho; rb_lia AMB).
  Ltac rb_ro := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
    repeat (apply awr_ok_cons_ro; [cbn; clear; lia|]); apply awr_ok_nil.
  Ltac rb_awro := try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => rb_ro end).
  Ltac rb_ro_eq HF := lazymatch type of HF with frame_of _ ?rs _ _ =>
    let H := fresh "Hmq" in pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as H end.
  Ltac rb_reg HS r Q := lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
    pose proof (st_ok_restrict_reg SEGS _ Ex ss _ r HS) as Q;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q end.
  (* B1 (0x88f00-0x88f34): check 3, c->reading[0], dst = c + 0x2e88 + 200 n, the `where` branch *)
  paj_run_tok RUN HS HJ2 SHOK Bspan; rb_awro.
  rb_ro_eq HF.
  (* TAIL: the body from the k test's fall-through (0x88f80, the state ss_tl) to refuse's return, proved once for
     the four where / line leaves; what differs between them is the FP state and the registers the address
     snprintf returned, its memory and model, and the state machine after the k test *)
  let Ew := rb_env HS in
  lazymatch goal with |- SRr _ _ _ (apost_baseF _ _ _ _ _ _ _ _ _ _ ?K ?Q) =>
  assert (TAIL : forall fx1 regs5 mem5 ms5 mdT,
    PaFx.fxrel fx fx1 ->
    st_ok_pi (fx := fx1) SEGS VAL (havoc Ew 1100 (map (getr regs5) CLOB)) ss_tl (restrict (w_H W) ms5) ->
    ajournal SEGS B STK_refuse sp0 (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms5) mdT 0 ->
    getr regs5 10 = w64 (Z.of_nat (length T1)) ->
    (forall i, 0 <= i < RtPFShared.sn_len (200 - 1) T1 ->
       rdW W mem5 (c + 11912 + 200 * nr + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (200 - 1) T1) 0)) ->
    (forall a, 0 <= a < 2 ^ 64 ->
       ~ (c + 11912 + 200 * nr <= a < c + 11912 + 200 * nr + RtPFShared.sn_len (200 - 1) T1) ->
       ~ (sp0 + (rsp1 sp0 - sp0) - RtPFCmd.CMD_SNP_K <= a < sp0 + (rsp1 sp0 - sp0)) ->
       rdW W mem5 a = rdW W (ms_mem ms1) a) ->
    (forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms5) a = rdW W mem5 a) ->
    SRr SEGS W (mkCfg ms5 mdT) (apost_baseF (fx := fx1) SEGS B STK_refuse (refuse_W c rcs) regs ly S W mem md K Q)) end.
  { clear HS HJ2 HF HFr HG.
    intros fx1 regs5 mem5 ms5 mdT Hfx1 HS HJ3 HK10 HBY HKP UNk.
    pose proof (SRr_run_pi_AJ (fx := fx1) B LAWS) as RUNP1.
    pose proof (SRr_run_pi_AJ_call (fx := fx1) B LAWS) as RUNC1.
    let Ex := rb_env HS in
    assert (HEI8 : img_env VAL A_LIM Ex)
      by (repeat first [apply img_env_havoc_hi | apply img_env_ewset_hi]; first [eassumption | unfold A_LIM; rb_lia AMB]).
    assert (CR0 : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) RtPFCmd.CMD_SNP_CR)
      by (unfold RtPFCmd.CMD_SNP_CR; repeat constructor; cbn [fst snd]; rb_lia AMB).
  (* ===== 0x88f80-0x88fa4: ap's shadow unpoisoned (SH + 4 := 0), va_start (F + 0x20 := s0 + 8), the vsnprintf
     arguments, to the call; a plain run (it stores a shadow byte) with the two windows open ===== *)
  Ltac rb_Y HS V2 V33 V1028 V1041 V10 sp0 F c :=
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      assert (Y2 : bv_unsigned (ew Ex 2) = sp0) by (rb_evE; exact V2);
      assert (Y33 : bv_unsigned (ew Ex 33) = rsp1 sp0) by (rb_evE; exact V33);
      assert (Y1028 : bv_unsigned (ew Ex 1028) = F) by (rb_evE; exact V1028);
      assert (Y1041 : bv_unsigned (ew Ex 1041) = SB + F / 8) by (rb_evE; exact V1041);
      assert (Y10 : bv_unsigned (ew Ex 10) = c) by (rb_evE; exact V10)
    | st_ok _ ?Ex _ _ =>
      assert (Y2 : bv_unsigned (ew Ex 2) = sp0) by (rb_evE; exact V2);
      assert (Y33 : bv_unsigned (ew Ex 33) = rsp1 sp0) by (rb_evE; exact V33);
      assert (Y1028 : bv_unsigned (ew Ex 1028) = F) by (rb_evE; exact V1028);
      assert (Y1041 : bv_unsigned (ew Ex 1041) = SB + F / 8) by (rb_evE; exact V1041);
      assert (Y10 : bv_unsigned (ew Ex 10) = c) by (rb_evE; exact V10) end.
  all: rb_Y HS V2 V33 V1028 V1041 V10 sp0 F c.
  all: destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos (proj1 HJ3) Hfin2) as (_ & _ & HFP5 & HFSP5).
  all: fold F in HFP5, HFSP5.
  all: change (fs_frame_bytes 0) with 64 in HFP5, HFSP5.
  all: change (64 / 8) with 8 in HFSP5.
  all: rrewin HS 1041%nat 0 4 5 ltac:(intros o Ho; rewrite Y1041; apply (apresent_writable SEGS); exact (proj1 (HFSP5 o ltac:(rb_lia AMB)))).
  all: rrewin HS 1028%nat 32 32 40 ltac:(intros o Ho; rewrite Y1028; apply (apresent_writable SEGS); exact (proj1 (HFP5 (F + o) ltac:(rb_lia AMB)))).
  all: paj_run_shc RUNP1 RUNC1 HS HJ3.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => r_awr Y2 Y33 Y1028 Y1041 Y10 INF INF sp0 F c end).
  all: pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => (SB + F / 8 + 4 <= a < SB + F / 8 + 5) \/ (F + 32 <= a < F + 40)) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?Y2, ?Y33, ?Y1028, ?Y1041, ?Y10 in Hrr; clear - Hrr; lia |]);
    destruct Hin)) as UNv.
  all: cbn [ms_mem restrict mkst] in UNv.
  all: clear HF HFr HG Y2 Y33 Y1028 Y1041 Y10.
  (* ===== the vsnprintf call (0x88fa4): vsnprintf (slot + k, 200 - k, fp, sp0 - 40), the va_list over the spilled
     a3 .. a7 (s0 + 8 = sp0 - 40) ===== *)
  all: lazymatch type of HS with
       | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msV
       | st_ok _ _ _ (restrict _ ?m) => rename m into msV end.
  all: pmkst HS.
  Ltac rb_reg2 HS r Q :=
    lazymatch type of HS with
    | st_ok _ ?Ex ?ss _ =>
      pose proof (st_ok_restrict_reg SEGS _ Ex ss _ r HS) as Q;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q
    | st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as Q;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q end;
    cbn [ms_regs restrict mkst] in Q.
  all: prreg HS (1%bv : bv 5) Q1v.
  all: rb_reg2 HS (2%bv : bv 5) Q2v. all: rb_reg2 HS (3%bv : bv 5) Q3v. all: rb_reg2 HS (4%bv : bv 5) Q4v.
  all: rb_reg2 HS (10%bv : bv 5) Q10v. all: rb_reg2 HS (11%bv : bv 5) Q11v. all: rb_reg2 HS (12%bv : bv 5) Q12v.
  all: rb_reg2 HS (13%bv : bv 5) Q13v.
  (* the atoms the four argument registers read, at this state's environment *)
  all: assert (E12 : ew E 12 = getr regs 12)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; rb_lia AMB); exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)).
  all: let Ex := rb_env HS in
    assert (Z2 : bv_unsigned (ew Ex 2) = sp0) by (rb_evE; exact V2);
    assert (Z10 : bv_unsigned (ew Ex 10) = c) by (rb_evE; exact V10);
    assert (Z1042 : bv_unsigned (ew Ex 1042) = nr) by (rb_evE; exact V1042);
    assert (Z12 : bv_unsigned (ew Ex 12) = fp)
      by (rb_evE; rewrite AG3, AG2 by rb_lia AMB; rewrite E12, H12; unfold w64; apply unsigned_lit_small; rb_lia AMB);
    assert (Z1104 : bv_unsigned (ew Ex 1104) = Z.of_nat (length T1))
      by (rb_evE; change 1104%nat with (1100 + 4)%nat;
          rewrite (ew_havoc_new _ 1100 (map (getr regs5) CLOB) 4 (Z_to_bv 64 0)) by (cbn; rb_lia AMB); cbn [nth map CLOB];
          rewrite HK10; unfold w64; apply unsigned_lit_small; rb_lia AMB).
  all: assert (USW : forall Ex op a b, U Ex (SAluw op a b) =
      bv_wrap 64 (bv_swrap 32 (zalu_raw 31 32 op (U Ex a mod 2 ^ 32) (U Ex b mod 2 ^ 32))))
    by (intros Ex op a b; rewrite U_of_S, S_SAluw; reflexivity).
  Ltac rb_uval USW BND := rewrite denot_lit_U; unfold w64; f_equal;
    repeat first [rewrite U_lit by lia | rewrite USW | rewrite U_SAlu | rewrite U_SMd | rewrite U_SExt | rewrite U_SOff];
    cbn [zalu_raw zmd_raw]; cbv iota;
    repeat match goal with Y : bv_unsigned (ew ?Ex ?n) = _ |- context [bv_unsigned (ew ?Ex ?n)] => rewrite Y end;
    try unfold zcanon; try unfold M64; try unfold bv_swrap; try unfold bv_wrap;
    try change (bv_modulus 64) with (2 ^ 64); try change (bv_modulus 32) with (2 ^ 32);
    try change (bv_half_modulus 32) with (2 ^ 31); try change (2 ^ Z.of_N 32) with (2 ^ 32);
    clear - BND; Z.div_mod_to_equations; lia.
  all: assert (BND : 4096 <= c <= 2 ^ 47 - 16616 /\ 0 <= nr <= 7 /\ 0 <= Z.of_nat (length T1) <= 108 /\
      2 ^ 46 <= sp0 <= 2 ^ 47 /\ 0 <= fp < 2 ^ 64) by rb_lia AMB.
  all: set (d2 := c + 11912 + 200 * nr + Z.of_nat (length T1)).
  all: set (n2 := 200 - Z.of_nat (length T1)).
  all: set (T2 := SegModel.fmt f args).
  all: assert (QD2 : getr (ms_regs msV) 10 = w64 d2)
    by (rewrite Q10v; subst d2; rb_uval USW BND).
  all: assert (QN2 : getr (ms_regs msV) 11 = w64 n2)
    by (rewrite Q11v; subst n2; rb_uval USW BND).
  all: assert (QF2 : getr (ms_regs msV) 12 = w64 fp)
    by (rewrite Q12v; rb_uval USW BND).
  all: assert (QA2 : getr (ms_regs msV) 13 = w64 (sp0 - 40))
    by (rewrite Q13v; rb_uval USW BND).
  all: assert (QSP2 : spZ (ms_regs msV) = sp0 + (rsp1 sp0 - sp0))
    by (unfold spZ; rewrite Q2v; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rb_evE; rewrite V33; rb_lia AMB).
  all: assert (QGP2 : getr (ms_regs msV) 3 = w64 (as_gp B))
    by (rewrite Q3v; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rb_evE; rewrite AG3, AG2, E3 by rb_lia AMB; exact Hgp).
  all: assert (QTP2 : getr (ms_regs msV) 4 = w64 (as_tp B))
    by (rewrite Q4v; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rb_evE; rewrite AG3, AG2, E4 by rb_lia AMB; exact Htp).
  all: assert (QRA2 : YK0s.ret_ok (getr (ms_regs msV) 1))
    by (rewrite Q1v; apply ret_ok_codeptr_v; [rb_lia AMB | reflexivity]).
  (* the call's journal, its AR state, the guard cells, the literals *)
  all: pose proof (proj1 HJ3) as HARv.
  all: pose proof (ROMJ _ _ HJ3) as ROMV.
  all: pose proof (SSPX _ _ _ _ _ HARv) as (SSPv1 & gcanv & SSPv2).
  (* the bytes of the entry's blocks and frames at the call, outside c->refused and the slot *)
  all: assert (KSV : forall a,
      ((exists p k, In (p, k) (ablocks B ly S) /\ p <= a < p + req_size k) \/
       (exists cid pos, In (cid, pos) (frames S) /\ (in_zr a (frame_rng ly (cid, pos)) \/
          in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)))) ->
      ~ (c + 0x34cc <= a < c + 0x34d0) -> ~ (c + 11912 + 200 * nr <= a < c + 11912 + 200 * nr + 200) ->
      rdW W (ms_mem msV) a = rdW W mem a)
    by (intros a Hloc Hnr Hns; destruct (LOCB a Hloc) as (Hb1 & Hb2 & Hb3);
        assert (Ha64 : 0 <= a < 2 ^ 64) by (revert Hb1; rb_zl AMB);
        rewrite (UNv a Ha64) by (intros [Q|Q]; [apply Hb2 | apply Hb3]; revert Q; clear; lia);
        rewrite (UNk a Ha64);
        rewrite HKP; [exact (KS1 a Hloc Hnr) | exact Ha64 | rewrite SNL1; revert Hns HT1l; clear; lia
                     | revert Hb1; rb_zl AMB]).
  (* the regions vsnprintf writes: its window below sp1 and the rest of the slot *)
  all: set (RSV := RtPFShared.snp_out RtPFSeg.SEG_VSN_K (spZ (ms_regs msV)) d2 (RtPFShared.sn_len (n2 - 1) T2)).
  all: assert (DST2 : forall a, d2 <= a < d2 + n2 ->
      awr_byte SEGS B STK_refuse sp0 (refuse_W c rcs) (ablocks B ly S) (ablocks B ly S2) (frames S) ly [(0, fpos)] a /\
      ~ (sp0 + (rsp1 sp0 - sp0) - RtPFSeg.SEG_VSN_K <= a < sp0 + (rsp1 sp0 - sp0)))
    by (intros a Ha; subst d2 n2; split; [exact (proj1 (DST1 a ltac:(rb_lia AMB))) |];
        first [exact (proj2 (DST1 a ltac:(rb_lia AMB))) | unfold RtPFSeg.SEG_VSN_K, RtPFCmd.CMD_SNP_K in *; rb_lia AMB]).
  all: assert (PWR2 : forall a, d2 <= a < d2 + n2 -> inFP (refuse_W c rcs) a ->
      (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ sp0 <= a < ly_top ly ->
      writable_at SEGS (mrestrict (w_H W) (ms_mem msV)) a)
    by (intros a Ha _ [[_ Hi] | Hs]; exfalso; subst d2 n2;
        [exact (blk_img SEGS B LAWS ly S W mem md pb kb a HAR Hpbin ltac:(rb_lia AMB) Hi) | rb_lia AMB]).
  all: pose proof (HADDRJ _ _ d2 n2 HARv ltac:(subst d2 n2; rb_lia AMB) ltac:(subst d2 n2; rb_lia AMB) ltac:(subst d2 n2; rb_lia AMB))
    as (_ & _ & _ & RAD2 & HUL2').
  all: pose proof (HUL2' ltac:(subst n2; rb_lia AMB)) as HUL2. all: clear HUL2'.
  all: assert (HKe2 : ESTACK <= RtPFSeg.SEG_VSN_K) by (unfold RtPFSeg.SEG_VSN_K; rb_lia AMB).
  all: assert (Hbud2 : RtPFSeg.SEG_VSN_K - (rsp1 sp0 - sp0) <= STK_refuse) by (unfold RtPFSeg.SEG_VSN_K; rewrite FFS, Hes; rb_lia AMB).
  all: destruct (refuse_pft.r_snp_pre SEGS B LAWS Hsegs RtPFSeg.SEG_VSN_K W (ms_regs msV) (ms_mem msV) STK_refuse sp0
      (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 _ 0 d2 n2 T2 (rsp1 sp0 - sp0)
      (getr (ms_regs msV) 1) HJ3 ltac:(subst n2; rb_lia AMB) QSP2 Ho16 Hneg HKe2 Hbud2 QGP2 QTP2 eq_refl QRA2 DST2 PWR2 RAD2 HUL2)
    as ((HEP2 & Hslo2 & Hscr2) & Hlen2 & _ & HDEST2 & HRAD2l & HHULL2l).
  (* the variadic words: a3 .. a7 spilled at sp0 - 40 .. sp0 - 8 (the stack region's chunks) *)
  all: lazymatch type of HS with
    | st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let i := eval vm_compute in (r_find (ss_mem ssx) 2%nat (-144) 0) in
      let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HRS
    | st_ok _ ?Ex ?ssx ?msx =>
      let i := eval vm_compute in (r_find (ss_mem ssx) 2%nat (-144) 0) in
      let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      pose proof (st_ok_region_nth (segs := SEGS) Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as HRS end.
  all: cbn [ms_mem restrict mkst] in HRS.
  all: assert (EA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        subst E; rewrite Eimg_low by (unfold A_TEXT; rb_lia AMB); apply ew_Ereg_nat; exact Hn).
  all: lazymatch type of HRS with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) _ _ _ _ ?cs) =>
    assert (WD : forall off n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 1024)%nat ->
      In (YP09.mkChunk off (CVal 8 (SOff n 0))) cs ->
      rdword (rdW W (ms_mem msV)) (sp0 + off) = Some (bv_unsigned (getr regs r)))
    by (intros off n r Hn Hn1 Hin; destruct HRS as (_ & _ & _ & Hcs);
        pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck; cbn [YP09.r_base base_val] in Hck;
        assert (HB2 : bv_unsigned (ew Ex 2) = sp0) by (rb_evE; exact V2);
        rewrite HB2 in Hck;
        pose proof (val_of_chunk_any SEGS Ex _ sp0 off 8%N (SOff n 0) Hck ltac:(rb_lia AMB)) as Hv;
        assert (HVn : bv_unsigned (sv_denot Ex (SOff n 0)) mod 2 ^ (8 * Z.of_N 8) = bv_unsigned (getr regs r))
          by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rb_evE; rewrite AG3, AG2 by rb_lia AMB; rewrite (EA n r Hn);
              apply Z.mod_small; pose proof (bv_unsigned_in_range 64 (getr regs r)) as R64;
              change (bv_modulus 64) with (2 ^ 64) in R64; exact R64);
        rewrite HVn in Hv;
        apply (rdword_of_val_mem SEGS (w_H W) (ms_mem msV) (sp0 + off) _ Hv);
        pose proof (bv_unsigned_in_range 64 (getr regs r)) as R64; change (bv_modulus 64) with (2 ^ 64) in R64; exact R64) end.
  all: set (WS := map (fun r : word => bv_unsigned r) [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17]).
  all: assert (WORDS : RtPFShared.words_at (rdW W (ms_mem msV)) (sp0 - 40) WS)
    by (intros i Hi; subst WS; cbn [length map] in Hi;
        destruct i as [|[|[|[|[|i]]]]]; cbn [nth map];
        [ replace (sp0 - 40 + 8 * Z.of_nat 0) with (sp0 + -40) by (clear; lia); apply (WD (-40) 13%nat 13%bv)
        | replace (sp0 - 40 + 8 * Z.of_nat 1) with (sp0 + -32) by (clear; lia); apply (WD (-32) 14%nat 14%bv)
        | replace (sp0 - 40 + 8 * Z.of_nat 2) with (sp0 + -24) by (clear; lia); apply (WD (-24) 15%nat 15%bv)
        | replace (sp0 - 40 + 8 * Z.of_nat 3) with (sp0 + -16) by (clear; lia); apply (WD (-16) 16%nat 16%bv)
        | replace (sp0 - 40 + 8 * Z.of_nat 4) with (sp0 + -8) by (clear; lia); apply (WD (-8) 17%nat 17%bv)
        | revert Hi; clear; lia ];
        first [reflexivity | solve [cbn [In]; repeat (first [left; reflexivity | right])] | (clear; lia)]).
  (* the text: SegModel.fmt f args through FFR at RtPFSeg.FR_seg (refuse_pft.r_ffr_seg) *)
  all: assert (FFMT : forall rs, Forall (fun r => fst r + snd r <= 0x10000 \/ kImgEnd <= fst r) rs ->
      refuse_pft.ffr_fmt SEGS B gotwA (rdW W (ms_mem msV)) rs fp f)
    by (intros rs Hrs; destruct (LITJ _ _ HJ3 fp f HFLIT) as (Hs & Ha);
        pose proof HFLIT as (_ & _ & _ & _ & Himg); destruct FPB as (Hfq1 & Hfq2);
        split; [rb_lia AMB |]; split; [exact Hfq2 |]; split; [exact Hs |]; split; [exact Ha |]; split; [exact Himg |];
        split; [unfold amem_range, kLowMemEnd, gotwA in *; rb_lia AMB |];
        eapply Forall_impl; [| exact Hrs]; intros [x0 y0] Hxy; unfold zdisjoint, seg_spec.cstr_span in *; cbn [fst snd] in *;
        pose proof (Z.mod_pos_bound (- (fp + Z.of_nat (length f) + 1)) 8 ltac:(rb_lia AMB)); unfold gotwA, kImgEnd in *; rb_lia AMB).
  all: assert (RSOKV1 : Forall (fun r => fst r + snd r <= 0x10000 \/ kImgEnd <= fst r) RSV)
    by (pose proof (OFFI d2 (RtPFShared.sn_len (n2 - 1) T2) ltac:(subst d2; rb_lia AMB) ltac:(subst d2 n2; rb_lia AMB) ltac:(rb_lia AMB)) as HO;
        subst RSV; unfold RtPFShared.snp_out; rewrite QSP2;
        apply Forall_cons; [cbn [fst snd]; right; unfold RtPFSeg.SEG_VSN_K, kImgEnd in *; rewrite FFS in Hbud; rb_lia AMB |];
        apply Forall_cons; [cbn [fst snd]; exact HO | apply Forall_nil]).
  all: assert (RSOKV2 : Forall (fun r => (ly_stk_lo ly <= fst r /\ fst r + snd r <= sp0) \/
      (c + 11912 + 200 * nr <= fst r /\ fst r + snd r <= c + 11912 + 200 * nr + 200)) RSV)
    by (subst RSV; unfold RtPFShared.snp_out; rewrite QSP2;
        apply Forall_cons; [cbn [fst snd]; left; unfold RtPFSeg.SEG_VSN_K in *; rewrite FFS in Hbud; rb_lia AMB |];
        apply Forall_cons; [cbn [fst snd]; right; subst d2 n2; rb_lia AMB | apply Forall_nil]).
  all: assert (FARGS : refuse_pft.ffr_args (rdW W (ms_mem msV)) RSV WS args)
    by (subst WS; exact (VARGS _ _ RSV HARv KSV RSOKV2 args _ HVA HVLOC)).
  all: assert (ARGOK : forall rd rs ws xs, refuse_pft.ffr_args rd rs ws xs -> Forall refuse_f.rf_argok xs)
    by (intros rd rs ws xs; revert ws; induction xs as [|x xs IH]; intros ws H; [apply Forall_nil |];
        destruct ws as [|wq ws]; [cbn in H; destruct H |]; cbn [refuse_pft.ffr_args] in H; destruct H as (Hx & Hr);
        apply Forall_cons; [| exact (IH ws Hr)];
        destruct x as [s | z]; cbn [refuse_pft.ffr_arg refuse_f.rf_argok] in *;
        [ destruct Hx as (_ & _ & Hb & Hl & _);
          split; [intros Hin; pose proof (proj1 (Forall_forall _ _) Hb 0 Hin) as Hq; cbv beta in Hq; rb_lia AMB |];
          split; [eapply Forall_impl; [| exact Hb]; intros v Hv; cbv beta in Hv |- *; rb_lia AMB | exact Hl]
        | rb_lia AMB ]).
  all: destruct (refuse_f.rf_txt f args ltac:(right; right; exact Hf) Hkinds (ARGOK _ _ _ _ FARGS)) as (HT2z & HT2b & HT2).
  all: fold T2 in HT2, HT2z, HT2b.
  all: assert (FFV : RtPFSeg.FR_seg RtPFCmd.CMD_IMG_LO gotwA (rdW W (ms_mem msV)) RSV fp WS T2)
    by (exact (refuse_pft.r_ffr_seg SEGS B gotwA (rdW W (ms_mem msV)) RSV fp f WS args
                       ltac:(unfold refuse_pft.REFUSE_ALL_FMTS; right; right; exact Hf) Hkinds (FFMT RSV RSOKV1) FARGS)).
  (* the remaining premises of row 5 *)
  all: assert (IMGDV : forall xi wi, 0x10000 <= xi -> xi + wi <= kImgEnd -> Forall (zdisjoint (xi, wi)) RSV)
    by (intros xi wi Hx1 Hx2;
        pose proof (OFFI d2 (RtPFShared.sn_len (n2 - 1) T2) ltac:(subst d2; rb_lia AMB) ltac:(subst d2 n2; rb_lia AMB) ltac:(rb_lia AMB)) as HO;
        subst RSV; unfold RtPFShared.snp_out; rewrite QSP2; unfold RtPFSeg.SEG_VSN_K, kImgEnd in *; rewrite FFS in Hbud;
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rb_lia AMB |];
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rb_lia AMB | apply Forall_nil]).
  all: assert (CR1V : Forall (fun r => Forall (zdisjoint r) RSV) RtPFCmd.CMD_SNP_CR)
    by (unfold RtPFCmd.CMD_SNP_CR; constructor; [apply IMGDV; unfold kImgEnd; rb_lia AMB |];
        constructor; [apply IMGDV; unfold kImgEnd; rb_lia AMB | constructor]).
  all: assert (PWDV : pairwise zdisjoint RSV)
    by (subst RSV; unfold RtPFShared.snp_out; rewrite QSP2; cbn [pairwise]; split; [| split; [apply Forall_nil | exact I]];
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold RtPFSeg.SEG_VSN_K in *; rewrite FFS in Hbud; subst d2 n2; rb_lia AMB
                           | apply Forall_nil]).
  all: assert (APD : Forall (zdisjoint (sp0 - 40, 8 * Z.of_nat (length WS))) RSV)
    by (subst WS RSV; cbn [length map]; unfold RtPFShared.snp_out; rewrite QSP2; unfold RtPFSeg.SEG_VSN_K in *;
        rewrite FFS in Hbud;
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rb_lia AMB |];
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; subst d2 n2; rb_lia AMB | apply Forall_nil]).
  all: pose proof (amem8_of_block SEGS B LAWS ly S2 W (ms_mem msV) _ pb kb d2 (RtPFShared.sn_len (n2 - 1) T2)
      HARv HpbT ltac:(subst d2 n2; rb_lia AMB) ltac:(subst d2 n2; rb_lia AMB) ltac:(subst d2 n2; rb_lia AMB)) as AMR2.
  all: pose proof (VSNP fx1) as VSNPx; unfold RtPFSeg.seg_avsnprintf_realizes in VSNPx.
  all: eapply SRr_bind;
    [ apply (refuse_pft.r_snp_post SEGS B LAWS Hsegs RtPFSeg.SEG_VSN_K (SIGMA SS___interceptor_trampoline_vsnprintf) W
        (ms_regs msV) (ms_mem msV) STK_refuse sp0 (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 _ 0
        d2 n2 T2 (rsp1 sp0 - sp0) (getr (ms_regs msV) 1) HJ3 eq_refl QSP2 Hneg Hbud2
        ltac:(rb_lia AMB) (fun a Ha => proj1 (DST2 a Ha)));
      exact (VSNPx ly S2 W (ms_regs msV) (ms_mem msV) _ d2 n2 fp (sp0 - 40) WS T2 gcanv
        HEP2 Hslo2 Hscr2 QD2 QN2 QF2 QA2 ROMV CR0 CR1V SSPv1 SSPv2
        ltac:(unfold gotwA; rb_lia AMB) ltac:(unfold gotwA; rb_lia AMB) ltac:(unfold guardA; rb_lia AMB) ltac:(unfold guardA; rb_lia AMB)
        (IMGDV gotwA 8 ltac:(unfold gotwA; rb_lia AMB) ltac:(unfold gotwA, kImgEnd; rb_lia AMB))
        (IMGDV guardA 8 ltac:(unfold guardA; rb_lia AMB) ltac:(unfold guardA, kImgEnd; rb_lia AMB))
        WORDS ltac:(rb_lia AMB) ltac:(subst WS; cbn [length map]; rb_lia AMB) APD FFV ltac:(subst n2; rb_lia AMB) HT2
        ltac:(subst d2; rb_lia AMB) ltac:(subst d2 n2; rb_lia AMB) PWDV HDEST2 ltac:(unfold amem_range in *; rb_lia AMB) HRAD2l HHULL2l
        ltac:(pose proof (OFFI d2 (RtPFShared.sn_len (n2 - 1) T2) ltac:(subst d2; rb_lia AMB) ltac:(subst d2 n2; rb_lia AMB) ltac:(rb_lia AMB));
              unfold zdisjoint; cbn [fst snd]; unfold RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI, kImgEnd in *; rb_lia AMB)
        (PaFx.fxrel_frm0 fx fx1 HFRM Hfx1)
        ltac:(rewrite QSP2; rb_lia AMB)
        ltac:(left; rewrite QSP2; unfold RtPFSeg.SEG_VSN_K in *; rewrite FFS in Hbud; subst d2 n2; rb_lia AMB)
        ltac:(subst WS; cbn [length map]; rb_lia AMB)
        AMR2)
    | ].
  (* ===== after vsnprintf: the FP state fx2, the symbolic state rebuilt ===== *)
  all: cbv beta; intros W3 c3 _ (-> & fx2 & regs6 & mem6 & md6 & Hfx2 & -> & HJ4 & HP4 & HK10b & HBY2 & HKP2 & HPR2 & HSM2).
  all: apply (PaFx.srr_apost_baseF_lift (fx := fx1) SEGS fx2); [exact Hfx2 |].
  all: assert (KEEPS2 : forall a, (c + 13512 <= a < c + 13520) \/ (SB + F / 8 <= a < SB + F / 8 + 8) \/
      (F <= a < F + 64) \/ (sp0 - 144 <= a < sp0) -> rdW W mem6 a = rdW W (ms_mem msV) a)
    by (intros a Ha; apply HKP2; subst d2 n2; revert Ha Hlen2; rb_zl AMB).
  all: let Ex := rb_env HS in
    assert (HEIv : img_env VAL A_LIM Ex)
      by (repeat first [apply img_env_havoc_hi | apply img_env_ewset_hi]; first [eassumption | unfold A_LIM; rb_lia AMB]).
  all: jafter_call_keep_hi HS 1130%nat regs6 (mrestrict (w_H W) mem6) HP4 [0;1;2;3;4;5]%nat HS2.
  all: match type of HS2 with ?A -> _ => assert (HQ : A) by (
         cbn [ms_mem restrict mkst]; repeat apply Forall_cons; try apply Forall_nil;
         (eapply region_kept_aview; [ rb_evE; first [exact V10 | exact V1041 | exact V1028 | exact V2]
           | intros ?a ?Ha; apply KEEPS2; rb_lia AMB | exact HPR2 ])); specialize (HS2 HQ); clear HQ end.
  all: rewrite <- (restrict_mkst_fx (fx := fx1)) in HS2.
  all: apply (PaFx.st_ok_pi_restrict_xfx fx1 fx2) in HS2.
  all: clear HS; rename HS2 into HS.
  all: rewrite Q1v.
  all: pose proof (paj_run_to (fx := fx2) B LAWS) as RUNTO2.
  all: pose proof (SRr_run_to_pi_AJ (fx := fx2) B LAWS) as RUNTOP2.
  all: let Ex := rb_env HS in
    assert (HEIw : img_env VAL A_LIM Ex)
      by (repeat first [apply img_env_havoc_hi | apply img_env_ewset_hi]; first [eassumption | unfold A_LIM; rb_lia AMB]);
    assert (ZSHC4 : range_addressable (rdW W mem6) SHADOW_OFF c 16616)
      by exact (range_addressable_of_block SEGS B LAWS ly S2 W mem6 _ pb kb c 16616 (proj1 HJ4) HpbT Hpb1 ltac:(rb_lia AMB));
    assert (UB4 : U Ex (SOff 32 0) = SHADOW_OFF)
      by (rewrite (U_atom Ex 32 SB); [reflexivity | rb_evE; rewrite AG3, AG2, E32 by rb_lia AMB; reflexivity | unfold SB; rb_lia AMB]);
    assert (UC4 : U Ex (SOff 10 0) = c)
      by (apply U_atom; [rb_evE; rewrite AG3, AG2 by rb_lia AMB; rewrite E10, H10; reflexivity | rb_lia AMB]);
    assert (SHOK4 : sh_ok SEGS (SOff 32 0) [mkSHE 10 0x34c8 0x34d0] Ex (mrestrict (w_H W) mem6))
      by (unfold sh_ok; repeat apply Forall_cons; try apply Forall_nil;
          eapply (shent_ok_of_range SEGS (w_H W) mem6 Ex (SOff 32 0) 10%nat c 16616 c 0x34c8 0x34d0 ZSHC4 UB4 UC4);
          [rb_lia AMB | rb_lia AMB | intros x Hx; unfold SHADOW_OFF; unfold rnam, kLowShadowBeg, kHighMemBeg in Hpbapp; rb_lia AMB]).
  (* 0x88fa8-0x88fbc: check 4 on c->n_refusals, n_refusals++ (`sw` into c + 0x34c8): a token run with that window
     open and the frame's windows closed, to the shadow store at 0x88fc0 *)
  all: rb_Y HS V2 V33 V1028 V1041 V10 sp0 F c.
  all: destruct (al_blocks _ _ LAWS _ _ _ _ _ pb kb (proj1 HJ4) HpbT) as (_ & _ & _ & _ & Hpbpres4 & _).
  all: rrewin HS 1041%nat 0 0 0 ltac:(intros o Ho; rb_lia AMB).
  all: rrewin HS 1028%nat 32 32 32 ltac:(intros o Ho; rb_lia AMB).
  all: rrewin HS 10%nat 13512 13512 13516
    ltac:(intros o Ho; rewrite Y10; apply (apresent_writable SEGS);
          first [exact (proj1 (Hpbpres4 (c + o) ltac:(rb_lia AMB))) | exact (Hpbpres4 (c + o) ltac:(rb_lia AMB))]).
  all: paj_run_to_tok RUNTO2 HS HJ4 SHOK4 Bspan 17036.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let INFN := fresh "INFN" in
    assert (INFN : forall a, c + 0x34c8 <= a < c + 0x34cc -> awr_byte SEGS B stk spx fp b0 bc fr0 lyx own a);
    [ intros ?a ?Ha; right; left; split;
      [ exists (c + seg_spec.RC_NREF, c + seg_spec.RC_NREF + 4);
        split; [unfold refuse_W; apply in_or_app; right; rewrite Hn8b; right; left; reflexivity
               | cbn [fst snd]; unfold seg_spec.RC_NREF; rb_lia AMB]
      | exists pb, kb; split; [exact HpbT | rb_lia AMB] ]
    | r_awr Y2 Y33 Y1028 Y1041 Y10 INF INFN sp0 F c ] end).
  all: pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c + 13512 <= a < c + 13516) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?Y2, ?Y33, ?Y1028, ?Y1041, ?Y10 in Hrr; clear - Hrr; lia |]);
    destruct Hin)) as UNr1.
  all: cbn [ms_mem restrict mkst] in UNr1.
  all: clear HF HFr HG Y2 Y33 Y1028 Y1041 Y10.
  all: lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  (* 0x88fc0: SH + 4 := 0xf8 (ap's shadow poisoned again), a plain run to the release 0x88fc4 *)
  all: rb_Y HS V2 V33 V1028 V1041 V10 sp0 F c.
  all: destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos (proj1 HJ4) Hfin2) as (_ & _ & HFP6 & HFSP6).
  all: fold F in HFP6, HFSP6.
  all: change (fs_frame_bytes 0) with 64 in HFP6, HFSP6.
  all: change (64 / 8) with 8 in HFSP6.
  all: rrewin HS 10%nat 13512 13516 13516 ltac:(intros o Ho; rb_lia AMB).
  all: rrewin HS 1041%nat 0 4 5 ltac:(intros o Ho; rewrite Y1041; apply (apresent_writable SEGS); exact (proj1 (HFSP6 o ltac:(rb_lia AMB)))).
  all: paj_run_to_shc RUNTOP2 HS HJ4 17040.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => r_awr Y2 Y33 Y1028 Y1041 Y10 INF INF sp0 F c end).
  all: pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => SB + F / 8 + 4 <= a < SB + F / 8 + 5) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?Y2, ?Y33, ?Y1028, ?Y1041, ?Y10 in Hrr; clear - Hrr; lia |]);
    destruct Hin)) as UNr2.
  all: cbn [ms_mem restrict mkst] in UNr2.
  all: clear HF HFr HG Y2 Y33 Y1028 Y1041 Y10.
  all: rrewin HS 1041%nat 0 0 0 ltac:(intros o Ho; rb_lia AMB).
  all: lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msR end.
  (* c->refused + 1 (the `sw` at 0x88ee4) and c->n_refusals + 1 (the `sw` at 0x88fb8): the chunks of atom 10's
     region at the release, read as the n >= 8 arm reads RR1 *)
  all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let i := eval vm_compute in (r_find (ss_mem ssx) 10%nat 13512 0) in
    let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS ltac:(vm_compute; reflexivity)) as HR10;
    cbn [ms_mem restrict] in HR10 end.
  all: lazymatch type of HR10 with region_ok _ ?Ex _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) =>
    pose proof (r_region_aval4 SEGS Ex _ _ 10%nat c cs lo hi wlo whi 13516 (SAlu ALU_ADD (SExt true 32 (SOff 1043 0)) (SLit 1))
      (bv_unsigned (Z_to_bv 64 (Z.land (rc_refused rcs + 2 ^ 31) (2 ^ 32 - 1) - 2 ^ 31 + 1))) HR10
      ltac:(rb_evE; exact V10) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(apply r_inc_denot; [rb_evE; exact E3_1043 | rb_lia AMB])) as VRr;
    pose proof (r_region_aval4 SEGS Ex _ _ 10%nat c cs lo hi wlo whi 13512 (SOff 1042 1) (nr + 1) HR10
      ltac:(rb_evE; exact V10) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
      ltac:(cbn [sv_denot]; rb_evE; rewrite E3_1042, unsigned_lit_small by rb_lia AMB; reflexivity)) as VRn end.
  all: clear HR10.
  all: assert (RR1 : rd32 (rdW W (ms_mem msR)) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1))
    by (intros k Hk;
        transitivity (Some (YG0f.le_byte (bv_unsigned (Z_to_bv 64 (Z.land (rc_refused rcs + 2 ^ 31) (2 ^ 32 - 1) - 2 ^ 31 + 1))) 4 k));
        [exact (VRr k Hk) | f_equal; exact (refuse_f.rf_sw_inc (rc_refused rcs) ltac:(rb_lia AMB) k Hk)]).
  all: assert (RN1 : rd32 (rdW W (ms_mem msR)) (c + seg_spec.RC_NREF) (Z.of_nat (length (rc_refusal rcs)) + 1))
    by (intros k Hk; rewrite <- Enr; exact (VRn k Hk)).
  all: clear VRr VRn.
  (* the message: snprintf's T1 ++ [0] at d, then vsnprintf's firstn (199 - |T1|) T2 ++ [0] at d2 = d + |T1| *)
  all: set (TX := T1 ++ firstn (Z.to_nat (199 - Z.of_nat (length T1))) T2).
  all: assert (LTX : Z.of_nat (length TX) = Z.of_nat (length T1) + Z.of_nat (length (firstn (Z.to_nat (199 - Z.of_nat (length T1))) T2)))
    by (subst TX; rewrite length_app; rb_lia AMB).
  all: assert (LF2 : (length (firstn (Z.to_nat (199 - Z.of_nat (length T1))) T2) <= Z.to_nat (199 - Z.of_nat (length T1)))%nat)
    by (rewrite length_firstn; rb_lia AMB).
  all: assert (SNL2 : RtPFShared.sn_len (n2 - 1) T2 = Z.of_nat (length (firstn (Z.to_nat (199 - Z.of_nat (length T1))) T2)) + 1)
    by (unfold RtPFShared.sn_len, RtPFShared.sn_bytes; subst n2;
        replace (Z.to_nat (200 - Z.of_nat (length T1) - 1)) with (Z.to_nat (199 - Z.of_nat (length T1))) by rb_lia AMB;
        rewrite length_app; cbn [length]; rb_lia AMB).
  all: assert (SNB2 : RtPFShared.sn_bytes (n2 - 1) T2 = firstn (Z.to_nat (199 - Z.of_nat (length T1))) T2 ++ [0])
    by (unfold RtPFShared.sn_bytes; subst n2;
        replace (Z.to_nat (200 - Z.of_nat (length T1) - 1)) with (Z.to_nat (199 - Z.of_nat (length T1))) by rb_lia AMB;
        reflexivity).
  all: assert (SNB1 : RtPFShared.sn_bytes (200 - 1) T1 = T1 ++ [0])
    by (unfold RtPFShared.sn_bytes; change (Z.to_nat (200 - 1)) with 199%nat; rewrite firstn_all2 by rb_lia AMB; reflexivity).
  (* the release memory against the vsnprintf memory, the snprintf memory and the entry memory *)
  all: assert (K6 : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 13512 <= a < c + 13516) -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 5) ->
      rdW W (ms_mem msR) a = rdW W mem6 a)
    by (intros a Ha H1 H2; rewrite (UNr2 a Ha H2); exact (UNr1 a Ha H1)).
  all: assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 5) -> ~ (F + 32 <= a < F + 40) ->
      rdW W (ms_mem msV) a = rdW W mem5 a)
    by (intros a Ha H1 H2; rewrite (UNv a Ha) by (intros [Q|Q]; [exact (H1 Q) | exact (H2 Q)]);
        exact (UNk a Ha)).
  all: assert (HZS : sa_zs (rdW W (ms_mem msR)) (seg_spec.refusal_addr c (length (rc_refusal rcs))) (TX ++ [0]))
    by (intros i Hi; rewrite length_app in Hi; cbn [length] in Hi;
        assert (Hia : 0 <= Z.of_nat i < 200) by (revert Hi LTX LF2 HT1l; clear; lia);
        replace (seg_spec.refusal_addr c (length (rc_refusal rcs)) + Z.of_nat i) with (c + 11912 + 200 * nr + Z.of_nat i)
          by (unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN; rewrite Enr; rb_lia AMB);
        destruct (Nat.lt_ge_cases i (length T1)) as [Hlt | Hge];
        [ rewrite K6 by (revert Hia; rb_zl AMB);
          rewrite HKP2 by (subst d2 n2; revert Hia Hlt Hlen2; rb_zl AMB);
          rewrite K5 by (revert Hia; rb_zl AMB);
          rewrite (HBY (Z.of_nat i) ltac:(rewrite SNL1; rb_lia AMB)); rewrite SNB1, Nat2Z.id;
          subst TX; rewrite <- app_assoc; rewrite !app_nth1 by (rewrite ?length_app; cbn [length]; rb_lia AMB); reflexivity
        | replace (c + 11912 + 200 * nr + Z.of_nat i) with (d2 + Z.of_nat (i - length T1)) by (subst d2; rb_lia AMB);
          rewrite K6 by (subst d2; revert Hia Hge; rb_zl AMB);
          rewrite (HBY2 (Z.of_nat (i - length T1)) ltac:(rewrite SNL2; rb_lia AMB)); rewrite SNB2, Nat2Z.id;
          subst TX; rewrite <- app_assoc; rewrite (app_nth2 T1) by rb_lia AMB; reflexivity ]).
  all: assert (HKR : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
      ~ (seg_spec.RC_NREF <= i < seg_spec.RC_NREF + 4) ->
      ~ (seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) <= i <
         seg_spec.RC_REFUSAL + 200 * Z.of_nat (length (rc_refusal rcs)) + Z.of_nat (length TX) + 1) ->
      rdW W (ms_mem msR) (c + i) = rdW W mem (c + i))
    by (intros i Hi H1 H2 H3;
        unfold seg_spec.SEG_C_SIZE, seg_spec.RC_REFUSED, seg_spec.RC_NREF, seg_spec.RC_REFUSAL in *;
        assert (Hn3 : ~ (c + 11912 + 200 * nr <= c + i < c + 11912 + 200 * nr + Z.of_nat (length TX) + 1))
          by (rewrite Enr; rb_lia AMB);
        rewrite K6 by (revert Hi H2; rb_zl AMB);
        rewrite HKP2 by (subst d2 n2; rewrite ?SNL2; revert Hi Hn3 LTX; rb_zl AMB);
        rewrite K5 by (revert Hi; rb_zl AMB);
        rewrite HKP by (rewrite ?SNL1; revert Hi Hn3 LTX; rb_zl AMB);
        apply KC1; rb_lia AMB).
  all: assert (TXZ : ~ In 0 TX)
    by (subst TX; intros H0; apply in_app_or in H0; destruct H0 as [H0 | H0];
        [exact (HT1z H0) | apply HT2z; rewrite <- (firstn_skipn (Z.to_nat (199 - Z.of_nat (length T1))) T2);
                           apply in_or_app; left; exact H0]).
  all: assert (TXB : Forall (fun x => 0 <= x < 256) TX)
    by (subst TX; apply Forall_app; split;
        [eapply Forall_impl; [| exact HT1b]; intros x Hx; cbv beta in Hx |- *; rb_lia AMB
        | pose proof HT2b as HB2; rewrite <- (firstn_skipn (Z.to_nat (199 - Z.of_nat (length T1))) T2) in HB2;
          apply Forall_app in HB2; destruct HB2 as (HB2 & _);
          eapply Forall_impl; [| exact HB2]; intros x Hx; cbv beta in Hx |- *; rb_lia AMB]).
  all: assert (TXL : (length TX < 200)%nat) by (revert LTX LF2 HT1l; clear; lia).
  all: assert (HRC1 : sa_rconf (rdW W (ms_mem msR)) c (SegModel.refuse rcs ln f args))
    by (rewrite (refuse_f.rf_refuse_lt8 rcs bs0 ln f args HENC Hln Hn7);
        exact (refuse_f.rf_upd_slot (rdW W mem) (rdW W (ms_mem msR)) c rcs TX HRC Hrf32 Hn7 TXZ TXB TXL HKR RR1 RN1 HZS)).
  (* the release state ss_rel and refuse_r's release, at the FP state fx2 the two calls left *)
  all: r_to_rel HS.
  all: lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (EvR := Ex) in HS end.
  all: assert (HEIR : img_env VAL A_LIM EvR)
    by (subst EvR; repeat first [apply img_env_havoc_hi | apply img_env_ewset_hi]; first [eassumption | unfold A_LIM; rb_lia AMB]).
  all: assert (AGR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EvR n = getr regs r)
    by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        subst EvR; rb_evE; rewrite AG3, AG2 by rb_lia AMB; exact (EA n r Hn)).
  all: assert (R32 : ew EvR 32 = Z_to_bv 64 SB) by (subst EvR; rb_evE; rewrite AG3, AG2 by rb_lia AMB; exact E32).
  all: assert (R2 : ew EvR 2 = getr regs 2) by (subst EvR; rb_evE; rewrite AG3, AG2 by rb_lia AMB; exact E2).
  all: assert (R1028 : ew EvR 1028 = Z_to_bv 64 (frame_addr ly 0 fpos))
    by (subst EvR; rb_evE; rewrite AG3 by rb_lia AMB; exact E2_1028).
  all: assert (R1040 : ew EvR 1040 = Z_to_bv 64 (flag_addr ly 0 fpos))
    by (subst EvR; rb_evE; rewrite AG3 by rb_lia AMB; exact E2_1040).
  all: assert (R1041 : ew EvR 1041 = Z_to_bv 64 (SB + frame_addr ly 0 fpos / 8))
    by (subst EvR; rb_evE; rewrite AG3 by rb_lia AMB; exact E2_1041).
  all: assert (HBLK : exists pb kb, In (pb, kb) (ablocks B ly S) /\ pb <= c /\ c + seg_spec.SEG_C_SIZE <= pb + req_size kb)
    by (exists pb, kb; split; [exact Hpbin | split; [rb_lia AMB | unfold seg_spec.SEG_C_SIZE; rb_lia AMB]]).
  all: assert (HS2f : exists f0, S2 = set_fs f0 S) by (exists fS2; first [exact ES2 | exact (eq_sym ES2)]).
  all: eapply (refuse_r.r_release (fx := fx2)) with (B := B) (ly := ly) (S := S) (W := W) (regs := regs) (mem := mem)
    (md := md) (ch := ch) (c := c) (rcs' := SegModel.refuse rcs ln f args) (FP := refuse_W c rcs) (S2 := S2)
    (fpos := fpos) (Ev := EvR);
  [ assumption .. | exact HPRE | exact HEIR | exact HS | exact HJ4 | exact Hfrs2 | exact Eab | exact HS2f
  | exact AGR | exact R32 | exact R2 | exact R1028 | exact R1040 | exact R1041 | exact HBLK | exact HRC1 ].
    Unshelve.
  }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  all: lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hwh end.
  (* B2 (0x88f38 / 0x88f40-0x88f44): where, the `line` branch *)
  all: paj_run_tok RUN HS HJ2 SHOK Bspan; rb_awro.
  all: rb_ro_eq HF0.
  all: psrr_branch_tok RUN BR HS SHOK Bspan.
  all: lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hln0 end.
  (* B3 (0x88f48-0x88f5c / 0x88f64-0x88f74): the snprintf arguments, to the call *)
  all: paj_run_tok RUN HS HJ2 SHOK Bspan; rb_awro.
  all: rb_ro_eq HF1.
  all: assert (Hm4 : ms_mem ms4 = ms_mem ms1) by congruence.
  all: clear HF HFr HG HF0 HFr0 HG0 HF1 HFr1 HG1.
  (* the two branches as facts; the leaves are (rd0 <> 0, ln = 0), (rd0 <> 0, ln > 0), (rd0 = 0, ln = 0),
     (rd0 = 0, ln > 0) *)
  all: lazymatch type of Hwh with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite branch_ne_U, (U_atom Ex 1044 rd0 ltac:(rb_evE; exact E3_1044) ltac:(rb_lia AMB)), (U_lit Ex 0 ltac:(rb_lia AMB)) in Hwh end.
  all: first [ apply Bool.negb_true_iff, Z.eqb_neq in Hwh | apply Bool.negb_false_iff, Z.eqb_eq in Hwh ].
  all: lazymatch type of Hwh with ?T => change (rnam T) in Hwh end.
  all: lazymatch type of Hln0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (BGE Ex ltac:(rb_evE; rewrite AG3, AG2 by rb_lia AMB; exact E11)) in Hln0 end.
  all: first [ apply Bool.negb_true_iff, Z.ltb_ge in Hln0 | apply Bool.negb_false_iff, Z.ltb_lt in Hln0 ].
  (* ===== the address snprintf (0x88f5c / 0x88f74): the machine at the call, its registers ===== *)
  all: pmkst HS.
  all: rewrite Hm4 in HJ2 |- *.
  all: prreg HS (1%bv : bv 5) Q1.
  all: rb_reg HS (2%bv : bv 5) Q2. all: rb_reg HS (3%bv : bv 5) Q3. all: rb_reg HS (4%bv : bv 5) Q4.
  all: rb_reg HS (10%bv : bv 5) Q10. all: rb_reg HS (11%bv : bv 5) Q11. all: rb_reg HS (12%bv : bv 5) Q12.
  all: rb_reg HS (13%bv : bv 5) Q13. all: rb_reg HS (14%bv : bv 5) Q14.
  all: assert (QSP : spZ (ms_regs ms4) = sp0 + (rsp1 sp0 - sp0))
    by (unfold spZ; rewrite Q2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rb_evE; rewrite V33; rb_lia AMB).
  all: assert (QGP : getr (ms_regs ms4) 3 = w64 (as_gp B))
    by (rewrite Q3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rb_evE; rewrite AG3, AG2, E3 by rb_lia AMB; exact Hgp).
  all: assert (QTP : getr (ms_regs ms4) 4 = w64 (as_tp B))
    by (rewrite Q4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rb_evE; rewrite AG3, AG2, E4 by rb_lia AMB; exact Htp).
  all: assert (QRA : YK0s.ret_ok (getr (ms_regs ms4) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [rb_lia AMB | reflexivity]).
  all: assert (QD : getr (ms_regs ms4) 10 = w64 (c + 11912 + 200 * nr))
    by (rewrite Q10; apply DSLOT; [rb_evE; rewrite AG3, AG2 by rb_lia AMB; rewrite E10, H10; reflexivity | rb_evE; exact E3_1042]).
  all: assert (QN : getr (ms_regs ms4) 11 = w64 200) by (rewrite Q11; reflexivity).
  all: assert (A3 : argZ (ms_regs ms4) 3 = bv_unsigned (getr (ms_regs ms4) 13))
    by (unfold argZ; do 2 f_equal; apply bv_eq; reflexivity).
  all: assert (A4 : argZ (ms_regs ms4) 4 = bv_unsigned (getr (ms_regs ms4) 14))
    by (unfold argZ; do 2 f_equal; apply bv_eq; reflexivity).
  (* the format: "%s: " (A_OBJ 72) for line <= 0, "%s:%d: " (A_OBJ 71) for line > 0 *)
  all: assert (QFA : getr (ms_regs ms4) 12 = w64 (seg_litA_rc (SegModel.r_addr_fmt ln)))
    by (rewrite Q12; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold SegModel.r_addr_fmt;
        lazymatch goal with HEIx : img_env _ _ ?Ex |- ew ?Ex ?n = _ =>
          rewrite (img_env_atomP Ex n HEIx ltac:(unfold A_TEXT, A_LIM; rb_lia AMB)) end;
        first [ rewrite (proj2 (Z.ltb_ge 0 ln) ltac:(rb_lia AMB)); change 313%nat with (A_OBJ 72); rewrite LA72; reflexivity
              | rewrite (proj2 (Z.ltb_lt 0 ln) ltac:(rb_lia AMB)); change 312%nat with (A_OBJ 71); rewrite LA71; reflexivity ]).
  (* where: c->reading (c + 0x4080) when c->reading[0] <> 0, else "reac-pw.conf" (A_OBJ 34) *)
  all: assert (QWH : argZ (ms_regs ms4) 3 =
      (if SegModel.hd0 (rc_reading rcs) =? 0 then seg_litA_rc SegModel.S_base else c + 16512))
    by (rewrite A3, Q13;
        lazymatch goal with HEIx : img_env _ _ ?Ex |- bv_unsigned (sv_denot ?Ex _) = _ =>
        first [ rewrite (proj2 (Z.eqb_neq (SegModel.hd0 (rc_reading rcs)) 0) Hwh);
                pose proof (U_atom_off Ex 10 c 16512 ltac:(rb_evE; rewrite AG3, AG2 by rb_lia AMB; rewrite E10, H10; reflexivity)
                  ltac:(rb_lia AMB) ltac:(rb_lia AMB)) as HU; unfold U in HU; exact HU
              | rewrite (proj2 (Z.eqb_eq (SegModel.hd0 (rc_reading rcs)) 0) Hwh);
                pose proof (U_img_atom Ex HEIx 275 ltac:(unfold A_TEXT, A_LIM; rb_lia AMB)) as HU; unfold U in HU; rewrite HU;
                change 275%nat with (A_OBJ 34); exact LA34 ] end).
  all: assert (QLN : 0 < ln -> argZ (ms_regs ms4) 4 = ln)
    by (intros Hlp; first [ rb_lia AMB | rewrite A4, Q14;
        lazymatch goal with |- bv_unsigned (sv_denot ?Ex _) = _ =>
          pose proof (U_atom Ex 11 ln ltac:(rb_evE; rewrite AG3, AG2 by rb_lia AMB; exact E11) ltac:(rb_lia AMB)) as HU; unfold U in HU; exact HU end ]).
  (* the regions the call writes: its window below sp1 and the slot's first |T1| + 1 bytes *)
  all: assert (RSOK1 : Forall (fun r => fst r + snd r <= c + 0x34c8 \/ c + 0x4080 + 104 <= fst r)
      (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms4)) (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1)))
    by (unfold RtPFShared.snp_out; rewrite QSP, SNL1; repeat constructor; cbn [fst snd]; unfold RtPFCmd.CMD_SNP_K; rb_lia AMB).
  all: assert (RSOK2 : Forall (fun r => fst r + snd r <= 0x10000 \/ kImgEnd <= fst r)
      (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms4)) (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1)))
    by (unfold RtPFShared.snp_out; rewrite QSP, SNL1; constructor; [cbn [fst snd]; right; unfold RtPFCmd.CMD_SNP_K, kImgEnd; rb_lia AMB |];
        constructor; [cbn [fst snd]; apply OFFI; rb_lia AMB | constructor]).
  all: assert (FFP : RtPFCmd.FR_cmd (rdW W (ms_mem ms1))
      (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms4)) (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1))
      (seg_litA_rc (SegModel.r_addr_fmt ln)) (map (argZ (ms_regs ms4)) [3; 4; 5; 6; 7]) T1)
    by (apply (refuse_pft.r_fr_cmd_addr SEGS B);
        [ unfold SegModel.r_addr_fmt; destruct (0 <? ln); [left | right; left]; reflexivity
        | unfold SegModel.r_addr_fmt, SegModel.r_addr_args; destruct (0 <? ln); reflexivity
        | apply FLIT; [unfold SegModel.r_addr_fmt; destruct (0 <? ln); [left | right; left]; reflexivity | exact RSOK2]
        | unfold SegModel.r_addr_args; cbn [map];
          assert (WARG : refuse_pft.ffr_arg (rdW W (ms_mem ms1))
              (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms4)) (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1))
              (argZ (ms_regs ms4) 3) (SegModel.AS (SegModel.r_where rcs)))
            by (rewrite QWH; unfold SegModel.r_where;
                destruct (Z.eqb_spec (SegModel.hd0 (rc_reading rcs)) 0) as [Hz1|Hz1];
                [apply WLIT; exact RSOK2 | apply WREAD; [exact RSOK1 | exact Hz1]]);
          destruct (Z.ltb_spec 0 ln) as [Hlp|Hlp]; cbn [refuse_pft.ffr_args];
          [split; [exact WARG | split; [split; [rb_lia AMB | exact (QLN Hlp)] | exact I]] | split; [exact WARG | exact I]] ]).
  all: assert (CR0 : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) RtPFCmd.CMD_SNP_CR)
    by (unfold RtPFCmd.CMD_SNP_CR; repeat constructor; cbn [fst snd]; rb_lia AMB).
  all: assert (IMGD : forall x w, 0x10000 <= x -> x + w <= kImgEnd ->
      Forall (zdisjoint (x, w))
        (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms4)) (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1)))
    by (intros xi wi Hx1 Hx2; pose proof (OFFI (c + 11912 + 200 * nr) (Z.of_nat (length T1) + 1) ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB)) as HO;
        unfold RtPFShared.snp_out; rewrite QSP, SNL1; unfold RtPFCmd.CMD_SNP_K, kImgEnd in *;
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rb_lia AMB |];
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rb_lia AMB | apply Forall_nil]).
  all: assert (CR1 : Forall (fun r => Forall (zdisjoint r)
      (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms4)) (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1)))
      RtPFCmd.CMD_SNP_CR)
    by (unfold RtPFCmd.CMD_SNP_CR; constructor; [apply IMGD; unfold kImgEnd; rb_lia AMB |];
        constructor; [apply IMGD; unfold kImgEnd; rb_lia AMB | constructor]).
  all: assert (PWD : pairwise zdisjoint
      (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms4)) (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1)))
    by (unfold RtPFShared.snp_out; rewrite QSP, SNL1; cbn [pairwise]; split; [| split; [apply Forall_nil | exact I]];
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold RtPFCmd.CMD_SNP_K; rb_lia AMB | apply Forall_nil]).
  all: assert (SPD : Forall (zdisjoint (spZ (ms_regs ms4), 8 * Z.of_nat (length (@nil Z))))
      (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms4)) (c + 11912 + 200 * nr) (RtPFShared.sn_len (200 - 1) T1)))
    by (cbn [length]; unfold RtPFShared.snp_out; rewrite QSP, SNL1; unfold RtPFCmd.CMD_SNP_K;
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rb_lia AMB |];
        apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; rb_lia AMB | apply Forall_nil]).
  all: destruct (refuse_pft.r_snp_pre SEGS B LAWS Hsegs RtPFCmd.CMD_SNP_K W (ms_regs ms4) (ms_mem ms1) STK_refuse sp0
      (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 _ 0 (c + 11912 + 200 * nr) 200 T1 (rsp1 sp0 - sp0)
      (getr (ms_regs ms4) 1) HJ2 ltac:(rb_lia AMB) QSP Ho16 Hneg HKe Hbud QGP QTP eq_refl QRA DST1 PWR1 RAD1 HUL1)
    as ((HEP & Hslo' & Hscr) & Hlen1 & _ & HDEST & HRADl & HHULLl).
  all: pose proof (SNP fx) as SNPx; unfold RtFormat.asnprintf_realizes, RtPFCmd.asnprintf_sh in SNPx.
  all: eapply SRr_bind;
    [ apply (refuse_pft.r_snp_post SEGS B LAWS Hsegs RtPFCmd.CMD_SNP_K (SIGMA SS___interceptor_trampoline_snprintf) W
        (ms_regs ms4) (ms_mem ms1) STK_refuse sp0 (refuse_W c rcs) ly S W mem md [(0, fpos)] ly S2 _ 0
        (c + 11912 + 200 * nr) 200 T1 (rsp1 sp0 - sp0) (getr (ms_regs ms4) 1) HJ2 eq_refl QSP Hneg Hbud
        ltac:(rb_lia AMB) (fun a Ha => proj1 (DST1 a Ha)));
      exact (SNPx ly S2 W (ms_regs ms4) (ms_mem ms1) _ (c + 11912 + 200 * nr) 200
        (seg_litA_rc (SegModel.r_addr_fmt ln)) [] (map (argZ (ms_regs ms4)) [3; 4; 5; 6; 7]) T1 gcan
        HEP Hslo' Hscr QD QN QFA ROM1 CR0 CR1 SSP1 SSP2 ltac:(unfold gotwA; rb_lia AMB) ltac:(unfold gotwA; rb_lia AMB)
        ltac:(unfold guardA; rb_lia AMB) ltac:(unfold guardA; rb_lia AMB)
        (IMGD gotwA 8 ltac:(unfold gotwA; rb_lia AMB) ltac:(unfold gotwA, kImgEnd; rb_lia AMB))
        (IMGD guardA 8 ltac:(unfold guardA; rb_lia AMB) ltac:(unfold guardA, kImgEnd; rb_lia AMB))
        ltac:(split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; rb_lia AMB])
        ltac:(cbn [length]; rewrite QSP; rb_lia AMB) SPD FFP ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rewrite SNL1; rb_lia AMB)
        PWD HDEST AMR1 HRADl HHULLl
        ltac:(unfold zdisjoint; cbn [fst snd]; rewrite SNL1; unfold RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI;
              pose proof (OFFI (c + 11912 + 200 * nr) (Z.of_nat (length T1) + 1) ltac:(rb_lia AMB) ltac:(rb_lia AMB) ltac:(rb_lia AMB));
              unfold kImgEnd in *; rb_lia AMB)
        HFRM)
    | ].
  (* ===== after snprintf: the FP state fx1, the symbolic state rebuilt (k = |T1| in a0, atom 1104) ===== *)
  all: cbv beta; intros W2 c2 _ (-> & fx1 & regs5 & mem5 & md5 & Hfx1 & -> & HJ3 & HP3 & HK10 & HBY & HKP & HPR & HSM).
  all: apply (PaFx.srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx1 |].
  all: assert (KEEPS1 : forall a, (c + 13512 <= a < c + 13520) \/ (SB + F / 8 <= a < SB + F / 8 + 8) \/
      (F <= a < F + 64) \/ (sp0 - 144 <= a < sp0) -> rdW W mem5 a = rdW W (ms_mem ms1) a)
    by (intros a Ha; apply HKP; rewrite ?SNL1; revert Ha; rb_zl AMB).
  all: jafter_call_keep_hi HS 1100%nat regs5 (mrestrict (w_H W) mem5) HP3 [1;2;3;4;5;7]%nat HS2.
  all: match type of HS2 with ?A -> _ => assert (HQ : A) by (
         cbn [ms_mem restrict]; rewrite Hm4; repeat apply Forall_cons; try apply Forall_nil;
         (eapply region_kept_aview; [ rb_evE; first [exact V10 | exact V1041 | exact V1028 | exact V2]
           | intros ?a ?Ha; apply KEEPS1; rb_lia AMB | exact HPR ])); specialize (HS2 HQ); clear HQ end.
  all: rewrite <- (restrict_mkst_fx (fx := fx)) in HS2.
  all: apply (PaFx.st_ok_pi_restrict_xfx fx fx1) in HS2.
  all: clear HS; rename HS2 into HS.
  all: rewrite Q1.
  all: pose proof (paj_run (fx := fx1) B LAWS) as RUN1.
  all: pose proof (paj_branch (fx := fx1) (PI := PI)) as BR1.
  all: pose proof (SRr_run_pi_AJ (fx := fx1) B LAWS) as RUNP1.
  all: pose proof (SRr_run_pi_AJ_call (fx := fx1) B LAWS) as RUNC1.
  all: lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HEI8 : img_env VAL A_LIM Ex)
      by (apply img_env_havoc_hi; [lazymatch goal with H : img_env _ _ ?E0 |- img_env _ _ ?E0 => exact H end | unfold A_LIM; rb_lia AMB]);
    assert (ZSHC3 : range_addressable (rdW W mem5) SHADOW_OFF c 16616)
      by exact (range_addressable_of_block SEGS B LAWS ly S2 W mem5 _ pb kb c 16616 (proj1 HJ3) HpbT Hpb1 ltac:(rb_lia AMB));
    assert (UB3 : U Ex (SOff 32 0) = SHADOW_OFF)
      by (rewrite (U_atom Ex 32 SB); [reflexivity | rb_evE; rewrite AG3, AG2, E32 by rb_lia AMB; reflexivity | unfold SB; rb_lia AMB]);
    assert (UC3 : U Ex (SOff 10 0) = c)
      by (apply U_atom; [rb_evE; rewrite AG3, AG2 by rb_lia AMB; rewrite E10, H10; reflexivity | rb_lia AMB]);
    assert (SHOK3 : sh_ok SEGS (SOff 32 0) [mkSHE 10 0x34c8 0x34d0] Ex (mrestrict (w_H W) mem5))
      by (unfold sh_ok; repeat apply Forall_cons; try apply Forall_nil;
          eapply (shent_ok_of_range SEGS (w_H W) mem5 Ex (SOff 32 0) 10%nat c 16616 c 0x34c8 0x34d0 ZSHC3 UB3 UC3);
          [rb_lia AMB | rb_lia AMB | intros x Hx; unfold SHADOW_OFF; unfold rnam, kLowShadowBeg, kHighMemBeg in Hpbapp; rb_lia AMB]) end.
  (* 0x88f60 `j` / 0x88f78: the k test `bltu 199, k` *)
  all: paj_run_tok RUN1 HS HJ3 SHOK3 Bspan; rb_awro.
  all: pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rb_lia AMB |]);
    destruct Hin)) as UNk.
  all: cbn [ms_mem restrict mkst] in UNk.
  all: clear HF HFr HG.
  all: psrr_branch_tok RUN1 BR1 HS SHOK3 Bspan.
  all: lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hkt end.
  all: lazymatch type of Hkt with branch_taken _ (sv_denot ?Ex _) (sv_denot _ (SOff ?n _)) = _ =>
    rewrite branch_ltu_U, (U_lit Ex 199 ltac:(rb_lia AMB)) in Hkt;
    rewrite (U_atom Ex n (Z.of_nat (length T1))) in Hkt;
    [| rb_evE; change 1104%nat with (1100 + 4)%nat;
       rewrite (ew_havoc_new _ 1100 (map (getr regs5) CLOB) 4 (Z_to_bv 64 0)) by (cbn; rb_lia AMB); cbn [nth map CLOB]; exact HK10
     | rb_lia AMB] end.
  (* k > 199 (unsigned) is not taken: k = |T1| <= 108 (refuse_f.rf_T1) *)
  all: try (apply Z.ltb_lt in Hkt; exfalso; rb_lia AMB).
  all: apply Z.ltb_ge in Hkt.
  (* the four leaves meet after the k test: drop the leaf's branch conditions, reach ss_tl and apply TAIL *)
  all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss ?msx =>
    pose proof (st_ok_pi_facts_incl3 Ex ss msx (f_atoms (ss_facts ss))
      [ {| ac_c := neg_bc BC_LTU; ac_a := SLit 199; ac_b := SOff 1104 0 |};
        {| ac_c := BC_GE; ac_a := SLit 7; ac_b := SOff 1042 0 |} ]
      (f_alias (ss_facts ss)) HS (fun x H => H)
      ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; vm_compute in Hx;
            repeat (destruct Hx as [<- | Hx]; [vm_compute; repeat (first [left; reflexivity | right]) |]); destruct Hx)
      (fun x H => H)) as HS2 end.
  all: clear HS; rename HS2 into HS.
  all: lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let Heq := fresh "Heq" in assert (Heq : ss = ss_tl) by (vm_compute; reflexivity); rewrite Heq in HS; clear Heq end.
  all: exact (TAIL fx1 regs5 mem5 ms5 _ Hfx1 HS HJ3 HK10 HBY HKP (fun a Ha => UNk a Ha (fun q => q))).
  Unshelve.
Qed.
End e.
End f.
End d.
