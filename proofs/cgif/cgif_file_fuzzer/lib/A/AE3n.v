(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AE3e AE3f AE3g AE6g AE39 AE2p AE3i AE3h AF0m AE22 AF0x AE20 AE2y AE7f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FMT_usage : Z := 0x15859.
Definition lit_usage1 : list Z := [117; 115; 97; 103; 101; 58; 32].
Definition lit_usage2 : list Z := [32; 73; 78; 80; 85; 84; 10].
Definition INT_MAX : Z := 2147483647.
Definition vu0 : sstate := ss_vf FMT_usage (SOff 32 0).
Definition vu_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu0).
Definition vu_af1 : sstate := Eval vm_compute in vf_after_icpt 34 vu_st1 RA_FX OSP_FX (-352) lit_usage1.
Definition vu_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu_af1).
Definition vu_af2 : sstate := Eval vm_compute in vf_after_icpt 50 vu_st2 RA_FX OSP_FX (-345) [].
Definition vu_st3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu_af2).
Definition vu_af3 : sstate := Eval vm_compute in vf_after_icpt 66 vu_st3 RA_SN OSP_SN 0 [].
Definition vu_r01 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu_st1).
Definition vu_rest1 : smem := Eval vm_compute in tl (ss_mem vu_st1).
Definition vu_r02 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu_st2).
Definition vu_rest2 : smem := Eval vm_compute in tl (ss_mem vu_st2).
Definition vu_r03 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu_st3).
Definition vu_rest3 : smem := Eval vm_compute in tl (ss_mem vu_st3).
Lemma vu_run1 : sym_runN tfibsegs tfibmusl_tbl FUEL vu0 = (vu_st1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vu_run2 : sym_runN tfibsegs tfibmusl_tbl FUEL vu_af1 = (vu_st2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vu_run3 : sym_runN tfibsegs tfibmusl_tbl FUEL vu_af2 = (vu_st3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition vu1_af3f : sstate := Eval vm_compute in vf_add_fact vu_af3 70 (mkAF 0 66 0).
Definition vu1_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af3f).
Definition vu1_af4 : sstate := Eval vm_compute in set_regs_pc vu1_st4 [((12%bv : bv 5), SLit 0)] 0x942a4.
Definition vu1_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af4).
Definition vu1_af5 : sstate := Eval vm_compute in vf_after_icpt 82 vu1_st5 RA_FX OSP_FX (-345) [].
Definition vu1_st6 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af5).
Definition vu1_r05 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu1_st5).
Definition vu1_rest5 : smem := Eval vm_compute in tl (ss_mem vu1_st5).
Definition vu1_r06 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu1_st6).
Definition vu1_rest6 : smem := Eval vm_compute in tl (ss_mem vu1_st6).
Lemma vu1_run4 : sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af3f = (vu1_st4, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 32 0) (SOff 70 0)))). Proof. vm_compute. reflexivity. Qed.
Lemma vu1_run5 : sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af4 = (vu1_st5, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vu1_run6 : sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af5 = (vu1_st6, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition vu1_af6 : sstate := Eval vm_compute in vf_after_icpt_n 98 vu1_st6 RA_FX OSP_FX (-345) (-272).
Definition vu1_st7 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af6).
Lemma vu1_run7 : sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af6 = (vu1_st7, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))). Proof. vm_compute. reflexivity. Qed.
Definition vu1_st7c : sstate := Eval vm_compute in YP06.add_cond vu1_st7 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7)).
Definition vu1_st8 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu1_st7c).
Definition vu1_r08 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu1_st8).
Definition vu1_rest8 : smem := Eval vm_compute in tl (ss_mem vu1_st8).
Definition vu1_af8 : sstate := Eval vm_compute in vf_after_icpt_n 114 vu1_st8 RA_FX OSP_FX (-345) (-272).
Definition vu1_st9 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af8).
Definition vu1_st9c : sstate := Eval vm_compute in YP06.add_cond vu1_st9 (mkAC BC_NE (SAlu ALU_ADD (SOff 2 (-338)) (SOff 70 0)) (SOff 2 (-352))).
Definition vu1_st10 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu1_st9c).
Definition vu1_af10 : sstate := Eval vm_compute in wl_after vu1_st10 0 (-480) 130.
Definition vu1_st11 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af10).
Lemma vu1_run8 : sym_runN tfibsegs tfibmusl_tbl FUEL vu1_st7c = (vu1_st8, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vu1_run9 : sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af8 = (vu1_st9, RS_stopped (SR_branch BC_EQ (SAlu ALU_ADD (SOff 2 (-338)) (SOff 70 0)) (SOff 2 (-352)))). Proof. vm_compute. reflexivity. Qed.
Lemma vu1_run10 : sym_runN tfibsegs tfibmusl_tbl FUEL vu1_st9c = (vu1_st10, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Lemma vu1_run11 : sym_runN tfibsegs tfibmusl_tbl FUEL vu1_af10 = (vu1_st11, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition vu2_af3f : sstate := Eval vm_compute in vf_add_fact vu_af3 70 (mkAF 67 73 0).
Definition vu2_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af3f).
Definition vu2_af4 : sstate := Eval vm_compute in set_regs_pc vu2_st4 [((12%bv : bv 5), SLit 0)] 0x942a4.
Definition vu2_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af4).
Definition vu2_af5 : sstate := Eval vm_compute in vf_after_icpt 82 vu2_st5 RA_FX OSP_FX (-345) [].
Definition vu2_st6 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af5).
Definition vu2_r05 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu2_st5).
Definition vu2_rest5 : smem := Eval vm_compute in tl (ss_mem vu2_st5).
Definition vu2_r06 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu2_st6).
Definition vu2_rest6 : smem := Eval vm_compute in tl (ss_mem vu2_st6).
Lemma vu2_run4 : sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af3f = (vu2_st4, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 32 0) (SOff 70 0)))). Proof. vm_compute. reflexivity. Qed.
Lemma vu2_run5 : sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af4 = (vu2_st5, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vu2_run6 : sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af5 = (vu2_st6, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition vu2_af6 : sstate := Eval vm_compute in vf_after_icpt_n 98 vu2_st6 RA_FX OSP_FX (-345) (-272).
Definition vu2_st7 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af6).
Lemma vu2_run7 : sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af6 = (vu2_st7, RS_stopped (SR_branch BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))). Proof. vm_compute. reflexivity. Qed.
Definition vu2_st7c : sstate := Eval vm_compute in YP06.add_cond vu2_st7 (mkAC BC_LTU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7)).
Definition vu2_st8 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu2_st7c).
Definition vu2_st8c : sstate := Eval vm_compute in YP06.add_cond vu2_st8 (mkAC BC_NE (SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SOff 2 (-352))).
Definition vu2_st9 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu2_st8c).
Definition vu2_af9 : sstate := Eval vm_compute in wl_after vu2_st9 0 (-1024) 114.
Definition vu2_st10 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af9).
Definition vu2_st10r : sstate := Eval vm_compute in resume vu2_st10 (SLit 0) (ss_mem vu2_st10) (ss_facts vu2_st10).
Definition vu2_st11 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu2_st10r).
Lemma vu2_run8 : sym_runN tfibsegs tfibmusl_tbl FUEL vu2_st7c = (vu2_st8, RS_stopped (SR_branch BC_EQ (SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SOff 2 (-352)))). Proof. vm_compute. reflexivity. Qed.
Lemma vu2_run9 : sym_runN tfibsegs tfibmusl_tbl FUEL vu2_st8c = (vu2_st9, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Lemma vu2_run10 : sym_runN tfibsegs tfibmusl_tbl FUEL vu2_af9 = (vu2_st10, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Lemma vu2_run11 : sym_runN tfibsegs tfibmusl_tbl FUEL vu2_st10r = (vu2_st11, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition vu3_af3f : sstate := Eval vm_compute in vf_add_fact vu_af3 70 (mkAF 74 33554425 0).
Definition vu3_st4 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af3f).
Definition vu3_af4 : sstate := Eval vm_compute in set_regs_pc vu3_st4 [((12%bv : bv 5), SLit 0)] 0x942a4.
Definition vu3_st5 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af4).
Definition vu3_af5 : sstate := Eval vm_compute in vf_after_icpt 82 vu3_st5 RA_FX OSP_FX (-345) [].
Definition vu3_st6 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af5).
Definition vu3_r05 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu3_st5).
Definition vu3_rest5 : smem := Eval vm_compute in tl (ss_mem vu3_st5).
Definition vu3_r06 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu3_st6).
Definition vu3_rest6 : smem := Eval vm_compute in tl (ss_mem vu3_st6).
Lemma vu3_run4 : sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af3f = (vu3_st4, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 32 0) (SOff 70 0)))). Proof. vm_compute. reflexivity. Qed.
Lemma vu3_run5 : sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af4 = (vu3_st5, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vu3_run6 : sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af5 = (vu3_st6, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition vu3_af6 : sstate := Eval vm_compute in wl_after vu3_st6 0 (-1024) 98.
Definition vu3_st7 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af6).
Definition vu3_r07 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem vu3_st7).
Definition vu3_rest7 : smem := Eval vm_compute in tl (ss_mem vu3_st7).
Definition vu3_af7 : sstate := Eval vm_compute in vf_after_icpt 109 vu3_st7 RA_FX OSP_FX (-352) lit_usage2.
Definition vu3_wx := Eval vm_compute in (wx_step tfibmusl_tbl 125 vu3_af7).
Definition vu3_st8 : sstate := Eval vm_compute in match vu3_wx with Some (s1, _, _, _) => s1 | None => vu3_af7 end.
Definition vu3_af8 : sstate := Eval vm_compute in match vu3_wx with Some (_, s2, _, _) => s2 | None => vu3_af7 end.
Definition vu3_st9 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af8).
Lemma vu3_wx_eq : wx_step tfibmusl_tbl 125 vu3_af7 = Some (vu3_st8, vu3_af8, lit_usage2, 2). Proof. vm_compute. reflexivity. Qed.
Lemma vu3_run7 : sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af6 = (vu3_st7, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma vu3_run9 : sym_runN tfibsegs tfibmusl_tbl FUEL vu3_af8 = (vu3_st9, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Section S.
Variable B : asyms.
Hypothesis TL : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ASTRNLEN : astrnlen_realizesM B (pc_wrap_strnlen (as_code B)).
Let HBcode := ts_code B TL.
Lemma lit_usage1_range : Forall (fun z => 0 <= z < 256) lit_usage1. Proof. apply Forall_range_of_forallb. vm_compute. reflexivity. Qed.
Lemma lit_usage2_range : Forall (fun z => 0 <= z < 256) lit_usage2. Proof. apply Forall_range_of_forallb. vm_compute. reflexivity. Qed.
Theorem tfib_vfprintf_usage_A1 : forall ly S (W : world tfibsegs) regs mem md ch ap s (str : list byte) L cval T,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 s ->
L = Z.of_nat (length str) -> 0 <= L -> L <= 66 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - VF_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF FMT_usage 17 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof.
intros ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HL HLlo HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDERR = 664952) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (rewrite KHI; lia).
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
assert (HLlen : length str = Z.to_nat L) by lia.
unfold cfg_at. change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vf_entry W regs mem FMT_usage (SOff 32 0) ap s cval Hsp44 Hsp47 Hal16
ltac:(intros a Ha; apply Hpres; exact Ha) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg ltac:(lia)
HFP Hgot Hcan Hcv Hro ltac:(cbn [sv_denot]; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS0.
change (ss_vf FMT_usage (SOff 32 0)) with vu0 in HS0.
remember (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; subst E0; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; apply unsigned_lit_small; lia).
assert (A32_0 : bv_unsigned (ew E0 32) = s) by (rewrite HE0, (ew_Ereg_extra regs _ 0); cbn [nth]; apply unsigned_lit_small; lia).
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E0) by (rewrite HE0; split; [intros i Hi; reflexivity | reflexivity]).
clear HE0 EE.
pose proof (VI_init B ly S W sp0 mem md HAR Hpres) as VI0.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 vu0 vu_st1 _ _ _ HS0 vu_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VI1 : VI B ly S W sp0 mem md (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms1) mat1 VI0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin); tauto.
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin); tauto.
- apply (vf_band_present W E0 vu_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VI0 HF1 HFr1.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms1) _ FMT_usage 17 88153 7 VI1 Hstk Hra_f Hhull_f
ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(rewrite KHI; unfold FMT_usage; lia)) as [SRA1' SHU1'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E0 vu_st1 ms1 _ ly S sp0 vu_r01 vu_rest1 34 RA_FX OSP_FX (-352) (SLit 88153) (88153) 7 lit_usage1
HS1 ltac:(rewrite HBcode; reflexivity) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E0 sp0 ap vu_rest1 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hap2)
(vf_rest_w E0 vu_rest1 ltac:(vm_compute; reflexivity))
(proj1 VI1) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI1))) SRA1' SHU1') HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
change (vf_after_icpt 34 vu_st1 RA_FX OSP_FX (-352) lit_usage1) with vu_af1 in HS1'.
assert (VI1' : VI B ly S W sp0 mem md (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 7))).
- exact VI1.
- exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr1'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (rewrite OLD1 by (cbv; lia); exact G12_0).
assert (A32_1 : bv_unsigned (ew E1 32) = s) by (rewrite OLD1 by (cbv; lia); exact A32_0).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
clear HE1 HS1 VI1 SRA1' SHU1'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E1 vu_af1 vu_st2 _ _ _ HS1' vu_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VI2 : VI B ly S W sp0 mem md (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms2) mat2 VI1') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin); tauto.
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin); tauto.
- apply (vf_band_present W E1 vu_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VI1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF 88160 0) by (intros y Hy; lia).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms2)) 88160 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E1 vu_st2 ms2 _ ly S sp0 vu_r02 vu_rest2 50 RA_FX OSP_FX (-345) (SLit 88160) (88160) 0 (@nil Z)
HS2 ltac:(rewrite HBcode; reflexivity) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E1 sp0 ap vu_rest2 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hap2)
(vf_rest_w E1 vu_rest2 ltac:(vm_compute; reflexivity))
(proj1 VI2) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI2))) SRA2' SHU2') HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 50 vu_st2 RA_FX OSP_FX (-345) (@nil Z)) with vu_af2 in HS2'.
assert (VI2' : VI B ly S W sp0 mem md (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- exact VI2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (rewrite OLD2 by (cbv; lia); exact G12_1).
assert (A32_2 : bv_unsigned (ew E2 32) = s) by (rewrite OLD2 by (cbv; lia); exact A32_1).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2 HS2 VI2 SRA2' SHU2'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E2 vu_af2 vu_st3 _ _ _ HS2' vu_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VI3 : VI B ly S W sp0 mem md (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms3) mat3 VI2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin); tauto.
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin); tauto.
- apply (vf_band_present W E2 vu_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VI2' HF3 HFr3.
assert (STR3 : vf_str W (ms_mem ms3) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI3)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms3) _ s (L + 1) s (L + 1) VI3 Hstk Hra_s Hhull_s
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [SRA3' SHU3'].
pose proof (vf_tail_xfer W mem (ms_mem ms3) sp0 s L Hstail (proj1 (proj2 (proj2 (proj2 VI3)))) Hal16 ltac:(lia) ltac:(lia) ltac:(lia) Hsband Hsfile) as TAIL3.
pose proof (mconsts_view_xfer W mem (ms_mem ms3) sp0 Hromv (proj1 (proj2 (proj2 (proj2 VI3)))) Hsp44) as ROM3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_strnlen B ASTRNLEN W E2 vu_st3 ms3 _ ly S sp0 vu_r03 vu_rest3 66 RA_SN OSP_SN (SOff 32 0) s INT_MAX L
HS3 ltac:(rewrite HBcode; reflexivity) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, <- A32_2, Z_to_bv_bv_unsigned; reflexivity) ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_SN; lia) ltac:(unfold OSP_SN; lia) ltac:(unfold RA_SN; lia) ltac:(reflexivity)
ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(unfold OSP_SN; lia)
(vf_rest_ok E2 sp0 ap vu_rest3 ltac:(vm_compute; reflexivity) G12_2 Hap1 Hap2)
(vf_rest_w E2 vu_rest3 ltac:(vm_compute; reflexivity))
(proj1 VI3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VI3)))
ltac:(rewrite HL; apply (vf_str_first_byte W _ s str INT_MAX STR3); unfold INT_MAX; lia)
ltac:(intros a Ha; apply (vf_str_readable W _ s str STR3); lia)
Hams SRA3' (SHU3' ltac:(lia)) TAIL3 ROM3) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & HL3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 66 vu_st3 RA_SN OSP_SN 0 []) with vu_af3 in HS3'.
assert (VI3' : VI B ly S W sp0 mem md (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms3) _ (ms_mem ms3') _
(fun a => sp0 + OSP_SN - 2 * ESTACK <= a < sp0 + OSP_SN)).
- exact VI3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_SN in *. lia.
- intros a Hr Hna. apply Hfr3'; [exact Hr | exact Hna].
- exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (rewrite OLD3 by (cbv; lia); exact G12_2).
assert (A32_3 : bv_unsigned (ew E3 32) = s) by (rewrite OLD3 by (cbv; lia); exact A32_2).
assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
assert (A70_3 : bv_unsigned (ew E3 70) = L).
{ rewrite HE3, (ew_havoc_new E2 66 _ 4 (w64 0)) by (cbn; lia). unfold CLOB. cbn [nth map]. rewrite HL3'. apply unsigned_lit_small. lia. }
clear HE3 HS3 VI3 SRA3' SHU3' STR3.
pose proof (st_ok_add_fact E3 vu_af3 _ 70 0 66 HS3' eq_refl ltac:(rewrite A70_3; lia)) as HS3f.
change (vf_add_fact vu_af3 70 (mkAF 0 66 0)) with vu1_af3f in HS3f. clear HS3'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 vu1_af3f vu1_st4 _ _ _ HS3f vu1_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3f.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VI4 : VI B ly S W sp0 mem md (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms4) mat4 VI3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (vf_windows_sound E3 vu1_af3f sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (vf_windows_sound E3 vu1_af3f sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- apply (vf_band_present W E3 vu1_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VI3' HF4 HFr4.
assert (STR4 : vf_str W (ms_mem ms4) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI4)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
assert (R11_4 : getr (ms_regs ms4) 11 = Z_to_bv 64 (s + L)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 _ _ 11 HS4).
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite denot_lit_U, U_add_off_atom by (rewrite ?A32_3, ?A70_3; unfold M64; lia). rewrite A32_3, A70_3. f_equal. lia. }
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_lbu_nul W E3 vu1_st4 ms4 _ 82 (s + L) HS4 eq_refl eq_refl ltac:(vm_compute; reflexivity) R11_4 ltac:(lia)
ltac:(rewrite HL; exact (proj1 (proj2 STR4)))) HAI4).
intros W4l c4l _ HAI4l (-> & ms4l & mat4l & -> & HS4l & Hmm4l). cbn [cfg_model] in HAI4l. rewrite ?wvb_wvb in HAI4l |- *.
change (set_regs_pc vu1_st4 [((12%bv : bv 5), SLit 0)] 0x942a4) with vu1_af4 in HS4l.
assert (VI4l : VI B ly S W sp0 mem md (ms_mem ms4l) (with_vm_backing (m_vm_lazy md) mat4l md)).
{ rewrite Hmm4l. pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms4) mat4l VI4) as VR.
rewrite ?wvb_wvb in VR. apply VR; [intros; reflexivity | intros; reflexivity | exact (proj1 (proj2 (proj2 VI4)))]. }
clear VI4 HS4 STR4 R11_4.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 vu1_af4 vu1_st5 _ _ _ HS4l vu1_run5) HAI4l).
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4l.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VI5 : VI B ly S W sp0 mem md (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms5) mat5 VI4l) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF5. intros Hin. destruct (vf_windows_sound E3 vu1_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- intros x Hx1 Hx2. apply HFr5. intros Hin. destruct (vf_windows_sound E3 vu1_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- apply (vf_band_present W E3 vu1_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VI4l HF5 HFr5.
assert (SRA5' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms5)) SHADOW_OFF 68444 0) by (intros y Hy; lia).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms5)) 68444 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E3 vu1_st5 ms5 _ ly S sp0 vu1_r05 vu1_rest5 82 RA_FX OSP_FX (-345) (SLit 68444) (68444) 0 (@nil Z)
HS5 ltac:(rewrite HBcode; reflexivity) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E3 sp0 ap vu1_rest5 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hap2)
(vf_rest_w E3 vu1_rest5 ltac:(vm_compute; reflexivity))
(proj1 VI5) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI5))) SRA5' SHU5') HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
change (vf_after_icpt 82 vu1_st5 RA_FX OSP_FX (-345) (@nil Z)) with vu1_af5 in HS5'.
assert (VI5' : VI B ly S W sp0 mem md (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- exact VI5.
- exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr5'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm5'. }
remember (havoc E3 82 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 82)%nat -> ew E5 j = ew E3 j) by (intros j Hj; rewrite HE5; apply ew_havoc_old; exact Hj).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by (cbv; lia); exact Usp3).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (rewrite OLD5 by (cbv; lia); exact G3_3).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (rewrite OLD5 by (cbv; lia); exact G4_3).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (rewrite OLD5 by (cbv; lia); exact G12_3).
assert (A32_5 : bv_unsigned (ew E5 32) = s) by (rewrite OLD5 by (cbv; lia); exact A32_3).
assert (A70_5 : bv_unsigned (ew E5 70) = L) by (rewrite OLD5 by (cbv; lia); exact A70_3).
assert (HAE5 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE5 HS5 VI5 SRA5' SHU5'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 vu1_af5 vu1_st6 _ _ _ HS5' vu1_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VI6 : VI B ly S W sp0 mem md (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms6) mat6 VI5') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6. intros Hin. destruct (vf_windows_sound E5 vu1_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- intros x Hx1 Hx2. apply HFr6. intros Hin. destruct (vf_windows_sound E5 vu1_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- apply (vf_band_present W E5 vu1_st6 ms6 sp0 HS6 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
clear VI5' HF6 HFr6.
assert (STR6 : vf_str W (ms_mem ms6) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI6)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms6) _ s (L + 1) s L VI6 Hstk Hra_s Hhull_s
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [SRA6' SHU6'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_sym B LAWS AMEMCPY W E5 vu1_st6 ms6 _ ly S sp0 vu1_r06 vu1_rest6 98 RA_FX OSP_FX (-345) (-272)
(SOff 2 (-345)) (SOff 32 0) (SOff 70 0) (-345) (s) (L)
HS6 ltac:(rewrite HBcode; reflexivity) eq_refl Usp5 G3_5 G4_5 eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(cbn; lia)
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Usp5; reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A32_5; reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A70_5; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(lia) ltac:(unfold OSP_FX; lia) ltac:(lia) ltac:(destruct Hams as [Hams'|[Hams' Hams'']]; [left; lia | right; lia])
(vf_rest_ok E5 sp0 ap vu1_rest6 ltac:(vm_compute; reflexivity) G12_5 Hap1 Hap2)
(vf_rest_w E5 vu1_rest6 ltac:(vm_compute; reflexivity))
(proj1 VI6) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI6)))
ltac:(intros a Ha; apply (vf_str_readable W _ s str STR6); lia) SRA6' SHU6') HAI6).
intros W6' c6' _ HAI6' (-> & ms6' & mat6' & -> & HS6' & HAR6' & HP6' & Heff6' & Hfr6' & Hpm6'). cbn [cfg_model] in HAI6'.
rewrite wvb_wvb in HAI6', HAR6' |- *.
change (vf_after_icpt_n 98 vu1_st6 RA_FX OSP_FX (-345) (-272)) with vu1_af6 in HS6'.
assert (VI6' : VI B ly S W sp0 mem md (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms6) _ (ms_mem ms6') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + (L)))).
- exact VI6.
- exact HAR6'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat6' mat6 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr6'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm6'. }
assert (STRBUF6' : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms6') (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite (Heff6' (Z.of_nat i)) by lia. apply (proj1 STR6). exact Hi. }
remember (havoc E5 98 (map (getr (ms_regs ms6')) CLOB)) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 98)%nat -> ew E6 j = ew E5 j) by (intros j Hj; rewrite HE6; apply ew_havoc_old; exact Hj).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by (cbv; lia); exact Usp5).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (rewrite OLD6 by (cbv; lia); exact G3_5).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (rewrite OLD6 by (cbv; lia); exact G4_5).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (rewrite OLD6 by (cbv; lia); exact G12_5).
assert (A32_6 : bv_unsigned (ew E6 32) = s) by (rewrite OLD6 by (cbv; lia); exact A32_5).
assert (A70_6 : bv_unsigned (ew E6 70) = L) by (rewrite OLD6 by (cbv; lia); exact A70_5).
assert (HAE6 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E6)
by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
clear HE6 HS6 VI6 SRA6' SHU6' Heff6'.
clear STR6.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 vu1_af6 vu1_st7 _ _ _ HS6' vu1_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VI7 : VI B ly S W sp0 mem md (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms7) mat7 VI6') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7. intros Hin. destruct (vf_windows_sound_n E6 vu1_af6 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr7. intros Hin. destruct (vf_windows_sound_n E6 vu1_af6 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms6') (ms_mem ms7) sp0 (-345) (proj1 (proj2 (proj2 VI6')))
(vf_band_present_n W E6 vu1_st7 ms7 sp0 (-345) HS7 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia))).
intros a Ha. apply HF7. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu1_af6 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (STRBUF7 : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms7) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF6' i Hi). apply aview_eq_of. apply HFr7. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu1_af6 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI6' HF7 HFr7 STRBUF6'.
pose proof (st_ok_add_cond tfibsegs E6 vu1_st7 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7) HS7 ltac:(rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A70_6; unfold M64; lia); rewrite A70_6; change (zcanon 7) with 7; apply Bool.negb_true_iff; apply Z.ltb_ge; lia)) as HS7c.
change (YP06.add_cond vu1_st7 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))) with vu1_st7c in HS7c. clear HS7.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 vu1_st7c vu1_st8 _ _ _ HS7c vu1_run8) HAI7).
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8. clear HS7c.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VI8 : VI B ly S W sp0 mem md (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms8) mat8 VI7) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF8. intros Hin. destruct (vf_windows_sound_n E6 vu1_st7c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr8. intros Hin. destruct (vf_windows_sound_n E6 vu1_st7c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms7) (ms_mem ms8) sp0 (-345) (proj1 (proj2 (proj2 VI7)))
(vf_band_present_n W E6 vu1_st8 ms8 sp0 (-345) HS8 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia))).
intros a Ha. apply HF8. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu1_st7c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (STRBUF8 : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms8) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF7 i Hi). apply aview_eq_of. apply HFr8. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu1_st7c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI7 HF8 HFr8 STRBUF7.
pose proof HS8 as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & Hmem8 & _). cbn [restrict ms_mem] in Hmem8.
assert (LIT2AV8 : forall i, (i < 7)%nat -> aview tfibsegs (w_H W) (ms_mem ms8) (88162 + Z.of_nat i) = Some (nth i lit_usage2 0)).
{ intros i Hi. apply (lit_buf_aview W E6 (ms_mem ms8) (ss_mem vu1_st8) (SLit 88162) 88162 7 lit_usage2 Hmem8 ltac:(vm_compute; reflexivity) eq_refl lit_usage2_range i Hi). }
clear Hmem8.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms8) _ FMT_usage 17 88162 7 VI8 Hstk Hra_f Hhull_f
ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(rewrite KHI; unfold FMT_usage; lia)) as [SRA8' SHU8'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_sym B LAWS AMEMCPY W E6 vu1_st8 ms8 _ ly S sp0 vu1_r08 vu1_rest8 114 RA_FX OSP_FX (-345) (-272)
(SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SLit 88162) (SLit 7) (-345 + L) (88162) (7)
HS8 ltac:(rewrite HBcode; reflexivity) eq_refl Usp6 G3_6 G4_6 eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(cbn; lia)
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(rewrite denot_lit_U, U_add_off_atom by (rewrite ?Usp6, ?A70_6; unfold M64; lia); rewrite Usp6, A70_6; f_equal; lia) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(lia) ltac:(unfold OSP_FX; lia) ltac:(lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E6 sp0 ap vu1_rest8 ltac:(vm_compute; reflexivity) G12_6 Hap1 Hap2)
(vf_rest_w E6 vu1_rest8 ltac:(vm_compute; reflexivity))
(proj1 VI8) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI8)))
ltac:(intros a Ha; replace a with (88162 + Z.of_nat (Z.to_nat (a - 88162))) by lia; rewrite (LIT2AV8 (Z.to_nat (a - 88162)) ltac:(lia)); discriminate) SRA8' SHU8') HAI8).
intros W8' c8' _ HAI8' (-> & ms8' & mat8' & -> & HS8' & HAR8' & HP8' & Heff8' & Hfr8' & Hpm8'). cbn [cfg_model] in HAI8'.
rewrite wvb_wvb in HAI8', HAR8' |- *.
change (vf_after_icpt_n 114 vu1_st8 RA_FX OSP_FX (-345) (-272)) with vu1_af8 in HS8'.
assert (VI8' : VI B ly S W sp0 mem md (ms_mem ms8') (with_vm_backing (m_vm_lazy md) mat8' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms8) _ (ms_mem ms8') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345 + L) <= a < sp0 + (-345 + L) + (7)))).
- exact VI8.
- exact HAR8'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat8' mat8 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr8'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm8'. }
assert (STRBUF8' : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms8') (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF8 i Hi). apply Hfr8'; [lia | unfold OSP_FX; lia | lia]. }
assert (LIT2BUF8' : forall i, (i < 7)%nat -> aview tfibsegs (w_H W) (ms_mem ms8') (sp0 + (-345 + L) + Z.of_nat i) = Some (nth i lit_usage2 0)).
{ intros i Hi. rewrite (Heff8' (Z.of_nat i)) by lia. apply LIT2AV8. exact Hi. }
remember (havoc E6 114 (map (getr (ms_regs ms8')) CLOB)) as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 114)%nat -> ew E7 j = ew E6 j) by (intros j Hj; rewrite HE7; apply ew_havoc_old; exact Hj).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (rewrite OLD7 by (cbv; lia); exact Usp6).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (rewrite OLD7 by (cbv; lia); exact G3_6).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (rewrite OLD7 by (cbv; lia); exact G4_6).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (rewrite OLD7 by (cbv; lia); exact G12_6).
assert (A32_7 : bv_unsigned (ew E7 32) = s) by (rewrite OLD7 by (cbv; lia); exact A32_6).
assert (A70_7 : bv_unsigned (ew E7 70) = L) by (rewrite OLD7 by (cbv; lia); exact A70_6).
assert (HAE7 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E7)
by (rewrite HE7; apply env_agree_havoc_ge; [cbv; lia | exact HAE6]).
clear HE7 HS8 VI8 SRA8' SHU8' Heff8' STRBUF8.
clear LIT2AV8.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E7 vu1_af8 vu1_st9 _ _ _ HS8' vu1_run9) HAI8').
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8'.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VI9 : VI B ly S W sp0 mem md (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms9) mat9 VI8') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF9. intros Hin. destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr9. intros Hin. destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms8') (ms_mem ms9) sp0 (-345) (proj1 (proj2 (proj2 VI8')))
(vf_band_present_n W E7 vu1_st9 ms9 sp0 (-345) HS9 ltac:(vm_compute; reflexivity) Usp7 ltac:(lia))).
intros a Ha. apply HF9. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (STRBUF9 : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms9) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF8' i Hi). apply aview_eq_of. apply HFr9. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (LIT2BUF9 : forall i, (i < 7)%nat -> aview tfibsegs (w_H W) (ms_mem ms9) (sp0 + (-345 + L) + Z.of_nat i) = Some (nth i lit_usage2 0)).
{ intros i Hi. rewrite <- (LIT2BUF8' i Hi). apply aview_eq_of. apply HFr9. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_af8 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI8' HF9 HFr9 STRBUF8' LIT2BUF8'.
pose proof (st_ok_add_cond_neg tfibsegs E7 vu1_st9 _ BC_EQ (SAlu ALU_ADD (SOff 2 (-338)) (SOff 70 0)) (SOff 2 (-352)) HS9 ltac:(rewrite branch_eq_U, U_add_off_atom, U_off by (rewrite ?Usp7, ?A70_7; unfold M64; lia); rewrite Usp7, A70_7; apply Z.eqb_neq; lia)) as HS9c.
change (YP06.add_cond vu1_st9 (mkAC (neg_bc BC_EQ) (SAlu ALU_ADD (SOff 2 (-338)) (SOff 70 0)) (SOff 2 (-352)))) with vu1_st9c in HS9c. clear HS9.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E7 vu1_st9c vu1_st10 _ _ _ HS9c vu1_run10) HAI9).
intros W10 c10 _ HAI10 (-> & ms10 & mat10 & -> & HS10 & HF10 & HFr10). cbn [cfg_model] in HAI10. clear HS9c.
rewrite ?wvb_wvb in HAI10 |- *.
assert (VI10 : VI B ly S W sp0 mem md (ms_mem ms10) (with_vm_backing (m_vm_lazy md) mat10 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms10) mat10 VI9) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF10. intros Hin. destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr10. intros Hin. destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms9) (ms_mem ms10) sp0 (-345) (proj1 (proj2 (proj2 VI9)))
(vf_band_present_n_ecall W E7 vu1_st10 ms10 sp0 (-345) HS10 ltac:(vm_compute; reflexivity) Usp7 ltac:(lia))).
intros a Ha. apply HF10. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (STRBUF10 : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms10) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF9 i Hi). apply aview_eq_of. apply HFr10. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (LIT2BUF10 : forall i, (i < 7)%nat -> aview tfibsegs (w_H W) (ms_mem ms10) (sp0 + (-345 + L) + Z.of_nat i) = Some (nth i lit_usage2 0)).
{ intros i Hi. rewrite <- (LIT2BUF9 i Hi). apply aview_eq_of. apply HFr10. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_st9c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI9 HF10 HFr10 STRBUF9 LIT2BUF9.
replace (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2) with ((map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2) ++ []) by apply app_nil_r.
pose proof HS10 as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & Hregs10 & Hmem10 & HG10). cbn [restrict ms_mem] in Hmem10.
pose proof (lit_buf_sound tfibsegs E7 (mrestrict (w_H W) (ms_mem ms10)) (ss_mem vu1_st10) (SLit (F_STDERR + 120)) 4 [2; 0; 0; 0] Hmem10
ltac:(vm_compute; reflexivity)) as Hfdrd. cbn [sv_denot] in Hfdrd.
assert (LIT1AV10 : forall i, (i < 7)%nat -> aview tfibsegs (w_H W) (ms_mem ms10) (sp0 + (-352) + Z.of_nat i) = Some (nth i lit_usage1 0)).
{ intros i Hi. apply (lit_buf_aview W E7 (ms_mem ms10) (ss_mem vu1_st10) (SOff 2 (-352)) (sp0 + (-352)) 7 lit_usage1 Hmem10 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Usp7; reflexivity) lit_usage1_range i Hi). }
eapply (srz_sym_stdio_writev2 W E7 vu1_st10 ms10 _ (Z_to_bv 64 2) ch 0 2 (-480) F_STDERR _ (SOff 2 (-352)) (SOff 70 14) (SLit 0) (SLit 0)
((map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) ([]) (map (Z_to_bv 8) [2; 0; 0; 0]) 130 T HAI10 HS10 eq_refl eq_refl eq_refl).
- reflexivity.
- eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
- reflexivity.
- vm_compute. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val, U_add_off_atom, U_off by (rewrite ?Usp7, ?A70_7; unfold M64; lia). rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val', U_add_off_atom, U_off by (rewrite ?Usp7, ?A70_7; unfold M64; lia). rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite U_SLit, !U_off by (rewrite A70_7; unfold M64; lia). change (zcanon 0) with 0. lia.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite U_SLit. reflexivity.
- reflexivity.
- reflexivity.
- cbn. lia. - cbn. lia. - cbn. lia. - cbn. lia.
- vm_compute. reflexivity.
-
rewrite word_to_nat_U, U_off by (rewrite A70_7; unfold M64; lia). cbn [sv_denot]. rewrite Usp7, A70_7.
replace (Z.to_nat (L + 14)) with (length lit_usage1 + length str + length lit_usage2)%nat by (rewrite HLlen; cbn; lia).
apply (rdn_cat3 (w_H W) (ms_mem ms10) (sp0 + (-352)) lit_usage1 str lit_usage2 lit_usage1_range lit_usage2_range LIT1AV10).
+ intros i Hi. replace (sp0 + (-352) + Z.of_nat (length lit_usage1) + Z.of_nat i) with (sp0 + (-345) + Z.of_nat i) by (cbn; lia). apply STRBUF10. exact Hi.
+ intros i Hi. replace (sp0 + (-352) + Z.of_nat (length lit_usage1) + Z.of_nat (length str) + Z.of_nat i) with (sp0 + (-345 + L) + Z.of_nat i) by (rewrite HLlen; cbn; lia).
apply LIT2BUF10. cbn in Hi. exact Hi.
-   reflexivity.
- rewrite U_SLit, U_off by (rewrite A70_7; unfold M64; lia). rewrite A70_7. change (zcanon 0) with 0. lia.
- rewrite !U_off by (rewrite ?Usp7, ?A70_7; unfold M64; lia). rewrite Usp7, A70_7. lia.
- rewrite !U_off by (rewrite ?Usp7, ?A70_7; unfold M64; lia). rewrite Usp7, A70_7. lia.
- rewrite !U_SLit. change (zcanon 0) with 0. lia.
- rewrite !U_SLit. change (zcanon 0) with 0. rewrite Usp7. lia.
- exact Hfdrd.
- vm_compute. reflexivity.
- unfold F_STDERR. lia.
- unfold F_STDERR. lia.
- rewrite Usp7. unfold F_STDERR. lia.
- rewrite Usp7. lia.
- rewrite Usp7. lia.
- vm_compute. reflexivity.
-
intros ms10' ws10' mat10' HS10' HF10' HFr10' HAI10'. rewrite ?wvb_wvb in HAI10' |- *.
change (wl_after vu1_st10 0 (-480) 130) with vu1_af10 in HS10'.
remember (havoc E7 130 ws10') as E8 eqn:HE8.
assert (OLD8 : forall j, (j < 130)%nat -> ew E8 j = ew E7 j) by (intros j Hj; rewrite HE8; apply ew_havoc_old; exact Hj).
assert (Usp8 : bv_unsigned (ew E8 2) = sp0) by (rewrite OLD8 by (cbv; lia); exact Usp7).
assert (G3_8 : ew E8 3 = w64 (as_gp B)) by (rewrite OLD8 by (cbv; lia); exact G3_7).
assert (G4_8 : ew E8 4 = w64 (as_tp B)) by (rewrite OLD8 by (cbv; lia); exact G4_7).
assert (G12_8 : bv_unsigned (ew E8 12) = ap) by (rewrite OLD8 by (cbv; lia); exact G12_7).
assert (A32_8 : bv_unsigned (ew E8 32) = s) by (rewrite OLD8 by (cbv; lia); exact A32_7).
assert (A70_8 : bv_unsigned (ew E8 70) = L) by (rewrite OLD8 by (cbv; lia); exact A70_7).
assert (HAE8 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E8)
by (rewrite HE8; apply env_agree_havoc_ge; [cbv; lia | exact HAE7]).
assert (VI10' : VI B ly S W sp0 mem md (ms_mem ms10') (with_vm_backing (m_vm_lazy md) mat10' md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms10') mat10' VI10) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF10'. intros Hin. destruct (vf_windows_sound_n E7 vu1_st10 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr10'. intros Hin. destruct (vf_windows_sound_n E7 vu1_st10 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms10) (ms_mem ms10') sp0 (-345) (proj1 (proj2 (proj2 VI10)))
(vf_band_present_n W E8 vu1_af10 ms10' sp0 (-345) HS10' ltac:(vm_compute; reflexivity) Usp8 ltac:(lia))).
intros a Ha. apply HF10'. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu1_st10 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear HE8 HS10 VI10 Hfdrd Hregs10 Hmem10 HG10 HF10' HFr10'.
clear STRBUF10 LIT2BUF10 LIT1AV10.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E8 vu1_af10 vu1_st11 _ _ _ HS10' vu1_run11) HAI10').
intros W11 c11 _ HAI11 (-> & ms11 & mat11 & -> & HS11 & HF11 & HFr11). cbn [cfg_model] in HAI11. clear HS10'.
rewrite ?wvb_wvb in HAI11 |- *.
assert (VI11 : VI B ly S W sp0 mem md (ms_mem ms11) (with_vm_backing (m_vm_lazy md) mat11 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms11) mat11 VI10') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF11. intros Hin. destruct (vf_windows_sound_n E8 vu1_af10 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp8 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr11. intros Hin. destruct (vf_windows_sound_n E8 vu1_af10 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp8 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms10') (ms_mem ms11) sp0 (-345) (proj1 (proj2 (proj2 VI10')))
(vf_band_present_n W E8 vu1_st11 ms11 sp0 (-345) HS11 ltac:(vm_compute; reflexivity) Usp8 ltac:(lia))).
intros a Ha. apply HF11. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E8 vu1_af10 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp8 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI10' HF11 HFr11.
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms11) (v_jalr (getr (ms_regs ms11) 1) 0) (ms_mem ms11) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | exact HAI11 | ].
{ eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E8); [exact HS11 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VI11 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS11 (1%bv : bv 5) Q1.
rewrite OLD8, OLD7, OLD6, OLD5, OLD3, OLD2, OLD1 in Q1 by (cbv; lia). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfibsegs (w_H W) E8 _ _ 10 HS11) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Q10 end.
rewrite denot_lit_U, !U_SAlu, !U_SLit in Q10. cbn [zalu_raw] in Q10. change (zcanon 0) with 0 in Q10.
rewrite !Z.lor_0_l, U_off in Q10 by (rewrite A70_8; unfold M64; lia). rewrite A70_8, !(zcanon_id (L + 14)) in Q10 by (unfold M64; lia).
replace (v_jalr (getr (ms_regs ms11) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
apply (HK (ms_regs ms11) (ms_mem ms11) (with_vm_backing (m_vm_lazy md) matR md)).
* apply (al_frame _ _ LAWS ly S W (ms_mem ms11) _ (ms_mem ms11) _ HAR9); [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | exact (AE2y.hs_kept_refl _ _)].
* exact (aregs_preserved_of_st_ok _ E8 _ _ regs [Z_to_bv 64 s; Z_to_bv 64 cval] HS11 HAE8 ltac:(vm_compute; reflexivity)).
* apply with_vm_backing_same.
* rewrite Q10. reflexivity.
* destruct HS11 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
unfold stderr_after_vfprintf, file_is, stderr_fields_after_vf.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit E8 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem vu1_st11) _ _ _ Hmem9); vm_compute; reflexivity).
* exact Hfr9.
* exact Hpm9.
* exact HAIR.
Qed.
Theorem tfib_vfprintf_usage_A2 : forall ly S (W : world tfibsegs) regs mem md ch ap s (str : list byte) L cval T,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 s ->
L = Z.of_nat (length str) -> 67 <= L -> L <= 73 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - VF_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF FMT_usage 17 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof.
intros ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HL HLlo HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDERR = 664952) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (rewrite KHI; lia).
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
assert (HLlen : length str = Z.to_nat L) by lia.
unfold cfg_at. change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vf_entry W regs mem FMT_usage (SOff 32 0) ap s cval Hsp44 Hsp47 Hal16
ltac:(intros a Ha; apply Hpres; exact Ha) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg ltac:(lia)
HFP Hgot Hcan Hcv Hro ltac:(cbn [sv_denot]; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS0.
change (ss_vf FMT_usage (SOff 32 0)) with vu0 in HS0.
remember (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; subst E0; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; apply unsigned_lit_small; lia).
assert (A32_0 : bv_unsigned (ew E0 32) = s) by (rewrite HE0, (ew_Ereg_extra regs _ 0); cbn [nth]; apply unsigned_lit_small; lia).
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E0) by (rewrite HE0; split; [intros i Hi; reflexivity | reflexivity]).
clear HE0 EE.
pose proof (VI_init B ly S W sp0 mem md HAR Hpres) as VI0.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 vu0 vu_st1 _ _ _ HS0 vu_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VI1 : VI B ly S W sp0 mem md (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms1) mat1 VI0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin); tauto.
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin); tauto.
- apply (vf_band_present W E0 vu_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VI0 HF1 HFr1.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms1) _ FMT_usage 17 88153 7 VI1 Hstk Hra_f Hhull_f
ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(rewrite KHI; unfold FMT_usage; lia)) as [SRA1' SHU1'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E0 vu_st1 ms1 _ ly S sp0 vu_r01 vu_rest1 34 RA_FX OSP_FX (-352) (SLit 88153) (88153) 7 lit_usage1
HS1 ltac:(rewrite HBcode; reflexivity) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E0 sp0 ap vu_rest1 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hap2)
(vf_rest_w E0 vu_rest1 ltac:(vm_compute; reflexivity))
(proj1 VI1) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI1))) SRA1' SHU1') HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
change (vf_after_icpt 34 vu_st1 RA_FX OSP_FX (-352) lit_usage1) with vu_af1 in HS1'.
assert (VI1' : VI B ly S W sp0 mem md (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 7))).
- exact VI1.
- exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr1'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (rewrite OLD1 by (cbv; lia); exact G12_0).
assert (A32_1 : bv_unsigned (ew E1 32) = s) by (rewrite OLD1 by (cbv; lia); exact A32_0).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
clear HE1 HS1 VI1 SRA1' SHU1'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E1 vu_af1 vu_st2 _ _ _ HS1' vu_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VI2 : VI B ly S W sp0 mem md (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms2) mat2 VI1') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin); tauto.
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin); tauto.
- apply (vf_band_present W E1 vu_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VI1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF 88160 0) by (intros y Hy; lia).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms2)) 88160 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E1 vu_st2 ms2 _ ly S sp0 vu_r02 vu_rest2 50 RA_FX OSP_FX (-345) (SLit 88160) (88160) 0 (@nil Z)
HS2 ltac:(rewrite HBcode; reflexivity) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E1 sp0 ap vu_rest2 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hap2)
(vf_rest_w E1 vu_rest2 ltac:(vm_compute; reflexivity))
(proj1 VI2) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI2))) SRA2' SHU2') HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 50 vu_st2 RA_FX OSP_FX (-345) (@nil Z)) with vu_af2 in HS2'.
assert (VI2' : VI B ly S W sp0 mem md (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- exact VI2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (rewrite OLD2 by (cbv; lia); exact G12_1).
assert (A32_2 : bv_unsigned (ew E2 32) = s) by (rewrite OLD2 by (cbv; lia); exact A32_1).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2 HS2 VI2 SRA2' SHU2'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E2 vu_af2 vu_st3 _ _ _ HS2' vu_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VI3 : VI B ly S W sp0 mem md (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms3) mat3 VI2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin); tauto.
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin); tauto.
- apply (vf_band_present W E2 vu_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VI2' HF3 HFr3.
assert (STR3 : vf_str W (ms_mem ms3) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI3)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms3) _ s (L + 1) s (L + 1) VI3 Hstk Hra_s Hhull_s
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [SRA3' SHU3'].
pose proof (vf_tail_xfer W mem (ms_mem ms3) sp0 s L Hstail (proj1 (proj2 (proj2 (proj2 VI3)))) Hal16 ltac:(lia) ltac:(lia) ltac:(lia) Hsband Hsfile) as TAIL3.
pose proof (mconsts_view_xfer W mem (ms_mem ms3) sp0 Hromv (proj1 (proj2 (proj2 (proj2 VI3)))) Hsp44) as ROM3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_strnlen B ASTRNLEN W E2 vu_st3 ms3 _ ly S sp0 vu_r03 vu_rest3 66 RA_SN OSP_SN (SOff 32 0) s INT_MAX L
HS3 ltac:(rewrite HBcode; reflexivity) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, <- A32_2, Z_to_bv_bv_unsigned; reflexivity) ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_SN; lia) ltac:(unfold OSP_SN; lia) ltac:(unfold RA_SN; lia) ltac:(reflexivity)
ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(unfold OSP_SN; lia)
(vf_rest_ok E2 sp0 ap vu_rest3 ltac:(vm_compute; reflexivity) G12_2 Hap1 Hap2)
(vf_rest_w E2 vu_rest3 ltac:(vm_compute; reflexivity))
(proj1 VI3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VI3)))
ltac:(rewrite HL; apply (vf_str_first_byte W _ s str INT_MAX STR3); unfold INT_MAX; lia)
ltac:(intros a Ha; apply (vf_str_readable W _ s str STR3); lia)
Hams SRA3' (SHU3' ltac:(lia)) TAIL3 ROM3) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & HL3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 66 vu_st3 RA_SN OSP_SN 0 []) with vu_af3 in HS3'.
assert (VI3' : VI B ly S W sp0 mem md (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms3) _ (ms_mem ms3') _
(fun a => sp0 + OSP_SN - 2 * ESTACK <= a < sp0 + OSP_SN)).
- exact VI3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_SN in *. lia.
- intros a Hr Hna. apply Hfr3'; [exact Hr | exact Hna].
- exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (rewrite OLD3 by (cbv; lia); exact G12_2).
assert (A32_3 : bv_unsigned (ew E3 32) = s) by (rewrite OLD3 by (cbv; lia); exact A32_2).
assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
assert (A70_3 : bv_unsigned (ew E3 70) = L).
{ rewrite HE3, (ew_havoc_new E2 66 _ 4 (w64 0)) by (cbn; lia). unfold CLOB. cbn [nth map]. rewrite HL3'. apply unsigned_lit_small. lia. }
clear HE3 HS3 VI3 SRA3' SHU3' STR3.
pose proof (st_ok_add_fact E3 vu_af3 _ 70 67 73 HS3' eq_refl ltac:(rewrite A70_3; lia)) as HS3f.
change (vf_add_fact vu_af3 70 (mkAF 67 73 0)) with vu2_af3f in HS3f. clear HS3'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 vu2_af3f vu2_st4 _ _ _ HS3f vu2_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3f.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VI4 : VI B ly S W sp0 mem md (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms4) mat4 VI3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (vf_windows_sound E3 vu2_af3f sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (vf_windows_sound E3 vu2_af3f sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- apply (vf_band_present W E3 vu2_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VI3' HF4 HFr4.
assert (STR4 : vf_str W (ms_mem ms4) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI4)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
assert (R11_4 : getr (ms_regs ms4) 11 = Z_to_bv 64 (s + L)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 _ _ 11 HS4).
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite denot_lit_U, U_add_off_atom by (rewrite ?A32_3, ?A70_3; unfold M64; lia). rewrite A32_3, A70_3. f_equal. lia. }
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_lbu_nul W E3 vu2_st4 ms4 _ 82 (s + L) HS4 eq_refl eq_refl ltac:(vm_compute; reflexivity) R11_4 ltac:(lia)
ltac:(rewrite HL; exact (proj1 (proj2 STR4)))) HAI4).
intros W4l c4l _ HAI4l (-> & ms4l & mat4l & -> & HS4l & Hmm4l). cbn [cfg_model] in HAI4l. rewrite ?wvb_wvb in HAI4l |- *.
change (set_regs_pc vu2_st4 [((12%bv : bv 5), SLit 0)] 0x942a4) with vu2_af4 in HS4l.
assert (VI4l : VI B ly S W sp0 mem md (ms_mem ms4l) (with_vm_backing (m_vm_lazy md) mat4l md)).
{ rewrite Hmm4l. pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms4) mat4l VI4) as VR.
rewrite ?wvb_wvb in VR. apply VR; [intros; reflexivity | intros; reflexivity | exact (proj1 (proj2 (proj2 VI4)))]. }
clear VI4 HS4 STR4 R11_4.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 vu2_af4 vu2_st5 _ _ _ HS4l vu2_run5) HAI4l).
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4l.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VI5 : VI B ly S W sp0 mem md (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms5) mat5 VI4l) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF5. intros Hin. destruct (vf_windows_sound E3 vu2_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- intros x Hx1 Hx2. apply HFr5. intros Hin. destruct (vf_windows_sound E3 vu2_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- apply (vf_band_present W E3 vu2_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VI4l HF5 HFr5.
assert (SRA5' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms5)) SHADOW_OFF 68444 0) by (intros y Hy; lia).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms5)) 68444 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E3 vu2_st5 ms5 _ ly S sp0 vu2_r05 vu2_rest5 82 RA_FX OSP_FX (-345) (SLit 68444) (68444) 0 (@nil Z)
HS5 ltac:(rewrite HBcode; reflexivity) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E3 sp0 ap vu2_rest5 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hap2)
(vf_rest_w E3 vu2_rest5 ltac:(vm_compute; reflexivity))
(proj1 VI5) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI5))) SRA5' SHU5') HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
change (vf_after_icpt 82 vu2_st5 RA_FX OSP_FX (-345) (@nil Z)) with vu2_af5 in HS5'.
assert (VI5' : VI B ly S W sp0 mem md (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- exact VI5.
- exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr5'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm5'. }
remember (havoc E3 82 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 82)%nat -> ew E5 j = ew E3 j) by (intros j Hj; rewrite HE5; apply ew_havoc_old; exact Hj).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by (cbv; lia); exact Usp3).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (rewrite OLD5 by (cbv; lia); exact G3_3).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (rewrite OLD5 by (cbv; lia); exact G4_3).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (rewrite OLD5 by (cbv; lia); exact G12_3).
assert (A32_5 : bv_unsigned (ew E5 32) = s) by (rewrite OLD5 by (cbv; lia); exact A32_3).
assert (A70_5 : bv_unsigned (ew E5 70) = L) by (rewrite OLD5 by (cbv; lia); exact A70_3).
assert (HAE5 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE5 HS5 VI5 SRA5' SHU5'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 vu2_af5 vu2_st6 _ _ _ HS5' vu2_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VI6 : VI B ly S W sp0 mem md (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms6) mat6 VI5') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6. intros Hin. destruct (vf_windows_sound E5 vu2_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- intros x Hx1 Hx2. apply HFr6. intros Hin. destruct (vf_windows_sound E5 vu2_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- apply (vf_band_present W E5 vu2_st6 ms6 sp0 HS6 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
clear VI5' HF6 HFr6.
assert (STR6 : vf_str W (ms_mem ms6) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI6)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms6) _ s (L + 1) s L VI6 Hstk Hra_s Hhull_s
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [SRA6' SHU6'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_sym B LAWS AMEMCPY W E5 vu2_st6 ms6 _ ly S sp0 vu2_r06 vu2_rest6 98 RA_FX OSP_FX (-345) (-272)
(SOff 2 (-345)) (SOff 32 0) (SOff 70 0) (-345) (s) (L)
HS6 ltac:(rewrite HBcode; reflexivity) eq_refl Usp5 G3_5 G4_5 eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(cbn; lia)
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Usp5; reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A32_5; reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A70_5; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(lia) ltac:(unfold OSP_FX; lia) ltac:(lia) ltac:(destruct Hams as [Hams'|[Hams' Hams'']]; [left; lia | right; lia])
(vf_rest_ok E5 sp0 ap vu2_rest6 ltac:(vm_compute; reflexivity) G12_5 Hap1 Hap2)
(vf_rest_w E5 vu2_rest6 ltac:(vm_compute; reflexivity))
(proj1 VI6) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI6)))
ltac:(intros a Ha; apply (vf_str_readable W _ s str STR6); lia) SRA6' SHU6') HAI6).
intros W6' c6' _ HAI6' (-> & ms6' & mat6' & -> & HS6' & HAR6' & HP6' & Heff6' & Hfr6' & Hpm6'). cbn [cfg_model] in HAI6'.
rewrite wvb_wvb in HAI6', HAR6' |- *.
change (vf_after_icpt_n 98 vu2_st6 RA_FX OSP_FX (-345) (-272)) with vu2_af6 in HS6'.
assert (VI6' : VI B ly S W sp0 mem md (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms6) _ (ms_mem ms6') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + (L)))).
- exact VI6.
- exact HAR6'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat6' mat6 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr6'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm6'. }
assert (STRBUF6' : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms6') (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite (Heff6' (Z.of_nat i)) by lia. apply (proj1 STR6). exact Hi. }
remember (havoc E5 98 (map (getr (ms_regs ms6')) CLOB)) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 98)%nat -> ew E6 j = ew E5 j) by (intros j Hj; rewrite HE6; apply ew_havoc_old; exact Hj).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by (cbv; lia); exact Usp5).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (rewrite OLD6 by (cbv; lia); exact G3_5).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (rewrite OLD6 by (cbv; lia); exact G4_5).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (rewrite OLD6 by (cbv; lia); exact G12_5).
assert (A32_6 : bv_unsigned (ew E6 32) = s) by (rewrite OLD6 by (cbv; lia); exact A32_5).
assert (A70_6 : bv_unsigned (ew E6 70) = L) by (rewrite OLD6 by (cbv; lia); exact A70_5).
assert (HAE6 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E6)
by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
clear HE6 HS6 VI6 SRA6' SHU6' Heff6'.
clear STR6.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 vu2_af6 vu2_st7 _ _ _ HS6' vu2_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VI7 : VI B ly S W sp0 mem md (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms7) mat7 VI6') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7. intros Hin. destruct (vf_windows_sound_n E6 vu2_af6 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr7. intros Hin. destruct (vf_windows_sound_n E6 vu2_af6 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms6') (ms_mem ms7) sp0 (-345) (proj1 (proj2 (proj2 VI6')))
(vf_band_present_n W E6 vu2_st7 ms7 sp0 (-345) HS7 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia))).
intros a Ha. apply HF7. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_af6 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (STRBUF7 : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms7) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF6' i Hi). apply aview_eq_of. apply HFr7. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_af6 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI6' HF7 HFr7 STRBUF6'.
pose proof (st_ok_add_cond_neg tfibsegs E6 vu2_st7 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7) HS7 ltac:(rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A70_6; unfold M64; lia); rewrite A70_6; change (zcanon 7) with 7; apply Bool.negb_false_iff; apply Z.ltb_lt; lia)) as HS7c.
change (YP06.add_cond vu2_st7 (mkAC (neg_bc BC_GEU) (SAlu ALU_SUB (SLit 0) (SOff 70 (-73))) (SLit 7))) with vu2_st7c in HS7c. clear HS7.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 vu2_st7c vu2_st8 _ _ _ HS7c vu2_run8) HAI7).
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8. clear HS7c.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VI8 : VI B ly S W sp0 mem md (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms8) mat8 VI7) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF8. intros Hin. destruct (vf_windows_sound_n E6 vu2_st7c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr8. intros Hin. destruct (vf_windows_sound_n E6 vu2_st7c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms7) (ms_mem ms8) sp0 (-345) (proj1 (proj2 (proj2 VI7)))
(vf_band_present_n W E6 vu2_st8 ms8 sp0 (-345) HS8 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia))).
intros a Ha. apply HF8. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st7c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (STRBUF8 : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms8) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF7 i Hi). apply aview_eq_of. apply HFr8. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st7c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI7 HF8 HFr8 STRBUF7.
pose proof (st_ok_add_cond_neg tfibsegs E6 vu2_st8 _ BC_EQ (SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SOff 2 (-352)) HS8 ltac:(rewrite branch_eq_U, U_add_off_atom, U_off by (rewrite ?Usp6, ?A70_6; unfold M64; lia); rewrite Usp6, A70_6; apply Z.eqb_neq; lia)) as HS8c.
change (YP06.add_cond vu2_st8 (mkAC (neg_bc BC_EQ) (SAlu ALU_ADD (SOff 2 (-345)) (SOff 70 0)) (SOff 2 (-352)))) with vu2_st8c in HS8c. clear HS8.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 vu2_st8c vu2_st9 _ _ _ HS8c vu2_run9) HAI8).
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8c.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VI9 : VI B ly S W sp0 mem md (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms9) mat9 VI8) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF9. intros Hin. destruct (vf_windows_sound_n E6 vu2_st8c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr9. intros Hin. destruct (vf_windows_sound_n E6 vu2_st8c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms8) (ms_mem ms9) sp0 (-345) (proj1 (proj2 (proj2 VI8)))
(vf_band_present_n_ecall W E6 vu2_st9 ms9 sp0 (-345) HS9 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia))).
intros a Ha. apply HF9. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st8c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
assert (STRBUF9 : forall i, (i < length str)%nat -> aview tfibsegs (w_H W) (ms_mem ms9) (sp0 + (-345) + Z.of_nat i) = Some (bv_unsigned (nth i str 0%bv))).
{ intros i Hi. rewrite <- (STRBUF8 i Hi). apply aview_eq_of. apply HFr9. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st8c sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI8 HF9 HFr9 STRBUF8.
rewrite (app_assoc (map (Z_to_bv 8) lit_usage1) str (map (Z_to_bv 8) lit_usage2)).
pose proof HS9 as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & Hregs9 & Hmem9 & HG9). cbn [restrict ms_mem] in Hmem9.
pose proof (lit_buf_sound tfibsegs E6 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem vu2_st9) (SLit (F_STDERR + 120)) 4 [2; 0; 0; 0] Hmem9
ltac:(vm_compute; reflexivity)) as Hfdrd. cbn [sv_denot] in Hfdrd.
assert (LIT1AV9 : forall i, (i < 7)%nat -> aview tfibsegs (w_H W) (ms_mem ms9) (sp0 + (-352) + Z.of_nat i) = Some (nth i lit_usage1 0)).
{ intros i Hi. apply (lit_buf_aview W E6 (ms_mem ms9) (ss_mem vu2_st9) (SOff 2 (-352)) (sp0 + (-352)) 7 lit_usage1 Hmem9 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Usp6; reflexivity) lit_usage1_range i Hi). }
pose proof (lit_buf_sound tfibsegs E6 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem vu2_st9) (SLit 88162) 7 lit_usage2 Hmem9
ltac:(vm_compute; reflexivity)) as Hl2rd.
eapply (srz_sym_stdio_writev2 W E6 vu2_st9 ms9 _ (Z_to_bv 64 2) ch 0 2 (-1024) F_STDERR _ (SOff 2 (-352)) (SOff 70 7) (SLit 88162) (SLit 7)
((map (Z_to_bv 8) lit_usage1 ++ str)) (map (Z_to_bv 8) lit_usage2) (map (Z_to_bv 8) [2; 0; 0; 0]) 114 T HAI9 HS9 eq_refl eq_refl eq_refl).
- reflexivity.
- eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
- reflexivity.
- vm_compute. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val, U_add_off_atom, U_off by (rewrite ?Usp6, ?A70_6; unfold M64; lia). rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val', U_add_off_atom, U_off by (rewrite ?Usp6, ?A70_6; unfold M64; lia). rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite U_SLit, !U_off by (rewrite A70_6; unfold M64; lia). rewrite A70_6. change (zcanon 7) with 7. lia.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite U_SLit. reflexivity.
- reflexivity.
- reflexivity.
- cbn. lia. - cbn. lia. - cbn. lia. - cbn. lia.
- vm_compute. reflexivity.
-
rewrite word_to_nat_U, U_off by (rewrite A70_6; unfold M64; lia). cbn [sv_denot]. rewrite Usp6, A70_6.
replace (Z.to_nat (L + 7)) with (length lit_usage1 + length str + @length Z [])%nat by (rewrite HLlen; cbn; lia).
replace (map (Z_to_bv 8) lit_usage1 ++ str) with (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) []) by (cbn [map]; rewrite app_nil_r; reflexivity).
apply (rdn_cat3 (w_H W) (ms_mem ms9) (sp0 + (-352)) lit_usage1 str [] lit_usage1_range ltac:(constructor) LIT1AV9).
+ intros i Hi. replace (sp0 + (-352) + Z.of_nat (length lit_usage1) + Z.of_nat i) with (sp0 + (-345) + Z.of_nat i) by (cbn; lia). apply STRBUF9. exact Hi.
+ intros i Hi. cbn in Hi. lia.
-   change (word_to_nat (sv_denot E6 (SLit 7))) with 7%nat. exact Hl2rd.
- rewrite U_SLit, U_off by (rewrite A70_6; unfold M64; lia). rewrite A70_6. change (zcanon 7) with 7. lia.
- rewrite !U_off by (rewrite ?Usp6, ?A70_6; unfold M64; lia). rewrite Usp6, A70_6. lia.
- rewrite !U_off by (rewrite ?Usp6, ?A70_6; unfold M64; lia). rewrite Usp6, A70_6. lia.
- rewrite !U_SLit. change (zcanon 88162) with 88162. change (zcanon 7) with 7. lia.
- rewrite !U_SLit. change (zcanon 88162) with 88162. change (zcanon 7) with 7. rewrite Usp6. lia.
- exact Hfdrd.
- vm_compute. reflexivity.
- unfold F_STDERR. lia.
- unfold F_STDERR. lia.
- rewrite Usp6. unfold F_STDERR. lia.
- rewrite Usp6. lia.
- rewrite Usp6. lia.
- vm_compute. reflexivity.
-
intros ms9' ws9' mat9' HS9' HF9' HFr9' HAI9'. rewrite ?wvb_wvb in HAI9' |- *.
change (wl_after vu2_st9 0 (-1024) 114) with vu2_af9 in HS9'.
remember (havoc E6 114 ws9') as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 114)%nat -> ew E7 j = ew E6 j) by (intros j Hj; rewrite HE7; apply ew_havoc_old; exact Hj).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (rewrite OLD7 by (cbv; lia); exact Usp6).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (rewrite OLD7 by (cbv; lia); exact G3_6).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (rewrite OLD7 by (cbv; lia); exact G4_6).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (rewrite OLD7 by (cbv; lia); exact G12_6).
assert (A32_7 : bv_unsigned (ew E7 32) = s) by (rewrite OLD7 by (cbv; lia); exact A32_6).
assert (A70_7 : bv_unsigned (ew E7 70) = L) by (rewrite OLD7 by (cbv; lia); exact A70_6).
assert (HAE7 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E7)
by (rewrite HE7; apply env_agree_havoc_ge; [cbv; lia | exact HAE6]).
assert (VI9' : VI B ly S W sp0 mem md (ms_mem ms9') (with_vm_backing (m_vm_lazy md) mat9' md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms9') mat9' VI9) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF9'. intros Hin. destruct (vf_windows_sound_n E6 vu2_st9 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr9'. intros Hin. destruct (vf_windows_sound_n E6 vu2_st9 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms9) (ms_mem ms9') sp0 (-345) (proj1 (proj2 (proj2 VI9)))
(vf_band_present_n W E7 vu2_af9 ms9' sp0 (-345) HS9' ltac:(vm_compute; reflexivity) Usp7 ltac:(lia))).
intros a Ha. apply HF9'. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E6 vu2_st9 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear HE7 HS9 VI9 Hfdrd Hregs9 Hmem9 HG9 HF9' HFr9'.
clear STRBUF9 LIT1AV9 Hl2rd.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E7 vu2_af9 vu2_st10 _ _ _ HS9' vu2_run10) HAI9').
intros W10 c10 _ HAI10 (-> & ms10 & mat10 & -> & HS10 & HF10 & HFr10). cbn [cfg_model] in HAI10. clear HS9'.
rewrite ?wvb_wvb in HAI10 |- *.
assert (VI10 : VI B ly S W sp0 mem md (ms_mem ms10) (with_vm_backing (m_vm_lazy md) mat10 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms10) mat10 VI9') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF10. intros Hin. destruct (vf_windows_sound_n E7 vu2_af9 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr10. intros Hin. destruct (vf_windows_sound_n E7 vu2_af9 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms9') (ms_mem ms10) sp0 (-345) (proj1 (proj2 (proj2 VI9')))
(vf_band_present_n_ecall W E7 vu2_st10 ms10 sp0 (-345) HS10 ltac:(vm_compute; reflexivity) Usp7 ltac:(lia))).
intros a Ha. apply HF10. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu2_af9 sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI9' HF10 HFr10.
eapply (srz_sym_writev_empty W E7 vu2_st10 ms10 _ (Z_to_bv 64 2) ch 0 2 _ (Some 2%nat) (-456) (SLit 0) (SLit 0) T HAI10 HS10 eq_refl eq_refl).
+ reflexivity.
+ eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
+ reflexivity.
+ match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val. rewrite Z.eqb_refl. reflexivity.
+ match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite U_off by (rewrite Usp7; unfold M64; lia). cbn [base_val]. reflexivity.
+ vm_compute. reflexivity.
+ rewrite U_SLit. reflexivity.
+ reflexivity.
+ reflexivity.
+ cbn. lia.
+ cbn. lia.
+ cbn [base_val]. rewrite Usp7. lia.
+ cbn [base_val]. rewrite Usp7. lia.
+ cbn [base_val]. rewrite Usp7. lia.
+ match goal with |- U _ ?x <= _ => let x' := eval vm_compute in x in change x with x' end;
first [ rewrite U_off by (rewrite Usp7; unfold M64; lia); cbn [base_val]; rewrite Usp7; lia | rewrite U_SLit; (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) | rewrite U_SLit; cbn; lia ].
+ intros ms10r mat10r HS10r Hmm10r HAI10r. rewrite ?wvb_wvb in HAI10r |- *.
change (resume vu2_st10 (SLit 0) (ss_mem vu2_st10) (ss_facts vu2_st10)) with vu2_st10r in HS10r.
assert (VI10r : VI B ly S W sp0 mem md (ms_mem ms10r) (with_vm_backing (m_vm_lazy md) mat10r md)).
{ rewrite Hmm10r. pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms10) mat10r VI10) as VR.
rewrite ?wvb_wvb in VR. apply VR; [intros; reflexivity | intros; reflexivity | exact (proj1 (proj2 (proj2 VI10)))]. }
clear VI10 HS10.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E7 vu2_st10r vu2_st11 _ _ _ HS10r vu2_run11) HAI10r).
intros W11 c11 _ HAI11 (-> & ms11 & mat11 & -> & HS11 & HF11 & HFr11). cbn [cfg_model] in HAI11. clear HS10r.
rewrite ?wvb_wvb in HAI11 |- *.
assert (VI11 : VI B ly S W sp0 mem md (ms_mem ms11) (with_vm_backing (m_vm_lazy md) mat11 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms11) mat11 VI10r) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF11. intros Hin. destruct (vf_windows_sound_n E7 vu2_st10r sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- intros x Hx1 Hx2. apply HFr11. intros Hin. destruct (vf_windows_sound_n E7 vu2_st10r sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [apply Hx1; unfold vf_band; lia | tauto].
- apply (vf_band_present_gap W (ms_mem ms10r) (ms_mem ms11) sp0 (-345) (proj1 (proj2 (proj2 VI10r)))
(vf_band_present_n W E7 vu2_st11 ms11 sp0 (-345) HS11 ltac:(vm_compute; reflexivity) Usp7 ltac:(lia))).
intros a Ha. apply HF11. rewrite unsigned_lit_small by lia. intros Hin.
destruct (vf_windows_sound_n E7 vu2_st10r sp0 (-345) _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [lia | unfold vf_file in Hw; lia]. }
clear VI10r HF11 HFr11.
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms11) (v_jalr (getr (ms_regs ms11) 1) 0) (ms_mem ms11) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | exact HAI11 | ].
{ eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E7); [exact HS11 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VI11 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS11 (1%bv : bv 5) Q1.
rewrite OLD7, OLD6, OLD5, OLD3, OLD2, OLD1 in Q1 by (cbv; lia). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfibsegs (w_H W) E7 _ _ 10 HS11) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Q10 end.
rewrite denot_lit_U, !U_SAlu, !U_SLit in Q10. cbn [zalu_raw] in Q10. change (zcanon 0) with 0 in Q10.
rewrite !Z.lor_0_l, U_off in Q10 by (rewrite A70_7; unfold M64; lia). rewrite A70_7, !(zcanon_id (L + 14)) in Q10 by (unfold M64; lia).
replace (v_jalr (getr (ms_regs ms11) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
apply (HK (ms_regs ms11) (ms_mem ms11) (with_vm_backing (m_vm_lazy md) matR md)).
* apply (al_frame _ _ LAWS ly S W (ms_mem ms11) _ (ms_mem ms11) _ HAR9); [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | exact (AE2y.hs_kept_refl _ _)].
* exact (aregs_preserved_of_st_ok _ E7 _ _ regs [Z_to_bv 64 s; Z_to_bv 64 cval] HS11 HAE7 ltac:(vm_compute; reflexivity)).
* apply with_vm_backing_same.
* rewrite Q10. reflexivity.
* destruct HS11 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
unfold stderr_after_vfprintf, file_is, stderr_fields_after_vf.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit E7 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem vu2_st11) _ _ _ Hmem9); vm_compute; reflexivity).
* exact Hfr9.
* exact Hpm9.
* exact HAIR.
Qed.
Theorem tfib_vfprintf_usage_A3 : forall ly S (W : world tfibsegs) regs mem md ch ap s (str : list byte) L cval T,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 s ->
L = Z.of_nat (length str) -> 74 <= L -> L <= 33554425 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - VF_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF FMT_usage 17 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof.
intros ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HL HLlo HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
assert (HFF : F_STDERR = 664952) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (rewrite KHI; lia).
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
assert (HLlen : length str = Z.to_nat L) by lia.
unfold cfg_at. change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vf_entry W regs mem FMT_usage (SOff 32 0) ap s cval Hsp44 Hsp47 Hal16
ltac:(intros a Ha; apply Hpres; exact Ha) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg ltac:(lia)
HFP Hgot Hcan Hcv Hro ltac:(cbn [sv_denot]; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS0.
change (ss_vf FMT_usage (SOff 32 0)) with vu0 in HS0.
remember (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; subst E0; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; apply unsigned_lit_small; lia).
assert (A32_0 : bv_unsigned (ew E0 32) = s) by (rewrite HE0, (ew_Ereg_extra regs _ 0); cbn [nth]; apply unsigned_lit_small; lia).
assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E0) by (rewrite HE0; split; [intros i Hi; reflexivity | reflexivity]).
clear HE0 EE.
pose proof (VI_init B ly S W sp0 mem md HAR Hpres) as VI0.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 vu0 vu_st1 _ _ _ HS0 vu_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VI1 : VI B ly S W sp0 mem md (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms1) mat1 VI0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin); tauto.
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (vf_windows_sound E0 vu0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin); tauto.
- apply (vf_band_present W E0 vu_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VI0 HF1 HFr1.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms1) _ FMT_usage 17 88153 7 VI1 Hstk Hra_f Hhull_f
ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(rewrite KHI; unfold FMT_usage; lia)) as [SRA1' SHU1'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E0 vu_st1 ms1 _ ly S sp0 vu_r01 vu_rest1 34 RA_FX OSP_FX (-352) (SLit 88153) (88153) 7 lit_usage1
HS1 ltac:(rewrite HBcode; reflexivity) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E0 sp0 ap vu_rest1 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hap2)
(vf_rest_w E0 vu_rest1 ltac:(vm_compute; reflexivity))
(proj1 VI1) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI1))) SRA1' SHU1') HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Hfr1' & Hpm1'). cbn [cfg_model] in HAI1'.
rewrite wvb_wvb in HAI1', HAR1' |- *.
change (vf_after_icpt 34 vu_st1 RA_FX OSP_FX (-352) lit_usage1) with vu_af1 in HS1'.
assert (VI1' : VI B ly S W sp0 mem md (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 7))).
- exact VI1.
- exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr1'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (rewrite OLD1 by (cbv; lia); exact G12_0).
assert (A32_1 : bv_unsigned (ew E1 32) = s) by (rewrite OLD1 by (cbv; lia); exact A32_0).
assert (HAE1 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
clear HE1 HS1 VI1 SRA1' SHU1'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E1 vu_af1 vu_st2 _ _ _ HS1' vu_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2. clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VI2 : VI B ly S W sp0 mem md (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms2) mat2 VI1') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin); tauto.
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (vf_windows_sound E1 vu_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin); tauto.
- apply (vf_band_present W E1 vu_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VI1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF 88160 0) by (intros y Hy; lia).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms2)) 88160 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E1 vu_st2 ms2 _ ly S sp0 vu_r02 vu_rest2 50 RA_FX OSP_FX (-345) (SLit 88160) (88160) 0 (@nil Z)
HS2 ltac:(rewrite HBcode; reflexivity) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E1 sp0 ap vu_rest2 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hap2)
(vf_rest_w E1 vu_rest2 ltac:(vm_compute; reflexivity))
(proj1 VI2) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI2))) SRA2' SHU2') HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2'). cbn [cfg_model] in HAI2'.
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 50 vu_st2 RA_FX OSP_FX (-345) (@nil Z)) with vu_af2 in HS2'.
assert (VI2' : VI B ly S W sp0 mem md (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- exact VI2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (rewrite OLD2 by (cbv; lia); exact G12_1).
assert (A32_2 : bv_unsigned (ew E2 32) = s) by (rewrite OLD2 by (cbv; lia); exact A32_1).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2 HS2 VI2 SRA2' SHU2'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E2 vu_af2 vu_st3 _ _ _ HS2' vu_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VI3 : VI B ly S W sp0 mem md (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms3) mat3 VI2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin); tauto.
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (vf_windows_sound E2 vu_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin); tauto.
- apply (vf_band_present W E2 vu_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VI2' HF3 HFr3.
assert (STR3 : vf_str W (ms_mem ms3) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI3)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms3) _ s (L + 1) s (L + 1) VI3 Hstk Hra_s Hhull_s
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [SRA3' SHU3'].
pose proof (vf_tail_xfer W mem (ms_mem ms3) sp0 s L Hstail (proj1 (proj2 (proj2 (proj2 VI3)))) Hal16 ltac:(lia) ltac:(lia) ltac:(lia) Hsband Hsfile) as TAIL3.
pose proof (mconsts_view_xfer W mem (ms_mem ms3) sp0 Hromv (proj1 (proj2 (proj2 (proj2 VI3)))) Hsp44) as ROM3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_strnlen B ASTRNLEN W E2 vu_st3 ms3 _ ly S sp0 vu_r03 vu_rest3 66 RA_SN OSP_SN (SOff 32 0) s INT_MAX L
HS3 ltac:(rewrite HBcode; reflexivity) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, <- A32_2, Z_to_bv_bv_unsigned; reflexivity) ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_SN; lia) ltac:(unfold OSP_SN; lia) ltac:(unfold RA_SN; lia) ltac:(reflexivity)
ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX; lia) ltac:(lia) ltac:(lia) ltac:(unfold OSP_SN; lia)
(vf_rest_ok E2 sp0 ap vu_rest3 ltac:(vm_compute; reflexivity) G12_2 Hap1 Hap2)
(vf_rest_w E2 vu_rest3 ltac:(vm_compute; reflexivity))
(proj1 VI3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VI3)))
ltac:(rewrite HL; apply (vf_str_first_byte W _ s str INT_MAX STR3); unfold INT_MAX; lia)
ltac:(intros a Ha; apply (vf_str_readable W _ s str STR3); lia)
Hams SRA3' (SHU3' ltac:(lia)) TAIL3 ROM3) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & HL3' & Hfr3' & Hpm3'). cbn [cfg_model] in HAI3'.
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 66 vu_st3 RA_SN OSP_SN 0 []) with vu_af3 in HS3'.
assert (VI3' : VI B ly S W sp0 mem md (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms3) _ (ms_mem ms3') _
(fun a => sp0 + OSP_SN - 2 * ESTACK <= a < sp0 + OSP_SN)).
- exact VI3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_SN in *. lia.
- intros a Hr Hna. apply Hfr3'; [exact Hr | exact Hna].
- exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (rewrite OLD3 by (cbv; lia); exact G12_2).
assert (A32_3 : bv_unsigned (ew E3 32) = s) by (rewrite OLD3 by (cbv; lia); exact A32_2).
assert (HAE3 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
assert (A70_3 : bv_unsigned (ew E3 70) = L).
{ rewrite HE3, (ew_havoc_new E2 66 _ 4 (w64 0)) by (cbn; lia). unfold CLOB. cbn [nth map]. rewrite HL3'. apply unsigned_lit_small. lia. }
clear HE3 HS3 VI3 SRA3' SHU3' STR3.
pose proof (st_ok_add_fact E3 vu_af3 _ 70 74 33554425 HS3' eq_refl ltac:(rewrite A70_3; lia)) as HS3f.
change (vf_add_fact vu_af3 70 (mkAF 74 33554425 0)) with vu3_af3f in HS3f. clear HS3'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 vu3_af3f vu3_st4 _ _ _ HS3f vu3_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4. clear HS3f.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VI4 : VI B ly S W sp0 mem md (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms4) mat4 VI3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (vf_windows_sound E3 vu3_af3f sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (vf_windows_sound E3 vu3_af3f sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- apply (vf_band_present W E3 vu3_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VI3' HF4 HFr4.
assert (STR4 : vf_str W (ms_mem ms4) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI4)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
assert (R11_4 : getr (ms_regs ms4) 11 = Z_to_bv 64 (s + L)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 _ _ 11 HS4).
match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite denot_lit_U, U_add_off_atom by (rewrite ?A32_3, ?A70_3; unfold M64; lia). rewrite A32_3, A70_3. f_equal. lia. }
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_lbu_nul W E3 vu3_st4 ms4 _ 82 (s + L) HS4 eq_refl eq_refl ltac:(vm_compute; reflexivity) R11_4 ltac:(lia)
ltac:(rewrite HL; exact (proj1 (proj2 STR4)))) HAI4).
intros W4l c4l _ HAI4l (-> & ms4l & mat4l & -> & HS4l & Hmm4l). cbn [cfg_model] in HAI4l. rewrite ?wvb_wvb in HAI4l |- *.
change (set_regs_pc vu3_st4 [((12%bv : bv 5), SLit 0)] 0x942a4) with vu3_af4 in HS4l.
assert (VI4l : VI B ly S W sp0 mem md (ms_mem ms4l) (with_vm_backing (m_vm_lazy md) mat4l md)).
{ rewrite Hmm4l. pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms4) mat4l VI4) as VR.
rewrite ?wvb_wvb in VR. apply VR; [intros; reflexivity | intros; reflexivity | exact (proj1 (proj2 (proj2 VI4)))]. }
clear VI4 HS4 STR4 R11_4.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 vu3_af4 vu3_st5 _ _ _ HS4l vu3_run5) HAI4l).
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. clear HS4l.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VI5 : VI B ly S W sp0 mem md (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms5) mat5 VI4l) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF5. intros Hin. destruct (vf_windows_sound E3 vu3_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- intros x Hx1 Hx2. apply HFr5. intros Hin. destruct (vf_windows_sound E3 vu3_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin); tauto.
- apply (vf_band_present W E3 vu3_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VI4l HF5 HFr5.
assert (SRA5' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms5)) SHADOW_OFF 68444 0) by (intros y Hy; lia).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms5)) 68444 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E3 vu3_st5 ms5 _ ly S sp0 vu3_r05 vu3_rest5 82 RA_FX OSP_FX (-345) (SLit 68444) (68444) 0 (@nil Z)
HS5 ltac:(rewrite HBcode; reflexivity) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E3 sp0 ap vu3_rest5 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hap2)
(vf_rest_w E3 vu3_rest5 ltac:(vm_compute; reflexivity))
(proj1 VI5) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI5))) SRA5' SHU5') HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Hfr5' & Hpm5'). cbn [cfg_model] in HAI5'.
rewrite wvb_wvb in HAI5', HAR5' |- *.
change (vf_after_icpt 82 vu3_st5 RA_FX OSP_FX (-345) (@nil Z)) with vu3_af5 in HS5'.
assert (VI5' : VI B ly S W sp0 mem md (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-345) <= a < sp0 + (-345) + 0))).
- exact VI5.
- exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr5'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm5'. }
remember (havoc E3 82 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 82)%nat -> ew E5 j = ew E3 j) by (intros j Hj; rewrite HE5; apply ew_havoc_old; exact Hj).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by (cbv; lia); exact Usp3).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (rewrite OLD5 by (cbv; lia); exact G3_3).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (rewrite OLD5 by (cbv; lia); exact G4_3).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (rewrite OLD5 by (cbv; lia); exact G12_3).
assert (A32_5 : bv_unsigned (ew E5 32) = s) by (rewrite OLD5 by (cbv; lia); exact A32_3).
assert (A70_5 : bv_unsigned (ew E5 70) = L) by (rewrite OLD5 by (cbv; lia); exact A70_3).
assert (HAE5 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE5 HS5 VI5 SRA5' SHU5'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 vu3_af5 vu3_st6 _ _ _ HS5' vu3_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6. clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VI6 : VI B ly S W sp0 mem md (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms6) mat6 VI5') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6. intros Hin. destruct (vf_windows_sound E5 vu3_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- intros x Hx1 Hx2. apply HFr6. intros Hin. destruct (vf_windows_sound E5 vu3_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- apply (vf_band_present_ecall W E5 vu3_st6 ms6 sp0 HS6 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
clear VI5' HF6 HFr6.
eapply (srz_conseq tfibsegs); [ | rewrite (app_assoc (map (Z_to_bv 8) lit_usage1) str (map (Z_to_bv 8) lit_usage2)), (map_app (WriteEv ch)); apply t_emit_app ].
assert (STR6 : vf_str W (ms_mem ms6) s str).
{ apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply (proj1 (proj2 (proj2 (proj2 VI6)))); [lia | unfold vf_band; lia | unfold vf_file; lia]. }
pose proof HS6 as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & Hregs6 & Hmem6 & HG6). cbn [restrict ms_mem] in Hmem6.
pose proof (lit_buf_sound tfibsegs E5 (mrestrict (w_H W) (ms_mem ms6)) (ss_mem vu3_st6) (SLit (F_STDERR + 120)) 4 [2; 0; 0; 0] Hmem6
ltac:(vm_compute; reflexivity)) as Hfdrd. cbn [sv_denot] in Hfdrd.
pose proof (lit_buf_sound tfibsegs E5 (mrestrict (w_H W) (ms_mem ms6)) (ss_mem vu3_st6) (SOff 2 (-352)) 7 lit_usage1 Hmem6
ltac:(vm_compute; reflexivity)) as Hbuf6.
eapply (srz_sym_stdio_writev2 W E5 vu3_st6 ms6 _ (Z_to_bv 64 2) ch 0 2 (-1024) F_STDERR _ (SOff 2 (-352)) (SLit 7) (SOff 32 0) (SOff 70 0)
(map (Z_to_bv 8) lit_usage1) (str) (map (Z_to_bv 8) [2; 0; 0; 0]) 98 _ HAI6 HS6 eq_refl eq_refl eq_refl).
- reflexivity.
- eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
- reflexivity.
- vm_compute. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val, !U_off by (rewrite Usp5; unfold M64; lia). rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
- match goal with |- sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite iovcnt_val', !U_off by (rewrite Usp5; unfold M64; lia). rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end.
rewrite U_SLit, !U_off by (rewrite A70_5; unfold M64; lia). rewrite A70_5. change (zcanon 7) with 7. lia.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite U_SLit. reflexivity.
- reflexivity.
- reflexivity.
- cbn. lia. - cbn. lia. - cbn. lia. - cbn. lia.
- vm_compute. reflexivity.
-   change (word_to_nat (sv_denot E5 (SLit 7))) with 7%nat. exact Hbuf6.
-   rewrite word_to_nat_U, (U_atom E5 70 L) by (first [rewrite <- A70_5, Z_to_bv_bv_unsigned; reflexivity | lia]).
cbn [sv_denot]. rewrite Z.add_0_r, A32_5, <- HLlen. exact (vf_str_rdn W _ s str STR6).
- rewrite U_SLit, (U_atom E5 70 L) by (first [rewrite <- A70_5, Z_to_bv_bv_unsigned; reflexivity | lia]). change (zcanon 7) with 7. lia.
- rewrite U_SLit, U_off by (rewrite Usp5; unfold M64; lia). rewrite Usp5. change (zcanon 7) with 7. lia.
- rewrite U_SLit, U_off by (rewrite Usp5; unfold M64; lia). rewrite Usp5. change (zcanon 7) with 7. lia.
- rewrite (U_atom E5 70 L) by (first [rewrite <- A70_5, Z_to_bv_bv_unsigned; reflexivity | lia]).
rewrite (U_atom E5 32 s) by (first [rewrite <- A32_5, Z_to_bv_bv_unsigned; reflexivity | lia]). lia.
- rewrite (U_atom E5 70 L) by (first [rewrite <- A70_5, Z_to_bv_bv_unsigned; reflexivity | lia]).
rewrite (U_atom E5 32 s) by (first [rewrite <- A32_5, Z_to_bv_bv_unsigned; reflexivity | lia]). rewrite Usp5. lia.
- exact Hfdrd.
- vm_compute. reflexivity.
- unfold F_STDERR. lia.
- unfold F_STDERR. lia.
- rewrite Usp5. unfold F_STDERR. lia.
- rewrite Usp5. lia.
- rewrite Usp5. lia.
- vm_compute. reflexivity.
-
intros ms6' ws6' mat6' HS6' HF6' HFr6' HAI6'. rewrite ?wvb_wvb in HAI6' |- *.
change (wl_after vu3_st6 0 (-1024) 98) with vu3_af6 in HS6'.
remember (havoc E5 98 ws6') as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 98)%nat -> ew E6 j = ew E5 j) by (intros j Hj; rewrite HE6; apply ew_havoc_old; exact Hj).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by (cbv; lia); exact Usp5).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (rewrite OLD6 by (cbv; lia); exact G3_5).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (rewrite OLD6 by (cbv; lia); exact G4_5).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (rewrite OLD6 by (cbv; lia); exact G12_5).
assert (A32_6 : bv_unsigned (ew E6 32) = s) by (rewrite OLD6 by (cbv; lia); exact A32_5).
assert (A70_6 : bv_unsigned (ew E6 70) = L) by (rewrite OLD6 by (cbv; lia); exact A70_5).
assert (HAE6 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E6)
by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
assert (VI6' : VI B ly S W sp0 mem md (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms6') mat6' VI6) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6'. intros Hin. destruct (vf_windows_sound E5 vu3_st6 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- intros x Hx1 Hx2. apply HFr6'. intros Hin. destruct (vf_windows_sound E5 vu3_st6 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin); tauto.
- apply (vf_band_present W E6 vu3_af6 ms6' sp0 HS6' ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
clear HE6 HS6 VI6 Hfdrd Hregs6 Hmem6 HG6 HF6' HFr6'.
clear STR6 Hbuf6.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 vu3_af6 vu3_st7 _ _ _ HS6' vu3_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7. clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VI7 : VI B ly S W sp0 mem md (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms7) mat7 VI6') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7. intros Hin. destruct (vf_windows_sound E6 vu3_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin); tauto.
- intros x Hx1 Hx2. apply HFr7. intros Hin. destruct (vf_windows_sound E6 vu3_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin); tauto.
- apply (vf_band_present W E6 vu3_st7 ms7 sp0 HS7 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
clear VI6' HF7 HFr7.
destruct (vf_shadow_xfer B ly S W sp0 mem md (ms_mem ms7) _ FMT_usage 17 88162 7 VI7 Hstk Hra_f Hhull_f
ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(unfold FMT_usage; lia) ltac:(rewrite KHI; unfold FMT_usage; lia)) as [SRA7' SHU7'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy B LAWS AMEMCPY W E6 vu3_st7 ms7 _ ly S sp0 vu3_r07 vu3_rest7 109 RA_FX OSP_FX (-352) (SLit 88162) (88162) 7 lit_usage2
HS7 ltac:(rewrite HBcode; reflexivity) eq_refl Usp6 G3_6 G4_6 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(reflexivity) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(cbn; lia) ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(lia) ltac:(cbn; lia) ltac:(unfold OSP_FX; cbn; lia) ltac:(cbn; lia) ltac:(left; unfold kLowMemEnd; cbn; lia)
(vf_rest_ok E6 sp0 ap vu3_rest7 ltac:(vm_compute; reflexivity) G12_6 Hap1 Hap2)
(vf_rest_w E6 vu3_rest7 ltac:(vm_compute; reflexivity))
(proj1 VI7) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VI7))) SRA7' SHU7') HAI7).
intros W7' c7' _ HAI7' (-> & ms7' & mat7' & -> & HS7' & HAR7' & HP7' & Hfr7' & Hpm7'). cbn [cfg_model] in HAI7'.
rewrite wvb_wvb in HAI7', HAR7' |- *.
change (vf_after_icpt 109 vu3_st7 RA_FX OSP_FX (-352) lit_usage2) with vu3_af7 in HS7'.
assert (VI7' : VI B ly S W sp0 mem md (ms_mem ms7') (with_vm_backing (m_vm_lazy md) mat7' md)).
{ eapply (VI_splice B ly S W sp0 mem md (ms_mem ms7) _ (ms_mem ms7') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ (sp0 + (-352) <= a < sp0 + (-352) + 7))).
- exact VI7.
- exact HAR7'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat7' mat7 md). apply with_vm_backing_same.
- intros a Ha. unfold vf_band, OSP_FX in *. lia.
- intros a Hr Hna. apply Hfr7'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm7'. }
remember (havoc E6 109 (map (getr (ms_regs ms7')) CLOB)) as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 109)%nat -> ew E7 j = ew E6 j) by (intros j Hj; rewrite HE7; apply ew_havoc_old; exact Hj).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (rewrite OLD7 by (cbv; lia); exact Usp6).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (rewrite OLD7 by (cbv; lia); exact G3_6).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (rewrite OLD7 by (cbv; lia); exact G4_6).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (rewrite OLD7 by (cbv; lia); exact G12_6).
assert (A32_7 : bv_unsigned (ew E7 32) = s) by (rewrite OLD7 by (cbv; lia); exact A32_6).
assert (A70_7 : bv_unsigned (ew E7 70) = L) by (rewrite OLD7 by (cbv; lia); exact A70_6).
assert (HAE7 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E7)
by (rewrite HE7; apply env_agree_havoc_ge; [cbv; lia | exact HAE6]).
clear HE7 HS7 VI7 SRA7' SHU7'.
eapply (srz_stdio_writev_by_run tfibmusl_tbl W E7 vu3_af7 ms7' _ ch 125 vu3_st8 vu3_af8 lit_usage2 2 T tfibmusl_tbl_ok HS7' HAI7' vu3_wx_eq).
{ eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same]. }
intros ms8 ws8 mat8 HS8 HF8 HFr8 _ _ HAI8. rewrite ?wvb_wvb in HAI8 |- *.
assert (VI8 : VI B ly S W sp0 mem md (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms8) mat8 VI7') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF8. intros Hin. destruct (vf_windows_sound E7 vu3_af7 sp0 _ ltac:(vm_compute; reflexivity) Usp7 Hin); tauto.
- intros x Hx1 Hx2. apply HFr8. intros Hin. destruct (vf_windows_sound E7 vu3_af7 sp0 _ ltac:(vm_compute; reflexivity) Usp7 Hin); tauto.
- apply (vf_band_present W (havoc E7 125 ws8) vu3_af8 ms8 sp0 HS8 ltac:(vm_compute; reflexivity)); [|lia].
rewrite ew_havoc_old by (cbv; lia). exact Usp7. }
remember (havoc E7 125 ws8) as E8 eqn:HE8.
assert (OLD8 : forall j, (j < 125)%nat -> ew E8 j = ew E7 j) by (intros j Hj; rewrite HE8; apply ew_havoc_old; exact Hj).
assert (Usp8 : bv_unsigned (ew E8 2) = sp0) by (rewrite OLD8 by (cbv; lia); exact Usp7).
assert (A70_8 : bv_unsigned (ew E8 70) = L) by (rewrite OLD8 by (cbv; lia); exact A70_7).
assert (HAE8 : env_agree 32 (Ereg regs [Z_to_bv 64 s; Z_to_bv 64 cval]) E8)
by (rewrite HE8; apply env_agree_havoc_ge; [cbv; lia | exact HAE7]).
clear HE8 HS7' VI7' HF8 HFr8.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E8 vu3_af8 vu3_st9 _ _ _ HS8 vu3_run9) HAI8).
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9. clear HS8.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VI9 : VI B ly S W sp0 mem md (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VI_run B LAWS ly S W sp0 mem md HFown Hstk ltac:(lia) _ _ (ms_mem ms9) mat9 VI8) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF9. intros Hin. destruct (vf_windows_sound E8 vu3_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp8 Hin); tauto.
- intros x Hx1 Hx2. apply HFr9. intros Hin. destruct (vf_windows_sound E8 vu3_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp8 Hin); tauto.
- apply (vf_band_present W E8 vu3_st9 ms9 sp0 HS9 ltac:(vm_compute; reflexivity) Usp8 ltac:(lia)). }
clear VI8 HF9 HFr9.
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms9) (v_jalr (getr (ms_regs ms9) 1) 0) (ms_mem ms9) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | exact HAI9 | ].
{ eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E8); [exact HS9 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VI9 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS9 (1%bv : bv 5) Q1.
rewrite OLD8, OLD7, OLD6, OLD5, OLD3, OLD2, OLD1 in Q1 by (cbv; lia). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfibsegs (w_H W) E8 _ _ 10 HS9) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Q10 end.
rewrite denot_lit_U, !U_SAlu, !U_SLit in Q10. cbn [zalu_raw] in Q10. change (zcanon 0) with 0 in Q10.
rewrite !Z.lor_0_l, U_off in Q10 by (rewrite A70_8; unfold M64; lia). rewrite A70_8, !(zcanon_id (L + 14)) in Q10 by (unfold M64; lia).
replace (v_jalr (getr (ms_regs ms9) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
apply (HK (ms_regs ms9) (ms_mem ms9) (with_vm_backing (m_vm_lazy md) matR md)).
* apply (al_frame _ _ LAWS ly S W (ms_mem ms9) _ (ms_mem ms9) _ HAR9); [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | exact (AE2y.hs_kept_refl _ _)].
* exact (aregs_preserved_of_st_ok _ E8 _ _ regs [Z_to_bv 64 s; Z_to_bv 64 cval] HS9 HAE8 ltac:(vm_compute; reflexivity)).
* apply with_vm_backing_same.
* rewrite Q10. reflexivity.
* destruct HS9 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
unfold stderr_after_vfprintf, file_is, stderr_fields_after_vf.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit E8 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem vu3_st9) _ _ _ Hmem9); vm_compute; reflexivity).
* exact Hfr9.
* exact Hpm9.
* exact HAIR.
Qed.
Theorem tfib_vfprintf_usage : forall ly S (W : world tfibsegs) regs mem md ch ap s (str : list byte) L cval T,
ecall_pre tfibsegs B ly S W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_usage -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 s ->
L = Z.of_nat (length str) -> L <= 33554425 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - VF_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF FMT_usage 17 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) FMT_usage 17 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 14) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_usage1 ++ str ++ map (Z_to_bv 8) lit_usage2)) T).
Proof.
intros ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HL HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK.
destruct (Z_lt_le_dec 66 L) as [H1|H1];
[| exact (tfib_vfprintf_usage_A1 ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg HL ltac:(lia) H1 Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK)].
destruct (Z_lt_le_dec 73 L) as [H2|H2];
[| exact (tfib_vfprintf_usage_A2 ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg HL ltac:(lia) H2 Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK)].
exact (tfib_vfprintf_usage_A3 ly S W regs mem md ch ap s str L cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg HL ltac:(lia) HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s HFP HFown Hgot Hcan Hcv Hro Hra_f Hhull_f Hch HAI0 HK).
Qed.
End S.
End b.
