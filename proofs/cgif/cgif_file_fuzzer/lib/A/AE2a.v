(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q YA0m YA0k YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y AE3i AE2l AE2h AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2g AE2j AE2d.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YK0r YK0p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FO_ECALL : Z := 0x93594.
Definition FO_FDOPEN_RA : Z := 0x935d4.
Definition FO_MALLOC_RA : Z := 0x92a10.
Definition FO_MEMSET_RA : Z := 0x92a24.
Definition FO_IOCTL : Z := 0x92b14.
Definition FO_RET : Z := 0x93618.
Definition PC_MALLOC : Z := 0x52930.
Definition FO_S2VAL : Z := 0x24100000000000.
Definition PC_MEMSET : Z := 0x515d4.
Definition PC_ERRNO_LOC : Z := 0x8d2f8.
Definition FO_WIN : Z := 2304.
Definition FO_FRAME : Z := 2144.
Definition tbl_fo : ctable := Eval vm_compute in build_ranges [(PC_ERRNO_LOC, 3%nat)] tbl_ff.
Lemma tbl_fo_eq : tbl_fo = build_ranges [(PC_ERRNO_LOC, 3%nat)] tbl_ff.
Proof. vm_cast_no_check (eq_refl tbl_fo). Qed.
Lemma tbl_fo_ok : table_ok tfibsegs tbl_fo.
Proof. rewrite tbl_fo_eq. apply build_ranges_ok; [| apply tbl_ff_ok]. repeat constructor; cbn; discriminate. Qed.
Definition RUNO (s : sstate) := sym_runN tfibsegs tbl_fo FUEL s.
Definition RUNTOO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_fo FUEL stop s.
Definition stkO : YP09.region := YP09.mkRegion (Some 2%nat) (- FO_WIN) 0 (- FO_WIN) 0 [].
Definition errR : YP09.region := YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [].
Definition envO : list YP09.region :=
[YP09.mkRegion None A_threaded (A_threaded + 1) 0 0 [YP09.mkChunk A_threaded (CVal 1 (SLit 0))];
YP09.mkRegion None A_need_locks (A_need_locks + 1) 0 0 [YP09.mkChunk A_need_locks (CVal 1 (SLit 0))];
YP09.mkRegion None A_ofl_lock (A_ofl_lock + 4) 0 0 [YP09.mkChunk A_ofl_lock (CVal 4 (SLit 0))];
YP09.mkRegion None A_ofl_head (A_ofl_head + 8) A_ofl_head (A_ofl_head + 8) [YP09.mkChunk A_ofl_head (CVal 8 (SLit 0))]].
Definition memO : smem := stkO :: skipn 1 memS ++ canR ++ [errR] ++ envO.
Definition factsO : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (4%nat, mkAF 4096 (2^47) 3)].
Definition ssO1 : sstate := mkSS FF_real_fopen (sr_set (sr_set sr_atoms 10%bv (SLit A_PATH)) 11%bv (SLit A_WB)) memO None (mkFacts factsO [] []).
Definition eO1 : sstate := Eval vm_compute in fst (RUNO ssO1).
Lemma r_O1 : RUNO ssO1 = (eO1, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition resumeO2 (e : sstate) : sstate :=
resume e (SOff 40 0) (ss_mem e) (mkFacts ((40%nat, mkAF 0 (2^31 - 1) 0) :: f_atoms (ss_facts e)) (f_conds (ss_facts e)) (f_alias (ss_facts e))).
Definition eO2 : sstate := Eval vm_compute in fst (RUNO (resumeO2 eO1)).
Lemma r_O2 : RUNO (resumeO2 eO1) = (eO2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition resumeO2r (e : sstate) : sstate :=
resume e (SOff 40 0) (ss_mem e) (mkFacts ((40%nat, mkAF (2^64 - 4095) (2^64 - 1) 0) :: f_atoms (ss_facts e)) (f_conds (ss_facts e)) (f_alias (ss_facts e))).
Definition eO2r : sstate := Eval vm_compute in fst (RUNO (resumeO2r eO1)).
Lemma r_O2r : RUNO (resumeO2r eO1) = (eO2r, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition ssB : sstate := mkSS FO_MALLOC_RA sr_atoms [] None (mkFacts [(10%nat, mkAF 4096 (2^47 - 4096) 4)] [] []).
Definition eB : sstate := Eval vm_compute in fst (RUNTOO PC_MEMSET ssB).
Lemma r_B : RUNTOO PC_MEMSET ssB = (eB, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition FO_WINC : Z := 2208.
Definition stkC_chunks : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SLit FO_S2VAL));
YP09.mkChunk 40 (CVal 8 (SOff 9 0)); YP09.mkChunk 48 (CVal 8 (SLit A_WB)); YP09.mkChunk 56 (CVal 8 (SLit FO_FDOPEN_RA));
YP09.mkChunk 64 (CVal 8 (SOff 35 0)); YP09.mkChunk 72 (CVal 8 (SOff 34 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 88 (CVal 8 (SOff 37 0))].
Definition stkC : YP09.region := YP09.mkRegion (Some 2%nat) (- FO_WINC) 96 (- FO_WINC) 96 stkC_chunks.
Definition zhdr : list YP09.chunk :=
flat_map (fun i => let o := 8 * Z.of_nat i in
if existsb (Z.eqb o) [0; 120; 136; 144] then [YP09.mkChunk o (CVal 4 (SLit 0)); YP09.mkChunk (o + 4) (CVal 4 (SLit 0))]
else [YP09.mkChunk o (CVal 8 (SLit 0))]) (seq 0 29).
Definition blkC (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 8%nat) 0 1264 0 1264 cs.
Definition memC : smem := stkC :: skipn 1 memS ++ canR ++ envO ++ [blkC zhdr].
Definition factsC : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (8%nat, mkAF 4096 (2^47 - 4096) 4); (9%nat, mkAF 0 (2^31 - 1) 0)].
Definition ssC : sstate := mkSS FO_MEMSET_RA (sr_set (sr_set sr_atoms 18%bv (SLit A_WB)) 19%bv (SLit A_canary)) memC None (mkFacts factsC [] []).
Definition eC1 : sstate := Eval vm_compute in fst (RUNO ssC).
Lemma r_C1 : RUNO ssC = (eC1, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition resumeC2 (e : sstate) : sstate := resume e (SLit (2^64 - 25)) (ss_mem e) (ss_facts e).
Definition eC2 : sstate := Eval vm_compute in fst (RUNO (resumeC2 eC1)).
Lemma r_C2 : RUNO (resumeC2 eC1) = (eC2, RS_stopped (SR_jalr (SOff 37 0))). Proof. vm_compute. reflexivity. Qed.
Definition skelsO (blk : bool) (e : sstate) : bool :=
(Z.of_nat (length (ss_mem e)) =? (if blk then 24 else 23)) &&
match ss_mem e with
| r0 :: rest => skel_is r0 (Some 2%nat) (- FO_WIN) 0 (- FO_WIN) 0 &&
match nth_error rest 17, nth_error rest 21 with
| Some re, Some ro => skel_is re (Some 4%nat) (-164) (-160) (-164) (-160) && skel_is ro None A_ofl_head (A_ofl_head + 8) A_ofl_head (A_ofl_head + 8)
| _, _ => false end &&
(if blk then match nth_error rest 22 with Some rb => skel_is rb (Some 41%nat) 0 1264 0 1264 | None => false end else true)
| _ => false end.
Definition WINS : list (option nat * Z * Z) := Eval vm_compute in windows (ss_mem eO1).
Definition skelsC (e : sstate) : bool :=
(Z.of_nat (length (ss_mem e)) =? 23) &&
match ss_mem e with
| r0 :: rest => skel_is r0 (Some 2%nat) (- FO_WINC) 96 (- FO_WINC) 96 &&
match nth_error rest 20, nth_error rest 21 with
| Some ro, Some rb => skel_is ro None A_ofl_head (A_ofl_head + 8) A_ofl_head (A_ofl_head + 8) && skel_is rb (Some 8%nat) 0 1264 0 1264
| _, _ => false end
| _ => false end.
Definition WINSC : list (option nat * Z * Z) := Eval vm_compute in windows (ss_mem ssC).
Lemma wins_O1 : windows (ss_mem eO1) = WINS /\ windows (ss_mem (resumeO2 eO1)) = WINS /\ windows (ss_mem (resumeO2r eO1)) = WINS /\ windows (ss_mem ssO1) = WINS.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma wins_C : windows (ss_mem ssC) = WINSC /\ windows (ss_mem (resumeC2 eC1)) = WINSC.
Proof. vm_compute. split; reflexivity. Qed.
Definition shapeO1 (e : sstate) : bool :=
(ss_pc e =? FO_ECALL) && match ss_resv e with None => true | _ => false end
&& reg_is e 17 (SLit 56) && reg_is e 10 (SLit (2^64 - 100)) && reg_is e 11 (SLit A_PATH) && reg_is e 12 (SLit 33345) && reg_is e 13 (SLit 438)
&& skelsO false e && ss_atoms_lt 40 e.
Lemma shapeO1_ok : shapeO1 eO1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KEPTO : list Z := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27].
Definition cellsO2 : list (Z * sv) :=
[(-8, SOff 1 0); (-16, SOff 8 0); (-24, SOff 9 0); (-32, SOff 18 0);
(-40, SLit FO_FDOPEN_RA); (-48, SLit A_WB); (-56, SOff 40 0); (-64, SLit FO_S2VAL); (-72, SOff 19 0); (-80, SOff 32 0)].
Definition shapeO2 (e : sstate) : bool :=
(ss_pc e =? PC_MALLOC) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SLit 1264) && reg_is e 1 (SLit FO_MALLOC_RA) && reg_is e 2 (SOff 2 (-96)) && reg_is e 8 (SLit A_WB) && reg_is e 9 (SOff 40 0)
&& reg_is e 18 (SLit A_WB) && reg_is e 19 (SLit A_canary)
&& forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPTO
&& forallb (fun c => has_chunk e 0 (fst c) 8 (snd c)) cellsO2
&& has_chunk e 22 A_ofl_head 8 (SLit 0) && skelsO false e.
Lemma shapeO2_ok : shapeO2 eO2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KEPTR1 : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeO2r (e : sstate) : bool :=
(ss_pc e =? FO_RET) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SLit 0) && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPTR1
&& has_chunk e 18 (-164) 4 (SAluw ALU_SUB (SLit 0) (SOff 40 0)) && has_chunk e 22 A_ofl_head 8 (SLit 0) && skelsO false e.
Lemma shapeO2r_ok : shapeO2r eO2r = true. Proof. vm_compute. reflexivity. Qed.
Definition KEPTB : list Z := [2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].
Definition shapeB (e : sstate) : bool :=
(ss_pc e =? PC_MEMSET) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SOff 10 0) && reg_is e 11 (SLit 0) && reg_is e 12 (SLit 232) && reg_is e 1 (SLit FO_MEMSET_RA) && reg_is e 8 (SOff 10 0)
&& forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPTB
&& (Z.of_nat (length (ss_mem e)) =? 0).
Lemma shapeB_ok : shapeB eB = true. Proof. vm_compute. reflexivity. Qed.
Definition shapeC1 (e : sstate) : bool :=
(ss_pc e =? FO_IOCTL) && match ss_resv e with None => true | _ => false end
&& reg_is e 17 (SLit 29) && reg_is e 10 (SOff 9 0) && reg_is e 11 (SLit 0x5413) && skelsC e && ss_atoms_lt 40 e.
Lemma shapeC1_ok : shapeC1 eC1 = true. Proof. vm_compute. reflexivity. Qed.
Definition hdrC : list (Z * N * sv) :=
[(0, 4%N, SLit 4); (4, 4%N, SLit 0); (8, 8%N, SLit 0); (16, 8%N, SLit 0); (24, 8%N, SLit A_stdio_close); (32, 8%N, SLit 0); (40, 8%N, SLit 0); (48, 8%N, SLit 0);
(56, 8%N, SLit 0); (64, 8%N, SLit A_stdio_read); (72, 8%N, SLit A_stdio_write); (80, 8%N, SLit A_stdio_seek); (88, 8%N, SOff 8 240); (96, 8%N, SLit 1024);
(104, 8%N, SLit 0); (112, 8%N, SLit 0); (120, 4%N, SOff 9 0); (124, 4%N, SLit 0); (128, 8%N, SLit 0); (136, 4%N, SLit 0);
(140, 4%N, SLit 18446744073709551615); (144, 4%N, SLit 18446744073709551615); (148, 4%N, SLit 0);
(152, 8%N, SLit 0); (160, 8%N, SLit 0); (168, 8%N, SLit 0); (176, 8%N, SLit 0); (184, 8%N, SLit 0); (192, 8%N, SLit 0); (200, 8%N, SLit 0);
(208, 8%N, SLit 0); (216, 8%N, SLit 0); (224, 8%N, SLit 0)].
Definition KEPTC : list Z := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeC2 (e : sstate) : bool :=
(ss_pc e =? FO_RET) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SOff 8 0) && reg_is e 1 (SOff 37 0) && reg_is e 2 (SOff 2 96)
&& reg_is e 8 (SOff 33 0) && reg_is e 9 (SOff 34 0) && reg_is e 18 (SOff 35 0) && reg_is e 19 (SOff 36 0)
&& forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPTC
&& forallb (fun c => has_chunk e 22 (fst (fst c)) (snd (fst c)) (snd c)) hdrC
&& has_chunk e 21 A_ofl_head 8 (SOff 8 0) && skelsC e.
Lemma shapeC2_ok : shapeC2 eC2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac INL := cbn; repeat (first [left; reflexivity | right]).
Lemma fo_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_fo FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_fo tbl_fo_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma fo_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_fo FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_fo tbl_fo_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma fo_apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|]. exfalso.
apply (Hg (Z_to_bv 64 a)); unfold mrestrict; rewrite Hh; [rewrite Hb; discriminate | exact E'].
Qed.
Lemma fo_phase_g : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_fo FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
destruct (msteps_run_gen tfibsegs tbl_fo tbl_fo_ok FUEL E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
apply (SRr_msteps tfibsegs AF0x.Hwx_tfa W ms msr' md _ Hms). intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb md model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
assert (Hmm : mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) = ms_mem msr') by (pose proof (f_equal ms_mem Hrr) as EE; exact EE).
pose proof (msteps_mem_grows tfibsegs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply SRr_ret. split; [reflexivity|]. exists (unrestrict (w_H W) (ms_mem ms) msr'), (m_vm_materialized model'). split; [reflexivity|].
split; [rewrite Hrr; exact HS'|]. split; [cbn [unrestrict ms_mem]; apply frame_of_unrestrict; exact Hfr|].
split; [rewrite Hmm; exact Hfr | rewrite Hmm; exact Hgr].
Qed.
Lemma ro_img_mb : forall (m m' : word -> option byte),
(forall a, IMG_RO_LO <= a < IMG_RO_HI -> mbyte tfibsegs m' a = mbyte tfibsegs m a) -> ro_img m -> ro_img m'.
Proof.
intros m m' Heq Hro E. pose proof (Hro E) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; [intros o Ho; exfalso; clear - Ho; cbn in Ho; lia|].
apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) X4 c Hc i Hi) as (b & Hcb & Hmb). exists b. split; [exact Hcb|].
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & _).
revert Hmb. cbn [YP09.r_base base_val]. rewrite !Z.add_0_l. rewrite (Heq (YP09.c_off c + i)) by lia. intros Hmb; exact Hmb.
Qed.
Lemma ofl_img_facts_fo : forall i, 0 <= i < 8 ->
img_writable_ok tfibsegs (A_ofl_head + i) = true /\ seg_rom tfibsegs (Z_to_bv 64 (A_ofl_head + i)) <> None.
Proof.
intros i Hi.
assert (C : forall j, In j [0; 1; 2; 3; 4; 5; 6; 7] -> img_writable_ok tfibsegs (A_ofl_head + j) = true /\ seg_rom tfibsegs (Z_to_bv 64 (A_ofl_head + j)) <> None).
{ intros j Hj. cbn [In] in Hj. repeat (destruct Hj as [<- | Hj]; [vm_compute; split; [reflexivity | discriminate]|]). destruct Hj. }
apply C. cbn [In]. lia.
Qed.
Lemma val_of_chunk_mod : forall E mem base off (n : N) (e : sv) v,
YP09.chunk_ok tfibsegs E mem base (YP09.mkChunk off (CVal n e)) ->
bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n) = v -> (Z.of_N n <= 8) ->
val_mem tfibsegs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H0 He Hn k Hk. unfold YP09.chunk_ok in H0. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in H0.
pose proof (N_nat_Z n) as Hnn.
destruct (H0 (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1.
unfold byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. rewrite Z.mod_mod by lia. subst v. rewrite Hnn.
set (w := bv_unsigned (sv_denot E e)). set (K := Z.of_nat k). set (N8 := Z.of_N n).
assert (HK : 0 <= K < N8) by (subst K N8; lia).
rewrite (Z.mod_small (w mod 2 ^ (8 * N8)) (2 ^ (8 * N8))) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
rewrite !Z.shiftr_div_pow2 by lia.
replace (2 ^ (8 * N8)) with (2 ^ (8 * K) * 2 ^ (8 * (N8 - K))) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try (apply Z.pow_pos_nonneg); lia).
rewrite (Z.mul_comm (2 ^ (8 * K))), Z.div_add by (apply Z.pow_nonzero; lia).
rewrite (Z.div_small (w mod 2 ^ (8 * K))) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
rewrite Z.add_0_l.
replace (2 ^ (8 * (N8 - K))) with (256 * 2 ^ (8 * (N8 - K) - 8)) by (change 256 with (2 ^ 8); rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try (apply Z.pow_pos_nonneg); lia).
rewrite (Z.mul_comm 256), Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma val_mem_zero : forall (m : word -> option byte) a (n : nat),
(forall i, 0 <= i < Z.of_nat n -> mbyte tfibsegs m (a + i) = Some (Z_to_bv 8 0)) -> val_mem tfibsegs m a n 0.
Proof. intros m a n Hz k Hk. rewrite (Hz (Z.of_nat k)) by lia. f_equal. apply bv_eq. unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l; [reflexivity | apply Z.pow_nonzero; lia]. Qed.
Lemma same_io_sbm : forall m m', same_but_materialized m m' -> same_io m m'.
Proof. intros m m' Hs. rewrite (same_but_materialized_wvb m m' Hs). destruct m as [f' [mp lz mt] io fs pr li ti]. repeat split; reflexivity. Qed.
Lemma same_io_trans3 : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. auto. Qed.
Definition md_frame (mdA md1 : Model) : Prop := m_vmmaps md1 = m_vmmaps mdA /\ m_vm_lazy md1 = m_vm_lazy mdA.
Lemma md_frame_sbm : forall a b, same_but_materialized a b -> md_frame a b.
Proof. intros a b Hs. pose proof (same_but_materialized_frame a b Hs) as (_ & V & L & _). exact (conj V L). Qed.
Lemma md_frame_trans : forall a b c, md_frame a b -> md_frame b c -> md_frame a c.
Proof. intros a b c [V1 L1] [V2 L2]. split; congruence. Qed.
Lemma md_frame_with_fds : forall x m, md_frame m (with_fds x m). Proof. intros. split; reflexivity. Qed.
Lemma md_frame_with_fs : forall x m, md_frame m (with_fs x m). Proof. intros. split; reflexivity. Qed.
Lemma md_frame_eager : forall a b, md_frame a b -> eager_used b = eager_used a.
Proof. intros a b [V L]. unfold eager_used. rewrite V, L. reflexivity. Qed.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variable cval : Z.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let m0 := mrestrict H mem.
Definition FOP_WIN : Z := 6400.
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hal16 : sp0 mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + FOP_WIN <= sp0.
Hypothesis Hshi : sp0 <= ly_stk_hi ly.
Hypothesis Hpres : forall a, sp0 - FOP_WIN <= a < sp0 -> apresent H mem a.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis G10 : getr regs 10 = w64 A_PATH.
Hypothesis G11 : getr regs 11 = w64 A_WB.
Hypothesis HIO : cells_hold m0 io_cells.
Hypothesis HSTC : cells_hold m0 st_cells.
Hypothesis HIMG : ro_img m0.
Hypothesis Hcan1 : val_mem tfibsegs m0 A_GOT_canary 8 A_canary.
Hypothesis Hcan2 : val_mem tfibsegs m0 A_canary 8 cval.
Hypothesis Hcv : 0 <= cval < 2 ^ 64.
Hypothesis Henv0 : val_mem tfibsegs m0 A_threaded 1 0.
Hypothesis Henv1 : val_mem tfibsegs m0 A_need_locks 1 0.
Hypothesis Henv2 : val_mem tfibsegs m0 A_ofl_lock 4 0.
Hypothesis Hhead : val_mem tfibsegs m0 A_ofl_head 8 0.
Hypothesis HOFLown : forall a, A_ofl_head <= a < A_ofl_head + 8 -> ~ aowned B ly S a.
Hypothesis HERRown : forall a, TFIB_TP - 164 <= a < TFIB_TP - 160 -> ~ aowned B ly S a.
Definition stackW (a : Z) : Prop := sp0 - FOP_WIN <= a < sp0.
Definition errW (a : Z) : Prop := TFIB_TP - 164 <= a < TFIB_TP - 160.
Definition oflW (a : Z) : Prop := A_ofl_head <= a < A_ofl_head + 8.
Variable OPRE : Model -> Prop.
Hypothesis HOPRE : OPRE md.
Hypothesis OPRE_sbm : forall m m', same_but_materialized m m' -> OPRE m -> OPRE m'.
Hypothesis OPENAT : forall regs1 mem1 md1 (Q : world tfibsegs -> config -> Prop),
AI tfibsegs (w_H W) (w_A W) md1 -> OPRE md1 ->
bv_unsigned (getr regs1 17) = 56 -> getr regs1 10 = w64 (2 ^ 64 - 100) -> getr regs1 11 = w64 A_PATH ->
getr regs1 12 = w64 33345 -> getr regs1 13 = w64 438 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
(forall md' e, 1 <= e <= 4095 -> same_but_materialized md1 md' ->
SRr tfibsegs W (mkCfg (mkst (regupd regs1 10 (errno_ret e)) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem1 (seg_rom tfibsegs)) md') Q) ->
(forall md' (fd : word), bv_unsigned fd < 2 ^ 31 -> fd_lookup (m_fds md1) fd = None ->
same_but_materialized (with_fds (fd_insert (m_fds md1) fd (FdFileW sink_path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs md1) sink_path []) md1)) md' ->
SRr tfibsegs W (mkCfg (mkst (regupd regs1 10 fd) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem1 (seg_rom tfibsegs)) md') Q) ->
SRr tfibsegs W (mkCfg (pend_at regs1 (Z_to_bv 64 FO_ECALL) mem1 (seg_rom tfibsegs)) md1) Q.
Definition LAPOST : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\
((exists regs' mem' md' (e : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\ 1 <= e <= 4095 /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
m_vmmaps md' = m_vmmaps md /\ m_vm_lazy md' = m_vm_lazy md /\ same_io md md' /\ os_kept md md' /\ same_but_materialized md md' /\
val_mem tfibsegs (mrestrict H mem') (TFIB_TP - 164) 4 e /\ val_mem tfibsegs (mrestrict H mem') A_ofl_head 8 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> aview tfibsegs H mem' a = aview tfibsegs H mem a) /\
(forall a, stackW a -> apresent H mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ errW a -> ~ oflW a -> apresent H mem a -> apresent H mem' a))
\/
(exists regsT memT mdT (fd : word) (v8 v9 v18 v19 : Z),
c' = cfg_at tfibsegs PC_MALLOC regsT memT mdT /\ AR tfibsegs B ly S W memT mdT /\
getr regsT 10 = w64 1264 /\ getr regsT 1 = w64 FO_MALLOC_RA /\ getr regsT 2 = w64 (sp0 - FO_FRAME - 96) /\
getr regsT 8 = w64 A_WB /\ getr regsT 9 = fd /\ getr regsT 18 = w64 A_WB /\ getr regsT 19 = w64 A_canary /\
(forall r, In r AE2g.KEPTF -> getr regsT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
bv_unsigned fd < 2 ^ 31 /\ fd_lookup (m_fds md) fd = None /\
m_fds mdT = fd_insert (m_fds md) fd (FdFileW sink_path (Z_to_bv 64 0)) /\ m_fs mdT = fs_set (m_fs md) sink_path [] /\
m_vmmaps mdT = m_vmmaps md /\ m_vm_lazy mdT = m_vm_lazy md /\ os_kept md mdT /\
0 <= v8 < 2 ^ 64 /\ 0 <= v9 < 2 ^ 64 /\ 0 <= v18 < 2 ^ 64 /\ 0 <= v19 < 2 ^ 64 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 8) 8 IO_RET /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 16) 8 v8 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 24) 8 v9 /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 32) 8 v18 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 40) 8 FO_FDOPEN_RA /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 48) 8 A_WB /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 56) 8 (bv_unsigned fd) /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 64) 8 FO_S2VAL /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 72) 8 v19 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FO_FRAME - 80) 8 cval /\
(forall j rz off, nth_error SAVEDF j = Some (rz, off) -> val_mem tfibsegs (mrestrict H memT) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))) /\
val_mem tfibsegs (mrestrict H memT) A_ofl_head 8 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> aview tfibsegs H memT a = aview tfibsegs H mem a) /\
(forall a, stackW a -> apresent H memT a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ errW a -> ~ oflW a -> apresent H mem a -> apresent H memT a))).
Lemma factsM : 2 ^ 44 <= sp0 /\ sp0 <= 2 ^ 47 /\ FOP_WIN = 6400 /\ FO_WIN = 2304 /\ FO_FRAME = 2144 /\
(ly_stk_hi ly <= 2 ^ 47 /\ 17594333495296 + 6400 <= sp0) /\ A_ofl_head = 0x5f9688 /\ TFIB_TP = 0x5d8f90 /\ TFIB_IMG_END = 0x5fb000 /\
bv_unsigned (getr regs 4) = TFIB_TP.
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FS : FOP_WIN = 6400) by reflexivity. rewrite FS in *. clear OPENAT. subst sp0.
repeat split; try lia; try reflexivity. rewrite Htp, (ts_tp B TB). apply unsigned_lit_small. unfold TFIB_TP. lia.
Qed.
Lemma frameO : forall (memA mem1 : word -> option byte) mdA md1 (Wr : Z -> Prop) (blk : Z -> Prop),
AR tfibsegs B ly S W memA mdA ->
(forall a, Wr a \/ ~ Wr a) ->
(forall a, Wr a -> stackW a \/ errW a \/ oflW a \/ blk a) ->
(forall a, blk a -> ~ aowned B ly S a /\ AF0x.off_img a) ->
(forall z : word, ~ Wr (bv_unsigned z) -> mem1 z = memA z) ->
(forall a, Wr a -> ~ errW a -> ~ oflW a -> apresent H mem1 a) ->
md_frame mdA md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H mem1 a = aview tfibsegs H memA a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ errW a -> ~ oflW a -> apresent H memA a -> apresent H mem1 a) /\
AR tfibsegs B ly S W mem1 md1.
Proof.
intros memA mem1 mdA md1 Wr blk HARA Wdec HWin Hblk MEQ PRS MF.
pose proof factsM as (Hsp & Hsp2 & FS & FW & FF & Lhi & HO & HT & HIE & Etp). rewrite FS in *. unfold stackW, errW, oflW in *. rewrite HO, HT in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H mem1 a = aview tfibsegs H memA a).
{ intros a Hr Hw. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Hw. }
assert (PM : forall a, 0 <= a < 2 ^ 64 -> ~ (0x5d8f90 - 164 <= a < 0x5d8f90 - 160) -> ~ (0x5f9688 <= a < 0x5f9688 + 8) -> apresent H memA a -> apresent H mem1 a).
{ intros a Hr He Ho Hp. destruct (Wdec a) as [Hw|Hw]; [apply PRS; assumption|].
apply (apresent_same H memA mem1 a); [apply MEQ; rewrite unsigned_lit_small by lia; exact Hw | exact Hp]. }
split; [exact AV|]. split; [exact PM|].
pose proof (md_frame_eager _ _ MF) as Feu. destruct MF as [Fmaps Flazy].
assert (IMGb : forall a, (0x5d8f90 - 164 <= a < 0x5d8f90 - 160) \/ (0x5f9688 <= a < 0x5f9688 + 8) -> seg_rom tfibsegs (Z_to_bv 64 a) <> None).
{ intros a Ha.
assert (C : forall j, In j [0; 1; 2; 3] -> seg_rom tfibsegs (Z_to_bv 64 (0x5d8f90 - 164 + j)) <> None /\ (j < 4 \/ True))
by (intros j Hj; cbn [In] in Hj; repeat (destruct Hj as [<- | Hj]; [vm_compute; split; [discriminate | lia]|]); destruct Hj).
destruct Ha as [Ha|Ha].
- replace a with (0x5d8f90 - 164 + (a - (0x5d8f90 - 164))) by lia. apply (proj1 (C (a - (0x5d8f90 - 164)) ltac:(cbn [In]; lia))).
- rewrite <- HO in Ha. destruct (ofl_img_facts_fo (a - A_ofl_head) ltac:(lia)) as [_ Hrom]. replace (A_ofl_head + (a - A_ofl_head)) with a in Hrom by lia. exact Hrom. }
apply (al_frame _ _ LAWS ly S W memA mdA mem1 _ HARA).
+ intros a Hr Hown. apply AV; [exact Hr|]. intros Hw. destruct (HWin a Hw) as [Hs | [He | [Ho | Hb]]].
* exact (al_stack _ _ LAWS ly S W memA mdA a HARA ltac:(unfold sp0 in *; lia) Hown).
* exact (HERRown a He Hown).
* exact (HOFLown a Ho Hown).
* exact (proj1 (Hblk a Hb) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem1 a). rewrite (AE2y.aview_mod _ memA a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Wdec a') as [Hw|Hw]; [| rewrite AV by assumption; exact Hv].
destruct (HWin a' Hw) as [Hs | [He | [Ho | Hb]]].
* apply AE2y.aview_some_of_apresent. apply PRS; [exact Hw | lia | lia].
* unfold aview, mbyte. destruct (mrestrict (w_H W) mem1 (Z_to_bv 64 a')) as [b|]; [cbn; discriminate|].
pose proof (IMGb a' (or_introl He)) as Hrom. destruct (seg_rom tfibsegs (Z_to_bv 64 a')); [cbn; discriminate | exfalso; exact (Hrom eq_refl)].
* unfold aview, mbyte. destruct (mrestrict (w_H W) mem1 (Z_to_bv 64 a')) as [b|]; [cbn; discriminate|].
pose proof (IMGb a' (or_intror Ho)) as Hrom. destruct (seg_rom tfibsegs (Z_to_bv 64 a')); [cbn; discriminate | exfalso; exact (Hrom eq_refl)].
* pose proof (proj2 (Hblk a' Hb)) as Hoff. apply AE2y.aview_some_of_apresent. apply PRS; [exact Hw | | ]; unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in Hoff; lia.
+ exact Fmaps.
+ exact Flazy.
+ exact Feu.
+ intros a Hband Hh. pose proof (AE2y.in_band_rw_u64 a Hband) as Hr. change (w64 a) with (Z_to_bv 64 a) in *.
apply MEQ. rewrite unsigned_lit_small by lia. intros Hw. destruct (HWin a Hw) as [Hs | [He | [Ho | Hb]]].
* exfalso. pose proof (Hpres a Hs) as [Hn0 _]. unfold H in Hn0. rewrite Hh in Hn0. discriminate.
* unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband. clear - Hband He. lia.
* unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband. clear - Hband Ho. lia.
* exfalso. pose proof (PRS a Hw ltac:(clear - Hb Hblk; pose proof (proj2 (Hblk a Hb)) as X; unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in X; lia)
ltac:(clear - Hb Hblk; pose proof (proj2 (Hblk a Hb)) as X; unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in X; lia)) as [Hn0 _].
unfold H in Hn0. rewrite Hh in Hn0. discriminate.
Qed.
Theorem fopen_LA : SRr tfibsegs W (cfg_at tfibsegs FF_pc_wrap_fopen regs mem md) LAPOST.
Proof.
pose proof factsM as (Hsp & Hsp2 & FS & FW & FF & Lhi & HO & HT & HIE & Etp). rewrite FS in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi' & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi'.
pose proof AF0x.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (IW : IO_WIN = 2160) by reflexivity. assert (IFR : IO_FRAME = 2144) by reflexivity.
eapply SRr_bind.
{ apply (iopen_front B LAWS TB ly S W regs mem md HAR Hal16); rewrite ?IW.
- lia.
- exact Hshi.
- intros a Ha. apply Hpres. lia.
- exact G10.
- exact G11.
- exact HIO. }
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & MF1 & HAR1 & Q10 & Q11 & Q1 & Q2 & QK & QS & AV1 & PRS1 & PM1).
rewrite IW in AV1, PRS1. rewrite IFR in Q2. fold H in AV1, PRS1, PM1, QS. fold sp0 in Q2, QS, AV1, PRS1.
set (E1 := AE2y.Env regs1 [cval]).
assert (E1reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E1 i = getr regs1 r) by (intros; apply AE2y.Env_reg; assumption).
assert (E1_2 : bv_unsigned (ew E1 2) = sp0 - 2144) by (rewrite (E1reg 2%nat 2%bv eq_refl), Q2; apply unsigned_lit_small; lia).
assert (E1_4 : bv_unsigned (ew E1 4) = TFIB_TP) by (rewrite (E1reg 4%nat 4%bv eq_refl); rewrite <- Etp; f_equal; exact (QK 4 ltac:(unfold AE2g.KEPTF; INL))).
assert (E1_32 : ew E1 32 = Z_to_bv 64 cval) by (exact (AE2y.Env_x regs1 [cval] 0%nat cval eq_refl)).
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2160 <= a < sp0) -> mbyte tfibsegs (mrestrict H mem1) a = mbyte tfibsegs (mrestrict H mem) a).
{ intros a Hr Hs. apply AE2y.mbyte_of_aview. apply AV1; lia. }
assert (HSTC1 : cells_hold (mrestrict H mem1) st_cells).
{ apply (cells_hold_frame m0); [| | exact HSTC].
- intros a Hx. unfold st_cells, A_WB in Hx. apply Exists_exists in Hx as (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Hr; apply MB1; lia.
- unfold st_cells. repeat constructor; cbn; lia. }
assert (HIMG1 : ro_img (mrestrict H mem1)).
{ apply (ro_img_mb m0); [| exact HIMG]. intros a Ha. unfold IMG_RO_LO, IMG_RO_HI in Ha. apply MB1; lia. }
assert (WOFL : forall (m : word -> option byte) o, 0 <= o < 8 -> writable_at tfibsegs m (A_ofl_head + o)).
{ intros m o Ho. destruct (ofl_img_facts_fo o Ho) as [Hw _]. unfold img_writable_ok in Hw.
apply (writable_at_grows tfibsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
unfold writable_at. destruct (wview tfibsegs (fun _ => None) (Z_to_bv 64 (A_ofl_head + o))); [discriminate | discriminate Hw]. }
assert (WERR : forall (m : word -> option byte) o, 0 <= o < 4 -> writable_at tfibsegs m (TFIB_TP - 164 + o)).
{ intros m o Ho.
assert (C : forall j, In j [0; 1; 2; 3] -> img_writable_ok tfibsegs (TFIB_TP - 164 + j) = true)
by (intros j Hj; cbn [In] in Hj; repeat (destruct Hj as [<- | Hj]; [vm_compute; reflexivity|]); destruct Hj).
pose proof (C o ltac:(cbn [In]; lia)) as Hw. unfold img_writable_ok in Hw.
apply (writable_at_grows tfibsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
unfold writable_at. destruct (wview tfibsegs (fun _ => None) (Z_to_bv 64 (TFIB_TP - 164 + o))); [discriminate | discriminate Hw]. }
assert (HS1 : st_ok tfibsegs E1 ssO1 (restrict H (mkst regs1 (Z_to_bv 64 FF_real_fopen) mem1 (seg_rom tfibsegs)))).
{ unfold ssO1.
apply (st_ok_pin_reg E1 (mkSS FF_real_fopen (sr_set sr_atoms 10%bv (SLit A_PATH)) memO None (mkFacts factsO [] [])) _ 11%bv (SLit A_WB));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite Q11; reflexivity].
apply (st_ok_pin_reg E1 (mkSS FF_real_fopen sr_atoms memO None (mkFacts factsO [] [])) _ 10%bv (SLit A_PATH));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite Q10; reflexivity].
rewrite restrict_mkst_fx. unfold E1, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 (map (Z_to_bv 64) [cval])) with E1.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memO. apply Forall_cons.
{ unfold stkO. rewrite FW. apply (region_ok_stack tfibsegs E1 _ 2 (sp0 - 2144) (- 2304)); [exact E1_2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. destruct (Z_lt_le_dec a (sp0 - 2160)) as [L|L]; [apply PM1, Hpres; lia | apply PRS1; lia]. }
unfold memS. change (skipn 1 ([stkS; img_piece 0x2011e 8; img_piece 0x10330 (0x10398 - 0x10330)] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells)))
with ([img_piece 0x2011e 8; img_piece 0x10330 (0x10398 - 0x10330)] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells)).
rewrite <- !app_assoc. apply Forall_app. split.
{ apply Forall_cons; [apply (img_piece_ok _ E1 0x1cd1e (0x20b7c - 0x1cd1e)); [exact HIMG1 | unfold img_ro_chunks; cbn; tauto | lia | lia | lia]|].
apply Forall_cons; [apply (img_piece_ok _ E1 0x10330 (0x10398 - 0x10330)); [exact HIMG1 | unfold img_ro_chunks; cbn; tauto | lia | lia | lia]|]. apply Forall_nil. }
apply Forall_app. split.
{ rewrite !map_app. apply Forall_app. split; [exact (AE2y.icpt_rodata_ok B TB ly S H mem1 E1 (proj1 HAR1))|].
apply Forall_app. split; [exact (rodata_ok B TB st_const ly S H mem1 E1 (st_const_chk ly) (proj1 HAR1))|].
exact (cells_region_ok _ E1 st_cells HSTC1). }
apply Forall_app. split.
{ unfold canR. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_canary, A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x9ec38 8 (SLit 0x5f8fd0) 0x5f8fd0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Hcan1]. }
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f8fd0 8 (SOff 32 0) cval); [cbn [sv_denot]; rewrite E1_32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Hcan2]. } }
apply Forall_cons.
{ unfold errR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E1_4, HT.
split; [lia|]. split; [lia|]. split; [intros o Ho; replace (6131600 + o) with (TFIB_TP - 164 + (o + 164)) by (rewrite HT; lia); apply WERR; lia | apply Forall_nil]. }
unfold envO. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; unfold A_threaded, A_need_locks, A_ofl_lock; rewrite ?HO.
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f9221 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Henv0]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f9223 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Henv1]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f9680 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MB1; lia | exact Henv2]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; replace o with (A_ofl_head + (o - 0x5f9688)) by (rewrite HO; lia); apply WOFL; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E1 _ 0 0x5f9688 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l].
rewrite <- HO. apply (val_mem_frame tfibsegs m0); [intros x Hx; rewrite HO in Hx; apply MB1; lia | exact Hhead]. }
- apply pairwise_disjoint_of_extents. unfold memO, memS, stkO, stkS, img_piece, st_cells, st_const, icpt_rodata, canR, errR, envO, ro_region, extent_of_region.
cbn [skipn map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E1_2, E1_4, HT.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_WB, A_GOT_canary, A_canary, A_threaded, A_need_locks, A_ofl_lock, A_ofl_head, FO_WIN in *. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsO]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E1_2, E1_4, HT.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia. replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
unfold cfg_at. change (w64 FF_real_fopen) with (Z_to_bv 64 FF_real_fopen).
eapply SRr_bind; [exact (fo_phase W E1 ssO1 eO1 _ (mkst regs1 (Z_to_bv 64 FF_real_fopen) mem1 (seg_rom tfibsegs)) md1 HS1 r_O1)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [ms_mem mkst] in HF2. clear HFr2.
set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
assert (MF2 : same_but_materialized md1 md2) by (subst md2; apply with_vm_backing_same).
pose proof shapeO1_ok as Hsh. unfold shapeO1 in Hsh.
apply andb_prop in Hsh as [Hsh Hat]. apply andb_prop in Hsh as [Hsh Hsk]. apply andb_prop in Hsh as [Hsh R13]. apply andb_prop in Hsh as [Hsh R12].
apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh R17]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv2 : ss_resv eO1 = None) by (destruct (ss_resv eO1); [discriminate | reflexivity]).
destruct (st_ok_ecall_shape_r tfibsegs H E1 eO1 ms2 HS2 Hresv2) as (regs2 & mem2 & Hms2 & Hregs2 & Hmemok2 & HG2).
assert (Hmm2 : ms_mem ms2 = mem2) by (rewrite Hms2; reflexivity). rewrite Hmm2 in HF2.
assert (WIN : forall E rs a, windows rs = WINS -> bv_unsigned (ew E 2) = sp0 - 2144 -> bv_unsigned (ew E 4) = TFIB_TP -> in_wrange E rs a ->
(sp0 - 2144 - 2304 <= a < sp0 - 2144) \/ errW a \/ oflW a).
{ intros E rs a HWl E2 E4 Hin. destruct (in_wrange_windows E rs a Hin) as (bw & lo & hi & Ht & Hr). rewrite HWl in Ht. unfold WINS in Ht. cbn [In] in Ht.
unfold errW, oflW. rewrite HO, HT. rewrite HT in E4.
repeat (destruct Ht as [Et | Ht]; [injection Et as <- <- <-; cbn [base_val] in Hr; rewrite ?E2, ?E4 in Hr; lia|]). destruct Ht. }
pose proof wins_O1 as (WL1 & WL2 & WL2r & WL0).
assert (MEQ2 : forall z : word, ~ ((sp0 - 2144 - 2304 <= bv_unsigned z < sp0 - 2144) \/ errW (bv_unsigned z) \/ oflW (bv_unsigned z)) -> mem2 z = mem1 z).
{ intros z Hz. apply (HF2 z). intros Hin. exact (Hz (WIN E1 _ _ WL0 E1_2 E1_4 Hin)). }
clear HF2.
assert (RD2 : forall (r : bv 5) v, reg_is eO1 (bv_unsigned r) v = true -> getr regs2 r = sv_denot E1 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply Hregs2. }
assert (Q2_17 : bv_unsigned (getr regs2 17) = 56) by (rewrite (RD2 17%bv (SLit 56) R17); reflexivity).
assert (Q2_10 : getr regs2 10 = w64 (2 ^ 64 - 100)) by (rewrite (RD2 10%bv _ R10); reflexivity).
assert (Q2_11 : getr regs2 11 = w64 A_PATH) by (rewrite (RD2 11%bv _ R11); reflexivity).
assert (Q2_12 : getr regs2 12 = w64 33345) by (rewrite (RD2 12%bv _ R12); reflexivity).
assert (Q2_13 : getr regs2 13 = w64 438) by (rewrite (RD2 13%bv _ R13); reflexivity).
unfold skelsO in Hsk. apply andb_prop in Hsk as [Hlen Hsk]. destruct (ss_mem eO1) as [|r0 rest] eqn:Hmem; [discriminate Hsk|].
apply andb_prop in Hsk as [Hsk _]. apply andb_prop in Hsk as [K0 _]. apply skel_is_sound in K0 as (K0a & K0lo & K0hi & K0b & K0c). rewrite FW in K0b, K0lo.
assert (PRS2s : forall a, sp0 - 2144 - 2304 <= a < sp0 - 2144 -> apresent H mem2 a).
{ intros a Ha. apply (mem_ok_window_apresent H E1 mem2 _ 0 r0 a Hmemok2 ltac:(rewrite ?Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite K0a, K0b, K0c. cbn [base_val]. rewrite E1_2. lia. }
set (Wr2 := fun a => (sp0 - 2144 - 2304 <= a < sp0 - 2144) \/ errW a \/ oflW a).
assert (Wr2d : forall a, Wr2 a \/ ~ Wr2 a) by (intros a; subst Wr2; cbn beta; unfold errW, oflW; lia).
assert (Wr2i : forall a, Wr2 a -> stackW a \/ errW a \/ oflW a \/ False) by (intros a Ha; subst Wr2; cbn beta in Ha; unfold stackW; destruct Ha as [Ha|Ha]; [left; lia | tauto]).
assert (Wr2p : forall a, Wr2 a -> ~ errW a -> ~ oflW a -> apresent H mem2 a).
{ intros a Ha He Hof. subst Wr2. cbn beta in Ha. destruct Ha as [Hs | [Hx | Hx]]; [exact (PRS2s a Hs) | exfalso; exact (He Hx) | exfalso; exact (Hof Hx)]. }
destruct (frameO mem1 mem2 md1 md2 Wr2 (fun _ => False) HAR1 Wr2d Wr2i ltac:(intros a Hf; destruct Hf) MEQ2 Wr2p (md_frame_sbm _ _ MF2)) as (AV2 & PM2 & HAR2).
subst Wr2. cbv beta in AV2. clear Wr2d Wr2i Wr2p.
assert (MB2 : forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> mbyte tfibsegs (mrestrict H mem2) a = mbyte tfibsegs (mrestrict H mem) a).
{ intros a Hr Hs He Hof. unfold stackW in Hs. rewrite <- (MB1 a Hr ltac:(lia)). apply AE2y.mbyte_of_aview. apply AV2; [lia|]. intros [Hx|[Hx|Hx]]; [lia | exact (He Hx) | exact (Hof Hx)]. }
assert (AVF2 : forall a, 0 <= a < 2 ^ 64 -> ~ stackW a -> ~ errW a -> ~ oflW a -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Hs He Hof. rewrite AV2; [apply AV1; [exact Hr | unfold stackW in Hs; lia] | exact Hr | unfold stackW in Hs; intros [Hx|[Hx|Hx]]; [lia | exact (He Hx) | exact (Hof Hx)]]. }
rewrite Hms2. apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
rewrite Hpc. apply (OPENAT regs2 mem2 md2 LAPOST HAI (OPRE_sbm md md2 (same_but_materialized_trans _ _ _ MF1 MF2) HOPRE) Q2_17 Q2_10 Q2_11 Q2_12 Q2_13 AVF2).
-
intros md3 e He MF3.
set (RET := errno_ret e).
assert (HRETu : bv_unsigned RET = 2 ^ 64 - e).
{ subst RET. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (- e) with ((2 ^ 64 - e) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
set (E2 := ewset E1 40 RET).
assert (E2old : forall i, (i < 40)%nat -> ew E2 i = ew E1 i) by (intros i Hi; subst E2; apply ew_ewset_other; lia).
assert (E2_40 : ew E2 40 = RET) by (subst E2; apply ew_ewset_same).
assert (E2_2 : bv_unsigned (ew E2 2) = sp0 - 2144) by (rewrite (E2old 2%nat ltac:(lia)); exact E1_2).
assert (E2_4 : bv_unsigned (ew E2 4) = TFIB_TP) by (rewrite (E2old 4%nat ltac:(lia)); exact E1_4).
assert (HS3 : st_ok tfibsegs E2 (resumeO2r eO1) (restrict H (mkst (regupd regs2 10 RET) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)))).
{ unfold resumeO2r. rewrite restrict_mkst_fx, <- Hpc. subst E2.
apply (st_ok_resume_atom tfibsegs 40 (mkAF (2 ^ 64 - 4095) (2 ^ 64 - 1) 0) E1 eO1 regs2 (mrestrict H mem2) RET Hregs2 ltac:(rewrite Hmem; exact Hmemok2) HG2 Hat); cbn [af_lo af_hi af_al2]; rewrite ?HRETu; [lia | lia |].
change (2 ^ 0) with 1. apply Z.mod_1_r. }
eapply SRr_bind; [exact (fo_phase W E2 (resumeO2r eO1) eO2r _ (mkst (regupd regs2 10 RET) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)) md3 HS3 r_O2r)|].
intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [ms_mem mkst] in HF4. clear HFr4.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
assert (MF4 : same_but_materialized md2 md4) by (eapply same_but_materialized_trans; [exact MF3 | subst md4; apply with_vm_backing_same]).
pose proof shapeO2r_ok as Hsr. unfold shapeO2r in Hsr.
apply andb_prop in Hsr as [Hsr Hsk4]. apply andb_prop in Hsr as [Hsr Hofl4]. apply andb_prop in Hsr as [Hsr Herr4]. apply andb_prop in Hsr as [Hsr HK4].
apply andb_prop in Hsr as [Hsr Z10]. apply andb_prop in Hsr as [Hpc4 Hrv4]. apply Z.eqb_eq in Hpc4.
assert (Hresv4 : ss_resv eO2r = None) by (destruct (ss_resv eO2r); [discriminate | reflexivity]).
unfold skelsO in Hsk4. apply andb_prop in Hsk4 as [Hlen4 Hsk4]. destruct (ss_mem eO2r) as [|q0 qrest] eqn:Hmem4; [discriminate Hsk4|].
apply andb_prop in Hsk4 as [Hsk4 _]. apply andb_prop in Hsk4 as [J0 Hsk4].
destruct (nth_error qrest 17) as [qe|] eqn:Hqe; [|discriminate Hsk4]. destruct (nth_error qrest 21) as [qo|] eqn:Hqo; [|discriminate Hsk4].
apply andb_prop in Hsk4 as [Je Jo].
apply skel_is_sound in J0 as (J0a & J0lo & J0hi & J0b & J0c). apply skel_is_sound in Je as (Jea & Jelo & Jehi & Jeb & Jec). apply skel_is_sound in Jo as (Joa & Jolo & Johi & Job & Joc).
rewrite FW in J0b, J0lo.
assert (MEQ4 : forall z : word, ~ ((sp0 - 2144 - 2304 <= bv_unsigned z < sp0 - 2144) \/ errW (bv_unsigned z) \/ oflW (bv_unsigned z)) -> ms_mem ms4 z = mem2 z).
{ intros z Hz. apply (HF4 z). intros Hin. exact (Hz (WIN E2 _ _ WL2r E2_2 E2_4 Hin)). }
clear HF4.
assert (RD4 : forall (r : bv 5) v, reg_is eO2r (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot E2 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E2 eO2r ms4 r HS4). }
set (regs4 := ms_regs ms4) in *.
assert (PK4 : forall r, In r KEPTR1 -> getr regs4 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTR1 in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK4. specialize (HK4 _ Hin). cbn beta in HK4.
rewrite (RD4 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (E2old (Z.to_nat r) ltac:(lia)), (E1reg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK4. }
assert (P4_1 : getr regs4 1 = w64 IO_RET) by (etransitivity; [exact (PK4 1 ltac:(unfold KEPTR1; INL)) | exact Q1]).
assert (P4_2 : getr regs4 2 = w64 (sp0 - 2144)) by (etransitivity; [exact (PK4 2 ltac:(unfold KEPTR1; INL)) | exact Q2]).
assert (P4_10 : getr regs4 10 = w64 0) by (rewrite (RD4 10%bv (SLit 0) Z10); reflexivity).
assert (PRS4s : forall a, sp0 - 2144 - 2304 <= a < sp0 - 2144 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E2 eO2r ms4 0 q0 a HS4 ltac:(rewrite ?Hmem4; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite J0a, J0b, J0c. cbn [base_val]. rewrite E2_2. lia. }
set (Wr4 := fun a => (sp0 - 2144 - 2304 <= a < sp0 - 2144) \/ errW a \/ oflW a).
assert (Wr4d : forall a, Wr4 a \/ ~ Wr4 a) by (intros a; subst Wr4; cbn beta; unfold errW, oflW; lia).
assert (Wr4i : forall a, Wr4 a -> stackW a \/ errW a \/ oflW a \/ False) by (intros a Ha; subst Wr4; cbn beta in Ha; unfold stackW; destruct Ha as [Ha|Ha]; [left; lia | tauto]).
assert (Wr4p : forall a, Wr4 a -> ~ errW a -> ~ oflW a -> apresent H (ms_mem ms4) a).
{ intros a Ha He' Hof. subst Wr4. cbn beta in Ha. destruct Ha as [Hs | [Hx | Hx]]; [exact (PRS4s a Hs) | exfalso; exact (He' Hx) | exfalso; exact (Hof Hx)]. }
destruct (frameO mem2 (ms_mem ms4) md2 md4 Wr4 (fun _ => False) HAR2 Wr4d Wr4i ltac:(intros a Hf; destruct Hf) MEQ4 Wr4p (md_frame_sbm _ _ MF4)) as (AV4 & PM4 & HAR4).
subst Wr4. cbv beta in AV4. clear Wr4d Wr4i Wr4p.
eapply SRr_bind.
{ eapply (SRr_ret_at tfibsegs tbl_fo tbl_fo_ok Hwx W E2 eO2r ms4 md4
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms4) (v_jalr (getr (ms_regs ms4) 1) 0) (ms_mem ms4) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md4) mat' md4)));
[exact HS4 | exact Hresv4 | rewrite Hpc4; vm_compute; reflexivity | intros mat'; split; [reflexivity | exists mat'; reflexivity]]. }
intros W5 c5 _ (-> & mat5 & ->).
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4). fold regs4.
assert (MF5 : same_but_materialized md4 md5) by (subst md5; apply with_vm_backing_same).
rewrite P4_1, (AE2y.ret_ok_lit IO_RET ltac:(unfold IO_RET; lia) eq_refl).
assert (R4sp : spZ regs4 = sp0 - 2144) by (unfold spZ; rewrite P4_2; apply unsigned_lit_small; lia).
assert (MBtop : forall a, 0 <= a < 2 ^ 64 -> sp0 - 2144 <= a < sp0 -> mbyte tfibsegs (mrestrict H (ms_mem ms4)) a = mbyte tfibsegs (mrestrict H mem1) a).
{ intros a Hr Ha. unfold errW, oflW in AV4, AV2. rewrite HO, HT in AV4, AV2. apply AE2y.mbyte_of_aview. rewrite AV4 by lia. apply AV2; lia. }
set (v := map (fun p : Z * Z => bv_unsigned (getr regs (Z_to_bv 5 (fst p)))) SAVEDF).
assert (HCv : forall j, (j < 8)%nat -> val_mem tfibsegs (mrestrict H (ms_mem ms4)) (spZ regs4 + 2136 - 8 * Z.of_nat j) 8 (nth j v 0)).
{ intros j Hj. rewrite R4sp. apply (val_mem_frame tfibsegs (mrestrict H mem1)); [intros x Hx; apply MBtop; lia|].
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [| | | | | | | | lia]; subst v; cbn [map fst nth SAVEDF].
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 0) with (sp0 + -8) by lia. exact (QS 0%nat 1 (-8) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 1) with (sp0 + -16) by lia. exact (QS 1%nat 8 (-16) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 2) with (sp0 + -24) by lia. exact (QS 2%nat 9 (-24) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 3) with (sp0 + -32) by lia. exact (QS 3%nat 18 (-32) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 4) with (sp0 + -40) by lia. exact (QS 4%nat 19 (-40) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 5) with (sp0 + -48) by lia. exact (QS 5%nat 20 (-48) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 6) with (sp0 + -56) by lia. exact (QS 6%nat 21 (-56) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 7) with (sp0 + -64) by lia. exact (QS 7%nat 22 (-64) eq_refl). }
assert (Heven : bv_unsigned (getr regs 1) mod 2 = 0).
{ pose proof (u64_range (getr regs 1)) as Hu. pose proof (f_equal bv_unsigned Hra) as E. unfold v_jalr, jalr_tgtZ in E.
rewrite Z.add_0_r, Z_to_bv_unsigned in E.
assert (Hld : Z.land (bv_unsigned (getr regs 1)) (-2) = Z.shiftl (Z.shiftr (bv_unsigned (getr regs 1)) 1) 1).
{ change (-2) with (Z.lnot (Z.ones 1)). rewrite <- Z.ldiff_land. apply Z.ldiff_ones_r. lia. }
rewrite Hld, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 in E by lia. change (2 ^ 1) with 2 in E.
unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
pose proof (Z.mul_div_le (bv_unsigned (getr regs 1)) 2 ltac:(lia)) as Hm1. assert (Hm2 : 0 <= bv_unsigned (getr regs 1) / 2) by (apply Z.div_pos; lia).
rewrite Z.mod_small in E by lia. rewrite <- E. apply Z_mod_mult. }
change (mkCfg (mkst regs4 (Z_to_bv 64 IO_RET) (ms_mem ms4) (seg_rom tfibsegs)) md5) with (cfg_at tfibsegs IO_RET regs4 (ms_mem ms4) md5).
eapply SRr_bind.
{ apply (iopen_tail W regs4 (ms_mem ms4) md5 v eq_refl); rewrite ?R4sp; unfold IO_FRAME; try lia.
- subst v. cbn [map fst SAVEDF]. repeat (apply Forall_cons; [apply u64_range|]). apply Forall_nil.
- subst v. cbn [map fst nth SAVEDF]. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). exact Heven.
- replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- intros j Hj. fold H. rewrite <- R4sp. exact (HCv j Hj). }
intros W6 c6 _ (-> & regs6 & md6 & -> & MF6 & T10 & T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & TK).
pose proof same_io_sbm as SIO.
assert (MF46 : same_but_materialized md4 md6) by (eapply same_but_materialized_trans; [exact MF5 | exact MF6]).
pose proof (same_but_materialized_frame md md1 MF1) as (_ & V01 & Z01 & _). pose proof (same_but_materialized_frame md1 md2 MF2) as (_ & V12 & Z12 & _).
pose proof (same_but_materialized_frame md2 md4 MF4) as (_ & V24 & Z24 & _). pose proof (same_but_materialized_frame md4 md6 MF46) as (_ & V46 & Z46 & _).
assert (Hv0 : nth 0 v 0 = bv_unsigned (getr regs 1)) by (subst v; cbn [map fst nth SAVEDF]; replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity); reflexivity).
apply SRr_ret. split; [reflexivity|]. left. exists regs6, (ms_mem ms4), md6, e.
split; [rewrite Hv0; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact He|].
split.
{ apply (al_frame _ _ LAWS ly S W (ms_mem ms4) md4 (ms_mem ms4) md6 HAR4); [intros a Hr Hown; reflexivity | intros a Hv'; exact Hv' | exact V46 | exact Z46 | | intros a _ _; reflexivity].
apply (same_but_materialized_frame md4 _ MF46). }
split.
{ intros rr Hr. unfold acallee_saved in Hr.
assert (KK : forall r, In r [3; 4; 23; 24; 25; 26; 27] -> getr regs6 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hin. cbn [In] in Hin.
rewrite (TK r) by (unfold KEPTT; cbn [In]; lia). rewrite (PK4 r) by (unfold KEPTR1; cbn [In]; lia). apply (QK r). unfold AE2g.KEPTF. cbn [In]. lia. }
assert (VV : forall j (r : Z), nth_error SAVEDF j = nth_error SAVEDF j -> (j < 8)%nat -> fst (nth j SAVEDF (0, 0)) = r -> w64 (nth j v 0) = getr regs (Z_to_bv 5 r)).
{ intros j r _ Hj Hrz. subst v. rewrite <- Hrz.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [| | | | | | | | lia]; cbn [map fst nth SAVEDF]; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity. }
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T2, R4sp. unfold IO_FRAME. replace (sp0 - 2144 + 2144) with sp0 by lia.
unfold sp0, spZ, w64. apply Z_to_bv_bv_unsigned.
* exact (KK 3 ltac:(INL)).
* exact (KK 4 ltac:(INL)).
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T8. exact (VV 1%nat 8 eq_refl ltac:(lia) eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T9. exact (VV 2%nat 9 eq_refl ltac:(lia) eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ (rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27)) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | Hc]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T18. exact (VV 3%nat 18 eq_refl ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T19. exact (VV 4%nat 19 eq_refl ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T20. exact (VV 5%nat 20 eq_refl ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T21. exact (VV 6%nat 21 eq_refl ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T22. exact (VV 7%nat 22 eq_refl ltac:(lia) eq_refl).
-- apply KK. cbn [In]. lia. }
split; [rewrite T10; exact P4_10|].
split; [rewrite V46, V24, V12; exact V01|].
split; [rewrite Z46, Z24, Z12; exact Z01|].
pose proof same_io_trans3 as SIOT.
split.
{ apply (SIOT md md4 md6); [| exact (SIO _ _ MF46)]. apply (SIOT md md2 md4); [| exact (SIO _ _ MF4)].
apply (SIOT md md1 md2); [exact (SIO _ _ MF1) | exact (SIO _ _ MF2)]. }
split.
{ eapply os_kept_trans; [exact (os_kept_sbm _ _ MF1)|]. eapply os_kept_trans; [exact (os_kept_sbm _ _ MF2)|].
eapply os_kept_trans; [exact (os_kept_sbm _ _ MF4) | exact (os_kept_sbm _ _ MF46)]. }
split.
{ eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact MF2|]. eapply same_but_materialized_trans; [exact MF4 | exact MF46]. }
split.
{
unfold has_chunk in Herr4. rewrite Hmem4 in Herr4. change (nth_error (q0 :: qrest) 18) with (nth_error qrest 17) in Herr4. rewrite Hqe in Herr4.
apply existsb_exists in Herr4 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 eO2r _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs qe ltac:(right; eapply nth_error_In; exact Hqe)) as (_ & _ & _ & Hcs). rewrite Jea in Hcs. cbn [base_val] in Hcs. rewrite E2_4 in Hcs.
replace (TFIB_TP - 164) with (TFIB_TP + -164) by lia.
apply (val_of_chunk_ok tfibsegs E2 _ _ (-164) 4 _ e (proj1 (Forall_forall _ _) Hcs _ Hc)); [| cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite E2_40. apply bv_eq.
rewrite !low32_lit.
replace (alu32 ALU_SUB (Z_to_bv 32 0) (Z_to_bv 32 (bv_unsigned RET + 0))) with (low32 (Z_to_bv 64 e)).
2:{ rewrite low32_lit. apply bv_eq. rewrite alu32_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw]. unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32). rewrite HRETu, Z.add_0_r, (Z.mod_small e) by lia. change (0 mod 2 ^ 32) with 0.
replace (2 ^ 64 - e) with ((2 ^ 32 - e) + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 32 - e)) by lia.
replace (0 - (2 ^ 32 - e)) with (e + (-1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
unfold low32. rewrite sext32_small by lia. reflexivity. }
split.
{
unfold has_chunk in Hofl4. rewrite Hmem4 in Hofl4. change (nth_error (q0 :: qrest) 22) with (nth_error qrest 21) in Hofl4. rewrite Hqo in Hofl4.
apply existsb_exists in Hofl4 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 eO2r _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs qo ltac:(right; eapply nth_error_In; exact Hqo)) as (_ & _ & _ & Hcs). rewrite Joa in Hcs. cbn [base_val] in Hcs.
rewrite <- (Z.add_0_l A_ofl_head).
exact (val_of_chunk_ok tfibsegs E2 _ _ A_ofl_head 8 (SLit 0) 0 (proj1 (Forall_forall _ _) Hcs _ Hc) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
split.
{ intros a Hr Hs Herr Hofl.
rewrite AV4; [| exact Hr | unfold stackW in Hs; intros [X|[X|X]]; [lia | exact (Herr X) | exact (Hofl X)]].
rewrite AV2; [| exact Hr | unfold stackW in Hs; intros [X|[X|X]]; [lia | exact (Herr X) | exact (Hofl X)]]. apply AV1; [exact Hr | unfold stackW in Hs; lia]. }
split.
{ intros a Hs. unfold stackW in Hs. unfold errW, oflW in PM4, PM2. rewrite HO, HT in PM4, PM2.
destruct (Z_lt_le_dec a (sp0 - 2144 - 2304)) as [L|L]; [| destruct (Z_lt_le_dec a (sp0 - 2144)) as [L2|L2]; [apply PRS4s; lia|]].
- apply PM4; [lia | lia | lia |]. apply PM2; [lia | lia | lia |]. apply PM1, Hpres. lia.
- apply PM4; [lia | lia | lia |]. apply PM2; [lia | lia | lia |]. apply PRS1. lia. }
intros a Hr Herr Hofl Hp. apply PM4; [exact Hr | exact Herr | exact Hofl |]. apply PM2; [exact Hr | exact Herr | exact Hofl |]. apply PM1. exact Hp.
-
intros md3 fd Hfd Hfdn MF3.
pose proof (u64_range fd) as Hfdu.
set (E2 := ewset E1 40 fd).
assert (E2old : forall i, (i < 40)%nat -> ew E2 i = ew E1 i) by (intros i Hi; subst E2; apply ew_ewset_other; lia).
assert (E2_40 : ew E2 40 = fd) by (subst E2; apply ew_ewset_same).
assert (E2_2 : bv_unsigned (ew E2 2) = sp0 - 2144) by (rewrite (E2old 2%nat ltac:(lia)); exact E1_2).
assert (E2_4 : bv_unsigned (ew E2 4) = TFIB_TP) by (rewrite (E2old 4%nat ltac:(lia)); exact E1_4).
assert (HS3 : st_ok tfibsegs E2 (resumeO2 eO1) (restrict H (mkst (regupd regs2 10 fd) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)))).
{ unfold resumeO2. rewrite restrict_mkst_fx, <- Hpc. subst E2.
apply (st_ok_resume_atom tfibsegs 40 (mkAF 0 (2 ^ 31 - 1) 0) E1 eO1 regs2 (mrestrict H mem2) fd Hregs2 ltac:(rewrite Hmem; exact Hmemok2) HG2 Hat); cbn [af_lo af_hi af_al2]; [lia | lia |].
change (2 ^ 0) with 1. apply Z.mod_1_r. }
eapply SRr_bind; [exact (fo_phase W E2 (resumeO2 eO1) eO2 _ (mkst (regupd regs2 10 fd) (v_addi (Z_to_bv 64 FO_ECALL) 4) mem2 (seg_rom tfibsegs)) md3 HS3 r_O2)|].
intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [ms_mem mkst] in HF4. clear HFr4.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
set (md2' := with_fds (fd_insert (m_fds md2) fd (FdFileW sink_path (Z_to_bv 64 0))) (with_fs (fs_set (m_fs md2) sink_path []) md2)) in MF3.
assert (MD24 : md_frame md2 md4).
{ eapply md_frame_trans; [| apply md_frame_sbm; subst md4; apply with_vm_backing_same]. eapply md_frame_trans; [| exact (md_frame_sbm _ _ MF3)].
subst md2'. eapply md_frame_trans; [apply md_frame_with_fs | apply md_frame_with_fds]. }
pose proof shapeO2_ok as Hsr. unfold shapeO2 in Hsr.
apply andb_prop in Hsr as [Hsr Hsk4]. apply andb_prop in Hsr as [Hsr Hofl4]. apply andb_prop in Hsr as [Hsr HC4]. apply andb_prop in Hsr as [Hsr HK4].
apply andb_prop in Hsr as [Hsr Z19]. apply andb_prop in Hsr as [Hsr Z18]. apply andb_prop in Hsr as [Hsr Z9]. apply andb_prop in Hsr as [Hsr Z8].
apply andb_prop in Hsr as [Hsr Z2]. apply andb_prop in Hsr as [Hsr Z1]. apply andb_prop in Hsr as [Hsr Z10].
apply andb_prop in Hsr as [Hpc4 Hrv4]. apply Z.eqb_eq in Hpc4.
unfold skelsO in Hsk4. apply andb_prop in Hsk4 as [Hlen4 Hsk4]. destruct (ss_mem eO2) as [|q0 qrest] eqn:Hmem4; [discriminate Hsk4|].
apply andb_prop in Hsk4 as [Hsk4 _]. apply andb_prop in Hsk4 as [J0 Hsk4].
destruct (nth_error qrest 17) as [qe|] eqn:Hqe; [|discriminate Hsk4]. destruct (nth_error qrest 21) as [qo|] eqn:Hqo; [|discriminate Hsk4].
apply andb_prop in Hsk4 as [Je Jo].
apply skel_is_sound in J0 as (J0a & J0lo & J0hi & J0b & J0c). apply skel_is_sound in Jo as (Joa & Jolo & Johi & Job & Joc). clear Je.
rewrite FW in J0b, J0lo.
assert (MEQ4 : forall z : word, ~ ((sp0 - 2144 - 2304 <= bv_unsigned z < sp0 - 2144) \/ errW (bv_unsigned z) \/ oflW (bv_unsigned z)) -> ms_mem ms4 z = mem2 z).
{ intros z Hz. apply (HF4 z). intros Hin. exact (Hz (WIN E2 _ _ WL2 E2_2 E2_4 Hin)). }
clear HF4.
assert (RD4 : forall (r : bv 5) v, reg_is eO2 (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot E2 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E2 eO2 ms4 r HS4). }
set (regs4 := ms_regs ms4) in *.
assert (PRS4s : forall a, sp0 - 2144 - 2304 <= a < sp0 - 2144 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E2 eO2 ms4 0 q0 a HS4 ltac:(rewrite ?Hmem4; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite J0a, J0b, J0c. cbn [base_val]. rewrite E2_2. lia. }
set (Wr4 := fun a => (sp0 - 2144 - 2304 <= a < sp0 - 2144) \/ errW a \/ oflW a).
assert (Wr4d : forall a, Wr4 a \/ ~ Wr4 a) by (intros a; subst Wr4; cbn beta; unfold errW, oflW; lia).
assert (Wr4i : forall a, Wr4 a -> stackW a \/ errW a \/ oflW a \/ False) by (intros a Ha; subst Wr4; cbn beta in Ha; unfold stackW; destruct Ha as [Ha|Ha]; [left; lia | tauto]).
assert (Wr4p : forall a, Wr4 a -> ~ errW a -> ~ oflW a -> apresent H (ms_mem ms4) a).
{ intros a Ha He' Hof. subst Wr4. cbn beta in Ha. destruct Ha as [Hs | [Hx | Hx]]; [exact (PRS4s a Hs) | exfalso; exact (He' Hx) | exfalso; exact (Hof Hx)]. }
destruct (frameO mem2 (ms_mem ms4) md2 md4 Wr4 (fun _ => False) HAR2 Wr4d Wr4i ltac:(intros a Hf; destruct Hf) MEQ4 Wr4p MD24) as (AV4 & PM4 & HAR4).
subst Wr4. cbv beta in AV4. clear Wr4d Wr4i Wr4p.
pose proof (st_ok_restrict_mkst tfibsegs H E2 _ _ HS4 eq_refl) as Hshape4. rewrite Hpc4 in Hshape4. fold regs4 in Hshape4.
assert (CELL : forall off v z, has_chunk eO2 0 off 8 v = true -> sv_denot E2 v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
val_mem tfibsegs (mrestrict H (ms_mem ms4)) (sp0 - 2144 + off) 8 z).
{ intros off v z Hh Hd Hz. unfold has_chunk in Hh. rewrite Hmem4 in Hh. cbn [nth_error] in Hh. apply existsb_exists in Hh as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 eO2 _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs q0 ltac:(left; reflexivity)) as (_ & _ & _ & Hcs). rewrite J0a in Hcs. cbn [base_val] in Hcs. rewrite E2_2 in Hcs.
exact (val_of_chunk_ok tfibsegs E2 _ _ off 8 v z (proj1 (Forall_forall _ _) Hcs _ Hc) Hd Hz ltac:(cbn; lia)). }
assert (HCo : forall off v, In (off, v) cellsO2 -> has_chunk eO2 0 off 8 v = true) by (intros off v Hin; rewrite forallb_forall in HC4; exact (HC4 _ Hin)).
pose proof (same_but_materialized_frame md md1 MF1) as (_ & V01 & Z01 & _ & _ & _ & _ & _ & FD01 & _ & _ & FS01 & _).
pose proof (same_but_materialized_frame md1 md2 MF2) as (_ & V12 & Z12 & _ & _ & _ & _ & _ & FD12 & _ & _ & FS12 & _).
pose proof (same_but_materialized_frame _ md3 MF3) as (_ & V23 & Z23 & _ & _ & _ & _ & _ & FD23 & _ & _ & FS23 & _).
assert (MF34 : same_but_materialized md3 md4) by (subst md4; apply with_vm_backing_same).
pose proof (same_but_materialized_frame md3 md4 MF34) as (_ & V34 & Z34 & _ & _ & _ & _ & _ & FD34 & _ & _ & FS34 & _).
assert (MBtop : forall a, 0 <= a < 2 ^ 64 -> sp0 - 2144 <= a < sp0 -> mbyte tfibsegs (mrestrict H (ms_mem ms4)) a = mbyte tfibsegs (mrestrict H mem1) a).
{ intros a Hr Ha. unfold errW, oflW in AV4, AV2. rewrite HO, HT in AV4, AV2. apply AE2y.mbyte_of_aview. rewrite AV4 by lia. apply AV2; lia. }
set (v8 := bv_unsigned (getr regs1 8%bv)). set (v9 := bv_unsigned (getr regs1 9%bv)). set (v18 := bv_unsigned (getr regs1 18%bv)). set (v19 := bv_unsigned (getr regs1 19%bv)).
assert (EV : forall i (r : bv 5) vv, Z.of_nat i = bv_unsigned r -> (i < 40)%nat -> vv = bv_unsigned (getr regs1 r) -> sv_denot E2 (SOff i 0) = Z_to_bv 64 vv).
{ intros i r vv Hi Hlt ->. cbn [sv_denot]. rewrite (E2old i Hlt), (E1reg i r Hi), Z.add_0_r. reflexivity. }
apply SRr_ret. split; [reflexivity|]. right. exists regs4, (ms_mem ms4), md4, fd, v8, v9, v18, v19.
split; [unfold cfg_at; rewrite Hshape4 at 1; reflexivity|].
split; [exact HAR4|].
split; [rewrite (RD4 10%bv _ Z10); reflexivity|].
split; [rewrite (RD4 1%bv _ Z1); reflexivity|].
split; [rewrite (RD4 2%bv _ Z2); cbn [sv_denot]; rewrite E2_2, FF; unfold w64; f_equal; lia|].
split; [rewrite (RD4 8%bv _ Z8); reflexivity|].
split; [rewrite (RD4 9%bv _ Z9); cbn [sv_denot]; rewrite E2_40, Z.add_0_r; apply Z_to_bv_bv_unsigned|].
split; [rewrite (RD4 18%bv _ Z18); reflexivity|].
split; [rewrite (RD4 19%bv _ Z19); reflexivity|].
split.
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold AE2g.KEPTF in Hin; cbn in Hin; lia).
assert (Hur : bv_unsigned (Z_to_bv 5 r) = r) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
rewrite forallb_forall in HK4. pose proof (HK4 r ltac:(unfold KEPTO; unfold AE2g.KEPTF in Hin; cbn [In] in Hin |- *; lia)) as Hk. cbn beta in Hk.
rewrite (RD4 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)) by (rewrite Hur; exact Hk).
cbn [sv_denot]. rewrite (E2old (Z.to_nat r) ltac:(lia)), (E1reg (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Hur; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
exact (QK r Hin). }
split; [exact Hfd|].
split; [rewrite <- FD01, <- FD12; exact Hfdn|].
split; [rewrite FD34, FD23; subst md2'; cbn [m_fds with_fds with_fs]; rewrite FD12, FD01; reflexivity|].
split; [rewrite FS34, FS23; subst md2'; cbn [m_fs with_fds with_fs]; rewrite FS12, FS01; reflexivity|].
split; [exact (eq_trans (proj1 MD24) (eq_trans V12 V01))|].
split; [exact (eq_trans (proj2 MD24) (eq_trans Z12 Z01))|].
split.
{ eapply os_kept_trans; [exact (os_kept_sbm _ _ MF1)|]. eapply os_kept_trans; [exact (os_kept_sbm _ _ MF2)|].
eapply os_kept_trans; [| exact (os_kept_sbm _ _ MF34)]. eapply os_kept_trans; [| exact (os_kept_sbm _ _ MF3)].
subst md2'. eapply os_kept_trans; [apply os_kept_with_fs | apply os_kept_with_fds]. }
split; [subst v8; apply u64_range|]. split; [subst v9; apply u64_range|]. split; [subst v18; apply u64_range|]. split; [subst v19; apply u64_range|].
rewrite FF.
split; [replace (sp0 - 2144 - 8) with (sp0 - 2144 + -8) by lia; apply (CELL (-8) _ _ (HCo _ _ ltac:(unfold cellsO2; INL))); [| unfold IO_RET; lia];
cbn [sv_denot]; rewrite (E2old 1%nat ltac:(lia)), (E1reg 1%nat 1%bv eq_refl), Q1, Z.add_0_r; reflexivity|].
split; [replace (sp0 - 2144 - 16) with (sp0 - 2144 + -16) by lia; apply (CELL (-16) _ _ (HCo (-16) (SOff 8 0) ltac:(unfold cellsO2; INL))); [exact (EV 8%nat 8%bv v8 eq_refl ltac:(lia) eq_refl) | subst v8; apply u64_range]|].
split; [replace (sp0 - 2144 - 24) with (sp0 - 2144 + -24) by lia; apply (CELL (-24) _ _ (HCo (-24) (SOff 9 0) ltac:(unfold cellsO2; INL))); [exact (EV 9%nat 9%bv v9 eq_refl ltac:(lia) eq_refl) | subst v9; apply u64_range]|].
split; [replace (sp0 - 2144 - 32) with (sp0 - 2144 + -32) by lia; apply (CELL (-32) _ _ (HCo (-32) (SOff 18 0) ltac:(unfold cellsO2; INL))); [exact (EV 18%nat 18%bv v18 eq_refl ltac:(lia) eq_refl) | subst v18; apply u64_range]|].
split; [replace (sp0 - 2144 - 40) with (sp0 - 2144 + -40) by lia; apply (CELL (-40) _ _ (HCo (-40) (SLit FO_FDOPEN_RA) ltac:(unfold cellsO2; INL))); [reflexivity | unfold FO_FDOPEN_RA; lia]|].
split; [replace (sp0 - 2144 - 48) with (sp0 - 2144 + -48) by lia; apply (CELL (-48) _ _ (HCo (-48) (SLit A_WB) ltac:(unfold cellsO2; INL))); [reflexivity | unfold A_WB; lia]|].
split; [replace (sp0 - 2144 - 56) with (sp0 - 2144 + -56) by lia; apply (CELL (-56) _ _ (HCo (-56) (SOff 40 0) ltac:(unfold cellsO2; INL))); [cbn [sv_denot]; rewrite E2_40, Z.add_0_r; reflexivity | apply u64_range]|].
split; [replace (sp0 - 2144 - 64) with (sp0 - 2144 + -64) by lia; apply (CELL (-64) _ _ (HCo (-64) (SLit FO_S2VAL) ltac:(unfold cellsO2; INL))); [reflexivity | unfold FO_S2VAL; lia]|].
split; [replace (sp0 - 2144 - 72) with (sp0 - 2144 + -72) by lia; apply (CELL (-72) _ _ (HCo (-72) (SOff 19 0) ltac:(unfold cellsO2; INL))); [exact (EV 19%nat 19%bv v19 eq_refl ltac:(lia) eq_refl) | subst v19; apply u64_range]|].
split; [replace (sp0 - 2144 - 80) with (sp0 - 2144 + -80) by lia; apply (CELL (-80) _ _ (HCo (-80) (SOff 32 0) ltac:(unfold cellsO2; INL))); [| exact Hcv];
cbn [sv_denot]; rewrite (E2old 32%nat ltac:(lia)), E1_32, Z.add_0_r, unsigned_lit_small by lia; reflexivity|].
split.
{ intros j rz off Hj. assert (Hoff : -64 <= off <= -8) by (do 8 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply (val_mem_frame tfibsegs (mrestrict H mem1)); [| exact (QS j rz off Hj)]. intros x Hx. apply MBtop; lia. }
split.
{
unfold has_chunk in Hofl4. rewrite Hmem4 in Hofl4. change (nth_error (q0 :: qrest) 22) with (nth_error qrest 21) in Hofl4. rewrite Hqo in Hofl4.
apply existsb_exists in Hofl4 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 eO2 _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs qo ltac:(right; eapply nth_error_In; exact Hqo)) as (_ & _ & _ & Hcs). rewrite Joa in Hcs. cbn [base_val] in Hcs.
rewrite <- (Z.add_0_l A_ofl_head).
exact (val_of_chunk_ok tfibsegs E2 _ _ A_ofl_head 8 (SLit 0) 0 (proj1 (Forall_forall _ _) Hcs _ Hc) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
split.
{ intros a Hr Hs Herr Hofl.
rewrite AV4; [| exact Hr | unfold stackW in Hs; intros [X|[X|X]]; [lia | exact (Herr X) | exact (Hofl X)]].
rewrite AV2; [| exact Hr | unfold stackW in Hs; intros [X|[X|X]]; [lia | exact (Herr X) | exact (Hofl X)]]. apply AV1; [exact Hr | unfold stackW in Hs; lia]. }
split.
{ intros a Hs. unfold stackW in Hs. unfold errW, oflW in PM4, PM2. rewrite HO, HT in PM4, PM2.
destruct (Z_lt_le_dec a (sp0 - 2144 - 2304)) as [L|L]; [| destruct (Z_lt_le_dec a (sp0 - 2144)) as [L2|L2]; [apply PRS4s; lia|]].
- apply PM4; [lia | lia | lia |]. apply PM2; [lia | lia | lia |]. apply PM1, Hpres. lia.
- apply PM4; [lia | lia | lia |]. apply PM2; [lia | lia | lia |]. apply PRS1. lia. }
intros a Hr Herr Hofl Hp. apply PM4; [exact Hr | exact Herr | exact Hofl |]. apply PM2; [exact Hr | exact Herr | exact Hofl |]. apply PM1. exact Hp.
Qed.
End g.
Theorem fopen_LB : forall (W2 : world tfibsegs) regs2 mem2 md2 (f : Z),
getr regs2 10 = w64 f -> 4096 <= f -> f + 4096 <= 2 ^ 47 -> f mod 16 = 0 ->
SRr tfibsegs W2 (cfg_at tfibsegs FO_MALLOC_RA regs2 mem2 md2)
(fun W' c' => W' = W2 /\ exists regs' md', c' = cfg_at tfibsegs PC_MEMSET regs' mem2 md' /\ same_but_materialized md2 md' /\
getr regs' 10 = w64 f /\ getr regs' 11 = w64 0 /\ getr regs' 12 = w64 232 /\ getr regs' 1 = w64 FO_MEMSET_RA /\ getr regs' 8 = w64 f /\
(forall r, In r KEPTB -> getr regs' (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r))).
Proof.
intros W2 regs2 mem2 md2 f G10 Hf1 Hf2 Hf3. pose proof AF0x.Hwx_tfa as Hwx. set (H2 := w_H W2).
set (E := AE2y.Env regs2 []).
assert (EregL : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs2 r) by (intros; apply AE2y.Env_reg; assumption).
assert (E10 : bv_unsigned (ew E 10) = f) by (rewrite (EregL 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS0 : st_ok tfibsegs E ssB (restrict H2 (mkst regs2 (Z_to_bv 64 FO_MALLOC_RA) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssB, E, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (map (Z_to_bv 64) [])) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. vm_compute. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10. change (2 ^ 4) with 16.
repeat split; try lia. }
unfold cfg_at. change (w64 FO_MALLOC_RA) with (Z_to_bv 64 FO_MALLOC_RA).
eapply SRr_bind; [exact (fo_phase_to W2 E PC_MEMSET ssB eB _ (mkst regs2 (Z_to_bv 64 FO_MALLOC_RA) mem2 (seg_rom tfibsegs)) md2 HS0 r_B)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [ms_mem mkst] in HF1. clear HFr1.
assert (MEQ : forall z : word, ms_mem ms1 z = mem2 z).
{ intros z. apply (HF1 z). intros (r & Hin & Hr). unfold ssB in Hin. cbn [ss_mem] in Hin. destruct Hin. }
assert (MEM : ms_mem ms1 = mem2) by (apply FunctionalExtensionality.functional_extensionality; exact MEQ).
pose proof shapeB_ok as Hsh. unfold shapeB in Hsh.
apply andb_prop in Hsh as [Hsh _]. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh Q8]. apply andb_prop in Hsh as [Hsh Q1].
apply andb_prop in Hsh as [Hsh Q12]. apply andb_prop in Hsh as [Hsh Q11]. apply andb_prop in Hsh as [Hsh Q10].
apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eB (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H2 E eB ms1 r HS1). }
pose proof (st_ok_restrict_mkst tfibsegs H2 E _ _ HS1 eq_refl) as Hshape. rewrite Hpc, MEM in Hshape. rewrite Hshape.
apply SRr_ret. split; [reflexivity|]. exists (ms_regs ms1), (with_vm_backing (m_vm_lazy md2) mat1 md2).
split; [reflexivity|]. split; [apply with_vm_backing_same|].
assert (F10 : sv_denot E (SOff 10 0) = w64 f) by (cbn [sv_denot]; rewrite (EregL 10%nat 10%bv eq_refl), G10, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
split; [rewrite (RD 10%bv (SOff 10 0) Q10); exact F10|].
split; [rewrite (RD 11%bv (SLit 0) Q11); reflexivity|].
split; [rewrite (RD 12%bv (SLit 232) Q12); reflexivity|].
split; [rewrite (RD 1%bv (SLit FO_MEMSET_RA) Q1); reflexivity|].
split; [rewrite (RD 8%bv (SOff 10 0) Q8); exact F10|].
intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTB in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK. specialize (HK _ Hin). cbn beta in HK.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (EregL (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs regsC : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (f cval v8 v9 v18 v19 : Z) (fd : word) (fde : FdEntry).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let m0 := mrestrict H mem.
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hal16 : sp0 mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + FOP_WIN <= sp0.
Hypothesis Hshi : sp0 <= ly_stk_hi ly.
Hypothesis Hpres : forall a, sp0 - FOP_WIN <= a < sp0 -> apresent H mem a.
Hypothesis C2 : getr regsC 2 = w64 (sp0 - 2240).
Hypothesis C8 : getr regsC 8 = w64 f.
Hypothesis C9 : getr regsC 9 = fd.
Hypothesis C18 : getr regsC 18 = w64 A_WB.
Hypothesis C19 : getr regsC 19 = w64 A_canary.
Hypothesis CK : forall r, In r AE2g.KEPTF -> getr regsC (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Hypothesis Hfd : bv_unsigned fd < 2 ^ 31.
Hypothesis Hf1 : 4096 <= f.
Hypothesis Hf2 : f + 4096 <= 2 ^ 47.
Hypothesis Hf3 : f mod 16 = 0.
Hypothesis HZ : forall i, 0 <= i < 232 -> aview tfibsegs H mem (f + i) = Some 0.
Hypothesis HBpres : forall a, f <= a < f + 1264 -> apresent H mem a.
Hypothesis HBown : forall a, f <= a < f + 1264 -> ~ aowned B ly S a.
Hypothesis HBstk : f + 1264 <= sp0 - FOP_WIN \/ sp0 <= f.
Hypothesis HBimg : f + 1264 <= TFIB_IMG_LO \/ TFIB_IMG_END <= f.
Hypothesis HBam : amem_range f 1264.
Hypothesis HSTC : cells_hold m0 st_cells.
Hypothesis HIMG : ro_img m0.
Hypothesis Hcan1 : val_mem tfibsegs m0 A_GOT_canary 8 A_canary.
Hypothesis Hcan2 : val_mem tfibsegs m0 A_canary 8 cval.
Hypothesis Hcv : 0 <= cval < 2 ^ 64.
Hypothesis Henv0 : val_mem tfibsegs m0 A_threaded 1 0.
Hypothesis Henv1 : val_mem tfibsegs m0 A_need_locks 1 0.
Hypothesis Henv2 : val_mem tfibsegs m0 A_ofl_lock 4 0.
Hypothesis Hhead : val_mem tfibsegs m0 A_ofl_head 8 0.
Hypothesis HOFLown : forall a, A_ofl_head <= a < A_ofl_head + 8 -> ~ aowned B ly S a.
Hypothesis Hv8 : 0 <= v8 < 2 ^ 64.
Hypothesis Hv9 : 0 <= v9 < 2 ^ 64.
Hypothesis Hv18 : 0 <= v18 < 2 ^ 64.
Hypothesis Hv19 : 0 <= v19 < 2 ^ 64.
Hypothesis D8 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 8) 8 IO_RET.
Hypothesis D16 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 16) 8 v8.
Hypothesis D24 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 24) 8 v9.
Hypothesis D32 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 32) 8 v18.
Hypothesis D40 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 40) 8 FO_FDOPEN_RA.
Hypothesis D48 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 48) 8 A_WB.
Hypothesis D56 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 56) 8 (bv_unsigned fd).
Hypothesis D64 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 64) 8 FO_S2VAL.
Hypothesis D72 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 72) 8 v19.
Hypothesis D80 : val_mem tfibsegs m0 (sp0 - FO_FRAME - 80) 8 cval.
Hypothesis QS : forall j rz off, nth_error SAVEDF j = Some (rz, off) -> val_mem tfibsegs m0 (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz))).
Hypothesis HFDL : fd_lookup (m_fds md) fd = Some fde.
Hypothesis Hfde : forall rd wr : bool, fde <> FdUrandom.
Definition stackC (a : Z) : Prop := sp0 - FOP_WIN <= a < sp0.
Definition blkW (a : Z) : Prop := f <= a < f + 1264.
Definition LCPOST : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ getr regs' 10 = w64 f /\
m_vmmaps md' = m_vmmaps md /\ m_vm_lazy md' = m_vm_lazy md /\ same_io md md' /\ os_kept md md' /\ same_but_materialized md md' /\
m_fds md' = m_fds md /\ m_fs md' = m_fs md /\
file_at tfibsegs tfib_K (mrestrict H mem') f (bv_unsigned fd) [] /\
val_mem tfibsegs (mrestrict H mem') A_ofl_head 8 f /\
(forall a, 0 <= a < 2 ^ 64 -> ~ stackC a -> ~ blkW a -> ~ oflW a -> aview tfibsegs H mem' a = aview tfibsegs H mem a) /\
(forall a, stackC a -> apresent H mem' a) /\
(forall a, apresent H mem a -> apresent H mem' a).
Lemma factsC' : 2 ^ 44 <= sp0 /\ sp0 <= 2 ^ 47 /\ FOP_WIN = 6400 /\ FO_WINC = 2208 /\ FO_FRAME = 2144 /\
(ly_stk_hi ly <= 2 ^ 47 /\ 17594333495296 + 6400 <= sp0) /\ A_ofl_head = 0x5f9688 /\ TFIB_IMG_END = 0x5fb000.
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FS : FOP_WIN = 6400) by reflexivity. rewrite FS in *. subst sp0.
repeat split; try lia; try reflexivity.
Qed.
Lemma frameC : forall (memA mem1 : word -> option byte) mdA md1 (Wr : Z -> Prop),
AR tfibsegs B ly S W memA mdA ->
(forall a, Wr a \/ ~ Wr a) ->
(forall a, Wr a -> stackC a \/ oflW a \/ blkW a) ->
(forall z : word, ~ Wr (bv_unsigned z) -> mem1 z = memA z) ->
(forall a, Wr a -> ~ oflW a -> apresent H mem1 a) ->
md_frame mdA md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H mem1 a = aview tfibsegs H memA a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ oflW a -> apresent H memA a -> apresent H mem1 a) /\
AR tfibsegs B ly S W mem1 md1.
Proof.
intros memA mem1 mdA md1 Wr HARA Wdec HWin MEQ PRS MF.
pose proof factsC' as (Hsp & Hsp2 & FS & FW & FF & Lhi & HO & HIE). rewrite FS in *. unfold stackC, oflW, blkW in *. rewrite HO in *.
pose proof asan_consts as (C1 & C2' & C3 & C4 & C5).
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H mem1 a = aview tfibsegs H memA a).
{ intros a Hr Hw. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Hw. }
assert (PM : forall a, 0 <= a < 2 ^ 64 -> ~ (0x5f9688 <= a < 0x5f9688 + 8) -> apresent H memA a -> apresent H mem1 a).
{ intros a Hr Ho Hp. destruct (Wdec a) as [Hw|Hw]; [apply PRS; assumption|].
apply (apresent_same H memA mem1 a); [apply MEQ; rewrite unsigned_lit_small by lia; exact Hw | exact Hp]. }
split; [exact AV|]. split; [exact PM|].
pose proof (md_frame_eager _ _ MF) as Feu. destruct MF as [Fmaps Flazy].
assert (IMGb : forall a, (0x5f9688 <= a < 0x5f9688 + 8) -> seg_rom tfibsegs (Z_to_bv 64 a) <> None).
{ intros a Ha. rewrite <- HO in Ha. destruct (ofl_img_facts_fo (a - A_ofl_head) ltac:(lia)) as [_ Hrom]. replace (A_ofl_head + (a - A_ofl_head)) with a in Hrom by lia. exact Hrom. }
apply (al_frame _ _ LAWS ly S W memA mdA mem1 _ HARA).
+ intros a Hr Hown. apply AV; [exact Hr|]. intros Hw. destruct (HWin a Hw) as [Hs | [Ho | Hb]].
* exact (al_stack _ _ LAWS ly S W memA mdA a HARA ltac:(unfold sp0 in *; lia) Hown).
* exact (HOFLown a Ho Hown).
* exact (HBown a Hb Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem1 a). rewrite (AE2y.aview_mod _ memA a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Wdec a') as [Hw|Hw]; [| rewrite AV by assumption; exact Hv].
destruct (HWin a' Hw) as [Hs | [Ho | Hb]].
* apply AE2y.aview_some_of_apresent. apply PRS; [exact Hw | lia].
* unfold aview, mbyte. destruct (mrestrict (w_H W) mem1 (Z_to_bv 64 a')) as [b|]; [cbn; discriminate|].
pose proof (IMGb a' Ho) as Hrom. destruct (seg_rom tfibsegs (Z_to_bv 64 a')); [cbn; discriminate | exfalso; exact (Hrom eq_refl)].
* apply AE2y.aview_some_of_apresent. apply PRS; [exact Hw |]. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. lia.
+ exact Fmaps.
+ exact Flazy.
+ exact Feu.
+ intros a Hband Hh. pose proof (AE2y.in_band_rw_u64 a Hband) as Hr. change (w64 a) with (Z_to_bv 64 a) in *.
apply MEQ. rewrite unsigned_lit_small by lia. intros Hw. destruct (HWin a Hw) as [Hs | [Ho | Hb]].
* exfalso. pose proof (Hpres a Hs) as [Hn0 _]. unfold H in Hn0. rewrite Hh in Hn0. discriminate.
* unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband. clear - Hband Ho. lia.
* exfalso. pose proof (HBpres a Hb) as [Hn0 _]. unfold H in Hn0. rewrite Hh in Hn0. discriminate.
Qed.
Theorem fopen_LC : SRr tfibsegs W (cfg_at tfibsegs FO_MEMSET_RA regsC mem md) LCPOST.
Proof.
pose proof factsC' as (Hsp & Hsp2 & FS & FW & FF & Lhi & HO & HIE). rewrite FS in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi' & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi'.
pose proof AF0x.Hwx_tfa as Hwx. pose proof asan_consts as (K1 & K2 & K3 & K4 & K5).
assert (IW : IO_WIN = 2160) by reflexivity. assert (IFR : IO_FRAME = 2144) by reflexivity.
set (E := AE2y.Env regsC [cval; v8; v9; v18; v19; IO_RET]).
assert (EregC : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regsC r) by (intros; apply AE2y.Env_reg; assumption).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 2240) by (rewrite (EregC 2%nat 2%bv eq_refl), C2; apply unsigned_lit_small; lia).
assert (E8 : bv_unsigned (ew E 8) = f) by (rewrite (EregC 8%nat 8%bv eq_refl), C8; apply unsigned_lit_small; lia).
assert (E9 : ew E 9 = fd) by (rewrite (EregC 9%nat 9%bv eq_refl); exact C9).
assert (E32 : ew E 32 = Z_to_bv 64 cval) by (exact (AE2y.Env_x regsC [cval; v8; v9; v18; v19; IO_RET] 0%nat cval eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 v8) by (exact (AE2y.Env_x regsC [cval; v8; v9; v18; v19; IO_RET] 1%nat v8 eq_refl)).
assert (E34 : ew E 34 = Z_to_bv 64 v9) by (exact (AE2y.Env_x regsC [cval; v8; v9; v18; v19; IO_RET] 2%nat v9 eq_refl)).
assert (E35 : ew E 35 = Z_to_bv 64 v18) by (exact (AE2y.Env_x regsC [cval; v8; v9; v18; v19; IO_RET] 3%nat v18 eq_refl)).
assert (E36 : ew E 36 = Z_to_bv 64 v19) by (exact (AE2y.Env_x regsC [cval; v8; v9; v18; v19; IO_RET] 4%nat v19 eq_refl)).
assert (E37 : ew E 37 = Z_to_bv 64 IO_RET) by (exact (AE2y.Env_x regsC [cval; v8; v9; v18; v19; IO_RET] 5%nat IO_RET eq_refl)).
assert (EX : forall i z, ew E i = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> sv_denot E (SOff i 0) = Z_to_bv 64 z).
{ intros i z Hi Hz. cbn [sv_denot]. rewrite Hi, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (HZB : forall a, f <= a < f + 232 -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0)).
{ intros a Ha. replace a with (f + (a - f)) by lia. apply (AF0x.aview_byte H mem). apply HZ. lia. }
assert (WOFL : forall (m : word -> option byte) o, 0 <= o < 8 -> writable_at tfibsegs m (A_ofl_head + o)).
{ intros m o Ho. destruct (ofl_img_facts_fo o Ho) as [Hw _]. unfold img_writable_ok in Hw.
apply (writable_at_grows tfibsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
unfold writable_at. destruct (wview tfibsegs (fun _ => None) (Z_to_bv 64 (A_ofl_head + o))); [discriminate | discriminate Hw]. }
assert (ZSH : forallb (fun c => match c with YP09.mkChunk o (CVal n (SLit 0)) => (0 <=? o) && (o + Z.of_N n <=? 232) && (Z.of_N n <=? 8) | _ => false end) zhdr = true) by (vm_compute; reflexivity).
assert (HS1 : st_ok tfibsegs E ssC (restrict H (mkst regsC (Z_to_bv 64 FO_MEMSET_RA) mem (seg_rom tfibsegs)))).
{ unfold ssC.
apply (st_ok_pin_reg E (mkSS FO_MEMSET_RA (sr_set sr_atoms 18%bv (SLit A_WB)) memC None (mkFacts factsC [] [])) _ 19%bv (SLit A_canary));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite C19; reflexivity].
apply (st_ok_pin_reg E (mkSS FO_MEMSET_RA sr_atoms memC None (mkFacts factsC [] [])) _ 18%bv (SLit A_WB));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite C18; reflexivity].
rewrite restrict_mkst_fx. unfold E, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regsC (map (Z_to_bv 64) [cval; v8; v9; v18; v19; IO_RET])) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memC. apply Forall_cons.
{
unfold stkC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2, FW.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply AE2y.apresent_writable; apply Hpres; lia|].
unfold stkC_chunks. rewrite FF in *.
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [exact (EX 32%nat cval E32 Hcv) | cbn; lia | cbn; lia | replace (sp0 - 2240 + 16) with (sp0 - 2144 - 80) by lia; exact D80]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [exact (EX 36%nat v19 E36 Hv19) | cbn; lia | cbn; lia | replace (sp0 - 2240 + 24) with (sp0 - 2144 - 72) by lia; exact D72]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [reflexivity | unfold FO_S2VAL; cbn; lia | cbn; lia | replace (sp0 - 2240 + 32) with (sp0 - 2144 - 64) by lia; exact D64]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [cbn [sv_denot]; rewrite E9, Z.add_0_r; reflexivity | cbn; pose proof (u64_range fd); lia | cbn; lia | replace (sp0 - 2240 + 40) with (sp0 - 2144 - 56) by lia; exact D56]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [reflexivity | unfold A_WB; cbn; lia | cbn; lia | replace (sp0 - 2240 + 48) with (sp0 - 2144 - 48) by lia; exact D48]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [reflexivity | unfold FO_FDOPEN_RA; cbn; lia | cbn; lia | replace (sp0 - 2240 + 56) with (sp0 - 2144 - 40) by lia; exact D40]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [exact (EX 35%nat v18 E35 Hv18) | cbn; lia | cbn; lia | replace (sp0 - 2240 + 64) with (sp0 - 2144 - 32) by lia; exact D32]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [exact (EX 34%nat v9 E34 Hv9) | cbn; lia | cbn; lia | replace (sp0 - 2240 + 72) with (sp0 - 2144 - 24) by lia; exact D24]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [exact (EX 33%nat v8 E33 Hv8) | cbn; lia | cbn; lia | replace (sp0 - 2240 + 80) with (sp0 - 2144 - 16) by lia; exact D16]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [exact (EX 37%nat IO_RET E37 ltac:(unfold IO_RET; lia)) | unfold IO_RET; cbn; lia | cbn; lia | replace (sp0 - 2240 + 88) with (sp0 - 2144 - 8) by lia; exact D8]|].
apply Forall_nil. }
unfold memS. change (skipn 1 ([stkS; img_piece 0x2011e 8; img_piece 0x10330 (0x10398 - 0x10330)] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells)))
with ([img_piece 0x2011e 8; img_piece 0x10330 (0x10398 - 0x10330)] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells)).
rewrite <- !app_assoc. apply Forall_app. split.
{ apply Forall_cons; [apply (img_piece_ok _ E 0x1cd1e (0x20b7c - 0x1cd1e)); [exact HIMG | unfold img_ro_chunks; cbn; tauto | lia | lia | lia]|].
apply Forall_cons; [apply (img_piece_ok _ E 0x10330 (0x10398 - 0x10330)); [exact HIMG | unfold img_ro_chunks; cbn; tauto | lia | lia | lia]|]. apply Forall_nil. }
apply Forall_app. split.
{ rewrite !map_app. apply Forall_app. split; [exact (AE2y.icpt_rodata_ok B TB ly S H mem E (proj1 HAR))|].
apply Forall_app. split; [exact (rodata_ok B TB st_const ly S H mem E (st_const_chk ly) (proj1 HAR))|].
exact (cells_region_ok _ E st_cells HSTC). }
apply Forall_app. split.
{ unfold canR. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_canary, A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ 0 0x9ec38 8 (SLit 0x5f8fd0) 0x5f8fd0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hcan1]. }
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ 0 0x5f8fd0 8 (SOff 32 0) cval); [exact (EX 32%nat cval E32 Hcv) | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hcan2]. } }
apply Forall_app. split.
{ unfold envO. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; unfold A_threaded, A_need_locks, A_ofl_lock; rewrite ?HO.
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ 0 0x5f9221 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Henv0]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ 0 0x5f9223 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Henv1]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ 0 0x5f9680 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Henv2]. }
{ split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; replace o with (A_ofl_head + (o - 0x5f9688)) by (rewrite HO; lia); apply WOFL; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E _ 0 0x5f9688 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l]. rewrite <- HO. exact Hhead. } }
apply Forall_cons; [|apply Forall_nil].
unfold blkC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E8.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply AE2y.apresent_writable; apply HBpres; lia|].
apply Forall_forall. intros c Hc. rewrite forallb_forall in ZSH. specialize (ZSH c Hc).
destruct c as [o [n e| | |]]; try discriminate ZSH. destruct e as [z| | | | | | | | | |]; try discriminate ZSH. destruct z; try discriminate ZSH.
apply andb_prop in ZSH as [ZSH Zn]. apply andb_prop in ZSH as [Zo Zhi]. apply Z.leb_le in Zo. apply Z.leb_le in Zhi. apply Z.leb_le in Zn.
eapply (chunk_ok_val tfibsegs E _ f o n (SLit 0) 0); [reflexivity | split; [lia | apply Z.pow_pos_nonneg; lia] | exact Zn |].
apply val_mem_zero. intros i Hi. rewrite N_nat_Z in Hi. replace (f + o + i) with (f + (o + i)) by lia. rewrite <- (Z.add_comm (o + i) f), (Z.add_comm (o + i) f). apply HZB. lia.
- apply pairwise_disjoint_of_extents. unfold memC, memS, stkC, stkS, img_piece, st_cells, st_const, icpt_rodata, canR, envO, blkC, ro_region, extent_of_region.
cbn [skipn map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E8.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_WB, A_GOT_canary, A_canary, A_threaded, A_need_locks, A_ofl_lock, A_ofl_head, FO_WINC, TFIB_IMG_LO, TFIB_IMG_END in *.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HBam. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsC]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2, E8, E9.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. pose proof (u64_range fd) as Hfdu. repeat split; try lia; [replace (sp0 - 2240) with (sp0 + (-140) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16 | apply Z.mod_1_r]. }
assert (WIN : forall E' rs a, windows rs = WINSC -> bv_unsigned (ew E' 2) = sp0 - 2240 -> bv_unsigned (ew E' 8) = f -> in_wrange E' rs a ->
(sp0 - 2240 - 2208 <= a < sp0 - 2144) \/ oflW a \/ blkW a).
{ intros E' rs a HWl X2 X8 Hin. destruct (in_wrange_windows E' rs a Hin) as (bw & lo & hi & Ht & Hr). rewrite HWl in Ht. unfold WINSC in Ht. cbn [In] in Ht.
unfold oflW, blkW. rewrite HO.
repeat (destruct Ht as [Et | Ht]; [injection Et as <- <- <-; cbn [base_val] in Hr; rewrite ?X2, ?X8 in Hr; lia|]). destruct Ht. }
pose proof wins_C as [WL1 WL2].
unfold cfg_at. change (w64 FO_MEMSET_RA) with (Z_to_bv 64 FO_MEMSET_RA).
eapply SRr_bind; [exact (fo_phase_g W E ssC eC1 _ (mkst regsC (Z_to_bv 64 FO_MEMSET_RA) mem (seg_rom tfibsegs)) md HS1 r_C1)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2 & GR2). cbn [ms_mem mkst] in HF2, GR2. clear HFr2.
set (md2 := with_vm_backing (m_vm_lazy md) mat2 md) in *.
assert (MF2 : same_but_materialized md md2) by (subst md2; apply with_vm_backing_same).
pose proof shapeC1_ok as Hsh. unfold shapeC1 in Hsh.
apply andb_prop in Hsh as [Hsh Hat]. apply andb_prop in Hsh as [Hsh Hsk]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10].
apply andb_prop in Hsh as [Hsh R17]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv2 : ss_resv eC1 = None) by (destruct (ss_resv eC1); [discriminate | reflexivity]).
destruct (st_ok_ecall_shape_r tfibsegs H E eC1 ms2 HS2 Hresv2) as (regs2 & mem2 & Hms2 & Hregs2 & Hmemok2 & HG2).
assert (Hmm2 : ms_mem ms2 = mem2) by (rewrite Hms2; reflexivity). rewrite Hmm2 in HF2, GR2.
assert (MEQ2 : forall z : word, ~ ((sp0 - 2240 - 2208 <= bv_unsigned z < sp0 - 2144) \/ oflW (bv_unsigned z) \/ blkW (bv_unsigned z)) -> mem2 z = mem z).
{ intros z Hz. apply (HF2 z). intros Hin. exact (Hz (WIN E _ _ WL1 E2 E8 Hin)). }
clear HF2.
assert (RD2 : forall (r : bv 5) v, reg_is eC1 (bv_unsigned r) v = true -> getr regs2 r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply Hregs2. }
assert (Q2_17 : bv_unsigned (getr regs2 17) = 29) by (rewrite (RD2 17%bv (SLit 29) R17); reflexivity).
assert (Q2_10 : getr regs2 10 = fd) by (rewrite (RD2 10%bv _ R10); cbn [sv_denot]; rewrite E9, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (Q2_11 : getr regs2 11 = w64 0x5413) by (rewrite (RD2 11%bv _ R11); reflexivity).
unfold skelsC in Hsk. apply andb_prop in Hsk as [Hlen Hsk]. destruct (ss_mem eC1) as [|r0 rest] eqn:Hmem; [discriminate Hsk|].
apply andb_prop in Hsk as [K0 Hsk]. apply skel_is_sound in K0 as (K0a & K0lo & K0hi & K0b & K0c). rewrite FW in K0b, K0lo.
destruct (nth_error rest 20) as [ro|] eqn:Hro; [|discriminate Hsk]. destruct (nth_error rest 21) as [rb|] eqn:Hrb; [|discriminate Hsk].
apply andb_prop in Hsk as [Jo Jb]. apply skel_is_sound in Jo as (Joa & Jolo & Johi & Job & Joc). apply skel_is_sound in Jb as (Jba & Jblo & Jbhi & Jbb & Jbc).
assert (PRS2b : forall a, f <= a < f + 1264 -> apresent H mem2 a).
{ intros a Ha. apply (mem_ok_window_apresent H E mem2 _ 22 rb a Hmemok2 ltac:(rewrite ?Hmem; exact Hrb)); [| unfold AF0x.off_img; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia].
rewrite Jba, Jbb, Jbc. cbn [base_val]. rewrite E8. lia. }
assert (PRS2s : forall a, sp0 - 2240 - 2208 <= a < sp0 - 2144 -> apresent H mem2 a).
{ intros a Ha. apply (mem_ok_window_apresent H E mem2 _ 0 r0 a Hmemok2 ltac:(rewrite ?Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite K0a, K0b, K0c. cbn [base_val]. rewrite E2. lia. }
set (Wr2 := fun a => (sp0 - 2240 - 2208 <= a < sp0 - 2144) \/ oflW a \/ blkW a).
assert (Wr2d : forall a, Wr2 a \/ ~ Wr2 a) by (intros a; subst Wr2; cbn beta; unfold oflW, blkW; lia).
assert (Wr2i : forall a, Wr2 a -> stackC a \/ oflW a \/ blkW a) by (intros a Ha; subst Wr2; cbn beta in Ha; unfold stackC; destruct Ha as [Ha|Ha]; [left; lia | tauto]).
assert (Wr2p : forall a, Wr2 a -> ~ oflW a -> apresent H mem2 a).
{ intros a Ha Hof. subst Wr2. cbn beta in Ha. destruct Ha as [Hs | [Hx | Hb]]; [exact (PRS2s a Hs) | exfalso; exact (Hof Hx) | apply PRS2b; unfold blkW in Hb; exact Hb]. }
destruct (frameC mem mem2 md md2 Wr2 HAR Wr2d Wr2i MEQ2 Wr2p (md_frame_sbm _ _ MF2)) as (AV2 & PM2 & HAR2).
subst Wr2. cbv beta in AV2. clear Wr2d Wr2i Wr2p.
pose proof (same_but_materialized_frame md md2 MF2) as (_ & V02 & Z02 & _ & _ & _ & _ & _ & FD02 & _ & _ & FS02 & _).
rewrite Hms2. apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
destruct (node_ioctl_winsz_lazy tfibsegs (w_H W) (w_A W) regs2 (Z_to_bv 64 (ss_pc eC1)) mem2 (seg_rom tfibsegs) md2 fd fde HAI Q2_17 Q2_10
ltac:(apply Syscall.fd32_id; lia) ltac:(rewrite FD02; exact HFDL) Hfde ltac:(rewrite Q2_11; vm_compute; reflexivity)) as [Hnode HAI3].
apply (SRr_node tfibsegs W _ unit _ tt _ Hnode); [intros [] _; cbn [cfg_model]; exact HAI3|]. intros [].
assert (HS3 : st_ok tfibsegs E (resumeC2 eC1) (restrict H (mkst (regupd regs2 10 (errno_ret ENOTTY)) (v_addi (Z_to_bv 64 (ss_pc eC1)) 4) mem2 (seg_rom tfibsegs)))).
{ unfold resumeC2. rewrite restrict_mkst_fx. apply (st_ok_resume_sv tfibsegs E eC1 regs2 (mrestrict H mem2) (SLit (2 ^ 64 - 25)) (errno_ret ENOTTY) Hregs2 ltac:(rewrite Hmem; exact Hmemok2) HG2).
unfold errno_ret, ENOTTY. apply bv_eq. reflexivity. }
eapply SRr_bind; [exact (fo_phase_g W E (resumeC2 eC1) eC2 _ (mkst (regupd regs2 10 (errno_ret ENOTTY)) (v_addi (Z_to_bv 64 (ss_pc eC1)) 4) mem2 (seg_rom tfibsegs)) md2 HS3 r_C2)|].
intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4 & GR4). cbn [ms_mem mkst] in HF4, GR4. clear HFr4.
set (md4 := with_vm_backing (m_vm_lazy md2) mat4 md2) in *.
assert (MF4 : same_but_materialized md2 md4) by (subst md4; apply with_vm_backing_same).
pose proof (same_but_materialized_frame md2 md4 MF4) as (_ & V24 & Z24 & _ & _ & _ & _ & _ & FD24 & _ & _ & FS24 & _).
pose proof shapeC2_ok as Hsr. unfold shapeC2 in Hsr.
apply andb_prop in Hsr as [Hsr Hsk4]. apply andb_prop in Hsr as [Hsr Hofl4]. apply andb_prop in Hsr as [Hsr HC4]. apply andb_prop in Hsr as [Hsr HK4].
apply andb_prop in Hsr as [Hsr Z19]. apply andb_prop in Hsr as [Hsr Z18]. apply andb_prop in Hsr as [Hsr Z9]. apply andb_prop in Hsr as [Hsr Z8].
apply andb_prop in Hsr as [Hsr Z2]. apply andb_prop in Hsr as [Hsr Z1]. apply andb_prop in Hsr as [Hsr Z10].
apply andb_prop in Hsr as [Hpc4 Hrv4]. apply Z.eqb_eq in Hpc4.
assert (Hresv4 : ss_resv eC2 = None) by (destruct (ss_resv eC2); [discriminate | reflexivity]).
unfold skelsC in Hsk4. apply andb_prop in Hsk4 as [Hlen4 Hsk4]. destruct (ss_mem eC2) as [|q0 qrest] eqn:Hmem4; [discriminate Hsk4|].
apply andb_prop in Hsk4 as [J0 Hsk4].
destruct (nth_error qrest 20) as [qo|] eqn:Hqo; [|discriminate Hsk4]. destruct (nth_error qrest 21) as [qb|] eqn:Hqb; [|discriminate Hsk4].
apply andb_prop in Hsk4 as [J1 J2].
apply skel_is_sound in J0 as (J0a & J0lo & J0hi & J0b & J0c). apply skel_is_sound in J1 as (J1a & J1lo & J1hi & J1b & J1c). apply skel_is_sound in J2 as (J2a & J2lo & J2hi & J2b & J2c).
rewrite FW in J0b, J0lo.
assert (MEQ4 : forall z : word, ~ ((sp0 - 2240 - 2208 <= bv_unsigned z < sp0 - 2144) \/ oflW (bv_unsigned z) \/ blkW (bv_unsigned z)) -> ms_mem ms4 z = mem2 z).
{ intros z Hz. apply (HF4 z). intros Hin. exact (Hz (WIN E _ _ WL2 E2 E8 Hin)). }
clear HF4.
assert (RD4 : forall (r : bv 5) v, reg_is eC2 (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E eC2 ms4 r HS4). }
set (regs4 := ms_regs ms4) in *.
assert (PRS4s : forall a, sp0 - 2240 - 2208 <= a < sp0 - 2144 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E eC2 ms4 0 q0 a HS4 ltac:(rewrite ?Hmem4; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite J0a, J0b, J0c. cbn [base_val]. rewrite E2. lia. }
assert (PRS4b : forall a, f <= a < f + 1264 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E eC2 ms4 22 qb a HS4 ltac:(rewrite ?Hmem4; exact Hqb)); [| unfold AF0x.off_img; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia].
rewrite J2a, J2b, J2c. cbn [base_val]. rewrite E8. lia. }
set (Wr4 := fun a => (sp0 - 2240 - 2208 <= a < sp0 - 2144) \/ oflW a \/ blkW a).
assert (Wr4d : forall a, Wr4 a \/ ~ Wr4 a) by (intros a; subst Wr4; cbn beta; unfold oflW, blkW; lia).
assert (Wr4i : forall a, Wr4 a -> stackC a \/ oflW a \/ blkW a) by (intros a Ha; subst Wr4; cbn beta in Ha; unfold stackC; destruct Ha as [Ha|Ha]; [left; lia | tauto]).
assert (Wr4p : forall a, Wr4 a -> ~ oflW a -> apresent H (ms_mem ms4) a).
{ intros a Ha Hof. subst Wr4. cbn beta in Ha. destruct Ha as [Hs | [Hx | Hb]]; [exact (PRS4s a Hs) | exfalso; exact (Hof Hx) | apply PRS4b; unfold blkW in Hb; exact Hb]. }
destruct (frameC mem2 (ms_mem ms4) md2 md4 Wr4 HAR2 Wr4d Wr4i MEQ4 Wr4p (md_frame_sbm _ _ MF4)) as (AV4 & PM4 & HAR4).
subst Wr4. cbv beta in AV4. clear Wr4d Wr4i Wr4p.
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS4 eq_refl) as Hshape4. rewrite Hpc4 in Hshape4. fold regs4 in Hshape4.
assert (P4_1 : getr regs4 1 = w64 IO_RET) by (rewrite (RD4 1%bv _ Z1); exact (EX 37%nat IO_RET E37 ltac:(unfold IO_RET; lia))).
assert (P4_2 : getr regs4 2 = w64 (sp0 - 2144)) by (rewrite (RD4 2%bv _ Z2); cbn [sv_denot]; rewrite E2; unfold w64; f_equal; lia).
assert (P4_10 : getr regs4 10 = w64 f) by (rewrite (RD4 10%bv _ Z10); cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity).
assert (R4sp : spZ regs4 = sp0 - 2144) by (unfold spZ; rewrite P4_2; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ eapply (SRr_ret_at tfibsegs tbl_fo tbl_fo_ok Hwx W E eC2 ms4 md4
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms4) (v_jalr (getr (ms_regs ms4) 1) 0) (ms_mem ms4) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md4) mat' md4)));
[exact HS4 | exact Hresv4 | rewrite Hpc4; vm_compute; reflexivity | intros mat'; split; [reflexivity | exists mat'; reflexivity]]. }
intros W5 c5 _ (-> & mat5 & ->).
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4). fold regs4.
assert (MF5 : same_but_materialized md4 md5) by (subst md5; apply with_vm_backing_same).
rewrite P4_1, (AE2y.ret_ok_lit IO_RET ltac:(unfold IO_RET; lia) eq_refl).
assert (MBtop : forall a, 0 <= a < 2 ^ 64 -> sp0 - 2144 <= a < sp0 -> mbyte tfibsegs (mrestrict H (ms_mem ms4)) a = mbyte tfibsegs m0 a).
{ intros a Hr Ha. unfold oflW, blkW in AV4, AV2. rewrite HO in AV4, AV2. apply AE2y.mbyte_of_aview. rewrite AV4 by lia. apply AV2; lia. }
set (v := map (fun p : Z * Z => bv_unsigned (getr regs (Z_to_bv 5 (fst p)))) SAVEDF).
assert (HCv : forall j, (j < 8)%nat -> val_mem tfibsegs (mrestrict H (ms_mem ms4)) (spZ regs4 + 2136 - 8 * Z.of_nat j) 8 (nth j v 0)).
{ intros j Hj. rewrite R4sp. apply (val_mem_frame tfibsegs m0); [intros x Hx; apply MBtop; lia|].
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [| | | | | | | | lia]; subst v; cbn [map fst nth SAVEDF].
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 0) with (sp0 + -8) by lia. exact (QS 0%nat 1 (-8) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 1) with (sp0 + -16) by lia. exact (QS 1%nat 8 (-16) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 2) with (sp0 + -24) by lia. exact (QS 2%nat 9 (-24) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 3) with (sp0 + -32) by lia. exact (QS 3%nat 18 (-32) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 4) with (sp0 + -40) by lia. exact (QS 4%nat 19 (-40) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 5) with (sp0 + -48) by lia. exact (QS 5%nat 20 (-48) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 6) with (sp0 + -56) by lia. exact (QS 6%nat 21 (-56) eq_refl).
- replace (sp0 - 2144 + 2136 - 8 * Z.of_nat 7) with (sp0 + -64) by lia. exact (QS 7%nat 22 (-64) eq_refl). }
assert (Heven : bv_unsigned (getr regs 1) mod 2 = 0).
{ pose proof (u64_range (getr regs 1)) as Hu. pose proof (f_equal bv_unsigned Hra) as EQ. unfold v_jalr, jalr_tgtZ in EQ.
rewrite Z.add_0_r, Z_to_bv_unsigned in EQ.
assert (Hld : Z.land (bv_unsigned (getr regs 1)) (-2) = Z.shiftl (Z.shiftr (bv_unsigned (getr regs 1)) 1) 1).
{ change (-2) with (Z.lnot (Z.ones 1)). rewrite <- Z.ldiff_land. apply Z.ldiff_ones_r. lia. }
rewrite Hld, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 in EQ by lia. change (2 ^ 1) with 2 in EQ.
unfold bv_wrap in EQ. change (bv_modulus 64) with (2 ^ 64) in EQ.
pose proof (Z.mul_div_le (bv_unsigned (getr regs 1)) 2 ltac:(lia)) as Hm1. assert (Hm2 : 0 <= bv_unsigned (getr regs 1) / 2) by (apply Z.div_pos; lia).
rewrite Z.mod_small in EQ by lia. rewrite <- EQ. apply Z_mod_mult. }
change (mkCfg (mkst regs4 (Z_to_bv 64 IO_RET) (ms_mem ms4) (seg_rom tfibsegs)) md5) with (cfg_at tfibsegs IO_RET regs4 (ms_mem ms4) md5).
eapply SRr_bind.
{ apply (iopen_tail W regs4 (ms_mem ms4) md5 v eq_refl); rewrite ?R4sp; unfold IO_FRAME; try lia.
- subst v. cbn [map fst SAVEDF]. repeat (apply Forall_cons; [apply u64_range|]). apply Forall_nil.
- subst v. cbn [map fst nth SAVEDF]. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). exact Heven.
- replace (sp0 - 2144) with (sp0 + (-134) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- intros j Hj. fold H. rewrite <- R4sp. exact (HCv j Hj). }
intros W6 c6 _ (-> & regs6 & md6 & -> & MF6 & T10 & T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & TK).
pose proof (st_ok_mem_ok tfibsegs E eC2 _ HS4) as (_ & Hrs4 & _). cbn [ms_mem restrict] in Hrs4. rewrite Hmem4 in Hrs4.
pose proof (proj1 (Forall_forall _ _) Hrs4 qb ltac:(right; eapply nth_error_In; exact Hqb)) as (_ & _ & _ & HcsB). rewrite J2a in HcsB. cbn [base_val] in HcsB. rewrite E8 in HcsB.
assert (HCB : forall off n e, In (off, n, e) hdrC -> exists c, In c (r_chunks qb) /\ c = YP09.mkChunk off (CVal n e)).
{ intros off n e Hin. rewrite forallb_forall in HC4. specialize (HC4 _ Hin). cbn [fst snd] in HC4. unfold has_chunk in HC4. rewrite Hmem4 in HC4.
change (nth_error (q0 :: qrest) 22) with (nth_error qrest 21) in HC4. rewrite Hqb in HC4. apply existsb_exists in HC4 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. exists c. split; [exact Hc | exact Hcc]. }
assert (CELLB : forall off n e z, In (off, n, e) hdrC -> sv_denot E e = Z_to_bv 64 z -> 0 <= z < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms4)) (f + off) (N.to_nat n) z).
{ intros off n e z Hin Hd Hz Hn. destruct (HCB off n e Hin) as (c & Hc & ->). exact (val_of_chunk_ok tfibsegs E _ _ off n e z (proj1 (Forall_forall _ _) HcsB _ Hc) Hd Hz Hn). }
assert (CELLM : forall off n e z, In (off, n, e) hdrC -> bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n) = z -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms4)) (f + off) (N.to_nat n) z).
{ intros off n e z Hin Hd Hn. destruct (HCB off n e Hin) as (c & Hc & ->). exact (val_of_chunk_mod E _ _ off n e z (proj1 (Forall_forall _ _) HcsB _ Hc) Hd Hn). }
assert (Z0 : forall off n, In (off, n, SLit 0) hdrC -> Z.of_N n <= 8 -> val_mem tfibsegs (mrestrict H (ms_mem ms4)) (f + off) (N.to_nat n) 0).
{ intros off n Hin Hn. apply (CELLB off n (SLit 0) 0 Hin eq_refl); [split; [lia | apply Z.pow_pos_nonneg; lia] | exact Hn]. }
assert (HOFL4 : val_mem tfibsegs (mrestrict H (ms_mem ms4)) A_ofl_head 8 f).
{ unfold has_chunk in Hofl4. rewrite Hmem4 in Hofl4. change (nth_error (q0 :: qrest) 21) with (nth_error qrest 20) in Hofl4. rewrite Hqo in Hofl4.
apply existsb_exists in Hofl4 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (proj1 (Forall_forall _ _) Hrs4 qo ltac:(right; eapply nth_error_In; exact Hqo)) as (_ & _ & _ & Hcs). rewrite J1a in Hcs. cbn [base_val] in Hcs.
rewrite <- (Z.add_0_l A_ofl_head).
apply (val_of_chunk_ok tfibsegs E _ _ A_ofl_head 8 (SOff 8 0) f (proj1 (Forall_forall _ _) Hcs _ Hc)); [cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity | cbn; lia | cbn; lia]. }
pose proof (same_but_materialized_frame md4 md5 MF5) as (_ & V45 & Z45 & _ & _ & _ & _ & _ & FD45 & _ & _ & FS45 & _).
pose proof (same_but_materialized_frame md5 md6 MF6) as (_ & V56 & Z56 & _ & _ & _ & _ & _ & FD56 & _ & _ & FS56 & _).
assert (MF46 : same_but_materialized md4 md6) by (eapply same_but_materialized_trans; [exact MF5 | exact MF6]).
assert (Hv0 : nth 0 v 0 = bv_unsigned (getr regs 1)) by (subst v; cbn [map fst nth SAVEDF]; replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity); reflexivity).
apply SRr_ret. split; [reflexivity|]. exists regs6, (ms_mem ms4), md6.
split; [rewrite Hv0; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ apply (al_frame _ _ LAWS ly S W (ms_mem ms4) md4 (ms_mem ms4) md6 HAR4); [intros a Hr Hown; reflexivity | intros a Hv'; exact Hv' | exact (eq_trans V56 V45) | exact (eq_trans Z56 Z45) | | intros a _ _; reflexivity].
apply (same_but_materialized_frame md4 _ MF46). }
split.
{ intros rr Hr. unfold acallee_saved in Hr.
assert (KK : forall r, In r [3; 4; 23; 24; 25; 26; 27] -> getr regs6 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hin. cbn [In] in Hin. assert (Hr' : 0 <= r < 32) by lia.
assert (Hur : bv_unsigned (Z_to_bv 5 r) = r) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
rewrite (TK r) by (unfold KEPTT; cbn [In]; lia).
rewrite forallb_forall in HK4. pose proof (HK4 r ltac:(unfold KEPTC; cbn [In]; lia)) as Hk. cbn beta in Hk.
rewrite (RD4 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)) by (rewrite Hur; exact Hk).
cbn [sv_denot]. rewrite (EregC (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Hur; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply (CK r). unfold AE2g.KEPTF. cbn [In]. lia. }
assert (VV : forall j (r : Z), (j < 8)%nat -> fst (nth j SAVEDF (0, 0)) = r -> w64 (nth j v 0) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj Hrz. subst v. rewrite <- Hrz.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [| | | | | | | | lia]; cbn [map fst nth SAVEDF]; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity. }
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T2, R4sp. unfold IO_FRAME. replace (sp0 - 2144 + 2144) with sp0 by lia.
unfold sp0, spZ, w64. apply Z_to_bv_bv_unsigned.
* exact (KK 3 ltac:(INL)).
* exact (KK 4 ltac:(INL)).
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T8. exact (VV 1%nat 8 ltac:(lia) eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T9. exact (VV 2%nat 9 ltac:(lia) eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ (rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27)) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | Hc]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T18. exact (VV 3%nat 18 ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T19. exact (VV 4%nat 19 ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T20. exact (VV 5%nat 20 ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T21. exact (VV 6%nat 21 ltac:(lia) eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T22. exact (VV 7%nat 22 ltac:(lia) eq_refl).
-- apply KK. cbn [In]. lia. }
split; [rewrite T10; exact P4_10|].
split; [rewrite V56, V45, V24; exact V02|].
split; [rewrite Z56, Z45, Z24; exact Z02|].
split.
{ apply (same_io_trans3 md md4 md6); [| exact (same_io_sbm _ _ MF46)]. apply (same_io_trans3 md md2 md4); [exact (same_io_sbm _ _ MF2) | exact (same_io_sbm _ _ MF4)]. }
split.
{ eapply os_kept_trans; [exact (os_kept_sbm _ _ MF2)|]. eapply os_kept_trans; [exact (os_kept_sbm _ _ MF4) | exact (os_kept_sbm _ _ MF46)]. }
split; [eapply same_but_materialized_trans; [exact MF2|]; eapply same_but_materialized_trans; [exact MF4 | exact MF46]|].
split; [rewrite FD56, FD45, FD24; exact FD02|].
split; [rewrite FS56, FS45, FS24; exact FS02|].
split.
{
pose proof (u64_range fd) as Hfdu.
assert (N8 : Z.of_N 8 <= 8) by (cbn; lia). assert (N4 : Z.of_N 4 <= 8) by (cbn; lia).
split.
- unfold file_static. cbn [ak_close ak_read ak_write ak_seek tfib_K].
split; [lia|].
split; [apply (CELLB 0 4%N (SLit 4) 4 ltac:(unfold hdrC; INL) eq_refl ltac:(cbn; lia) N4)|].
split; [exact (Z0 8 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 16 8%N ltac:(unfold hdrC; INL) N8)|].
split; [apply (CELLB 24 8%N (SLit A_stdio_close) A_stdio_close ltac:(unfold hdrC; INL) eq_refl ltac:(unfold A_stdio_close; cbn; lia) N8)|].
split; [exact (Z0 48 8%N ltac:(unfold hdrC; INL) N8)|].
split; [apply (CELLB 64 8%N (SLit A_stdio_read) A_stdio_read ltac:(unfold hdrC; INL) eq_refl ltac:(unfold A_stdio_read; cbn; lia) N8)|].
split; [apply (CELLB 72 8%N (SLit A_stdio_write) A_stdio_write ltac:(unfold hdrC; INL) eq_refl ltac:(unfold A_stdio_write; cbn; lia) N8)|].
split; [apply (CELLB 80 8%N (SLit A_stdio_seek) A_stdio_seek ltac:(unfold hdrC; INL) eq_refl ltac:(unfold A_stdio_seek; cbn; lia) N8)|].
split; [apply (CELLB 88 8%N (SOff 8 240) (f + FILE_BUF_OFF) ltac:(unfold hdrC; INL)); [cbn [sv_denot]; rewrite E8; reflexivity | unfold FILE_BUF_OFF; cbn; lia | exact N8]|].
split; [apply (CELLB 96 8%N (SLit 1024) FILE_BUFSIZ ltac:(unfold hdrC; INL) eq_refl ltac:(unfold FILE_BUFSIZ; cbn; lia) N8)|].
split; [exact (Z0 104 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 112 8%N ltac:(unfold hdrC; INL) N8)|].
split; [apply (CELLB 120 4%N (SOff 9 0) (bv_unsigned fd) ltac:(unfold hdrC; INL)); [cbn [sv_denot]; rewrite E9, Z.add_0_r; reflexivity | cbn; lia | exact N4]|].
split; [exact (Z0 124 4%N ltac:(unfold hdrC; INL) N4)|]. split; [exact (Z0 128 8%N ltac:(unfold hdrC; INL) N8)|].
split; [apply (CELLM 140 4%N (SLit 18446744073709551615) U32M1 ltac:(unfold hdrC; INL)); [vm_compute; reflexivity | exact N4]|].
split; [apply (CELLM 144 4%N (SLit 18446744073709551615) U32M1 ltac:(unfold hdrC; INL)); [vm_compute; reflexivity | exact N4]|].
split; [exact (Z0 152 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 160 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 168 8%N ltac:(unfold hdrC; INL) N8)|].
split; [exact (Z0 176 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 184 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 192 8%N ltac:(unfold hdrC; INL) N8)|].
split; [exact (Z0 200 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 208 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 216 8%N ltac:(unfold hdrC; INL) N8)|].
exact (Z0 224 8%N ltac:(unfold hdrC; INL) N8).
- left. split; [reflexivity|]. split; [exact (Z0 32 8%N ltac:(unfold hdrC; INL) N8)|]. split; [exact (Z0 40 8%N ltac:(unfold hdrC; INL) N8)|].
split; [exact (Z0 56 8%N ltac:(unfold hdrC; INL) N8) | exact (Z0 136 4%N ltac:(unfold hdrC; INL) N4)]. }
split; [exact HOFL4|].
split.
{ intros a Hr Hs Hb Hofl.
rewrite AV4; [| exact Hr | unfold stackC in Hs; intros [X|[X|X]]; [lia | exact (Hofl X) | exact (Hb X)]].
apply AV2; [exact Hr | unfold stackC in Hs; intros [X|[X|X]]; [lia | exact (Hofl X) | exact (Hb X)]]. }
split.
{ intros a Hs. unfold stackC in Hs. unfold oflW, blkW in PM4, PM2. rewrite HO in PM4, PM2.
destruct (Z_lt_le_dec a (sp0 - 2240 - 2208)) as [L|L]; [| destruct (Z_lt_le_dec a (sp0 - 2144)) as [L2|L2]; [apply PRS4s; lia|]].
- apply PM4; [lia | lia |]. apply PM2; [lia | lia |]. apply Hpres. lia.
- apply PM4; [lia | lia |]. apply PM2; [lia | lia |]. apply Hpres. lia. }
intros a Hp. eapply fo_apresent_grows; [exact GR4|]. eapply fo_apresent_grows; [exact GR2 | exact Hp].
Qed.
End h.
End d.
