(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the tables of __asan_stack_malloc_7 (0x40244) of plugin-hostd/fuzz_command's ASan build,
   from cgif_rgb_fuzzer's lib/YF9a.v in the form of this tree's class-5 walk lib/A/Rt/RtSM5T.v: the code addresses
   (FS_ENTRY 0x40244, FS_LOOP 0x402e0, FS_FOUND 0x4032c, FS_SDFF 0x40360, FS_MSRET 0x40384), the walk table (the class-7
   body, 95 words, the TLS path and MemToShadow ranges of RtSM5T and PoisonShadow 0x59824, 233 words, over A/AE34.v's
   tbl_icpt) and the read-only cells read from fuzz_command.asan, each with the value Tfib_const states for it (fs_cv);
   TP, TSD and the thread cells from A/AF0m.v; the generic lemmas of RtSM5T; module paths. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AB1w AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* Measured on the pinned fuzz_command.asan: __asan_stack_malloc_7 is 95 instructions, 0x40244..0x403bc, laid out as
   cgif_rgb's class-7 entry 0x3d1d8 (every phase address below is the donor's plus 0x306c). Its frame is 48 bytes
   (ra, s0, s1, s2, s3); s1 keeps the size a0, s2 the fake stack F and then the frame, s3 the stack-size log 20.
   The probe loop at 0x402e0: hint in a2, mask 127 in a5, flag base F + 0x8f00 in a4, flag address in a3, index in a7.
   After the frame is found: sd s0,24(frame); sd a3,8184(frame) (the flag pointer); jal MemToShadow 0x40410 (result
   unused); PoisonShadow(frame, size, 0) at 0x59824, which tail-jumps through GOT 0xa6410 -> 0xa82b0 -> musl memset
   0x9ef40 with ra = 0x40384 once the count n / 8 is below common_flags()->clear_shadow_mmap_threshold
   (0x142be8 + 120, value 2^64 - 1); then a0 = frame and return. *)

(* The value Tfib_const (the AR invariant's constant cells) gives an address; -1 when it has no such cell, which makes
   rodata_chk fail. *)
Definition fs_cv_e (e : aexp) : Z :=
match cell_lookup (Tfib_const_sym ++ Tfib_const_abs ++ Tfib_const_shadow) e with
| Some (ACell _ _ (AV (ANum v))) => v
| _ => -1
end.
Definition fs_cv (a : Z) : Z := fs_cv_e (ANum a).
Definition fs_ro_vals (l : list (Z * Z * list (Z * BinNums.N))) : list (Z * Z * list (Z * BinNums.N * Z)) :=
map (fun r => (fst (fst r), snd (fst r), map (fun c => (fst c, snd c, fs_cv (fst (fst r) + fst c))) (snd r))) l.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition CID : Z := 7.
Definition FS_ENTRY : Z := 0x40244.
Definition FS_LOOP : Z := 0x402e0.
Definition FS_FOUND : Z := 0x4032c.
Definition FS_SDFF : Z := 0x40360.
Definition FS_MSRET : Z := 0x40384.
Definition FS_WIN : Z := 224.
Definition FS_N : Z := 128.
Definition FS_FLOFF : Z := 0x8f00.
Definition FS_B : Z := 8192.
Definition FS_FROFF : Z := 0x709000.
Definition FS_HOFF : Z := 56.
Definition TP : Z := Eval compute in TFIB_TP.
Definition TSD : Z := Eval compute in TFIB_TSD.
Definition T48 : Z := Eval vm_compute in fs_cv_e (AT 48).
Definition T56 : Z := Eval vm_compute in fs_cv_e (AT 56).
(* The class-7 body (95 words from 0x40244), the callee ranges of the class-5 walk (the TLS trampoline's tail, the
   interceptor, musl __tls_get_addr, GetCurrentThread, AsanTSDGet, pthread_getspecific, DTLS_on_tls_get_addr, the
   fast path of MemToShadow 0x40410) and PoisonShadow 0x59824 up to its tail jump. *)
Definition fs_ranges : list (Z * nat) :=
(0x40244, 95%nat) :: [(0x67b00, 2%nat); (0x4b040, 31%nat); (0x9fbb8, 9%nat); (0x61e40, 8%nat); (0x5a98c, 6%nat);
(0xa0c6c, 7%nat); (0x6f554, 140%nat); (0x40410, 28%nat); (0x59824, 233%nat)].
Definition tbl_fs : ctable := Eval vm_compute in build_ranges fs_ranges tbl_icpt.
Lemma tbl_fs_eq : tbl_fs = build_ranges fs_ranges tbl_icpt. Proof. vm_cast_no_check (eq_refl tbl_fs). Qed.
Lemma tbl_fs_ok : table_ok tfibsegs tbl_fs.
Proof. rewrite tbl_fs_eq. apply build_ranges_ok; [vm_compute; repeat constructor; discriminate | exact tbl_icpt_ok]. Qed.
Lemma fs_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_fs FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_fs tbl_fs_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma fs_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_fs FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_fs tbl_fs_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
(* The cells the walk reads besides icpt_rodata: the image cells of the class-5 walk, the three thread-pointer cells, and
   the two PoisonShadow reads that icpt_rodata does not hold (GOT 0xa6410 -> the REAL(memset) slot 0xa82b0, and the
   threshold common_flags + 120), each with the value Tfib_const states for it. *)
Definition fsA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) := Eval vm_compute in
icpt_rodata ++ fs_ro_vals (
[(0xa70f0, 16, [(0, 8%N); (8, 8%N)]); (0xa81d8, 8, [(0, 8%N)]); (0xa63e0, 8, [(0, 8%N)]); (0x142c71, 1, [(0, 1%N)]);
(0xa6440, 8, [(0, 8%N)]); (0x140b58, 4, [(0, 4%N)]); (0xa7100, 8, [(0, 8%N)]); (0xb0920, 8, [(0, 1%N); (4, 4%N)])] ++
[(TP - 88, 8, [(0, 8%N)]); (TP - 8, 8, [(0, 8%N)]); (fs_cv (TP - 8) + 8, 8, [(0, 8%N)])] ++
[(0xa6410, 8, [(0, 8%N)]); (0x142c60, 8, [(0, 8%N)])]).
Lemma fsA_rodata_chk : forall ly, rodata_chk ly fsA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition aT : nat := 32. Definition aC : nat := 33. Definition aD : nat := 34. Definition aF : nat := 35. Definition aH : nat := 36.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- FS_WIN) 0 (- FS_WIN) 0 [].
Definition rTSD : YP09.region := YP09.mkRegion None TSD (TSD + 8) TSD TSD [YP09.mkChunk TSD (CVal 8 (SOff aC 0))].
Definition rTP0 : YP09.region := YP09.mkRegion None TP (TP + 8) TP TP [YP09.mkChunk TP (CVal 8 (SOff aF 0))].
Definition rTP8 : YP09.region := YP09.mkRegion None (TP + 8) (TP + 16) (TP + 8) (TP + 8) [YP09.mkChunk (TP + 8) (CVal 8 (SOff aD 0))].
Definition rT : YP09.region := YP09.mkRegion (Some aT) 48 64 48 48 [YP09.mkChunk 48 (CVal 8 (SLit T48)); YP09.mkChunk 56 (CVal 8 (SLit T56))].
Definition rC : YP09.region := YP09.mkRegion (Some aC) 152 160 152 152 [YP09.mkChunk 152 (CVal 8 (SOff aT 0))].
Definition rD : YP09.region := YP09.mkRegion (Some aD) 24 32 24 24 [YP09.mkChunk 24 (CVal 8 (SLit TP))].
Definition rF : YP09.region := YP09.mkRegion (Some aF) FS_HOFF 97 FS_HOFF (FS_HOFF + 8)
[YP09.mkChunk FS_HOFF (CVal 8 (SOff aH 0)); YP09.mkChunk 88 (CVal 8 (SLit 20)); YP09.mkChunk 96 (CVal 1 (SLit 0))].
Definition memA : smem := stkA :: rTSD :: rTP0 :: rTP8 :: rT :: rC :: rD :: rF :: map ro_region fsA_rodata.
Definition factsA : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + FS_WIN) kHighMemEnd 4);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12);
(aC, mkAF 4096 (CEIL_MAX - 256) 3);
(aD, mkAF 4096 (CEIL_MAX - 4096) 12);
(aF, mkAF 4096 (CEIL_MAX - kFakeStackSize) 12);
(aH, mkAF 0 (2^64 - 1) 0);
(10%nat, mkAF 8 FS_B 3)].
Definition regsA : list sv := Eval vm_compute in (firstn 4 sr_atoms ++ [SLit TP] ++ skipn 5 sr_atoms).
Definition ssA : sstate := mkSS FS_ENTRY regsA memA None (mkFacts factsA [] []).
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_fs FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_fs FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition eA : sstate := Eval vm_compute in fst (RUNTO FS_LOOP ssA).
Definition add_fact (ss : sstate) (n : nat) (f : afact) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Lemma st_ok_add_fact : forall E ss ms n lo hi,
st_ok tfibsegs E ss ms -> ss_resv ss = None -> lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfibsegs E (add_fact ss n (mkAF lo hi 0)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [assumption|]). split; [|split; assumption].
cbn [atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [exact Hr|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
Qed.
(* The frame atom carries 32-byte alignment (al2 5): PoisonShadow checks frame mod 8 = 0. *)
Lemma st_ok_add_fact5 : forall E ss ms n lo hi,
st_ok tfibsegs E ss ms -> ss_resv ss = None -> bv_unsigned (ew E n) mod 32 = 0 -> lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfibsegs E (add_fact ss n (mkAF lo hi 5)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hm Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [assumption|]). split; [|split; assumption].
cbn [atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [exact Hr|]. split; [change (2 ^ 5) with 32; exact Hm | lia].
Qed.
Definition aH2 : nat := 37. Definition aPOS : nat := 38. Definition aFLG : nat := 39. Definition aCNT : nat := 40. Definition aFF : nat := 41.
Definition rFLG : YP09.region := YP09.mkRegion (Some aFLG) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition rFF : YP09.region := YP09.mkRegion (Some aFF) 0 FS_B 0 FS_B [].
Definition updC1 : list (bv 5 * sv) := [((12%bv : bv 5), SOff aH2 0); ((17%bv : bv 5), SOff aPOS 0); ((13%bv : bv 5), SOff aFLG 0); ((5%bv : bv 5), SLit 0); ((10%bv : bv 5), SOff aCNT 0)].
(* rF, icpt_rodata (8-14), the common_flags slot 0xa63e0 (17), GOT 0xa6410 (26) and the threshold cell (27). *)
Definition idxC1 : list nat := [7; 8; 9; 10; 11; 12; 13; 14; 17; 26; 27]%nat.
Definition memC1 : smem := nth 0 (ss_mem eA) stkA :: rFLG :: map (fun i => nth i (ss_mem eA) stkA) idxC1.
Definition preC1 : sstate := add_fact (mkSS FS_FOUND (sr_sets (ss_regs eA) updC1) memC1 None (ss_facts eA)) aPOS (mkAF 0 (FS_N - 1) 0).
Definition ssC1 : sstate := Eval vm_compute in preC1.
Lemma ssC1_eq : preC1 = ssC1. Proof. vm_compute. reflexivity. Qed.
Definition eC1 : sstate := Eval vm_compute in fst (RUN ssC1).
Definition stC1 : run_status := Eval vm_compute in snd (RUN ssC1).
Definition s2C1 : sv := Eval vm_compute in RG eC1 18.
Definition ffLO (hi : bool) : Z := if hi then kHighMemBeg else 4096.
Definition ffHI (hi : bool) : Z := if hi then CEIL_MAX - FS_B else kLowShadowBeg - FS_B.
Definition memC2 : smem := nth 0 (ss_mem eC1) stkA :: rFF :: tl (ss_mem eC1).
Definition preC2 (hi : bool) : sstate := add_fact (mkSS (ss_pc eC1) (sr_sets (ss_regs eC1) [((18%bv : bv 5), SOff aFF 0)]) memC2 None (ss_facts eC1)) aFF (mkAF (ffLO hi) (ffHI hi) 5).
Definition ssC2H : sstate := Eval vm_compute in preC2 true.
Definition ssC2L : sstate := Eval vm_compute in preC2 false.
Definition ssC2 (hi : bool) : sstate := if hi then ssC2H else ssC2L.
Lemma ssC2_eq : forall hi, preC2 hi = ssC2 hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition eC2H : sstate := Eval vm_compute in fst (RUN ssC2H).
Definition stC2H : run_status := Eval vm_compute in snd (RUN ssC2H).
Definition eC2L : sstate := Eval vm_compute in fst (RUN ssC2L).
Definition stC2L : run_status := Eval vm_compute in snd (RUN ssC2L).
Definition eC2 (hi : bool) : sstate := if hi then eC2H else eC2L.
Definition stC2 (hi : bool) : run_status := if hi then stC2H else stC2L.
(* The run stops at PoisonShadow's threshold branch (count < 2^64 - 1), which the run cannot decide. *)
Definition cntC2 : sv := Eval vm_compute in match stC2H with RS_stopped (SR_branch _ a _) => a | _ => SLit 0 end.
Definition THR : Z := 18446744073709551615.
Definition ACOND (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition ssC2bH : sstate := Eval vm_compute in ACOND eC2H BC_LTU cntC2 (SLit THR).
Definition ssC2bL : sstate := Eval vm_compute in ACOND eC2L BC_LTU cntC2 (SLit THR).
Definition ssC2b (hi : bool) : sstate := if hi then ssC2bH else ssC2bL.
Lemma ssC2b_eq : forall hi, ACOND (eC2 hi) BC_LTU cntC2 (SLit THR) = ssC2b hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition eC2bH : sstate := Eval vm_compute in fst (RUN ssC2bH).
Definition stC2bH : run_status := Eval vm_compute in snd (RUN ssC2bH).
Definition eC2bL : sstate := Eval vm_compute in fst (RUN ssC2bL).
Definition stC2bL : run_status := Eval vm_compute in snd (RUN ssC2bL).
Definition eC2b (hi : bool) : sstate := if hi then eC2bH else eC2bL.
Definition stC2b (hi : bool) : run_status := if hi then stC2bH else stC2bL.
Definition a0C2 : sv := Eval vm_compute in RG eC2bH 10.
Definition a2C2 : sv := Eval vm_compute in RG eC2bH 12.
Definition CLOB : list (bv 5) := [11; 12; 13; 14; 15; 16]%bv.
Definition ssC3H : sstate := Eval vm_compute in ss_after_stretch eC2bH (ss_mem eC2bH) 43 CLOB FS_MSRET.
Definition ssC3L : sstate := Eval vm_compute in ss_after_stretch eC2bL (ss_mem eC2bL) 43 CLOB FS_MSRET.
Definition ssC3 (hi : bool) : sstate := if hi then ssC3H else ssC3L.
Lemma ssC3_eq : forall hi, ss_after_stretch (eC2b hi) (ss_mem (eC2b hi)) 43 CLOB FS_MSRET = ssC3 hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition eC3H : sstate := Eval vm_compute in fst (RUN ssC3H).
Definition stC3H : run_status := Eval vm_compute in snd (RUN ssC3H).
Definition eC3L : sstate := Eval vm_compute in fst (RUN ssC3L).
Definition stC3L : run_status := Eval vm_compute in snd (RUN ssC3L).
Definition eC3 (hi : bool) : sstate := if hi then eC3H else eC3L.
Definition stC3 (hi : bool) : run_status := if hi then stC3H else stC3L.
Definition FS_RET : Z := Eval vm_compute in ss_pc eC3H.
Lemma eC3_pc : forall hi, ss_pc (eC3 hi) = FS_RET. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma fetch_lit_fs : forall (p : word) (w : bv 32), clookup tbl_fs (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof. intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply tbl_fs_ok. exact H. Qed.
Lemma fs_frames_cid : fs_frames CID = FS_N. Proof. vm_compute. reflexivity. Qed.
Lemma land_mask_N : forall h, 0 <= h -> Z.land (h mod 2 ^ 64) (FS_N - 1) = h mod FS_N.
Proof.
intros h Hh. replace (FS_N - 1) with (Z.ones 7) by reflexivity. rewrite Z.land_ones by lia.
change FS_N with (2 ^ 7). rewrite <- (Z.mod_mod_divide h (2 ^ 64) (2 ^ 7)) by (first [lia | exists (2 ^ (64 - 7)); reflexivity]). reflexivity.
Qed.
Lemma v_and_mask : forall h, 0 <= h -> v_and (Z_to_bv 64 h) (Z_to_bv 64 (FS_N - 1)) = Z_to_bv 64 (h mod FS_N).
Proof.
intros h Hh. unfold v_and. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (FS_N - 1)) by (unfold FS_N; lia). rewrite land_mask_N by exact Hh. reflexivity.
Qed.
Lemma step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_and (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv. rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Lemma v_addiw_dec : forall c, 1 <= c < 2 ^ 31 -> v_addiw (Z_to_bv 64 c) (-1) = Z_to_bv 64 (c - 1).
Proof.
intros c Hc. unfold v_addiw. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296. f_equal.
change (2 ^ 31)%Z with 2147483648 in Hc. rewrite Z.mod_small by lia. lia.
Qed.
End e.
Ltac ftac := apply fetch_lit_fs; vm_compute; reflexivity.
Ltac steplb1 F0 D RD := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D | gr; imm_norm; rewrite v_addi_lit, Z.add_0_r; exact RD ]
| step_simpl ].
Ltac svand F0 D vv := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | val ]
| step_simpl ].
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma F_L0 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x0)) = Some (0x00f678b3%bv : bv 32). Proof. ftac. Qed.
Lemma D_L0 : decode_any (0x00f678b3%bv : bv 32) = Some (Op ALU_AND 17 12 15, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L4 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x4)) = Some (0x011706b3%bv : bv 32). Proof. ftac. Qed.
Lemma D_L4 : decode_any (0x011706b3%bv : bv 32) = Some (Op ALU_ADD 13 14 17, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L8 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x8)) = Some (0x0006c283%bv : bv 32). Proof. ftac. Qed.
Lemma D_L8 : decode_any (0x0006c283%bv : bv 32) = Some (Load SZ1 false 5 13 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_Lc : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0xc)) = Some (0x04028063%bv : bv 32). Proof. ftac. Qed.
Lemma D_Lc : decode_any (0x04028063%bv : bv 32) = Some (Branch BC_EQ 5 0 64, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L10 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x10)) = Some (0xfff5051b%bv : bv 32). Proof. ftac. Qed.
Lemma D_L10 : decode_any (0xfff5051b%bv : bv 32) = Some (OpImm32 10 10 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L14 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x14)) = Some (0x00160613%bv : bv 32). Proof. ftac. Qed.
Lemma D_L14 : decode_any (0x00160613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L18 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x18)) = Some (0xfe0514e3%bv : bv 32). Proof. ftac. Qed.
Lemma D_L18 : decode_any (0xfe0514e3%bv : bv 32) = Some (Branch BC_NE 10 0 8168, 4%Z). Proof. vm_refl_bv. Qed.
Section o.
Variables (live : list (Z * Z)) (FL : Z) (mem rom : word -> option byte).
Hypothesis HFL : 0 <= FL /\ FL + FS_N < 2 ^ 64.
Hypothesis Hflags : forall p, 0 <= p < FS_N -> rdn tfibsegs mem (Z_to_bv 64 (FL + p)) 1 = Some [Z_to_bv 8 (if mem_pos live CID p then 1 else 0)].
Definition lkeep (x : bv 5) : Prop := x <> 5%bv /\ x <> 10%bv /\ x <> 12%bv /\ x <> 13%bv /\ x <> 17%bv.
Definition lfin (regs : bvmap 5 word) (pc : word) (pos hint' : Z) : Prop :=
exists regs' c', msteps tfibsegs (mkst regs pc mem rom) (mkst regs' (Z_to_bv 64 FS_FOUND) mem rom)
/\ getr regs' 12 = Z_to_bv 64 (hint' - 1) /\ getr regs' 17 = Z_to_bv 64 pos /\ getr regs' 13 = Z_to_bv 64 (FL + pos)
/\ getr regs' 5 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 c' /\ 1 <= c' <= FS_N
/\ forall x, lkeep x -> getr regs' x = getr regs x.
Lemma lfin_steps : forall regs pc regs2 pc2 pos hint',
msteps tfibsegs (mkst regs pc mem rom) (mkst regs2 pc2 mem rom) -> (forall x, lkeep x -> getr regs2 x = getr regs x) ->
lfin regs2 pc2 pos hint' -> lfin regs pc pos hint'.
Proof.
intros regs pc regs2 pc2 pos hint' Hms Hfr (regs' & c' & Hms' & A & Bq & C & D & E & G & K).
exists regs', c'. split; [eapply msteps_trans; [exact Hms | exact Hms']|]. split; [exact A|]. split; [exact Bq|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact G|].
intros x Hx. rewrite (K x Hx). apply Hfr. exact Hx.
Qed.
Lemma lfin_pc : forall regs (pc pc' : word) pos hint', bv_unsigned pc = bv_unsigned pc' -> lfin regs pc' pos hint' -> lfin regs pc pos hint'.
Proof. intros regs pc pc' pos hint' H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let x := fresh "x" in let Hx := fresh "Hkeep" in
intros x Hx; unfold lkeep in Hx; destruct Hx as (?&?&?&?&?); rewrite ?getr_other by assumption; reflexivity.
Lemma probe_loop : forall fuel h regs pos hint',
fs_probe fuel live CID h = Some (pos, hint') ->
getr regs 12 = Z_to_bv 64 h -> getr regs 15 = Z_to_bv 64 (FS_N - 1) -> getr regs 14 = Z_to_bv 64 FL ->
getr regs 10 = Z_to_bv 64 (Z.of_nat fuel) -> Z.of_nat fuel <= FS_N -> 0 <= h ->
lfin regs (Z_to_bv 64 (FS_LOOP + 0x0)) pos hint'.
Proof.
induction fuel as [|f IH]; intros h regs pos hint' Hp H12 H15 H14 H10 Hfuel Hh; [discriminate Hp|].
destruct HFL as [HFL0 HFL1]. assert (HN : FS_N = 128) by reflexivity.
pose proof (Z.mod_pos_bound h FS_N ltac:(lia)) as Hm.
cbn [fs_probe] in Hp. rewrite fs_frames_cid in Hp.
pose proof (Hflags (h mod FS_N) Hm) as RD.
destruct (mem_pos live CID (h mod FS_N)) eqn:Hmp.
-
assert (Hf1 : (1 <= f)%nat) by (destruct f; [cbn in Hp; discriminate Hp | lia]).
eapply lfin_steps.
+ norm_pc.
svand F_L0 D_L0 (Z_to_bv 64 (h mod FS_N)); [rewrite (v_and_mask h Hh); reflexivity|].
sv F_L4 D_L4 (Z_to_bv 64 (FL + h mod FS_N)).
steplb1 F_L8 D_L8 RD.
stepbf F_Lc D_Lc.
stepiwv F_L10 D_L10 (Z_to_bv 64 (Z.of_nat f)) ltac:(gr; rwH; imm_norm; rewrite v_addiw_dec by lia; f_equal; lia).
sv F_L14 D_L14 (Z_to_bv 64 (h + 1)).
stepbt F_L18 D_L18.
apply mst_refl.
+ frame.
+ eapply lfin_pc; [| eapply (IH (h + 1))]; [vm_compute; reflexivity | exact Hp | gr; reflexivity | gr; exact H15 | gr; exact H14 | gr; reflexivity | lia | lia].
-
injection Hp as <- <-.
eexists _, (Z.of_nat (S f)). split.
+ norm_pc.
svand F_L0 D_L0 (Z_to_bv 64 (h mod FS_N)); [rewrite (v_and_mask h Hh); reflexivity|].
sv F_L4 D_L4 (Z_to_bv 64 (FL + h mod FS_N)).
steplb1 F_L8 D_L8 RD.
stepbt F_Lc D_Lc.
wlit_replace (Z_to_bv 64 FS_FOUND). apply mst_refl.
+ split; [gr; rewrite H12; f_equal; lia|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; exact H10|]. split; [lia | frame].
Qed.
End o.
Lemma r_A : RUNTO FS_LOOP ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma r_C1 : RUN ssC1 = (eC1, stC1). Proof. vm_compute. reflexivity. Qed.
Lemma r_C2 : forall hi, RUN (ssC2 hi) = (eC2 hi, stC2 hi). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma r_C2b : forall hi, RUN (ssC2b hi) = (eC2b hi, stC2b hi). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma r_C3 : forall hi, RUN (ssC3 hi) = (eC3 hi, stC3 hi). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma stack_malloc_inv : forall cid S pos S',
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
exists hint', fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint') /\
S' = set_fs (mkFS (zupd cid hint' (fs_hint (st_fs S))) ((cid, pos) :: fs_live (st_fs S))) S.
Proof.
intros cid S pos S' H. unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S)))) as [[p h']|] eqn:Hp.
- cbn [ibind apath] in H. injection H as <- <-. exists h'. split; reflexivity.
- cbn [apath] in H. discriminate H.
Qed.
Lemma fs_probe_facts : forall fuel live cid h pos hint',
fs_probe fuel live cid h = Some (pos, hint') -> 0 < fs_frames cid ->
mem_pos live cid pos = false /\ 0 <= pos < fs_frames cid /\ h < hint' /\ pos = (hint' - 1) mod fs_frames cid.
Proof.
induction fuel as [|f IH]; intros live cid h pos hint' Hp HN; [discriminate Hp|].
cbn [fs_probe] in Hp. destruct (mem_pos live cid (h mod fs_frames cid)) eqn:Hm.
- destruct (IH _ _ _ _ _ Hp HN) as (A & Bq & C & D). repeat split; first [assumption | lia].
- injection Hp as <- <-. pose proof (Z.mod_pos_bound h (fs_frames cid) HN). replace (h + 1 - 1) with h by lia. repeat split; first [exact Hm | lia].
Qed.
Lemma combine_seq_nth : forall {X} (l : list X) (d : X) s n, (n < length l)%nat -> In ((s + n)%nat, nth n l d) (combine (seq s (length l)) l).
Proof.
induction l as [|x l IH]; intros d s n Hn; cbn in Hn; [lia|]. cbn [length seq combine].
destruct n as [|n]; [left; rewrite Nat.add_0_r; reflexivity | right]. replace (s + S n)%nat with (S s + n)%nat by lia. apply IH. lia.
Qed.
Lemma env_agree_Ereg_app : forall regs l1 l2 k, (k <= 32 + length l1)%nat -> env_agree k (Ereg regs l1) (Ereg regs (l1 ++ l2)).
Proof.
intros regs l1 l2 k Hk. split; [|reflexivity]. intros n Hn.
destruct (Nat.lt_ge_cases n 32) as [L|L].
- unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia].
- replace n with (32 + (n - 32))%nat by lia. rewrite !ew_Ereg_extra. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma val_mem_mod64 : forall (m : word -> option byte) a x, val_mem tfibsegs m a 8 x -> val_mem tfibsegs m a 8 (x mod 2 ^ 64).
Proof.
intros m a x Hv k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold le_byte, YG0f.le_byte, YO0f.le_byte.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma fs_probe_shift : forall fuel live cid h h2 pos hint',
0 < fs_frames cid -> h2 mod fs_frames cid = h mod fs_frames cid ->
fs_probe fuel live cid h = Some (pos, hint') -> fs_probe fuel live cid h2 = Some (pos, h2 + (hint' - h)).
Proof.
induction fuel as [|f IH]; intros live cid h h2 pos hint' HN Hc Hp; [discriminate Hp|].
cbn [fs_probe] in Hp |- *. rewrite Hc. destruct (mem_pos live cid (h mod fs_frames cid)).
- rewrite (IH live cid (h + 1) (h2 + 1) pos hint' HN); [f_equal; f_equal; lia | | exact Hp].
rewrite (Z.add_mod h2 1), (Z.add_mod h 1) by lia. rewrite Hc. reflexivity.
- injection Hp as <- <-. f_equal. f_equal. lia.
Qed.
Lemma memA_windows : forall E a, in_wrange E memA a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
vm_compute in Ht. repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; exact Hw | exfalso; lia] |]). destruct Ht.
Qed.
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? FS_LOOP) && reg_is ss 12 (SOff aH 0) && reg_is ss 15 (SLit (FS_N - 1)) && reg_is ss 14 (SOff aF FS_FLOFF) && reg_is ss 10 (SLit FS_N)
&& reg_is ss 18 (SOff aF 0) && reg_is ss 8 (SOff 2 0) && reg_is ss 2 (SOff 2 (-48)) && reg_is ss 9 (SOff 10 0).
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma eA_atoms : ss_atoms_lt 37 eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma C1_facts : ss_pc eC1 = FS_SDFF /\ reg_is eC1 18 s2C1 = true /\ ss_atoms_lt 43 eC1 = true /\ ss_resv eC1 = None /\
match stC1 with RS_stopped (SR_addr _) => True | _ => False end.
Proof. vm_compute. repeat split; reflexivity || exact I. Qed.
Lemma C2_facts : forall hi, stC2 hi = RS_stopped (SR_branch BC_LTU cntC2 (SLit THR)) /\ ss_resv (eC2 hi) = None.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma C2b_facts : forall hi, stC2b hi = RS_stopped SR_fetch /\ ss_pc (eC2b hi) = tfib_A_musl_memset /\ ss_resv (eC2b hi) = None /\
reg_is (eC2b hi) 10 a0C2 = true /\ reg_is (eC2b hi) 11 (SLit 0) = true /\ reg_is (eC2b hi) 12 a2C2 = true /\ reg_is (eC2b hi) 1 (SLit FS_MSRET) = true /\
ss_atoms_lt 43 (eC2b hi) = true /\ no_cdata (ss_mem (eC2b hi)) = true.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma stC2_match : forall hi (A : Type) (x y : A), match stC2 hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma stC2b_match : forall hi (A : Type) (x y : A), match stC2b hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma stC3_match : forall hi (A : Type) (x y : A), match stC3 hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma C3_facts : forall hi, stC3 hi = RS_stopped (SR_jalr (SOff 1 0)) /\ ss_resv (eC3 hi) = None /\
forallb (fun r => reg_is (eC3 hi) r (SOff (Z.to_nat r) 0)) [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true /\
reg_is (eC3 hi) 10 (SOff aFF 0) = true /\ reg_is (eC3 hi) 4 (SLit TP) = true.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma s2C1_eq : s2C1 = SAlu ALU_ADD (SOff aF 7376896) (SAlu ALU_SLL (SOff aPOS 0) (SLit 13)). Proof. vm_compute. reflexivity. Qed.
Lemma a0C2_eq : a0C2 = SAlu ALU_ADD (SLit SHADOW_OFF) (SAlu ALU_SRL (SOff aFF 0) (SLit 3)). Proof. vm_compute. reflexivity. Qed.
Lemma cntC2_eq : cntC2 = SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-8)) (SOff aFF 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aFF 0) (SLit 3)). Proof. vm_compute. reflexivity. Qed.
Lemma a2C2_eq : a2C2 = SAlu ALU_ADD cntC2 (SLit 0). Proof. vm_compute. reflexivity. Qed.
Lemma s2C1_denot : forall E F pos, bv_unsigned (ew E aF) = F -> bv_unsigned (ew E aPOS) = pos -> 0 <= F -> 0 <= pos ->
F + FS_FROFF + pos * FS_B < 2 ^ 64 -> sv_denot E s2C1 = Z_to_bv 64 (F + FS_FROFF + pos * FS_B).
Proof.
intros E F pos HF Hp HF0 Hp0 Hhi. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E s2C1)). f_equal.
change (bv_unsigned (sv_denot E s2C1)) with (U E s2C1). rewrite (U_zev E s2C1) by (vm_compute; reflexivity).
rewrite s2C1_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HF, Hp, Z.add_0_r. change (Z.land (zcanon 13) 63) with 13.
unfold FS_FROFF, FS_B in *. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 13) with 8192.
rewrite (zcanon_small pos) by lia. rewrite (zcanon_small (pos * 8192)) by lia. rewrite (zcanon_small (F + 7376896)) by lia. apply zcanon_small. lia.
Qed.
Lemma a0C2_denot : forall E FF, bv_unsigned (ew E aFF) = FF -> 0 <= FF < 2 ^ 64 -> sv_denot E a0C2 = Z_to_bv 64 (SHADOW_OFF + FF / 8).
Proof.
intros E FF HFF Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a0C2)). f_equal.
change (bv_unsigned (sv_denot E a0C2)) with (U E a0C2). rewrite (U_zev E a0C2) by (vm_compute; reflexivity).
rewrite a0C2_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, !Z.add_0_r. change (Z.land (zcanon 3) 63) with 3. change (zcanon SHADOW_OFF) with SHADOW_OFF.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold SHADOW_OFF.
pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound FF 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small FF) by lia. rewrite (zcanon_small (FF / 8)) by lia. apply zcanon_small. lia.
Qed.
Lemma cntC2_U : forall E FF n, bv_unsigned (ew E aFF) = FF -> bv_unsigned (ew E 10) = n ->
8 <= FF -> FF + n <= 2 ^ 63 -> FF mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> U E cntC2 = n / 8.
Proof.
intros E FF n HFF Hn H8 Hhi Hm1 Hm2 Hn8. rewrite (U_zev E cntC2) by (vm_compute; reflexivity).
rewrite cntC2_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, Hn, !Z.add_0_r. change (Z.land (zcanon 3) 63) with 3.
assert (Eq1 : FF = 8 * (FF / 8)) by (pose proof (Z.div_mod FF 8 ltac:(lia)); lia).
assert (Eq2 : n = 8 * (n / 8)) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
set (f := FF / 8) in *. set (m := n / 8) in *.
assert (Hf : 1 <= f) by lia. assert (Hm : 1 <= m) by lia.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_small (n + -8)) by lia. rewrite (zcanon_small FF) by lia. rewrite (zcanon_small (n + -8 + FF)) by lia. change (zcanon 1) with 1.
replace ((n + -8 + FF) / 8) with (f + m - 1) by (rewrite Eq1, Eq2; replace (8 * m + -8 + 8 * f) with ((f + m - 1) * 8) by lia; rewrite Z_div_mult by lia; reflexivity).
replace (FF / 8) with f by reflexivity.
rewrite (zcanon_small (f + m - 1)) by lia. rewrite (zcanon_small (f + m - 1 + 1)) by lia. rewrite (zcanon_small f) by lia.
replace (f + m - 1 + 1 - f) with m by lia. apply zcanon_small. lia.
Qed.
Lemma a2C2_U : forall E FF n, bv_unsigned (ew E aFF) = FF -> bv_unsigned (ew E 10) = n ->
8 <= FF -> FF + n <= 2 ^ 63 -> FF mod 8 = 0 -> n mod 8 = 0 -> 8 <= n -> U E a2C2 = n / 8.
Proof.
intros E FF n HFF Hn H8 Hhi Hm1 Hm2 Hn8. rewrite (U_zev E a2C2) by (vm_compute; reflexivity).
rewrite a2C2_eq. cbn [zev zalu_raw]. rewrite <- (U_zev E cntC2) by (vm_compute; reflexivity).
rewrite (cntC2_U E FF n HFF Hn H8 Hhi Hm1 Hm2 Hn8). change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (Z.div_pos n 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound n 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
apply zcanon_small. lia.
Qed.
Lemma memC1_windows : forall E a, in_wrange E (ss_mem ssC1) a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 39) + 0 <= a < bv_unsigned (ew E 39) + 1) \/
(bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
vm_compute in Ht. repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; exact Hw | exfalso; lia] |]). destruct Ht.
Qed.
Definition C23_windows (E : env) (a : Z) : Prop :=
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 41) + 0 <= a < bv_unsigned (ew E 41) + FS_B) \/
(bv_unsigned (ew E 39) + 0 <= a < bv_unsigned (ew E 39) + 1) \/ (bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Ltac c23w Ht Hw := vm_compute in Ht; repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw | right; right; right; exact Hw | exfalso; lia] |]); destruct Ht.
Lemma memC2_windows : forall hi E a, in_wrange E (ss_mem (ssC2 hi)) a -> C23_windows E a.
Proof. intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw). unfold C23_windows. destruct zhi; c23w Ht Hw. Qed.
Lemma memC2b_windows : forall hi E a, in_wrange E (ss_mem (ssC2b hi)) a -> C23_windows E a.
Proof. intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw). unfold C23_windows. destruct zhi; c23w Ht Hw. Qed.
Lemma memC3_windows : forall hi E a, in_wrange E (ss_mem (ssC3 hi)) a -> C23_windows E a.
Proof. intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw). unfold C23_windows. destruct zhi; c23w Ht Hw. Qed.
Definition rSTK3 : YP09.region := Eval vm_compute in nth 0 (ss_mem eC3H) stkA.
Definition rFF3 : YP09.region := Eval vm_compute in nth 1 (ss_mem eC3H) stkA.
Definition rFLG3 : YP09.region := Eval vm_compute in nth 2 (ss_mem eC3H) stkA.
Definition rF3 : YP09.region := Eval vm_compute in nth 3 (ss_mem eC3H) stkA.
Lemma eC3_regions : forall hi, nth_error (ss_mem (eC3 hi)) 0 = Some rSTK3 /\ nth_error (ss_mem (eC3 hi)) 1 = Some rFF3 /\
nth_error (ss_mem (eC3 hi)) 2 = Some rFLG3 /\ nth_error (ss_mem (eC3 hi)) 3 = Some rF3.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma rSTK3_shape : YP09.r_base rSTK3 = Some 2%nat /\ YP09.r_wlo rSTK3 = - FS_WIN /\ YP09.r_whi rSTK3 = 0. Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rFF3_shape : YP09.r_base rFF3 = Some aFF /\ YP09.r_wlo rFF3 = 0 /\ YP09.r_whi rFF3 = FS_B /\
nth_error (YP09.r_chunks rFF3) 0 = Some (YP09.mkChunk (FS_B - 8) (CVal 8 (SOff aFLG 0))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rFLG3_shape : YP09.r_base rFLG3 = Some aFLG /\ YP09.r_wlo rFLG3 = 0 /\ YP09.r_whi rFLG3 = 1 /\
nth_error (YP09.r_chunks rFLG3) 0 = Some (YP09.mkChunk 0 (CVal 1 (SLit 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rF3_shape : YP09.r_base rF3 = Some aF /\ YP09.r_wlo rF3 = FS_HOFF /\ YP09.r_whi rF3 = FS_HOFF + 8 /\
nth_error (YP09.r_chunks rF3) 0 = Some (YP09.mkChunk FS_HOFF (CVal 8 (SOff aH2 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma aview_of_val_mem : forall (H : word -> bool) mem a (n : nat) v k, val_mem tfibsegs (mrestrict H mem) a n v -> (k < n)%nat ->
aview tfibsegs H mem (a + Z.of_nat k) = Some (YG0f.le_byte v n k).
Proof.
intros H mem a n v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. change (YG0f.le_byte v n k) with (YO0f.le_byte v n k).
unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma hs_kept_gen : forall (H : word -> bool) (mem mem' : word -> option byte) (P : Z -> Prop),
(forall z : word, ~ P (bv_unsigned z) -> mem' z = mem z) ->
(forall a, P a -> exists m0, apresent H m0 a) ->
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros H mem mem' P MEQ PRES a Ha Hh. rewrite MEQ; [reflexivity|]. intros HP.
rewrite unsigned_lit_small in HP by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
destruct (PRES a HP) as (m0 & Hf & _). rewrite Hh in Hf. discriminate Hf.
Qed.
Lemma frame_addr_cid : forall ly pos, frame_addr ly CID pos = ly_F ly + FS_FROFF + pos * FS_B.
Proof. intros ly pos. unfold frame_addr, fs_frame_off, FS_FROFF, kFakeFramesOff, CID. change (Z.shiftl 1 kStackSizeLog) with 1048576. change (fs_frame_bytes 7) with FS_B. unfold FS_B. lia. Qed.
Lemma flag_addr_cid : forall ly pos, flag_addr ly CID pos = ly_F ly + FS_FLOFF + pos.
Proof. intros ly pos. unfold flag_addr, fs_flag_off, FS_FLOFF, kFakeFlagsOff, CID. change (fs_flags_off 7) with (36608 - 4096). lia. Qed.
End g.
