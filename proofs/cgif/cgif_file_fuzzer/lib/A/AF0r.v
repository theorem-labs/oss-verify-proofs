(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0t YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN32.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition CID : Z := 1.
Definition FS_ENTRY : Z := 0x3c8a4.
Definition FS_LOOP : Z := 0x3c938.
Definition FS_FOUND : Z := 0x3c9b0.
Definition FS_SDFF : Z := 0x3c9dc.
Definition FS_SDSH : Z := 0x3c9f8.
Definition FS_WIN : Z := 208.
Definition FS_N : Z := 8192.
Definition FS_FLOFF : Z := 0x5000.
Definition FS_B : Z := 128.
Definition FS_FROFF : Z := 0x109000.
Definition FS_HOFF : Z := 8.
Definition TP : Z := 0x5d8f90.
Definition TSD : Z := 0x5fa338.
Definition fs_ranges : list (Z * nat) :=
[(0x3c8a4, 100%nat); (0x3ca34, 100%nat); (0x61aac, 2%nat); (0x46274, 31%nat); (0x97e88, 9%nat); (0x5bdec, 8%nat);
(0x54938, 6%nat); (0x98f3c, 7%nat); (0x69500, 140%nat); (0x3cbd0, 28%nat)].
Definition tbl_fs : ctable := Eval vm_compute in build_ranges fs_ranges tbl_icpt.
Lemma tbl_fs_eq : tbl_fs = build_ranges fs_ranges tbl_icpt. Proof. vm_cast_no_check (eq_refl tbl_fs). Qed.
Lemma tbl_fs_ok : table_ok tfibsegs tbl_fs.
Proof. rewrite tbl_fs_eq. apply build_ranges_ok; [unfold fs_ranges; repeat constructor; cbn; discriminate | exact tbl_icpt_ok]. Qed.
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
Definition fsA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++
[(0x9ec90, 16, [(0, 8%N, 1); (8, 8%N, 0xfffffffffffff800)]); (0x9fd50, 8, [(0, 8%N, 0x97e88)]); (0x9df88, 8, [(0, 8%N, 0x137b28)]);
(0x137bb1, 1, [(0, 1%N, 1)]); (0x9dfe8, 8, [(0, 8%N, 0x135a98)]); (0x135a98, 4, [(0, 4%N, 0)]); (0x9eca0, 8, [(0, 8%N, 0x8)]);
(0xa5860, 8, [(0, 1%N, 1); (4, 4%N, 0)]); (TP - 88, 8, [(0, 8%N, TSD)]); (TP - 8, 8, [(0, 8%N, 0x5d8fb0)]); (0x5d8fb8, 8, [(0, 8%N, 0x5d9790)])].
Lemma fsA_rodata_chk : forall ly, rodata_chk ly fsA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition aT : nat := 32. Definition aC : nat := 33. Definition aD : nat := 34. Definition aF : nat := 35. Definition aH : nat := 36.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- FS_WIN) 0 (- FS_WIN) 0 [].
Definition rTSD : YP09.region := YP09.mkRegion None TSD (TSD + 8) TSD TSD [YP09.mkChunk TSD (CVal 8 (SOff aC 0))].
Definition rTP0 : YP09.region := YP09.mkRegion None TP (TP + 8) TP TP [YP09.mkChunk TP (CVal 8 (SOff aF 0))].
Definition rTP8 : YP09.region := YP09.mkRegion None (TP + 8) (TP + 16) (TP + 8) (TP + 8) [YP09.mkChunk (TP + 8) (CVal 8 (SOff aD 0))]    .
Definition rT : YP09.region := YP09.mkRegion (Some aT) 48 64 48 48 [YP09.mkChunk 48 (CVal 8 (SLit 0x5d96c8)); YP09.mkChunk 56 (CVal 8 (SLit 0x5d97a4))].
Definition rC : YP09.region := YP09.mkRegion (Some aC) 152 160 152 152 [YP09.mkChunk 152 (CVal 8 (SOff aT 0))].
Definition rD : YP09.region := YP09.mkRegion (Some aD) 24 32 24 24 [YP09.mkChunk 24 (CVal 8 (SLit TP))].
Definition rF : YP09.region := YP09.mkRegion (Some aF) FS_HOFF 97 FS_HOFF (FS_HOFF + 8)
[YP09.mkChunk FS_HOFF (CVal 8 (SOff aH 0)); YP09.mkChunk 88 (CVal 8 (SLit 20)); YP09.mkChunk 96 (CVal 1 (SLit 0))].
Definition memA : smem := stkA :: rTSD :: rTP0 :: rTP8 :: rT :: rC :: rD :: rF :: map ro_region fsA_rodata.
Definition factsA : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + FS_WIN) kHighMemEnd 4);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)              ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)                ;
(aD, mkAF 4096 (CEIL_MAX - 4096) 12)              ;
(aF, mkAF 4096 (CEIL_MAX - kFakeStackSize) 12)    ;
(aH, mkAF 0 (2^64 - 1) 0)].
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
Definition aH2 : nat := 37. Definition aPOS : nat := 38. Definition aFLG : nat := 39. Definition aCNT : nat := 40. Definition aFF : nat := 41. Definition aSH : nat := 42.
Definition rFLG : YP09.region := YP09.mkRegion (Some aFLG) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition rFF : YP09.region := YP09.mkRegion (Some aFF) 0 FS_B 0 FS_B [].
Definition rSH : YP09.region := YP09.mkRegion (Some aSH) 0 (FS_B / 8) 0 (FS_B / 8) [].
Definition updC1 : list (bv 5 * sv) := [((12%bv : bv 5), SOff aH2 0); ((17%bv : bv 5), SOff aPOS 0); ((15%bv : bv 5), SOff aFLG 0); ((5%bv : bv 5), SLit 0); ((10%bv : bv 5), SOff aCNT 0)].
Definition idxC1 : list nat := [7; 8; 9; 10; 11; 12; 13; 14]%nat.
Definition memC1 : smem := nth 0 (ss_mem eA) stkA :: rFLG :: map (fun i => nth i (ss_mem eA) stkA) idxC1.
Definition preC1 : sstate := add_fact (mkSS FS_FOUND (sr_sets (ss_regs eA) updC1) memC1 None (ss_facts eA)) aPOS (mkAF 0 (FS_N - 1) 0).
Definition ssC1 : sstate := Eval vm_compute in preC1.
Lemma ssC1_eq : preC1 = ssC1. Proof. vm_compute. reflexivity. Qed.
Definition eC1 : sstate := Eval vm_compute in fst (RUN ssC1).
Definition stC1 : run_status := Eval vm_compute in snd (RUN ssC1).
Definition s1C1 : sv := Eval vm_compute in RG eC1 9.
Definition ffLO (hi : bool) : Z := if hi then kHighMemBeg else 4096.
Definition ffHI (hi : bool) : Z := if hi then CEIL_MAX - FS_B else kLowShadowBeg - FS_B.
Definition shLO (hi : bool) : Z := if hi then kHighShadowBeg else kLowShadowBeg + TFIB_IMG_END / 8.
Definition shHI (hi : bool) : Z := if hi then kHighShadowEnd - FS_B / 8 else kLowShadowEnd - FS_B / 8.
Definition memC2 : smem := nth 0 (ss_mem eC1) stkA :: rFF :: tl (ss_mem eC1).
Definition preC2 (hi : bool) : sstate := add_fact (mkSS (ss_pc eC1) (sr_sets (ss_regs eC1) [((9%bv : bv 5), SOff aFF 0)]) memC2 None (ss_facts eC1)) aFF (mkAF (ffLO hi) (ffHI hi) 0).
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
Definition a1C2 : sv := Eval vm_compute in RG eC2H 11.
Definition memC2e : smem := Eval vm_compute in ss_mem eC2H.
Lemma eC2_mem : forall hi, ss_mem (eC2 hi) = memC2e. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition memC3 : smem := nth 0 memC2e stkA :: rSH :: tl memC2e.
Definition preC3 (hi : bool) : sstate := add_fact (mkSS (ss_pc (eC2 hi)) (sr_sets (ss_regs (eC2 hi)) [((11%bv : bv 5), SOff aSH 0)]) memC3 None (ss_facts (eC2 hi))) aSH (mkAF (shLO hi) (shHI hi) 0).
Definition ssC3H : sstate := Eval vm_compute in preC3 true.
Definition ssC3L : sstate := Eval vm_compute in preC3 false.
Definition ssC3 (hi : bool) : sstate := if hi then ssC3H else ssC3L.
Lemma ssC3_eq : forall hi, preC3 hi = ssC3 hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
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
intros h Hh. replace (FS_N - 1) with (Z.ones 13) by reflexivity. rewrite Z.land_ones by lia.
change FS_N with (2 ^ 13). rewrite <- (Z.mod_mod_divide h (2 ^ 64) (2 ^ 13)) by (first [exists (2 ^ (64 - 13)); reflexivity | lia]). reflexivity.
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
Lemma F_L0 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x0)) = Some (0x00e678b3%bv : bv 32). Proof. ftac. Qed.
Lemma D_L0 : decode_any (0x00e678b3%bv : bv 32) = Some (Op ALU_AND 17 12 14, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L4 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x4)) = Some (0x011687b3%bv : bv 32). Proof. ftac. Qed.
Lemma D_L4 : decode_any (0x011687b3%bv : bv 32) = Some (Op ALU_ADD 15 13 17, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L8 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x8)) = Some (0x0007c283%bv : bv 32). Proof. ftac. Qed.
Lemma D_L8 : decode_any (0x0007c283%bv : bv 32) = Some (Load SZ1 false 5 15 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_Lc : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0xc)) = Some (0x06028663%bv : bv 32). Proof. ftac. Qed.
Lemma D_Lc : decode_any (0x06028663%bv : bv 32) = Some (Branch BC_EQ 5 0 108, 4%Z). Proof. vm_refl_bv. Qed.
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
Definition lkeep (x : bv 5) : Prop := x <> 5%bv /\ x <> 10%bv /\ x <> 12%bv /\ x <> 15%bv /\ x <> 17%bv.
Definition lfin (regs : bvmap 5 word) (pc : word) (pos hint' : Z) : Prop :=
exists regs' c', msteps tfibsegs (mkst regs pc mem rom) (mkst regs' (Z_to_bv 64 FS_FOUND) mem rom)
/\ getr regs' 12 = Z_to_bv 64 (hint' - 1) /\ getr regs' 17 = Z_to_bv 64 pos /\ getr regs' 15 = Z_to_bv 64 (FL + pos)
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
getr regs 12 = Z_to_bv 64 h -> getr regs 14 = Z_to_bv 64 (FS_N - 1) -> getr regs 13 = Z_to_bv 64 FL ->
getr regs 10 = Z_to_bv 64 (Z.of_nat fuel) -> Z.of_nat fuel <= FS_N -> 0 <= h ->
lfin regs (Z_to_bv 64 (FS_LOOP + 0x0)) pos hint'.
Proof.
induction fuel as [|f IH]; intros h regs pos hint' Hp H12 H14 H13 H10 Hfuel Hh; [discriminate Hp|].
destruct HFL as [HFL0 HFL1]. assert (HN : FS_N = 8192) by reflexivity.
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
+ eapply lfin_pc; [| eapply (IH (h + 1))]; [vm_compute; reflexivity | exact Hp | gr; reflexivity | gr; exact H14 | gr; exact H13 | gr; reflexivity | lia | lia].
-
injection Hp as <- <-.
eexists _, (Z.of_nat (S f)). split.
+ norm_pc.
svand F_L0 D_L0 (Z_to_bv 64 (h mod FS_N)); [rewrite (v_and_mask h Hh); reflexivity|].
sv F_L4 D_L4 (Z_to_bv 64 (FL + h mod FS_N)).
steplb1 F_L8 D_L8 RD.
stepbt F_Lc D_Lc.
replace (Z_to_bv 64 FS_FOUND) with (248240%bv : bv 64) by (apply bv_eq; reflexivity). apply mst_refl.
+ split; [gr; rewrite H12; f_equal; lia|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; exact H10|]. split; [lia | frame].
Qed.
End o.
Lemma r_A : RUNTO FS_LOOP ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma r_C1 : RUN ssC1 = (eC1, stC1). Proof. vm_compute. reflexivity. Qed.
Lemma r_C2 : forall hi, RUN (ssC2 hi) = (eC2 hi, stC2 hi). Proof. intros [|]; vm_compute; reflexivity. Qed.
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
Lemma In_fs_cells_acells : forall (B : asyms) ly S c, In c (fs_cells S) -> In c (acells B ly S).
Proof. intros B ly S c H. unfold acells. rewrite !in_app_iff. right; right; right; right; right; left. exact H. Qed.
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
(ss_pc ss =? FS_LOOP) && reg_is ss 12 (SOff aH 0) && reg_is ss 14 (SLit (FS_N - 1)) && reg_is ss 13 (SOff aF FS_FLOFF) && reg_is ss 10 (SLit FS_N)
&& reg_is ss 9 (SOff aF 0) && reg_is ss 8 (SOff 2 0) && reg_is ss 2 (SOff 2 (-32)).
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma eA_atoms : ss_atoms_lt 37 eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma C1_facts : ss_pc eC1 = FS_SDFF /\ reg_is eC1 9 s1C1 = true /\ ss_atoms_lt 43 eC1 = true /\ ss_resv eC1 = None /\
match stC1 with RS_stopped (SR_addr _) => True | _ => False end.
Proof. vm_compute. repeat split; reflexivity || exact I. Qed.
Lemma C2_facts : forall hi, ss_pc (eC2 hi) = FS_SDSH /\ reg_is (eC2 hi) 11 a1C2 = true /\ ss_atoms_lt 43 (eC2 hi) = true /\ ss_resv (eC2 hi) = None /\
match stC2 hi with RS_stopped (SR_addr _) => True | _ => False end.
Proof. intros [|]; vm_compute; repeat split; reflexivity || exact I. Qed.
Lemma stC2_match : forall hi (A : Type) (x y : A), match stC2 hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma stC3_match : forall hi (A : Type) (x y : A), match stC3 hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma eC2_split : forall hi, ss_mem (eC2 hi) = nth 0 (ss_mem (eC2 hi)) stkA :: tl (ss_mem (eC2 hi)). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma C3_facts : forall hi, stC3 hi = RS_stopped (SR_jalr (SOff 1 0)) /\ ss_resv (eC3 hi) = None /\
forallb (fun r => reg_is (eC3 hi) r (SOff (Z.to_nat r) 0)) [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true /\
reg_is (eC3 hi) 10 (SOff aFF 0) = true /\ reg_is (eC3 hi) 4 (SLit TP) = true.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma s1C1_eq : s1C1 = SAlu ALU_ADD (SOff aF 1085440) (SAlu ALU_SLL (SOff aPOS 0) (SLit 7)). Proof. vm_compute. reflexivity. Qed.
Lemma a1C2_eq : a1C2 = SAlu ALU_ADD (SAlu ALU_ADD (SLit SHADOW_OFF) (SAlu ALU_SRL (SOff aFF 0) (SLit 3))) (SLit 0). Proof. vm_compute. reflexivity. Qed.
Lemma s1C1_denot : forall E F pos, bv_unsigned (ew E aF) = F -> bv_unsigned (ew E aPOS) = pos -> 0 <= F -> 0 <= pos ->
F + FS_FROFF + pos * FS_B < 2 ^ 64 -> sv_denot E s1C1 = Z_to_bv 64 (F + FS_FROFF + pos * FS_B).
Proof.
intros E F pos HF Hp HF0 Hp0 Hhi. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E s1C1)). f_equal.
change (bv_unsigned (sv_denot E s1C1)) with (U E s1C1). rewrite (U_zev E s1C1) by (vm_compute; reflexivity).
rewrite s1C1_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HF, Hp, Z.add_0_r. change (Z.land (zcanon 7) 63) with 7.
unfold FS_FROFF, FS_B in *. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 7) with 128.
rewrite (zcanon_small pos) by lia. rewrite (zcanon_small (pos * 128)) by lia. rewrite (zcanon_small (F + 1085440)) by lia. apply zcanon_small. lia.
Qed.
Lemma a1C2_denot : forall E FF, bv_unsigned (ew E aFF) = FF -> 0 <= FF < 2 ^ 64 -> sv_denot E a1C2 = Z_to_bv 64 (SHADOW_OFF + FF / 8).
Proof.
intros E FF HFF Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a1C2)). f_equal.
change (bv_unsigned (sv_denot E a1C2)) with (U E a1C2). rewrite (U_zev E a1C2) by (vm_compute; reflexivity).
rewrite a1C2_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, !Z.add_0_r. change (Z.land (zcanon 3) 63) with 3. change (zcanon SHADOW_OFF) with SHADOW_OFF.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold SHADOW_OFF.
pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound FF 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small FF) by lia. rewrite (zcanon_small (FF / 8)) by lia. rewrite (zcanon_small (2147450880 + FF / 8)) by lia. apply zcanon_small. lia.
Qed.
Lemma memC1_windows : forall E a, in_wrange E (ss_mem ssC1) a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 39) + 0 <= a < bv_unsigned (ew E 39) + 1) \/
(bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
vm_compute in Ht. repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; exact Hw | exfalso; lia] |]). destruct Ht.
Qed.
Lemma memC2_windows : forall hi E a, in_wrange E (ss_mem (ssC2 hi)) a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 41) + 0 <= a < bv_unsigned (ew E 41) + FS_B) \/
(bv_unsigned (ew E 39) + 0 <= a < bv_unsigned (ew E 39) + 1) \/ (bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
destruct zhi; vm_compute in Ht; repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw | right; right; right; exact Hw | exfalso; lia] |]); destruct Ht.
Qed.
Lemma memC3_windows : forall hi E a, in_wrange E (ss_mem (ssC3 hi)) a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 42) + 0 <= a < bv_unsigned (ew E 42) + FS_B / 8) \/
(bv_unsigned (ew E 41) + 0 <= a < bv_unsigned (ew E 41) + FS_B) \/
(bv_unsigned (ew E 39) + 0 <= a < bv_unsigned (ew E 39) + 1) \/ (bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
destruct zhi; vm_compute in Ht; repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw | right; right; right; left; exact Hw | right; right; right; right; exact Hw | exfalso; lia] |]); destruct Ht.
Qed.
Definition rSTK3 : YP09.region := Eval vm_compute in nth 0 (ss_mem eC3H) stkA.
Definition rSH3 : YP09.region := Eval vm_compute in nth 1 (ss_mem eC3H) stkA.
Definition rFF3 : YP09.region := Eval vm_compute in nth 2 (ss_mem eC3H) stkA.
Definition rFLG3 : YP09.region := Eval vm_compute in nth 3 (ss_mem eC3H) stkA.
Definition rF3 : YP09.region := Eval vm_compute in nth 4 (ss_mem eC3H) stkA.
Lemma eC3_regions : forall hi, nth_error (ss_mem (eC3 hi)) 0 = Some rSTK3 /\ nth_error (ss_mem (eC3 hi)) 1 = Some rSH3 /\ nth_error (ss_mem (eC3 hi)) 2 = Some rFF3 /\
nth_error (ss_mem (eC3 hi)) 3 = Some rFLG3 /\ nth_error (ss_mem (eC3 hi)) 4 = Some rF3.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma rSTK3_shape : YP09.r_base rSTK3 = Some 2%nat /\ YP09.r_wlo rSTK3 = - FS_WIN /\ YP09.r_whi rSTK3 = 0. Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rSH3_shape : YP09.r_base rSH3 = Some aSH /\ YP09.r_wlo rSH3 = 0 /\ YP09.r_whi rSH3 = FS_B / 8 /\
forall j, (j < 2)%nat -> nth_error (YP09.r_chunks rSH3) j = Some (YP09.mkChunk (FS_B / 8 - 8 - 8 * Z.of_nat j) (CVal 8 (SLit 0))).
Proof. vm_compute. repeat split; try reflexivity. intros j Hj. do 2 (destruct j as [|j]; [reflexivity|]). lia. Qed.
Lemma rFF3_shape : YP09.r_base rFF3 = Some aFF /\ YP09.r_wlo rFF3 = 0 /\ YP09.r_whi rFF3 = FS_B /\
nth_error (YP09.r_chunks rFF3) 0 = Some (YP09.mkChunk (FS_B - 8) (CVal 8 (SOff aFLG 0))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rFLG3_shape : YP09.r_base rFLG3 = Some aFLG /\ YP09.r_wlo rFLG3 = 0 /\ YP09.r_whi rFLG3 = 1 /\
nth_error (YP09.r_chunks rFLG3) 0 = Some (YP09.mkChunk 0 (CVal 1 (SLit 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rF3_shape : YP09.r_base rF3 = Some aF /\ YP09.r_wlo rF3 = FS_HOFF /\ YP09.r_whi rF3 = FS_HOFF + 8 /\
nth_error (YP09.r_chunks rF3) 0 = Some (YP09.mkChunk FS_HOFF (CVal 8 (SOff aH2 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rSH3_chunk : forall q, 0 <= q < 2 -> In (YP09.mkChunk (8 * q) (CVal 8 (SLit 0))) (YP09.r_chunks rSH3).
Proof.
intros q Hq.
assert (Hc : exists j, (j < 2)%nat /\ q = 2 - 1 - Z.of_nat j) by (exists (Z.to_nat (2 - 1 - q)); split; lia).
destruct Hc as (j & Hj & ->). pose proof (proj2 (proj2 (proj2 rSH3_shape)) j Hj) as X.
replace (8 * (2 - 1 - Z.of_nat j)) with (FS_B / 8 - 8 - 8 * Z.of_nat j) by (change (FS_B / 8) with 16; lia).
exact (nth_error_In _ _ X).
Qed.
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
Proof. intros ly pos. unfold frame_addr, fs_frame_off, FS_FROFF, kFakeFramesOff, CID. change (Z.shiftl 1 kStackSizeLog) with 1048576. change (fs_frame_bytes 1) with FS_B. unfold FS_B. lia. Qed.
Lemma flag_addr_cid : forall ly pos, flag_addr ly CID pos = ly_F ly + FS_FLOFF + pos.
Proof. intros ly pos. unfold flag_addr, fs_flag_off, FS_FLOFF, kFakeFlagsOff, CID. change (fs_flags_off 1) with (20480 - 4096). lia. Qed.
End g.
