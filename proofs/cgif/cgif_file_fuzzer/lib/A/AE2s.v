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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN32.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE3b AE6z AE70 AE2z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition MC_ENTRY : Z := 0x41904.
Definition MC_REAL : Z := 0x97194.
Definition MC_RSTOP : Z := 0x41900.
Definition MC_XENT : Z := 0x4273c.
Definition MC_YEND : Z := 0x427dc.
Definition MC_CALLRET : Z := 0x427e8.
Definition MC_RETC : Z := 0x43074.
Definition MC_FRAME : Z := 2240.
Definition MC_SCR : Z := 2312.
Lemma mc_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_mc FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_mc tbl_mc_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma mc_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_mc FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_mc tbl_mc_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition mcA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0x9df88, 8, [(0, 8%N, 0x137b28)]); (0x137c20, 8, [(0, 8%N, 0x101010101010101)]); (0x9fcd0, 8, [(0, 8%N, 0x97194)])].
Lemma mcA_rodata_chk : forall ly, rodata_chk ly mcA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- MC_FRAME) 0 (- MC_FRAME) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 0 (2^32 - 1) 0)].
Definition ssA : sstate := mkSS MC_ENTRY sr_atoms (stkA :: map ro_region mcA_rodata) None (mkFacts factsA [] []).
Definition RUNTOX (s : sstate) := sym_run_toN tfibsegs tbl_mc FUEL MC_XENT s.
Definition eA : sstate := Eval vm_compute in fst (RUNTOX ssA).
Lemma r_A : RUNTOX ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_mc FUEL s.
Definition RUNTOR (s : sstate) := sym_run_toN tfibsegs tbl_mc FUEL MC_RSTOP s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition regs0 : list sv := Eval vm_compute in (firstn 21 sr_atoms ++ [SLit 0x97194] ++ skipn 22 sr_atoms).
Definition facts0 : list (nat * afact) := [(20%nat, mkAF 0 (2^47) 0); (18%nat, mkAF 0 (2^47) 0); (9%nat, mkAF 0 0 0)].
Definition ss0 : sstate := mkSS MC_XENT regs0 [] None (mkFacts facts0 [] []).
Definition z0_e0 : sstate := Eval vm_compute in fst (RUN (ss0)).
Lemma r_z0_0 : RUN (ss0) = (z0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 20 0) (SLit (-1))) (SOff 9 0))). Proof. vm_compute. reflexivity. Qed.
Definition z0_e1 : sstate := Eval vm_compute in fst (RUN (AC z0_e0 BC_GEU (RG z0_e0 11) (RG z0_e0 9))).
Lemma r_z0_1 : RUN (AC z0_e0 BC_GEU (RG z0_e0 11) (RG z0_e0 9)) = (z0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 9 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition z0_e2 : sstate := Eval vm_compute in fst (RUN (AC z0_e1 BC_GEU (RG z0_e1 11) (RG z0_e1 25))).
Lemma r_z0_2 : RUN (AC z0_e1 BC_GEU (RG z0_e1 11) (RG z0_e1 25)) = (z0_e2, RS_stopped (SR_branch BC_NE (SOff 9 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition z0_e3 : sstate := Eval vm_compute in fst (RUN (AC z0_e2 BC_EQ (RG z0_e2 9) (SLit 0))).
Lemma r_z0_3 : RUN (AC z0_e2 BC_EQ (RG z0_e2 9) (SLit 0)) = (z0_e3, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 9 0))). Proof. vm_compute. reflexivity. Qed.
Definition z0_e4 : sstate := Eval vm_compute in fst (RUNTOR (AC z0_e3 BC_GEU (RG z0_e3 11) (RG z0_e3 9))).
Lemma r_z0_4 : RUNTOR (AC z0_e3 BC_GEU (RG z0_e3 11) (RG z0_e3 9)) = (z0_e4, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition regsC : list sv := regs0.
Definition ssC : sstate := mkSS MC_YEND regsC [] None (mkFacts [] [] []).
Definition eC : sstate := Eval vm_compute in fst (RUNTOR ssC).
Lemma r_C : RUNTOR ssC = (eC, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 2232 (CVal 8 (SOff 32 0));
YP09.mkChunk 2224 (CVal 8 (SOff 33 0));
YP09.mkChunk 2216 (CVal 8 (SOff 34 0));
YP09.mkChunk 2208 (CVal 8 (SOff 35 0));
YP09.mkChunk 2176 (CVal 8 (SOff 36 0));
YP09.mkChunk 2168 (CVal 8 (SOff 37 0));
YP09.mkChunk 2160 (CVal 8 (SOff 38 0));
YP09.mkChunk 2152 (CVal 8 (SOff 39 0));
YP09.mkChunk 2144 (CVal 8 (SOff 40 0));
YP09.mkChunk 2136 (CVal 8 (SOff 41 0));
YP09.mkChunk 2128 (CVal 8 (SOff 42 0));
YP09.mkChunk 2120 (CVal 8 (SOff 43 0));
YP09.mkChunk 2112 (CVal 8 (SOff 44 0));
YP09.mkChunk 2104 (CVal 8 (SOff 45 0));
YP09.mkChunk 2096 (CVal 8 (SOff 46 0));
YP09.mkChunk 2088 (CVal 8 (SOff 47 0));
YP09.mkChunk 2184 (CVal 8 (SLit 274548))].
Definition ss_epi : sstate := mkSS MC_CALLRET sr_atoms [YP09.mkRegion (Some 2%nat) 0 2240 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Definition SAVEDA : list (sv * Z) := [(SOff 1 0, -8); (SOff 8 0, -16); (SOff 9 0, -24); (SOff 18 0, -32); (SLit 274548, -56); (SOff 12 0, -64); (SOff 11 0, -72); (SOff 10 0, -80); (SOff 19 0, -88); (SOff 20 0, -96); (SOff 21 0, -104); (SOff 22 0, -112); (SOff 23 0, -120); (SOff 24 0, -128); (SOff 25 0, -136); (SOff 26 0, -144); (SOff 27 0, -152)].
Definition KEPTA : list Z := [3; 4; 22; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? MC_XENT) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - MC_FRAME) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 20 (SOff 10 0) && reg_is ss 18 (SOff 11 0) && reg_is ss 9 (SOff 12 0) && reg_is ss 21 (SLit MC_REAL) && reg_is ss 19 (SLit MC_RETC) &&
reg_is ss 2 (SOff 2 (-2240)) && reg_is ss 10 (SOff 2 (-40)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (fst p)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Definition shapeC (ss : sstate) : bool :=
(ss_pc ss =? MC_RSTOP) && reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 18 0) && reg_is ss 12 (SOff 9 0) && reg_is ss 1 (SLit MC_CALLRET) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27].
Lemma shapeC_ok : shapeC eC = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma munrestrict_mrestrict_same : forall (H : word -> bool) (m : word -> option byte) z, munrestrict H m (mrestrict H m) z = m z.
Proof. intros H m z. unfold munrestrict, mrestrict. destruct (H z); reflexivity. Qed.
Lemma br_cls65_zero : forall E (pn : nat), ew E pn = Z_to_bv 64 0 ->
branch_taken BC_GEU (sv_denot E (SLit 18446744073709551551)) (sv_denot E (SOff pn (-65))) = true.
Proof.
intros E pn Hn. rewrite branch_geu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by lia.
unfold zcanon, M64. change (18446744073709551551 mod 2 ^ 64) with (2 ^ 64 - 65). change ((0 + -65) mod 2 ^ 64) with (2 ^ 64 - 65).
rewrite Z.ltb_irrefl. reflexivity.
Qed.
Lemma br_atom_zero : forall E (pn : nat), ew E pn = Z_to_bv 64 0 ->
branch_taken BC_NE (sv_denot E (SOff pn 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E pn Hn. unfold branch_taken. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. reflexivity.
Qed.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Lemma mc_tail : forall ly S (W : world tfibsegs) regs mem md (regsR : bvmap 5 word) (memR : word -> option byte) mdR x y n,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok tfibsegs W regs mem x n -> src_ok tfibsegs W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) y n) ->
AR tfibsegs B ly S W memR mdR -> same_but_materialized md mdR ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MC_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) memR a = aview tfibsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memR a) ->
getr regsR 10 = w64 x -> getr regsR 11 = w64 y -> getr regsR 12 = w64 n ->
getr regsR 1 = w64 MC_CALLRET -> getr regsR 2 = w64 (spZ regs - 2240) -> getr regsR 19 = w64 MC_RETC ->
getr regsR 3 = getr regs 3 -> getr regsR 4 = getr regs 4 ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 56) 8 274548 ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 64) 8 (bv_unsigned (getr regs 12)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 72) 8 (bv_unsigned (getr regs 11)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 80) 8 (bv_unsigned (getr regs 10)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 88) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 96) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 104) 8 (bv_unsigned (getr regs 21)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 112) 8 (bv_unsigned (getr regs 22)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 120) 8 (bv_unsigned (getr regs 23)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 128) 8 (bv_unsigned (getr regs 24)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 136) 8 (bv_unsigned (getr regs 25)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 144) 8 (bv_unsigned (getr regs 26)) ->
val_mem tfibsegs (mrestrict (w_H W) memR) (spZ regs - 152) 8 (bv_unsigned (getr regs 27)) ->
SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 MC_RSTOP) memR (seg_rom tfibsegs)) mdR)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (x + i) = aview tfibsegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md regsR memR mdR x y n HPRE Hslo2 Hpres2 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy
HARR HsbmR AVR PMR G10 G11 G12 G1 G2 G19 G3 G4 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 V16.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx. unfold src_ok in Hsx, Hsy. unfold ESTACK, MC_SCR in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (H := w_H W) in *.
assert (Hamr : x + n <= 2 ^ 47 - 1 /\ y + n <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamx, Hamy; lia).
assert (RRsp : spZ regsR = sp0 - 2240) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (HPRER : ecall_pre tfibsegs B ly S W regsR memR mdR).
{ split; [exact HARR|]. split; [rewrite G1; apply (ret_ok_lit MC_CALLRET); [unfold MC_CALLRET; lia | reflexivity]|].
split; [rewrite RRsp; replace (sp0 - 2240) with (sp0 + (-140) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
split; [rewrite RRsp; unfold ESTACK; unfold sp0 in *; lia|]. split; [rewrite RRsp; unfold sp0 in *; lia|].
split; [intros a Ha; rewrite RRsp in Ha; unfold ESTACK in Ha; apply PMR; apply Hpres2; unfold sp0 in *; lia|].
split; [rewrite G3; exact Hgp | rewrite G4; exact Htp]. }
pose proof (memcmp_icpt_contract B LAWS TB ly S W regsR memR mdR x y n HPRER G10 G11 G12 Hn Hx Hxn Hy Hyn) as HR.
unfold cfg_at in HR. change (w64 268544) with (Z_to_bv 64 MC_RSTOP) in HR.
eapply SRr_bind.
{ apply HR; clear HR.
- intros a Ha. rewrite RRsp. unfold ESTACK. split; [| pose proof (Hbx a Ha); unfold sp0 in *; lia].
fold H. rewrite AVR; [exact (proj1 (Hsx a Ha)) | lia | pose proof (Hbx a Ha); unfold sp0 in *; lia].
- intros a Ha. rewrite RRsp. unfold ESTACK. split; [| pose proof (Hby a Ha); unfold sp0 in *; lia].
fold H. rewrite AVR; [exact (proj1 (Hsy a Ha)) | lia | pose proof (Hby a Ha); unfold sp0 in *; lia].
- exact Hamx.
- exact Hamy.
- eapply range_addressable_agree; [|exact Hrax]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. fold H. apply AVR; unfold sp0 in *; lia.
- intros Hn0 s' Hs. fold H. rewrite AVR; [exact (Hhx Hn0 s' Hs) | |];
pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (x + n - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(lia)); unfold sp0 in *; lia.
- eapply range_addressable_agree; [|exact Hray]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. fold H. apply AVR; unfold sp0 in *; lia.
- intros Hn0 s' Hs. fold H. rewrite AVR; [exact (Hhy Hn0 s' Hs) | |];
pose proof (shadow_addr_bounds y ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (y + n - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr y) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr y) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (y + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (y + n - 1)) 8 ltac:(lia)); unfold sp0 in *; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & model' & v & -> & HAR2 & AP2 & Hsbm & A10 & HIFFR & Hfr2 & Hpm2).
unfold raZ. rewrite G1. unfold w64 at 1. rewrite unsigned_lit_small by (unfold MC_CALLRET; lia). rewrite RRsp in Hfr2. unfold ESTACK in Hfr2.
unfold cfg_at. change (w64 MC_CALLRET) with (Z_to_bv 64 MC_CALLRET).
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regsR rr) by (intros rr z -> Hcs; exact (AP2 z Hcs)).
assert (AV2' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2240 - 4096 <= a < sp0 - 2240) -> aview tfibsegs H mem2 a = aview tfibsegs H memR a) by (intros a Hr Ha; exact (Hfr2 a Hr Ha)).
assert (VM : forall a (nn : nat) (vv : Z), val_mem tfibsegs (mrestrict H memR) a nn vv -> sp0 - 160 <= a -> a + Z.of_nat nn <= sp0 -> val_mem tfibsegs (mrestrict H mem2) a nn vv).
{ intros a nn vv Hv Hlo Hhi. apply (AF0x.val_mem_ext (mrestrict H memR)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply AV2'; lia. }
assert (HIFF : v = w64 0 <-> forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (x + i) = aview tfibsegs (w_H W) mem (y + i)).
{ rewrite HIFFR. fold H. split; intros HE i Hi; specialize (HE i Hi).
+ rewrite <- (AVR (x + i)), <- (AVR (y + i)); [exact HE | lia | pose proof (Hby (y + i) ltac:(lia)); unfold sp0 in *; lia | lia | pose proof (Hbx (x + i) ltac:(lia)); unfold sp0 in *; lia].
+ rewrite (AVR (x + i)), (AVR (y + i)); [exact HE | lia | pose proof (Hby (y + i) ltac:(lia)); unfold sp0 in *; lia | lia | pose proof (Hbx (x + i) ltac:(lia)); unfold sp0 in *; lia]. }
clear HIFFR.
set (E4 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 12; getr regs 11; getr regs 10; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27]).
assert (R2sp : getr regs2 2 = w64 (sp0 - 2240)) by (rewrite (K2 2%bv 2 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact G2).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2240).
{ subst E4. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R2sp. unfold w64. apply unsigned_lit_small. lia. }
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 MC_CALLRET) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 12; getr regs 11; getr regs 10; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2240) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK : forall (j : nat) (rq : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 12; getr regs 11; getr regs 10; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27] (Z_to_bv 64 0) = getr regs rq -> Z.of_nat j < 16 ->
val_mem tfibsegs (mrestrict H mem2) (sp0 - 2240 + off) 8 (bv_unsigned (getr regs rq)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem2) (sp0 - 2240) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j rq off Hnth Hj8 Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2240) off 8 _ (bv_unsigned (getr regs rq))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs rq)). zside.
- zside.
- exact Hv. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0%nat 1%bv (2232)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2232) with (sp0 - 8) by lia; exact (VM _ _ _ V0 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 1%nat 8%bv (2224)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2224) with (sp0 - 16) by lia; exact (VM _ _ _ V1 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 2%nat 9%bv (2216)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2216) with (sp0 - 24) by lia; exact (VM _ _ _ V2 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 3%nat 18%bv (2208)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2208) with (sp0 - 32) by lia; exact (VM _ _ _ V3 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 4%nat 12%bv (2176)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2176) with (sp0 - 64) by lia; exact (VM _ _ _ V5 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 5%nat 11%bv (2168)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2168) with (sp0 - 72) by lia; exact (VM _ _ _ V6 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 6%nat 10%bv (2160)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2160) with (sp0 - 80) by lia; exact (VM _ _ _ V7 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 7%nat 19%bv (2152)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2152) with (sp0 - 88) by lia; exact (VM _ _ _ V8 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 8%nat 20%bv (2144)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2144) with (sp0 - 96) by lia; exact (VM _ _ _ V9 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 9%nat 21%bv (2136)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2136) with (sp0 - 104) by lia; exact (VM _ _ _ V10 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 10%nat 22%bv (2128)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2128) with (sp0 - 112) by lia; exact (VM _ _ _ V11 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 11%nat 23%bv (2120)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2120) with (sp0 - 120) by lia; exact (VM _ _ _ V12 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 12%nat 24%bv (2112)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2112) with (sp0 - 128) by lia; exact (VM _ _ _ V13 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 13%nat 25%bv (2104)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2104) with (sp0 - 136) by lia; exact (VM _ _ _ V14 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 14%nat 26%bv (2096)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2096) with (sp0 - 144) by lia; exact (VM _ _ _ V15 ltac:(lia) ltac:(cbn; lia))].
+ apply (CK 15%nat 27%bv (2088)); [reflexivity | cbn; lia | replace (sp0 - 2240 + 2088) with (sp0 - 152) by lia; exact (VM _ _ _ V16 ltac:(lia) ltac:(cbn; lia))].
+ eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2240) 2184 8 (SLit 274548) 274548); [reflexivity | zside | zside | replace (sp0 - 2240 + 2184) with (sp0 - 56) by lia; exact (VM _ _ _ V4 ltac:(lia) ltac:(cbn; lia))].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2240) with (spZ regs + (-140) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply SRr_bind; [apply (mc_phase W E4 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_mc tbl_mc_ok Hwx W E4); [exact HS4 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = mem2 z) by (intros z; apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (10%bv : bv 5) Q10. rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21. rreg HS4 (22%bv : bv 5) Q22. rreg HS4 (23%bv : bv 5) Q23.
rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 12; getr regs 11; getr regs 10; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regs2 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs2 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs2 _ ii rr Hnth)).
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regs2 _ 0)). rewrite X32 in Q1.
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
split; [reflexivity|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy model') mat' model'), v.
pose proof (same_but_materialized_frame model' _ (with_vm_backing_same model' mat')) as MF.
assert (AV4 : forall a, aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H mem2 a) by (intros a; apply aview_same; apply MEQ4).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
+   apply (al_frame _ _ LAWS ly S W mem2 model' (ms_mem ms4) _ HAR2).
* intros a Hr Hown. apply AV4.
* intros a Hv. rewrite AV4. exact Hv.
* apply MF. * apply MF. * apply MF.
* exact (AE2y.hs_kept_eq _ _ _ MEQ4).
+
intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl). rewrite (K2 3%bv 3 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact G3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl). rewrite (K2 4%bv 4 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact G4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 7%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 8%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 9%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22. exact (X 10%nat 22%bv eq_refl).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23. exact (X 11%nat 23%bv eq_refl).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24. exact (X 12%nat 24%bv eq_refl).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25. exact (X 13%nat 25%bv eq_refl).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26. exact (X 14%nat 26%bv eq_refl).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27. exact (X 15%nat 27%bv eq_refl).
+ eapply same_but_materialized_trans; [exact HsbmR|]. eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same].
+ rewrite Q10, (Y 10%nat 10%bv eq_refl). exact A10.
+ exact HIFF.
+ intros a Hr Hs. rewrite AV4. rewrite AV2' by (unfold sp0 in *; lia). apply AVR; [exact Hr | unfold sp0 in *; lia].
+ intros a Hp. apply (apresent_same H mem2 (ms_mem ms4) a (MEQ4 _)). apply Hpm2. apply PMR. exact Hp.
Qed.
End f.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x y n : Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis Hslo2 : ly_stk_lo ly + 2 * ESTACK <= spZ regs.
Hypothesis Hpres2 : forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 y.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hx : 0 <= x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis Hy : 0 <= y.
Hypothesis Hyn : y + n <= 2 ^ 63.
Hypothesis Hsx : src_ok tfibsegs W regs mem x n.
Hypothesis Hsy : src_ok tfibsegs W regs mem y n.
Hypothesis Hbx : forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs).
Hypothesis Hby : forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs).
Hypothesis Hamx : amem_range x n.
Hypothesis Hamy : amem_range y n.
Hypothesis Hrax : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis Hhx : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Hypothesis Hray : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y n.
Hypothesis Hhy : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) y n.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Theorem bc_icpt_srr : SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (x + i) = aview tfibsegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
assert (Hamr : x + n <= 2 ^ 47 - 1 /\ y + n <= 2 ^ 47 - 1) by (pose proof Hamx as X1; pose proof Hamy as Y1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X1, Y1; lia).
pose proof AF0x.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a v, val_mem tfibsegs (mrestrict H m) a 8 v ->
(forall b, a <= b < a + 8 -> aview tfibsegs H m' b = aview tfibsegs H m b) -> val_mem tfibsegs (mrestrict H m') a 8 v).
{ intros m m' a v Hv Hf. apply (AF0x.val_mem_ext (mrestrict H m)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply Hf. lia. }
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 y) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (EE12 : ew EE 12 = Z_to_bv 64 n) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_ok B TB mcA_rodata ly S H mem EE (mcA_rodata_chk ly) (proj1 HAR))].
unfold stkA, MC_FRAME. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2240)); [exact EE2 | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply HpresE. subst sp0. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, mcA_rodata, icpt_rodata, ro_region, extent_of_region, MC_FRAME.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE11, EE12, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; first [exact Hal16 | apply Z.mod_1_r | subst sp0; lia]. }
eapply SRr_bind; [apply (mc_phase_to W EE MC_XENT _ _ _ _ _ HS0 r_A)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2240 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_FRAME) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold MC_FRAME in *. lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hsh R21].
apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK. rewrite Hi in Hin. specialize (HK _ Hin). cbn beta in HK. rewrite <- Hi, Nat2Z.id in HK.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK]. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j v off, nth_error SAVEDA j = Some (v, off) -> forall z, sv_denot EE v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 z).
{ intros j v off Hj z Hz Hrg. rewrite forallb_forall in HSV. specialize (HSV (v, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 v _ Hck Hz); zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q20 : getr regs1 20 = w64 x) by (rewrite (RD 20%bv (SOff 10 0) R20); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q18 : getr regs1 18 = w64 y) by (rewrite (RD 18%bv (SOff 11 0) R18); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q9 : getr regs1 9 = w64 n) by (rewrite (RD 9%bv (SOff 12 0) R9); cbn [sv_denot]; rewrite EE12, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q21 : getr regs1 21 = w64 MC_REAL) by (rewrite (RD 21%bv (SLit MC_REAL) R21); reflexivity).
assert (Q19 : getr regs1 19 = w64 MC_RETC) by (rewrite (RD 19%bv (SLit MC_RETC) R19); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 2240)) by (rewrite (RD 2%bv (SOff 2 (-2240)) R2); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q3 : getr regs1 3 = getr regs 3) by (exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia))).
assert (Q4 : getr regs1 4 = getr regs 4) by (exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia))).
assert (R1sp : spZ regs1 = sp0 - 2240) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2240 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2240 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold MC_FRAME. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2240)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2240)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
-
set (E0 := AE2y.Env regs1 []).
assert (E0reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs1 r) by (intros; apply AE2y.Env_reg; assumption).
assert (E0_20 : ew E0 20 = Z_to_bv 64 x) by (rewrite (E0reg 20%nat 20%bv eq_refl); exact Q20).
assert (E0_18 : ew E0 18 = Z_to_bv 64 y) by (rewrite (E0reg 18%nat 18%bv eq_refl); exact Q18).
assert (E0_9 : ew E0 9 = Z_to_bv 64 0) by (rewrite (E0reg 9%nat 9%bv eq_refl), Q9, Hn0; reflexivity).
assert (HZ0 : st_ok tfibsegs E0 ss0 (restrict H (mkst regs1 (Z_to_bv 64 MC_XENT) (ms_mem ms1) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss0.
apply (st_ok_regs tfibsegs E0 (mkSS MC_XENT sr_atoms [] None (mkFacts facts0 [] [])) _ regs0).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold E0; rewrite (AE2y.Env_reg regs1 _ 21 21%bv eq_refl), Q21; reflexivity) ] |]).
destruct Hr. }
unfold E0, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 (map (Z_to_bv 64) [])) with E0.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_nil.
+ cbn. exact I.
+ split; [|split; exact I]. cbn [f_atoms atoms_ok facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E0_20, E0_18, E0_9, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; first [apply Z.mod_1_r | lia]. }
assert (MZ0 : forall z, ms_mem (mkst regs1 (Z_to_bv 64 MC_XENT) (ms_mem ms1) (seg_rom tfibsegs)) z = ms_mem ms1 z) by (intros z; reflexivity).
eapply SRr_bind; [apply (mc_phase W E0 _ _ _ _ _ HZ0 r_z0_0)|].
cbv beta. intros W01 c01 _ (-> & mz1 & mt1 & -> & HZ1 & HFz1 & _). rewrite ?wvb_wvb in *.
assert (MZ1 : forall z, ms_mem mz1 z = ms_mem ms1 z) by (intros z; rewrite (HFz1 z); [apply MZ0 | intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht]).
clear HFz1 HZ0.
pose proof (st_ok_add_cond_neg tfibsegs E0 _ _ BC_LTU (RG z0_e0 11) (RG z0_e0 9) HZ1 (br_ovf_false E0 20 9 x 0 E0_20 E0_9 ltac:(lia) ltac:(lia))) as HZ1'.
change (neg_bc BC_LTU) with BC_GEU in HZ1'. clear HZ1.
eapply SRr_bind; [apply (mc_phase W E0 _ _ _ _ _ HZ1' r_z0_1)|].
cbv beta. intros W02 c02 _ (-> & mz2 & mt2 & -> & HZ2 & HFz2 & _). rewrite ?wvb_wvb in *.
assert (MZ2 : forall z, ms_mem mz2 z = ms_mem ms1 z) by (intros z; rewrite (HFz2 z); [apply MZ1 | intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht]).
clear HFz2 HZ1'.
pose proof (st_ok_add_cond tfibsegs E0 _ _ BC_GEU (RG z0_e1 11) (RG z0_e1 25) HZ2 (br_cls65_zero E0 9 E0_9)) as HZ2'. clear HZ2.
eapply SRr_bind; [apply (mc_phase W E0 _ _ _ _ _ HZ2' r_z0_2)|].
cbv beta. intros W03 c03 _ (-> & mz3 & mt3 & -> & HZ3 & HFz3 & _). rewrite ?wvb_wvb in *.
assert (MZ3 : forall z, ms_mem mz3 z = ms_mem ms1 z) by (intros z; rewrite (HFz3 z); [apply MZ2 | intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht]).
clear HFz3 HZ2'.
pose proof (st_ok_add_cond_neg tfibsegs E0 _ _ BC_NE (RG z0_e2 9) (SLit 0) HZ3 (br_atom_zero E0 9 E0_9)) as HZ3'.
change (neg_bc BC_NE) with BC_EQ in HZ3'. clear HZ3.
eapply SRr_bind; [apply (mc_phase W E0 _ _ _ _ _ HZ3' r_z0_3)|].
cbv beta. intros W04 c04 _ (-> & mz4 & mt4 & -> & HZ4 & HFz4 & _). rewrite ?wvb_wvb in *.
assert (MZ4 : forall z, ms_mem mz4 z = ms_mem ms1 z) by (intros z; rewrite (HFz4 z); [apply MZ3 | intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht]).
clear HFz4 HZ3'.
pose proof (st_ok_add_cond_neg tfibsegs E0 _ _ BC_LTU (RG z0_e3 11) (RG z0_e3 9) HZ4 (br_ovf_false E0 18 9 y 0 E0_18 E0_9 ltac:(lia) ltac:(lia))) as HZ4'.
change (neg_bc BC_LTU) with BC_GEU in HZ4'. clear HZ4.
eapply SRr_bind; [apply (mc_phase_to W E0 MC_RSTOP _ _ _ _ _ HZ4' r_z0_4)|].
cbv beta. intros W05 c05 _ (-> & mz5 & mt5 & -> & HZ5 & HFz5 & _). rewrite ?wvb_wvb in *.
assert (MZ5 : forall z, ms_mem mz5 z = ms_mem ms1 z) by (intros z; rewrite (HFz5 z); [apply MZ4 | intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht]).
clear HFz5.
assert (SH0 : (ss_pc z0_e4 =? MC_RSTOP) && reg_is z0_e4 10 (SOff 20 0) && reg_is z0_e4 11 (SOff 18 0) && reg_is z0_e4 12 (SOff 9 0) && reg_is z0_e4 1 (SLit MC_CALLRET) &&
reg_is z0_e4 2 (SOff 2 0) && reg_is z0_e4 19 (SOff 19 0) && reg_is z0_e4 3 (SOff 3 0) && reg_is z0_e4 4 (SOff 4 0) = true) by (vm_compute; reflexivity).
apply andb_prop in SH0 as [SH0 Z4]. apply andb_prop in SH0 as [SH0 Z3]. apply andb_prop in SH0 as [SH0 Z19]. apply andb_prop in SH0 as [SH0 Z2].
apply andb_prop in SH0 as [SH0 Z1]. apply andb_prop in SH0 as [SH0 Z12]. apply andb_prop in SH0 as [SH0 Z11]. apply andb_prop in SH0 as [Zpc Z10]. apply Z.eqb_eq in Zpc.
assert (RDZ : forall (r : bv 5) v, reg_is z0_e4 (bv_unsigned r) v = true -> getr (ms_regs mz5) r = sv_denot E0 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E0 z0_e4 mz5 r HZ5). }
pose proof (st_ok_restrict_mkst tfibsegs H E0 _ _ HZ5 eq_refl) as Zshape. rewrite Zpc in Zshape. rewrite Zshape.
assert (AVT : forall b, sp0 - 160 <= b < sp0 -> aview tfibsegs H (ms_mem mz5) b = aview tfibsegs H (ms_mem ms1) b) by (intros b Hb; apply aview_same; apply MZ5).
apply (mc_tail B LAWS TB ly S W regs mem md (ms_regs mz5) (ms_mem mz5) (with_vm_backing (m_vm_lazy md1) mt5 md1) x y n HPRE Hslo2 Hpres2 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy).
+ apply (al_frame _ _ LAWS ly S W (ms_mem ms1) md1 (ms_mem mz5) _ HAR1); [intros a _ _; apply aview_same; apply MZ5 | intros a Hv; erewrite aview_same; [exact Hv | apply MZ5] | | | | exact (AE2y.hs_kept_eq _ _ _ MZ5)];
apply (same_but_materialized_frame md1 _ (with_vm_backing_same md1 mt5)).
+ eapply same_but_materialized_trans; [exact MF1 | apply with_vm_backing_same].
+ intros a Hr Ha. unfold MC_SCR in Ha. erewrite aview_same; [| apply MZ5]. apply AV1; [exact Hr | lia].
+ intros a Hp. apply (apresent_same H (ms_mem ms1) (ms_mem mz5) a (MZ5 _)). apply PM1. exact Hp.
+ rewrite (RDZ 10%bv (SOff 20 0) Z10). cbn [sv_denot]. rewrite E0_20, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
+ rewrite (RDZ 11%bv (SOff 18 0) Z11). cbn [sv_denot]. rewrite E0_18, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
+ rewrite (RDZ 12%bv (SOff 9 0) Z12). cbn [sv_denot]. rewrite E0_9, unsigned_lit_small by lia. rewrite Hn0. reflexivity.
+ rewrite (RDZ 1%bv (SLit MC_CALLRET) Z1). reflexivity.
+ rewrite (RDZ 2%bv (SOff 2 0) Z2). cbn [sv_denot]. rewrite (E0reg 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact Q2.
+ rewrite (RDZ 19%bv (SOff 19 0) Z19). cbn [sv_denot]. rewrite (E0reg 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact Q19.
+ rewrite (RDZ 3%bv (SOff 3 0) Z3). cbn [sv_denot]. rewrite (E0reg 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact Q3.
+ rewrite (RDZ 4%bv (SOff 4 0) Z4). cbn [sv_denot]. rewrite (E0reg 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact Q4.
+ apply (VT (ms_mem ms1)); [exact (CK 0%nat (SOff 1 0) (-8) eq_refl (bv_unsigned (getr regs 1)) ltac:(cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 1))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 1%nat (SOff 8 0) (-16) eq_refl (bv_unsigned (getr regs 8)) ltac:(cbn [sv_denot]; rewrite (EEreg 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 8))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 2%nat (SOff 9 0) (-24) eq_refl (bv_unsigned (getr regs 9)) ltac:(cbn [sv_denot]; rewrite (EEreg 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 9))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 3%nat (SOff 18 0) (-32) eq_refl (bv_unsigned (getr regs 18)) ltac:(cbn [sv_denot]; rewrite (EEreg 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 18))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 4%nat (SLit 274548) (-56) eq_refl 274548 eq_refl ltac:(lia)) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 5%nat (SOff 12 0) (-64) eq_refl (bv_unsigned (getr regs 12)) ltac:(cbn [sv_denot]; rewrite (EEreg 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 12))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 6%nat (SOff 11 0) (-72) eq_refl (bv_unsigned (getr regs 11)) ltac:(cbn [sv_denot]; rewrite (EEreg 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 11))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 7%nat (SOff 10 0) (-80) eq_refl (bv_unsigned (getr regs 10)) ltac:(cbn [sv_denot]; rewrite (EEreg 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 10))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 8%nat (SOff 19 0) (-88) eq_refl (bv_unsigned (getr regs 19)) ltac:(cbn [sv_denot]; rewrite (EEreg 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 19))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 9%nat (SOff 20 0) (-96) eq_refl (bv_unsigned (getr regs 20)) ltac:(cbn [sv_denot]; rewrite (EEreg 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 20))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 10%nat (SOff 21 0) (-104) eq_refl (bv_unsigned (getr regs 21)) ltac:(cbn [sv_denot]; rewrite (EEreg 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 21))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 11%nat (SOff 22 0) (-112) eq_refl (bv_unsigned (getr regs 22)) ltac:(cbn [sv_denot]; rewrite (EEreg 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 22))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 12%nat (SOff 23 0) (-120) eq_refl (bv_unsigned (getr regs 23)) ltac:(cbn [sv_denot]; rewrite (EEreg 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 23))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 13%nat (SOff 24 0) (-128) eq_refl (bv_unsigned (getr regs 24)) ltac:(cbn [sv_denot]; rewrite (EEreg 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 24))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 14%nat (SOff 25 0) (-136) eq_refl (bv_unsigned (getr regs 25)) ltac:(cbn [sv_denot]; rewrite (EEreg 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 25))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 15%nat (SOff 26 0) (-144) eq_refl (bv_unsigned (getr regs 26)) ltac:(cbn [sv_denot]; rewrite (EEreg 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 26))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 16%nat (SOff 27 0) (-152) eq_refl (bv_unsigned (getr regs 27)) ltac:(cbn [sv_denot]; rewrite (EEreg 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 27))) | intros b Hb; apply AVT; lia].
-
assert (Hn1 : 1 <= n < 2 ^ 32) by lia.
eapply SRr_bind.
{ apply (mcmpx_check_srr B LAWS TB ly S W regs1 (ms_mem ms1) md1 x n HAR1).
- rewrite R1sp. replace (sp0 - 2240) with (sp0 + (-140) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite R1sp. unfold AE6z.RC_SCR. unfold sp0 in *. lia.
- rewrite R1sp. unfold sp0 in *. lia.
- intros a Ha. rewrite R1sp in Ha. unfold AE6z.RC_SCR in Ha. apply PM1. apply HpresE. unfold sp0 in *. lia.
- exact Q9.
- exact Q20.
- exact Hn1.
- exact Hx.
- exact Hxn.
- exact Hamx.
- eapply range_addressable_agree; [|exact Hrax]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. apply AV1; unfold sp0 in *; lia.
- intros s' Hs. rewrite AV1; [exact (Hhx ltac:(lia) s' Hs) | |];
pose proof (shadow_addr_bounds x ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (x + n - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(lia)); unfold sp0 in *; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & K2 & Hsbm2 & (A10_2 & A9_2 & A25_2) & Hfr2 & Hpm2).
rewrite R1sp in Hfr2. unfold AE6z.RC_SCR in Hfr2.
assert (KK2 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 22 -> z <> 25 -> z <> 26 -> getr regs2 rr = getr regs1 rr).
{ intros z rr -> H1 H2 H3 H5 H6. exact (K2 z H1 H2 H3 H5 H6). }
assert (R2sp : spZ regs2 = sp0 - 2240) by (unfold spZ; rewrite (KK2 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact R1sp).
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2240 - 72 <= a < sp0 - 2240) -> aview tfibsegs H mem2 a = aview tfibsegs H (ms_mem ms1) a) by (intros a Hr Ha; exact (Hfr2 a Hr Ha)).
unfold cfg_at. eapply SRr_bind.
{ apply (mcmpy_check_srr B LAWS TB ly S W regs2 mem2 md2 y n HAR2).
- rewrite R2sp. replace (sp0 - 2240) with (sp0 + (-140) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite R2sp. unfold AE70.RC_SCR. unfold sp0 in *. lia.
- rewrite R2sp. unfold sp0 in *. lia.
- intros a Ha. rewrite R2sp in Ha. unfold AE70.RC_SCR in Ha. apply Hpm2. apply PM1. apply HpresE. unfold sp0 in *. lia.
- exact A9_2.
- rewrite (KK2 18 18%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q18.
- exact A25_2.
- exact Hn1.
- exact Hy.
- exact Hyn.
- exact Hamy.
- eapply range_addressable_agree; [|exact Hray]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. rewrite AV2 by (unfold sp0 in *; lia). apply AV1; unfold sp0 in *; lia.
- intros s' Hs. rewrite AV2, AV1; [exact (Hhy ltac:(lia) s' Hs) | | | |];
pose proof (shadow_addr_bounds y ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (y + n - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr y) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr y) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (y + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (y + n - 1)) 8 ltac:(lia)); unfold sp0 in *; lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & K3 & Hsbm3 & (A10_3 & A9_3) & Hfr3 & Hpm3).
rewrite R2sp in Hfr3. unfold AE70.RC_SCR in Hfr3.
assert (KK3 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 22 -> z <> 25 -> getr regs3 rr = getr regs2 rr).
{ intros z rr -> H1 H2 H3 H5. exact (K3 z H1 H2 H3 H5). }
assert (AV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2240 - 72 <= a < sp0 - 2240) -> aview tfibsegs H mem3 a = aview tfibsegs H mem2 a) by (intros a Hr Ha; exact (Hfr3 a Hr Ha)).
set (EC := AE2y.Env regs3 []).
assert (ECreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EC i = getr regs3 r) by (intros; apply AE2y.Env_reg; assumption).
assert (Q21_3 : getr regs3 21 = w64 MC_REAL).
{ rewrite (KK3 21 21%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite (KK2 21 21%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q21. }
assert (HC0 : st_ok tfibsegs EC ssC (restrict H (mkst regs3 (w64 AE70.RC_END) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC, regsC.
apply (st_ok_regs tfibsegs EC (mkSS MC_YEND sr_atoms [] None (mkFacts [] [] [])) _ regs0).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EC; rewrite (AE2y.Env_reg regs3 _ 21 21%bv eq_refl), Q21_3; reflexivity) ] |]).
destruct Hr. }
unfold EC, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (map (Z_to_bv 64) [])) with EC.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_nil.
+ cbn. exact I.
+ split; [|split; exact I]. cbn. exact I. }
eapply SRr_bind; [apply (mc_phase_to W EC MC_RSTOP _ _ _ _ _ HC0 r_C)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & _). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z, ms_mem ms4 z = mem3 z) by (intros z; rewrite (HF4 z); [reflexivity | intros Hin; destruct (in_wrange_windows EC _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht]).
clear HF4.
pose proof shapeC_ok as SC. unfold shapeC in SC.
apply andb_prop in SC as [SC CK4]. apply andb_prop in SC as [SC C1]. apply andb_prop in SC as [SC C12]. apply andb_prop in SC as [SC C11]. apply andb_prop in SC as [Cpc C10]. apply Z.eqb_eq in Cpc.
assert (RDC : forall (r : bv 5) v, reg_is eC (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EC eC ms4 r HS4). }
assert (RKC : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms4) r = getr regs3 r).
{ intros r i Hi Hin. rewrite forallb_forall in CK4. rewrite Hi in Hin. specialize (CK4 _ Hin). cbn beta in CK4. rewrite <- Hi, Nat2Z.id in CK4.
rewrite (RDC r (SOff i 0)); [| rewrite <- Hi; exact CK4]. cbn [sv_denot]. rewrite (ECreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (st_ok_restrict_mkst tfibsegs H EC _ _ HS4 eq_refl) as Cshape. rewrite Cpc in Cshape. rewrite Cshape.
assert (AVT : forall b, sp0 - 160 <= b < sp0 -> aview tfibsegs H (ms_mem ms4) b = aview tfibsegs H (ms_mem ms1) b).
{ intros b Hb. erewrite aview_same; [| apply MEQ4]. rewrite AV3 by (unfold sp0 in *; lia). apply AV2; unfold sp0 in *; lia. }
apply (mc_tail B LAWS TB ly S W regs mem md (ms_regs ms4) (ms_mem ms4) (with_vm_backing (m_vm_lazy md3) mat4 md3) x y n HPRE Hslo2 Hpres2 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy).
+ apply (al_frame _ _ LAWS ly S W mem3 md3 (ms_mem ms4) _ HAR3); [intros a _ _; apply aview_same; apply MEQ4 | intros a Hv; erewrite aview_same; [exact Hv | apply MEQ4] | | | | exact (AE2y.hs_kept_eq _ _ _ MEQ4)];
apply (same_but_materialized_frame md3 _ (with_vm_backing_same md3 mat4)).
+ eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact Hsbm2|]. eapply same_but_materialized_trans; [exact Hsbm3 | apply with_vm_backing_same].
+ intros a Hr Ha. unfold MC_SCR in Ha. erewrite aview_same; [| apply MEQ4]. rewrite AV3, AV2; [apply AV1; [exact Hr | lia] | exact Hr | lia | exact Hr | lia].
+ intros a Hp. apply (apresent_same H mem3 (ms_mem ms4) a (MEQ4 _)). apply Hpm3. apply Hpm2. apply PM1. exact Hp.
+ rewrite (RDC 10%bv (SOff 10 0) C10). cbn [sv_denot]. rewrite (ECreg 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, A10_3.
rewrite (KK2 20 20%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q20.
+ rewrite (RDC 11%bv (SOff 18 0) C11). cbn [sv_denot]. rewrite (ECreg 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (KK3 18 18%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite (KK2 18 18%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q18.
+ rewrite (RDC 12%bv (SOff 9 0) C12). cbn [sv_denot]. rewrite (ECreg 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact A9_3.
+ rewrite (RDC 1%bv (SLit MC_CALLRET) C1). reflexivity.
+ rewrite (RKC 2%bv 2%nat eq_refl ltac:(cbn; lia)). rewrite (KK3 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite (KK2 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q2.
+ rewrite (RKC 19%bv 19%nat eq_refl ltac:(cbn; lia)). rewrite (KK3 19 19%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite (KK2 19 19%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q19.
+ rewrite (RKC 3%bv 3%nat eq_refl ltac:(cbn; lia)). rewrite (KK3 3 3%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite (KK2 3 3%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q3.
+ rewrite (RKC 4%bv 4%nat eq_refl ltac:(cbn; lia)). rewrite (KK3 4 4%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite (KK2 4 4%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q4.
+ apply (VT (ms_mem ms1)); [exact (CK 0%nat (SOff 1 0) (-8) eq_refl (bv_unsigned (getr regs 1)) ltac:(cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 1))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 1%nat (SOff 8 0) (-16) eq_refl (bv_unsigned (getr regs 8)) ltac:(cbn [sv_denot]; rewrite (EEreg 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 8))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 2%nat (SOff 9 0) (-24) eq_refl (bv_unsigned (getr regs 9)) ltac:(cbn [sv_denot]; rewrite (EEreg 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 9))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 3%nat (SOff 18 0) (-32) eq_refl (bv_unsigned (getr regs 18)) ltac:(cbn [sv_denot]; rewrite (EEreg 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 18))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 4%nat (SLit 274548) (-56) eq_refl 274548 eq_refl ltac:(lia)) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 5%nat (SOff 12 0) (-64) eq_refl (bv_unsigned (getr regs 12)) ltac:(cbn [sv_denot]; rewrite (EEreg 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 12))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 6%nat (SOff 11 0) (-72) eq_refl (bv_unsigned (getr regs 11)) ltac:(cbn [sv_denot]; rewrite (EEreg 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 11))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 7%nat (SOff 10 0) (-80) eq_refl (bv_unsigned (getr regs 10)) ltac:(cbn [sv_denot]; rewrite (EEreg 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 10))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 8%nat (SOff 19 0) (-88) eq_refl (bv_unsigned (getr regs 19)) ltac:(cbn [sv_denot]; rewrite (EEreg 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 19))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 9%nat (SOff 20 0) (-96) eq_refl (bv_unsigned (getr regs 20)) ltac:(cbn [sv_denot]; rewrite (EEreg 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 20))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 10%nat (SOff 21 0) (-104) eq_refl (bv_unsigned (getr regs 21)) ltac:(cbn [sv_denot]; rewrite (EEreg 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 21))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 11%nat (SOff 22 0) (-112) eq_refl (bv_unsigned (getr regs 22)) ltac:(cbn [sv_denot]; rewrite (EEreg 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 22))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 12%nat (SOff 23 0) (-120) eq_refl (bv_unsigned (getr regs 23)) ltac:(cbn [sv_denot]; rewrite (EEreg 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 23))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 13%nat (SOff 24 0) (-128) eq_refl (bv_unsigned (getr regs 24)) ltac:(cbn [sv_denot]; rewrite (EEreg 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 24))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 14%nat (SOff 25 0) (-136) eq_refl (bv_unsigned (getr regs 25)) ltac:(cbn [sv_denot]; rewrite (EEreg 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 25))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 15%nat (SOff 26 0) (-144) eq_refl (bv_unsigned (getr regs 26)) ltac:(cbn [sv_denot]; rewrite (EEreg 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 26))) | intros b Hb; apply AVT; lia].
+ apply (VT (ms_mem ms1)); [exact (CK 16%nat (SOff 27 0) (-152) eq_refl (bv_unsigned (getr regs 27)) ltac:(cbn [sv_denot]; rewrite (EEreg 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) (u64_range (getr regs 27))) | intros b Hb; apply AVT; lia].
Qed.
End g.
Theorem bc_icpt_realizes : forall B, AR_laws tfibsegs B -> TfibSyms B ->
forall ly S (W : world tfibsegs) regs mem md x y n,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok tfibsegs W regs mem x n -> src_ok tfibsegs W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) y n) ->
SRr tfibsegs W (cfg_at tfibsegs 0x41904 regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (x + i) = aview tfibsegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S W regs mem md x y n HPRE Hslo2 Hpres2 G10 G11 G12 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy.
exact (bc_icpt_srr B LAWS TB ly S W regs mem md x y n HPRE Hslo2 Hpres2 G10 G11 G12 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy).
Qed.
Corollary bcmp_icpt_contract : forall B, AR_laws tfibsegs B -> TfibSyms B -> abcmp_realizes tfibsegs B 0x41904.
Proof. intros B LAWS TB. exact (bc_icpt_realizes B LAWS TB). Qed.
End d.
