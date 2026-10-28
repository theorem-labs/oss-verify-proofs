(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q YA0m YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AE2l AF0m AB1w AF0x AE2y AE3i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE04 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2h AE2k AE30 AE31.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA0k YI00 YI01 YI16.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE3e AE3f AE3g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE2i YK0p.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall.
From LinuxProcessSemantics.EquivalenceDefinition Require MeasureLib.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YK0r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition A_GOT_canary : Z := 0x9ec38.
Definition A_canary : Z := 0x5f8fd0.
Definition FWX_BR : Z := 0x9370c.
Definition FWX_MEMCPY_RA : Z := 0x937d4.
Definition FWR_RETPC : Z := 0x938bc.
Definition WV_ECALL : Z := 0x92d74.
Definition WV_BNE : Z := 0x92d7c.
Definition FWR_STK : Z := 4224.
Definition file_chunksB : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit 4)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
YP09.mkChunk 24 (CVal 8 (SLit A_stdio_close)); YP09.mkChunk 32 (CVal 8 (SOff 8 1264)); YP09.mkChunk 40 (CVal 8 (SOff 10 0));
YP09.mkChunk 48 (CVal 8 (SLit 0)); YP09.mkChunk 56 (CVal 8 (SOff 8 240)); YP09.mkChunk 64 (CVal 8 (SLit A_stdio_read)); YP09.mkChunk 72 (CVal 8 (SLit A_stdio_write));
YP09.mkChunk 80 (CVal 8 (SLit A_stdio_seek)); YP09.mkChunk 88 (CVal 8 (SOff 8 240)); YP09.mkChunk 96 (CVal 8 (SLit 1024));
YP09.mkChunk 104 (CVal 8 (SLit 0)); YP09.mkChunk 112 (CVal 8 (SLit 0)); YP09.mkChunk 120 (CVal 4 (SOff 33 0)); YP09.mkChunk 124 (CVal 4 (SLit 0));
YP09.mkChunk 128 (CVal 8 (SLit 0)); YP09.mkChunk 136 (CVal 4 (SLit 4294967295)); YP09.mkChunk 140 (CVal 4 (SLit 4294967295)); YP09.mkChunk 144 (CVal 4 (SLit 4294967295));
YP09.mkChunk 152 (CVal 8 (SLit 0)); YP09.mkChunk 160 (CVal 8 (SLit 0)); YP09.mkChunk 168 (CVal 8 (SLit 0)); YP09.mkChunk 176 (CVal 8 (SLit 0));
YP09.mkChunk 184 (CVal 8 (SLit 0)); YP09.mkChunk 192 (CVal 8 (SLit 0)); YP09.mkChunk 200 (CVal 8 (SLit 0)); YP09.mkChunk 208 (CVal 8 (SLit 0));
YP09.mkChunk 216 (CVal 8 (SLit 0)); YP09.mkChunk 224 (CVal 8 (SLit 0))].
Definition fileRB : YP09.region := YP09.mkRegion (Some 8%nat) 0 232 0 232 file_chunksB.
Definition stk_chunksX : list YP09.chunk :=
[YP09.mkChunk 120 (CVal 8 (SOff 34 0)); YP09.mkChunk 112 (CVal 8 (SOff 35 0)); YP09.mkChunk 104 (CVal 8 (SOff 36 0));
YP09.mkChunk 96 (CVal 8 (SOff 37 0)); YP09.mkChunk 88 (CVal 8 (SOff 38 0)); YP09.mkChunk 80 (CVal 8 (SOff 39 0)); YP09.mkChunk 72 (CVal 8 (SOff 40 0));
YP09.mkChunk 56 (CVal 8 (SLit 0x93890)); YP09.mkChunk 48 (CVal 8 (SOff 9 0)); YP09.mkChunk 40 (CVal 8 (SLit 1));
YP09.mkChunk 32 (CVal 8 (SOff 9 0)); YP09.mkChunk 24 (CVal 8 (SOff 8 0)); YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 8 (CVal 8 (SOff 40 0))].
Definition stkX : YP09.region := YP09.mkRegion (Some 2%nat) (128 - FWR_STK) 128 (128 - FWR_STK) 128 stk_chunksX.
Definition canR : list YP09.region :=
[YP09.mkRegion None A_GOT_canary (A_GOT_canary + 8) 0 0 [YP09.mkChunk A_GOT_canary (CVal 8 (SLit A_canary))];
YP09.mkRegion None A_canary (A_canary + 8) 0 0 [YP09.mkChunk A_canary (CVal 8 (SOff 32 0))]].
Definition factsX : list (nat * afact) :=
[(2%nat, mkAF (2^43) (2^47) 4); (8%nat, mkAF 4096 (2^47) 4); (18%nat, mkAF 0 (2^47) 0); (9%nat, mkAF 1 (2^30) 0);
(10%nat, mkAF 4096 (2^47) 0); (33%nat, mkAF 0 (2^31-1) 0); (11%nat, mkAF 0 (2^47) 0)].
Definition ssX : sstate := mkSS FWX_BR sr_atoms ([stkX; fileRB] ++ canR) None (mkFacts factsX [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tfibmusl_tbl FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (n : N) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n' e => N.eqb n' n && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (i : nat) (off : Z) (n : N) (v : sv) : bool :=
match nth_error (ss_mem ss) i with Some r => existsb (chunk_is off n v) (YP09.r_chunks r) | None => false end.
Definition hdr_svs (wp : sv) : list (Z * N * sv) :=
[(0, 4%N, SLit 4); (8, 8%N, SLit 0); (16, 8%N, SLit 0); (24, 8%N, SLit A_stdio_close); (32, 8%N, SOff 8 1264); (40, 8%N, wp); (48, 8%N, SLit 0); (56, 8%N, SOff 8 240);
(64, 8%N, SLit A_stdio_read); (72, 8%N, SLit A_stdio_write); (80, 8%N, SLit A_stdio_seek); (88, 8%N, SOff 8 240); (96, 8%N, SLit 1024); (104, 8%N, SLit 0); (112, 8%N, SLit 0);
(120, 4%N, SOff 33 0); (124, 4%N, SLit 0); (128, 8%N, SLit 0); (136, 4%N, SLit 4294967295); (140, 4%N, SLit 4294967295); (144, 4%N, SLit 4294967295);
(152, 8%N, SLit 0); (160, 8%N, SLit 0); (168, 8%N, SLit 0); (176, 8%N, SLit 0); (184, 8%N, SLit 0); (192, 8%N, SLit 0); (200, 8%N, SLit 0); (208, 8%N, SLit 0); (216, 8%N, SLit 0); (224, 8%N, SLit 0)].
Definition hdr_has (ss : sstate) (i : nat) (wp : sv) : bool := forallb (fun c => has_chunk ss i (fst (fst c)) (snd (fst c)) (snd c)) (hdr_svs wp).
Definition condFit : acond := mkAC BC_GEU (SOff 11 0) (SOff 9 0).
Definition condNoFit : acond := mkAC BC_LTU (SOff 11 0) (SOff 9 0).
Definition condEmpty : acond := mkAC BC_EQ (SOff 10 0) (SOff 8 240).
Definition condPend : acond := mkAC BC_NE (SOff 10 0) (SOff 8 240).
Definition skel_is (r : YP09.region) (b : option nat) (lo hi wlo whi : Z) : bool :=
obase_eqb (YP09.r_base r) b && (YP09.r_lo r =? lo) && (YP09.r_hi r =? hi) && (YP09.r_wlo r =? wlo) && (YP09.r_whi r =? whi).
Lemma skel_is_sound : forall r b lo hi wlo whi, skel_is r b lo hi wlo whi = true ->
YP09.r_base r = b /\ YP09.r_lo r = lo /\ YP09.r_hi r = hi /\ YP09.r_wlo r = wlo /\ YP09.r_whi r = whi.
Proof.
intros r b lo hi wlo whi Hs. unfold skel_is in Hs. apply andb_prop in Hs as [Hs E5]. apply andb_prop in Hs as [Hs E4]. apply andb_prop in Hs as [Hs E3]. apply andb_prop in Hs as [E1 E2].
apply obase_eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. apply Z.eqb_eq in E4. apply Z.eqb_eq in E5. repeat split; assumption.
Qed.
Definition skels_X (ss : sstate) : bool :=
match ss_mem ss with [r0; r1; r2; r3] =>
skel_is r0 (Some 2%nat) (128 - FWR_STK) 128 (128 - FWR_STK) 128 && skel_is r1 (Some 8%nat) 0 232 0 232 &&
skel_is r2 None A_GOT_canary (A_GOT_canary + 8) 0 0 && skel_is r3 None A_canary (A_canary + 8) 0 0
| _ => false end.
Definition eFit : sstate := Eval vm_compute in fst (RUN (add_cond ssX condFit)).
Lemma r_Fit : RUN (add_cond ssX condFit) = (eFit, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition shapeFit (ss : sstate) : bool :=
(ss_pc ss =? MC_ENTRY) && match ss_resv ss with None => true | _ => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 18 0) && reg_is ss 12 (SOff 9 0) && reg_is ss 1 (SLit FWX_MEMCPY_RA) &&
reg_is ss 2 (SOff 2 0) && reg_is ss 8 (SOff 8 0) && reg_is ss 9 (SOff 9 0) && reg_is ss 18 (SOff 18 0) && reg_is ss 19 (SLit 0) &&
reg_is ss 3 (SOff 3 0) && reg_is ss 4 (SOff 4 0) && skels_X ss.
Lemma shapeFit_ok : shapeFit eFit = true /\ hdr_has eFit 1 (SOff 10 0) = true. Proof. vm_compute. split; reflexivity. Qed.
Definition trim_head (rs : smem) : smem := match rs with r0 :: rest => trim_lo r0 0 :: rest | [] => [] end.
Lemma submem_trim_head : forall rs, submem (trim_head rs) rs.
Proof. intros [|r0 rest]; cbn; [constructor|]. apply submem_keep; [apply subregion_trim_lo | apply submem_refl]. Qed.
Definition memAft : smem := trim_head (ss_mem eFit).
Definition ssAft0 : sstate := ss_after_stretch eFit memAft 44 CLOB FWX_MEMCPY_RA.
Definition ssAft : sstate := mkSS (ss_pc ssAft0) (sr_set (ss_regs ssAft0) 10%bv (SOff 10 0)) (ss_mem ssAft0) (ss_resv ssAft0) (ss_facts ssAft0).
Definition eAft : sstate := Eval vm_compute in fst (RUN ssAft).
Lemma r_Aft : RUN ssAft = (eAft, RS_stopped (SR_jalr (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Definition KEPTR : list Z := [3; 4; 22; 23; 24; 25; 26; 27].
Definition shapeRet (wlo : Z) (wp : sv) (ss : sstate) : bool :=
(ss_pc ss =? FWR_RETPC) && match ss_resv ss with None => true | _ => false end &&
reg_is ss 10 (SOff 9 0) && reg_is ss 1 (SOff 34 0) && reg_is ss 2 (SOff 2 128) &&
reg_is ss 8 (SOff 35 0) && reg_is ss 9 (SOff 36 0) && reg_is ss 18 (SOff 37 0) && reg_is ss 19 (SOff 38 0) && reg_is ss 20 (SOff 39 0) && reg_is ss 21 (SOff 40 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTR &&
has_chunk ss 1 40 8 wp && has_chunk ss 1 32 8 (SOff 8 1264) && has_chunk ss 1 56 8 (SOff 8 240) && has_chunk ss 1 136 4 (SLit 4294967295) &&
match ss_mem ss with r0 :: r1 :: _ =>
obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? wlo) && (YP09.r_whi r0 =? 128) &&
obase_eqb (YP09.r_base r1) (Some 8%nat) && (YP09.r_wlo r1 =? 0) && (YP09.r_whi r1 =? 232)
| _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 2 (ss_mem ss)).
Lemma shapeAft_ok : shapeRet 0 (SAlu ALU_ADD (SOff 9 0) (SOff 10 0)) eAft = true /\ hdr_has eAft 1 (SAlu ALU_ADD (SOff 9 0) (SOff 10 0)) = true.
Proof. vm_compute. split; reflexivity. Qed.
Definition REM : sv := SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 8 0) (SLit 18446744073709551615)) (SLit (-240))) (SOff 9 0)) (SOff 10 0).
Definition LEN0 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 8 0) (SLit (-1))) (SLit (-240))) (SOff 10 0).
Definition IOVX : sv := SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff 10 0) (SOff 8 240))) (SLit 1)) (SLit 0).
Definition condRet : acond := mkAC BC_EQ (SOff 44 0) REM.
Definition ssF (c : acond) : sstate := add_cond (add_cond ssX condNoFit) c.
Definition eF1 : sstate := Eval vm_compute in fst (RUN (ssF condEmpty)).
Definition eF2 : sstate := Eval vm_compute in fst (RUN (ssF condPend)).
Lemma r_F1 : RUN (ssF condEmpty) = (eF1, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Lemma r_F2 : RUN (ssF condPend) = (eF2, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition shapeF (iovoff : Z) (ss : sstate) : bool :=
(ss_pc ss =? WV_ECALL) && match ss_resv ss with None => true | _ => false end &&
reg_is ss 17 (SLit 66) && reg_is ss 10 (SOff 33 0) && reg_is ss 11 (SOff 2 iovoff) && reg_is ss 12 IOVX && reg_is ss 2 (SOff 2 (-48)) &&
skels_X ss && ss_atoms_lt 44 ss.
Lemma shapeF1_ok : shapeF (-24) eF1 = true /\ iov_read1 (ss_mem eF1) (Some 2%nat) (-24) = Some (SOff 18 0, SOff 9 0).
Proof. vm_compute. split; reflexivity. Qed.
Lemma shapeF2_ok : shapeF (-40) eF2 = true /\ (iov_read1 (ss_mem eF2) (Some 2%nat) (-40) = Some (SOff 8 240, LEN0) /\ iov_read1 (ss_mem eF2) (Some 2%nat) (-24) = Some (SOff 18 0, SOff 9 0)).
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition resumeR (e : sstate) : sstate :=
add_cond (resume e (SOff 44 0) (ss_mem e) (mkFacts ((44%nat, mkAF 1 (2^31) 0) :: f_atoms (ss_facts e)) (f_conds (ss_facts e)) (f_alias (ss_facts e)))) condRet.
Definition eR1 : sstate := Eval vm_compute in fst (RUN (resumeR eF1)).
Definition eR2 : sstate := Eval vm_compute in fst (RUN (resumeR eF2)).
Lemma r_R1 : RUN (resumeR eF1) = (eR1, RS_stopped (SR_jalr (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_R2 : RUN (resumeR eF2) = (eR2, RS_stopped (SR_jalr (SOff 34 0))). Proof. vm_compute. reflexivity. Qed.
Lemma shapeR1_ok : shapeRet (128 - FWR_STK) (SOff 8 240) eR1 = true /\ hdr_has eR1 1 (SOff 8 240) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma shapeR2_ok : shapeRet (128 - FWR_STK) (SOff 8 240) eR2 = true /\ hdr_has eR2 1 (SOff 8 240) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma chunk_is_sound : forall off n v c, chunk_is off n v c = true -> c = YP09.mkChunk off (CVal n v).
Proof.
intros off n v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma musl_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tfibmusl_tbl FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tfibmusl_tbl tfibmusl_tbl_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma mem_ok_window_apresent : forall (H : word -> bool) E (mem : word -> option byte) rs i r a,
mem_ok tfibsegs E (mrestrict H mem) rs -> nth_error rs i = Some r ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
AF0x.off_img a -> apresent H mem a.
Proof.
intros H E mem rs i r a (_ & Hrs & _) Hi Ha Hhi. apply AF0x.writable_off_apresent; [exact Hhi|].
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & Hw & _).
replace a with (base_val E (YP09.r_base r) + (a - base_val E (YP09.r_base r))) by lia. apply Hw. lia.
Qed.
Definition hdr_cells (f wp fd : Z) : list (Z * N * Z) :=
[(0, 4%N, 4); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, A_stdio_close); (32, 8%N, f + 1264); (40, 8%N, wp); (48, 8%N, 0); (56, 8%N, f + 240);
(64, 8%N, A_stdio_read); (72, 8%N, A_stdio_write); (80, 8%N, A_stdio_seek); (88, 8%N, f + 240); (96, 8%N, 1024); (104, 8%N, 0); (112, 8%N, 0);
(120, 4%N, fd); (124, 4%N, 0); (128, 8%N, 0); (136, 4%N, 4294967295); (140, 4%N, 4294967295); (144, 4%N, 4294967295);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0); (216, 8%N, 0); (224, 8%N, 0)].
Definition hdr_is (m : word -> option byte) (f wp fd : Z) : Prop :=
Forall (fun c => match c with (o, n, v) => val_mem tfibsegs m (f + o) (N.to_nat n) v end) (hdr_cells f wp fd).
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model).
Variables (f fd wpos n src cval : Z) (P bs Wb : list Z).
Let sp0 : Z := spZ regs0.
Let H := w_H W.
Hypothesis HAR : AR tfibsegs B ly S W memX mdX.
Hypothesis Hra0 : YK0s.ret_ok (getr regs0 1).
Hypothesis Hal16 : sp0 mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + FWR_STK <= sp0.
Hypothesis Hshi : sp0 <= ly_stk_hi ly.
Hypothesis HpresE : forall a, sp0 - FWR_STK <= a < sp0 -> apresent H memX a.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Htp : getr regs0 4 = w64 (as_tp B).
Hypothesis X2 : getr regsX 2 = w64 (sp0 - 128).
Hypothesis X3 : getr regsX 3 = getr regs0 3.
Hypothesis X4 : getr regsX 4 = getr regs0 4.
Hypothesis X8 : getr regsX 8 = w64 f.
Hypothesis X9 : getr regsX 9 = w64 n.
Hypothesis X18 : getr regsX 18 = w64 src.
Hypothesis X10 : getr regsX 10 = w64 wpos.
Hypothesis X11 : getr regsX 11 = w64 (f + 1264 - wpos).
Hypothesis XK : forall r, In r KEPTR -> getr regsX (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Definition SAVED0 : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56)].
Hypothesis HF0 : forall j rz off, nth_error SAVED0 j = Some (rz, off) ->
val_mem tfibsegs (mrestrict H memX) (sp0 + off) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 rz))).
Hypothesis HF1 : val_mem tfibsegs (mrestrict H memX) (sp0 - 72) 8 0x93890 /\ val_mem tfibsegs (mrestrict H memX) (sp0 - 80) 8 n /\
val_mem tfibsegs (mrestrict H memX) (sp0 - 88) 8 1 /\ val_mem tfibsegs (mrestrict H memX) (sp0 - 96) 8 n /\
val_mem tfibsegs (mrestrict H memX) (sp0 - 104) 8 f /\ val_mem tfibsegs (mrestrict H memX) (sp0 - 112) 8 (bv_unsigned (getr regs0 20)) /\
val_mem tfibsegs (mrestrict H memX) (sp0 - 120) 8 (bv_unsigned (getr regs0 21)).
Hypothesis HHDR : hdr_is (mrestrict H memX) f wpos fd.
Hypothesis Hwpos : wpos = f + 240 + Z.of_nat (length P).
Hypothesis HP : garr8 tfibsegs (mrestrict H memX) (f + 240) P.
Hypothesis HPlen : Z.of_nat (length P) <= 1024.
Hypothesis Hf0 : 4096 <= f.
Hypothesis Hfhi : f + FILE_BLOCK <= 2 ^ 47.
Hypothesis Hfal : f mod 16 = 0.
Hypothesis Hfd : 0 <= fd < 2 ^ 31.
Hypothesis HBLK : forall a, f <= a < f + FILE_BLOCK -> apresent H memX a /\ ~ aowned B ly S a.
Hypothesis HBstk : f + FILE_BLOCK <= sp0 - FWR_STK \/ sp0 <= f.
Hypothesis HBimg : f + FILE_BLOCK <= TFIB_IMG_LO \/ TFIB_IMG_END <= f.
Hypothesis HBam : amem_range f FILE_BLOCK.
Hypothesis HBra : range_addressable (aview tfibsegs H memX) SHADOW_OFF (f + 240) 1024.
Hypothesis HBhull : shadow_hull_vis (aview tfibsegs H memX) (f + 240) 1024.
Hypothesis HSRC : garr8 tfibsegs (mrestrict H memX) src bs.
Hypothesis Hn : n = Z.of_nat (length bs).
Hypothesis Hn1 : 1 <= n <= 2 ^ 30.
Hypothesis Hsrc0 : 0 <= src.
Hypothesis Hsrchi : src + n <= 2 ^ 47.
Hypothesis HSf : src + n <= f \/ f + FILE_BLOCK <= src.
Hypothesis HSstk : src + n <= sp0 - FWR_STK \/ sp0 <= src.
Hypothesis HSam : amem_range src n.
Hypothesis HSra : range_addressable (aview tfibsegs H memX) SHADOW_OFF src n.
Hypothesis HShull : shadow_hull_vis (aview tfibsegs H memX) src n.
Hypothesis Hcan1 : val_mem tfibsegs (mrestrict H memX) A_GOT_canary 8 A_canary.
Hypothesis Hcan2 : val_mem tfibsegs (mrestrict H memX) A_canary 8 cval.
Hypothesis Hcv : 0 <= cval < 2 ^ 64.
Hypothesis HfdL : fd_lookup (m_fds mdX) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length Wb)))).
Hypothesis HfsL : Fs.fs_lookup (m_fs mdX) sink_path = Some (YE00.bytes Wb).
Hypothesis HSmax : Z.of_nat (length Wb) + Z.of_nat (length P) + n <= SINK_MAX.
Definition POST : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' (Wb' P' : list Z),
c' = cfg_at tfibsegs (raZ regs0) regs' mem' md' /\ AR tfibsegs B ly S W mem' md' /\
aregs_preserved regs0 regs' /\ getr regs' 10 = w64 n /\
m_vmmaps md' = m_vmmaps mdX /\ m_vm_lazy md' = m_vm_lazy mdX /\
os_kept mdX md' /\
Wb' ++ P' = Wb ++ P ++ bs /\ Z.of_nat (length P') <= 1024 /\
hdr_is (mrestrict H mem') f (f + 240 + Z.of_nat (length P')) fd /\
garr8 tfibsegs (mrestrict H mem') (f + 240) P' /\
Fs.fs_lookup (m_fs md') sink_path = Some (YE00.bytes Wb') /\
(Fs.fs_sorted (m_fs mdX) = true -> Fs.fs_sorted (m_fs md') = true) /\
m_fds md' = (if (length Wb' =? length Wb)%nat then m_fds mdX else fd_insert (m_fds mdX) (Z_to_bv 64 fd) (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length Wb'))))) /\
(forall q, q <> sink_path -> Fs.fs_lookup (m_fs md') q = Fs.fs_lookup (m_fs mdX) q) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + FILE_BLOCK) -> ~ (sp0 - FWR_STK <= a < sp0) -> aview tfibsegs H mem' a = aview tfibsegs H memX a) /\
(forall a, apresent H memX a -> apresent H mem' a).
Definition XTRA : list Z := [cval; fd; bv_unsigned (getr regs0 1); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18);
bv_unsigned (getr regs0 19); bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21)].
Let EE : env := AE2y.Env regsX XTRA.
Let msX : machine_state := mkst regsX (Z_to_bv 64 FWX_BR) memX (seg_rom tfibsegs).
Lemma facts0 : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ FILE_BLOCK = 1264 /\ FWR_STK = 4224 /\ 0 <= Z.of_nat (length P) /\ (ly_stk_hi ly <= 2 ^ 47 /\ 17594333495296 + 4224 <= sp0).
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FB : FILE_BLOCK = 1264) by reflexivity. assert (FS : FWR_STK = 4224) by reflexivity. rewrite FB, FS in *. subst sp0.
repeat split; lia.
Qed.
Lemma EE_facts :
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regsX r) /\
(forall j z, nth_error XTRA j = Some z -> ew EE (32 + j) = Z_to_bv 64 z) /\
bv_unsigned (ew EE 2) = sp0 - 128 /\ ew EE 8 = Z_to_bv 64 f /\ ew EE 9 = Z_to_bv 64 n /\ ew EE 18 = Z_to_bv 64 src /\ ew EE 10 = Z_to_bv 64 wpos /\
ew EE 11 = Z_to_bv 64 (f + 1264 - wpos) /\ ew EE 32 = Z_to_bv 64 cval /\ ew EE 33 = Z_to_bv 64 fd /\
bv_unsigned (ew EE 8) = f /\ bv_unsigned (ew EE 10) = wpos.
Proof.
pose proof facts0 as (Hsp & FB & FS & HP0 & _). rewrite FB in *.
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regsX r) by (intros; apply AE2y.Env_reg; assumption).
assert (EEx : forall j z, nth_error XTRA j = Some z -> ew EE (32 + j) = Z_to_bv 64 z) by (intros j z Hj; exact (AE2y.Env_x regsX _ j z Hj)).
split; [exact EEreg|]. split; [exact EEx|].
split; [rewrite (EEreg 2%nat 2%bv eq_refl), X2; apply unsigned_lit_small; lia|].
split; [rewrite (EEreg 8%nat 8%bv eq_refl); exact X8|]. split; [rewrite (EEreg 9%nat 9%bv eq_refl); exact X9|].
split; [rewrite (EEreg 18%nat 18%bv eq_refl); exact X18|]. split; [rewrite (EEreg 10%nat 10%bv eq_refl); exact X10|].
split; [rewrite (EEreg 11%nat 11%bv eq_refl); exact X11|].
split; [exact (EEx 0%nat cval eq_refl)|]. split; [exact (EEx 1%nat fd eq_refl)|].
split; [rewrite (EEreg 8%nat 8%bv eq_refl), X8; apply unsigned_lit_small; lia|].
rewrite (EEreg 10%nat 10%bv eq_refl), X10; apply unsigned_lit_small; lia.
Qed.
Lemma core_entry : st_ok tfibsegs EE ssX (restrict H msX).
Proof.
pose proof facts0 as (Hsp & FB & FS & HP0 & _). rewrite FB in *.
pose proof EE_facts as (EEreg & EEx & EE2 & EE8 & EE9 & EE18 & EE10 & EE11 & EE32 & EE33 & EE8u & EE10u).
destruct HF1 as (C72 & C80 & C88 & C96 & C104 & C112 & C120).
subst msX. rewrite restrict_mkst_fx. unfold ssX. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regsX (map (Z_to_bv 64) XTRA)) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons.
{
unfold stkX, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EE2. unfold FWR_STK.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply AE2y.apresent_writable; apply HpresE; unfold sp0 in *; rewrite FS; lia|].
unfold stk_chunksX.
assert (CKx : forall j off z, nth_error XTRA j = Some z -> 0 <= z < 2 ^ 64 -> val_mem tfibsegs (mrestrict H memX) (sp0 - 128 + off) 8 z ->
YP09.chunk_ok tfibsegs EE (mrestrict H memX) (sp0 - 128) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off z Hj Hz Hv. eapply (chunk_ok_val tfibsegs EE _ (sp0 - 128) off 8 _ z); [cbn [sv_denot]; rewrite (EEx j z Hj), Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact Hv]. }
assert (CKr : forall i (r : bv 5) off z, Z.of_nat i = bv_unsigned r -> getr regsX r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> val_mem tfibsegs (mrestrict H memX) (sp0 - 128 + off) 8 z ->
YP09.chunk_ok tfibsegs EE (mrestrict H memX) (sp0 - 128) (YP09.mkChunk off (CVal 8 (SOff i 0)))).
{ intros i r off z Hi Hr Hz Hv. eapply (chunk_ok_val tfibsegs EE _ (sp0 - 128) off 8 _ z); [cbn [sv_denot]; rewrite (EEreg i r Hi), Hr, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact Hv]. }
assert (CKl : forall off z, 0 <= z < 2 ^ 64 -> val_mem tfibsegs (mrestrict H memX) (sp0 - 128 + off) 8 z ->
YP09.chunk_ok tfibsegs EE (mrestrict H memX) (sp0 - 128) (YP09.mkChunk off (CVal 8 (SLit z)))).
{ intros off z Hz Hv. eapply (chunk_ok_val tfibsegs EE _ (sp0 - 128) off 8 _ z); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia | exact Hv]. }
assert (U0 : forall r : bv 5, 0 <= bv_unsigned (getr regs0 r) < 2 ^ 64) by (intros r; pose proof (u64_range (getr regs0 r)); lia).
apply Forall_cons; [apply (CKx 2%nat 120 _ eq_refl (U0 1%bv)); replace (sp0 - 128 + 120) with (sp0 + -8) by lia; exact (HF0 0%nat 1 (-8) eq_refl)|].
apply Forall_cons; [apply (CKx 3%nat 112 _ eq_refl (U0 8%bv)); replace (sp0 - 128 + 112) with (sp0 + -16) by lia; exact (HF0 1%nat 8 (-16) eq_refl)|].
apply Forall_cons; [apply (CKx 4%nat 104 _ eq_refl (U0 9%bv)); replace (sp0 - 128 + 104) with (sp0 + -24) by lia; exact (HF0 2%nat 9 (-24) eq_refl)|].
apply Forall_cons; [apply (CKx 5%nat 96 _ eq_refl (U0 18%bv)); replace (sp0 - 128 + 96) with (sp0 + -32) by lia; exact (HF0 3%nat 18 (-32) eq_refl)|].
apply Forall_cons; [apply (CKx 6%nat 88 _ eq_refl (U0 19%bv)); replace (sp0 - 128 + 88) with (sp0 + -40) by lia; exact (HF0 4%nat 19 (-40) eq_refl)|].
apply Forall_cons; [apply (CKx 7%nat 80 _ eq_refl (U0 20%bv)); replace (sp0 - 128 + 80) with (sp0 + -48) by lia; exact (HF0 5%nat 20 (-48) eq_refl)|].
apply Forall_cons; [apply (CKx 8%nat 72 _ eq_refl (U0 21%bv)); replace (sp0 - 128 + 72) with (sp0 + -56) by lia; exact (HF0 6%nat 21 (-56) eq_refl)|].
apply Forall_cons; [apply (CKl 56 0x93890 ltac:(lia)); replace (sp0 - 128 + 56) with (sp0 - 72) by lia; exact C72|].
apply Forall_cons; [apply (CKr 9%nat 9%bv 48 n eq_refl X9 ltac:(lia)); replace (sp0 - 128 + 48) with (sp0 - 80) by lia; exact C80|].
apply Forall_cons; [apply (CKl 40 1 ltac:(lia)); replace (sp0 - 128 + 40) with (sp0 - 88) by lia; exact C88|].
apply Forall_cons; [apply (CKr 9%nat 9%bv 32 n eq_refl X9 ltac:(lia)); replace (sp0 - 128 + 32) with (sp0 - 96) by lia; exact C96|].
apply Forall_cons; [apply (CKr 8%nat 8%bv 24 f eq_refl X8 ltac:(lia)); replace (sp0 - 128 + 24) with (sp0 - 104) by lia; exact C104|].
apply Forall_cons; [apply (CKx 7%nat 16 _ eq_refl (U0 20%bv)); replace (sp0 - 128 + 16) with (sp0 - 112) by lia; exact C112|].
apply Forall_cons; [apply (CKx 8%nat 8 _ eq_refl (U0 21%bv)); replace (sp0 - 128 + 8) with (sp0 - 120) by lia; exact C120 | apply Forall_nil]. }
apply Forall_cons.
{
unfold fileRB, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EE8u.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply AE2y.apresent_writable; apply (proj1 (HBLK (f + o) ltac:(lia)))|].
assert (HC : forall o nn v, In (o, nn, v) (hdr_cells f wpos fd) -> val_mem tfibsegs (mrestrict H memX) (f + o) (N.to_nat nn) v).
{ intros o nn v Hin. unfold hdr_is in HHDR. exact (proj1 (Forall_forall _ _) HHDR (o, nn, v) Hin). }
unfold file_chunksB.
repeat (apply Forall_cons; [ eapply (chunk_ok_val tfibsegs _ _ _ _ _ _ _);
[cbn [sv_denot]; rewrite ?EE8, ?EE10, ?EE33, ?Z.add_0_r, ?unsigned_lit_small; [reflexivity | lia ..]
| unfold A_stdio_close, A_stdio_read, A_stdio_write, A_stdio_seek; cbn; lia | cbn; lia
| apply HC; unfold hdr_cells; cbn [In]; repeat (first [left; reflexivity | right])] |]).
apply Forall_nil. }
unfold canR. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_canary, A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ 0 0x9ec38 8 (SLit 0x5f8fd0) 0x5f8fd0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hcan1]. }
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ 0 0x5f8fd0 8 (SOff 32 0) cval); [cbn [sv_denot]; rewrite EE32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hcan2]. }
- apply pairwise_disjoint_of_extents. unfold stkX, fileRB, canR, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N].
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite EE2. rewrite EE8u. unfold A_GOT_canary, A_canary, FWR_STK.
unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsX]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE8, EE9, EE18, EE10, EE11, EE33, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; try lia.
replace (sp0 - 128) with (sp0 + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
Qed.
Lemma hdr_of_st_ok : forall E ss ms i r (wp : sv) (wpv : Z),
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some 8%nat -> bv_unsigned (ew E 8) = f ->
ew E 33 = Z_to_bv 64 fd -> sv_denot E wp = Z_to_bv 64 wpv -> 0 <= wpv < 2 ^ 64 ->
hdr_has ss i wp = true -> hdr_is (mrestrict H (ms_mem ms)) f wpv fd.
Proof.
intros E ss ms i r wp wpv HS Hi Hb E8 E33 Ewp Rwp Hh.
pose proof facts0 as (_ & FB & _).
unfold hdr_is. apply Forall_forall. intros [[o nn] v] Hin.
assert (HX : forall sv, In (o, nn, sv) (hdr_svs wp) -> sv_denot E sv = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (f + o) (N.to_nat nn) v).
{ intros sv Hsv Hd Hr Hn8. unfold hdr_has in Hh. rewrite forallb_forall in Hh. specialize (Hh _ Hsv). cbn [fst snd] in Hh.
unfold has_chunk in Hh. rewrite Hi in Hh. apply existsb_exists in Hh as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs). rewrite Hb in Hcs. cbn [base_val] in Hcs. rewrite E8 in Hcs.
exact (val_of_chunk_ok tfibsegs E _ _ o nn sv v (proj1 (Forall_forall _ _) Hcs _ Hc) Hd Hr Hn8). }
unfold hdr_cells in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <- <-;
eapply HX; [unfold hdr_svs; cbn [In]; repeat (first [left; reflexivity | right])
| cbn [sv_denot]; rewrite ?E33, ?Ewp, ?Z.add_0_r; try reflexivity; rewrite E8 || idtac; try reflexivity; rewrite unsigned_lit_small by lia; reflexivity
| unfold A_stdio_close, A_stdio_read, A_stdio_write, A_stdio_seek; cbn; lia | cbn; lia] |]).
destruct Hin.
Qed.
Lemma frame_AR : forall (memA mem1 : word -> option byte) mdA md1 k,
AR tfibsegs B ly S W memA mdA -> 0 <= k <= 4224 ->
(forall z : word, ~ (sp0 - k <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> mem1 z = memA z) ->
(forall a, sp0 - k <= a < sp0 -> apresent H mem1 a) -> (forall a, f <= a < f + 232 -> apresent H mem1 a) ->
same_but_materialized mdA md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - k <= a < sp0) -> ~ (f <= a < f + 232) -> aview tfibsegs H mem1 a = aview tfibsegs H memA a) /\
(forall a, apresent H memA a -> apresent H mem1 a) /\
AR tfibsegs B ly S W mem1 md1.
Proof.
intros memA mem1 mdA md1 k HARA Hk MEQ PRS PRSh MF.
pose proof facts0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - k <= a < sp0) -> ~ (f <= a < f + 232) -> aview tfibsegs H mem1 a = aview tfibsegs H memA a).
{ intros a Hr Ha Hb. apply aview_same. apply MEQ; rewrite unsigned_lit_small by lia; assumption. }
assert (PM : forall a, apresent H memA a -> apresent H mem1 a).
{ intros a Hp. rewrite (AE2y.apresent_mod _ mem1 a). rewrite (AE2y.apresent_mod _ memA a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - k)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS; lia|]];
(destruct (Z_lt_le_dec a' f) as [L4|L4]; [|destruct (Z_lt_le_dec a' (f + 232)) as [L5|L5]; [apply PRSh; lia|]]);
(apply (apresent_same H memA mem1 a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
split; [exact AV|]. split; [exact PM|].
pose proof (same_but_materialized_frame mdA md1 MF) as (_ & Fmaps & Flazy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Feu).
apply (al_frame _ _ LAWS ly S W memA mdA mem1 _ HARA).
+ intros a Hr Hown. apply AV; [exact Hr| |]. { intros Hs. exact (al_stack _ _ LAWS ly S W memA mdA a HARA ltac:(unfold sp0 in *; lia) Hown). }
intros Hb. exact (proj2 (HBLK a ltac:(lia)) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem1 a). rewrite (AE2y.aview_mod _ memA a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - k)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply AE2y.aview_some_of_apresent; apply PRS; lia|]];
(destruct (Z_lt_le_dec a' f) as [L4|L4]; [|destruct (Z_lt_le_dec a' (f + 232)) as [L5|L5]; [apply AE2y.aview_some_of_apresent; apply PRSh; lia|]]);
(rewrite AV by lia; exact Hv).
+ exact Fmaps.
+ exact Flazy.
+ exact Feu.
+ intros a Hband Hh. pose proof (in_band_rw_u64 a Hband) as Hr. change (w64 a) with (Z_to_bv 64 a) in *.
assert (NP : forall m, ~ apresent H m a) by (intros m [Hn0 _]; unfold H in Hn0; rewrite Hh in Hn0; discriminate).
destruct (Z_lt_le_dec a (sp0 - k)) as [L1|L1]; [|destruct (Z_lt_le_dec a sp0) as [L3|L3]; [exfalso; exact (NP _ (HpresE a ltac:(unfold sp0 in *; rewrite FS; lia)))|]];
(destruct (Z_lt_le_dec a f) as [L4|L4]; [|destruct (Z_lt_le_dec a (f + 232)) as [L5|L5]; [exfalso; exact (NP _ (proj1 (HBLK a ltac:(lia))))|]]);
(apply MEQ; rewrite unsigned_lit_small by lia; lia).
Qed.
Lemma AR_md : forall mem md md', AR tfibsegs B ly S W mem md ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md -> AR tfibsegs B ly S W mem md'.
Proof.
intros mem md md' HARA Hv Hl He. apply (al_frame _ _ LAWS ly S W mem md mem md' HARA); [intros; reflexivity | intros a Ha; exact Ha | exact Hv | exact Hl | exact He | intros; reflexivity].
Qed.
Lemma path_fits : Z.of_nat (length P) + n <= 1024 -> SRr tfibsegs W (mkCfg msX mdX) POST.
Proof.
intros HFIT.
pose proof facts0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_facts as (EEreg & EEx & EE2 & EE8 & EE9 & EE18 & EE10 & EE11 & EE32 & EE33 & EE8u & EE10u).
pose proof AF0x.Hwx_tfa as Hwx.
assert (Hwn : wpos + n <= f + 1264) by (subst wpos; lia).
assert (HS1 : st_ok tfibsegs EE (add_cond ssX condFit) (restrict H msX)).
{ apply st_ok_assume; [exact core_entry|]. unfold condFit. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
rewrite (U_atom EE 11 (f + 1264 - wpos) EE11) by lia. rewrite (U_atom EE 9 n EE9) by lia.
destruct (Z.ltb_spec (f + 1264 - wpos) n); [lia | reflexivity]. }
eapply SRr_bind; [exact (musl_phase W EE _ _ _ msX mdX HS1 r_Fit)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS2 & HF2 & HFr2).
assert (MEQ2 : forall z : word, ~ (sp0 - 4224 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms1 z = memX z).
{ intros z Hz1 Hz2. apply (HF2 z). intros Hin.
destruct (in_wrange_two_b EE (ss_mem (add_cond ssX condFit)) (bv_unsigned z) 2 (128 - FWR_STK) 128 (sp0 - 128) 8 0 232 f ltac:(vm_compute; reflexivity) EE2 EE8u Hin); rewrite ?FS in *; lia. }
clear HF2 HFr2.
pose proof (proj1 shapeFit_ok) as Hsh. pose proof (proj2 shapeFit_ok) as Hhdr1. unfold shapeFit in Hsh.
apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh R4]. apply andb_prop in Hsh as [Hsh R3]. apply andb_prop in Hsh as [Hsh R19].
apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R8]. apply andb_prop in Hsh as [Hsh R2].
apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10].
apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv eFit = None) by (destruct (ss_resv eFit); [discriminate | reflexivity]).
unfold skels_X in Hwin. destruct (ss_mem eFit) as [|r0 [|r1 [|r2 [|r3 [|? ?]]]]] eqn:Hmem; try discriminate Hwin.
apply andb_prop in Hwin as [Hwin K3]. apply andb_prop in Hwin as [Hwin K2]. apply andb_prop in Hwin as [K0 K1].
apply skel_is_sound in K0 as (W0a & RL0 & RH0 & W0b & W0c). apply skel_is_sound in K1 as (W1a & RL1 & RH1 & W1b & W1c).
apply skel_is_sound in K2 as (W2a & RL2 & RH2 & W2b & W2c). apply skel_is_sound in K3 as (W3a & RL3 & RH3 & W3b & W3c).
rewrite FS in W0b, RL0. unfold MC_ENTRY, FWX_MEMCPY_RA in Hpc, R1. unfold A_GOT_canary, A_canary in RL2, RH2, RL3, RH3.
assert (RD : forall (r : bv 5) v, reg_is eFit (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eFit ms1 r HS2). }
set (regs1 := ms_regs ms1) in *.
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS2 Hresv) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape.
set (md1 := with_vm_backing (m_vm_lazy mdX) mat1 mdX) in *.
assert (MF1 : same_but_materialized mdX md1) by (subst md1; apply with_vm_backing_same).
assert (Q10 : getr regs1 10 = w64 wpos) by (rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite EE10, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q11 : getr regs1 11 = w64 src) by (rewrite (RD 11%bv (SOff 18 0) R11); cbn [sv_denot]; rewrite EE18, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q12 : getr regs1 12 = w64 n) by (rewrite (RD 12%bv (SOff 9 0) R12); cbn [sv_denot]; rewrite EE9, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q1 : getr regs1 1 = w64 0x937d4) by (rewrite (RD 1%bv (SLit _) R1); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 128)) by (rewrite (RD 2%bv (SOff 2 0) R2); cbn [sv_denot]; rewrite (EEreg 2%nat 2%bv eq_refl), X2, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is eFit (bv_unsigned r) (SOff i 0) = true -> getr regs1 r = getr regsX r).
{ intros r i Hi Hr. rewrite (RD r (SOff i 0) Hr). cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q3 : getr regs1 3 = w64 (as_gp B)) by (rewrite (RK 3%bv 3%nat eq_refl R3), X3; exact Hgp).
assert (Q4 : getr regs1 4 = w64 (as_tp B)) by (rewrite (RK 4%bv 4%nat eq_refl R4), X4; exact Htp).
assert (Q8 : getr regs1 8 = w64 f) by (rewrite (RK 8%bv 8%nat eq_refl R8); exact X8).
assert (Q9 : getr regs1 9 = w64 n) by (rewrite (RK 9%bv 9%nat eq_refl R9); exact X9).
assert (Q18 : getr regs1 18 = w64 src) by (rewrite (RK 18%bv 18%nat eq_refl R18); exact X18).
assert (R1sp : spZ regs1 = sp0 - 128) by (unfold spZ; rewrite Q2; apply unsigned_lit_small; lia).
assert (PRS1 : forall a, sp0 - 4224 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent_off H EE eFit ms1 0 r0 a HS2 ltac:(rewrite Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PRSh : forall a, f <= a < f + 232 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent_off H EE eFit ms1 1 r1 a HS2 ltac:(rewrite Hmem; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite W1a, W1b, W1c. cbn [base_val]. rewrite EE8u. lia. }
destruct (frame_AR memX (ms_mem ms1) mdX md1 4224 HAR ltac:(lia) MEQ2 PRS1 PRSh MF1) as (AV1 & PM1 & HAR1).
rewrite Hshape. change (mkst regs1 (Z_to_bv 64 0x515d8) (ms_mem ms1) (seg_rom tfibsegs)) with (mkst regs1 (w64 0x515d8) (ms_mem ms1) (seg_rom tfibsegs)).
eapply SRr_bind.
{ apply (memcpy_icpt_realizes B LAWS TB ly S W regs1 (ms_mem ms1) md1 wpos src n).
- split; [exact HAR1|]. split; [rewrite Q1; apply AE2y.ret_ok_lit; [lia | reflexivity]|].
split; [rewrite R1sp; replace (sp0 - 128) with (sp0 + (-8) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
split; [rewrite R1sp; unfold ESTACK; rewrite FS in Hslo; lia|]. split; [rewrite R1sp; lia|].
split; [intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; apply PRS1; lia|]. exact (conj Q3 Q4).
- exact Q10. - exact Q11. - exact Q12. - lia. - lia. - lia.
- intros a Ha. split; [apply AE2y.apresent_writable; apply PM1; apply (proj1 (HBLK a ltac:(lia)))|].
split; [apply (proj2 (HBLK a ltac:(lia)))|]. rewrite R1sp. unfold ESTACK. rewrite FS in HBstk. lia.
- unfold amem_range in *. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
- eapply range_addressable_agree; [| eapply range_addressable_sub; [exact HBra | lia | lia]].
intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (AE2y.shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [Bz1 Bz2]. unfold kLowMemEnd, kHighShadowEnd in Bz1, Bz2.
apply AV1; [lia | destruct Lhi; unfold sp0 in *; lia |]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HBam. lia.
- intros Hn0 s' Hs. rewrite AV1; [apply (HBhull s') | | |];
pose proof (AE2y.shadow_addr_bounds wpos ltac:(unfold kHighMemEnd; lia)) as [B1 B2];
pose proof (AE2y.shadow_addr_bounds (wpos + n - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
pose proof (AE2y.shadow_addr_bounds (f + 240) ltac:(unfold kHighMemEnd; lia)) as [C1 C2];
pose proof (AE2y.shadow_addr_bounds (f + 240 + 1024 - 1) ltac:(unfold kHighMemEnd; lia)) as [D1 D2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2, C1, C2, D1, D2; unfold shadow_addr in *;
pose proof (Z.div_mod (SHADOW_OFF + wpos / 8) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (SHADOW_OFF + wpos / 8) 8 ltac:(lia));
pose proof (Z.div_mod (SHADOW_OFF + (wpos + n - 1) / 8) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (SHADOW_OFF + (wpos + n - 1) / 8) 8 ltac:(lia));
pose proof (Z.div_mod (SHADOW_OFF + (f + 240) / 8) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (SHADOW_OFF + (f + 240) / 8) 8 ltac:(lia));
pose proof (Z.div_mod (SHADOW_OFF + (f + 240 + 1024 - 1) / 8) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (SHADOW_OFF + (f + 240 + 1024 - 1) / 8) 8 ltac:(lia));
pose proof (Z.div_le_mono (f + 240) wpos 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_mono (wpos + n - 1) (f + 240 + 1024 - 1) 8 ltac:(lia) ltac:(lia));
unfold SHADOW_OFF, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; destruct Lhi; unfold sp0 in *; lia.
- assert (SRCeq : forall a, src <= a < src + n -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H memX a).
{ intros a Ha. apply AV1; [lia | rewrite FS in HSstk; lia | lia]. }
split; [lia|]. split; [lia|]. split.
{ intros a Ha. fold H. split; [| rewrite R1sp; unfold ESTACK; rewrite FS in HSstk; lia]. rewrite (SRCeq a Ha).
pose proof (garr8_mbyte tfibsegs _ _ _ (Z.to_nat (a - src)) HSRC ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia. replace (src + (a - src)) with a in Hb by lia.
unfold aview. rewrite Hb. cbn. discriminate. }
split; [lia|]. split; [exact HSam|]. split.
{ eapply range_addressable_agree; [| exact HSra]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (AE2y.shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [Bz1 Bz2]. unfold kLowMemEnd, kHighShadowEnd in Bz1, Bz2.
apply AV1; [lia | destruct Lhi; unfold sp0 in *; lia |]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HBam. lia. }
intros Hn0 s' Hs. rewrite AV1; [apply (HShull s' Hs) | | |];
pose proof (AE2y.shadow_addr_bounds src ltac:(unfold kHighMemEnd; lia)) as [B1 B2];
pose proof (AE2y.shadow_addr_bounds (src + n - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2; unfold shadow_addr in *;
pose proof (Z.div_mod (SHADOW_OFF + src / 8) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (SHADOW_OFF + src / 8) 8 ltac:(lia));
pose proof (Z.div_mod (SHADOW_OFF + (src + n - 1) / 8) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (SHADOW_OFF + (src + n - 1) / 8) 8 ltac:(lia));
unfold SHADOW_OFF, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; destruct Lhi; unfold sp0 in *; lia. }
cbv beta. intros W2' c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HPRES2 & HSBM2 & A10_2 & HCPY & HFR2 & HPM2).
rewrite R1sp in HFR2. unfold ESTACK in HFR2. fold H in HCPY, HFR2, HPM2.
set (E3 := havoc EE 44 (map (getr regs2) CLOB)).
assert (E3old : forall i, (i < 44)%nat -> ew E3 i = ew EE i) by (intros i Hi; subst E3; apply ew_havoc_old; exact Hi).
assert (MB2 : forall a, 0 <= a < 2 ^ 64 -> ~ (wpos <= a < wpos + n) -> ~ (sp0 - 128 - 4096 <= a < sp0 - 128) ->
mbyte tfibsegs (mrestrict H mem2) a = mbyte tfibsegs (mrestrict H (ms_mem ms1)) a).
{ intros a Hr H1 H2. apply AE2y.mbyte_of_aview. exact (HFR2 a Hr H1 H2). }
assert (HS3 : st_ok tfibsegs E3 ssAft (restrict H (mkst regs2 (w64 FWX_MEMCPY_RA) mem2 (seg_rom tfibsegs)))).
{ unfold ssAft. apply st_ok_pin_reg; [| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite (E3old 10%nat ltac:(lia)), EE10, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact A10_2].
unfold ssAft0. rewrite restrict_mkst_fx. change (w64 FWX_MEMCPY_RA) with (Z_to_bv 64 FWX_MEMCPY_RA). subst E3.
change (mrestrict H mem2) with (ms_mem (restrict H (mkst regs2 (w64 0) mem2 (seg_rom tfibsegs)))).
apply (st_ok_after_stretch tfibsegs 44 EE eFit (restrict H ms1) regs2 (ms_mem (restrict H (mkst regs2 (w64 0) mem2 (seg_rom tfibsegs)))) memAft FWX_MEMCPY_RA CLOB HS2 Hresv).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- unfold memAft. apply submem_trim_head.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- intros r Hr. rewrite Hshape. cbn [ms_regs restrict mkst]. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HPRES2. exact Hcs.
- unfold memAft. rewrite Hmem. cbn [trim_head]. rewrite Hshape. cbn [ms_mem restrict mkst].
assert (RKEPT : forall r : YP09.region, (forall a, base_val EE (YP09.r_base r) + YP09.r_lo r <= a < base_val EE (YP09.r_base r) + YP09.r_hi r ->
0 <= a < 2 ^ 64 /\ ~ (wpos <= a < wpos + n) /\ ~ (sp0 - 128 - 4096 <= a < sp0 - 128)) ->
(forall a, base_val EE (YP09.r_base r) + YP09.r_wlo r <= a < base_val EE (YP09.r_base r) + YP09.r_whi r -> apresent H (ms_mem ms1) a) ->
region_kept tfibsegs EE (mrestrict H (ms_mem ms1)) (mrestrict H mem2) r).
{ intros r Hext Hw. split.
- intros a Ha. destruct (Hext a Ha) as (Q0' & Q1' & Q2'). exact (MB2 a Q0' Q1' Q2').
- intros a Ha _. apply AE2y.apresent_writable. apply HPM2. exact (Hw a Ha). }
unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. rewrite FS in HBstk.
apply Forall_cons.
{ apply RKEPT; unfold trim_lo; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite W0a, ?RL0, ?RH0, ?W0b, ?W0c; cbn [base_val]; rewrite EE2;
[intros a Ha; lia | intros a Ha; apply PRS1; lia]. }
apply Forall_cons. { apply RKEPT; rewrite W1a, ?RL1, ?RH1, ?W1b, ?W1c; cbn [base_val]; rewrite EE8u; [intros a Ha; lia | intros a Ha; apply PRSh; lia]. }
apply Forall_cons. { apply RKEPT; rewrite W2a, ?RL2, ?RH2, ?W2b, ?W2c; cbn [base_val]; [intros a Ha; lia | intros a Ha; lia]. }
apply Forall_cons. { apply RKEPT; rewrite W3a, ?RL3, ?RH3, ?W3b, ?W3c; cbn [base_val]; [intros a Ha; lia | intros a Ha; lia]. }
apply Forall_nil. }
assert (E3_2 : bv_unsigned (ew E3 2) = sp0 - 128) by (rewrite (E3old 2%nat ltac:(lia)); exact EE2).
assert (E3_8 : bv_unsigned (ew E3 8) = f) by (rewrite (E3old 8%nat ltac:(lia)); exact EE8u).
unfold cfg_at, raZ. rewrite Q1, unsigned_lit_small by lia. change (w64 0x937d4) with (w64 FWX_MEMCPY_RA).
eapply SRr_bind; [exact (musl_phase W E3 ssAft eAft _ (mkst regs2 (w64 FWX_MEMCPY_RA) mem2 (seg_rom tfibsegs)) md2 HS3 r_Aft)|].
intros W4' c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [ms_mem mkst] in HF4. clear HFr4.
assert (MEQ4 : forall z : word, ~ (sp0 - 128 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms4 z = mem2 z).
{ intros z Hz1 Hz2. apply (HF4 z). intros Hin.
destruct (in_wrange_two_b E3 (ss_mem ssAft) (bv_unsigned z) 2 0 128 (sp0 - 128) 8 0 232 f ltac:(vm_compute; reflexivity) E3_2 E3_8 Hin); lia. }
clear HF4.
pose proof (proj1 shapeAft_ok) as HshA. pose proof (proj2 shapeAft_ok) as HhdrA. unfold shapeRet in HshA.
apply andb_prop in HshA as [HshA Hoth]. apply andb_prop in HshA as [HshA Hsk]. apply andb_prop in HshA as [HshA C136]. apply andb_prop in HshA as [HshA C56].
apply andb_prop in HshA as [HshA C32]. apply andb_prop in HshA as [HshA C40]. apply andb_prop in HshA as [HshA HK4].
apply andb_prop in HshA as [HshA T21]. apply andb_prop in HshA as [HshA T20]. apply andb_prop in HshA as [HshA T19]. apply andb_prop in HshA as [HshA T18].
apply andb_prop in HshA as [HshA T9]. apply andb_prop in HshA as [HshA T8]. apply andb_prop in HshA as [HshA T2]. apply andb_prop in HshA as [HshA T1].
apply andb_prop in HshA as [HshA T10]. apply andb_prop in HshA as [Hpc4 Hrv4]. apply Z.eqb_eq in Hpc4.
assert (Hresv4 : ss_resv eAft = None) by (destruct (ss_resv eAft); [discriminate | reflexivity]).
destruct (ss_mem eAft) as [|q0 [|q1 qrest]] eqn:Hmem4; try discriminate Hsk.
apply andb_prop in Hsk as [Hsk V1c]. apply andb_prop in Hsk as [Hsk V1b]. apply andb_prop in Hsk as [Hsk V1a].
apply andb_prop in Hsk as [Hsk V0c]. apply andb_prop in Hsk as [V0a V0b].
apply obase_eqb_eq in V0a. apply obase_eqb_eq in V1a. apply Z.eqb_eq in V0b. apply Z.eqb_eq in V0c. apply Z.eqb_eq in V1b. apply Z.eqb_eq in V1c.
assert (RD4 : forall (r : bv 5) v, reg_is eAft (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot E3 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E3 eAft ms4 r HS4). }
set (regs4 := ms_regs ms4) in *.
assert (XT : forall (r : bv 5) j (rz : bv 5), reg_is eAft (bv_unsigned r) (SOff (32 + j) 0) = true ->
nth_error XTRA j = Some (bv_unsigned (getr regs0 rz)) -> getr regs4 r = getr regs0 rz).
{ intros r j rz Hr Hj. rewrite (RD4 r _ Hr). cbn [sv_denot]. rewrite (E3old (32 + j)%nat).
- rewrite (EEx j _ Hj), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- assert (Hl : (j < length XTRA)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). unfold XTRA in Hl. cbn in Hl. lia. }
assert (P1 : getr regs4 1 = getr regs0 1) by (apply (XT 1%bv 2%nat 1%bv T1 eq_refl)).
assert (P8 : getr regs4 8 = getr regs0 8) by (apply (XT 8%bv 3%nat 8%bv T8 eq_refl)).
assert (P9 : getr regs4 9 = getr regs0 9) by (apply (XT 9%bv 4%nat 9%bv T9 eq_refl)).
assert (P18 : getr regs4 18 = getr regs0 18) by (apply (XT 18%bv 5%nat 18%bv T18 eq_refl)).
assert (P19 : getr regs4 19 = getr regs0 19) by (apply (XT 19%bv 6%nat 19%bv T19 eq_refl)).
assert (P20 : getr regs4 20 = getr regs0 20) by (apply (XT 20%bv 7%nat 20%bv T20 eq_refl)).
assert (P21 : getr regs4 21 = getr regs0 21) by (apply (XT 21%bv 8%nat 21%bv T21 eq_refl)).
assert (P2 : getr regs4 2 = getr regs0 2).
{ rewrite (RD4 2%bv (SOff 2 128) T2). cbn [sv_denot]. rewrite E3_2. replace (sp0 - 128 + 128) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (P10 : getr regs4 10 = w64 n) by (rewrite (RD4 10%bv (SOff 9 0) T10); cbn [sv_denot]; rewrite (E3old 9%nat ltac:(lia)), EE9, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (PK : forall r, In r KEPTR -> getr regs4 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTR in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK4. specialize (HK4 _ Hin). cbn beta in HK4.
rewrite (RD4 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (E3old (Z.to_nat r) ltac:(lia)), (EEreg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [apply XK; exact Hin|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK4. }
assert (PRS4 : forall a, sp0 - 128 <= a < sp0 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (st_ok_window_apresent_off H E3 eAft ms4 0 q0 a HS4 ltac:(rewrite Hmem4; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite V0a, V0b, V0c. cbn [base_val]. rewrite E3_2. lia. }
assert (PRSh4 : forall a, f <= a < f + 232 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (st_ok_window_apresent_off H E3 eAft ms4 1 q1 a HS4 ltac:(rewrite Hmem4; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite V1a, V1b, V1c. cbn [base_val]. rewrite E3_8. lia. }
assert (MB4 : forall a a', aview tfibsegs H (ms_mem ms4) a' = aview tfibsegs H memX a -> mbyte tfibsegs (mrestrict H (ms_mem ms4)) a' = mbyte tfibsegs (mrestrict H memX) a).
{ intros a a' E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H (ms_mem ms4)) a') as [b'|], (mbyte tfibsegs (mrestrict H memX) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E. }
eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E3); [exact HS4 | exact Hresv4 | rewrite Hpc4; vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse. split; [reflexivity|].
set (md5 := with_vm_backing (m_vm_lazy md2) mat' md2).
assert (MF5 : same_but_materialized mdX md5).
{ apply (same_but_materialized_trans mdX md1 md5 MF1). apply (same_but_materialized_trans md1 md2 md5 HSBM2). subst md5. apply with_vm_backing_same. }
pose proof (same_but_materialized_frame mdX md5 MF5) as (_ & Fmaps & Flazy & _ & _ & _ & _ & _ & Ffds & _ & _ & Ffs & _).
exists regs4, (ms_mem ms4), md5, Wb, (P ++ bs).
split. { unfold cfg_at, raZ. fold regs4. rewrite P1, Hra0. change (w64 (bv_unsigned (getr regs0 1))) with (Z_to_bv 64 (bv_unsigned (getr regs0 1))). rewrite Z_to_bv_bv_unsigned. reflexivity. }
destruct (frame_AR mem2 (ms_mem ms4) md2 md5 128 HAR2 ltac:(lia) MEQ4 PRS4 PRSh4 ltac:(subst md5; apply with_vm_backing_same)) as (AV4 & PM4 & HAR4).
assert (AVX : forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + 1264) -> ~ (sp0 - 4224 <= a < sp0) -> aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H memX a).
{ intros a Hr Hb Hs. rewrite AV4 by lia. rewrite HFR2 by lia. apply AV1; lia. }
split; [exact HAR4|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [exact P2 | exact (PK 3 ltac:(cbn; tauto)) | exact (PK 4 ltac:(cbn; tauto)) | exact P8 | exact P9 |].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ In r KEPTR) by (unfold KEPTR; cbn [In]; lia).
destruct Hc as [-> | [-> | [-> | [-> | Hk]]]]; [exact P18 | exact P19 | exact P20 | exact P21 | exact (PK r Hk)]. }
split; [exact P10|]. split; [exact Fmaps|]. split; [exact Flazy|]. split; [exact (os_kept_sbm _ _ MF5)|]. split; [reflexivity|].
split; [rewrite length_app; lia|].
split.
{ apply (hdr_of_st_ok E3 eAft ms4 1 q1 (SAlu ALU_ADD (SOff 9 0) (SOff 10 0)) (f + 240 + Z.of_nat (length (P ++ bs))) HS4 ltac:(rewrite Hmem4; reflexivity) V1a E3_8).
- rewrite (E3old 33%nat ltac:(lia)). exact EE33.
- rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E3 _)). change (bv_unsigned (sv_denot E3 ?x)) with (U E3 x).
rewrite (AE2y.U_add2 E3 9 10 n wpos); [f_equal; rewrite length_app; lia | rewrite (E3old 9%nat ltac:(lia)); exact EE9 | rewrite (E3old 10%nat ltac:(lia)); exact EE10 | lia | lia | lia].
- rewrite length_app. lia.
- exact HhdrA. }
split.
{ apply garr8_app. split.
- eapply garr8_frame; [exact HP|]. intros a Ha. apply MB4. rewrite ?FS in HBstk. rewrite AV4 by lia. rewrite HFR2 by lia. apply AV1; lia.
- apply (YI01.garr8_copy tfibsegs (mrestrict H memX) _ src). { exact HSRC. }
intros i Hi. apply MB4. rewrite AV4 by lia. replace (f + 240 + Z.of_nat (length P) + i) with (wpos + i) by lia. rewrite (HCPY i ltac:(lia)).
apply AV1; [lia | rewrite FS in HSstk; lia | lia]. }
split; [rewrite Ffs; exact HfsL|]. split; [intros Hso; rewrite Ffs; exact Hso|]. split; [rewrite Nat.eqb_refl; exact Ffds|]. split; [intros q _; rewrite Ffs; reflexivity|].
split; [intros a Hr Hb Hs; apply AVX; [exact Hr | rewrite FB in Hb; exact Hb | rewrite FS in Hs; exact Hs]|].
intros a Hp. apply PM4. apply HPM2. apply PM1. exact Hp.
Qed.
Lemma U_LEN0_REM : U EE LEN0 = Z.of_nat (length P) /\ U EE REM = Z.of_nat (length P) + n.
Proof.
pose proof facts0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_facts as (EEreg & EEx & EE2 & EE8 & EE9 & EE18 & EE10 & EE11 & EE32 & EE33 & EE8u & EE10u).
unfold LEN0, REM. rewrite !U_add_mod, !U_SMd, !U_SLit, (U_atom EE 8 f EE8), (U_atom EE 10 wpos EE10), (U_atom EE 9 n EE9) by lia.
cbn [zmd_raw]. replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity. replace (zcanon 18446744073709551615) with (2 ^ 64 - 1) by reflexivity.
replace (zcanon (-240)) with (2 ^ 64 - 240) by reflexivity. unfold zcanon, M64.
rewrite !Zplus_mod_idemp_l.
split.
- rewrite <- (Z.add_assoc ((f * (2 ^ 64 - 1)) mod 2 ^ 64) (2 ^ 64 - 240) wpos), Zplus_mod_idemp_l.
replace (f * (2 ^ 64 - 1) + (2 ^ 64 - 240 + wpos)) with ((wpos - f - 240) + (f + 1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
- rewrite <- (Z.add_assoc ((f * (2 ^ 64 - 1) + (2 ^ 64 - 240)) mod 2 ^ 64) n wpos), Zplus_mod_idemp_l.
replace (f * (2 ^ 64 - 1) + (2 ^ 64 - 240) + (n + wpos)) with ((wpos - f - 240 + n) + (f + 1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by lia. lia.
Qed.
Lemma path_flush2 : 1024 < Z.of_nat (length P) + n -> P <> [] -> SRr tfibsegs W (mkCfg msX mdX) POST.
Proof.
intros HNF HPne.
pose proof facts0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_facts as (EEreg & EEx & EE2 & EE8 & EE9 & EE18 & EE10 & EE11 & EE32 & EE33 & EE8u & EE10u).
pose proof AF0x.Hwx_tfa as Hwx. pose proof U_LEN0_REM as [UL0 UREM].
assert (HPpos : 0 < Z.of_nat (length P)) by (destruct P as [|x l]; [exfalso; exact (HPne eq_refl) | cbn [length]; lia]).
assert (HSM : SINK_MAX = 2 ^ 62) by reflexivity. rewrite HSM in HSmax.
assert (HS1 : st_ok tfibsegs EE (ssF condPend) (restrict H msX)).
{ unfold ssF. apply st_ok_assume; [apply st_ok_assume; [exact core_entry|]|].
- unfold condNoFit. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (U_atom EE 11 (f + 1264 - wpos) EE11), (U_atom EE 9 n EE9) by lia.
apply Z.ltb_lt. lia.
- unfold condPend. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, (U_atom EE 10 wpos EE10), (U_atom_off EE 8 f 240 EE8) by lia.
destruct (Z.eqb_spec wpos (f + 240)); [lia | reflexivity]. }
eapply SRr_bind; [exact (musl_phase W EE _ _ _ msX mdX HS1 r_F2)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS2 & HF2 & HFr2). clear HFr2.
set (md1 := with_vm_backing (m_vm_lazy mdX) mat1 mdX) in *.
assert (MF1 : same_but_materialized mdX md1) by (subst md1; apply with_vm_backing_same).
pose proof (same_but_materialized_frame mdX md1 MF1) as (_ & F1maps & F1lazy & _ & _ & _ & _ & _ & F1fds & _ & _ & F1fs & _ & _ & _ & _ & F1eu).
pose proof (proj1 shapeF2_ok) as Hsh. pose proof (proj2 shapeF2_ok) as [HIO1 HIO2]. unfold shapeF in Hsh.
apply andb_prop in Hsh as [Hsh Hat]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R12].
apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh R17]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv eF2 = None) by (destruct (ss_resv eF2); [discriminate | reflexivity]).
unfold skels_X in Hwin. destruct (ss_mem eF2) as [|r0 [|r1 [|r2 [|r3 [|? ?]]]]] eqn:Hmem; try discriminate Hwin.
apply andb_prop in Hwin as [Hwin K3]. apply andb_prop in Hwin as [Hwin K2]. apply andb_prop in Hwin as [K0 K1].
apply skel_is_sound in K0 as (W0a & RL0 & RH0 & W0b & W0c). apply skel_is_sound in K1 as (W1a & RL1 & RH1 & W1b & W1c).
rewrite FS in W0b, RL0.
destruct (st_ok_ecall_shape_r tfibsegs H EE eF2 ms1 HS2 Hresv) as (regs1 & mem1 & Hms1 & Hregs & Hmemok & HG).
assert (Hmm : ms_mem ms1 = mem1) by (rewrite Hms1; reflexivity). rewrite Hmm in HF2.
assert (MEQ2 : forall z : word, ~ (sp0 - 4224 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> mem1 z = memX z).
{ intros z Hz1 Hz2. apply (HF2 z). intros Hin.
destruct (in_wrange_two_b EE (ss_mem (ssF condPend)) (bv_unsigned z) 2 (128 - FWR_STK) 128 (sp0 - 128) 8 0 232 f ltac:(vm_compute; reflexivity) EE2 EE8u Hin); rewrite ?FS in *; lia. }
clear HF2.
assert (RD : forall (r : bv 5) v, reg_is eF2 (bv_unsigned r) v = true -> getr regs1 r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply Hregs. }
assert (Q17 : bv_unsigned (getr regs1 17) = 66) by (rewrite (RD 17%bv (SLit 66) R17); reflexivity).
assert (Q10 : getr regs1 10 = Z_to_bv 64 fd) by (rewrite (RD 10%bv (SOff 33 0) R10); cbn [sv_denot]; rewrite EE33, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q11 : getr regs1 11 = Z_to_bv 64 (sp0 - 168)) by (rewrite (RD 11%bv (SOff 2 (-40)) R11); cbn [sv_denot]; rewrite EE2; f_equal; lia).
assert (Q12 : getr regs1 12 = Z_to_bv 64 2).
{ rewrite (RD 12%bv IOVX R12). rewrite denot_lit_U. unfold IOVX. rewrite U_iovcnt, (U_atom EE 10 wpos EE10), (U_atom_off EE 8 f 240 EE8) by lia.
destruct (Z.eqb_spec wpos (f + 240)); [lia | reflexivity]. }
assert (PRS1 : forall a, sp0 - 4224 <= a < sp0 -> apresent H mem1 a).
{ intros a Ha. apply (mem_ok_window_apresent H EE mem1 _ 0 r0 a Hmemok ltac:(rewrite Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PRSh : forall a, f <= a < f + 232 -> apresent H mem1 a).
{ intros a Ha. apply (mem_ok_window_apresent H EE mem1 _ 1 r1 a Hmemok ltac:(rewrite Hmem; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite W1a, W1b, W1c. cbn [base_val]. rewrite EE8u. lia. }
destruct (frame_AR memX mem1 mdX md1 4224 HAR ltac:(lia) MEQ2 PRS1 PRSh MF1) as (AV1 & PM1 & HAR1).
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 4224 <= a < sp0) -> ~ (f <= a < f + 232) -> mbyte tfibsegs (mrestrict H mem1) a = mbyte tfibsegs (mrestrict H memX) a).
{ intros a Hr H1 H2. apply AE2y.mbyte_of_aview. exact (AV1 a Hr H1 H2). }
rewrite FS in HBstk, HSstk.
assert (HP1 : garr8 tfibsegs (mrestrict H mem1) (f + 240) P) by (eapply garr8_frame; [exact HP|]; intros a Ha; apply MB1; lia).
assert (HSRC1 : garr8 tfibsegs (mrestrict H mem1) src bs) by (eapply garr8_frame; [exact HSRC|]; intros a Ha; apply MB1; lia).
destruct (iov_read1_sound tfibsegs EE (mrestrict H mem1) (ss_mem eF2) (Some 2%nat) (-40) _ _ Hmemok ltac:(rewrite Hmem; exact HIO1)) as [M0r L0r].
destruct (iov_read1_sound tfibsegs EE (mrestrict H mem1) (ss_mem eF2) (Some 2%nat) (-24) _ _ Hmemok ltac:(rewrite Hmem; exact HIO2)) as [M1r L1r].
cbn [base_val sv_denot] in M0r, L0r, M1r, L1r. rewrite EE2 in M0r, L0r, M1r, L1r. rewrite EE8u in M0r. rewrite EE18 in M1r. rewrite EE9 in L1r.
rewrite (unsigned_lit_small src), Z.add_0_r in M1r by lia. rewrite (unsigned_lit_small n), Z.add_0_r in L1r by lia.
change (sv_denot EE LEN0) with (Z_to_bv 64 (U EE LEN0)) in L0r || rewrite (denot_lit_U EE LEN0) in L0r. rewrite UL0 in L0r.
replace (sp0 - 128 + -40 + 8) with (sp0 - 160) in L0r by lia. replace (sp0 - 128 + -40) with (sp0 - 168) in M0r by lia.
replace (sp0 - 128 + -24 + 8) with (sp0 - 144) in L1r by lia. replace (sp0 - 128 + -24) with (sp0 - 152) in M1r by lia.
destruct (rdn_restrict_inv W mem1 (sp0 - 168) 8 _ ltac:(lia) ltac:(lia) M0r) as [M0 V0].
destruct (rdn_restrict_inv W mem1 (sp0 - 160) 8 _ ltac:(lia) ltac:(lia) L0r) as [L0 V1].
destruct (rdn_restrict_inv W mem1 (sp0 - 152) 8 _ ltac:(lia) ltac:(lia) M1r) as [M1 V2].
destruct (rdn_restrict_inv W mem1 (sp0 - 144) 8 _ ltac:(lia) ltac:(lia) L1r) as [L1 V3].
pose proof (rdn_of_garr8 tfibsegs (mrestrict H mem1) (f + 240) P HP1) as B0r. pose proof (rdn_of_garr8 tfibsegs (mrestrict H mem1) src bs HSRC1) as B1r.
destruct (rdn_restrict_inv W mem1 (f + 240) (length P) _ ltac:(lia) ltac:(lia) B0r) as [B0 VB0].
destruct (rdn_restrict_inv W mem1 src (length bs) _ ltac:(lia) ltac:(lia) B1r) as [B1 VB1].
clear M0r L0r M1r L1r B0r B1r.
assert (VIOV : vis_range W (sp0 - 168) (sp0 - 136)).
{ intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 160)); [apply V0; lia|]. destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 152)); [apply V1; lia|].
destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 144)); [apply V2; lia | apply V3; lia]. }
rewrite Hms1. apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
assert (HMRW : MAX_RW_COUNT = 0x7ffff000) by reflexivity.
destruct (node_writev_file2_lazy tfibsegs (w_H W) (w_A W) regs1 (Z_to_bv 64 (ss_pc eF2)) mem1 (seg_rom tfibsegs) md1 (Z_to_bv 64 fd) sink_path
(Z_to_bv 64 (Z.of_nat (length Wb))) (bytes Wb) (Z_to_bv 64 (f + 240)) (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 src) (Z_to_bv 64 n)
(bytes P) (bytes bs) HAI Q17) as (Hnode & HAI5 & Hsbm5).
- rewrite F1fds. exact HfdL.
- apply Syscall.fd32_id. rewrite unsigned_lit_small by lia. lia.
- exact Q10.
- exact Q12.
- rewrite Q11. apply ms_read_u64_of_rdn. exact M0.
- rewrite Q11, unsigned_lit_small by lia. apply ms_read_u64_of_rdn. replace (sp0 - 168 + 8) with (sp0 - 160) by lia. exact L0.
- rewrite Q11, unsigned_lit_small by lia. apply ms_read_u64_of_rdn. replace (sp0 - 168 + 16) with (sp0 - 152) by lia. exact M1.
- rewrite Q11, unsigned_lit_small by lia. apply ms_read_u64_of_rdn. replace (sp0 - 168 + 24) with (sp0 - 144) by lia. exact L1.
- apply ms_read_bytes_of_rdn. rewrite word_to_nat_len by lia. exact B0.
- apply ms_read_bytes_of_rdn. rewrite word_to_nat_lit by lia. rewrite Hn, Nat2Z.id. exact B1.
- rewrite Q11. unfold access_okb, TASK_SIZE. rewrite unsigned_lit_small by lia. apply andb_true_intro; split; apply Z.leb_le; lia.
- unfold access_okb, TASK_SIZE. rewrite !unsigned_lit_small by lia. apply andb_true_intro; split; apply Z.leb_le; lia.
- unfold access_okb, TASK_SIZE. rewrite !unsigned_lit_small by lia. apply andb_true_intro; split; apply Z.leb_le; lia.
- rewrite !unsigned_lit_small by lia. rewrite HMRW. lia.
- rewrite F1fs. exact HfsL.
- rewrite !unsigned_lit_small by lia. lia.
- rewrite unsigned_lit_small, bytes_length by lia. unfold rw_bytes_max. lia.
-
unfold writev_copyins. apply ranges_avoid_app; apply (ranges_avoid_of_elems W); intros a m Hin.
+ rewrite Q12, Q11 in Hin. replace (iovcnt32 (Z_to_bv 64 2)) with (Z_to_bv 64 2 : word) in Hin by reflexivity.
destruct (import_iovecs_accesses_in _ (Z_to_bv 64 (sp0 - 168)) a (Z_to_bv 64 2) m ltac:(rewrite unsigned_lit_small by lia; lia) ltac:(rewrite !unsigned_lit_small by lia; lia) Hin) as [-> [i [Hi Hb]]].
rewrite !unsigned_lit_small in Hi, Hb by lia.
apply (range_avoids_of_vis W a 16 (sp0 - 168) (sp0 - 136) VIOV); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.
+ destruct (iov_prefix_accesses_in _ _ _ _ Hin) as [len [Hil Hm]].
destruct Hil as [Heq | [Heq | []]]; injection Heq as E1 E2; subst a len.
* rewrite word_to_nat_len in Hm by lia. apply (range_avoids_of_vis W _ m (f + 240) (f + 240 + Z.of_nat (length P)) VB0); rewrite ?unsigned_lit_small by lia; lia.
* rewrite word_to_nat_lit in Hm by lia. rewrite Hn, Nat2Z.id in Hm. apply (range_avoids_of_vis W _ m src (src + Z.of_nat (length bs)) VB1); rewrite ?unsigned_lit_small by lia; lia.
- cbv zeta in Hnode, HAI5, Hsbm5.
set (m' := with_fds _ (with_fs _ md1)) in *. set (m5 := materialized_succ m' _) in *.
cbn [ms_mem pend_at] in Hnode.
apply (SRr_node tfibsegs W _ unit _ tt _ Hnode); [intros [] _; cbn [cfg_model]; exact HAI5|]. intros [].
set (RET := len_word (bytes P ++ bytes bs)).
assert (HRET : RET = Z_to_bv 64 (Z.of_nat (length P) + n)).
{ subst RET. unfold len_word. f_equal. rewrite length_app, !bytes_length. lia. }
assert (HRETu : bv_unsigned RET = Z.of_nat (length P) + n) by (rewrite HRET; apply unsigned_lit_small; lia).
set (E5 := ewset EE 44 RET).
assert (E5old : forall i, (i < 44)%nat -> ew E5 i = ew EE i) by (intros i Hi; subst E5; apply ew_ewset_other; lia).
assert (E5_44 : ew E5 44 = Z_to_bv 64 (Z.of_nat (length P) + n)) by (subst E5; rewrite ew_ewset_same; exact HRET).
assert (HS5 : st_ok tfibsegs E5 (resumeR eF2) (restrict H (mkst (regupd regs1 10 RET) (v_addi (Z_to_bv 64 (ss_pc eF2)) 4) mem1 (seg_rom tfibsegs)))).
{ unfold resumeR. apply st_ok_assume.
- rewrite restrict_mkst_fx. subst E5.
apply (st_ok_resume_atom tfibsegs 44 (mkAF 1 (2 ^ 31) 0) EE eF2 regs1 (mrestrict H mem1) RET Hregs Hmemok HG Hat); cbn [af_lo af_hi af_al2]; rewrite ?HRETu; [lia | lia |].
change (2 ^ 0) with 1. apply Z.mod_1_r.
- unfold condRet. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (U_atom E5 44 _ E5_44) by lia.
unfold U. rewrite (sv_denot_agree 44 EE E5 REM ltac:(subst E5; apply env_agree_ewset) eq_refl). fold (U EE REM). rewrite UREM. apply Z.eqb_refl. }
assert (E5_2 : bv_unsigned (ew E5 2) = sp0 - 128) by (rewrite (E5old 2%nat ltac:(lia)); exact EE2).
assert (E5_8 : bv_unsigned (ew E5 8) = f) by (rewrite (E5old 8%nat ltac:(lia)); exact EE8u).
assert (HAR5 : AR tfibsegs B ly S W mem1 m5).
{ pose proof (same_but_materialized_frame m' m5 Hsbm5) as (_ & V5 & L5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U5).
assert (V' : m_vmmaps m' = m_vmmaps md1) by (subst m'; apply (proj1 (ledgers_with_fds_fs _ _ md1))).
assert (L' : m_vm_lazy m' = m_vm_lazy md1) by (subst m'; apply (proj1 (proj2 (ledgers_with_fds_fs _ _ md1)))).
apply (AR_md mem1 md1 m5 HAR1); [rewrite V5; exact V' | rewrite L5; exact L' | rewrite U5; unfold eager_used; rewrite V', L'; reflexivity]. }
eapply SRr_bind; [exact (musl_phase W E5 (resumeR eF2) eR2 _ (mkst (regupd regs1 10 RET) (v_addi (Z_to_bv 64 (ss_pc eF2)) 4) mem1 (seg_rom tfibsegs)) m5 HS5 r_R2)|].
intros W6' c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [ms_mem mkst] in HF6. clear HFr6.
assert (MEQ6 : forall z : word, ~ (sp0 - 4224 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms6 z = mem1 z).
{ intros z Hz1 Hz2. apply (HF6 z). intros Hin.
destruct (in_wrange_two_b E5 (ss_mem (resumeR eF2)) (bv_unsigned z) 2 (128 - FWR_STK) 128 (sp0 - 128) 8 0 232 f ltac:(vm_compute; reflexivity) E5_2 E5_8 Hin); rewrite ?FS in *; lia. }
clear HF6.
pose proof (proj1 shapeR2_ok) as HshA. pose proof (proj2 shapeR2_ok) as HhdrA. unfold shapeRet in HshA.
apply andb_prop in HshA as [HshA Hoth]. apply andb_prop in HshA as [HshA Hsk]. apply andb_prop in HshA as [HshA C136]. apply andb_prop in HshA as [HshA C56].
apply andb_prop in HshA as [HshA C32]. apply andb_prop in HshA as [HshA C40]. apply andb_prop in HshA as [HshA HK6].
apply andb_prop in HshA as [HshA T21]. apply andb_prop in HshA as [HshA T20]. apply andb_prop in HshA as [HshA T19]. apply andb_prop in HshA as [HshA T18].
apply andb_prop in HshA as [HshA T9]. apply andb_prop in HshA as [HshA T8]. apply andb_prop in HshA as [HshA T2]. apply andb_prop in HshA as [HshA T1].
apply andb_prop in HshA as [HshA T10]. apply andb_prop in HshA as [Hpc6 Hrv6]. apply Z.eqb_eq in Hpc6.
assert (Hresv6 : ss_resv eR2 = None) by (destruct (ss_resv eR2); [discriminate | reflexivity]).
destruct (ss_mem eR2) as [|q0 [|q1 qrest]] eqn:Hmem6; try discriminate Hsk.
apply andb_prop in Hsk as [Hsk V1c]. apply andb_prop in Hsk as [Hsk V1b]. apply andb_prop in Hsk as [Hsk V1a].
apply andb_prop in Hsk as [Hsk V0c]. apply andb_prop in Hsk as [V0a V0b].
apply obase_eqb_eq in V0a. apply obase_eqb_eq in V1a. apply Z.eqb_eq in V0b. apply Z.eqb_eq in V0c. apply Z.eqb_eq in V1b. apply Z.eqb_eq in V1c. rewrite FS in V0b.
assert (RD6 : forall (r : bv 5) v, reg_is eR2 (bv_unsigned r) v = true -> getr (ms_regs ms6) r = sv_denot E5 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E5 eR2 ms6 r HS6). }
set (regs6 := ms_regs ms6) in *.
assert (XT : forall (r : bv 5) j (rz : bv 5), reg_is eR2 (bv_unsigned r) (SOff (32 + j) 0) = true ->
nth_error XTRA j = Some (bv_unsigned (getr regs0 rz)) -> getr regs6 r = getr regs0 rz).
{ intros r j rz Hr Hj. rewrite (RD6 r _ Hr). cbn [sv_denot]. rewrite (E5old (32 + j)%nat).
- rewrite (EEx j _ Hj), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- assert (Hl : (j < length XTRA)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). unfold XTRA in Hl. cbn in Hl. lia. }
assert (P1 : getr regs6 1 = getr regs0 1) by (apply (XT 1%bv 2%nat 1%bv T1 eq_refl)).
assert (P8 : getr regs6 8 = getr regs0 8) by (apply (XT 8%bv 3%nat 8%bv T8 eq_refl)).
assert (P9 : getr regs6 9 = getr regs0 9) by (apply (XT 9%bv 4%nat 9%bv T9 eq_refl)).
assert (P18 : getr regs6 18 = getr regs0 18) by (apply (XT 18%bv 5%nat 18%bv T18 eq_refl)).
assert (P19 : getr regs6 19 = getr regs0 19) by (apply (XT 19%bv 6%nat 19%bv T19 eq_refl)).
assert (P20 : getr regs6 20 = getr regs0 20) by (apply (XT 20%bv 7%nat 20%bv T20 eq_refl)).
assert (P21 : getr regs6 21 = getr regs0 21) by (apply (XT 21%bv 8%nat 21%bv T21 eq_refl)).
assert (P2 : getr regs6 2 = getr regs0 2).
{ rewrite (RD6 2%bv (SOff 2 128) T2). cbn [sv_denot]. rewrite E5_2. replace (sp0 - 128 + 128) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (P10 : getr regs6 10 = w64 n) by (rewrite (RD6 10%bv (SOff 9 0) T10); cbn [sv_denot]; rewrite (E5old 9%nat ltac:(lia)), EE9, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (PK : forall r, In r KEPTR -> getr regs6 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTR in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK6. specialize (HK6 _ Hin). cbn beta in HK6.
rewrite (RD6 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (E5old (Z.to_nat r) ltac:(lia)), (EEreg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [apply XK; exact Hin|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK6. }
assert (PRS6 : forall a, sp0 - 4224 <= a < sp0 -> apresent H (ms_mem ms6) a).
{ intros a Ha. apply (st_ok_window_apresent_off H E5 eR2 ms6 0 q0 a HS6 ltac:(rewrite Hmem6; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite V0a, V0b, V0c. cbn [base_val]. rewrite E5_2. lia. }
assert (PRSh6 : forall a, f <= a < f + 232 -> apresent H (ms_mem ms6) a).
{ intros a Ha. apply (st_ok_window_apresent_off H E5 eR2 ms6 1 q1 a HS6 ltac:(rewrite Hmem6; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite V1a, V1b, V1c. cbn [base_val]. rewrite E5_8. lia. }
eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E5); [exact HS6 | exact Hresv6 | rewrite Hpc6; vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse. split; [reflexivity|].
set (md7 := with_vm_backing (m_vm_lazy m5) mat' m5).
assert (MF7 : same_but_materialized m' md7).
{ apply (same_but_materialized_trans m' m5 md7 Hsbm5). subst md7. apply with_vm_backing_same. }
pose proof (same_but_materialized_frame m' md7 MF7) as (_ & F7maps & F7lazy & _ & _ & _ & _ & _ & F7fds & _ & _ & F7fs & _).
destruct (frame_AR mem1 (ms_mem ms6) m5 md7 4224 HAR5 ltac:(lia) MEQ6 PRS6 PRSh6 ltac:(subst md7; apply with_vm_backing_same)) as (AV6 & PM6 & HAR7).
exists regs6, (ms_mem ms6), md7, (Wb ++ P ++ bs), [].
split. { unfold cfg_at, raZ. fold regs6. rewrite P1, Hra0. change (w64 (bv_unsigned (getr regs0 1))) with (Z_to_bv 64 (bv_unsigned (getr regs0 1))). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact HAR7|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [exact P2 | exact (PK 3 ltac:(cbn; tauto)) | exact (PK 4 ltac:(cbn; tauto)) | exact P8 | exact P9 |].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ In r KEPTR) by (unfold KEPTR; cbn [In]; lia).
destruct Hc as [-> | [-> | [-> | [-> | Hk]]]]; [exact P18 | exact P19 | exact P20 | exact P21 | exact (PK r Hk)]. }
assert (V' : m_vmmaps m' = m_vmmaps md1) by (subst m'; apply (proj1 (ledgers_with_fds_fs _ _ md1))).
assert (L' : m_vm_lazy m' = m_vm_lazy md1) by (subst m'; apply (proj1 (proj2 (ledgers_with_fds_fs _ _ md1)))).
split; [exact P10|]. split; [rewrite F7maps, V'; exact F1maps|]. split; [rewrite F7lazy, L'; exact F1lazy|].
split; [eapply os_kept_trans; [exact (os_kept_sbm _ _ MF1) | eapply os_kept_trans; [| exact (os_kept_sbm _ _ MF7)]; subst m'; eapply os_kept_trans; [apply os_kept_with_fs | apply os_kept_with_fds]]|].
split; [rewrite app_nil_r; reflexivity|].
split; [cbn; lia|].
split.
{ apply (hdr_of_st_ok E5 eR2 ms6 1 q1 (SOff 8 240) (f + 240 + Z.of_nat (@length Z [])) HS6 ltac:(rewrite Hmem6; reflexivity) V1a E5_8).
- rewrite (E5old 33%nat ltac:(lia)). exact EE33.
- cbn [sv_denot length Z.of_nat]. rewrite E5_8, Z.add_0_r. reflexivity.
- cbn [length Z.of_nat]. lia.
- exact HhdrA. }
split; [apply garr8_nil|].
assert (Hfs7 : m_fs md7 = fs_set (m_fs mdX) sink_path (bytes (Wb ++ P ++ bs))).
{ rewrite F7fs. subst m'. rewrite State.m_fs_with_fds, State.m_fs_with_fs, F1fs. f_equal.
rewrite file_write_append; [rewrite !bytes_app; reflexivity|]. rewrite word_to_nat_len, bytes_length by lia. reflexivity. }
split; [rewrite Hfs7; apply MeasureLib.fs_lookup_set|]. split; [intros Hso; rewrite Hfs7; apply YK0r.fs_set_sorted; exact Hso|].
split.
{ rewrite !length_app. destruct (Nat.eqb_spec (length Wb + (length P + length bs)) (length Wb)) as [Habs|_]; [exfalso; lia|].
rewrite F7fds. subst m'. rewrite State.m_fds_with_fds, F1fds. f_equal. f_equal. f_equal. fold RET.
apply bv_eq. rewrite bv_add_unsigned, HRETu, !unsigned_lit_small by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. rewrite !Nat2Z.inj_add. lia. }
split; [intros q Hq; rewrite Hfs7; apply MeasureLib.fs_lookup_set_other; exact Hq|].
split; [intros a Hr Hb Hs; rewrite FB in Hb; rewrite AV6 by lia; apply AV1; lia|].
intros a Hp. apply PM6. apply PM1. exact Hp.
Qed.
Lemma path_flush1 : 1024 < Z.of_nat (length P) + n -> P = [] -> SRr tfibsegs W (mkCfg msX mdX) POST.
Proof.
intros HNF HP0nil.
pose proof facts0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_facts as (EEreg & EEx & EE2 & EE8 & EE9 & EE18 & EE10 & EE11 & EE32 & EE33 & EE8u & EE10u).
pose proof AF0x.Hwx_tfa as Hwx. pose proof U_LEN0_REM as [UL0 UREM].
assert (HPz : Z.of_nat (length P) = 0) by (rewrite HP0nil; reflexivity).
assert (HSM : SINK_MAX = 2 ^ 62) by reflexivity. rewrite HSM in HSmax.
assert (HS1 : st_ok tfibsegs EE (ssF condEmpty) (restrict H msX)).
{ unfold ssF. apply st_ok_assume; [apply st_ok_assume; [exact core_entry|]|].
- unfold condNoFit. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (U_atom EE 11 (f + 1264 - wpos) EE11), (U_atom EE 9 n EE9) by lia.
apply Z.ltb_lt. lia.
- unfold condEmpty. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (U_atom EE 10 wpos EE10), (U_atom_off EE 8 f 240 EE8) by lia.
apply Z.eqb_eq. lia. }
eapply SRr_bind; [exact (musl_phase W EE _ _ _ msX mdX HS1 r_F1)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS2 & HF2 & HFr2). clear HFr2.
set (md1 := with_vm_backing (m_vm_lazy mdX) mat1 mdX) in *.
assert (MF1 : same_but_materialized mdX md1) by (subst md1; apply with_vm_backing_same).
pose proof (same_but_materialized_frame mdX md1 MF1) as (_ & F1maps & F1lazy & _ & _ & _ & _ & _ & F1fds & _ & _ & F1fs & _ & _ & _ & _ & F1eu).
pose proof (proj1 shapeF1_ok) as Hsh. pose proof (proj2 shapeF1_ok) as HIO2. unfold shapeF in Hsh.
apply andb_prop in Hsh as [Hsh Hat]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R12].
apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh R17]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv eF1 = None) by (destruct (ss_resv eF1); [discriminate | reflexivity]).
unfold skels_X in Hwin. destruct (ss_mem eF1) as [|r0 [|r1 [|r2 [|r3 [|? ?]]]]] eqn:Hmem; try discriminate Hwin.
apply andb_prop in Hwin as [Hwin K3]. apply andb_prop in Hwin as [Hwin K2]. apply andb_prop in Hwin as [K0 K1].
apply skel_is_sound in K0 as (W0a & RL0 & RH0 & W0b & W0c). apply skel_is_sound in K1 as (W1a & RL1 & RH1 & W1b & W1c).
rewrite FS in W0b, RL0.
destruct (st_ok_ecall_shape_r tfibsegs H EE eF1 ms1 HS2 Hresv) as (regs1 & mem1 & Hms1 & Hregs & Hmemok & HG).
assert (Hmm : ms_mem ms1 = mem1) by (rewrite Hms1; reflexivity). rewrite Hmm in HF2.
assert (MEQ2 : forall z : word, ~ (sp0 - 4224 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> mem1 z = memX z).
{ intros z Hz1 Hz2. apply (HF2 z). intros Hin.
destruct (in_wrange_two_b EE (ss_mem (ssF condEmpty)) (bv_unsigned z) 2 (128 - FWR_STK) 128 (sp0 - 128) 8 0 232 f ltac:(vm_compute; reflexivity) EE2 EE8u Hin); rewrite ?FS in *; lia. }
clear HF2.
assert (RD : forall (r : bv 5) v, reg_is eF1 (bv_unsigned r) v = true -> getr regs1 r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply Hregs. }
assert (Q17 : bv_unsigned (getr regs1 17) = 66) by (rewrite (RD 17%bv (SLit 66) R17); reflexivity).
assert (Q10 : getr regs1 10 = Z_to_bv 64 fd) by (rewrite (RD 10%bv (SOff 33 0) R10); cbn [sv_denot]; rewrite EE33, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q11 : getr regs1 11 = Z_to_bv 64 (sp0 - 152)) by (rewrite (RD 11%bv (SOff 2 (-24)) R11); cbn [sv_denot]; rewrite EE2; f_equal; lia).
assert (Q12 : getr regs1 12 = Z_to_bv 64 1).
{ rewrite (RD 12%bv IOVX R12). rewrite denot_lit_U. unfold IOVX. rewrite U_iovcnt, (U_atom EE 10 wpos EE10), (U_atom_off EE 8 f 240 EE8) by lia.
destruct (Z.eqb_spec wpos (f + 240)); [reflexivity | lia]. }
assert (PRS1 : forall a, sp0 - 4224 <= a < sp0 -> apresent H mem1 a).
{ intros a Ha. apply (mem_ok_window_apresent H EE mem1 _ 0 r0 a Hmemok ltac:(rewrite Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PRSh : forall a, f <= a < f + 232 -> apresent H mem1 a).
{ intros a Ha. apply (mem_ok_window_apresent H EE mem1 _ 1 r1 a Hmemok ltac:(rewrite Hmem; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite W1a, W1b, W1c. cbn [base_val]. rewrite EE8u. lia. }
destruct (frame_AR memX mem1 mdX md1 4224 HAR ltac:(lia) MEQ2 PRS1 PRSh MF1) as (AV1 & PM1 & HAR1).
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 4224 <= a < sp0) -> ~ (f <= a < f + 232) -> mbyte tfibsegs (mrestrict H mem1) a = mbyte tfibsegs (mrestrict H memX) a).
{ intros a Hr H1 H2. apply AE2y.mbyte_of_aview. exact (AV1 a Hr H1 H2). }
rewrite FS in HBstk, HSstk.
assert (HSRC1 : garr8 tfibsegs (mrestrict H mem1) src bs) by (eapply garr8_frame; [exact HSRC|]; intros a Ha; apply MB1; lia).
destruct (iov_read1_sound tfibsegs EE (mrestrict H mem1) (ss_mem eF1) (Some 2%nat) (-24) _ _ Hmemok ltac:(rewrite Hmem; exact HIO2)) as [M1r L1r].
cbn [base_val sv_denot] in M1r, L1r. rewrite EE2 in M1r, L1r. rewrite EE18 in M1r. rewrite EE9 in L1r.
rewrite (unsigned_lit_small src), Z.add_0_r in M1r by lia. rewrite (unsigned_lit_small n), Z.add_0_r in L1r by lia.
replace (sp0 - 128 + -24 + 8) with (sp0 - 144) in L1r by lia. replace (sp0 - 128 + -24) with (sp0 - 152) in M1r by lia.
destruct (rdn_restrict_inv W mem1 (sp0 - 152) 8 _ ltac:(lia) ltac:(lia) M1r) as [M1 V2].
destruct (rdn_restrict_inv W mem1 (sp0 - 144) 8 _ ltac:(lia) ltac:(lia) L1r) as [L1 V3].
pose proof (rdn_of_garr8 tfibsegs (mrestrict H mem1) src bs HSRC1) as B1r.
destruct (rdn_restrict_inv W mem1 src (length bs) _ ltac:(lia) ltac:(lia) B1r) as [B1 VB1].
clear M1r L1r B1r.
assert (VIOV : vis_range W (sp0 - 152) (sp0 - 136)).
{ intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 144)); [apply V2; lia | apply V3; lia]. }
rewrite Hms1. apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
assert (HMRW : MAX_RW_COUNT = 0x7ffff000) by reflexivity.
destruct (node_writev_file1_lazy tfibsegs (w_H W) (w_A W) regs1 (Z_to_bv 64 (ss_pc eF1)) mem1 (seg_rom tfibsegs) md1 (Z_to_bv 64 fd) sink_path
(Z_to_bv 64 (Z.of_nat (length Wb))) (bytes Wb) (Z_to_bv 64 src) (Z_to_bv 64 n) (bytes bs) HAI Q17) as (Hnode & HAI5 & Hsbm5).
- rewrite F1fds. exact HfdL.
- apply Syscall.fd32_id. rewrite unsigned_lit_small by lia. lia.
- exact Q10.
- exact Q12.
- rewrite Q11. apply ms_read_u64_of_rdn. exact M1.
- rewrite Q11, unsigned_lit_small by lia. apply ms_read_u64_of_rdn. replace (sp0 - 152 + 8) with (sp0 - 144) by lia. exact L1.
- apply ms_read_bytes_of_rdn. rewrite word_to_nat_lit by lia. rewrite Hn, Nat2Z.id. exact B1.
- rewrite Q11. unfold access_okb, TASK_SIZE. rewrite unsigned_lit_small by lia. apply andb_true_intro; split; apply Z.leb_le; lia.
- unfold access_okb, TASK_SIZE. rewrite !unsigned_lit_small by lia. apply andb_true_intro; split; apply Z.leb_le; lia.
- rewrite !unsigned_lit_small by lia. rewrite HMRW. lia.
- rewrite F1fs. exact HfsL.
- rewrite !unsigned_lit_small by lia. lia.
- rewrite unsigned_lit_small, bytes_length by lia. unfold rw_bytes_max. lia.
-
unfold writev_copyins. apply ranges_avoid_app; apply (ranges_avoid_of_elems W); intros a m Hin.
+ rewrite Q12, Q11 in Hin. replace (iovcnt32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) in Hin by reflexivity.
destruct (import_iovecs_accesses_in _ (Z_to_bv 64 (sp0 - 152)) a (Z_to_bv 64 1) m ltac:(rewrite unsigned_lit_small by lia; lia) ltac:(rewrite !unsigned_lit_small by lia; lia) Hin) as [-> [i [Hi Hb]]].
rewrite !unsigned_lit_small in Hi, Hb by lia.
apply (range_avoids_of_vis W a 16 (sp0 - 152) (sp0 - 136) VIOV); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.
+ destruct (iov_prefix_accesses_in _ _ _ _ Hin) as [len [Hil Hm]].
destruct Hil as [Heq | []]; injection Heq as E1 E2; subst a len.
rewrite word_to_nat_lit in Hm by lia. rewrite Hn, Nat2Z.id in Hm. apply (range_avoids_of_vis W _ m src (src + Z.of_nat (length bs)) VB1); rewrite ?unsigned_lit_small by lia; lia.
- cbv zeta in Hnode, HAI5, Hsbm5.
set (m' := with_fds _ (with_fs _ md1)) in *. set (m5 := materialized_succ m' _) in *.
cbn [ms_mem pend_at] in Hnode.
apply (SRr_node tfibsegs W _ unit _ tt _ Hnode); [intros [] _; cbn [cfg_model]; exact HAI5|]. intros [].
set (RET := len_word (bytes bs)).
assert (HRET : RET = Z_to_bv 64 (Z.of_nat (length P) + n)).
{ subst RET. unfold len_word. f_equal. rewrite !bytes_length. lia. }
assert (HRETu : bv_unsigned RET = Z.of_nat (length P) + n) by (rewrite HRET; apply unsigned_lit_small; lia).
set (E5 := ewset EE 44 RET).
assert (E5old : forall i, (i < 44)%nat -> ew E5 i = ew EE i) by (intros i Hi; subst E5; apply ew_ewset_other; lia).
assert (E5_44 : ew E5 44 = Z_to_bv 64 (Z.of_nat (length P) + n)) by (subst E5; rewrite ew_ewset_same; exact HRET).
assert (HS5 : st_ok tfibsegs E5 (resumeR eF1) (restrict H (mkst (regupd regs1 10 RET) (v_addi (Z_to_bv 64 (ss_pc eF1)) 4) mem1 (seg_rom tfibsegs)))).
{ unfold resumeR. apply st_ok_assume.
- rewrite restrict_mkst_fx. subst E5.
apply (st_ok_resume_atom tfibsegs 44 (mkAF 1 (2 ^ 31) 0) EE eF1 regs1 (mrestrict H mem1) RET Hregs Hmemok HG Hat); cbn [af_lo af_hi af_al2]; rewrite ?HRETu; [lia | lia |].
change (2 ^ 0) with 1. apply Z.mod_1_r.
- unfold condRet. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (U_atom E5 44 _ E5_44) by lia.
unfold U. rewrite (sv_denot_agree 44 EE E5 REM ltac:(subst E5; apply env_agree_ewset) eq_refl). fold (U EE REM). rewrite UREM. apply Z.eqb_refl. }
assert (E5_2 : bv_unsigned (ew E5 2) = sp0 - 128) by (rewrite (E5old 2%nat ltac:(lia)); exact EE2).
assert (E5_8 : bv_unsigned (ew E5 8) = f) by (rewrite (E5old 8%nat ltac:(lia)); exact EE8u).
assert (HAR5 : AR tfibsegs B ly S W mem1 m5).
{ pose proof (same_but_materialized_frame m' m5 Hsbm5) as (_ & V5 & L5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U5).
assert (V' : m_vmmaps m' = m_vmmaps md1) by (subst m'; apply (proj1 (ledgers_with_fds_fs _ _ md1))).
assert (L' : m_vm_lazy m' = m_vm_lazy md1) by (subst m'; apply (proj1 (proj2 (ledgers_with_fds_fs _ _ md1)))).
apply (AR_md mem1 md1 m5 HAR1); [rewrite V5; exact V' | rewrite L5; exact L' | rewrite U5; unfold eager_used; rewrite V', L'; reflexivity]. }
eapply SRr_bind; [exact (musl_phase W E5 (resumeR eF1) eR1 _ (mkst (regupd regs1 10 RET) (v_addi (Z_to_bv 64 (ss_pc eF1)) 4) mem1 (seg_rom tfibsegs)) m5 HS5 r_R1)|].
intros W6' c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [ms_mem mkst] in HF6. clear HFr6.
assert (MEQ6 : forall z : word, ~ (sp0 - 4224 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms6 z = mem1 z).
{ intros z Hz1 Hz2. apply (HF6 z). intros Hin.
destruct (in_wrange_two_b E5 (ss_mem (resumeR eF1)) (bv_unsigned z) 2 (128 - FWR_STK) 128 (sp0 - 128) 8 0 232 f ltac:(vm_compute; reflexivity) E5_2 E5_8 Hin); rewrite ?FS in *; lia. }
clear HF6.
pose proof (proj1 shapeR1_ok) as HshA. pose proof (proj2 shapeR1_ok) as HhdrA. unfold shapeRet in HshA.
apply andb_prop in HshA as [HshA Hoth]. apply andb_prop in HshA as [HshA Hsk]. apply andb_prop in HshA as [HshA C136]. apply andb_prop in HshA as [HshA C56].
apply andb_prop in HshA as [HshA C32]. apply andb_prop in HshA as [HshA C40]. apply andb_prop in HshA as [HshA HK6].
apply andb_prop in HshA as [HshA T21]. apply andb_prop in HshA as [HshA T20]. apply andb_prop in HshA as [HshA T19]. apply andb_prop in HshA as [HshA T18].
apply andb_prop in HshA as [HshA T9]. apply andb_prop in HshA as [HshA T8]. apply andb_prop in HshA as [HshA T2]. apply andb_prop in HshA as [HshA T1].
apply andb_prop in HshA as [HshA T10]. apply andb_prop in HshA as [Hpc6 Hrv6]. apply Z.eqb_eq in Hpc6.
assert (Hresv6 : ss_resv eR1 = None) by (destruct (ss_resv eR1); [discriminate | reflexivity]).
destruct (ss_mem eR1) as [|q0 [|q1 qrest]] eqn:Hmem6; try discriminate Hsk.
apply andb_prop in Hsk as [Hsk V1c]. apply andb_prop in Hsk as [Hsk V1b]. apply andb_prop in Hsk as [Hsk V1a].
apply andb_prop in Hsk as [Hsk V0c]. apply andb_prop in Hsk as [V0a V0b].
apply obase_eqb_eq in V0a. apply obase_eqb_eq in V1a. apply Z.eqb_eq in V0b. apply Z.eqb_eq in V0c. apply Z.eqb_eq in V1b. apply Z.eqb_eq in V1c. rewrite FS in V0b.
assert (RD6 : forall (r : bv 5) v, reg_is eR1 (bv_unsigned r) v = true -> getr (ms_regs ms6) r = sv_denot E5 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E5 eR1 ms6 r HS6). }
set (regs6 := ms_regs ms6) in *.
assert (XT : forall (r : bv 5) j (rz : bv 5), reg_is eR1 (bv_unsigned r) (SOff (32 + j) 0) = true ->
nth_error XTRA j = Some (bv_unsigned (getr regs0 rz)) -> getr regs6 r = getr regs0 rz).
{ intros r j rz Hr Hj. rewrite (RD6 r _ Hr). cbn [sv_denot]. rewrite (E5old (32 + j)%nat).
- rewrite (EEx j _ Hj), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
- assert (Hl : (j < length XTRA)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). unfold XTRA in Hl. cbn in Hl. lia. }
assert (P1 : getr regs6 1 = getr regs0 1) by (apply (XT 1%bv 2%nat 1%bv T1 eq_refl)).
assert (P8 : getr regs6 8 = getr regs0 8) by (apply (XT 8%bv 3%nat 8%bv T8 eq_refl)).
assert (P9 : getr regs6 9 = getr regs0 9) by (apply (XT 9%bv 4%nat 9%bv T9 eq_refl)).
assert (P18 : getr regs6 18 = getr regs0 18) by (apply (XT 18%bv 5%nat 18%bv T18 eq_refl)).
assert (P19 : getr regs6 19 = getr regs0 19) by (apply (XT 19%bv 6%nat 19%bv T19 eq_refl)).
assert (P20 : getr regs6 20 = getr regs0 20) by (apply (XT 20%bv 7%nat 20%bv T20 eq_refl)).
assert (P21 : getr regs6 21 = getr regs0 21) by (apply (XT 21%bv 8%nat 21%bv T21 eq_refl)).
assert (P2 : getr regs6 2 = getr regs0 2).
{ rewrite (RD6 2%bv (SOff 2 128) T2). cbn [sv_denot]. rewrite E5_2. replace (sp0 - 128 + 128) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (P10 : getr regs6 10 = w64 n) by (rewrite (RD6 10%bv (SOff 9 0) T10); cbn [sv_denot]; rewrite (E5old 9%nat ltac:(lia)), EE9, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (PK : forall r, In r KEPTR -> getr regs6 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTR in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK6. specialize (HK6 _ Hin). cbn beta in HK6.
rewrite (RD6 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (E5old (Z.to_nat r) ltac:(lia)), (EEreg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [apply XK; exact Hin|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK6. }
assert (PRS6 : forall a, sp0 - 4224 <= a < sp0 -> apresent H (ms_mem ms6) a).
{ intros a Ha. apply (st_ok_window_apresent_off H E5 eR1 ms6 0 q0 a HS6 ltac:(rewrite Hmem6; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite V0a, V0b, V0c. cbn [base_val]. rewrite E5_2. lia. }
assert (PRSh6 : forall a, f <= a < f + 232 -> apresent H (ms_mem ms6) a).
{ intros a Ha. apply (st_ok_window_apresent_off H E5 eR1 ms6 1 q1 a HS6 ltac:(rewrite Hmem6; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite V1a, V1b, V1c. cbn [base_val]. rewrite E5_8. lia. }
eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E5); [exact HS6 | exact Hresv6 | rewrite Hpc6; vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse. split; [reflexivity|].
set (md7 := with_vm_backing (m_vm_lazy m5) mat' m5).
assert (MF7 : same_but_materialized m' md7).
{ apply (same_but_materialized_trans m' m5 md7 Hsbm5). subst md7. apply with_vm_backing_same. }
pose proof (same_but_materialized_frame m' md7 MF7) as (_ & F7maps & F7lazy & _ & _ & _ & _ & _ & F7fds & _ & _ & F7fs & _).
destruct (frame_AR mem1 (ms_mem ms6) m5 md7 4224 HAR5 ltac:(lia) MEQ6 PRS6 PRSh6 ltac:(subst md7; apply with_vm_backing_same)) as (AV6 & PM6 & HAR7).
exists regs6, (ms_mem ms6), md7, (Wb ++ P ++ bs), [].
split. { unfold cfg_at, raZ. fold regs6. rewrite P1, Hra0. change (w64 (bv_unsigned (getr regs0 1))) with (Z_to_bv 64 (bv_unsigned (getr regs0 1))). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact HAR7|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [exact P2 | exact (PK 3 ltac:(cbn; tauto)) | exact (PK 4 ltac:(cbn; tauto)) | exact P8 | exact P9 |].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ In r KEPTR) by (unfold KEPTR; cbn [In]; lia).
destruct Hc as [-> | [-> | [-> | [-> | Hk]]]]; [exact P18 | exact P19 | exact P20 | exact P21 | exact (PK r Hk)]. }
assert (V' : m_vmmaps m' = m_vmmaps md1) by (subst m'; apply (proj1 (ledgers_with_fds_fs _ _ md1))).
assert (L' : m_vm_lazy m' = m_vm_lazy md1) by (subst m'; apply (proj1 (proj2 (ledgers_with_fds_fs _ _ md1)))).
split; [exact P10|]. split; [rewrite F7maps, V'; exact F1maps|]. split; [rewrite F7lazy, L'; exact F1lazy|].
split; [eapply os_kept_trans; [exact (os_kept_sbm _ _ MF1) | eapply os_kept_trans; [| exact (os_kept_sbm _ _ MF7)]; subst m'; eapply os_kept_trans; [apply os_kept_with_fs | apply os_kept_with_fds]]|].
split; [rewrite app_nil_r; reflexivity|].
split; [cbn; lia|].
split.
{ apply (hdr_of_st_ok E5 eR1 ms6 1 q1 (SOff 8 240) (f + 240 + Z.of_nat (@length Z [])) HS6 ltac:(rewrite Hmem6; reflexivity) V1a E5_8).
- rewrite (E5old 33%nat ltac:(lia)). exact EE33.
- cbn [sv_denot length Z.of_nat]. rewrite E5_8, Z.add_0_r. reflexivity.
- cbn [length Z.of_nat]. lia.
- exact HhdrA. }
split; [apply garr8_nil|].
assert (Hfs7 : m_fs md7 = fs_set (m_fs mdX) sink_path (bytes (Wb ++ P ++ bs))).
{ rewrite F7fs. subst m'. rewrite State.m_fs_with_fds, State.m_fs_with_fs, F1fs. f_equal.
rewrite file_write_append; [rewrite HP0nil, !bytes_app; cbn [bytes map]; reflexivity|]. rewrite word_to_nat_len, bytes_length by lia. reflexivity. }
split; [rewrite Hfs7; apply MeasureLib.fs_lookup_set|]. split; [intros Hso; rewrite Hfs7; apply YK0r.fs_set_sorted; exact Hso|].
split.
{ rewrite !length_app. destruct (Nat.eqb_spec (length Wb + (length P + length bs)) (length Wb)) as [Habs|_]; [exfalso; lia|].
rewrite F7fds. subst m'. rewrite State.m_fds_with_fds, F1fds. f_equal. f_equal. f_equal. fold RET.
apply bv_eq. rewrite bv_add_unsigned, HRETu, !unsigned_lit_small by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. rewrite !Nat2Z.inj_add. lia. }
split; [intros q Hq; rewrite Hfs7; apply MeasureLib.fs_lookup_set_other; exact Hq|].
split; [intros a Hr Hb Hs; rewrite FB in Hb; rewrite AV6 by lia; apply AV1; lia|].
intros a Hp. apply PM6. apply PM1. exact Hp.
Qed.
Theorem fwrite_core : SRr tfibsegs W (mkCfg msX mdX) POST.
Proof.
destruct (Z_lt_le_dec 1024 (Z.of_nat (length P) + n)) as [Hnf | Hfit]; [| apply path_fits; exact Hfit].
assert (HPc : P = [] \/ P <> []) by (destruct P; [left; reflexivity | right; discriminate]).
destruct HPc as [HP0nil | HPne]; [apply path_flush1; assumption | apply path_flush2; assumption].
Qed.
End g.
End d.
