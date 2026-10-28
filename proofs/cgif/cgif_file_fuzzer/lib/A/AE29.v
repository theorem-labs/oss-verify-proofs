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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2d.
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
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FFL_ENTRY : Z := 0x9310c.
Definition FFL_STK : Z := 144.
Definition XTRAF (cval fd wpos : Z) : list Z := [cval; fd; 0; 0; 0; 0; 0; 0; 0; wpos].
Definition fileF_chunks (wpos : sv) : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit 4)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
YP09.mkChunk 24 (CVal 8 (SLit A_stdio_close)); YP09.mkChunk 32 (CVal 8 (SOff 10 1264)); YP09.mkChunk 40 (CVal 8 wpos);
YP09.mkChunk 48 (CVal 8 (SLit 0)); YP09.mkChunk 56 (CVal 8 (SOff 10 240)); YP09.mkChunk 64 (CVal 8 (SLit A_stdio_read)); YP09.mkChunk 72 (CVal 8 (SLit A_stdio_write));
YP09.mkChunk 80 (CVal 8 (SLit A_stdio_seek)); YP09.mkChunk 88 (CVal 8 (SOff 10 240)); YP09.mkChunk 96 (CVal 8 (SLit 1024));
YP09.mkChunk 104 (CVal 8 (SLit 0)); YP09.mkChunk 112 (CVal 8 (SLit 0)); YP09.mkChunk 120 (CVal 4 (SOff 33 0)); YP09.mkChunk 124 (CVal 4 (SLit 0));
YP09.mkChunk 128 (CVal 8 (SLit 0)); YP09.mkChunk 136 (CVal 4 (SLit 4294967295)); YP09.mkChunk 140 (CVal 4 (SLit 4294967295)); YP09.mkChunk 144 (CVal 4 (SLit 4294967295));
YP09.mkChunk 152 (CVal 8 (SLit 0)); YP09.mkChunk 160 (CVal 8 (SLit 0)); YP09.mkChunk 168 (CVal 8 (SLit 0)); YP09.mkChunk 176 (CVal 8 (SLit 0));
YP09.mkChunk 184 (CVal 8 (SLit 0)); YP09.mkChunk 192 (CVal 8 (SLit 0)); YP09.mkChunk 200 (CVal 8 (SLit 0)); YP09.mkChunk 208 (CVal 8 (SLit 0));
YP09.mkChunk 216 (CVal 8 (SLit 0)); YP09.mkChunk 224 (CVal 8 (SLit 0))].
Definition fileF (wpos : sv) : YP09.region := YP09.mkRegion (Some 10%nat) 0 232 0 232 (fileF_chunks wpos).
Definition stkF : YP09.region := YP09.mkRegion (Some 2%nat) (- FFL_STK) 0 (- FFL_STK) 0 [].
Definition factsF : list (nat * afact) :=
[(2%nat, mkAF (2^43 + 128) (2^47) 4); (10%nat, mkAF 4096 (2^47) 4); (41%nat, mkAF 4096 (2^47) 0); (33%nat, mkAF 0 (2^31-1) 0)].
Definition condPendF : acond := mkAC BC_NE (SOff 41 0) (SOff 10 240).
Definition ssFP : sstate := add_cond (mkSS FFL_ENTRY sr_atoms ([stkF; fileF (SOff 41 0)] ++ canR) None (mkFacts factsF [] [])) condPendF.
Definition ssFE : sstate := mkSS FFL_ENTRY sr_atoms ([stkF; fileF (SOff 10 240)] ++ canR) None (mkFacts factsF [] []).
Definition eFP : sstate := Eval vm_compute in fst (RUN ssFP).
Definition eFE : sstate := Eval vm_compute in fst (RUN ssFE).
Definition LENF : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit (-1))) (SLit (-240))) (SOff 41 0).
Definition REMF : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 18446744073709551615)) (SLit (-240))) (SOff 41 0).
Definition condRetF : acond := mkAC BC_EQ (SOff 44 0) REMF.
Definition resumeF (e : sstate) : sstate :=
add_cond (resume e (SOff 44 0) (ss_mem e) (mkFacts ((44%nat, mkAF 1 (2^31) 0) :: f_atoms (ss_facts e)) (f_conds (ss_facts e)) (f_alias (ss_facts e)))) condRetF.
Definition eRP : sstate := Eval vm_compute in fst (RUN (resumeF eFP)).
Lemma r_FP : RUN ssFP = (eFP, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Lemma r_FE : RUN ssFE = (eFE, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_RP : RUN (resumeF eFP) = (eRP, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition fileZ_chunks (md : sv) : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit 4)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
YP09.mkChunk 24 (CVal 8 (SLit A_stdio_close)); YP09.mkChunk 32 (CVal 8 (SLit 0)); YP09.mkChunk 40 (CVal 8 (SLit 0));
YP09.mkChunk 48 (CVal 8 (SLit 0)); YP09.mkChunk 56 (CVal 8 (SLit 0)); YP09.mkChunk 64 (CVal 8 (SLit A_stdio_read)); YP09.mkChunk 72 (CVal 8 (SLit A_stdio_write));
YP09.mkChunk 80 (CVal 8 (SLit A_stdio_seek)); YP09.mkChunk 88 (CVal 8 (SOff 10 240)); YP09.mkChunk 96 (CVal 8 (SLit 1024));
YP09.mkChunk 104 (CVal 8 (SLit 0)); YP09.mkChunk 112 (CVal 8 (SLit 0)); YP09.mkChunk 120 (CVal 4 (SOff 33 0)); YP09.mkChunk 124 (CVal 4 (SLit 0));
YP09.mkChunk 128 (CVal 8 (SLit 0)); YP09.mkChunk 136 (CVal 4 md); YP09.mkChunk 140 (CVal 4 (SLit 4294967295)); YP09.mkChunk 144 (CVal 4 (SLit 4294967295));
YP09.mkChunk 152 (CVal 8 (SLit 0)); YP09.mkChunk 160 (CVal 8 (SLit 0)); YP09.mkChunk 168 (CVal 8 (SLit 0)); YP09.mkChunk 176 (CVal 8 (SLit 0));
YP09.mkChunk 184 (CVal 8 (SLit 0)); YP09.mkChunk 192 (CVal 8 (SLit 0)); YP09.mkChunk 200 (CVal 8 (SLit 0)); YP09.mkChunk 208 (CVal 8 (SLit 0));
YP09.mkChunk 216 (CVal 8 (SLit 0)); YP09.mkChunk 224 (CVal 8 (SLit 0))].
Definition ssFZ : sstate := mkSS FFL_ENTRY sr_atoms ([stkF; YP09.mkRegion (Some 10%nat) 0 232 0 232 (fileZ_chunks (SLit 0))] ++ canR) None (mkFacts factsF [] []).
Definition eFZ : sstate := Eval vm_compute in fst (RUN ssFZ).
Lemma r_FZ : RUN ssFZ = (eFZ, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition FFL_RET : Z := 0x9322c.
Definition hdrZ13 (md : sv) : list (Z * N * sv) :=
[(0, 4%N, SLit 4); (8, 8%N, SLit 0); (16, 8%N, SLit 0); (24, 8%N, SLit A_stdio_close); (32, 8%N, SLit 0); (40, 8%N, SLit 0); (48, 8%N, SLit 0); (56, 8%N, SLit 0);
(64, 8%N, SLit A_stdio_read); (72, 8%N, SLit A_stdio_write); (80, 8%N, SLit A_stdio_seek); (88, 8%N, SOff 10 240); (96, 8%N, SLit 1024); (104, 8%N, SLit 0); (112, 8%N, SLit 0);
(120, 4%N, SOff 33 0); (124, 4%N, SLit 0); (128, 8%N, SLit 0); (136, 4%N, md); (140, 4%N, SLit 4294967295); (144, 4%N, SLit 4294967295);
(152, 8%N, SLit 0); (160, 8%N, SLit 0); (168, 8%N, SLit 0); (176, 8%N, SLit 0); (184, 8%N, SLit 0); (192, 8%N, SLit 0); (200, 8%N, SLit 0); (208, 8%N, SLit 0); (216, 8%N, SLit 0); (224, 8%N, SLit 0)].
Definition hdrZ_cells (f fd md : Z) : list (Z * N * Z) :=
[(0, 4%N, 4); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, A_stdio_close); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0);
(64, 8%N, A_stdio_read); (72, 8%N, A_stdio_write); (80, 8%N, A_stdio_seek); (88, 8%N, f + 240); (96, 8%N, 1024); (104, 8%N, 0); (112, 8%N, 0);
(120, 4%N, fd); (124, 4%N, 0); (128, 8%N, 0); (136, 4%N, md); (140, 4%N, 4294967295); (144, 4%N, 4294967295);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0); (216, 8%N, 0); (224, 8%N, 0)].
Definition hdrZ_is (m : word -> option byte) (f fd md : Z) : Prop :=
Forall (fun c => match c with (o, n, v) => val_mem tfibsegs m (f + o) (N.to_nat n) v end) (hdrZ_cells f fd md).
Definition KEPTZ : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeZ (e : sstate) (md : sv) : bool :=
(ss_pc e =? FFL_RET) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SLit 0) && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPTZ
&& forallb (fun c => has_chunk e 1 (fst (fst c)) (snd (fst c)) (snd c)) (hdrZ13 md)
&& match ss_mem e with
| [r0; r1; r2; r3] => skel_is r0 (Some 2%nat) (- FFL_STK) 0 (- FFL_STK) 0 && skel_is r1 (Some 10%nat) 0 232 0 232
&& skel_is r2 None A_GOT_canary (A_GOT_canary + 8) 0 0 && skel_is r3 None A_canary (A_canary + 8) 0 0
| _ => false end.
Lemma shapeZE_ok : shapeZ eFE (SLit 4294967295) = true. Proof. vm_compute. reflexivity. Qed.
Lemma shapeZZ_ok : shapeZ eFZ (SLit 0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma shapeZP_ok : shapeZ eRP (SLit 4294967295) = true. Proof. vm_compute. reflexivity. Qed.
Definition IOVF : sv := SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff 41 0) (SOff 10 240))) (SLit 1)) (SLit 0).
Definition shapeW (e : sstate) : bool :=
(ss_pc e =? WV_ECALL) && match ss_resv e with None => true | _ => false end
&& reg_is e 17 (SLit 66) && reg_is e 10 (SOff 33 0) && reg_is e 11 (SOff 2 (-136)) && reg_is e 12 IOVF
&& match ss_mem e with
| [r0; r1; r2; r3] => skel_is r0 (Some 2%nat) (- FFL_STK) 0 (- FFL_STK) 0 && skel_is r1 (Some 10%nat) 0 232 0 232
&& skel_is r2 None A_GOT_canary (A_GOT_canary + 8) 0 0 && skel_is r3 None A_canary (A_canary + 8) 0 0
| _ => false end
&& ss_atoms_lt 44 e.
Lemma shapeW_ok : shapeW eFP = true /\ iov_read1 (ss_mem eFP) (Some 2%nat) (-136) = Some (SOff 10 240, LENF) /\ iov_read1 (ss_mem eFP) (Some 2%nat) (-120) = Some (SLit 0, SLit 0).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma shapeZ_sound : forall e md, shapeZ e md = true ->
ss_pc e = FFL_RET /\ ss_resv e = None /\ reg_is e 10 (SLit 0) = true /\ (forall r, In r KEPTZ -> reg_is e r (SOff (Z.to_nat r) 0) = true) /\
(forall o nn v, In (o, nn, v) (hdrZ13 md) -> has_chunk e 1 o nn v = true) /\
exists r0 r1 r2 r3, ss_mem e = [r0; r1; r2; r3] /\
skel_is r0 (Some 2%nat) (- FFL_STK) 0 (- FFL_STK) 0 = true /\ skel_is r1 (Some 10%nat) 0 232 0 232 = true.
Proof.
intros e md Hs. unfold shapeZ in Hs.
apply andb_prop in Hs as [Hs Hm]. apply andb_prop in Hs as [Hs Hh]. apply andb_prop in Hs as [Hs Hk]. apply andb_prop in Hs as [Hs H10].
apply andb_prop in Hs as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
split; [exact Hpc|]. split; [destruct (ss_resv e); [discriminate Hrv | reflexivity]|]. split; [exact H10|].
split; [intros r Hr; rewrite forallb_forall in Hk; exact (Hk r Hr)|].
split; [intros o nn v Hin; rewrite forallb_forall in Hh; exact (Hh (o, nn, v) Hin)|].
destruct (ss_mem e) as [|r0 [|r1 [|r2 [|r3 [|? ?]]]]]; try discriminate Hm.
apply andb_prop in Hm as [Hm K3]. apply andb_prop in Hm as [Hm K2]. apply andb_prop in Hm as [K0 K1].
exists r0, r1, r2, r3. repeat split; assumption.
Qed.
Ltac INL := cbn; repeat (first [left; reflexivity | right]).
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (f fd cval : Z) (P Wb : list Z).
Let sp0 : Z := spZ regs0.
Let H := w_H W.
Let m0 := mrestrict H mem0.
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis Hra0 : YK0s.ret_ok (getr regs0 1).
Hypothesis Hal16 : sp0 mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + FFL_STK <= sp0.
Hypothesis Hshi : sp0 <= ly_stk_hi ly.
Hypothesis HpresE : forall a, sp0 - FFL_STK <= a < sp0 -> apresent H mem0 a.
Hypothesis A0 : getr regs0 10 = w64 f.
Hypothesis HFILE : file_at tfibsegs tfib_K m0 f fd P.
Hypothesis Hf0 : 4096 <= f.
Hypothesis Hfhi : f + FILE_BLOCK <= 2 ^ 47.
Hypothesis Hfal : f mod 16 = 0.
Hypothesis Hfd : 0 <= fd < 2 ^ 31.
Hypothesis HBLK : forall a, f <= a < f + FILE_BLOCK -> apresent H mem0 a /\ ~ aowned B ly S a.
Hypothesis HBstk : f + FILE_BLOCK <= sp0 - FFL_STK \/ sp0 <= f.
Hypothesis HBimg : f + FILE_BLOCK <= TFIB_IMG_LO \/ TFIB_IMG_END <= f.
Hypothesis HBam : amem_range f FILE_BLOCK.
Hypothesis Hcan1 : val_mem tfibsegs m0 A_GOT_canary 8 A_canary.
Hypothesis Hcan2 : val_mem tfibsegs m0 A_canary 8 cval.
Hypothesis Hcv : 0 <= cval < 2 ^ 64.
Hypothesis HfdL : fd_lookup (m_fds md0) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length Wb)))).
Hypothesis HfsL : Fs.fs_lookup (m_fs md0) sink_path = Some (YE00.bytes Wb).
Hypothesis HSmax : Z.of_nat (length Wb) + Z.of_nat (length P) <= SINK_MAX.
Definition ZPOST : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' mdw,
c' = cfg_at tfibsegs (raZ regs0) regs' mem' md' /\ AR tfibsegs B ly S W mem' md' /\
aregs_preserved regs0 regs' /\ getr regs' 10 = w64 0 /\
m_vmmaps md' = m_vmmaps md0 /\ m_vm_lazy md' = m_vm_lazy md0 /\ os_kept md0 md' /\
(mdw = 0 \/ mdw = 4294967295) /\ hdrZ_is (mrestrict H mem') f fd mdw /\
Fs.fs_lookup (m_fs md') sink_path = Some (YE00.bytes (Wb ++ P)) /\
(Fs.fs_sorted (m_fs md0) = true -> Fs.fs_sorted (m_fs md') = true) /\
fd_lookup (m_fds md') (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length (Wb ++ P))))) /\
fd_remove (m_fds md') (Z_to_bv 64 fd) = fd_remove (m_fds md0) (Z_to_bv 64 fd) /\
(forall q, q <> sink_path -> Fs.fs_lookup (m_fs md') q = Fs.fs_lookup (m_fs md0) q) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + 232) -> ~ (sp0 - FFL_STK <= a < sp0) -> aview tfibsegs H mem' a = aview tfibsegs H mem0 a) /\
(forall a, apresent H mem0 a -> apresent H mem' a).
Let wpos : Z := f + 240 + Z.of_nat (length P).
Let EE : env := AE2y.Env regs0 (XTRAF cval fd wpos).
Let ms0 : machine_state := mkst regs0 (Z_to_bv 64 FFL_ENTRY) mem0 (seg_rom tfibsegs).
Lemma factsF0 : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ FILE_BLOCK = 1264 /\ FFL_STK = 144 /\ 0 <= Z.of_nat (length P) <= 1024 /\ (ly_stk_hi ly <= 2 ^ 47 /\ 17594333495296 + 144 <= sp0).
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (HPL : Z.of_nat (length P) <= 1024).
{ destruct HFILE as [_ [(-> & _) | (_ & _ & _ & _ & _ & HL)]]; [cbn; lia | unfold FILE_BUFSIZ in HL; exact HL]. }
assert (FB : FILE_BLOCK = 1264) by reflexivity. assert (FS : FFL_STK = 144) by reflexivity. rewrite FB, FS in *. subst sp0.
repeat split; lia.
Qed.
Lemma EE_factsF :
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs0 r) /\
(forall j z, nth_error (XTRAF cval fd wpos) j = Some z -> ew EE (32 + j) = Z_to_bv 64 z) /\
bv_unsigned (ew EE 2) = sp0 /\ ew EE 10 = Z_to_bv 64 f /\ ew EE 32 = Z_to_bv 64 cval /\ ew EE 33 = Z_to_bv 64 fd /\ ew EE 41 = Z_to_bv 64 wpos /\
bv_unsigned (ew EE 10) = f /\ bv_unsigned (ew EE 41) = wpos.
Proof.
pose proof factsF0 as (Hsp & FB & FS & HP0 & Lhi).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs0 r) by (intros; apply AE2y.Env_reg; assumption).
assert (EEx : forall j z, nth_error (XTRAF cval fd wpos) j = Some z -> ew EE (32 + j) = Z_to_bv 64 z) by (intros j z Hj; exact (AE2y.Env_x regs0 _ j z Hj)).
split; [exact EEreg|]. split; [exact EEx|].
split; [rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity|].
split; [rewrite (EEreg 10%nat 10%bv eq_refl); exact A0|].
split; [exact (EEx 0%nat cval eq_refl)|]. split; [exact (EEx 1%nat fd eq_refl)|]. split; [exact (EEx 9%nat wpos eq_refl)|].
split; [rewrite (EEreg 10%nat 10%bv eq_refl), A0; apply unsigned_lit_small; rewrite FB in *; lia|].
change (ew EE 41) with (ew EE (32 + 9)). rewrite (EEx 9%nat wpos eq_refl). apply unsigned_lit_small. subst wpos. rewrite FB in *. lia.
Qed.
Lemma entry_st_okF : forall fr chunks,
fr = YP09.mkRegion (Some 10%nat) 0 232 0 232 chunks ->
((chunks = fileF_chunks (SOff 41 0) /\ val_mem tfibsegs m0 (f + 32) 8 (f + 1264) /\ val_mem tfibsegs m0 (f + 40) 8 wpos /\ val_mem tfibsegs m0 (f + 56) 8 (f + 240) /\ val_mem tfibsegs m0 (f + 136) 4 4294967295)
\/ (chunks = fileF_chunks (SOff 10 240) /\ P = [] /\ val_mem tfibsegs m0 (f + 32) 8 (f + 1264) /\ val_mem tfibsegs m0 (f + 40) 8 wpos /\ val_mem tfibsegs m0 (f + 56) 8 (f + 240) /\ val_mem tfibsegs m0 (f + 136) 4 4294967295)
\/ (chunks = fileZ_chunks (SLit 0) /\ P = [] /\ val_mem tfibsegs m0 (f + 32) 8 0 /\ val_mem tfibsegs m0 (f + 40) 8 0 /\ val_mem tfibsegs m0 (f + 56) 8 0 /\ val_mem tfibsegs m0 (f + 136) 4 0)) ->
st_ok tfibsegs EE (mkSS FFL_ENTRY sr_atoms ([stkF; fr] ++ canR) None (mkFacts factsF [] [])) (restrict H ms0).
Proof.
intros fr chunks -> Hch.
pose proof factsF0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_factsF as (EEreg & EEx & EE2 & EE10 & EE32 & EE33 & EE41 & EE10u & EE41u).
destruct HFILE as [HST HWIN].
subst ms0. rewrite restrict_mkst_fx. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs0 (map (Z_to_bv 64) (XTRAF cval fd wpos))) with EE.
- apply regs_ok_Ereg.
- destruct Hch as [(-> & _) | [(-> & _) | (-> & _)]]; vm_compute; reflexivity.
- apply Forall_cons.
{ unfold stkF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EE2. unfold FFL_STK.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply AE2y.apresent_writable; apply HpresE; unfold sp0 in *; rewrite FS; lia | apply Forall_nil]. }
apply Forall_cons.
{ assert (HC : forall o nn v, In (o, nn, v) [(0, 4%N, 4); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, A_stdio_close); (48, 8%N, 0); (64, 8%N, A_stdio_read); (72, 8%N, A_stdio_write);
(80, 8%N, A_stdio_seek); (88, 8%N, f + 240); (96, 8%N, 1024); (104, 8%N, 0); (112, 8%N, 0); (120, 4%N, fd); (124, 4%N, 0); (128, 8%N, 0);
(140, 4%N, 4294967295); (144, 4%N, 4294967295); (152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0);
(200, 8%N, 0); (208, 8%N, 0); (216, 8%N, 0); (224, 8%N, 0)] ->
val_mem tfibsegs m0 (f + o) (N.to_nat nn) v).
{ intros o nn v Hin. unfold file_static in HST. unfold FILE_BUF_OFF, FILE_BUFSIZ, U32M1 in HST. cbn [ak_close ak_read ak_write ak_seek tfib_K] in HST.
repeat match type of HST with _ /\ _ => let X := fresh "C" in destruct HST as [X HST] end.
cbn [In] in Hin.
repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <- <-; cbn [N.to_nat]; assumption|]). destruct Hin. }
assert (CK : forall o nn e v, sv_denot EE e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 -> val_mem tfibsegs m0 (f + o) (N.to_nat nn) v ->
YP09.chunk_ok tfibsegs EE m0 f (YP09.mkChunk o (CVal nn e))).
{ intros o nn e v He Hv Hn8 Hval. exact (chunk_ok_val tfibsegs EE m0 f o nn e v He Hv Hn8 Hval). }
destruct Hch as [(-> & W32 & W40 & W56 & W136) | [(-> & HPn & W32 & W40 & W56 & W136) | (-> & HPn & W32 & W40 & W56 & W136)]];
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite EE10u;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply AE2y.apresent_writable; apply (proj1 (HBLK (f + o) ltac:(lia)))|]);
unfold fileF_chunks, fileZ_chunks; subst m0;
(repeat (apply Forall_cons; [ eapply CK;
[cbn [sv_denot]; rewrite ?EE10, ?EE41, ?EE33, ?Z.add_0_r, ?unsigned_lit_small; [reflexivity | lia ..]
| unfold A_stdio_close, A_stdio_read, A_stdio_write, A_stdio_seek; subst wpos; cbn; lia | cbn; lia
| first [exact W32 | exact W40 | exact W56 | exact W136
| (subst wpos; rewrite HPn in W40 || idtac; cbn [length Z.of_nat] in W40; rewrite ?Z.add_0_r in W40; exact W40)
| (apply HC; cbn [In]; repeat (first [left; reflexivity | right]))] ] |]); apply Forall_nil). }
unfold canR. subst m0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_GOT_canary, A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ 0 0x9ec38 8 (SLit 0x5f8fd0) 0x5f8fd0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hcan1]. }
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_canary.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ 0 0x5f8fd0 8 (SOff 32 0) cval); [cbn [sv_denot]; rewrite EE32, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hcan2]. }
- apply pairwise_disjoint_of_extents.
change (map (extent_of_region EE) ([stkF; YP09.mkRegion (Some 10%nat) 0 232 0 232 chunks] ++ canR))
with (extent_of_region EE stkF :: extent_of_region EE (YP09.mkRegion (Some 10%nat) 0 232 0 232 chunks) :: map (extent_of_region EE) canR).
unfold stkF, canR, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2, EE10u.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_GOT_canary, A_canary, FFL_STK.
unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. rewrite FS in HBstk. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsF]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE41, EE33, !unsigned_lit_small by (subst wpos; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. subst wpos. repeat split; lia.
Qed.
Lemma hdrZ_of_st_ok : forall E e ms r (mdw : Z),
st_ok tfibsegs E e (restrict H ms) -> nth_error (ss_mem e) 1 = Some r -> YP09.r_base r = Some 10%nat ->
bv_unsigned (ew E 10) = f -> ew E 33 = Z_to_bv 64 fd -> 0 <= mdw < 2 ^ 32 ->
(forall o nn v, In (o, nn, v) (hdrZ13 (SLit mdw)) -> has_chunk e 1 o nn v = true) ->
hdrZ_is (mrestrict H (ms_mem ms)) f fd mdw.
Proof.
intros E e ms r mdw HS Hi Hb E10 E33 Hmdw Hh.
pose proof factsF0 as (_ & FB & _). rewrite FB in *.
unfold hdrZ_is. apply Forall_forall. intros [[o nn] v] Hin.
assert (HX : forall sv, In (o, nn, sv) (hdrZ13 (SLit mdw)) -> sv_denot E sv = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (f + o) (N.to_nat nn) v).
{ intros sv Hsv Hd Hr Hn8. specialize (Hh _ _ _ Hsv).
unfold has_chunk in Hh. rewrite Hi in Hh. apply existsb_exists in Hh as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E e _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs). rewrite Hb in Hcs. cbn [base_val] in Hcs. rewrite E10 in Hcs.
exact (val_of_chunk_ok tfibsegs E _ _ o nn sv v (proj1 (Forall_forall _ _) Hcs _ Hc) Hd Hr Hn8). }
unfold hdrZ_cells in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <- <-;
eapply HX; [unfold hdrZ13; cbn [In]; repeat (first [left; reflexivity | right])
| cbn [sv_denot]; rewrite ?E33, ?Z.add_0_r; try reflexivity; rewrite E10 || idtac; try reflexivity; rewrite unsigned_lit_small by lia; reflexivity
| unfold A_stdio_close, A_stdio_read, A_stdio_write, A_stdio_seek; cbn; lia | cbn; lia] |]).
destruct Hin.
Qed.
Lemma frame_ARF : forall (memA mem1 : word -> option byte) mdA md1,
AR tfibsegs B ly S W memA mdA ->
(forall z : word, ~ (sp0 - FFL_STK <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> mem1 z = memA z) ->
(forall a, sp0 - FFL_STK <= a < sp0 -> apresent H mem1 a) -> (forall a, f <= a < f + 232 -> apresent H mem1 a) ->
same_but_materialized mdA md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - FFL_STK <= a < sp0) -> ~ (f <= a < f + 232) -> aview tfibsegs H mem1 a = aview tfibsegs H memA a) /\
(forall a, apresent H memA a -> apresent H mem1 a) /\
AR tfibsegs B ly S W mem1 md1.
Proof.
intros memA mem1 mdA md1 HARA MEQ PRS PRSh MF.
pose proof factsF0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *. rewrite FS in *.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 <= a < sp0) -> ~ (f <= a < f + 232) -> aview tfibsegs H mem1 a = aview tfibsegs H memA a).
{ intros a Hr Ha Hb. apply aview_same. apply MEQ; rewrite unsigned_lit_small by lia; assumption. }
assert (PM : forall a, apresent H memA a -> apresent H mem1 a).
{ intros a Hp. rewrite (AE2y.apresent_mod _ mem1 a). rewrite (AE2y.apresent_mod _ memA a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 144)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS; lia|]];
(destruct (Z_lt_le_dec a' f) as [L4|L4]; [|destruct (Z_lt_le_dec a' (f + 232)) as [L5|L5]; [apply PRSh; lia|]]);
(apply (apresent_same H memA mem1 a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
split; [exact AV|]. split; [exact PM|].
pose proof (same_but_materialized_frame mdA md1 MF) as (_ & Fmaps & Flazy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Feu).
apply (al_frame _ _ LAWS ly S W memA mdA mem1 _ HARA).
+ intros a Hr Hown. apply AV; [exact Hr| |]. { intros Hs. exact (al_stack _ _ LAWS ly S W memA mdA a HARA ltac:(unfold sp0 in *; lia) Hown). }
intros Hb. exact (proj2 (HBLK a ltac:(lia)) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem1 a). rewrite (AE2y.aview_mod _ memA a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 144)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply AE2y.aview_some_of_apresent; apply PRS; lia|]];
(destruct (Z_lt_le_dec a' f) as [L4|L4]; [|destruct (Z_lt_le_dec a' (f + 232)) as [L5|L5]; [apply AE2y.aview_some_of_apresent; apply PRSh; lia|]]);
(rewrite AV by lia; exact Hv).
+ exact Fmaps.
+ exact Flazy.
+ exact Feu.
+ intros a Hband Hh. pose proof (in_band_rw_u64 a Hband) as Hr. change (w64 a) with (Z_to_bv 64 a) in *.
assert (NP : forall m, ~ apresent H m a) by (intros m [Hn0 _]; unfold H in Hn0; rewrite Hh in Hn0; discriminate).
destruct (Z_lt_le_dec a (sp0 - 144)) as [L1|L1]; [|destruct (Z_lt_le_dec a sp0) as [L3|L3]; [exfalso; exact (NP _ (HpresE a ltac:(unfold sp0 in *; lia)))|]];
(destruct (Z_lt_le_dec a f) as [L4|L4]; [|destruct (Z_lt_le_dec a (f + 232)) as [L5|L5]; [exfalso; exact (NP _ (proj1 (HBLK a ltac:(lia))))|]]);
(apply MEQ; rewrite unsigned_lit_small by lia; lia).
Qed.
Lemma AR_mdF : forall mem md md', AR tfibsegs B ly S W mem md ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md -> AR tfibsegs B ly S W mem md'.
Proof.
intros mem md md' HARA Hv Hl He. apply (al_frame _ _ LAWS ly S W mem md mem md' HARA); [intros; reflexivity | intros a Ha; exact Ha | exact Hv | exact Hl | exact He | intros; reflexivity].
Qed.
Lemma tailZ : forall E e (mdw : Z) ms6 (memA : word -> option byte) mdA md6,
shapeZ e (SLit mdw) = true -> (mdw = 0 \/ mdw = 4294967295) ->
st_ok tfibsegs E e (restrict H ms6) ->
(forall i, (i < 44)%nat -> ew E i = ew EE i) ->
AR tfibsegs B ly S W memA mdA ->
same_but_materialized mdA md6 ->
(forall z : word, ~ (sp0 - FFL_STK <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms6 z = memA z) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - FFL_STK <= a < sp0) -> ~ (f <= a < f + 232) -> aview tfibsegs H memA a = aview tfibsegs H mem0 a) ->
(forall a, apresent H mem0 a -> apresent H memA a) ->
m_vmmaps mdA = m_vmmaps md0 -> m_vm_lazy mdA = m_vm_lazy md0 -> os_kept md0 mdA ->
Fs.fs_lookup (m_fs mdA) sink_path = Some (YE00.bytes (Wb ++ P)) ->
(Fs.fs_sorted (m_fs md0) = true -> Fs.fs_sorted (m_fs mdA) = true) ->
fd_lookup (m_fds mdA) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length (Wb ++ P))))) ->
fd_remove (m_fds mdA) (Z_to_bv 64 fd) = fd_remove (m_fds md0) (Z_to_bv 64 fd) ->
(forall q, q <> sink_path -> Fs.fs_lookup (m_fs mdA) q = Fs.fs_lookup (m_fs md0) q) ->
SRr tfibsegs W (mkCfg ms6 md6) ZPOST.
Proof.
intros E e mdw ms6 memA mdA md6 Hsh Hmdw HS6 Eold HARA MF6 MEQ6 AVA PMA Vm Lz OK FSL SRT FDL FDR OTH.
pose proof factsF0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_factsF as (EEreg & EEx & EE2 & EE10 & EE32 & EE33 & EE41 & EE10u & EE41u).
pose proof AF0x.Hwx_tfa as Hwx.
destruct (shapeZ_sound e (SLit mdw) Hsh) as (Hpc6 & Hresv6 & T10 & HK6 & Hh6 & q0 & q1 & q2 & q3 & Hmem6 & K0 & K1).
apply skel_is_sound in K0 as (V0a & V0lo & V0hi & V0b & V0c). apply skel_is_sound in K1 as (V1a & V1lo & V1hi & V1b & V1c).
rewrite FS in V0b, MEQ6, AVA.
assert (E6_2 : bv_unsigned (ew E 2) = sp0) by (rewrite (Eold 2%nat ltac:(lia)); exact EE2).
assert (E6_10 : bv_unsigned (ew E 10) = f) by (rewrite (Eold 10%nat ltac:(lia)); exact EE10u).
assert (RD6 : forall (r : bv 5) v, reg_is e (bv_unsigned r) v = true -> getr (ms_regs ms6) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E e ms6 r HS6). }
set (regs6 := ms_regs ms6) in *.
assert (PK : forall r, In r KEPTZ -> getr regs6 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTZ in Hin; cbn in Hin; lia).
rewrite (RD6 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (Eold (Z.to_nat r) ltac:(lia)), (EEreg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. apply HK6. exact Hin. }
assert (P1 : getr regs6 1 = getr regs0 1) by (exact (PK 1 ltac:(unfold KEPTZ; cbn; tauto))).
assert (P10 : getr regs6 10 = w64 0) by (rewrite (RD6 10%bv (SLit 0) T10); reflexivity).
assert (PRS6 : forall a, sp0 - 144 <= a < sp0 -> apresent H (ms_mem ms6) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E e ms6 0 q0 a HS6 ltac:(rewrite Hmem6; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite V0a, V0b, V0c. cbn [base_val]. rewrite E6_2. lia. }
assert (PRSh6 : forall a, f <= a < f + 232 -> apresent H (ms_mem ms6) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E e ms6 1 q1 a HS6 ltac:(rewrite Hmem6; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite V1a, V1b, V1c. cbn [base_val]. rewrite E6_10. lia. }
eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E); [exact HS6 | exact Hresv6 | rewrite Hpc6; vm_compute; reflexivity |].
intros mat'. split; [reflexivity|].
set (md7 := with_vm_backing (m_vm_lazy md6) mat' md6).
assert (MF7 : same_but_materialized mdA md7).
{ apply (same_but_materialized_trans mdA md6 md7 MF6). subst md7. apply with_vm_backing_same. }
pose proof (same_but_materialized_frame mdA md7 MF7) as (_ & F7maps & F7lazy & _ & _ & _ & _ & _ & F7fds & _ & _ & F7fs & _).
destruct (frame_ARF memA (ms_mem ms6) mdA md7 HARA ltac:(rewrite FS; exact MEQ6) ltac:(rewrite FS; exact PRS6) PRSh6 MF7) as (AV6 & PM6 & HAR7).
rewrite FS in AV6.
exists regs6, (ms_mem ms6), md7, mdw.
split. { unfold cfg_at, raZ. fold regs6. rewrite P1, Hra0. change (w64 (bv_unsigned (getr regs0 1))) with (Z_to_bv 64 (bv_unsigned (getr regs0 1))). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact HAR7|].
split. { intros r Hr. unfold acallee_saved in Hr. apply PK. unfold KEPTZ. cbn [In]. lia. }
split; [exact P10|].
split; [rewrite F7maps; exact Vm|]. split; [rewrite F7lazy; exact Lz|].
split; [eapply os_kept_trans; [exact OK | exact (os_kept_sbm _ _ MF7)]|].
split; [exact Hmdw|].
split.
{ apply (hdrZ_of_st_ok E e ms6 q1 mdw HS6 ltac:(rewrite Hmem6; reflexivity) V1a E6_10).
- rewrite (Eold 33%nat ltac:(lia)). exact EE33.
- lia.
- exact Hh6. }
split; [rewrite F7fs; exact FSL|]. split; [intros Hso; rewrite F7fs; exact (SRT Hso)|].
split; [rewrite F7fds; exact FDL|]. split; [rewrite F7fds; exact FDR|].
split; [intros q Hq; rewrite F7fs; exact (OTH q Hq)|].
split; [intros a Hr Hb Hs; rewrite FS in Hs; rewrite AV6 by lia; apply AVA; lia|].
intros a Hp. apply PM6. apply PMA. exact Hp.
Qed.
Lemma legZ : P = [] -> val_mem tfibsegs m0 (f + 32) 8 0 -> val_mem tfibsegs m0 (f + 40) 8 0 -> val_mem tfibsegs m0 (f + 56) 8 0 -> val_mem tfibsegs m0 (f + 136) 4 0 ->
SRr tfibsegs W (mkCfg ms0 md0) ZPOST.
Proof.
intros HPn W32 W40 W56 W136.
pose proof factsF0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_factsF as (EEreg & EEx & EE2 & EE10 & EE32 & EE33 & EE41 & EE10u & EE41u).
assert (HS1 : st_ok tfibsegs EE ssFZ (restrict H ms0)).
{ apply (entry_st_okF _ (fileZ_chunks (SLit 0)) eq_refl). right. right. repeat split; assumption. }
eapply SRr_bind; [exact (musl_phase W EE _ _ _ ms0 md0 HS1 r_FZ)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS2 & HF2 & HFr2). clear HFr2. cbn [ms_mem ms0 mkst] in HF2.
set (md1 := with_vm_backing (m_vm_lazy md0) mat1 md0) in *.
assert (MF1 : same_but_materialized md0 md1) by (subst md1; apply with_vm_backing_same).
assert (MEQ1 : forall z : word, ~ (sp0 - FFL_STK <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms1 z = mem0 z).
{ intros z Hz1 Hz2. apply (HF2 z). intros Hin.
destruct (in_wrange_two_b EE (ss_mem ssFZ) (bv_unsigned z) 2 (- FFL_STK) 0 sp0 10 0 232 f ltac:(vm_compute; reflexivity) EE2 EE10u Hin); rewrite ?FS in *; lia. }
apply (tailZ EE eFZ 0 ms1 mem0 md0 md1 shapeZZ_ok ltac:(left; reflexivity) HS2 ltac:(intros; reflexivity) HAR MF1 MEQ1).
- intros; reflexivity.
- intros a Ha; exact Ha.
- reflexivity.
- reflexivity.
- apply os_kept_refl.
- rewrite HPn, app_nil_r. exact HfsL.
- intros Hso; exact Hso.
- rewrite HPn, app_nil_r. exact HfdL.
- reflexivity.
- intros; reflexivity.
Qed.
Lemma legE : P = [] -> val_mem tfibsegs m0 (f + 32) 8 (f + 1264) -> val_mem tfibsegs m0 (f + 40) 8 wpos -> val_mem tfibsegs m0 (f + 56) 8 (f + 240) ->
val_mem tfibsegs m0 (f + 136) 4 4294967295 ->
SRr tfibsegs W (mkCfg ms0 md0) ZPOST.
Proof.
intros HPn W32 W40 W56 W136.
pose proof factsF0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_factsF as (EEreg & EEx & EE2 & EE10 & EE32 & EE33 & EE41 & EE10u & EE41u).
assert (HS1 : st_ok tfibsegs EE ssFE (restrict H ms0)).
{ apply (entry_st_okF _ (fileF_chunks (SOff 10 240)) eq_refl). right. left. repeat split; assumption. }
eapply SRr_bind; [exact (musl_phase W EE _ _ _ ms0 md0 HS1 r_FE)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS2 & HF2 & HFr2). clear HFr2. cbn [ms_mem ms0 mkst] in HF2.
set (md1 := with_vm_backing (m_vm_lazy md0) mat1 md0) in *.
assert (MF1 : same_but_materialized md0 md1) by (subst md1; apply with_vm_backing_same).
assert (MEQ1 : forall z : word, ~ (sp0 - FFL_STK <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms1 z = mem0 z).
{ intros z Hz1 Hz2. apply (HF2 z). intros Hin.
destruct (in_wrange_two_b EE (ss_mem ssFE) (bv_unsigned z) 2 (- FFL_STK) 0 sp0 10 0 232 f ltac:(vm_compute; reflexivity) EE2 EE10u Hin); rewrite ?FS in *; lia. }
apply (tailZ EE eFE 4294967295 ms1 mem0 md0 md1 shapeZE_ok ltac:(right; reflexivity) HS2 ltac:(intros; reflexivity) HAR MF1 MEQ1).
- intros; reflexivity.
- intros a Ha; exact Ha.
- reflexivity.
- reflexivity.
- apply os_kept_refl.
- rewrite HPn, app_nil_r. exact HfsL.
- intros Hso; exact Hso.
- rewrite HPn, app_nil_r. exact HfdL.
- reflexivity.
- intros; reflexivity.
Qed.
Lemma U_LENF_REMF : U EE LENF = Z.of_nat (length P) /\ U EE REMF = Z.of_nat (length P).
Proof.
pose proof factsF0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_factsF as (EEreg & EEx & EE2 & EE10 & EE32 & EE33 & EE41 & EE10u & EE41u).
unfold LENF, REMF. rewrite !U_add_mod, !U_SMd, !U_SLit, (U_atom EE 10 f EE10), (U_atom EE 41 wpos EE41) by (subst wpos; lia).
cbn [zmd_raw]. replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity. replace (zcanon 18446744073709551615) with (2 ^ 64 - 1) by reflexivity.
replace (zcanon (-240)) with (2 ^ 64 - 240) by reflexivity. unfold zcanon, M64.
rewrite !Zplus_mod_idemp_l.
rewrite <- (Z.add_assoc ((f * (2 ^ 64 - 1)) mod 2 ^ 64) (2 ^ 64 - 240) wpos), Zplus_mod_idemp_l.
replace (f * (2 ^ 64 - 1) + (2 ^ 64 - 240 + wpos)) with ((wpos - f - 240) + (f + 1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full, Z.mod_small by (subst wpos; lia).
subst wpos. split; lia.
Qed.
Lemma fd_remove_insert_same : forall fds k e, fd_remove (fd_insert fds k e) k = fd_remove fds k.
Proof.
intros fds k e. unfold fd_insert, fd_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. cbn [negb].
induction fds as [|[k' e'] fds IH]; [reflexivity|]. cbn [List.filter fst]. destruct (bv_eqb k' k) eqn:Hk; cbn [negb]; [exact IH|].
cbn [List.filter fst]. rewrite Hk. cbn [negb]. rewrite IH. reflexivity.
Qed.
Lemma legP : P <> [] -> val_mem tfibsegs m0 (f + 32) 8 (f + 1264) -> val_mem tfibsegs m0 (f + 40) 8 wpos -> val_mem tfibsegs m0 (f + 56) 8 (f + 240) ->
val_mem tfibsegs m0 (f + 136) 4 4294967295 -> garr8 tfibsegs m0 (f + 240) P ->
SRr tfibsegs W (mkCfg ms0 md0) ZPOST.
Proof.
intros HPne W32 W40 W56 W136 HP.
pose proof factsF0 as (Hsp & FB & FS & HP0 & Lhi). rewrite FB in *.
pose proof EE_factsF as (EEreg & EEx & EE2 & EE10 & EE32 & EE33 & EE41 & EE10u & EE41u).
pose proof AF0x.Hwx_tfa as Hwx. pose proof U_LENF_REMF as [ULF URF].
assert (HPpos : 0 < Z.of_nat (length P)) by (destruct P as [|x l]; [exfalso; exact (HPne eq_refl) | cbn [length]; lia]).
assert (HSM : SINK_MAX = 2 ^ 62) by reflexivity. rewrite HSM in HSmax.
assert (HS1 : st_ok tfibsegs EE ssFP (restrict H ms0)).
{ unfold ssFP. apply st_ok_assume; [apply (entry_st_okF _ (fileF_chunks (SOff 41 0)) eq_refl); left; repeat split; assumption|].
unfold condPendF. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, (U_atom EE 41 wpos EE41), (U_atom_off EE 10 f 240 EE10) by (subst wpos; lia).
destruct (Z.eqb_spec wpos (f + 240)); [subst wpos; exfalso; lia | reflexivity]. }
eapply SRr_bind; [exact (musl_phase W EE _ _ _ ms0 md0 HS1 r_FP)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS2 & HF2 & HFr2). clear HFr2. cbn [ms_mem ms0 mkst] in HF2.
set (md1 := with_vm_backing (m_vm_lazy md0) mat1 md0) in *.
assert (MF1 : same_but_materialized md0 md1) by (subst md1; apply with_vm_backing_same).
pose proof (same_but_materialized_frame md0 md1 MF1) as (_ & F1maps & F1lazy & _ & _ & _ & _ & _ & F1fds & _ & _ & F1fs & _ & _ & _ & _ & F1eu).
pose proof (proj1 shapeW_ok) as Hsh. pose proof (proj2 shapeW_ok) as [HIO1 HIO2]. unfold shapeW in Hsh.
apply andb_prop in Hsh as [Hsh Hat]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh R17]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv eFP = None) by (destruct (ss_resv eFP); [discriminate | reflexivity]).
destruct (ss_mem eFP) as [|r0 [|r1 [|r2 [|r3 [|? ?]]]]] eqn:Hmem; try discriminate Hwin.
apply andb_prop in Hwin as [Hwin K3]. apply andb_prop in Hwin as [Hwin K2]. apply andb_prop in Hwin as [K0 K1].
apply skel_is_sound in K0 as (W0a & RL0 & RH0 & W0b & W0c). apply skel_is_sound in K1 as (W1a & RL1 & RH1 & W1b & W1c).
rewrite FS in W0b, RL0.
destruct (st_ok_ecall_shape_r tfibsegs H EE eFP ms1 HS2 Hresv) as (regs1 & mem1 & Hms1 & Hregs & Hmemok & HG).
assert (Hmm : ms_mem ms1 = mem1) by (rewrite Hms1; reflexivity). rewrite Hmm in HF2.
assert (MEQ2 : forall z : word, ~ (sp0 - 144 <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> mem1 z = mem0 z).
{ intros z Hz1 Hz2. apply (HF2 z). intros Hin.
destruct (in_wrange_two_b EE (ss_mem ssFP) (bv_unsigned z) 2 (- FFL_STK) 0 sp0 10 0 232 f ltac:(vm_compute; reflexivity) EE2 EE10u Hin); rewrite ?FS in *; lia. }
clear HF2.
assert (RD : forall (r : bv 5) v, reg_is eFP (bv_unsigned r) v = true -> getr regs1 r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply Hregs. }
assert (Q17 : bv_unsigned (getr regs1 17) = 66) by (rewrite (RD 17%bv (SLit 66) R17); reflexivity).
assert (Q10 : getr regs1 10 = Z_to_bv 64 fd) by (rewrite (RD 10%bv (SOff 33 0) R10); cbn [sv_denot]; rewrite EE33, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (Q11 : getr regs1 11 = Z_to_bv 64 (sp0 - 136)) by (rewrite (RD 11%bv (SOff 2 (-136)) R11); cbn [sv_denot]; rewrite EE2; f_equal; lia).
assert (Q12 : getr regs1 12 = Z_to_bv 64 2).
{ rewrite (RD 12%bv IOVF R12). rewrite denot_lit_U. unfold IOVF. rewrite U_iovcnt, (U_atom EE 41 wpos EE41), (U_atom_off EE 10 f 240 EE10) by (subst wpos; lia).
destruct (Z.eqb_spec wpos (f + 240)); [subst wpos; exfalso; lia | reflexivity]. }
assert (PRS1 : forall a, sp0 - 144 <= a < sp0 -> apresent H mem1 a).
{ intros a Ha. apply (mem_ok_window_apresent H EE mem1 _ 0 r0 a Hmemok ltac:(rewrite Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PRSh : forall a, f <= a < f + 232 -> apresent H mem1 a).
{ intros a Ha. apply (mem_ok_window_apresent H EE mem1 _ 1 r1 a Hmemok ltac:(rewrite Hmem; reflexivity)); [| unfold AF0x.off_img, TFIB_IMG_LO, TFIB_IMG_END in *; clear - Ha HBimg Hf0 Hfhi; lia].
rewrite W1a, W1b, W1c. cbn [base_val]. rewrite EE10u. lia. }
destruct (frame_ARF mem0 mem1 md0 md1 HAR ltac:(rewrite FS; exact MEQ2) ltac:(rewrite FS; exact PRS1) PRSh MF1) as (AV1 & PM1 & HAR1).
rewrite FS in AV1.
assert (MB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 144 <= a < sp0) -> ~ (f <= a < f + 232) -> mbyte tfibsegs (mrestrict H mem1) a = mbyte tfibsegs (mrestrict H mem0) a).
{ intros a Hr H1 H2. apply AE2y.mbyte_of_aview. exact (AV1 a Hr H1 H2). }
rewrite FS in HBstk.
assert (HP1 : garr8 tfibsegs (mrestrict H mem1) (f + 240) P) by (eapply garr8_frame; [exact HP|]; intros a Ha; apply MB1; lia).
destruct (iov_read1_sound tfibsegs EE (mrestrict H mem1) (ss_mem eFP) (Some 2%nat) (-136) _ _ Hmemok ltac:(rewrite Hmem; exact HIO1)) as [M0r L0r].
destruct (iov_read1_sound tfibsegs EE (mrestrict H mem1) (ss_mem eFP) (Some 2%nat) (-120) _ _ Hmemok ltac:(rewrite Hmem; exact HIO2)) as [M1r L1r].
cbn [base_val sv_denot] in M0r, L0r, M1r, L1r. rewrite EE2 in M0r, L0r, M1r, L1r. rewrite EE10u in M0r.
change (sv_denot EE LENF) with (Z_to_bv 64 (U EE LENF)) in L0r || rewrite (denot_lit_U EE LENF) in L0r. rewrite ULF in L0r.
replace (sp0 + -136 + 8) with (sp0 - 128) in L0r by lia. replace (sp0 + -136) with (sp0 - 136) in M0r by lia.
replace (sp0 + -120 + 8) with (sp0 - 112) in L1r by lia. replace (sp0 + -120) with (sp0 - 120) in M1r by lia.
destruct (rdn_restrict_inv W mem1 (sp0 - 136) 8 _ ltac:(lia) ltac:(lia) M0r) as [M0 V0].
destruct (rdn_restrict_inv W mem1 (sp0 - 128) 8 _ ltac:(lia) ltac:(lia) L0r) as [L0 V1].
destruct (rdn_restrict_inv W mem1 (sp0 - 120) 8 _ ltac:(lia) ltac:(lia) M1r) as [M1 V2].
destruct (rdn_restrict_inv W mem1 (sp0 - 112) 8 _ ltac:(lia) ltac:(lia) L1r) as [L1 V3].
pose proof (rdn_of_garr8 tfibsegs (mrestrict H mem1) (f + 240) P HP1) as B0r.
destruct (rdn_restrict_inv W mem1 (f + 240) (length P) _ ltac:(lia) ltac:(lia) B0r) as [B0 VB0].
clear M0r L0r M1r L1r B0r.
assert (VIOV : vis_range W (sp0 - 136) (sp0 - 104)).
{ intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 128)); [apply V0; lia|]. destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 120)); [apply V1; lia|].
destruct (Z_lt_le_dec (bv_unsigned x) (sp0 - 112)); [apply V2; lia | apply V3; lia]. }
rewrite Hms1. apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
assert (HMRW : MAX_RW_COUNT = 0x7ffff000) by reflexivity.
destruct (node_writev_file2_lazy tfibsegs (w_H W) (w_A W) regs1 (Z_to_bv 64 (ss_pc eFP)) mem1 (seg_rom tfibsegs) md1 (Z_to_bv 64 fd) sink_path
(Z_to_bv 64 (Z.of_nat (length Wb))) (bytes Wb) (Z_to_bv 64 (f + 240)) (Z_to_bv 64 (Z.of_nat (length P))) (Z_to_bv 64 0) (Z_to_bv 64 0)
(bytes P) [] HAI Q17) as (Hnode & HAI5 & Hsbm5).
- rewrite F1fds. exact HfdL.
- apply Syscall.fd32_id. rewrite unsigned_lit_small by lia. lia.
- exact Q10.
- exact Q12.
- rewrite Q11. apply ms_read_u64_of_rdn. exact M0.
- rewrite Q11, unsigned_lit_small by lia. apply ms_read_u64_of_rdn. replace (sp0 - 136 + 8) with (sp0 - 128) by lia. exact L0.
- rewrite Q11, unsigned_lit_small by lia. apply ms_read_u64_of_rdn. replace (sp0 - 136 + 16) with (sp0 - 120) by lia. exact M1.
- rewrite Q11, unsigned_lit_small by lia. apply ms_read_u64_of_rdn. replace (sp0 - 136 + 24) with (sp0 - 112) by lia. exact L1.
- apply ms_read_bytes_of_rdn. rewrite word_to_nat_len by lia. exact B0.
- apply ms_read_bytes_of_rdn. rewrite word_to_nat_lit by lia. reflexivity.
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
destruct (import_iovecs_accesses_in _ (Z_to_bv 64 (sp0 - 136)) a (Z_to_bv 64 2) m ltac:(rewrite unsigned_lit_small by lia; lia) ltac:(rewrite !unsigned_lit_small by lia; lia) Hin) as [-> [i [Hi Hb]]].
rewrite !unsigned_lit_small in Hi, Hb by lia.
apply (range_avoids_of_vis W a 16 (sp0 - 136) (sp0 - 104) VIOV); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.
+ destruct (iov_prefix_accesses_in _ _ _ _ Hin) as [len [Hil Hm]].
destruct Hil as [Heq | [Heq | []]]; injection Heq as E1 E2; subst a len.
* rewrite word_to_nat_len in Hm by lia. apply (range_avoids_of_vis W _ m (f + 240) (f + 240 + Z.of_nat (length P)) VB0); rewrite ?unsigned_lit_small by lia; lia.
* rewrite word_to_nat_lit in Hm by lia. replace m with 0%nat by lia. intros k Hk. exfalso. lia.
- cbv zeta in Hnode, HAI5, Hsbm5.
set (m' := with_fds _ (with_fs _ md1)) in *. set (m5 := materialized_succ m' _) in *.
cbn [ms_mem pend_at] in Hnode.
apply (SRr_node tfibsegs W _ unit _ tt _ Hnode); [intros [] _; cbn [cfg_model]; exact HAI5|]. intros [].
set (RET := len_word (bytes P ++ [])).
assert (HRET : RET = Z_to_bv 64 (Z.of_nat (length P))).
{ subst RET. unfold len_word. f_equal. rewrite length_app, bytes_length. cbn [length]. lia. }
assert (HRETu : bv_unsigned RET = Z.of_nat (length P)) by (rewrite HRET; apply unsigned_lit_small; lia).
set (E5 := ewset EE 44 RET).
assert (E5old : forall i, (i < 44)%nat -> ew E5 i = ew EE i) by (intros i Hi; subst E5; apply ew_ewset_other; lia).
assert (E5_44 : ew E5 44 = Z_to_bv 64 (Z.of_nat (length P))) by (subst E5; rewrite ew_ewset_same; exact HRET).
assert (HS5 : st_ok tfibsegs E5 (resumeF eFP) (restrict H (mkst (regupd regs1 10 RET) (v_addi (Z_to_bv 64 (ss_pc eFP)) 4) mem1 (seg_rom tfibsegs)))).
{ unfold resumeF. apply st_ok_assume.
- rewrite restrict_mkst_fx. subst E5.
apply (st_ok_resume_atom tfibsegs 44 (mkAF 1 (2 ^ 31) 0) EE eFP regs1 (mrestrict H mem1) RET Hregs Hmemok HG Hat); cbn [af_lo af_hi af_al2]; rewrite ?HRETu; [lia | lia |].
change (2 ^ 0) with 1. apply Z.mod_1_r.
- unfold condRetF. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (U_atom E5 44 _ E5_44) by lia.
unfold U. rewrite (sv_denot_agree 44 EE E5 REMF ltac:(subst E5; apply env_agree_ewset) eq_refl). fold (U EE REMF). rewrite URF. apply Z.eqb_refl. }
assert (E5_2 : bv_unsigned (ew E5 2) = sp0) by (rewrite (E5old 2%nat ltac:(lia)); exact EE2).
assert (E5_10 : bv_unsigned (ew E5 10) = f) by (rewrite (E5old 10%nat ltac:(lia)); exact EE10u).
assert (V' : m_vmmaps m' = m_vmmaps md1) by (subst m'; apply (proj1 (ledgers_with_fds_fs _ _ md1))).
assert (L' : m_vm_lazy m' = m_vm_lazy md1) by (subst m'; apply (proj1 (proj2 (ledgers_with_fds_fs _ _ md1)))).
pose proof (same_but_materialized_frame m' m5 Hsbm5) as (_ & V5 & L5 & _ & _ & _ & _ & _ & F5fds & _ & _ & F5fs & _ & _ & _ & _ & U5).
assert (HAR5 : AR tfibsegs B ly S W mem1 m5).
{ apply (AR_mdF mem1 md1 m5 HAR1); [rewrite V5; exact V' | rewrite L5; exact L' | rewrite U5; unfold eager_used; rewrite V', L'; reflexivity]. }
eapply SRr_bind; [exact (musl_phase W E5 (resumeF eFP) eRP _ (mkst (regupd regs1 10 RET) (v_addi (Z_to_bv 64 (ss_pc eFP)) 4) mem1 (seg_rom tfibsegs)) m5 HS5 r_RP)|].
intros W6' c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [ms_mem mkst] in HF6. clear HFr6.
assert (MEQ6 : forall z : word, ~ (sp0 - FFL_STK <= bv_unsigned z < sp0) -> ~ (f <= bv_unsigned z < f + 232) -> ms_mem ms6 z = mem1 z).
{ intros z Hz1 Hz2. apply (HF6 z). intros Hin.
destruct (in_wrange_two_b E5 (ss_mem (resumeF eFP)) (bv_unsigned z) 2 (- FFL_STK) 0 sp0 10 0 232 f ltac:(vm_compute; reflexivity) E5_2 E5_10 Hin); rewrite ?FS in *; lia. }
clear HF6.
assert (Hfs5 : m_fs m5 = fs_set (m_fs md0) sink_path (bytes (Wb ++ P))).
{ rewrite F5fs. subst m'. rewrite State.m_fs_with_fds, State.m_fs_with_fs, F1fs. f_equal.
rewrite file_write_append; [rewrite app_nil_r, bytes_app; reflexivity|]. rewrite word_to_nat_len, bytes_length by lia. reflexivity. }
assert (Hfds5 : m_fds m5 = fd_insert (m_fds md0) (Z_to_bv 64 fd) (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length (Wb ++ P)))))).
{ rewrite F5fds. subst m'. rewrite State.m_fds_with_fds, F1fds. f_equal. f_equal. f_equal. fold RET.
apply bv_eq. rewrite bv_add_unsigned, HRETu, !unsigned_lit_small by (rewrite ?length_app; lia). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite length_app, Z.mod_small by lia. lia. }
apply (tailZ E5 eRP 4294967295 ms6 mem1 m5 _ shapeZP_ok ltac:(right; reflexivity) HS6 E5old HAR5 ltac:(apply with_vm_backing_same) MEQ6).
+ intros a Hr Hs Hb. apply AV1; assumption.
+ exact PM1.
+ rewrite V5, V'. exact F1maps.
+ rewrite L5, L'. exact F1lazy.
+ eapply os_kept_trans; [exact (os_kept_sbm _ _ MF1) | eapply os_kept_trans; [| exact (os_kept_sbm _ _ Hsbm5)]; subst m'; eapply os_kept_trans; [apply os_kept_with_fs | apply os_kept_with_fds]].
+ rewrite Hfs5. apply MeasureLib.fs_lookup_set.
+ intros Hso. rewrite Hfs5. apply YK0r.fs_set_sorted. exact Hso.
+ rewrite Hfds5. apply fd_lookup_insert_eq.
+ rewrite Hfds5. apply fd_remove_insert_same.
+ intros q Hq. rewrite Hfs5. apply MeasureLib.fs_lookup_set_other. exact Hq.
Qed.
Theorem fflush_real : SRr tfibsegs W (mkCfg ms0 md0) ZPOST.
Proof.
destruct HFILE as [HST [(HPn & W32 & W40 & W56 & W136) | (W32 & W40 & W56 & W136 & HPb & HPL)]].
- exact (legZ HPn W32 W40 W56 W136).
- unfold FILE_BUF_OFF, FILE_BUFSIZ, U32M1 in W32, W40, W56, W136, HPb. replace (f + 240 + 1024) with (f + 1264) in W32 by lia.
destruct (Nat.eq_dec (length P) 0) as [HL|HL].
+ apply length_zero_iff_nil in HL. exact (legE HL W32 W40 W56 W136).
+ refine (legP _ W32 W40 W56 W136 HPb). intros HPn. apply HL. rewrite HPn. reflexivity.
Qed.
End d.
End b.
