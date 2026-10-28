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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2f AE2e AE2d AE29.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Syscall.
From LinuxProcessSemantics.EquivalenceDefinition Require MeasureLib.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YK0r YK0p.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FC_REAL : Z := 0x92ee4.
Definition FC_AFTER : Z := 0x92f04.
Definition FC_CLOSE_ECALL : Z := 0x92bb4.
Definition FC_FREE1_RA : Z := 0x92f88.
Definition FC_JOIN : Z := 0x92f90.
Definition PC_FREE : Z := 0x5292c.
Definition PC_FFLUSH : Z := 0x41954.
Definition FCL_WIN : Z := 400.
Definition FCL_T : Z := 144.
Definition stk1 : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition ss1 : sstate := mkSS FC_REAL sr_atoms [stk1] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4); (10%nat, mkAF 4096 (2^47) 4)] [] []).
Definition e1 : sstate := Eval vm_compute in fst (RUN ss1).
Lemma r_1 : RUN ss1 = (e1, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition KEPT1 : list Z := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition cells1 : list (Z * sv) := [(-8, SOff 1 0); (-16, SOff 8 0); (-24, SOff 9 0); (-32, SOff 18 0); (-40, SOff 19 0)].
Definition shape1 (e : sstate) : bool :=
(ss_pc e =? PC_FFLUSH) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SOff 10 0) && reg_is e 1 (SLit FC_AFTER) && reg_is e 2 (SOff 2 (-48)) && reg_is e 8 (SOff 10 0)
&& forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPT1
&& forallb (fun c => has_chunk e 0 (fst c) 8 (snd c)) cells1
&& match ss_mem e with [r0] => skel_is r0 (Some 2%nat) (-48) 0 (-48) 0 | _ => false end.
Lemma shape1_ok : shape1 e1 = true. Proof. vm_compute. reflexivity. Qed.
Definition hdrC_chunks : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 4 (SLit 4)); YP09.mkChunk 24 (CVal 8 (SLit A_stdio_close)); YP09.mkChunk 104 (CVal 8 (SLit 0)); YP09.mkChunk 112 (CVal 8 (SLit 0));
YP09.mkChunk 120 (CVal 4 (SOff 33 0)); YP09.mkChunk 124 (CVal 4 (SLit 0)); YP09.mkChunk 168 (CVal 8 (SLit 0))].
Definition hdrC : YP09.region := YP09.mkRegion (Some 8%nat) 0 232 0 0 hdrC_chunks.
Definition stk5 : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition oflR : YP09.region := YP09.mkRegion None A_ofl_head (A_ofl_head + 8) A_ofl_head (A_ofl_head + 8) [YP09.mkChunk A_ofl_head (CVal 8 (SOff 8 0))].
Definition envR : list YP09.region :=
[YP09.mkRegion None A_need_locks (A_need_locks + 1) 0 0 [YP09.mkChunk A_need_locks (CVal 1 (SLit 0))];
YP09.mkRegion None A_ofl_lock (A_ofl_lock + 4) 0 0 [YP09.mkChunk A_ofl_lock (CVal 4 (SLit 0))]].
Definition facts5 : list (nat * afact) := [(2%nat, mkAF (2^43) (2^47) 4); (8%nat, mkAF 4096 (2^47) 4); (33%nat, mkAF 0 (2^31-1) 0)].
Definition ss5 : sstate := mkSS FC_AFTER sr_atoms ([stk5; hdrC; oflR] ++ envR) None (mkFacts facts5 [] []).
Definition e5 : sstate := Eval vm_compute in fst (RUN ss5).
Lemma r_5 : RUN ss5 = (e5, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition resume5 (e : sstate) : sstate := resume e (SLit 0) (ss_mem e) (ss_facts e).
Definition e7 : sstate := Eval vm_compute in fst (RUN (resume5 e5)).
Lemma r_7 : RUN (resume5 e5) = (e7, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition skels5 (e : sstate) : bool :=
match ss_mem e with
| [r0; r1; r2; r3; r4] => skel_is r0 (Some 2%nat) (-16) 0 (-16) 0 && skel_is r1 (Some 8%nat) 0 232 0 0
&& skel_is r2 None A_ofl_head (A_ofl_head + 8) A_ofl_head (A_ofl_head + 8)
&& skel_is r3 None A_need_locks (A_need_locks + 1) 0 0 && skel_is r4 None A_ofl_lock (A_ofl_lock + 4) 0 0
| _ => false end.
Definition shape5 (e : sstate) : bool :=
(ss_pc e =? FC_CLOSE_ECALL) && match ss_resv e with None => true | _ => false end
&& reg_is e 17 (SLit 57) && reg_is e 10 (SOff 33 0) && skels5 e.
Lemma shape5_ok : shape5 e5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KEPT7 : list Z := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shape7 (e : sstate) : bool :=
(ss_pc e =? PC_FREE) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SLit 0) && reg_is e 1 (SLit FC_FREE1_RA) && reg_is e 2 (SOff 2 0) && reg_is e 8 (SOff 8 0) && reg_is e 9 (SOff 10 0) && reg_is e 18 (SLit 0)
&& forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPT7
&& has_chunk e 2 A_ofl_head 8 (SLit 0) && skels5 e.
Lemma shape7_ok : shape7 e7 = true. Proof. vm_compute. reflexivity. Qed.
Definition ssL2 : sstate := mkSS FC_FREE1_RA sr_atoms [] None (mkFacts [] [] []).
Definition eL2 : sstate := Eval vm_compute in fst (RUN ssL2).
Lemma r_L2 : RUN ssL2 = (eL2, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition KEPTL2 : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeL2 (e : sstate) : bool :=
(ss_pc e =? PC_FREE) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SOff 8 0) && reg_is e 1 (SLit FC_JOIN) && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPTL2
&& match ss_mem e with [] => true | _ => false end.
Lemma shapeL2_ok : shapeL2 eL2 = true. Proof. vm_compute. reflexivity. Qed.
Definition stk3_chunks : list YP09.chunk :=
[YP09.mkChunk 40 (CVal 8 (SLit IC_RET)); YP09.mkChunk 32 (CVal 8 (SOff 8 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
YP09.mkChunk 8 (CVal 8 (SLit 0))].
Definition stk3 : YP09.region := YP09.mkRegion (Some 2%nat) 0 48 0 0 stk3_chunks.
Definition ssL3 : sstate := mkSS FC_JOIN sr_atoms [stk3] None (mkFacts [(2%nat, mkAF (2^43) (2^47 - 48) 4)] [] []).
Definition eL3 : sstate := Eval vm_compute in fst (RUN ssL3).
Lemma r_L3 : RUN ssL3 = (eL3, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Definition shapeL3 (e : sstate) : bool :=
(ss_pc e =? IC_RET) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SAlu ALU_OR (SOff 18 0) (SOff 9 0)) && reg_is e 1 (SLit IC_RET) && reg_is e 2 (SOff 2 48) && reg_is e 8 (SOff 8 0)
&& reg_is e 9 (SOff 34 0) && reg_is e 18 (SOff 35 0) && reg_is e 19 (SLit 0)
&& forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPT7
&& match ss_mem e with [r0] => skel_is r0 (Some 2%nat) 0 48 0 0 | _ => false end.
Lemma shapeL3_ok : shapeL3 eL3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma lk_free : clookup tfibmusl_tbl PC_FREE = None. Proof. vm_compute. reflexivity. Qed.
Lemma ofl_img_facts : forall i, 0 <= i < 8 ->
img_writable_ok tfibsegs (A_ofl_head + i) = true /\ seg_rom tfibsegs (Z_to_bv 64 (A_ofl_head + i)) <> None.
Proof.
intros i Hi.
assert (C : forall j, In j [0; 1; 2; 3; 4; 5; 6; 7] -> img_writable_ok tfibsegs (A_ofl_head + j) = true /\ seg_rom tfibsegs (Z_to_bv 64 (A_ofl_head + j)) <> None).
{ intros j Hj. cbn [In] in Hj. repeat (destruct Hj as [<- | Hj]; [vm_compute; split; [reflexivity | discriminate]|]). destruct Hj. }
apply C. cbn [In]. lia.
Qed.
Ltac INL := cbn; repeat (first [left; reflexivity | right]).
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (f fd cval M : Z) (P Wb : list Z).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let m0 := mrestrict H mem.
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hal16 : sp0 mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + FCL_WIN <= sp0.
Hypothesis Hshi : sp0 <= ly_stk_hi ly.
Hypothesis Hpres : forall a, sp0 - FCL_WIN <= a < sp0 -> apresent H mem a.
Hypothesis G10 : getr regs 10 = w64 f.
Hypothesis HFILE : file_at tfibsegs tfib_K m0 f fd P.
Hypothesis Hf0 : 4096 <= f.
Hypothesis Hfhi : f + FILE_BLOCK <= 2 ^ 47.
Hypothesis Hfal : f mod 16 = 0.
Hypothesis HBLK : forall a, f <= a < f + FILE_BLOCK -> apresent H mem a /\ ~ aowned B ly S a.
Hypothesis HBstk : f + FILE_BLOCK <= sp0 - FCL_WIN \/ sp0 <= f.
Hypothesis HBimg : f + FILE_BLOCK <= TFIB_IMG_LO \/ TFIB_IMG_END <= f.
Hypothesis HBam : amem_range f FILE_BLOCK.
Hypothesis HBmeta : f + FILE_BLOCK <= M \/ M + AMETA_SIZE <= f.
Hypothesis Hcan1 : val_mem tfibsegs m0 A_GOT_canary 8 A_canary.
Hypothesis Hcan2 : val_mem tfibsegs m0 A_canary 8 cval.
Hypothesis Hcv : 0 <= cval < 2 ^ 64.
Hypothesis HCELLS : cells_hold m0 ic_cells.
Hypothesis HIMG : ro_img m0.
Hypothesis Henv1 : val_mem tfibsegs m0 A_need_locks 1 0.
Hypothesis Henv2 : val_mem tfibsegs m0 A_ofl_lock 4 0.
Hypothesis Hhead : val_mem tfibsegs m0 A_ofl_head 8 f.
Hypothesis HOFLown : forall a, A_ofl_head <= a < A_ofl_head + 8 -> ~ aowned B ly S a.
Hypothesis HMM : val_mem tfibsegs m0 AE2e.A_META_MEM 8 M.
Hypothesis HMZ : forall a, M <= a < M + AMETA_SIZE -> mbyte tfibsegs m0 a = Some (Z_to_bv 8 0).
Hypothesis HMlo : TFIB_IMG_END <= M.
Hypothesis HMal : M mod 4096 = 0.
Hypothesis HMhi : M + AMETA_SIZE <= sp0 - FCL_WIN.
Hypothesis HfdL : fd_lookup (m_fds md) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length Wb)))).
Hypothesis HfsL : Fs.fs_lookup (m_fs md) sink_path = Some (YE00.bytes Wb).
Hypothesis HSmax : Z.of_nat (length Wb) + Z.of_nat (length P) <= SINK_MAX.
Definition oflW (a : Z) : Prop := A_ofl_head <= a < A_ofl_head + 8.
Definition L1POST : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regsT memT mdT (v9 v18 mdw : Z),
c' = cfg_at tfibsegs PC_FREE regsT memT mdT /\ AR tfibsegs B ly S W memT mdT /\
getr regsT 10 = w64 0 /\ getr regsT 1 = w64 FC_FREE1_RA /\ getr regsT 2 = w64 (sp0 - FCL_T) /\ getr regsT 8 = w64 f /\
getr regsT 9 = w64 0 /\ getr regsT 18 = w64 0 /\
(forall r, In r KEPT7 -> getr regsT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
m_vmmaps mdT = m_vmmaps md /\ m_vm_lazy mdT = m_vm_lazy md /\ os_kept md mdT /\
Fs.fs_lookup (m_fs mdT) sink_path = Some (YE00.bytes (Wb ++ P)) /\
(Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted (m_fs mdT) = true) /\
m_fds mdT = fd_remove (m_fds md) (Z_to_bv 64 fd) /\
(forall q, q <> sink_path -> Fs.fs_lookup (m_fs mdT) q = Fs.fs_lookup (m_fs md) q) /\
0 <= v9 < 2 ^ 64 /\ 0 <= v18 < 2 ^ 64 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FCL_T + 40) 8 IC_RET /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FCL_T + 32) 8 f /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FCL_T + 24) 8 v9 /\ val_mem tfibsegs (mrestrict H memT) (sp0 - FCL_T + 16) 8 v18 /\
val_mem tfibsegs (mrestrict H memT) (sp0 - FCL_T + 8) 8 0 /\
(forall j rz off, nth_error SAVEDC j = Some (rz, off) -> val_mem tfibsegs (mrestrict H memT) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))) /\
(mdw = 0 \/ mdw = 4294967295) /\ hdrZ_is (mrestrict H memT) f fd mdw /\
val_mem tfibsegs (mrestrict H memT) A_ofl_head 8 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - FCL_WIN <= a < sp0) -> ~ (f <= a < f + 232) -> ~ oflW a ->
aview tfibsegs H memT a = aview tfibsegs H mem a) /\
(forall a, sp0 - FCL_WIN <= a < sp0 -> apresent H memT a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ oflW a -> apresent H mem a -> apresent H memT a).
Lemma factsC : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ FILE_BLOCK = 1264 /\ FCL_WIN = 400 /\ FCL_T = 144 /\ 0 <= Z.of_nat (length P) <= 1024 /\ 0 <= fd < 2 ^ 31 /\
(ly_stk_hi ly <= 2 ^ 47 /\ 17594333495296 + 400 <= sp0) /\ A_ofl_head = 0x5f9688 /\ AMETA_SIZE = 3727360 /\ TFIB_IMG_END = 0x5fb000.
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (HPL : Z.of_nat (length P) <= 1024).
{ destruct HFILE as [_ [(-> & _) | (_ & _ & _ & _ & _ & HL)]]; [cbn; lia | unfold FILE_BUFSIZ in HL; exact HL]. }
pose proof (proj1 (proj1 HFILE)) as Hfd.
assert (FB : FILE_BLOCK = 1264) by reflexivity. assert (FS : FCL_WIN = 400) by reflexivity. rewrite FB, FS in *. subst sp0.
repeat split; try lia; reflexivity.
Qed.
Lemma VT : forall (m m' : word -> option byte) a (nn : nat) v, val_mem tfibsegs (mrestrict H m) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfibsegs H m' b = aview tfibsegs H m b) -> val_mem tfibsegs (mrestrict H m') a nn v.
Proof. intros m m' a nn v Hv Hf'. apply (AF0x.val_mem_ext (mrestrict H m)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply Hf'. lia. Qed.
Lemma frameW : forall (memA mem1 : word -> option byte) mdA md1 (Wr : Z -> Prop),
AR tfibsegs B ly S W memA mdA ->
(forall a, Wr a \/ ~ Wr a) ->
(forall a, Wr a -> (sp0 - FCL_WIN <= a < sp0) \/ (f <= a < f + 232) \/ oflW a) ->
(forall z : word, ~ Wr (bv_unsigned z) -> mem1 z = memA z) ->
(forall a, Wr a -> ~ oflW a -> apresent H mem1 a) ->
same_but_materialized mdA md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H mem1 a = aview tfibsegs H memA a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ oflW a -> apresent H memA a -> apresent H mem1 a) /\
AR tfibsegs B ly S W mem1 md1.
Proof.
intros memA mem1 mdA md1 Wr HARA Wdec HWin MEQ PRS MF.
pose proof factsC as (Hsp & FB & FS & FT & HP0 & Hfd & Lhi & HO & HAS & HIE). rewrite FB, FS in *. unfold oflW in *. rewrite HO in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H mem1 a = aview tfibsegs H memA a).
{ intros a Hr Hw. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Hw. }
assert (PM : forall a, 0 <= a < 2 ^ 64 -> ~ (0x5f9688 <= a < 0x5f9688 + 8) -> apresent H memA a -> apresent H mem1 a).
{ intros a Hr Ho Hp. destruct (Wdec a) as [Hw|Hw]; [apply PRS; assumption|].
apply (apresent_same H memA mem1 a); [apply MEQ; rewrite unsigned_lit_small by lia; exact Hw | exact Hp]. }
split; [exact AV|]. split; [exact PM|].
pose proof (same_but_materialized_frame mdA md1 MF) as (_ & Fmaps & Flazy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Feu).
apply (al_frame _ _ LAWS ly S W memA mdA mem1 _ HARA).
+ intros a Hr Hown. apply AV; [exact Hr|]. intros Hw. destruct (HWin a Hw) as [Hs | [Hh | Ho]].
* exact (al_stack _ _ LAWS ly S W memA mdA a HARA ltac:(unfold sp0 in *; lia) Hown).
* exact (proj2 (HBLK a ltac:(lia)) Hown).
* exact (HOFLown a Ho Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem1 a). rewrite (AE2y.aview_mod _ memA a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Wdec a') as [Hw|Hw]; [| rewrite AV by assumption; exact Hv].
destruct (HWin a' Hw) as [Hs | [Hh | Ho]].
* apply AE2y.aview_some_of_apresent. apply PRS; [exact Hw | lia].
* apply AE2y.aview_some_of_apresent. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. apply PRS; [exact Hw | lia].
* unfold aview, mbyte. destruct (mrestrict (w_H W) mem1 (Z_to_bv 64 a')) as [b|]; [cbn; discriminate|].
destruct (ofl_img_facts (a' - 0x5f9688) ltac:(lia)) as [_ Hrom]. rewrite HO in Hrom. replace (0x5f9688 + (a' - 0x5f9688)) with a' in Hrom by lia.
destruct (seg_rom tfibsegs (Z_to_bv 64 a')); [cbn; discriminate | exfalso; exact (Hrom eq_refl)].
+ exact Fmaps.
+ exact Flazy.
+ exact Feu.
+ intros a Hband Hh. pose proof (AE2y.in_band_rw_u64 a Hband) as Hr. change (w64 a) with (Z_to_bv 64 a) in *.
apply MEQ. rewrite unsigned_lit_small by lia. intros Hw. destruct (HWin a Hw) as [Hs | [Hh' | Ho]].
* exfalso. pose proof (Hpres a Hs) as [Hn0 _]. unfold H in Hn0. rewrite Hh in Hn0. discriminate.
* exfalso. pose proof (proj1 (HBLK a ltac:(lia))) as [Hn0 _]. unfold H in Hn0. rewrite Hh in Hn0. discriminate.
* unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hband. clear - Hband Ho. lia.
Qed.
Theorem fclose_L1 : SRr tfibsegs W (cfg_at tfibsegs IC_ENTRY regs mem md) L1POST.
Proof.
pose proof factsC as (Hsp & FB & FS & FT & HP0 & Hfd & Lhi & HO & HAS & HIE). rewrite FB, FS in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi' & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi'.
pose proof AF0x.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (IS : IC_STK = 272) by reflexivity. assert (IFR : IC_FRAME = 96) by reflexivity. assert (IW : IF_WIN = 96) by reflexivity.
assert (IFF : IF_FRAME = 80) by reflexivity. assert (IT : IF_TSTK = 176) by reflexivity. assert (FLS : FFL_STK = 144) by reflexivity.
eapply SRr_bind.
{ apply (iclose_front B LAWS TB ly S W regs mem md f M HAR Hal16); rewrite ?IS.
- unfold sp0 in *; lia.
- exact Hshi.
- intros a Ha. apply Hpres. unfold sp0 in *; lia.
- exact G10.
- exact Hf0.
- lia.
- exact Hfal.
- exact HCELLS.
- exact HIMG.
- split; [exact HMM|]. split; [exact HMZ|]. split; [exact HMlo|]. split; [exact HMal|]. rewrite IS. unfold sp0 in *; lia. }
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & MF1 & HAR1 & Q10 & Q1 & Q2 & Q8 & Q19 & QK & QS & AV1 & PRS1 & PM1).
rewrite IS in AV1, PRS1. rewrite IFR in Q2. fold H in AV1, PRS1, PM1, QS. fold sp0 in Q2, QS, AV1, PRS1.
set (E1 := AE2y.Env regs1 []).
assert (E1reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E1 i = getr regs1 r) by (intros; apply AE2y.Env_reg; assumption).
assert (E1_2 : bv_unsigned (ew E1 2) = sp0 - 96) by (rewrite (E1reg 2%nat 2%bv eq_refl), Q2; apply unsigned_lit_small; lia).
assert (E1_10 : ew E1 10 = Z_to_bv 64 f) by (rewrite (E1reg 10%nat 10%bv eq_refl); exact Q10).
assert (HS1 : st_ok tfibsegs E1 ss1 (restrict H (mkst regs1 (Z_to_bv 64 FC_REAL) mem1 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss1, E1, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 (map (Z_to_bv 64) [])) with E1.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold stk1. apply (region_ok_stack tfibsegs E1 _ 2 (sp0 - 96) (-48)); [exact E1_2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply PRS1. lia.
- apply pairwise_disjoint_of_extents. vm_compute. exact (conj I I).
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E1_2, E1_10, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. repeat split; try lia. replace (sp0 - 96) with (sp0 + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
unfold cfg_at. change (w64 IC_REAL) with (Z_to_bv 64 FC_REAL).
eapply SRr_bind; [exact (musl_phase W E1 ss1 e1 _ (mkst regs1 (Z_to_bv 64 FC_REAL) mem1 (seg_rom tfibsegs)) md1 HS1 r_1)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [ms_mem mkst] in HF2. clear HFr2.
pose proof shape1_ok as Hsh. unfold shape1 in Hsh.
apply andb_prop in Hsh as [Hsh Hsk]. apply andb_prop in Hsh as [Hsh Hcl]. apply andb_prop in Hsh as [Hsh HK1].
apply andb_prop in Hsh as [Hsh R8]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R10].
apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
destruct (ss_mem e1) as [|r0 [|? ?]] eqn:Hmem1; try discriminate Hsk.
apply skel_is_sound in Hsk as (K0a & K0lo & K0hi & K0b & K0c).
assert (Hresv2 : ss_resv e1 = None) by (destruct (ss_resv e1); [discriminate | reflexivity]).
assert (RD2 : forall (r : bv 5) v, reg_is e1 (bv_unsigned r) v = true -> getr (ms_regs ms2) r = sv_denot E1 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E1 e1 ms2 r HS2). }
set (regs2 := ms_regs ms2) in *.
assert (MEQ2 : forall z : word, ~ (sp0 - 144 <= bv_unsigned z < sp0 - 96) -> ms_mem ms2 z = mem1 z).
{ intros z Hz. apply (HF2 z). intros Hin.
unshelve epose proof (in_wrange_single_b E1 _ (bv_unsigned z) 2 (-48) 0 (sp0 - 96) _ E1_2 Hin) as X0; [vm_compute; reflexivity|]. lia. }
clear HF2.
assert (P2_10 : getr regs2 10 = w64 f) by (rewrite (RD2 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite E1_10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (P2_8 : getr regs2 8 = w64 f) by (rewrite (RD2 8%bv (SOff 10 0) R8); cbn [sv_denot]; rewrite E1_10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (P2_1 : getr regs2 1 = w64 FC_AFTER) by (rewrite (RD2 1%bv (SLit FC_AFTER) R1); reflexivity).
assert (P2_2 : getr regs2 2 = w64 (sp0 - 144)) by (rewrite (RD2 2%bv (SOff 2 (-48)) R2); cbn [sv_denot]; rewrite E1_2; unfold w64; f_equal; lia).
assert (P2K : forall r, In r KEPT1 -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPT1 in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK1. specialize (HK1 _ Hin). cbn beta in HK1.
rewrite (RD2 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (E1reg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK1. }
assert (CL2 : forall off (v : sv) (z : Z), In (off, v) cells1 -> sv_denot E1 v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
val_mem tfibsegs (mrestrict H (ms_mem ms2)) (sp0 - 96 + off) 8 z).
{ intros off v z Hin Hd Hz. rewrite forallb_forall in Hcl. specialize (Hcl _ Hin). cbn [fst snd] in Hcl.
unfold has_chunk in Hcl. rewrite Hmem1 in Hcl. cbn [nth_error] in Hcl. apply existsb_exists in Hcl as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E1 e1 _ HS2) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem1 in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs). rewrite K0a in Hcs. cbn [base_val] in Hcs. rewrite E1_2 in Hcs.
exact (val_of_chunk_ok tfibsegs E1 _ _ off 8 v z (proj1 (Forall_forall _ _) Hcs _ Hc) Hd Hz ltac:(cbn; lia)). }
assert (C2ra : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (sp0 - 104) 8 IC_RET).
{ replace (sp0 - 104) with (sp0 - 96 + -8) by lia. apply (CL2 (-8) (SOff 1 0)); [INL | cbn [sv_denot]; rewrite (E1reg 1%nat 1%bv eq_refl), Q1, Z.add_0_r; reflexivity | unfold IC_RET; lia]. }
assert (C2s0 : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (sp0 - 112) 8 f).
{ replace (sp0 - 112) with (sp0 - 96 + -16) by lia. apply (CL2 (-16) (SOff 8 0)); [INL | cbn [sv_denot]; rewrite (E1reg 8%nat 8%bv eq_refl), Q8, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia]. }
assert (C2s3 : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (sp0 - 136) 8 0).
{ replace (sp0 - 136) with (sp0 - 96 + -40) by lia. apply (CL2 (-40) (SOff 19 0)); [INL | cbn [sv_denot]; rewrite (E1reg 19%nat 19%bv eq_refl), Q19; reflexivity | lia]. }
set (v9 := bv_unsigned (getr regs1 9)). set (v18 := bv_unsigned (getr regs1 18)).
pose proof (u64_range (getr regs1 9)) as Hv9. pose proof (u64_range (getr regs1 18)) as Hv18.
assert (C2s1 : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (sp0 - 120) 8 v9).
{ replace (sp0 - 120) with (sp0 - 96 + -24) by lia. apply (CL2 (-24) (SOff 9 0)); [INL | cbn [sv_denot]; rewrite (E1reg 9%nat 9%bv eq_refl), Z.add_0_r; reflexivity | subst v9; lia]. }
assert (C2s2 : val_mem tfibsegs (mrestrict H (ms_mem ms2)) (sp0 - 128) 8 v18).
{ replace (sp0 - 128) with (sp0 - 96 + -32) by lia. apply (CL2 (-32) (SOff 18 0)); [INL | cbn [sv_denot]; rewrite (E1reg 18%nat 18%bv eq_refl), Z.add_0_r; reflexivity | subst v18; lia]. }
set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
assert (MF2 : same_but_materialized md1 md2) by (subst md2; apply with_vm_backing_same).
assert (PRS2 : forall a, sp0 - 144 <= a < sp0 - 96 -> apresent H (ms_mem ms2) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E1 e1 ms2 0 r0 a HS2 ltac:(rewrite Hmem1; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite K0a, K0b, K0c. cbn [base_val]. rewrite E1_2. lia. }
set (Wr2 := fun a => sp0 - 144 <= a < sp0 - 96).
assert (Wr2d : forall a, Wr2 a \/ ~ Wr2 a) by (intros a; subst Wr2; cbn beta; lia).
assert (Wr2i : forall a, Wr2 a -> (sp0 - 400 <= a < sp0) \/ (f <= a < f + 232) \/ oflW a) by (intros a Ha; left; subst Wr2; cbn beta in Ha; lia).
assert (Wr2p : forall a, Wr2 a -> ~ oflW a -> apresent H (ms_mem ms2) a) by (intros a Ha _; exact (PRS2 a Ha)).
destruct (frameW mem1 (ms_mem ms2) md1 md2 Wr2 HAR1 Wr2d Wr2i MEQ2 Wr2p MF2) as (AV2 & PM2 & HAR2). subst Wr2. cbv beta in AV2. clear Wr2d Wr2i Wr2p.
pose proof (st_ok_restrict_mkst tfibsegs H E1 _ _ HS2 eq_refl) as Hshape2. rewrite Hpc in Hshape2. fold regs2 in Hshape2. rewrite Hshape2.
assert (R2sp : spZ regs2 = sp0 - 144) by (unfold spZ; rewrite P2_2; apply unsigned_lit_small; lia).
assert (MB2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0) -> mbyte tfibsegs (mrestrict H (ms_mem ms2)) a = mbyte tfibsegs (mrestrict H mem) a).
{ intros a Hr Hs. apply AE2y.mbyte_of_aview. rewrite AV2 by lia. apply AV1; lia. }
assert (HCELLS2 : cells_hold (mrestrict H (ms_mem ms2)) if_cells).
{ apply (cells_hold_frame m0); [| | exact HCELLS].
- intros a Hx. unfold if_cells, AE2f.A_META_PTR, AE2f.A_META_MEM in Hx. apply Exists_exists in Hx as (r & Hin & Hr). cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; apply MB2; lia.
- unfold if_cells. repeat constructor; cbn; lia. }
change (mkst regs2 (Z_to_bv 64 PC_FFLUSH) (ms_mem ms2) (seg_rom tfibsegs)) with (mkst regs2 (w64 IF_ENTRY) (ms_mem ms2) (seg_rom tfibsegs)).
eapply SRr_bind.
{ apply (iflush_front B LAWS TB ly S W regs2 (ms_mem ms2) md2 f HAR2); rewrite ?R2sp, ?IW.
- replace (sp0 - 144) with (sp0 + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- lia.
- lia.
- intros a Ha. destruct (Z_lt_le_dec a (sp0 - 144)) as [L|L]; [apply PM2; [lia | unfold oflW; rewrite HO; lia |]; apply PM1, Hpres; lia | exfalso; lia].
- exact P2_10.
- exact Hf0.
- lia.
- exact Hfal.
- exact HCELLS2. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & MF3 & HAR3 & T10 & T1 & T2 & T8 & TK & TS & AV3 & PRS3 & PM3).
rewrite R2sp in *. rewrite IW in AV3, PRS3. rewrite IFF in T2. fold H in AV3, PRS3, PM3, TS.
assert (R3sp : spZ regs3 = sp0 - 224) by (unfold spZ; rewrite T2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (MB3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 272 <= a < sp0) -> mbyte tfibsegs (mrestrict H mem3) a = mbyte tfibsegs (mrestrict H mem) a).
{ intros a Hr Hs. rewrite <- (MB2 a Hr Hs). apply AE2y.mbyte_of_aview. apply AV3; lia. }
assert (MF03 : same_but_materialized md md3).
{ eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact MF2 | exact MF3]. }
pose proof (same_but_materialized_frame md md3 MF03) as (_ & V03 & L03 & _ & _ & _ & _ & _ & FD03 & _ & _ & FS03 & _).
assert (HFILE3 : file_at tfibsegs tfib_K (mrestrict H mem3) f fd P).
{ apply (file_at_frame tfibsegs tfib_K m0); [|exact HFILE]. intros x Hx. apply MB3; lia. }
assert (Hcan1_3 : val_mem tfibsegs (mrestrict H mem3) A_GOT_canary 8 A_canary).
{ apply (val_mem_frame tfibsegs m0); [|exact Hcan1]. intros x Hx. unfold A_GOT_canary in Hx. apply MB3; lia. }
assert (Hcan2_3 : val_mem tfibsegs (mrestrict H mem3) A_canary 8 cval).
{ apply (val_mem_frame tfibsegs m0); [|exact Hcan2]. intros x Hx. unfold A_canary in Hx. apply MB3; lia. }
unfold cfg_at. change (w64 IF_REAL) with (Z_to_bv 64 FFL_ENTRY).
eapply SRr_bind.
{ apply (fflush_real B LAWS ly S W regs3 mem3 md3 f fd cval P Wb HAR3); rewrite ?R3sp, ?FLS.
- rewrite T1. apply AE2y.ret_ok_lit; [unfold IF_RET; lia | reflexivity].
- replace (sp0 - 224) with (sp0 + (-14) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- lia.
- lia.
- intros a Ha. destruct (Z_lt_le_dec a (sp0 - 240)) as [L|L]; [| apply PRS3; lia].
apply PM3. apply PM2; [lia | unfold oflW; rewrite HO; lia |]. apply PM1, Hpres. lia.
- exact T10.
- exact HFILE3.
- exact Hf0.
- lia.
- exact Hfal.
- exact Hfd.
- intros a Ha. split; [| exact (proj2 (HBLK a Ha))]. apply PM3. apply PM2; [lia | unfold oflW; rewrite HO; unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg; lia |]. apply PM1. exact (proj1 (HBLK a Ha)).
- lia.
- exact HBimg.
- exact HBam.
- exact Hcan1_3.
- exact Hcan2_3.
- exact Hcv.
- rewrite FD03. exact HfdL.
- rewrite FS03. exact HfsL.
- exact HSmax. }
intros W4 c4 _ (-> & regs4 & mem4 & md4 & mdw & -> & HAR4 & AP4 & U10 & V4 & L4 & OK4 & Hmdw & HHDR4 & FS4 & SO4 & FDL4 & FDR4 & OTH4 & AV4 & PM4).
rewrite R3sp in *. rewrite FLS in AV4. fold H in AV4, PM4, HHDR4.
assert (R3ra : raZ regs3 = IF_RET) by (unfold raZ; rewrite T1; unfold w64; apply unsigned_lit_small; unfold IF_RET; lia).
rewrite R3ra.
assert (RO_MB : forall (m m' : word -> option byte),
(forall a, IMG_RO_LO <= a < IMG_RO_HI -> mbyte tfibsegs m' a = mbyte tfibsegs m a) -> ro_img m -> ro_img m').
{ intros m m' Heq Hro E. pose proof (Hro E) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; [intros o Ho; exfalso; clear - Ho; cbn in Ho; lia|].
apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) X4 c Hc i Hi) as (b & Hcb & Hmb). exists b. split; [exact Hcb|].
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & _).
revert Hmb. cbn [YP09.r_base base_val]. rewrite !Z.add_0_l. rewrite (Heq (YP09.c_off c + i)) by lia. intros Hmb; exact Hmb. }
assert (E42 : getr regs4 2 = getr regs3 2) by exact (AP4 2 ltac:(unfold acallee_saved; lia)).
assert (E48 : getr regs4 8 = getr regs3 8) by exact (AP4 8 ltac:(unfold acallee_saved; lia)).
assert (R4sp : spZ regs4 = sp0 - 224) by (unfold spZ; rewrite E42, T2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (MB4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 400 <= a < sp0) -> ~ (f <= a < f + 232) -> mbyte tfibsegs (mrestrict H mem4) a = mbyte tfibsegs (mrestrict H mem) a).
{ intros a Hr Hs Hh. rewrite <- (MB3 a Hr ltac:(lia)). apply AE2y.mbyte_of_aview. apply AV4; lia. }
assert (PRS4 : forall a, sp0 - 400 <= a < sp0 -> apresent H mem4 a).
{ intros a Ha. apply PM4. destruct (Z_lt_le_dec a (sp0 - 240)) as [L|L]; [| destruct (Z_lt_le_dec a (sp0 - 144)) as [L2|L2]; [apply PRS3; lia|]].
- apply PM3. apply PM2; [lia | unfold oflW; rewrite HO; lia |]. apply PM1, Hpres. lia.
- apply PM3. destruct (Z_lt_le_dec a (sp0 - 96)) as [L3|L3]; [apply PRS2; lia|]. apply PM2; [lia | unfold oflW; rewrite HO; lia |]. apply PRS1. lia. }
assert (HCELLS4 : cells_hold (mrestrict H mem4) if_cells).
{ apply (cells_hold_frame m0); [| | exact HCELLS].
- intros a Hx. unfold if_cells, AE2f.A_META_PTR, AE2f.A_META_MEM in Hx. apply Exists_exists in Hx as (r & Hin & Hr). cbn [In] in Hin.
unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; apply MB4; lia.
- unfold if_cells. repeat constructor; cbn; lia. }
assert (HIMG4 : ro_img (mrestrict H mem4)).
{ apply (RO_MB m0); [|exact HIMG]. intros a Ha. unfold IMG_RO_LO, IMG_RO_HI in Ha. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. apply MB4; lia. }
eapply SRr_bind.
{ apply (iflush_tail B LAWS ly S W regs4 mem4 md4 f M FC_AFTER f v9 HAR4); rewrite ?R4sp, ?IT, ?IFF.
- replace (sp0 - 224) with (sp0 + (-14) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- lia.
- lia.
- intros a Ha. apply PRS4. lia.
- rewrite E48. exact T8.
- exact Hf0.
- lia.
- exact Hfal.
- pose proof (TS 0%nat 1 (-8) eq_refl) as TSra. assert (E21 : getr regs2 (Z_to_bv 5 1) = getr regs2 1) by reflexivity.
rewrite E21, P2_1 in TSra. unfold w64 in TSra. rewrite unsigned_lit_small in TSra by (unfold FC_AFTER; lia).
apply (VT mem3); [| intros b Hb; apply AV4; lia]. replace (sp0 - 224 + 72) with (sp0 - 144 + -8) by lia. exact TSra.
- pose proof (TS 1%nat 8 (-16) eq_refl) as TSs0. assert (E28 : getr regs2 (Z_to_bv 5 8) = getr regs2 8) by reflexivity.
rewrite E28, P2_8 in TSs0. unfold w64 in TSs0. rewrite unsigned_lit_small in TSs0 by lia.
apply (VT mem3); [| intros b Hb; apply AV4; lia]. replace (sp0 - 224 + 64) with (sp0 - 144 + -16) by lia. exact TSs0.
- pose proof (TS 2%nat 9 (-24) eq_refl) as TSs1. rewrite (P2K 9 ltac:(unfold KEPT1; INL)) in TSs1.
assert (E19 : getr regs1 (Z_to_bv 5 9) = getr regs1 9) by reflexivity. rewrite E19 in TSs1. fold v9 in TSs1.
apply (VT mem3); [| intros b Hb; apply AV4; lia]. replace (sp0 - 224 + 56) with (sp0 - 144 + -24) by lia. exact TSs1.
- unfold FC_AFTER; lia.
- lia.
- subst v9; lia.
- reflexivity.
- exact HCELLS4.
- exact HIMG4.
- split; [| split; [| split; [exact HMlo | split; [exact HMal | lia]]]].
+ apply (VT mem); [exact HMM | intros b Hb; unfold AE2f.A_META_MEM in Hb]. rewrite <- (AV1 b) by lia. rewrite <- (AV2 b) by lia. rewrite <- (AV3 b) by lia.
apply AV4; unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg; lia.
+ intros a Ha. rewrite <- (HMZ a Ha). apply MB4; [lia | lia | clear - Ha HBmeta; lia]. }
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & MF5 & HAR5 & Y10 & Y1 & Y2 & Y8 & Y9 & YK & AV5 & PRS5 & PM5).
rewrite R4sp in *. rewrite IT, IFF in *. fold H in AV5, PRS5, PM5.
assert (Y2' : getr regs5 2 = w64 (sp0 - 144)) by (rewrite Y2; unfold w64; f_equal; lia).
assert (Y10' : getr regs5 10 = w64 0) by (rewrite Y10; exact U10).
assert (MB5 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 400 <= a < sp0) -> ~ (f <= a < f + 232) -> mbyte tfibsegs (mrestrict H mem5) a = mbyte tfibsegs (mrestrict H mem) a).
{ intros a Hr Hs Hh. rewrite <- (MB4 a Hr Hs Hh). apply AE2y.mbyte_of_aview. apply AV5; lia. }
assert (PRS5' : forall a, sp0 - 400 <= a < sp0 -> apresent H mem5 a) by (intros a Ha; apply PM5, PRS4; exact Ha).
assert (HB5 : forall a, f <= a < f + 1264 -> apresent H mem5 a).
{ intros a Ha. apply PM5, PM4, PM3. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. apply PM2; [lia | unfold oflW; rewrite HO; lia |]. apply PM1. exact (proj1 (HBLK a Ha)). }
assert (HC5 : forall o nn v, In (o, nn, v) (hdrZ_cells f fd mdw) -> val_mem tfibsegs (mrestrict H mem5) (f + o) (N.to_nat nn) v).
{ intros o nn v Hin. apply (VT mem4); [exact (proj1 (Forall_forall _ _) HHDR4 (o, nn, v) Hin) |]. intros b Hb.
assert (Ho : 0 <= o /\ o + Z.of_nat (N.to_nat nn) <= 232).
{ unfold hdrZ_cells in Hin. cbn [In] in Hin. repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <- <-; cbn; lia|]). destruct Hin. }
apply AV5; lia. }
set (E5 := AE2y.Env regs5 [0; fd]).
assert (E5reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E5 i = getr regs5 r) by (intros; apply AE2y.Env_reg; assumption).
assert (E5_2 : bv_unsigned (ew E5 2) = sp0 - 144) by (rewrite (E5reg 2%nat 2%bv eq_refl), Y2'; apply unsigned_lit_small; lia).
assert (E5_8 : ew E5 8 = Z_to_bv 64 f) by (rewrite (E5reg 8%nat 8%bv eq_refl); exact Y8).
assert (E5_8u : bv_unsigned (ew E5 8) = f) by (rewrite E5_8; apply unsigned_lit_small; lia).
assert (E5_10 : ew E5 10 = Z_to_bv 64 0) by (rewrite (E5reg 10%nat 10%bv eq_refl); exact Y10').
assert (E5_33 : ew E5 33 = Z_to_bv 64 fd) by (exact (AE2y.Env_x regs5 [0; fd] 1%nat fd eq_refl)).
assert (WOFL : forall (m : word -> option byte) o, 0 <= o < 8 -> writable_at tfibsegs m (A_ofl_head + o)).
{ intros m o Ho. destruct (ofl_img_facts o Ho) as [Hw _]. unfold img_writable_ok in Hw.
apply (writable_at_grows tfibsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
unfold writable_at. destruct (wview tfibsegs (fun _ => None) (Z_to_bv 64 (A_ofl_head + o))); [discriminate | discriminate Hw]. }
assert (HS5 : st_ok tfibsegs E5 ss5 (restrict H (mkst regs5 (Z_to_bv 64 FC_AFTER) mem5 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss5, E5, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs5 (map (Z_to_bv 64) [0; fd])) with E5.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons.
{ unfold stk5. apply (region_ok_stack tfibsegs E5 _ 2 (sp0 - 144) (-16)); [exact E5_2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply PRS5'. lia. }
apply Forall_cons.
{ unfold hdrC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E5_8u.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. unfold hdrC_chunks.
repeat (apply Forall_cons; [ eapply (chunk_ok_val tfibsegs E5);
[ cbn [sv_denot]; rewrite ?E5_33, ?Z.add_0_r, ?unsigned_lit_small; [reflexivity | lia ..]
| unfold A_stdio_close; cbn; lia | cbn; lia
| apply HC5; unfold hdrZ_cells; INL ] |]). apply Forall_nil. }
apply Forall_cons.
{ unfold oflR, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite HO.
split; [lia|]. split; [lia|]. split; [intros o Ho; rewrite Z.add_0_l; replace o with (0x5f9688 + (o - 0x5f9688)) by lia; rewrite <- HO; apply WOFL; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E5 _ 0 0x5f9688 8 (SOff 8 0) f); [cbn [sv_denot]; rewrite E5_8, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_l, <- HO. apply (val_mem_frame tfibsegs m0); [|exact Hhead]. intros x Hx. rewrite HO in Hx. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. apply MB5; lia. }
unfold envR. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_need_locks.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E5 _ 0 0x5f9223 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_l. apply (val_mem_frame tfibsegs m0); [|exact Henv1]. intros x Hx. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. apply MB5; lia. }
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold A_ofl_lock.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E5 _ 0 0x5f9680 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_l. apply (val_mem_frame tfibsegs m0); [|exact Henv2]. intros x Hx. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. apply MB5; lia. }
- apply pairwise_disjoint_of_extents.
change (map (extent_of_region E5) ([stk5; hdrC; oflR] ++ envR)) with (extent_of_region E5 stk5 :: extent_of_region E5 hdrC :: extent_of_region E5 oflR :: map (extent_of_region E5) envR).
unfold stk5, hdrC, oflR, envR, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E5_2, E5_8u.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_ofl_head, A_need_locks, A_ofl_lock.
unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok facts5]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E5_2, E5_8, E5_33, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; try lia.
replace (sp0 - 144) with (sp0 + (-9) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
eapply SRr_bind; [exact (musl_phase W E5 ss5 e5 _ (mkst regs5 (Z_to_bv 64 FC_AFTER) mem5 (seg_rom tfibsegs)) md5 HS5 r_5)|].
intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [ms_mem mkst] in HF6. clear HFr6.
set (md6 := with_vm_backing (m_vm_lazy md5) mat6 md5) in *.
assert (MF6 : same_but_materialized md5 md6) by (subst md6; apply with_vm_backing_same).
assert (WL5 : windows (ss_mem ss5) = [(Some 2%nat, -16, 0); (Some 8%nat, 0, 0); (None, 6264456, 6264464); (None, 0, 0); (None, 0, 0)]) by (vm_compute; reflexivity).
assert (WL7 : windows (ss_mem (resume5 e5)) = [(Some 2%nat, -16, 0); (Some 8%nat, 0, 0); (None, 6264456, 6264464); (None, 0, 0); (None, 0, 0)]) by (vm_compute; reflexivity).
assert (WIN : forall E rs a, windows rs = [(Some 2%nat, -16, 0); (Some 8%nat, 0, 0); (None, 6264456, 6264464); (None, 0, 0); (None, 0, 0)] ->
bv_unsigned (ew E 2) = sp0 - 144 -> in_wrange E rs a -> (sp0 - 160 <= a < sp0 - 144) \/ oflW a).
{ intros E rs a HWl E2 Hin. destruct (in_wrange_windows E rs a Hin) as (bw & lo & hi & Ht & Hr). rewrite HWl in Ht. cbn [In] in Ht. unfold oflW. rewrite HO.
destruct Ht as [Et | [Et | [Et | [Et | [Et | []]]]]]; injection Et as <- <- <-; cbn [base_val] in Hr; rewrite ?E2 in Hr; lia. }
pose proof shape5_ok as Hsh5. unfold shape5 in Hsh5.
apply andb_prop in Hsh5 as [Hsh5 Hsk5]. apply andb_prop in Hsh5 as [Hsh5 Q10s]. apply andb_prop in Hsh5 as [Hsh5 Q17s]. apply andb_prop in Hsh5 as [Hpc5 Hrv5]. apply Z.eqb_eq in Hpc5.
assert (Hresv5 : ss_resv e5 = None) by (destruct (ss_resv e5); [discriminate | reflexivity]).
unfold skels5 in Hsk5. destruct (ss_mem e5) as [|q0 [|q1 [|q2 [|q3 [|q4 [|? ?]]]]]] eqn:Hmem5; try discriminate Hsk5.
apply andb_prop in Hsk5 as [Hsk5 _]. apply andb_prop in Hsk5 as [Hsk5 _]. apply andb_prop in Hsk5 as [Hsk5 _]. apply andb_prop in Hsk5 as [K50 _].
apply skel_is_sound in K50 as (K50a & K50lo & K50hi & K50b & K50c).
destruct (st_ok_ecall_shape_r tfibsegs H E5 e5 ms6 HS6 Hresv5) as (regs6 & mem6 & Hms6 & Hregs6 & Hmemok6 & HG6).
assert (Hmm6 : ms_mem ms6 = mem6) by (rewrite Hms6; reflexivity). rewrite Hmm6 in HF6.
assert (MEQ6 : forall z : word, ~ ((sp0 - 160 <= bv_unsigned z < sp0 - 144) \/ oflW (bv_unsigned z)) -> mem6 z = mem5 z).
{ intros z Hz. apply (HF6 z). intros Hin. exact (Hz (WIN E5 _ _ WL5 E5_2 Hin)). }
clear HF6.
assert (RD6 : forall (r : bv 5) v, reg_is e5 (bv_unsigned r) v = true -> getr regs6 r = sv_denot E5 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply Hregs6. }
assert (Q6nr : bv_unsigned (getr regs6 17) = 57) by (rewrite (RD6 17%bv (SLit 57) Q17s); reflexivity).
assert (Q6fd : getr regs6 10 = Z_to_bv 64 fd) by (rewrite (RD6 10%bv (SOff 33 0) Q10s); cbn [sv_denot]; rewrite E5_33, Z.add_0_r, unsigned_lit_small by lia; reflexivity).
assert (PRS6s : forall a, sp0 - 160 <= a < sp0 - 144 -> apresent H mem6 a).
{ intros a Ha. apply (mem_ok_window_apresent H E5 mem6 _ 0 q0 a Hmemok6 ltac:(rewrite Hmem5; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite K50a, K50b, K50c. cbn [base_val]. rewrite E5_2. lia. }
set (Wr6 := fun a => (sp0 - 160 <= a < sp0 - 144) \/ oflW a).
assert (Wr6d : forall a, Wr6 a \/ ~ Wr6 a) by (intros a; subst Wr6; cbn beta; unfold oflW; lia).
assert (Wr6i : forall a, Wr6 a -> (sp0 - 400 <= a < sp0) \/ (f <= a < f + 232) \/ oflW a) by (intros a Ha; subst Wr6; cbn beta in Ha; destruct Ha; [left; lia | right; right; assumption]).
assert (Wr6p : forall a, Wr6 a -> ~ oflW a -> apresent H mem6 a) by (intros a Ha Hno; subst Wr6; cbn beta in Ha; destruct Ha as [Ha|Ha]; [exact (PRS6s a Ha) | exfalso; exact (Hno Ha)]).
destruct (frameW mem5 mem6 md5 md6 Wr6 HAR5 Wr6d Wr6i MEQ6 Wr6p MF6) as (AV6 & PM6 & HAR6). subst Wr6. cbv beta in AV6. clear Wr6d Wr6i Wr6p.
pose proof (same_but_materialized_frame md4 md5 MF5) as (_ & V45 & L45 & _ & _ & _ & _ & _ & FD45 & _ & _ & FS45 & _).
pose proof (same_but_materialized_frame md5 md6 MF6) as (_ & V56 & L56 & _ & _ & _ & _ & _ & FD56 & _ & _ & FS56 & _).
rewrite Hms6. apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
destruct (node_close_lazy tfibsegs (w_H W) (w_A W) regs6 (Z_to_bv 64 (ss_pc e5)) mem6 (seg_rom tfibsegs) md6 (Z_to_bv 64 fd) _ HAI Q6nr Q6fd
ltac:(apply Syscall.fd32_id; rewrite unsigned_lit_small by lia; lia) ltac:(rewrite FD56, FD45; exact FDL4)) as [Hnode HAI7].
apply (SRr_node tfibsegs W _ unit _ tt _ Hnode); [intros [] _; cbn [cfg_model]; exact HAI7|]. intros [].
set (md7 := with_fds (fd_remove (m_fds md6) (Z_to_bv 64 fd)) md6).
pose proof (ledgers_with_fds (fd_remove (m_fds md6) (Z_to_bv 64 fd)) md6) as (V67 & L67 & M67). fold md7 in V67, L67, M67.
assert (HAR7 : AR tfibsegs B ly S W mem6 md7).
{ apply (al_frame _ _ LAWS ly S W mem6 md6 mem6 md7 HAR6); [intros; reflexivity | intros a Ha; exact Ha | exact V67 | exact L67 | apply eager_used_vmmaps; [exact V67 | exact L67] | intros; reflexivity]. }
assert (HS7 : st_ok tfibsegs E5 (resume5 e5) (restrict H (mkst (regupd regs6 10 (Z_to_bv 64 0)) (v_addi (Z_to_bv 64 (ss_pc e5)) 4) mem6 (seg_rom tfibsegs)))).
{ unfold resume5. rewrite restrict_mkst_fx. apply (st_ok_resume_sv tfibsegs E5 e5 regs6 (mrestrict H mem6) (SLit 0) (Z_to_bv 64 0) Hregs6 Hmemok6 HG6). reflexivity. }
eapply SRr_bind; [exact (musl_phase W E5 (resume5 e5) e7 _ (mkst (regupd regs6 10 (Z_to_bv 64 0)) (v_addi (Z_to_bv 64 (ss_pc e5)) 4) mem6 (seg_rom tfibsegs)) md7 HS7 r_7)|].
intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [ms_mem mkst] in HF8. clear HFr8.
set (md8 := with_vm_backing (m_vm_lazy md7) mat8 md7) in *.
assert (MF8 : same_but_materialized md7 md8) by (subst md8; apply with_vm_backing_same).
pose proof shape7_ok as Hsh7. unfold shape7 in Hsh7.
apply andb_prop in Hsh7 as [Hsh7 Hsk7]. apply andb_prop in Hsh7 as [Hsh7 Hofl7]. apply andb_prop in Hsh7 as [Hsh7 HK7].
apply andb_prop in Hsh7 as [Hsh7 Z18]. apply andb_prop in Hsh7 as [Hsh7 Z9]. apply andb_prop in Hsh7 as [Hsh7 Z8]. apply andb_prop in Hsh7 as [Hsh7 Z2].
apply andb_prop in Hsh7 as [Hsh7 Z1]. apply andb_prop in Hsh7 as [Hsh7 Z10]. apply andb_prop in Hsh7 as [Hpc7 Hrv7]. apply Z.eqb_eq in Hpc7.
assert (Hresv7 : ss_resv e7 = None) by (destruct (ss_resv e7); [discriminate | reflexivity]).
unfold skels5 in Hsk7. destruct (ss_mem e7) as [|w0 [|w1 [|w2 [|w3 [|w4 [|? ?]]]]]] eqn:Hmem7; try discriminate Hsk7.
apply andb_prop in Hsk7 as [Hsk7 _]. apply andb_prop in Hsk7 as [Hsk7 _]. apply andb_prop in Hsk7 as [Hsk7 K72]. apply andb_prop in Hsk7 as [K70 _].
apply skel_is_sound in K70 as (K70a & K70lo & K70hi & K70b & K70c). apply skel_is_sound in K72 as (K72a & K72lo & K72hi & K72b & K72c).
assert (MEQ8 : forall z : word, ~ ((sp0 - 160 <= bv_unsigned z < sp0 - 144) \/ oflW (bv_unsigned z)) -> ms_mem ms8 z = mem6 z).
{ intros z Hz. apply (HF8 z). intros Hin. exact (Hz (WIN E5 _ _ WL7 E5_2 Hin)). }
clear HF8.
assert (RD8 : forall (r : bv 5) v, reg_is e7 (bv_unsigned r) v = true -> getr (ms_regs ms8) r = sv_denot E5 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E5 e7 ms8 r HS8). }
set (regs8 := ms_regs ms8) in *.
assert (PRS8s : forall a, sp0 - 160 <= a < sp0 - 144 -> apresent H (ms_mem ms8) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E5 e7 ms8 0 w0 a HS8 ltac:(rewrite Hmem7; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite K70a, K70b, K70c. cbn [base_val]. rewrite E5_2. lia. }
set (Wr8 := fun a => (sp0 - 160 <= a < sp0 - 144) \/ oflW a).
assert (Wr8d : forall a, Wr8 a \/ ~ Wr8 a) by (intros a; subst Wr8; cbn beta; unfold oflW; lia).
assert (Wr8i : forall a, Wr8 a -> (sp0 - 400 <= a < sp0) \/ (f <= a < f + 232) \/ oflW a) by (intros a Ha; subst Wr8; cbn beta in Ha; destruct Ha; [left; lia | right; right; assumption]).
assert (Wr8p : forall a, Wr8 a -> ~ oflW a -> apresent H (ms_mem ms8) a) by (intros a Ha Hno; subst Wr8; cbn beta in Ha; destruct Ha as [Ha|Ha]; [exact (PRS8s a Ha) | exfalso; exact (Hno Ha)]).
destruct (frameW mem6 (ms_mem ms8) md7 md8 Wr8 HAR7 Wr8d Wr8i MEQ8 Wr8p MF8) as (AV8 & PM8 & HAR8). subst Wr8. cbv beta in AV8. clear Wr8d Wr8i Wr8p.
pose proof (st_ok_restrict_mkst tfibsegs H E5 _ _ HS8 eq_refl) as Hshape8. rewrite Hpc7 in Hshape8. fold regs8 in Hshape8. rewrite Hshape8.
assert (MBtop : forall a, 0 <= a < 2 ^ 64 -> sp0 - 144 <= a < sp0 -> mbyte tfibsegs (mrestrict H (ms_mem ms8)) a = mbyte tfibsegs (mrestrict H (ms_mem ms2)) a).
{ intros a Hr Ha. unfold oflW in AV8, AV6. rewrite HO in AV8, AV6. apply AE2y.mbyte_of_aview.
rewrite AV8 by lia. rewrite AV6 by lia. rewrite AV5 by lia. rewrite AV4 by lia. apply AV3; lia. }
assert (PRS8 : forall a, sp0 - 400 <= a < sp0 -> apresent H (ms_mem ms8) a).
{ intros a Ha. unfold oflW in PM8, PM6. rewrite HO in PM8, PM6. apply PM8; [lia | lia |]. apply PM6; [lia | lia |]. apply PRS5'. exact Ha. }
pose proof (same_but_materialized_frame md7 md8 MF8) as (_ & V78 & L78 & _ & _ & _ & _ & _ & FD78 & _ & _ & FS78 & _).
assert (Efs : m_fs md8 = m_fs md4) by (rewrite FS78; subst md7; rewrite State.m_fs_with_fds, FS56, FS45; reflexivity).
assert (Efd : m_fds md8 = fd_remove (m_fds md) (Z_to_bv 64 fd)) by (rewrite FD78; subst md7; rewrite State.m_fds_with_fds, FD56, FD45, FDR4, FD03; reflexivity).
apply SRr_ret. split; [reflexivity|]. exists regs8, (ms_mem ms8), md8, v9, v18, mdw.
split; [unfold cfg_at; reflexivity|].
split; [exact HAR8|].
split; [rewrite (RD8 10%bv (SLit 0) Z10); reflexivity|].
split; [rewrite (RD8 1%bv (SLit FC_FREE1_RA) Z1); reflexivity|].
split; [rewrite (RD8 2%bv (SOff 2 0) Z2); cbn [sv_denot]; rewrite E5_2, Z.add_0_r, FT; reflexivity|].
split; [rewrite (RD8 8%bv (SOff 8 0) Z8); cbn [sv_denot]; rewrite E5_8, unsigned_lit_small, Z.add_0_r by lia; reflexivity|].
split; [rewrite (RD8 9%bv (SOff 10 0) Z9); cbn [sv_denot]; rewrite E5_10, unsigned_lit_small, Z.add_0_r by lia; reflexivity|].
split; [rewrite (RD8 18%bv (SLit 0) Z18); reflexivity|].
split.
{ intros r Hr. rewrite forallb_forall in HK7. pose proof (HK7 _ Hr) as Hk. cbn beta in Hk.
assert (Hr32 : 0 <= r < 32) by (unfold KEPT7 in Hr; cbn in Hr; lia).
assert (Hur : bv_unsigned (Z_to_bv 5 r) = r) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
unfold KEPT7 in Hr. cbn [In] in Hr.
rewrite (RD8 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)) by (rewrite Hur; exact Hk).
cbn [sv_denot]. rewrite (E5reg (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Hur; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (YK r) by (unfold AE2f.KEPTT; cbn [In]; lia).
rewrite (AP4 r) by (unfold acallee_saved; lia).
rewrite (TK r) by (unfold KEPTF; cbn [In]; lia).
rewrite (P2K r) by (unfold KEPT1; cbn [In]; lia).
apply (QK r). unfold KEPTC; cbn [In]; lia. }
split; [rewrite V78, V67, V56, V45, V4; exact V03|].
split; [rewrite L78, L67, L56, L45, L4; exact L03|].
split.
{ eapply os_kept_trans; [exact (os_kept_sbm _ _ MF03)|]. eapply os_kept_trans; [exact OK4|]. eapply os_kept_trans; [exact (os_kept_sbm _ _ MF5)|].
eapply os_kept_trans; [exact (os_kept_sbm _ _ MF6)|]. eapply os_kept_trans; [subst md7; apply os_kept_with_fds | exact (os_kept_sbm _ _ MF8)]. }
split; [rewrite Efs; exact FS4|].
split; [intros Hso; rewrite Efs; apply SO4; rewrite FS03; exact Hso|].
split; [exact Efd|].
split; [intros q Hq; rewrite Efs, (OTH4 q Hq), FS03; reflexivity|].
split; [exact Hv9|]. split; [exact Hv18|].
rewrite FT.
split; [apply (val_mem_frame tfibsegs (mrestrict H (ms_mem ms2))); [intros x Hx; apply MBtop; lia | replace (sp0 - 144 + 40) with (sp0 - 104) by lia; exact C2ra]|].
split; [apply (val_mem_frame tfibsegs (mrestrict H (ms_mem ms2))); [intros x Hx; apply MBtop; lia | replace (sp0 - 144 + 32) with (sp0 - 112) by lia; exact C2s0]|].
split; [apply (val_mem_frame tfibsegs (mrestrict H (ms_mem ms2))); [intros x Hx; apply MBtop; lia | replace (sp0 - 144 + 24) with (sp0 - 120) by lia; exact C2s1]|].
split; [apply (val_mem_frame tfibsegs (mrestrict H (ms_mem ms2))); [intros x Hx; apply MBtop; lia | replace (sp0 - 144 + 16) with (sp0 - 128) by lia; exact C2s2]|].
split; [apply (val_mem_frame tfibsegs (mrestrict H (ms_mem ms2))); [intros x Hx; apply MBtop; lia | replace (sp0 - 144 + 8) with (sp0 - 136) by lia; exact C2s3]|].
split.
{ intros j rz off Hj. assert (Hoff : -40 <= off <= -8) by (do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply (val_mem_frame tfibsegs (mrestrict H mem1)); [| exact (QS j rz off Hj)]. intros x Hx. rewrite (MBtop x) by lia.
apply AE2y.mbyte_of_aview. apply AV2; lia. }
split; [exact Hmdw|].
split.
{ unfold hdrZ_is. apply Forall_forall. intros [[o nn] v] Hin. apply (val_mem_frame tfibsegs (mrestrict H mem5)); [| exact (HC5 o nn v Hin)]. intros x Hx.
assert (Ho : 0 <= o /\ o + Z.of_nat (N.to_nat nn) <= 232).
{ unfold hdrZ_cells in Hin. cbn [In] in Hin. repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <- <-; cbn; lia|]). destruct Hin. }
unfold oflW in AV8, AV6. rewrite HO in AV8, AV6. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg.
apply AE2y.mbyte_of_aview. rewrite AV8 by lia. apply AV6; lia. }
split.
{
unfold has_chunk in Hofl7. rewrite Hmem7 in Hofl7. cbn [nth_error] in Hofl7. apply existsb_exists in Hofl7 as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E5 e7 _ HS8) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem7 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs w2 ltac:(INL)) as (_ & _ & _ & Hcs). rewrite K72a in Hcs. cbn [base_val] in Hcs.
rewrite <- (Z.add_0_l A_ofl_head). exact (val_of_chunk_ok tfibsegs E5 _ _ A_ofl_head 8 (SLit 0) 0 (proj1 (Forall_forall _ _) Hcs _ Hc) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
split.
{ intros a Hr Hs Hh Hofl. unfold oflW in *. rewrite HO in *. unfold TFIB_IMG_LO, TFIB_IMG_END in HBimg.
rewrite AV8 by lia. rewrite AV6 by lia. rewrite AV5 by lia. rewrite AV4 by lia. rewrite AV3 by lia. rewrite AV2 by lia. apply AV1; lia. }
split; [exact PRS8|].
intros a Hr Hofl Hp. unfold oflW in *. rewrite HO in *.
apply PM8; [lia | lia |]. apply PM6; [lia | lia |]. apply PM5, PM4, PM3. apply PM2; [lia | lia |]. apply PM1. exact Hp.
Qed.
End g.
Theorem fclose_L2 : forall (W2 : world tfibsegs) regs2 mem2 md2 (fv : Z),
getr regs2 8 = w64 fv -> 0 <= fv < 2 ^ 64 ->
SRr tfibsegs W2 (cfg_at tfibsegs FC_FREE1_RA regs2 mem2 md2)
(fun W' c' => W' = W2 /\ exists regs' md', c' = cfg_at tfibsegs PC_FREE regs' mem2 md' /\ same_but_materialized md2 md' /\
getr regs' 10 = w64 fv /\ getr regs' 1 = w64 FC_JOIN /\ (forall r, In r KEPTL2 -> getr regs' (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r))).
Proof.
intros W2 regs2 mem2 md2 fv G8 Hfv. pose proof AF0x.Hwx_tfa as Hwx. set (H2 := w_H W2).
set (E := AE2y.Env regs2 []).
assert (EregL : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs2 r) by (intros; apply AE2y.Env_reg; assumption).
assert (HS0 : st_ok tfibsegs E ssL2 (restrict H2 (mkst regs2 (Z_to_bv 64 FC_FREE1_RA) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssL2, E, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (map (Z_to_bv 64) [])) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. vm_compute. exact I.
- split; [|split; exact I]. cbn. exact I. }
unfold cfg_at. change (w64 FC_FREE1_RA) with (Z_to_bv 64 FC_FREE1_RA).
eapply SRr_bind; [exact (musl_phase W2 E ssL2 eL2 _ (mkst regs2 (Z_to_bv 64 FC_FREE1_RA) mem2 (seg_rom tfibsegs)) md2 HS0 r_L2)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [ms_mem mkst] in HF1. clear HFr1.
assert (MEQ : forall z : word, ms_mem ms1 z = mem2 z).
{ intros z. apply (HF1 z). intros (r & Hin & Hr). unfold ssL2 in Hin. cbn [ss_mem] in Hin. destruct Hin. }
assert (MEM : ms_mem ms1 = mem2) by (apply FunctionalExtensionality.functional_extensionality; exact MEQ).
pose proof shapeL2_ok as Hsh. unfold shapeL2 in Hsh.
apply andb_prop in Hsh as [Hsh _]. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh Q1]. apply andb_prop in Hsh as [Hsh Q10].
apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eL2 (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H2 E eL2 ms1 r HS1). }
pose proof (st_ok_restrict_mkst tfibsegs H2 E _ _ HS1 eq_refl) as Hshape. rewrite Hpc, MEM in Hshape. rewrite Hshape.
apply SRr_ret. split; [reflexivity|]. exists (ms_regs ms1), (with_vm_backing (m_vm_lazy md2) mat1 md2).
split; [reflexivity|]. split; [apply with_vm_backing_same|].
split; [rewrite (RD 10%bv (SOff 8 0) Q10); cbn [sv_denot]; rewrite (EregL 8%nat 8%bv eq_refl), G8, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
split; [rewrite (RD 1%bv (SLit FC_JOIN) Q1); reflexivity|].
intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTL2 in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK. specialize (HK _ Hin). cbn beta in HK.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (EregL (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK.
Qed.
Theorem fclose_L3 : forall (W3 : world tfibsegs) regs3 mem3 md3 (fv v9 v18 vra c8 c9 c18 c19 : Z),
let spT := spZ regs3 in let m3 := mrestrict (w_H W3) mem3 in
getr regs3 8 = w64 fv -> getr regs3 9 = w64 0 -> getr regs3 18 = w64 0 ->
2 ^ 43 <= spT -> spT + 144 <= 2 ^ 47 -> spT mod 16 = 0 -> 0 <= fv < 2 ^ 64 -> 0 <= v9 < 2 ^ 64 -> 0 <= v18 < 2 ^ 64 ->
val_mem tfibsegs m3 (spT + 40) 8 IC_RET -> val_mem tfibsegs m3 (spT + 32) 8 fv -> val_mem tfibsegs m3 (spT + 24) 8 v9 ->
val_mem tfibsegs m3 (spT + 16) 8 v18 -> val_mem tfibsegs m3 (spT + 8) 8 0 ->
val_mem tfibsegs m3 (spT + 136) 8 vra -> val_mem tfibsegs m3 (spT + 128) 8 c8 -> val_mem tfibsegs m3 (spT + 120) 8 c9 ->
val_mem tfibsegs m3 (spT + 112) 8 c18 -> val_mem tfibsegs m3 (spT + 104) 8 c19 ->
0 <= vra < 2 ^ 64 -> 0 <= c8 < 2 ^ 64 -> 0 <= c9 < 2 ^ 64 -> 0 <= c18 < 2 ^ 64 -> 0 <= c19 < 2 ^ 64 -> vra mod 2 = 0 ->
SRr tfibsegs W3 (cfg_at tfibsegs FC_JOIN regs3 mem3 md3)
(fun W' c' => W' = W3 /\ exists regs' md', c' = mkCfg (mkst regs' (w64 vra) mem3 (seg_rom tfibsegs)) md' /\ same_but_materialized md3 md' /\
getr regs' 10 = w64 0 /\ getr regs' 1 = w64 vra /\ getr regs' 2 = w64 (spT + 144) /\
getr regs' 8 = w64 c8 /\ getr regs' 9 = w64 c9 /\ getr regs' 18 = w64 c18 /\ getr regs' 19 = w64 c19 /\
(forall r, In r KEPT7 -> getr regs' (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r))).
Proof.
intros W3 regs3 mem3 md3 fv v9 v18 vra c8 c9 c18 c19 spT m3 G8 G9 G18 Hsplo Hsphi HalT Hfv Hv9 Hv18 D40 D32 D24 D16 D8 U136 U128 U120 U112 U104
Rra R8 R9 R18 R19 Heven.
pose proof AF0x.Hwx_tfa as Hwx. set (H3 := w_H W3) in *. assert (IFR : IC_FRAME = 96) by reflexivity.
set (E := AE2y.Env regs3 [0; 0; v9; v18]).
assert (EregL : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs3 r) by (intros; apply AE2y.Env_reg; assumption).
assert (E2 : bv_unsigned (ew E 2) = spT) by (rewrite (EregL 2%nat 2%bv eq_refl); reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 fv) by (rewrite (EregL 8%nat 8%bv eq_refl); exact G8).
assert (E9 : ew E 9 = Z_to_bv 64 0) by (rewrite (EregL 9%nat 9%bv eq_refl); exact G9).
assert (E18 : ew E 18 = Z_to_bv 64 0) by (rewrite (EregL 18%nat 18%bv eq_refl); exact G18).
assert (E34 : ew E 34 = Z_to_bv 64 v9) by (exact (AE2y.Env_x regs3 [0; 0; v9; v18] 2%nat v9 eq_refl)).
assert (E35 : ew E 35 = Z_to_bv 64 v18) by (exact (AE2y.Env_x regs3 [0; 0; v9; v18] 3%nat v18 eq_refl)).
assert (HS0 : st_ok tfibsegs E ssL3 (restrict H3 (mkst regs3 (Z_to_bv 64 FC_JOIN) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssL3, E, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (map (Z_to_bv 64) [0; 0; v9; v18])) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold stk3, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. unfold stk3_chunks.
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [reflexivity | unfold IC_RET; cbn; lia | cbn; lia | exact D40]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [cbn [sv_denot]; rewrite E8, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact D32]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact D24]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [cbn [sv_denot]; rewrite E35, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact D16]|].
apply Forall_cons; [eapply (chunk_ok_val tfibsegs E); [reflexivity | cbn; lia | cbn; lia | exact D8]|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. vm_compute. exact (conj I I).
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2. change (2 ^ 4) with 16.
repeat split; try lia; exact HalT. }
unfold cfg_at. change (w64 FC_JOIN) with (Z_to_bv 64 FC_JOIN).
eapply SRr_bind; [exact (musl_phase W3 E ssL3 eL3 _ (mkst regs3 (Z_to_bv 64 FC_JOIN) mem3 (seg_rom tfibsegs)) md3 HS0 r_L3)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [ms_mem mkst] in HF1. clear HFr1.
assert (MEQ : forall z : word, ms_mem ms1 z = mem3 z).
{ intros z. apply (HF1 z). intros (r & Hin & Hr). unfold ssL3 in Hin. cbn [ss_mem] in Hin. destruct Hin as [<-|[]]. cbn in Hr. lia. }
assert (MEM : ms_mem ms1 = mem3) by (apply FunctionalExtensionality.functional_extensionality; exact MEQ).
pose proof shapeL3_ok as Hsh. unfold shapeL3 in Hsh.
apply andb_prop in Hsh as [Hsh _]. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh Q19]. apply andb_prop in Hsh as [Hsh Q18]. apply andb_prop in Hsh as [Hsh Q9].
apply andb_prop in Hsh as [Hsh Q8]. apply andb_prop in Hsh as [Hsh Q2]. apply andb_prop in Hsh as [Hsh Q1]. apply andb_prop in Hsh as [Hsh Q10].
apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eL3 (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H3 E eL3 ms1 r HS1). }
pose proof (st_ok_restrict_mkst tfibsegs H3 E _ _ HS1 eq_refl) as Hshape. rewrite Hpc, MEM in Hshape. rewrite Hshape.
set (regs4 := ms_regs ms1) in *. set (md4 := with_vm_backing (m_vm_lazy md3) mat1 md3).
assert (P4_19 : getr regs4 19 = w64 0) by (rewrite (RD 19%bv (SLit 0) Q19); reflexivity).
assert (P4_2 : getr regs4 2 = w64 (spT + 48)) by (rewrite (RD 2%bv (SOff 2 48) Q2); cbn [sv_denot]; rewrite E2; reflexivity).
assert (R4sp : spZ regs4 = spT + 48) by (unfold spZ; rewrite P4_2; apply unsigned_lit_small; lia).
assert (P4_10 : getr regs4 10 = w64 0).
{ rewrite (RD 10%bv _ Q10). cbn [sv_denot]. rewrite E9, E18. apply bv_eq. vm_compute. reflexivity. }
change (Z_to_bv 64 IC_RET) with (w64 IC_RET).
eapply SRr_bind.
{ apply (iclose_tail W3 regs4 mem3 md4 vra c8 c9 c18 c19 P4_19); rewrite ?R4sp, ?IFR; try lia;
first [ replace (spT + 48) with (spT + 3 * 16) by lia; rewrite Z_mod_plus_full; exact HalT
| replace (spT + 48 + 88) with (spT + 136) by lia; exact U136
| replace (spT + 48 + 80) with (spT + 128) by lia; exact U128
| replace (spT + 48 + 72) with (spT + 120) by lia; exact U120
| replace (spT + 48 + 64) with (spT + 112) by lia; exact U112
| replace (spT + 48 + 56) with (spT + 104) by lia; exact U104
| exact Heven ]. }
intros W5 c5 _ (-> & regs5 & md5 & -> & MF5 & T1 & T2 & T8 & T9 & T18 & T19 & TK).
apply SRr_ret. split; [reflexivity|]. exists regs5, md5.
split; [reflexivity|]. split; [eapply same_but_materialized_trans; [apply with_vm_backing_same | exact MF5]|].
split; [etransitivity; [exact (TK 10 ltac:(unfold AE2e.KEPTT; INL)) | exact P4_10]|].
split; [exact T1|]. split; [rewrite T2, R4sp, IFR; unfold w64; f_equal; lia|].
split; [exact T8|]. split; [exact T9|]. split; [exact T18|]. split; [exact T19|].
intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPT7 in Hin; cbn in Hin; lia).
assert (Hur : bv_unsigned (Z_to_bv 5 r) = r) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; lia).
unfold KEPT7 in Hin. cbn [In] in Hin.
rewrite (TK r) by (unfold AE2e.KEPTT; cbn [In]; lia).
rewrite forallb_forall in HK. pose proof (HK r ltac:(unfold KEPT7; cbn [In]; lia)) as Hk. cbn beta in Hk.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)) by (rewrite Hur; exact Hk).
cbn [sv_denot]. rewrite (EregL (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Hur; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End d.
