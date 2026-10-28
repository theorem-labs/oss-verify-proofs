(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3 QWxq Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Qx2n QYTG Lib.SepCache QnDM QDUx Q9Ay Qy5Y QPUx Uy2A UvMd Q7wb U4l4 UzHs UDgQ U6hf UuJ9 UxDK Uoo0 UnKY UqYW U3qs QCqH QaBw QkUR UscZ UmCU UncX UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3.Mq2 QWxq.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Qx2n QYTG.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM.
Import QDUx Q9Ay.
Import Qy5Y QPUx.
Import Uy2A UvMd.
Import Q7wb.
Import U4l4 UzHs UDgQ U6hf UuJ9 UxDK Uoo0 UnKY UqYW U3qs.
Import QCqH QaBw.
Import QkUR UscZ.

Import UEQM.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hush := idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac br K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); try (exfalso; lia).
Tactic Notation "callx" tactic3(tac) := callw tac; try (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end).

Lemma strtod_file_raw : forall T p txt (fl : word) p0 (c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf : word) p1 (c152 c160 c168 c176 c184 c192 c200 c208 c216 c224 : word),
let J := mkJ fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c208 c216 c224 in
let f := mkSh txt 0 0 0 false false in
rf_cells_raw T p true f J c184 c192 c200 =
[C4 fl; CB 4 p0; C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 18446744073709551615); C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80;
C8 (Z_to_bv 64 T); C8 c96; C8 c104; C8 c112; C4 fd; C4 pp; C8 c128; C4 md; C4 lk; C4 lbf; CB 4 p1;
C8 c152; C8 c160; C8 c168; C8 c176; C8 c184; C8 c192; C8 c200; C8 c208; C8 c216; C8 c224].
Proof. intros. unfold rf_cells_raw, rf_rend. cbn. rewrite Z.add_0_r. reflexivity. Qed.

Theorem rstrtod_total_proof : UvMd.rstrtod_total_stmt.
Proof.
unfold UvMd.rstrtod_total_stmt. intros until ev. intros BY BYT Htxt Hlen Hlt PEC HS ST LO GT SPH Tpos HT T1 HPE HPE2 SEPE [SSP1 SSP2] ERR MI FRM Htp Ha0 Ha1.
cbv delta [rsegs] in *. fold rsegs in *.
unfold Uy2A.RSTRTOD_DEPTH, Uy2A.RGLOBALS_TOP, Uy2A.RIMG_LO, Uy2A.RATP in *. unfold Uy2A.RERRNO in *. unfold Uy2A.got_ssp, Uy2A.ssp_guard in SSP1, SSP2.
subst tp a0 a1.
pose_word_ranges.
assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map.
assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (subst txt; unfold zlength; rewrite length_app; cbn; lia).
unfold zlength in Hlt, SEPE, HT. unfold RGLOBALS_TOP in HT.
pose proof (munch_refl [(lo, bv_unsigned sp); (PE, PE + 8); (490332, 490332 + 4)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.

set (f0 := mkSh txt 0 0 0 false false).
pose proof HS as HS'. unfold scan_strtod_h in HS'. change (mkSh txt 0 0 0 false false) with f0 in HS'.
destruct (floatscan_h (fuel_of txt) f0 1 1) as [[fR yR]|] eqn:HM; [|discriminate HS'].
injection HS' as Ebits Eused.
assert (Hnul : znth txt (zlength pre) = 0%Z) by (subst txt; apply znth_app_mid).
assert (OK0 : sh_ok T txt f0).
{ unfold sh_ok, f0. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio]. unfold zlength in *. repeat split; try reflexivity; try lia; try (intros X; discriminate X). }
unfold Uy2A.RSTRTOD.

zs.
carve_frame 40%nat ST. rename FR into FRT.
carve_frame 232%nat ST. rename FR into FILE.
destruct (file_cells_of_junk _ _ _ _ FILE) as (fl & p0 & w8 & w16 & c24 & c32 & c40 & c48 & c56 & c64 & c72 & c80 & w88 & c96 & c104 & c112 & fd & pp & c128 & md & lk & lbf & p1 & c152 & c160 & c168 & c176 & c184 & c192 & c200 & c208 & c216 & c224 & FC & L0 & L1).
clear FILE. match goal with H : list byte |- _ => try clear H end.
zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
zs. zs. zs. zs.

set (J := mkJ fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c208 c216 c224).
rewrite <- (strtod_file_raw T (zlength pre) txt fl p0 c24 c32 c40 c48 c56 c64 c72 c80 c96 c104 c112 fd pp c128 md lk lbf p1 c152 c160 c168 c176 c184 c192 c200 c208 c216 c224) in FC.
fold J f0 in FC.
assert (RJ0 : RFJ T txt (zlength pre) true J 0 1 f0).
{ unfold RFJ, f0. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. split; [exact OK0|].
repeat split; try lia; intros X; try discriminate X; try lia. }
pose proof shlim_spec as SL. unfold shlim_stmt in SL.
zs. zs. zs. callx (eapply SL with (Fp := (bv_unsigned sp + -272)%Z) (T := T) (p := zlength pre) (w := true) (txt := txt) (f := f0) (J := J);
[exact FC | exact OK0 | exact L0 | exact L1 | lia | lia | unfold zlength in *; lia | assumption]).
clear SL.
match goal with H : rw_cells _ _ _ (rf_cells _ _ _ (sh_lim0 f0) _) |- _ => rename H into FC1 end. change (sh_lim0 f0) with f0 in FC1.
match goal with H : stk _ _ lo _ |- _ => rename H into STK end.

zs. zs. zs. zs.
destruct (stk_split _ _ _ (bv_unsigned sp + -272 - 8656)%Z _ STK ltac:(lia)) as [STlo SThi].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (UncX.Mq0.L_ENTRYh (Z_to_bv 64 0x5b554) (bv_unsigned sp + -272)%Z gp (Z_to_bv 64 PE) (Z_to_bv 64 T) (Z_to_bv 64 622192) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm
(bv_unsigned sp + -272)%Z T (zlength pre) J txt pre post canary 1%Z (fuel_of txt) f0 0%Z 1%Z fR yR) as LE end.
specialize (LE ltac:(right; reflexivity) eq_refl ltac:(intros X; exfalso; discriminate X) BYT Hp Hnul ltac:(unfold zlength in *; lia) ltac:(lia) T1
ltac:(unfold zlength in *; lia) ltac:(unfold UmCU.RERRNO, zlength in *; lia) ltac:(unfold UmCU.FS_DEPTH; lia) ltac:(lia) ltac:(lia)
ltac:(unfold UmCU.FS_DEPTH, zlength in *; lia) ltac:(unfold UmCU.FS_DEPTH, ssp_guard; lia) ltac:(unfold got_ssp, zlength in *; lia) ltac:(unfold ssp_guard, zlength in *; lia) ltac:(lia) FRM).
cbv zeta in LE. unfold UmCU.FS_DEPTH, UmCU.RERRNO, UmCU.FLOATSCAN, UmCU.RATP in LE.
unfold UmCU.fs_post, UmCU.Wfs, UmCU.FS_DEPTH, UmCU.RERRNO, UmCU.FokR in LE.
callx (eapply LE; [ exact HM | exact SThi | exact MI0 | exact FC1 | exact RJ0 | lia | lia | reflexivity | exact BY | split; [exact SSP1 | exact SSP2] | exact ERR ]).
clear LE.
match goal with H : rw_cells _ _ _ (rf_cells _ _ _ fR _) |- _ => rename H into FC2 end.
match goal with H : RFJ _ _ _ _ _ _ _ fR |- _ => rename H into RJ2 end.
match goal with H : ssp_cells _ canary |- _ => destruct H as [SSP3 SSP4]; unfold got_ssp, ssp_guard in SSP3, SSP4 end.
match goal with H : stk _ ?m' (bv_unsigned sp + -272 - 8656)%Z _ |- _ => pose proof (stk_merge _ _ _ _ _ STlo H ltac:(lia)) as STK2; clear H STlo end.
match goal with H : bytes_at _ _ T (zbytes txt) |- _ => rename H into BY2; unfold zbytes in BY2 end.
match goal with H : frm0 ?x |- evt _ _ (MS _ _ _ ?x _ _ _) => rename H into FRM2 end.
match goal with H : forall k : reg, _ -> _ -> _ -> reg_get _ k = reg_get F k |- _ => rename H into FOK end.
pose proof RJ2 as RJ3. destruct RJ3 as (OK2 & Rc2 & CC2 & KM2 & NS2 & SS2). destruct OK2 as (Hbuf2 & Rl2 & Rr2 & Rc02 & Rn2 & Rst2).
assert (JRR : JR (zlength pre) fR).
{ eapply (floatscan_h_JR txt (zlength pre) BYT Hp Hnul _ 1%Z eq_refl _ _ _ HM).
unfold JF, f0. cbn. repeat split; try reflexivity; try lia; intros X; try discriminate X; lia. }
unfold JR in JRR.
pose proof FC2 as FC3. unfold rf_cells in FC3.
cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale J] in FC3.
assert (RR : (0 <= rf_rend T (zlength pre) true fR <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio fR); unfold zlength in *; lia). unfold M64 in RR.

zs. (if_cases K0; zify_cond K0; try (rewrite ?signed_of_Z in K0 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs. zs. zs. zs.
match goal with H : rw_cells _ _ PE [C8 (Z_to_bv 64 ?v)] |- _ => replace v with (T + used)%Z in H by (rewrite <- Eused; unfold sh_cnt; lia) end.

zs. callx (eapply trunctfdf2_spec; [eassumption]).
cbv delta [rsegs] in *. fold rsegs in *.
rewrite !ulit_lo64, !ulit_hi64.
change (lo64 yR + 2 ^ 64 * hi64 yR)%Z with (canon yR). rewrite Q9Ay.f128_to_d_canon. rewrite Ebits.

zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs. zs. zs.
match goal with H : stk _ ?m' lo _, H2 : mem_inv _ ?m' |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename H into ST9; rename H2 into MI9 end.
release_frame FC3 ST9 (bv_unsigned sp + -40)%Z.
release_frame FRT ST9 (bv_unsigned sp).
apply evt_done. unfold Uy2A.rstrtod_post, Uy2A.ssp_cells, Uy2A.got_ssp, Uy2A.ssp_guard, Uy2A.RERRNO.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [unfold UmCU.RATP; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI9|]. split; [exact FRM2|].
split. { intros k H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity). exact (FOK k H10 H14 H15). }
split; [rewrite freg_get_same by (vm_compute; reflexivity); reflexivity|].
split; [exact ST9|]. split; [hyp|]. split; [exact BY2|]. split; [split; [exact SSP3 | exact SSP4]|]. split; [match goal with H : rw_cells _ _ 490332 _ |- _ => exact H end|].
rewrite <- Eused. unfold sh_cnt. lia.
Qed.

Theorem scan_strtod_h_total_proof : UvMd.scan_strtod_h_total_stmt.
Proof. exact scan_strtod_h_total. Qed.
End Mq0.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2TC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QROt.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXTs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXTs.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxSL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un81. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7Jg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7Jg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UVfK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UVfK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UISU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UISU. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8bj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8bj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x531d4%Z.
Definition w_14 := 0x00012517%Z.
Definition w_15 := 0x7c453a03%Z.
Definition w_18 := 0x00045597%Z.
Definition w_19 := 0xd5c58b13%Z.
Definition w_114 := 0xfffc3597%Z.
Definition w_116 := 0x18458593%Z.
Definition w_121 := 0xfffc3517%Z.
Definition w_122 := 0x18850c93%Z.
Definition w_130 := 0x00045597%Z.
Definition w_131 := 0xae45b583%Z.
Definition w_136 := 0xfffc3697%Z.
Definition w_137 := 0x1ac68693%Z.
Definition w_148 := 0xfffc3697%Z.
Definition w_149 := 0x19768693%Z.
Definition w_218 := 0xfffc3697%Z.
Definition w_220 := 0xfe468693%Z.
Definition w_311 := 0xfffc3717%Z.
Definition w_313 := 0xe9070713%Z.
Definition w_427 := 0x18d000ef%Z.
Definition w_552 := 0xdb0fd0ef%Z.
Definition hi_14 := (Z_to_bv 20 18).
Definition hi_18 := (Z_to_bv 20 69).
Definition hi_114 := (Z_to_bv 20 1048515).
Definition hi_121 := (Z_to_bv 20 1048515).
Definition hi_130 := (Z_to_bv 20 69).
Definition hi_136 := (Z_to_bv 20 1048515).
Definition hi_148 := (Z_to_bv 20 1048515).
Definition hi_218 := (Z_to_bv 20 1048515).
Definition hi_311 := (Z_to_bv 20 1048515).
Definition lo_15 := (Z_to_bv 12 1988).
Definition lo_19 := (Z_to_bv 12 3420).
Definition lo_116 := (Z_to_bv 12 388).
Definition lo_122 := (Z_to_bv 12 392).
Definition lo_131 := (Z_to_bv 12 2788).
Definition lo_137 := (Z_to_bv 12 428).
Definition lo_149 := (Z_to_bv 12 407).
Definition lo_220 := (Z_to_bv 12 4068).
Definition lo_313 := (Z_to_bv 12 3728).
Definition joff_427 := (Z_to_bv 21 2444).
Definition joff_552 := (Z_to_bv 21 2086320).
Definition e_197bc := 0x51024%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x531d4 (QROt.Mq3.alloc_slot_code 0x00012517%Z 0x7c453a03%Z 0x00045597%Z 0xd5c58b13%Z 0xfffc3597%Z 0x18458593%Z 0xfffc3517%Z 0x18850c93%Z 0x00045597%Z 0xae45b583%Z 0xfffc3697%Z 0x1ac68693%Z 0xfffc3697%Z 0x19768693%Z 0xfffc3697%Z 0xfe468693%Z 0xfffc3717%Z 0xe9070713%Z 0x18d000ef%Z 0xdb0fd0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x531d4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x531d4 /\ 0x531d4 + 2212 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.rconc_meta_stable') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.rconc_meta_stable')]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q2TC.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@Q2TC.rmalloc_fp) (@UDxd.rmalloc_fp) Q6nq.gwt_nil)))).
#[using="Type"] Lemma rmalloc_fp_widen : ltac2:(Q6nq.ty2 'GwI.segs '(@Q2TC.rmalloc_fp_widen) [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.rmalloc_fp_widen) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.rmalloc_fp_widen)]. Qed.

#[using="Type"] Lemma rregion_byte_raw : ltac2:(Q6nq.ty2 'GwI.segs '(@Q2TC.rregion_byte_raw) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.rregion_byte_raw) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.rregion_byte_raw)]. Qed.

#[using="Type"] Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x77b5c.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.rerrno_lit5) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.rerrno_lit5)]. Qed.

Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := QULt.Mq1.ist_facts_proof st0 LB st AR IS.

Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
mkR (Z_to_bv 64 0x535b4) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6'.
Lemma gw_eq_rnest_regs : @rnest_regs = ltac:(GwInst.gw_term (@Q2TC.rnest_regs 0x531d4 UKNz.RATP UKNz.RDEBRUIJN) (@rnest_regs)). Proof. unfold rnest_regs, Q2TC.rnest_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rnest_regs : gw_eqs.

Definition rnest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
(m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
mem_inv rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp - 144) /\
rw_cells rsegs m'' (errno_addr tp) [C4 errv''] /\ rauxv_ok m'' (bv_unsigned sp - 144) /\
rmrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
rpres_except (rmalloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
rw_cells rsegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ rmrep st2 m4.

Definition rNFAIL_stmt : Prop :=
forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
rnest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 -> errv'' = Z_to_bv 64 12 ->
rimplT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
(MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
F (Z_to_bv 64 0x5362c) fc None m'' (seg_rom rsegs)).

Definition rNSUCC_stmt : Prop :=
forall st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
rnest_ctx st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 ->
0 <= idx -> active st3 (ncls sc cnt1) = Some g3 -> slot_ok st3 g3 b3 r3 idx (nreq sc cnt1) ->
(forall a, r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx - 4 <= a
< r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx + get_stride (get_meta_rec st3 g3) - 4 ->
rmalloc_fp st0 st3 lo (bv_unsigned sp - 144) a) ->
(s_regions st0 = ∅ -> rdv pans_mem o st3 (fst b3, snd b3 + (16 + get_stride (get_meta_rec st3 g3) * idx) + -3) = 0) ->
rimplT o (ag_tail full_lay (upd_meta mm (m_set_maplen 0) (nest_layout st3 g3 idx (ncls sc cnt1) (UNIT * size_class sc) cnt1))
sc mm (slot_of st3 g3 idx) cnt1 (cnt1 - 1) (as_kq sc k bail)) s'' Q
(MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 idx) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
F (Z_to_bv 64 0x535b8) fc None m'' (seg_rom rsegs)).
End LEVEL.
Lemma gw_eq_rnest_regs__2 : @rnest_regs = ltac:(GwInst.gw_term (@Q2TC.rnest_regs 0x531d4 UKNz.RATP UKNz.RDEBRUIJN) (@rnest_regs)). Proof. unfold rnest_regs, Q2TC.rnest_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rnest_regs__2 : gw_eqs.

End RC__1.
Lemma gw_eq_rnest_regs__3 : @rnest_regs = ltac:(GwInst.gw_term (@Q2TC.rnest_regs 0x531d4 UKNz.RATP UKNz.RDEBRUIJN) (@rnest_regs)). Proof. unfold rnest_regs, Q2TC.rnest_regs; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rnest_regs__3 : gw_eqs.
