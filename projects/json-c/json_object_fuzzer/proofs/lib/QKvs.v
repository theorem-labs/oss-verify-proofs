(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Qx2n QYTG Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx QJVP Q6VZ Q7wb Qbf8 QSzV QcAG Qcjh QvBB QnkH Qi8L QmBS QKwd Qlfl QCqH QaBw QWjN QzYe QHB6 QWzD QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Qx2n QYTG.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import QJVP.Mq0 Q6VZ.Mq0.
Import Q7wb.
Import Qbf8 QSzV QcAG Qcjh QvBB.Mq1 QnkH.Mq1 Qi8L.Mq1 QmBS.Mq0 QKwd Qlfl.Mq0.
Import QCqH QaBw.
Import QWjN QzYe.

Import QTp6.
Import ListNotations. Unset Keyed Unification.
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

Theorem rstrtod_total_proof : Q6VZ.Mq0.rstrtod_total_stmt.
Proof.
unfold Q6VZ.Mq0.rstrtod_total_stmt. intros until ev. intros BY BYT Htxt Hlen Hlt PEC HS ST LO GT SPH Tpos HT T1 HPE HPE2 SEPE [SSP1 SSP2] ERR MI FRM Htp Ha0 Ha1.
cbv delta [rsegs] in *. fold rsegs in *.
unfold QJVP.Mq0.RSTRTOD_DEPTH, QJVP.Mq0.RGLOBALS_TOP, QJVP.Mq0.RIMG_LO, QJVP.Mq0.RATP in *. unfold QJVP.Mq0.RERRNO in *. unfold QJVP.Mq0.got_ssp, QJVP.Mq0.ssp_guard in SSP1, SSP2.
subst tp a0 a1.
pose_word_ranges.
assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map.
assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (subst txt; unfold zlength; rewrite length_app; cbn; lia).
unfold zlength in Hlt, SEPE, HT. unfold RGLOBALS_TOP in HT.
pose proof (munch_refl [(lo, bv_unsigned sp); (PE, PE + 8); (6434236, 6434236 + 4)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.

set (f0 := mkSh txt 0 0 0 false false).
pose proof HS as HS'. unfold scan_strtod_h in HS'. change (mkSh txt 0 0 0 false false) with f0 in HS'.
destruct (floatscan_h (fuel_of txt) f0 1 1) as [[fR yR]|] eqn:HM; [|discriminate HS'].
injection HS' as Ebits Eused.
assert (Hnul : znth txt (zlength pre) = 0%Z) by (subst txt; apply znth_app_mid).
assert (OK0 : sh_ok T txt f0).
{ unfold sh_ok, f0. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio]. unfold zlength in *. repeat split; try reflexivity; try lia; try (intros X; discriminate X). }
unfold QJVP.Mq0.RSTRTOD.

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
pose proof (QWzD.Mq0.L_ENTRYh (Z_to_bv 64 0xda64c) (bv_unsigned sp + -272)%Z gp (Z_to_bv 64 PE) (Z_to_bv 64 T) (Z_to_bv 64 6565536) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm
(bv_unsigned sp + -272)%Z T (zlength pre) J txt pre post canary 1%Z (fuel_of txt) f0 0%Z 1%Z fR yR) as LE end.
specialize (LE ltac:(right; reflexivity) eq_refl ltac:(intros X; exfalso; discriminate X) BYT Hp Hnul ltac:(unfold zlength in *; lia) ltac:(lia) T1
ltac:(unfold zlength in *; lia) ltac:(unfold QHB6.Mq0.RERRNO, zlength in *; lia) ltac:(unfold QHB6.Mq0.FS_DEPTH; lia) ltac:(lia) ltac:(lia)
ltac:(unfold QHB6.Mq0.FS_DEPTH, zlength in *; lia) ltac:(unfold QHB6.Mq0.FS_DEPTH, ssp_guard; lia) ltac:(unfold got_ssp, zlength in *; lia) ltac:(unfold ssp_guard, zlength in *; lia) ltac:(lia) FRM).
cbv zeta in LE. unfold QHB6.Mq0.FS_DEPTH, QHB6.Mq0.RERRNO, QHB6.Mq0.FLOATSCAN, QHB6.Mq0.RATP in LE.
unfold QHB6.Mq0.fs_post, QHB6.Mq0.Wfs, QHB6.Mq0.FS_DEPTH, QHB6.Mq0.RERRNO, QHB6.Mq0.FokR in LE.
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
apply evt_done. unfold QJVP.Mq0.rstrtod_post, QJVP.Mq0.ssp_cells, QJVP.Mq0.got_ssp, QJVP.Mq0.ssp_guard, QJVP.Mq0.RERRNO.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [unfold QHB6.Mq0.RATP; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI9|]. split; [exact FRM2|].
split. { intros k H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity). exact (FOK k H10 H14 H15). }
split; [rewrite freg_get_same by (vm_compute; reflexivity); reflexivity|].
split; [exact ST9|]. split; [hyp|]. split; [exact BY2|]. split; [split; [exact SSP3 | exact SSP4]|]. split; [match goal with H : rw_cells _ _ 6434236 _ |- _ => exact H end|].
rewrite <- Eused. unfold sh_cnt. lia.
Qed.

Theorem scan_strtod_h_total_proof : Q6VZ.Mq0.scan_strtod_h_total_stmt.
Proof. exact scan_strtod_h_total. Qed.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QyjG QM7w QNAo QXTs QCwx QFqQ Q98Z QkLq QdZ1 Qv4L QQbX QYnB QULt Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QM7w QNAo.Mq0 QXTs.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QmBS.Mq1 Qlfl.Mq3 QHB6.Mq1 QYnB.Mq4.

Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
intros MR REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

#[using="Type"] Lemma rmalloc_fp_widen st0 stA stB lo sp sp' a :
sp' <= sp ->
(forall rid r, (s_regions stA) !! rid = Some r ->
exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rmalloc_fp st0 stA lo sp' a -> rmalloc_fp st0 stB lo sp a.
Proof.
intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

#[using="Type"] Lemma rregion_byte_raw st m rid r off v :
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) off = Known v -> m (wa (r_base r + off)) = Some (b8 v).
Proof.
intros MR Hr Hk Ho Hc.
destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
cbn [ov_read_bytes] in RD.
destruct (m (wa (r_base r + off))) as [b|] eqn:E.
- cbn in RD. inversion RD. reflexivity.
- rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

#[using="Type"] Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x622dbc.
Proof. intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

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
mkR (Z_to_bv 64 0xced80) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6'.

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
F (Z_to_bv 64 0xcedf8) fc None m'' (seg_rom rsegs)).

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
F (Z_to_bv 64 0xced84) fc None m'' (seg_rom rsegs)).
End LEVEL.

End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE Q5JI QR6G Quzq QdmE QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Qx2n QYTG.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import QJVP Q6VZ.
Import Q7wb.
Import QeTw Q1BE Q5JI QR6G QvBB.Mq2 QnkH.Mqd Qi8L.Mq7 QmBS.Mq5 Quzq Qlfl.Mq5.
Import QCqH QaBw.
Import Q98Z QdmE.

Import QBpX.
Import ListNotations. Unset Keyed Unification.
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

Theorem rstrtod_total_proof : Q6VZ.rstrtod_total_stmt.
Proof.
unfold Q6VZ.rstrtod_total_stmt. intros until ev. intros BY BYT Htxt Hlen Hlt PEC HS ST LO GT SPH Tpos HT T1 HPE HPE2 SEPE [SSP1 SSP2] ERR MI FRM Htp Ha0 Ha1.
cbv delta [usegs] in *. fold usegs in *.
unfold QJVP.RSTRTOD_DEPTH, QJVP.RGLOBALS_TOP, QJVP.RIMG_LO, QJVP.RATP in *. unfold QJVP.RERRNO in *. unfold QJVP.got_ssp, QJVP.ssp_guard in SSP1, SSP2.
subst tp a0 a1.
pose_word_ranges.
assert (LT : length (map (Z_to_bv 8) txt) = length txt) by apply length_map.
assert (Hp : (0 <= zlength pre < zlength txt)%Z) by (subst txt; unfold zlength; rewrite length_app; cbn; lia).
unfold zlength in Hlt, SEPE, HT. unfold RGLOBALS_TOP in HT.
pose proof (munch_refl [(lo, bv_unsigned sp); (PE, PE + 8); (6444156, 6444156 + 4)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

set (f0 := mkSh txt 0 0 0 false false).
pose proof HS as HS'. unfold scan_strtod_h in HS'. change (mkSh txt 0 0 0 false false) with f0 in HS'.
destruct (floatscan_h (fuel_of txt) f0 1 1) as [[fR yR]|] eqn:HM; [|discriminate HS'].
injection HS' as Ebits Eused.
assert (Hnul : znth txt (zlength pre) = 0%Z) by (subst txt; apply znth_app_mid).
assert (OK0 : sh_ok T txt f0).
{ unfold sh_ok, f0. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio]. unfold zlength in *. repeat split; try reflexivity; try lia; try (intros X; discriminate X). }
unfold QJVP.RSTRTOD.

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
pose proof (QWzD.L_ENTRYh (Z_to_bv 64 0xdcd10) (bv_unsigned sp + -272)%Z gp (Z_to_bv 64 PE) (Z_to_bv 64 T) (Z_to_bv 64 6575456) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm
(bv_unsigned sp + -272)%Z T (zlength pre) J txt pre post canary 1%Z (fuel_of txt) f0 0%Z 1%Z fR yR) as LE end.
specialize (LE ltac:(right; reflexivity) eq_refl ltac:(intros X; exfalso; discriminate X) BYT Hp Hnul ltac:(unfold zlength in *; lia) ltac:(lia) T1
ltac:(unfold zlength in *; lia) ltac:(unfold QHB6.Mq3.RERRNO, zlength in *; lia) ltac:(unfold QHB6.Mq3.FS_DEPTH; lia) ltac:(lia) ltac:(lia)
ltac:(unfold QHB6.Mq3.FS_DEPTH, zlength in *; lia) ltac:(unfold QHB6.Mq3.FS_DEPTH, ssp_guard; lia) ltac:(unfold got_ssp, zlength in *; lia) ltac:(unfold ssp_guard, zlength in *; lia) ltac:(lia) FRM).
cbv zeta in LE. unfold QHB6.Mq3.FS_DEPTH, QHB6.Mq3.RERRNO, QHB6.Mq3.FLOATSCAN, QHB6.Mq3.RATP in LE.
unfold QHB6.Mq3.fs_post, QHB6.Mq3.Wfs, QHB6.Mq3.FS_DEPTH, QHB6.Mq3.RERRNO, QHB6.Mq3.FokR in LE.
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
cbv delta [usegs] in *. fold usegs in *.
rewrite !ulit_lo64, !ulit_hi64.
change (lo64 yR + 2 ^ 64 * hi64 yR)%Z with (canon yR). rewrite Q9Ay.f128_to_d_canon. rewrite Ebits.

zs. zs. zs. (if_cases K1; zify_cond K1; try (rewrite ?signed_of_Z in K1 by lia); [ exfalso; lia | ]).
zs. zs. zs. zs. zs. zs.
match goal with H : stk _ ?m' lo _, H2 : mem_inv _ ?m' |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename H into ST9; rename H2 into MI9 end.
release_frame FC3 ST9 (bv_unsigned sp + -40)%Z.
release_frame FRT ST9 (bv_unsigned sp).
apply evt_done. unfold QJVP.rstrtod_post, QJVP.ssp_cells, QJVP.got_ssp, QJVP.ssp_guard, QJVP.RERRNO.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [unfold QHB6.Mq3.RATP; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI9|]. split; [exact FRM2|].
split. { intros k H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity). exact (FOK k H10 H14 H15). }
split; [rewrite freg_get_same by (vm_compute; reflexivity); reflexivity|].
split; [exact ST9|]. split; [hyp|]. split; [exact BY2|]. split; [split; [exact SSP3 | exact SSP4]|]. split; [match goal with H : rw_cells _ _ 6444156 _ |- _ => exact H end|].
rewrite <- Eused. unfold sh_cnt. lia.
Qed.

Theorem scan_strtod_h_total_proof : Q6VZ.scan_strtod_h_total_stmt.
Proof. exact scan_strtod_h_total. Qed.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXTs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXTs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmBS.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qlfl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qlfl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHB6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHB6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnB.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rconc_meta_stable' st stE m q : rmrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
intros MR REL (ar & arr & kk & Ha & Hk & ->). pose proof MR as (WF & _). pose proof WF as (_ & _ & _ & WA & _).
destruct (WA ar arr Ha) as (r & Hr & _). destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _).
unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

#[using="Type"] Lemma rmalloc_fp_widen st0 stA stB lo sp sp' a :
sp' <= sp ->
(forall rid r, (s_regions stA) !! rid = Some r ->
exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
rmalloc_fp st0 stA lo sp' a -> rmalloc_fp st0 stB lo sp a.
Proof.
intros LE HR H. apply (rmalloc_fp_mono st0 stA stB lo sp a HR).
destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

#[using="Type"] Lemma rregion_byte_raw st m rid r off v :
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) off = Known v -> m (wa (r_base r + off)) = Some (b8 v).
Proof.
intros MR Hr Hk Ho Hc.
destruct (rmrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2). unfold alloc_ceiling in RC.
specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
cbn [ov_read_bytes] in RD.
destruct (m (wa (r_base r + off))) as [b|] eqn:E.
- cbn in RD. inversion RD. reflexivity.
- rewrite ref_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

#[using="Type"] Lemma rerrno_lit5 (tp : word) : tp = Z_to_bv 64 RATP -> errno_addr tp = 0x62547c.
Proof. intros ->. unfold RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

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
Hypothesis ST : stk usegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells usegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv usegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := QULt.Mq1.ist_facts_proof st0 LB st AR IS.

Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
mkR (Z_to_bv 64 0xd1444) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6'.

Definition rnest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
(m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
mem_inv usegs m'' /\ stk usegs m'' lo (bv_unsigned sp - 144) /\
rw_cells usegs m'' (errno_addr tp) [C4 errv''] /\ rauxv_ok m'' (bv_unsigned sp - 144) /\
rmrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
rpres_except (rmalloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
rw_cells usegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ rmrep st2 m4.

Definition rNFAIL_stmt : Prop :=
forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
rnest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 -> errv'' = Z_to_bv 64 12 ->
rimplT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
(MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
F (Z_to_bv 64 0xd14bc) fc None m'' (seg_rom usegs)).

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
F (Z_to_bv 64 0xd1448) fc None m'' (seg_rom usegs)).
End LEVEL.

End RC__1.
