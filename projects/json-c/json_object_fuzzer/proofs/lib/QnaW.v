(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW Q13u QDM6 QJFf QwAs Qc6I QVsB Qcrs Q0z1 QCiC Qpj5 QCNF QoNr QdZp Qu3b QnRU QteI QoBx Qs9x QC9y QQNJ Q8zl QvG1 QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QTVW.Mq5.
Import Q13u QDM6 QJFf.Mq0 QwAs.Mq1 Qc6I QJFf QVsB.

Import Q0z1.
Import QCiC.Mq1 Qpj5.Mq1. Import QCNF.Mq1 QoNr. Import QdZp.
Import Qu3b.Mq3.
Import QTVW.Mq1 Qu3b.Mq1 QnRU.Mq3 QnRU.Mq4 QteI.Mq1.
Import QCNF.Mq0.
Import QoBx Qu3b.Mq0.
Import Qs9x QC9y.
Import QQNJ.Mq1 Q8zl.Mq0.
Import QvG1.
Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_2 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_3 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_4 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_5 := lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
[C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].

Definition towrite_g_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
rw_cells asegs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
Z.land (bv_unsigned flags) 8 = 0 ->
(0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3374) fc None m (seg_rom asegs)).

Theorem towrite_g_proof : towrite_g_stmt.
Proof.
unfold towrite_g_stmt. intros until lbf. intros FC NOWR B0 BHI BS0 MI.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size gfile_cells csize Nat.add] in FB.
set (Fp := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(Fp, Fp + 148)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold gfile_cells in FC.
assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
do 5 zs. rewrite FL8. zs. zs. if_lit.
do 10 zs.
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold gfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

Theorem towrite_proof : towrite_stmt.
Proof.
unfold towrite_stmt. intros until tail. intros FC NOWR B0 BHI BS0 MI.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size file_cells csize Nat.add] in FB.
set (Fp := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
do 5 zs. rewrite FL8. zs. zs. if_lit.
do 10 zs.
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | let t := type of H in idtac "FC:" t; fail] end.
Qed.

Lemma arg_ok_vf {BAND : Band} : forall Fp B BS m m' lo sp sp' ap w a,
arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
destruct H as (slack & BY & HF & PAD & NZ & SZ & D1 & D2 & D3 & D4 & D5). exists slack.
split; [|repeat (split; [first [assumption | lia]|]); exact D5].
eapply bytes_at_transport; [exact BY | exact MU |].
cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf {BAND : Band} : forall Fp B BS m m' lo sp sp' ap ws args,
args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
rw_cells asegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
rw_cells asegs m A (pre ++ mid ++ post).
Proof.
intros m A pre mid post [[Hwf Hb] Hw] WF.
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
split; [split|].
- apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells asegs m B [CB 0 []].
Proof.
intros m B H0 H1. split; [split|].
- cbn. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition VF_FRAME : Z := 368.

Definition vf_saves_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (m' : word -> option byte) (j1 j2 : list byte),
ms' = MS (mkR (Z_to_bv 64 0xd38c4) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp t0 t1 t2 a0 a1 (Z_to_bv 64 0) a1
(Z_to_bv 64 (bv_unsigned sp + -368)) (Z_to_bv 64 (bv_unsigned sp + -272)) (Z_to_bv 64 (bv_unsigned sp + -104)) a5 a6 a7
(Z_to_bv 64 0x642ea0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3a0c) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 368, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned sp + -368)
[C8 a2; C8 a2; CB 80 j1; CB 168 j2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -368).

Lemma vf_saves {BAND : Band} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 368 -> band_lo <= lo -> mem_inv asegs m ->
rw_cells asegs m 0xe6b80 [C8 (Z_to_bv 64 0x642ea0)] -> rw_cells asegs m 0x642ea0 [C8 canary] ->
evt asegs (vf_saves_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd385c) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST LO LO0 MI SSP1 SSP2.
pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 368%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 368 _ _ [8;8;80;168;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR.
do 26 (zstep; try (fix_litstore; mem_after_store_opt)).
apply evt_done. unfold vf_saves_post. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [| exact ST].
lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -368) _ |- _ => exact H end.
Qed.

Lemma fmt_bytes_at : forall m A f, mem_inv asegs m -> ro_bytes_b asegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
bytes_at asegs m A (zb f).
Proof.
intros m A f MI RB H0 H1.
pose proof (ro_cells_bytes_at asegs m A _ (ro_cells_image asegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 QHig QBrp Qsn5 Q6sh QQwg QKTr QJBH QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QpY2 QYyZ QmP7 Q9Ho QOJv QOH4 QMSY QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QYyZ.Mq4 QmP7.Mq0 QYyZ.Mq0 QnRU.Mq0 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QnRU.Mq7 Q9Ho.Mq1 QOJv.Mq5 Qu3b.Mq2 QteI.Mq4 QOH4 Q8zl.Mq2 QQNJ.Mq6.
Import QpY2.Mq2.
Import QMSY.
Import QlES.
Export QVo2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition comb_W (sp c au : Z) : list (Z * Z) :=
[ (sp - COMB_STACK, sp); (rl_T X + 208, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8) ].

Definition comb_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (c lo : Z) (m : word -> option byte)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (comb_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ gstep RE X a (snd r) G G1
/\ if fst r then
exists i, tag_at G1 c i = Some TCached /\ a0 = wz (slot_beg RE c i)
/\ (forall t, tag_prim t = false -> RPrim (snd r) (set_tag c i t G1) RE X m')
/\ hjunk m' (slot_beg RE c i) (slot_beg RE c i + class_size c)
/\ rw_cells asegs m' (SH (slot_beg RE c i)) [CB (Z.to_nat (class_size c / 8)) (repeat fa_byte (Z.to_nat (class_size c / 8)))]
else a0 = wz 0 /\ RPrim (snd r) G1 RE X m'.

Lemma comb_tail : forall ra gp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (v0 v1 v2 v3 v4 vra sp : word)
(F : bvmap 5 word) fc (m0 m : word -> option byte) (s : PStateA) (a aX : AState) (G GX : ghost) (c lo : Z),
let cnt := c_count (cls aX c) in
rlay_ok RE X -> 1 <= c <= 30 -> 1 <= cnt -> as_cache_inited aX = true -> gstep RE X a aX G GX ->
RTconst RE X m -> RStats RE X m -> RPrim aX GX RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -48) ->
band_lo <= lo -> lo <= bv_unsigned sp - COMB_STACK ->
munch (comb_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m0 m -> wmono asegs m0 m ->
rw_cells asegs m (bv_unsigned sp + -48) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
evt asegs (comb_post vra sp gp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c lo m0 (true, upd_cls c (fun y => set_count (c_count y - 1) y) aX) s)
(MS (mkR ra (wz (bv_unsigned sp + -48)) gp (wz A_TP) t0 t1 t2 (wz c) (wz (pc_addr X c)) (wz A_INSTANCE) (wz (rl_T X + 208)) (wz cnt) (wz 8) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43a54) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros cnt RL Hc CNT EI GS RT RS RP MI ST CEIL LO MU WM FR.
pose proof CEIL as CEIL'. idtac. unfold COMB_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (max_count_facts c ltac:(lia)) as [MC1 _]. pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2.
pose proof (bsize_eq c ltac:(lia)) as BSZ.

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC. apply class_rep_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & _ & _ & _ & P6 & _ & _ & P9 & _).
cbv beta delta [pc_cells] in PC0. rewrite EI, BSZ in PC0. clear RI. subst cnt.
set (cnt := c_count (cls aX c)) in *.
set (i := nth (Z.to_nat (cnt - 1)) (pk_ca (K c)) 0).
assert (CHI : nth_error CH (Z.to_nat (cnt - 1)) = Some (wz (coff c i))) by (apply HCH; lia).
assert (HIN : In i (pk_ca (K c))) by (apply nth_In; lia).
pose proof (P6 i HIN) as TI. pose proof (tag_at_Some_lt _ _ _ _ TI) as [I0 I1]. unfold ncarved in I1.
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _). rewrite KO in G4.
assert (CF : 0 <= coff c i /\ coff c i * 16 <= 3758096384).
{ pose proof (coff_shl4 RE c i ltac:(lia) I0) as E. unfold slot_beg in E. clear - I0 I1 G1 G3 G4 SZ1 E. nia. }

pose proof HJS as HJ0. destruct (hjunk_split _ _ (rl_T X + 2784) _ HJ0 ltac:(lia)) as [_ HJ1].
destruct (hjunk_split _ _ (rl_T X + 2792) _ HJ1 ltac:(lia)) as [HJ2 _].
replace (rl_T X + 2792) with (rl_T X + 2784 + 8) in HJ2 by lia. destruct (hjunk_C8 _ _ HJ2) as [w3 STA]. clear HJ0 HJ1 HJ2.
assert (AMO : amo_aligned AD (wz (rl_T X + 2784)) = true) by (apply amo_aligned_intro8; [lia| unhide TA; Z.div_mod_to_equations; lia]).
rtc RT 24%nat K24. unfold A_INSTANCE in *.
remember (pc_addr X c) as PCA eqn:EPCA. unfold pc_addr in EPCA.
pose proof (munch_refl [(PCA, PCA + 4); (rl_T X + 2784, rl_T X + 2792)] m) as MUt. pose proof (wmono_refl asegs m) as WMt.
unfold comb_W, COMB_STACK, ri_addr in MU. rewrite ?KS, ?KO in MU.
step.
step.
step.
step.
step.
step.
step.
rewrite (unsigned_lit (cnt + -1)) by lia. rewrite Z.shiftl_mul_pow2, unsigned_lit, Z.shiftr_div_pow2 by lia.
change (2 ^ 32) with (4 * 1073741824). change (2 ^ 30) with 1073741824.
replace ((cnt + -1) * (4 * 1073741824) / 1073741824) with (4 * (cnt - 1)) by (rewrite <- (Z.div_mul (4 * (cnt - 1)) 1073741824) at 1 by lia; f_equal; lia).
step.
with_mem ltac:(fun mm => pose proof (u32arr_read asegs mm _ CH (cnt - 1) (wz (coff c i)) (wa (PCA + 4 * (cnt - 1) + 16)) ACH CHI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as HR).
step.
rewrite zx32_small by lia. clear HR.
amo_step AMO.
step.
step. step. step. step.
rewrite (unsigned_lit (coff c i)), (unsigned_lit c) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. change (2 ^ 32) with 4294967296.
replace (coff c i * 16 + (c * 4294967296 + al_space_beg (ae_L RE))) with (slot_beg RE c i)
by (rewrite <- (coff_shl4 RE c i) by lia; rewrite RB; unfold prim_lo; lia).
stp. step. if_lit.
do 6 step. step. step.
release_frame FR ST (bv_unsigned sp).

replace (cnt + -1) with (cnt - 1) in PC0 by lia.
apply (proj1 (rw_cells_app asegs _ _ [C4 (wz (cnt - 1))] _)) in PC0 as [PCk _].
assert (PCAB : rl_T X + 208 + 80 <= PCA /\ PCA + 80 <= rl_T X + 2768) by (rewrite EPCA; lia).
assert (FWc : Forall (wc_ok RE X c) [(PCA, PCA + 4); (rl_T X + 2784, rl_T X + 2792)]).
{ constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; right; left; unfold pc_addr; rewrite <- EPCA; lia|].
constructor; [cbn; right; left; lia| constructor]. }
epose proof (agree_other_classes RE X c _ m _ RL ltac:(lia) MUt WMt FWc) as OTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (AG : agree_on asegs (fun z => fp_cls RE X c z /\ ~ (pc_addr X c <= z < pc_addr X c + 4)) m mm);
[ eapply agree_on_of_munch; [exact MUt| exact WMt|]; intros z [Fz Nz] Hz; cbn; unfold pc_addr in Nz; rewrite <- EPCA in Nz; split; [exact Nz|]; split; [| exact I];
pose proof (fp_cls_not_stats RE X RL c z ltac:(lia) Fz); lia |];
destruct (pop_close aX (upd_cls c (fun y => set_count (c_count y - 1) y) aX) GX RE X m mm c K RL Hc EI CNT
ltac:(unfold upd_cls; rewrite cls_set_cls_eq; reflexivity)
ltac:(intros c0 NE; unfold upd_cls; rewrite cls_set_cls_ne by exact NE; reflexivity)
EI HJS GNE HCall WMt OTH AG ltac:(unfold pc_addr; rewrite <- EPCA; exact PCk)) as (_ & _ & RPF & SJ & SSH) end.
fold i in RPF, SJ, SSH.
apply evt_done. unfold comb_post. do 16 eexists. exists GX.
split; [reflexivity|]. split; [reflexivity|].
split. { unfold comb_W, COMB_STACK, ri_addr. rewrite ?KS, ?KO. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [assumption|].
split. { eapply RTconst_munch; [exact RT| exact MUt| exact WMt|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
split. { eapply RStats_munch; [exact RS| exact MUt| exact WMt|].
repeat (apply Forall_cons; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]). apply Forall_nil. }
split. { cbn [snd]. eapply gstep_trans; [exact GS|]. apply gstep_ext; [intros c0| intros c0| reflexivity| reflexivity];
unfold upd_cls; (destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite cls_set_cls_eq; reflexivity| rewrite cls_set_cls_ne by exact NE; reflexivity]). }
cbn [fst snd]. exists i. split; [exact TI|]. split; [reflexivity|]. split; [exact RPF|]. split; [exact SJ| exact SSH].
Qed.

Lemma combined_prim_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (n lo : Z),
let c := class_id n in
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - COMB_STACK ->
1 <= n <= 65536 ->
aimplT atn (cache_alloc (ae_L RE) a c) s
(comb_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 208)) (wz n) (wz 8) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz combined_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros c RT RL RS RP MI ST CEIL LO Hn.
pose proof CEIL as CEIL'. idtac. unfold COMB_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD. idtac. rewrite ?KHI_eq in TK.
pose proof (class_facts n Hn) as (Hc & _ & _ & _ & MC1 & _). cbv zeta in Hc, MC1. fold c in Hc, MC1.

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC. destruct HC as ((_ & PC0 & _) & PU & _).
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & P10 & _).
cbv beta delta [pc_cells] in PC0.

pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _). rewrite KO in G4.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL.
remember (pc_addr X c) as PCA eqn:EPCA. unfold pc_addr in EPCA.
set (cnt := c_count (cls a c)) in *.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold combined_entry. apply aimplT_from_evt.
carve_frame 48%nat ST.
do 7 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RP0 : RPrim a G RE X mm) by (eapply RPrim_stack; [exact RP| exact RL| exact MUs| exact WM| constructor; [cbn [fst]; idtac; lia| constructor]]);
assert (RT0 : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MUs| exact WM| constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor]]);
assert (RS0 : RStats RE X mm) by (eapply RStats_munch; [exact RS| exact MUs| exact WM| constructor; [st_avoid_solve| constructor]]) end.
step.
replace (v_sltiu (wz n) 1) with (wz 0) by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1; replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
step.
replace (n + 0) with n by lia.
step.
rewrite (unsigned_lit n), zb_lxor_ones by lia.
step. ifz.
stp. step. step. ifz.
stp. step. if_lit.
step. ifz.
apply classid_block; [exact Hn|]. intros a2' a4' a5' a6' a7' t0' t1'. fold c.
step. ifz.
stp. step. ifz.
stp. step. step.
rewrite (unsigned_lit c) by lia. replace (rl_T X + 208 + c * 80) with PCA by lia.
step.
rewrite sx32_small by lia.
step.
unfold cache_alloc. fold cnt.
assert (GSa : gstep RE X a a G G) by apply gstep_refl.
destruct (Z.eq_dec cnt 0) as [Z0|NZ].
-
rewrite Z0. if_lit. apply evt_done. cbn [Z.eqb].
eapply aimplT_bind.
{ apply aimplT_from_evt.
do 7 step. step.
apply evt_done. rewrite EPCA. change (rl_T X + 208 + 80 * c) with (pc_addr X c).
eapply (aimplT_tall atn); [apply refill_facts|].
eapply (refill_spec L RE X); try eassumption;
first [ rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; unfold REFILL_STACK; lia | lia | exact Z0 ]. }
intros [ok a1] s' ms' [[EI1 CNT1] POST]. cbn [fst snd] in EI1, CNT1. unfold refill_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m2 & G1 & -> & -> & MU1 & WM1 & MI1 & ST1 & RT1 & RS1 & GS & A0 & RP1).
cbn [fst snd] in A0, GS, RP1. subst ra0.
rewrite !(unsigned_lit (bv_unsigned sp + -48)) in * by lia.
replace (ret_pc (wz 277328)) with (wz 277328) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
clear PC0 MI ST. hide MUs.
unfold refill_W, REFILL_STACK, ri_addr, pc_addr in MU1. rewrite ?KS, ?KO in MU1.
change (536870912 / 8) with 67108864 in MU1. change (3758096384 / 8) with 469762048 in MU1.
lazymatch type of MU1 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU1 WM1 end. unhide MUs.
assert (MU : munch (comb_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m2).
{ unfold comb_W, COMB_STACK, ri_addr, pc_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048.
eapply munch_chain; [eapply munch_weaken; [| exact MUs]; sub_fp_solve| exact MU1| sub_fp_solve]. }
clear MUs MU1.
destruct ok; cbn [negb].
+ specialize (CNT1 eq_refl).
destruct (RPrim_open _ _ _ _ _ RP1) as (K1 & _ & _ & HCall1).
pose proof (HCall1 c ltac:(rewrite K32; lia)) as HC1. destruct HC1 as ((_ & PC1 & _) & _ & _).
cbv beta delta [pc_cells] in PC1. rewrite EI1 in PC1.
assert (PCAB : rl_T X + 208 + 80 <= PCA) by (rewrite EPCA; lia).
apply aimplT_ret.
step. ifz.
step.
rewrite sx32_small by (rewrite CNT1; Z.div_mod_to_equations; lia).
step. step. step. step.
eapply (comb_tail _ gp _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 s3 s4 ra sp F fc m m2 s a a1 G G1 c lo RL Hc
ltac:(rewrite CNT1; Z.div_mod_to_equations; lia) EI1 GS RT1 RS1 RP1 MI1 ST1 CEIL');
[unfold COMB_STACK; lia| exact MU| exact WM| exact FR].
+ apply aimplT_ret.
step. if_lit.
step. stp. step. if_lit.
step.
do 6 step. step. step.
release_frame FR ST1 (bv_unsigned sp).
apply evt_done. unfold comb_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|].
split; [exact RT1|]. split; [exact RS1|]. split; [exact GS|]. cbn [fst snd]. split; [reflexivity| exact RP1].
-
ifz. apply evt_done. replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
lazymatch goal with |- aimplT _ _ _ _ ?ms0 =>
eapply aimplT_bind with (Q1 := fun r s' ms' => r = (true, a) /\ s' = s /\ ms' = ms0) end.
{ apply aimplT_ret. apply evt_done. split; [reflexivity|]. split; reflexivity. }
intros r s' ms' (-> & -> & ->). cbn [negb fst snd]. apply aimplT_ret.
rewrite EPCA. change (rl_T X + 208 + 80 * c) with (pc_addr X c).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (comb_tail ra gp _ _ t2 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 s3 s4 ra sp F fc m mm s a a G G c lo RL Hc ltac:(lia)
ltac:(destruct (as_cache_inited a) eqn:EI; [reflexivity| pose proof (P10 eq_refl); lia]) GSa RT0 RS0 RP0 MI ST CEIL');
[unfold COMB_STACK; lia| | exact WM| exact FR] end.
unfold comb_W, COMB_STACK. eapply munch_weaken; [| exact MUs]. sub_fp_solve.
Qed.
End S.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QYyZ.Mq4 QmP7.Mq0 QYyZ.Mq0 QnRU.Mq0 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QnRU.Mq7 Q9Ho.Mq1 QOJv.Mq5 Qu3b.Mq2 QteI.Mq4 QOH4 Q8zl.Mq2.
Import QpY2.Mq2.
Import QQNJ.Mq6.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma qpop_tail : forall ra0 ra sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m0 m : word -> option byte) (s : PStateA) (a aX : AState) (G GX : ghost) (lo : Z),
let cnt := c_count (cls aX 24) in
rlay_ok RE X -> 1 <= cnt -> as_cache_inited aX = true -> gstep RE X a aX G GX ->
RTconst RE X m -> RStats RE X m -> RPrim aX GX RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
band_lo <= lo -> lo <= bv_unsigned sp - QPOP_STACK ->
munch (qpop_W RE X (bv_unsigned sp) a) m0 m -> wmono asegs m0 m ->
evt asegs (qpop_post RE X ra0 sp gp a0 a2 a3 a4 s6 s7 s8 s9 s10 s11 F fc s a G lo m0 (true, upd_cls 24 (fun y => set_count (c_count y - 1) y) aX) s)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 (wz (rl_T X + 208)) a2 a3 a4 (wz cnt) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x436fc) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros cnt RL CNT EI GS RT RS RP MI ST CEIL LO MU WM.
pose proof CEIL as CEIL'. idtac. unfold QPOP_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (reg_geom RE X RL 24 ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (max_count_facts 24 ltac:(lia)) as [MC1 _].

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall 24 ltac:(rewrite K32; lia)) as HC. apply class_rep_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & _ & _ & _ & P6 & _ & _ & P9 & _).
cbv beta delta [pc_cells] in PC0. rewrite EI in PC0. unfold pc_addr in PC0, ACH. subst cnt.
cbv beta delta [ri_cells] in RI. unfold ri_addr in RI.
replace (rl_T X + 208 + 80 * 24) with (rl_T X + 2128) in PC0, ACH by lia.
set (cnt := c_count (cls aX 24)) in *.
change (bmax 24) with 2 in PC0. change (bsize 24) with 8192 in PC0.

set (i := nth (Z.to_nat (cnt - 1)) (pk_ca (K 24)) 0).
assert (CHI : nth_error CH (Z.to_nat (cnt - 1)) = Some (wz (coff 24 i))) by (apply HCH; lia).
assert (HIN : In i (pk_ca (K 24))) by (apply nth_In; lia).
pose proof (P6 i HIN) as TI. pose proof (tag_at_Some_lt _ _ _ _ TI) as [I0 _].

pose proof HJS as HJ0. destruct (hjunk_split _ _ (rl_T X + 2784) _ HJ0 ltac:(lia)) as [_ HJ1].
destruct (hjunk_split _ _ (rl_T X + 2792) _ HJ1 ltac:(lia)) as [HJ2 _].
replace (rl_T X + 2792) with (rl_T X + 2784 + 8) in HJ2 by lia. destruct (hjunk_C8 _ _ HJ2) as [w3 STA]. clear HJ0 HJ1 HJ2.
assert (AMO : amo_aligned AD (wz (rl_T X + 2784)) = true) by (apply amo_aligned_intro8; [lia| Z.div_mod_to_equations; lia]).
rtc RT 24%nat K24. unfold A_INSTANCE in K24.
pose proof (munch_refl [(rl_T X + 2128, rl_T X + 2132); (rl_T X + 2784, rl_T X + 2792)] m) as MUt. pose proof (wmono_refl asegs m) as WMt.
unfold qpop_W, QPOP_STACK, ri_addr in MU. rewrite ?KS, ?KO in MU.
step.
step.
step.
step.
rewrite (unsigned_lit (cnt + -1)) by lia. rewrite Z.shiftl_mul_pow2, unsigned_lit, Z.shiftr_div_pow2 by lia.
change (2 ^ 32) with (4 * 1073741824). change (2 ^ 30) with 1073741824.
replace ((cnt + -1) * (4 * 1073741824) / 1073741824) with (4 * (cnt - 1)) by (rewrite <- (Z.div_mul (4 * (cnt - 1)) 1073741824) at 1 by lia; f_equal; lia).
step.
step.
step. step.
replace (rl_T X + 208 + 2047 + 529) with (rl_T X + 2784) by lia.
with_mem ltac:(fun mm => pose proof (u32arr_read asegs mm _ CH (cnt - 1) (wz (coff 24 i)) (wa (rl_T X + 208 + 4 * (cnt - 1) + 1936)) ACH CHI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as HR).
step.
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _). rewrite KO in G4.
pose proof (tag_at_Some_lt _ _ _ _ TI) as [_ I1]. unfold ncarved in I1.
assert (CF : 0 <= coff 24 i /\ coff 24 i * 16 <= 3758096384).
{ unfold coff. change (class_size 24 / 16) with 512. change (class_size 24) with 8192 in G1. clear - I0 I1 G1 G3 G4. nia. }
rewrite zx32_small by lia. clear HR.
amo_step AMO.
step. step.
step. step. step.
step. step.
rewrite (unsigned_lit (coff 24 i)) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
replace (coff 24 i * 16 + (al_space_beg (ae_L RE) + 103079215104)) with (slot_beg RE 24 i)
by (rewrite <- (coff_shl4 RE 24 i) by lia; rewrite RB; unfold prim_lo; lia).
assert (SBR : 17594333495296 <= slot_beg RE 24 i /\ slot_beg RE 24 i + 8192 <= band_lo).
{ rewrite <- (coff_shl4 RE 24 i) by lia. rewrite RB. lia. }
step.
ifz.

replace (cnt + -1) with (cnt - 1) in PC0 by lia.
replace (rl_T X + 2128) with (pc_addr X 24) in PC0, MUt by (unfold pc_addr; lia).
replace (rl_T X + 2132) with (pc_addr X 24 + 4) in MUt by (unfold pc_addr; lia).
apply (proj1 (rw_cells_app asegs _ _ [C4 (wz (cnt - 1))] _)) in PC0 as [PCk _].
assert (FWc : Forall (wc_ok RE X 24) [(pc_addr X 24, pc_addr X 24 + 4); (rl_T X + 2784, rl_T X + 2792)]).
{ constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; right; left; lia|].
constructor; [cbn; right; left; lia| constructor]. }
epose proof (agree_other_classes RE X 24 _ m _ RL ltac:(lia) MUt WMt FWc) as OTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (AG : agree_on asegs (fun z => fp_cls RE X 24 z /\ ~ (pc_addr X 24 <= z < pc_addr X 24 + 4)) m mm);
[ eapply agree_on_of_munch; [exact MUt| exact WMt|]; intros z [Fz Nz] Hz; cbn; split; [exact Nz|]; split; [| exact I];
pose proof (fp_cls_not_stats RE X RL 24 z ltac:(lia) Fz); lia |];
destruct (pop_close aX (upd_cls 24 (fun y => set_count (c_count y - 1) y) aX) GX RE X m mm 24 K RL ltac:(lia) EI CNT
ltac:(unfold upd_cls; rewrite cls_set_cls_eq; reflexivity)
ltac:(intros c0 NE; unfold upd_cls; rewrite cls_set_cls_ne by exact NE; reflexivity)
EI HJS GNE HCall WMt OTH AG PCk) as (_ & _ & RPF & SJ & SSH) end.
fold i in RPF, SJ, SSH.
apply evt_done. unfold qpop_post. do 22 eexists. exists GX.
split; [reflexivity|]. split; [reflexivity|].
split. { unfold qpop_W, QPOP_STACK, ri_addr. rewrite ?KS, ?KO. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [assumption|].
split. { eapply RTconst_munch; [exact RT| exact MUt| exact WMt|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| unfold pc_addr; lia| unfold pc_addr; lia]|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
split. { eapply RStats_munch; [exact RS| exact MUt| exact WMt|].
repeat (apply Forall_cons; [first [apply st_avoid_above; unfold A_ERRNO, pc_addr; lia| eapply st_avoid_T; [eassumption| unfold pc_addr; lia| unfold pc_addr; lia]]|]). apply Forall_nil. }
split. { cbn [snd]. eapply gstep_trans; [exact GS|]. apply gstep_ext; [intros c0| intros c0| reflexivity| reflexivity];
unfold upd_cls; (destruct (Z.eq_dec c0 24) as [->|NE]; [rewrite cls_set_cls_eq; reflexivity| rewrite cls_set_cls_ne by exact NE; reflexivity]). }
cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
exists i. split; [exact TI|]. split; [reflexivity|]. split; [exact RPF|]. split; [exact SJ| exact SSH].
Qed.

Lemma qpop24_spec : qpop24_stmt RE X L.
Proof.
unfold qpop24_stmt. intros until lo; intros RT RL RS RP MI ST CEIL LO.
pose proof CEIL as CEIL'. idtac. unfold QPOP_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD. idtac. rewrite ?KHI_eq in TK.
pose proof (max_count_facts 24 ltac:(lia)) as [MC1 _].

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall 24 ltac:(rewrite K32; lia)) as HC. destruct HC as ((_ & PC0 & _) & PU & _).
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & P10 & _).
cbv beta delta [pc_cells] in PC0. unfold pc_addr in PC0. replace (rl_T X + 208 + 80 * 24) with (rl_T X + 2128) in PC0 by lia.
set (cnt := c_count (cls a 24)) in *.
apply aimplT_from_evt.
step.
rewrite sx32_small by lia.
step.
unfold cache_alloc. change kBatchClass with 24. fold cnt.
destruct (Z.eq_dec cnt 0) as [Z0|NZ].
-
rewrite Z0. if_lit. apply evt_done. cbn [Z.eqb].
eapply aimplT_bind.
{ apply aimplT_from_evt.
do 12 step. step.
apply evt_done. replace (rl_T X + 2128) with (pc_addr X 24) by (unfold pc_addr; lia).
eapply (aimplT_tall atn); [apply refill_facts|].
eapply (refill_spec L RE X); try eassumption. lia. }
intros [ok a1] s' ms' [[EI1 CNT1] POST]. cbn [fst snd] in EI1, CNT1. unfold refill_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m1 & G1 & -> & -> & MU1 & WM1 & MI1 & ST1 & RT1 & RS1 & GS & A0 & RP1).
cbn [fst snd] in A0, GS, RP1. subst ra0.
replace (ret_pc (wz 276496)) with (wz 276496) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (MU : munch (qpop_W RE X (bv_unsigned sp) a) m m1).
{ unfold qpop_W, QPOP_STACK. unfold refill_W, REFILL_STACK in MU1. rewrite ?KS, ?KO in MU1 |- *.
change (3758096384 / 8) with 469762048 in MU1. change (536870912 / 8) with 67108864 in MU1 |- *.
replace (SH (reg_beg (ae_L RE) 24 + 3758096384)) with (SH (reg_beg (ae_L RE) 24) + 469762048) by (rewrite <- SH_plus8; f_equal; lia). exact MU1. }
clear MU1 PC0 MI ST.
destruct ok; cbn [negb].
+ specialize (CNT1 eq_refl). change (max_count 24 / 2) with 1 in CNT1.
destruct (RPrim_open _ _ _ _ _ RP1) as (K1 & _ & _ & HCall1).
pose proof (HCall1 24 ltac:(rewrite K32; lia)) as HC1. destruct HC1 as ((_ & PC1 & _) & _ & _).
cbv beta delta [pc_cells] in PC1. rewrite EI1 in PC1.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK' & TB' & _). cbn [fst snd] in TK', TB'.
assert (PCB : 0 < pc_addr X 24 /\ pc_addr X 24 + 80 <= band_lo) by (unfold pc_addr; clear - TK' TB'; lia).
clear TK' TB'.
apply aimplT_ret.
step.
step. ifz.
step. step. step.
step.
rewrite sx32_small by lia.
step. step.
eapply (qpop_tail ra _ sp gp _ _ _ _ _ a0 a2 a3 a4 _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m m1 s a a1 G G1 lo RL ltac:(lia) EI1 GS RT1 RS1 RP1 MI1 ST1 CEIL');
[unfold QPOP_STACK; lia| exact MU| exact WM1].
+ apply aimplT_ret.
step.
step. if_lit.
apply evt_done. unfold qpop_post. do 22 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
split; [exact RT1|]. split; [exact RS1|]. split; [exact GS|]. cbn [fst snd]. exact RP1.
-
ifz. apply evt_done. replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
lazymatch goal with |- aimplT _ _ _ _ ?ms0 =>
eapply aimplT_bind with (Q1 := fun r s' ms' => r = (true, a) /\ s' = s /\ ms' = ms0) end.
{ apply aimplT_ret. apply evt_done. split; [reflexivity|]. split; reflexivity. }
intros r s' ms' (-> & -> & ->). cbn [negb fst snd]. apply aimplT_ret.
eapply (qpop_tail ra ra sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m s a a G G lo RL ltac:(lia)
ltac:(destruct (as_cache_inited a) eqn:EI; [reflexivity| pose proof (P10 eq_refl); lia]) (gstep_refl RE X a G) RT RS RP MI ST CEIL');
[unfold QPOP_STACK; lia| apply munch_refl| apply wmono_refl].
Qed.
End S.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QAdh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 QYyZ.Mq8 QnRU.Mqc QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QnRU.Mqi Q9Ho.Mq3 QOJv.Mqc Qu3b QteI.Mqd QAdh Q8zl.Mq4 QQNJ.Mqc.
Import QpY2.Mqc.
Import QMSY.Mq0.
Import QlES.
Export QVo2.Mq2.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Definition comb_W (sp c au : Z) : list (Z * Z) :=
[ (sp - COMB_STACK, sp); (rl_T X + 208, rl_T X + 3168); (ri_addr RE c, ri_addr RE c + 128);
(fa_beg (ae_L RE) c, fa_beg (ae_L RE) c + kFreeArraySize);
(SH (fa_beg (ae_L RE) c), SH (fa_beg (ae_L RE) c) + kFreeArraySize / 8);
(reg_beg (ae_L RE) c + au, reg_beg (ae_L RE) c + kFreeArrayOffset);
(SH (reg_beg (ae_L RE) c + au), SH (reg_beg (ae_L RE) c) + kFreeArrayOffset / 8) ].

Definition comb_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PStateA) (a : AState) (G : ghost) (c lo : Z) (m : word -> option byte)
(r : bool * AState) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' G1,
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch (comb_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m' /\ RStats RE X m' /\ gstep RE X a (snd r) G G1
/\ if fst r then
exists i, tag_at G1 c i = Some TCached /\ a0 = wz (slot_beg RE c i)
/\ (forall t, tag_prim t = false -> RPrim (snd r) (set_tag c i t G1) RE X m')
/\ hjunk m' (slot_beg RE c i) (slot_beg RE c i + class_size c)
/\ rw_cells asegs m' (SH (slot_beg RE c i)) [CB (Z.to_nat (class_size c / 8)) (repeat fa_byte (Z.to_nat (class_size c / 8)))]
else a0 = wz 0 /\ RPrim (snd r) G1 RE X m'.

Lemma comb_tail : forall ra gp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (v0 v1 v2 v3 v4 vra sp : word)
(F : bvmap 5 word) fc (m0 m : word -> option byte) (s : PStateA) (a aX : AState) (G GX : ghost) (c lo : Z),
let cnt := c_count (cls aX c) in
rlay_ok RE X -> 1 <= c <= 30 -> 1 <= cnt -> as_cache_inited aX = true -> gstep RE X a aX G GX ->
RTconst RE X m -> RStats RE X m -> RPrim aX GX RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -48) ->
band_lo <= lo -> lo <= bv_unsigned sp - COMB_STACK ->
munch (comb_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m0 m -> wmono asegs m0 m ->
rw_cells asegs m (bv_unsigned sp + -48) [C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
evt asegs (comb_post vra sp gp v0 v1 v2 v3 v4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c lo m0 (true, upd_cls c (fun y => set_count (c_count y - 1) y) aX) s)
(MS (mkR ra (wz (bv_unsigned sp + -48)) gp (wz A_TP) t0 t1 t2 (wz c) (wz (pc_addr X c)) (wz A_INSTANCE) (wz (rl_T X + 208)) (wz cnt) (wz 8) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43c80) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros cnt RL Hc CNT EI GS RT RS RP MI ST CEIL LO MU WM FR.
pose proof CEIL as CEIL'. idtac. unfold COMB_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (max_count_facts c ltac:(lia)) as [MC1 _]. pose proof (class_size_facts c ltac:(lia)) as [SZ1 SZ2]. hide SZ2.
pose proof (bsize_eq c ltac:(lia)) as BSZ.

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC. apply class_rep_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & _ & _ & _ & P6 & _ & _ & P9 & _).
cbv beta delta [pc_cells] in PC0. rewrite EI, BSZ in PC0. clear RI. subst cnt.
set (cnt := c_count (cls aX c)) in *.
set (i := nth (Z.to_nat (cnt - 1)) (pk_ca (K c)) 0).
assert (CHI : nth_error CH (Z.to_nat (cnt - 1)) = Some (wz (coff c i))) by (apply HCH; lia).
assert (HIN : In i (pk_ca (K c))) by (apply nth_In; lia).
pose proof (P6 i HIN) as TI. pose proof (tag_at_Some_lt _ _ _ _ TI) as [I0 I1]. unfold ncarved in I1.
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _). rewrite KO in G4.
assert (CF : 0 <= coff c i /\ coff c i * 16 <= 3758096384).
{ pose proof (coff_shl4 RE c i ltac:(lia) I0) as E. unfold slot_beg in E. clear - I0 I1 G1 G3 G4 SZ1 E. nia. }

pose proof HJS as HJ0. destruct (hjunk_split _ _ (rl_T X + 2784) _ HJ0 ltac:(lia)) as [_ HJ1].
destruct (hjunk_split _ _ (rl_T X + 2792) _ HJ1 ltac:(lia)) as [HJ2 _].
replace (rl_T X + 2792) with (rl_T X + 2784 + 8) in HJ2 by lia. destruct (hjunk_C8 _ _ HJ2) as [w3 STA]. clear HJ0 HJ1 HJ2.
assert (AMO : amo_aligned AD (wz (rl_T X + 2784)) = true) by (apply amo_aligned_intro8; [lia| unhide TA; Z.div_mod_to_equations; lia]).
rtc RT 24%nat K24. unfold A_INSTANCE in *.
remember (pc_addr X c) as PCA eqn:EPCA. unfold pc_addr in EPCA.
pose proof (munch_refl [(PCA, PCA + 4); (rl_T X + 2784, rl_T X + 2792)] m) as MUt. pose proof (wmono_refl asegs m) as WMt.
unfold comb_W, COMB_STACK, ri_addr in MU. rewrite ?KS, ?KO in MU.
step.
step.
step.
step.
step.
step.
step.
rewrite (unsigned_lit (cnt + -1)) by lia. rewrite Z.shiftl_mul_pow2, unsigned_lit, Z.shiftr_div_pow2 by lia.
change (2 ^ 32) with (4 * 1073741824). change (2 ^ 30) with 1073741824.
replace ((cnt + -1) * (4 * 1073741824) / 1073741824) with (4 * (cnt - 1)) by (rewrite <- (Z.div_mul (4 * (cnt - 1)) 1073741824) at 1 by lia; f_equal; lia).
step.
with_mem ltac:(fun mm => pose proof (u32arr_read asegs mm _ CH (cnt - 1) (wz (coff c i)) (wa (PCA + 4 * (cnt - 1) + 16)) ACH CHI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as HR).
step.
rewrite zx32_small by lia. clear HR.
amo_step AMO.
step.
step. step. step. step.
rewrite (unsigned_lit (coff c i)), (unsigned_lit c) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. change (2 ^ 32) with 4294967296.
replace (coff c i * 16 + (c * 4294967296 + al_space_beg (ae_L RE))) with (slot_beg RE c i)
by (rewrite <- (coff_shl4 RE c i) by lia; rewrite RB; unfold prim_lo; lia).
stp. step. if_lit.
do 6 step. step. step.
release_frame FR ST (bv_unsigned sp).

replace (cnt + -1) with (cnt - 1) in PC0 by lia.
apply (proj1 (rw_cells_app asegs _ _ [C4 (wz (cnt - 1))] _)) in PC0 as [PCk _].
assert (PCAB : rl_T X + 208 + 80 <= PCA /\ PCA + 80 <= rl_T X + 2768) by (rewrite EPCA; lia).
assert (FWc : Forall (wc_ok RE X c) [(PCA, PCA + 4); (rl_T X + 2784, rl_T X + 2792)]).
{ constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; right; left; unfold pc_addr; rewrite <- EPCA; lia|].
constructor; [cbn; right; left; lia| constructor]. }
epose proof (agree_other_classes RE X c _ m _ RL ltac:(lia) MUt WMt FWc) as OTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (AG : agree_on asegs (fun z => fp_cls RE X c z /\ ~ (pc_addr X c <= z < pc_addr X c + 4)) m mm);
[ eapply agree_on_of_munch; [exact MUt| exact WMt|]; intros z [Fz Nz] Hz; cbn; unfold pc_addr in Nz; rewrite <- EPCA in Nz; split; [exact Nz|]; split; [| exact I];
pose proof (fp_cls_not_stats RE X RL c z ltac:(lia) Fz); lia |];
destruct (pop_close aX (upd_cls c (fun y => set_count (c_count y - 1) y) aX) GX RE X m mm c K RL Hc EI CNT
ltac:(unfold upd_cls; rewrite cls_set_cls_eq; reflexivity)
ltac:(intros c0 NE; unfold upd_cls; rewrite cls_set_cls_ne by exact NE; reflexivity)
EI HJS GNE HCall WMt OTH AG ltac:(unfold pc_addr; rewrite <- EPCA; exact PCk)) as (_ & _ & RPF & SJ & SSH) end.
fold i in RPF, SJ, SSH.
apply evt_done. unfold comb_post. do 16 eexists. exists GX.
split; [reflexivity|]. split; [reflexivity|].
split. { unfold comb_W, COMB_STACK, ri_addr. rewrite ?KS, ?KO. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [assumption|].
split. { eapply RTconst_munch; [exact RT| exact MUt| exact WMt|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
split. { eapply RStats_munch; [exact RS| exact MUt| exact WMt|].
repeat (apply Forall_cons; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]). apply Forall_nil. }
split. { cbn [snd]. eapply gstep_trans; [exact GS|]. apply gstep_ext; [intros c0| intros c0| reflexivity| reflexivity];
unfold upd_cls; (destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite cls_set_cls_eq; reflexivity| rewrite cls_set_cls_ne by exact NE; reflexivity]). }
cbn [fst snd]. exists i. split; [exact TI|]. split; [reflexivity|]. split; [exact RPF|]. split; [exact SJ| exact SSH].
Qed.

Lemma combined_prim_spec : forall ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (s : PStateA) (a : AState) (G : ghost) (n lo : Z),
let c := class_id n in
RTconst RE X m -> rlay_ok RE X -> RStats RE X m -> RPrim a G RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - COMB_STACK ->
1 <= n <= 65536 ->
aimplT atn (cache_alloc (ae_L RE) a c) s
(comb_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s a G c lo m)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz (rl_T X + 208)) (wz n) (wz 8) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz combined_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros c RT RL RS RP MI ST CEIL LO Hn.
pose proof CEIL as CEIL'. idtac. unfold COMB_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD. idtac. rewrite ?KHI_eq in TK.
pose proof (class_facts n Hn) as (Hc & _ & _ & _ & MC1 & _). cbv zeta in Hc, MC1. fold c in Hc, MC1.

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall c ltac:(rewrite K32; lia)) as HC. destruct HC as ((_ & PC0 & _) & PU & _).
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & P10 & _).
cbv beta delta [pc_cells] in PC0.

pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq).
assert (SHB1 : 2201439137792 <= SH (fa_beg (ae_L RE) c) /\ SH (fa_beg (ae_L RE) c) + 67108864 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite FB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD0.
assert (SHB2 : 2201439137792 <= SH (reg_beg (ae_L RE) c) /\ SH (reg_beg (ae_L RE) c) + 469762048 <= SH band_lo /\ SH band_lo <= 0x10007ff78000).
{ rewrite RB. unfold SH, A_SHADOW_OFS. Z.div_mod_to_equations. lia. }
pose proof SH_band as SHBD1.
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & G4 & _). rewrite KO in G4.
assert (SHB3 : SH (reg_beg (ae_L RE) c) <= SH (reg_beg (ae_L RE) c + c_alloc_user (cls a c)) <= SH (reg_beg (ae_L RE) c) + 469762048).
{ split; [apply SH_le; lia|]. rewrite <- (SH_plus8 (reg_beg (ae_L RE) c) 469762048). apply SH_le. lia. }
clear PAL.
remember (pc_addr X c) as PCA eqn:EPCA. unfold pc_addr in EPCA.
set (cnt := c_count (cls a c)) in *.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold combined_entry. apply aimplT_from_evt.
carve_frame 48%nat ST.
do 7 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RP0 : RPrim a G RE X mm) by (eapply RPrim_stack; [exact RP| exact RL| exact MUs| exact WM| constructor; [cbn [fst]; idtac; lia| constructor]]);
assert (RT0 : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MUs| exact WM| constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor]]);
assert (RS0 : RStats RE X mm) by (eapply RStats_munch; [exact RS| exact MUs| exact WM| constructor; [st_avoid_solve| constructor]]) end.
step.
replace (v_sltiu (wz n) 1) with (wz 0) by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1; replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
step.
replace (n + 0) with n by lia.
step.
rewrite (unsigned_lit n), zb_lxor_ones by lia.
step. ifz.
stp. step. step. ifz.
stp. step. if_lit.
step. ifz.
apply classid_block; [exact Hn|]. intros a2' a4' a5' a6' a7' t0' t1'. fold c.
step. ifz.
stp. step. ifz.
stp. step. step.
rewrite (unsigned_lit c) by lia. replace (rl_T X + 208 + c * 80) with PCA by lia.
step.
rewrite sx32_small by lia.
step.
unfold cache_alloc. fold cnt.
assert (GSa : gstep RE X a a G G) by apply gstep_refl.
destruct (Z.eq_dec cnt 0) as [Z0|NZ].
-
rewrite Z0. if_lit. apply evt_done. cbn [Z.eqb].
eapply aimplT_bind.
{ apply aimplT_from_evt.
do 7 step. step.
apply evt_done. rewrite EPCA. change (rl_T X + 208 + 80 * c) with (pc_addr X c).
eapply (aimplT_tall atn); [apply refill_facts|].
eapply (refill_spec L RE X); try eassumption;
first [ rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; unfold REFILL_STACK; lia | lia | exact Z0 ]. }
intros [ok a1] s' ms' [[EI1 CNT1] POST]. cbn [fst snd] in EI1, CNT1. unfold refill_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m2 & G1 & -> & -> & MU1 & WM1 & MI1 & ST1 & RT1 & RS1 & GS & A0 & RP1).
cbn [fst snd] in A0, GS, RP1. subst ra0.
rewrite !(unsigned_lit (bv_unsigned sp + -48)) in * by lia.
replace (ret_pc (wz 277884)) with (wz 277884) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
clear PC0 MI ST. hide MUs.
unfold refill_W, REFILL_STACK, ri_addr, pc_addr in MU1. rewrite ?KS, ?KO in MU1.
change (536870912 / 8) with 67108864 in MU1. change (3758096384 / 8) with 469762048 in MU1.
lazymatch type of MU1 with munch _ ?ma ?mb => transport_after_call asegs ma mb MU1 WM1 end. unhide MUs.
assert (MU : munch (comb_W (bv_unsigned sp) c (c_alloc_user (cls a c))) m m2).
{ unfold comb_W, COMB_STACK, ri_addr, pc_addr. rewrite ?KS, ?KO. change (536870912 / 8) with 67108864. change (3758096384 / 8) with 469762048.
eapply munch_chain; [eapply munch_weaken; [| exact MUs]; sub_fp_solve| exact MU1| sub_fp_solve]. }
clear MUs MU1.
destruct ok; cbn [negb].
+ specialize (CNT1 eq_refl).
destruct (RPrim_open _ _ _ _ _ RP1) as (K1 & _ & _ & HCall1).
pose proof (HCall1 c ltac:(rewrite K32; lia)) as HC1. destruct HC1 as ((_ & PC1 & _) & _ & _).
cbv beta delta [pc_cells] in PC1. rewrite EI1 in PC1.
assert (PCAB : rl_T X + 208 + 80 <= PCA) by (rewrite EPCA; lia).
apply aimplT_ret.
step. ifz.
step.
rewrite sx32_small by (rewrite CNT1; Z.div_mod_to_equations; lia).
step. step. step. step.
eapply (comb_tail _ gp _ _ _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ s0 s1 s2 s3 s4 ra sp F fc m m2 s a a1 G G1 c lo RL Hc
ltac:(rewrite CNT1; Z.div_mod_to_equations; lia) EI1 GS RT1 RS1 RP1 MI1 ST1 CEIL');
[unfold COMB_STACK; lia| exact MU| exact WM| exact FR].
+ apply aimplT_ret.
step. if_lit.
step. stp. step. if_lit.
step.
do 6 step. step. step.
release_frame FR ST1 (bv_unsigned sp).
apply evt_done. unfold comb_post. do 16 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact ST1|].
split; [exact RT1|]. split; [exact RS1|]. split; [exact GS|]. cbn [fst snd]. split; [reflexivity| exact RP1].
-
ifz. apply evt_done. replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
lazymatch goal with |- aimplT _ _ _ _ ?ms0 =>
eapply aimplT_bind with (Q1 := fun r s' ms' => r = (true, a) /\ s' = s /\ ms' = ms0) end.
{ apply aimplT_ret. apply evt_done. split; [reflexivity|]. split; reflexivity. }
intros r s' ms' (-> & -> & ->). cbn [negb fst snd]. apply aimplT_ret.
rewrite EPCA. change (rl_T X + 208 + 80 * c) with (pc_addr X c).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (comb_tail ra gp _ _ t2 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 s1 s2 s3 s4 ra sp F fc m mm s a a G G c lo RL Hc ltac:(lia)
ltac:(destruct (as_cache_inited a) eqn:EI; [reflexivity| pose proof (P10 eq_refl); lia]) GSa RT0 RS0 RP0 MI ST CEIL');
[unfold COMB_STACK; lia| | exact WM| exact FR] end.
unfold comb_W, COMB_STACK. eapply munch_weaken; [| exact MUs]. sub_fp_solve.
Qed.
End S.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QYyZ.Mqb QmP7.Mq1 QYyZ.Mq8 QnRU.Mqc QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QnRU.Mqi Q9Ho.Mq3 QOJv.Mqc Qu3b QteI.Mqd QAdh Q8zl.Mq4.
Import QpY2.Mqc.
Import QQNJ.Mqc.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma qpop_tail : forall ra0 ra sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m0 m : word -> option byte) (s : PStateA) (a aX : AState) (G GX : ghost) (lo : Z),
let cnt := c_count (cls aX 24) in
rlay_ok RE X -> 1 <= cnt -> as_cache_inited aX = true -> gstep RE X a aX G GX ->
RTconst RE X m -> RStats RE X m -> RPrim aX GX RE X m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
band_lo <= lo -> lo <= bv_unsigned sp - QPOP_STACK ->
munch (qpop_W RE X (bv_unsigned sp) a) m0 m -> wmono asegs m0 m ->
evt asegs (qpop_post RE X ra0 sp gp a0 a2 a3 a4 s6 s7 s8 s9 s10 s11 F fc s a G lo m0 (true, upd_cls 24 (fun y => set_count (c_count y - 1) y) aX) s)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 (wz (rl_T X + 208)) a2 a3 a4 (wz cnt) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x43928) fc None m (seg_rom asegs)).
Proof.
intros until lo; intros cnt RL CNT EI GS RT RS RP MI ST CEIL LO MU WM.
pose proof CEIL as CEIL'. idtac. unfold QPOP_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD.
unfold iv_disjoint in TD; cbn [fst snd] in TD. idtac. rewrite ?KHI_eq in TK.
pose proof (reg_geom RE X RL 24 ltac:(lia)) as (RB & FB & PAL & PK & PCH & PH & RIq). hide PAL.
pose proof (max_count_facts 24 ltac:(lia)) as [MC1 _].

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall 24 ltac:(rewrite K32; lia)) as HC. apply class_rep_split in HC.
destruct HC as (((j1 & j2 & j3 & j4 & RI) & PC0 & (CH & ACH & LCH & HCH)) & PU & REG).
pose proof PU as (P1 & P2 & _ & _ & _ & P6 & _ & _ & P9 & _).
cbv beta delta [pc_cells] in PC0. rewrite EI in PC0. unfold pc_addr in PC0, ACH. subst cnt.
cbv beta delta [ri_cells] in RI. unfold ri_addr in RI.
replace (rl_T X + 208 + 80 * 24) with (rl_T X + 2128) in PC0, ACH by lia.
set (cnt := c_count (cls aX 24)) in *.
change (bmax 24) with 2 in PC0. change (bsize 24) with 8192 in PC0.

set (i := nth (Z.to_nat (cnt - 1)) (pk_ca (K 24)) 0).
assert (CHI : nth_error CH (Z.to_nat (cnt - 1)) = Some (wz (coff 24 i))) by (apply HCH; lia).
assert (HIN : In i (pk_ca (K 24))) by (apply nth_In; lia).
pose proof (P6 i HIN) as TI. pose proof (tag_at_Some_lt _ _ _ _ TI) as [I0 _].

pose proof HJS as HJ0. destruct (hjunk_split _ _ (rl_T X + 2784) _ HJ0 ltac:(lia)) as [_ HJ1].
destruct (hjunk_split _ _ (rl_T X + 2792) _ HJ1 ltac:(lia)) as [HJ2 _].
replace (rl_T X + 2792) with (rl_T X + 2784 + 8) in HJ2 by lia. destruct (hjunk_C8 _ _ HJ2) as [w3 STA]. clear HJ0 HJ1 HJ2.
assert (AMO : amo_aligned AD (wz (rl_T X + 2784)) = true) by (apply amo_aligned_intro8; [lia| Z.div_mod_to_equations; lia]).
rtc RT 24%nat K24. unfold A_INSTANCE in K24.
pose proof (munch_refl [(rl_T X + 2128, rl_T X + 2132); (rl_T X + 2784, rl_T X + 2792)] m) as MUt. pose proof (wmono_refl asegs m) as WMt.
unfold qpop_W, QPOP_STACK, ri_addr in MU. rewrite ?KS, ?KO in MU.
step.
step.
step.
step.
rewrite (unsigned_lit (cnt + -1)) by lia. rewrite Z.shiftl_mul_pow2, unsigned_lit, Z.shiftr_div_pow2 by lia.
change (2 ^ 32) with (4 * 1073741824). change (2 ^ 30) with 1073741824.
replace ((cnt + -1) * (4 * 1073741824) / 1073741824) with (4 * (cnt - 1)) by (rewrite <- (Z.div_mul (4 * (cnt - 1)) 1073741824) at 1 by lia; f_equal; lia).
step.
step.
step. step.
replace (rl_T X + 208 + 2047 + 529) with (rl_T X + 2784) by lia.
with_mem ltac:(fun mm => pose proof (u32arr_read asegs mm _ CH (cnt - 1) (wz (coff 24 i)) (wa (rl_T X + 208 + 4 * (cnt - 1) + 1936)) ACH CHI ltac:(lia) ltac:(unfold wa; f_equal; lia)) as HR).
step.
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _). rewrite KO in G4.
pose proof (tag_at_Some_lt _ _ _ _ TI) as [_ I1]. unfold ncarved in I1.
assert (CF : 0 <= coff 24 i /\ coff 24 i * 16 <= 3758096384).
{ unfold coff. change (class_size 24 / 16) with 512. change (class_size 24) with 8192 in G1. clear - I0 I1 G1 G3 G4. nia. }
rewrite zx32_small by lia. clear HR.
amo_step AMO.
step. step.
step. step. step.
step. step.
rewrite (unsigned_lit (coff 24 i)) by lia. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
replace (coff 24 i * 16 + (al_space_beg (ae_L RE) + 103079215104)) with (slot_beg RE 24 i)
by (rewrite <- (coff_shl4 RE 24 i) by lia; rewrite RB; unfold prim_lo; lia).
assert (SBR : 17594333495296 <= slot_beg RE 24 i /\ slot_beg RE 24 i + 8192 <= band_lo).
{ rewrite <- (coff_shl4 RE 24 i) by lia. rewrite RB. lia. }
step.
ifz.

replace (cnt + -1) with (cnt - 1) in PC0 by lia.
replace (rl_T X + 2128) with (pc_addr X 24) in PC0, MUt by (unfold pc_addr; lia).
replace (rl_T X + 2132) with (pc_addr X 24 + 4) in MUt by (unfold pc_addr; lia).
apply (proj1 (rw_cells_app asegs _ _ [C4 (wz (cnt - 1))] _)) in PC0 as [PCk _].
assert (FWc : Forall (wc_ok RE X 24) [(pc_addr X 24, pc_addr X 24 + 4); (rl_T X + 2784, rl_T X + 2792)]).
{ constructor; [cbn -[fp_cls]; do 2 right; intros z Hz; right; left; lia|].
constructor; [cbn; right; left; lia| constructor]. }
epose proof (agree_other_classes RE X 24 _ m _ RL ltac:(lia) MUt WMt FWc) as OTH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (AG : agree_on asegs (fun z => fp_cls RE X 24 z /\ ~ (pc_addr X 24 <= z < pc_addr X 24 + 4)) m mm);
[ eapply agree_on_of_munch; [exact MUt| exact WMt|]; intros z [Fz Nz] Hz; cbn; split; [exact Nz|]; split; [| exact I];
pose proof (fp_cls_not_stats RE X RL 24 z ltac:(lia) Fz); lia |];
destruct (pop_close aX (upd_cls 24 (fun y => set_count (c_count y - 1) y) aX) GX RE X m mm 24 K RL ltac:(lia) EI CNT
ltac:(unfold upd_cls; rewrite cls_set_cls_eq; reflexivity)
ltac:(intros c0 NE; unfold upd_cls; rewrite cls_set_cls_ne by exact NE; reflexivity)
EI HJS GNE HCall WMt OTH AG PCk) as (_ & _ & RPF & SJ & SSH) end.
fold i in RPF, SJ, SSH.
apply evt_done. unfold qpop_post. do 22 eexists. exists GX.
split; [reflexivity|]. split; [reflexivity|].
split. { unfold qpop_W, QPOP_STACK, ri_addr. rewrite ?KS, ?KO. exact MU. }
split; [exact WM|]. split; [assumption|]. split; [assumption|].
split. { eapply RTconst_munch; [exact RT| exact MUt| exact WMt|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| unfold pc_addr; lia| unfold pc_addr; lia]|].
apply Forall_cons; [apply rt_avoid_Thigh; [exact RL| lia| lia]| apply Forall_nil]. }
split. { eapply RStats_munch; [exact RS| exact MUt| exact WMt|].
repeat (apply Forall_cons; [first [apply st_avoid_above; unfold A_ERRNO, pc_addr; lia| eapply st_avoid_T; [eassumption| unfold pc_addr; lia| unfold pc_addr; lia]]|]). apply Forall_nil. }
split. { cbn [snd]. eapply gstep_trans; [exact GS|]. apply gstep_ext; [intros c0| intros c0| reflexivity| reflexivity];
unfold upd_cls; (destruct (Z.eq_dec c0 24) as [->|NE]; [rewrite cls_set_cls_eq; reflexivity| rewrite cls_set_cls_ne by exact NE; reflexivity]). }
cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
exists i. split; [exact TI|]. split; [reflexivity|]. split; [exact RPF|]. split; [exact SJ| exact SSH].
Qed.

Lemma qpop24_spec : qpop24_stmt RE X L.
Proof.
unfold qpop24_stmt. intros until lo; intros RT RL RS RP MI ST CEIL LO.
pose proof CEIL as CEIL'. idtac. unfold QPOP_STACK in LO.
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (TA & TK & TB & TD & _). cbn [fst snd] in TA, TK, TB, TD. idtac. rewrite ?KHI_eq in TK.
pose proof (max_count_facts 24 ltac:(lia)) as [MC1 _].

destruct (RPrim_open _ _ _ _ _ RP) as (K & HJS & GNE & HCall).
pose proof (HCall 24 ltac:(rewrite K32; lia)) as HC. destruct HC as ((_ & PC0 & _) & PU & _).
pose proof PU as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & P10 & _).
cbv beta delta [pc_cells] in PC0. unfold pc_addr in PC0. replace (rl_T X + 208 + 80 * 24) with (rl_T X + 2128) in PC0 by lia.
set (cnt := c_count (cls a 24)) in *.
apply aimplT_from_evt.
step.
rewrite sx32_small by lia.
step.
unfold cache_alloc. change kBatchClass with 24. fold cnt.
destruct (Z.eq_dec cnt 0) as [Z0|NZ].
-
rewrite Z0. if_lit. apply evt_done. cbn [Z.eqb].
eapply aimplT_bind.
{ apply aimplT_from_evt.
do 12 step. step.
apply evt_done. replace (rl_T X + 2128) with (pc_addr X 24) by (unfold pc_addr; lia).
eapply (aimplT_tall atn); [apply refill_facts|].
eapply (refill_spec L RE X); try eassumption. lia. }
intros [ok a1] s' ms' [[EI1 CNT1] POST]. cbn [fst snd] in EI1, CNT1. unfold refill_post in POST.
destruct POST as (u0 & u1 & u2 & ra0 & ra1 & ra2 & ra3 & ra4 & ra5 & ra6 & ra7 & u3 & u4 & u5 & u6 & m1 & G1 & -> & -> & MU1 & WM1 & MI1 & ST1 & RT1 & RS1 & GS & A0 & RP1).
cbn [fst snd] in A0, GS, RP1. subst ra0.
replace (ret_pc (wz 277052)) with (wz 277052) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (MU : munch (qpop_W RE X (bv_unsigned sp) a) m m1).
{ unfold qpop_W, QPOP_STACK. unfold refill_W, REFILL_STACK in MU1. rewrite ?KS, ?KO in MU1 |- *.
change (3758096384 / 8) with 469762048 in MU1. change (536870912 / 8) with 67108864 in MU1 |- *.
replace (SH (reg_beg (ae_L RE) 24 + 3758096384)) with (SH (reg_beg (ae_L RE) 24) + 469762048) by (rewrite <- SH_plus8; f_equal; lia). exact MU1. }
clear MU1 PC0 MI ST.
destruct ok; cbn [negb].
+ specialize (CNT1 eq_refl). change (max_count 24 / 2) with 1 in CNT1.
destruct (RPrim_open _ _ _ _ _ RP1) as (K1 & _ & _ & HCall1).
pose proof (HCall1 24 ltac:(rewrite K32; lia)) as HC1. destruct HC1 as ((_ & PC1 & _) & _ & _).
cbv beta delta [pc_cells] in PC1. rewrite EI1 in PC1.
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK' & TB' & _). cbn [fst snd] in TK', TB'.
assert (PCB : 0 < pc_addr X 24 /\ pc_addr X 24 + 80 <= band_lo) by (unfold pc_addr; clear - TK' TB'; lia).
clear TK' TB'.
apply aimplT_ret.
step.
step. ifz.
step. step. step.
step.
rewrite sx32_small by lia.
step. step.
eapply (qpop_tail ra _ sp gp _ _ _ _ _ a0 a2 a3 a4 _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m m1 s a a1 G G1 lo RL ltac:(lia) EI1 GS RT1 RS1 RP1 MI1 ST1 CEIL');
[unfold QPOP_STACK; lia| exact MU| exact WM1].
+ apply aimplT_ret.
step.
step. if_lit.
apply evt_done. unfold qpop_post. do 22 eexists. exists G1.
split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
split; [exact RT1|]. split; [exact RS1|]. split; [exact GS|]. cbn [fst snd]. exact RP1.
-
ifz. apply evt_done. replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
lazymatch goal with |- aimplT _ _ _ _ ?ms0 =>
eapply aimplT_bind with (Q1 := fun r s' ms' => r = (true, a) /\ s' = s /\ ms' = ms0) end.
{ apply aimplT_ret. apply evt_done. split; [reflexivity|]. split; reflexivity. }
intros r s' ms' (-> & -> & ->). cbn [negb fst snd]. apply aimplT_ret.
eapply (qpop_tail ra ra sp gp t0 t1 t2 s0 s1 a0 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m s a a G G lo RL ltac:(lia)
ltac:(destruct (as_cache_inited a) eqn:EI; [reflexivity| pose proof (P10 eq_refl); lia]) (gstep_refl RE X a G) RT RS RP MI ST CEIL');
[unfold QPOP_STACK; lia| apply munch_refl| apply wmono_refl].
Qed.
End S.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoNr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoNr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QteI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QteI.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCNF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCNF.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoBx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QoBx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWHo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWHo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC9y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC9y.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQNJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQNJ.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8zl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8zl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1.
Local Set Keyed Unification.

Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_2 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_3 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_4 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_5 := lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
[C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].

Definition towrite_g_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
rw_cells asegs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
Z.land (bv_unsigned flags) 8 = 0 ->
(0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
mem_inv asegs m ->
evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5a38) fc None m (seg_rom asegs)).

Theorem towrite_g_proof : towrite_g_stmt.
Proof.
unfold towrite_g_stmt. intros until lbf. intros FC NOWR B0 BHI BS0 MI.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size gfile_cells csize Nat.add] in FB.
set (Fp := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(Fp, Fp + 148)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold gfile_cells in FC.
assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
do 5 zs. rewrite FL8. zs. zs. if_lit.
do 10 zs.
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold gfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

Theorem towrite_proof : towrite_stmt.
Proof.
unfold towrite_stmt. intros until tail. intros FC NOWR B0 BHI BS0 MI.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size file_cells csize Nat.add] in FB.
set (Fp := bv_unsigned a0) in *.
replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold file_cells in FC.
assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
rewrite <- Z.land_ones by lia.
rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
do 5 zs. rewrite FL8. zs. zs. if_lit.
do 10 zs.
apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | let t := type of H in idtac "FC:" t; fail] end.
Qed.

Lemma arg_ok_vf {BAND : Band} : forall Fp B BS m m' lo sp sp' ap w a,
arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
destruct H as (slack & BY & HF & PAD & NZ & SZ & D1 & D2 & D3 & D4 & D5). exists slack.
split; [|repeat (split; [first [assumption | lia]|]); exact D5].
eapply bytes_at_transport; [exact BY | exact MU |].
cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf {BAND : Band} : forall Fp B BS m m' lo sp sp' ap ws args,
args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
rw_cells asegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
rw_cells asegs m A (pre ++ mid ++ post).
Proof.
intros m A pre mid post [[Hwf Hb] Hw] WF.
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]].
split; [split|].
- apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells asegs m A cs -> A = A' -> rw_cells asegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells asegs m B [CB 0 []].
Proof.
intros m B H0 H1. split; [split|].
- cbn. split; [reflexivity | exact I].
- cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Definition VF_FRAME : Z := 368.

Definition vf_saves_post {BAND : Band} (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
fun ms' => exists (m' : word -> option byte) (j1 j2 : list byte),
ms' = MS (mkR (Z_to_bv 64 0xd5f88) (Z_to_bv 64 (bv_unsigned sp + -368)) gp tp t0 t1 t2 a0 a1 (Z_to_bv 64 0) a1
(Z_to_bv 64 (bv_unsigned sp + -368)) (Z_to_bv 64 (bv_unsigned sp + -272)) (Z_to_bv 64 (bv_unsigned sp + -104)) a5 a6 a7
(Z_to_bv 64 0x645560) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd60d0) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 368, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' (bv_unsigned sp + -368)
[C8 a2; C8 a2; CB 80 j1; CB 168 j2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 canary; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk asegs m' lo (bv_unsigned sp + -368).

Lemma vf_saves {BAND : Band} : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 368 -> band_lo <= lo -> mem_inv asegs m ->
rw_cells asegs m 0xe8f90 [C8 (Z_to_bv 64 0x645560)] -> rw_cells asegs m 0x645560 [C8 canary] ->
evt asegs (vf_saves_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 canary F fc m lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd5f20) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros ST LO LO0 MI SSP1 SSP2.
pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 368%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 368 _ _ [8;8;80;168;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR.
do 26 (zstep; try (fix_litstore; mem_after_store_opt)).
apply evt_done. unfold vf_saves_post. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [| exact ST].
lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -368) _ |- _ => exact H end.
Qed.

Lemma fmt_bytes_at : forall m A f, mem_inv asegs m -> ro_bytes_b asegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
bytes_at asegs m A (zb f).
Proof.
intros m A f MI RB H0 H1.
pose proof (ro_cells_bytes_at asegs m A _ (ro_cells_image asegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Lemma rw_cells_recast : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
