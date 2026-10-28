(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZ24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZ24.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhI1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULAQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULAQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXKA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Up8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Up8x.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Frames.
Variable L : heap_layout.
Variable HIx : heap_iface L.

#[using="Type"] Lemma frame_writes_ok4 : forall A LB m m' md W,
HEAP L HIx A LB m md ->
munch W m m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hi_top L HIx)
\/ (exists a n, In (a, n) LB /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)
\/ (forall x, fst iv <= x < snd iv -> hl_client_static L x /\ x < hi_top L HIx)) W ->
forall a, 0 <= a < 2^64 -> ~ (client_addr L LB alloc_ceiling a /\ a < hi_top L HIx) -> ~ hl_scratch L a -> m' (wa a) = m (wa a).
Proof.
intros A LB m m' md W HP MU HW a Ha Hna Hns. apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW].
cbn in H1. intros Hin. destruct H1 as [H1 | [(b & n & Hb & Hlo & Hhi) | [Hsc | Hcs]]].
- apply Hna. split; [left; lia | lia].
- apply Hna. pose proof (heap_blk L HIx _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). pose proof (hi_top_hi L HIx).
split; [| lia]. right; right. exists (b, n). split; [exact Hb| cbn; lia].
- apply Hns. apply Hsc. lia.
- apply Hna. destruct (Hcs a ltac:(lia)) as [C LT]. split; [right; left; exact C | exact LT].
Qed.

#[using="Type"] Lemma heap_presx_of_munchx : forall X LB SP W m m',
munch W m m' -> wmono (hl_segs L) m m' ->
(forall a, 0 <= a < 2^64 -> client_addrx L X LB SP a -> outside W a) ->
heap_presx L X LB SP m m'.
Proof.
intros X LB SP W m m' MU WM HW a Ha Hc. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
- apply WM.
Qed.
End Frames.

Section SeedLoop.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Variables (sp gp s0v s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (md : Model) (LB : list blk) (lo : Z) (m0 : word -> option byte) (T : TSet) (seedv : word).
Variable G : Z.
Hypothesis EG : G = bv_unsigned sp - 176.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= G - 224.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis SEEDM1 : sx32 seedv = Z_to_bv 64 (-1).
Hypothesis MOK : model_ok md.

Hypothesis K : forall ms' md', seed_settle_post HIx sp gp s0v s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md LB lo ms' md' ->
realizes rsegs (mkCfg ms' md') T.

Definition Vinv (c : config) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (A : AS S4L HIx) (errv : word) junk16 sbuf vf,
c = mkCfg (grs_head_st G x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m) md
/\ HEAPx A LB m md /\ grs_frame G s0v m junk16 sbuf /\ cells_size sbuf = 128%nat
/\ stk rsegs m lo G /\ rw_cells rsegs m (0x77c00 - 164) [C4 errv]
/\ rw_cells rsegs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C4 seedv]
/\ rw_cells rsegs m GGOT4 [C8 (Z_to_bv 64 (fn_lh_char_equal S4F))]
/\ rw_cells rsegs m GVDSO4 [C8 (Z_to_bv 64 vf)] /\ vdso_ok4 vf
/\ heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 m.

Definition wkind (iv : Z * Z) : Prop :=
(alloc_ceiling <= fst iv /\ snd iv <= bv_unsigned sp)
\/ (fst iv = 0x77c00 - 164 /\ snd iv = 0x77c00 - 164 + 4)
\/ (fst iv = GVDSO4 /\ snd iv = GVDSO4 + 8)
\/ (fst iv = GHASH4 + 8 /\ snd iv = GHASH4 + 12).

Definition basef (m : word -> option byte) (A : AS S4L HIx) : Prop :=
HEAPx A LB m md
/\ rw_cells rsegs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F))]
/\ rw_cells rsegs m GGOT4 [C8 (Z_to_bv 64 (fn_lh_char_equal S4F))]
/\ heap_presx S4L s4_volatile LB (bv_unsigned sp) m0 m.

#[using="lo G EG LO LOS HT"] Lemma basef_step : forall m m' A W,
basef m A -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> Forall wkind W ->
Forall (fun iv => fst iv = GHASH4 + 8 -> False) W \/ True ->
basef m' A.
Proof.
intros m m' A W (HP & GH & GG & HPX) MU WM MI HW _.
word_range sp SPR. unfold wkind, GVDSO4, GHASH4, GGOT4 in *. unfold_consts.
assert (DJ : forall A0 n0, (A0 + n0 <= 0x66a40 \/ (0x66a44 <= A0 /\ A0 + n0 <= 0x66f20) \/ (0x66f28 <= A0 /\ A0 + n0 <= 0x77b5c)) -> 0 <= n0 ->
disjoint_from W A0 n0).
{ intros A0 n0 HA Hn. clear -HW HA Hn SPR LO LOS EG. induction W as [|[lo' hi'] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
lia. }
split; [| split; [| split]].
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok4 S4L HIx _ _ _ _ _ _ HP MU).
clear -HW SPR LO LOS EG HT. induction W as [|[lo' hi'] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [H1 HW]. apply Forall_cons; [| apply IH; exact HW]. cbn [fst snd] in *.
pose proof (hi_top_hi S4L HIx) as HTH. unfold alloc_ceiling, sp_window_lo, stack_max_size in HTH.
destruct H1 as [H1 | [H1 | [H1 | H1]]].
+ left. unfold_consts. lia.
+ right; right; left. intros x Hx. cbn. lia.
+ right; right; right. intros x Hx. split; [| lia]. cbn. unfold s4_client_static. lia.
+ right; right; right. intros x Hx. split; [| lia]. cbn. unfold s4_client_static. lia.
- eapply rw_cells_transport; [exact GH | exact MU | exact WM |]. unfold GHASH4. apply DJ; cbn; lia.
- eapply rw_cells_transport; [exact GG | exact MU | exact WM |]. unfold GGOT4. apply DJ; cbn; lia.
- eapply heap_presx_trans; [exact HPX|]. eapply (heap_presx_of_munchx S4L); [exact MU | exact WM |].
intros a Ha Hc. clear -HW Ha Hc SPR LO LOS EG HP. induction W as [|[lo' hi'] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
destruct Hc as [Hc | [[Hcs Hnv] | Hb]].
+ destruct H1 as [H1|[H1|[H1|H1]]]; lia.
+ cbn in Hcs. unfold s4_client_static in Hcs. unfold s4_volatile in Hnv. destruct H1 as [H1|[H1|[H1|H1]]]; lia.
+ destruct Hb as ([ba bn] & Hb0 & Hbr). cbn in Hbr.
pose proof (heap_blk S4L HIx _ _ _ _ _ _ HP Hb0) as (_ & _ & _ & Hbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ _ _ HP Hb0) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi. destruct H1 as [H1|[H1|[H1|H1]]]; lia.
Qed.

Ltac wk_stack := left; cbn [fst snd]; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac wk_errno := right; left; cbn [fst snd]; lia.
Ltac wk_seed := right; right; right; cbn [fst snd]; unfold GHASH4; lia.

Definition gr_wf (bs : list byte) : bool := negb (bv_eqb (grseed_w bs) (Z_to_bv 64 (-1))).

#[using="Type"] Lemma gr_wf_witness : gr_wf [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] = true.
Proof. vm_compute. reflexivity. Qed.

#[using="EG LO LOS HT MOK"] Lemma tail_reenter : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m A errv vf w,
basef m A -> mem_inv rsegs m -> stk rsegs m lo (G + 176) -> rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
rw_cells rsegs m (GHASH4 + 8) [C4 seedv] ->
rw_cells rsegs m GVDSO4 [C8 (Z_to_bv 64 vf)] -> vdso_ok4 vf ->
bv_eqb w (Z_to_bv 64 (-1)) = true ->
lbw rsegs Vinv T false (mkCfg (at_grs_ret G s0v gp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc w m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) md).
Proof.
intros until w. intros BF MI ST ERR GS GV VF EQ.
word_range sp SPR. unfold_consts.
eapply lbw_of_evt_V; [exact MOK | eapply (grs_reenter G s0v) with (lo := lo); [exact EQ | exact MI | exact ST | lia | exact LO | lia] |].
intros ms' (x1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & junk16 & sbuf & m' & -> & MU & WM & MI' & ST' & FR' & Hsb).
split.
- pose proof (basef_step m m' A _ BF MU WM MI' ltac:(apply Forall_cons; [wk_stack | apply Forall_nil]) (or_intror I)) as (HP' & GH' & GG' & HPX').
unfold Vinv. do 16 eexists. exists m', A, errv, junk16, sbuf, vf.
split; [reflexivity|]. split; [exact HP'|]. split; [exact FR'|]. split; [exact Hsb|]. split; [exact ST'|].
split; [eapply rw_cells_transport; [exact ERR | exact MU | exact WM | cbn; lia]|].
split.
{ apply (proj2 (rw_cells_app rsegs m' GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F))] [C4 seedv])). split; [exact GH'|].
cbn [cells_size csize Nat.add]. eapply rw_cells_transport; [exact GS | exact MU | exact WM | unfold GHASH4; cbn; lia]. }
split; [exact GG'|]. split; [eapply rw_cells_transport; [exact GV | exact MU | exact WM | unfold GVDSO4; cbn; lia]|].
split; [exact VF | exact HPX'].
- unfold grs_head_st, at_grs_ret, grs_head, grs_ret_pc. intros E. apply (f_equal ms_pc_val) in E. unfold QEpW.MS in E. cbn [ms_pc_val] in E.
apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
Qed.

#[using="EG LO LOS HT SEEDM1 MOK K"] Lemma tail_exit : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m A errv vf w p,
basef m A -> mem_inv rsegs m -> stk rsegs m lo (G + 176) -> rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
rw_cells rsegs m (GHASH4 + 8) [C4 seedv] ->
rw_cells rsegs m GVDSO4 [C8 (Z_to_bv 64 vf)] -> vdso_ok4 vf ->
bv_eqb w (Z_to_bv 64 (-1)) = false ->
lbw rsegs Vinv T p (mkCfg (at_grs_ret G s0v gp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc w m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) md).
Proof.
intros until p. intros BF MI ST ERR GS GV VF NEQ.
word_range sp SPR. unfold_consts. pose proof BF as (HP & GH & GG & HPX).
assert (GC : rw_cells rsegs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C4 seedv]).
{ apply (proj2 (rw_cells_app rsegs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F))] [C4 seedv])). split; [exact GH | cbn [cells_size csize Nat.add]; exact GS]. }
eapply lbw_evt; [exact MOK | eapply (grs_exit G s0v); [exact NEQ | exact MI | exact GC | exact SEEDM1] |].
intros ms' (x1 & u0 & u1 & u2 & v & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & seed' & m' & -> & MU & WM & MI' & GC').
apply lbw_exit_rz. apply K. unfold seed_settle_post.
pose proof (basef_step m m' A _ BF MU WM MI' ltac:(apply Forall_cons; [wk_seed | apply Forall_nil]) (or_intror I)) as (HP' & GH' & GG' & HPX').
replace (G + 176) with (bv_unsigned sp) in ST by lia.
do 16 eexists. exists m', A, errv.
split; [rewrite EG; replace (bv_unsigned sp - 176 + 176) with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [reflexivity|].
split; [eapply stk_transport_disjoint; [exact ST | exact MU | exact WM | unfold GHASH4; cbn; lia]|].
split; [exact HPX'|].
split; [eapply rw_cells_transport; [exact ERR | exact MU | exact WM | unfold GHASH4; cbn; lia]|].
split; [| exact HP'].
split; [exists seed'; exact GC'|]. split; [exact GG'|]. exists vf. split; [| exact VF].
eapply rw_cells_transport; [exact GV | exact MU | exact WM | unfold GHASH4, GVDSO4; cbn; lia].
Qed.

Definition gr_after (r : word) (m : word -> option byte) (t0 t1 t2 t3 t4 t5 t6 : word) : machine_state :=
MS (mkR (Z_to_bv 64 0x51244) (Z_to_bv 64 (G + -16)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 (-1))
r (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 278)
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6086c) fc None m (seg_rom rsegs).

#[using="EG LO LOS HT SEEDM1 MOK K"] Lemma child_data : forall m A errv vf junk16 junk8 sb bs (t0 t1 t2 t3 t4 t5 t6 : word),
length bs = 4%nat ->
basef m A -> mem_inv rsegs m -> stk rsegs m lo (G + -16) -> rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
rw_cells rsegs m (GHASH4 + 8) [C4 seedv] -> rw_cells rsegs m GVDSO4 [C8 (Z_to_bv 64 vf)] -> vdso_ok4 vf ->
grs_frame G s0v m junk16 [CB 128 sb] -> rw_cells rsegs m (G + -16) [CB 8 junk8; C8 (Z_to_bv 64 grs_link)] ->
lbw rsegs Vinv T (gr_wf bs) (mkCfg (gr_after (len_word bs) (write_to_mem m (wa (G + 16)) bs) t0 t1 t2 t3 t4 t5 t6) md).
Proof.
intros until t6. intros LBS BF MI ST ERR GS GV VF FR FR16.
word_range sp SPR. unfold_consts. unfold gr_after.

unfold grs_frame in FR. cbn [app] in FR.
apply (rw_cells_app rsegs m G [CB 16 junk16]) in FR as [F0 F1]. cbn [cells_size csize Nat.add] in F1. replace (G + Z.of_nat 16) with (G + 16) in F1 by lia.
apply (rw_cells_app rsegs m (G + 16) [CB 128 sb]) in F1 as [F2 F3]. cbn [cells_size csize Nat.add] in F3. replace (G + 16 + Z.of_nat 128) with (G + 144) in F3 by lia.
destruct (syswrite_facts rsegs m (G + 16) 128 sb bs [(G + 16, G + 144)] m F2 ltac:(lia) MI (munch_refl _ _) (wmono_refl _ _) ltac:(cbn; lia))
as (F2' & MI1 & MU1 & WM1).
set (m1 := write_to_mem m (wa (G + 16)) bs) in *.
assert (FR1 : grs_frame G s0v m1 junk16 [CB (length bs) bs; CB (128 - length bs) (skipn (length bs) sb)]).
{ unfold grs_frame. cbn [app]. apply (proj2 (rw_cells_app rsegs m1 G [CB 16 junk16] _)). split.
- eapply rw_cells_transport; [exact F0 | exact MU1 | exact WM1 | cbn; lia].
- cbn [cells_size csize Nat.add]. replace (G + Z.of_nat 16) with (G + 16) by lia.
apply (proj2 (rw_cells_app rsegs m1 (G + 16) [CB (length bs) bs; CB (128 - length bs) (skipn (length bs) sb)] _)). split; [exact F2'|].
cbn [cells_size csize Nat.add]. replace (G + 16 + Z.of_nat (length bs + (128 - length bs + 0))) with (G + 144) by lia.
eapply rw_cells_transport; [exact F3 | exact MU1 | exact WM1 | cbn; lia]. }
pose proof (basef_step m m1 A _ BF MU1 WM1 MI1 ltac:(apply Forall_cons; [wk_stack | apply Forall_nil]) (or_intror I)) as BF1.
assert (ST1 : stk rsegs m1 lo (G + -16)) by (eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 | cbn; lia]).
assert (ERR1 : rw_cells rsegs m1 (0x77c00 - 164) [C4 errv]) by (eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; lia]).
assert (GS1 : rw_cells rsegs m1 (GHASH4 + 8) [C4 seedv]) by (eapply rw_cells_transport; [exact GS | exact MU1 | exact WM1 | unfold GHASH4; cbn; lia]).
assert (GV1 : rw_cells rsegs m1 GVDSO4 [C8 (Z_to_bv 64 vf)]) by (eapply rw_cells_transport; [exact GV | exact MU1 | exact WM1 | unfold GVDSO4; cbn; lia]).
assert (FR161 : rw_cells rsegs m1 (G + -16) [CB 8 junk8; C8 (Z_to_bv 64 grs_link)]) by (eapply rw_cells_transport; [exact FR16 | exact MU1 | exact WM1 | cbn; lia]).
clearbody m1. unfold gr_wf.

rewrite LBS in FR1. cbn [Nat.sub] in FR1.
eapply lbw_evt; [exact MOK | eapply (gr_post_full G s0v) with (lo := lo); [exact LBS | exact MI1 | exact ST1 | lia | exact LO | lia | exact FR1 | exact FR161 | exact ERR1] |].
intros ms' (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2).
pose proof (basef_step m1 m2 A _ BF1 MU2 WM2 MI2 ltac:(apply Forall_cons; [wk_stack | apply Forall_cons; [wk_errno | apply Forall_nil]]) (or_intror I)) as BF2.
assert (GS2 : rw_cells rsegs m2 (GHASH4 + 8) [C4 seedv]) by (eapply rw_cells_transport; [exact GS1 | exact MU2 | exact WM2 | unfold GHASH4; cbn; lia]).
assert (GV2 : rw_cells rsegs m2 GVDSO4 [C8 (Z_to_bv 64 vf)]) by (eapply rw_cells_transport; [exact GV1 | exact MU2 | exact WM2 | unfold GVDSO4; cbn; lia]).
destruct (bv_eqb (grseed_w bs) (Z_to_bv 64 (-1))) eqn:EQ; cbn [negb].
+ eapply tail_reenter; [exact BF2 | exact MI2 | exact ST2 | exact ERR2 | exact GS2 | exact GV2 | exact VF | exact EQ].
+ eapply tail_exit; [exact BF2 | exact MI2 | exact ST2 | exact ERR2 | exact GS2 | exact GV2 | exact VF | exact EQ].
Qed.

#[using="EG LO LOS HT SEEDM1 MOK K"] Lemma seed_body : forall c, Vinv c -> lbw rsegs Vinv T true c.
Proof.
intros c (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & A & errv & junk16 & sbuf & vf
& -> & HP & FR & Hsb & ST & ERR & GH & GG & GV & VF & HPX).
word_range sp SPR. unfold_consts.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
apply (rw_cells_app rsegs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F))]) in GH as [GH8 GS]. cbn [cells_size csize Nat.add] in GS.
replace (GHASH4 + Z.of_nat 8) with (GHASH4 + 8) in GS by lia.
assert (BF : basef m A) by (split; [exact HP | split; [exact GH8 | split; [exact GG | exact HPX]]]).

unfold grs_frame in FR.
pose proof (rw_cells_recast2 m G [CB 16 junk16] sbuf _ FR eq_refl Hsb) as FR1. clear FR.
cbn [cells_bytes cbytes app] in FR1. rewrite app_nil_r in FR1.
set (sb := cells_bytes sbuf) in FR1.
assert (LSB : length sb = 128%nat) by (destruct FR1 as [[WF _] _]; cbn in WF; tauto).
clearbody sb.

eapply lbw_evt; [exact MOK | eapply (gr_pre G s0v) with (lo := lo) (junk16 := junk16) (sbuf := [CB 128 sb]);
[exact MI | exact ST | lia | exact LO | lia | unfold grs_frame; cbn [app]; exact FR1] |].
intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & junk8 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR16 & FRg1).
pose proof (basef_step m m1 A _ BF MU1 WM1 MI1 ltac:(apply Forall_cons; [wk_stack | apply Forall_nil]) (or_intror I)) as BF1.
assert (ERR1 : rw_cells rsegs m1 (0x77c00 - 164) [C4 errv]) by (eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; lia]).
assert (GS1 : rw_cells rsegs m1 (GHASH4 + 8) [C4 seedv]) by (eapply rw_cells_transport; [exact GS | exact MU1 | exact WM1 | unfold GHASH4; cbn; lia]).
assert (GV1 : rw_cells rsegs m1 GVDSO4 [C8 (Z_to_bv 64 vf)]) by (eapply rw_cells_transport; [exact GV | exact MU1 | exact WM1 | unfold GVDSO4; cbn; lia]).

unfold gr_ecall_pc.
eapply (lbw_getrandom_k rsegs) with (buflen := 4) (wf := gr_wf);
[ vm_compute; reflexivity | vm_compute; reflexivity | exact (proj1 MOK) | exact (proj2 MOK)
| reflexivity | reflexivity | lia | lia | right; reflexivity | | | ].
-
unfold grs_frame in FRg1. cbn [app] in FRg1.
pose proof (proj2 (proj1 (rw_cells_app rsegs m1 G [CB 16 junk16] _) FRg1)) as FRb. cbn [cells_size csize Nat.add] in FRb.
pose proof (proj1 (proj1 (rw_cells_app rsegs m1 _ [CB 128 sb] _) FRb)) as FRb1.
cbn [getr bv_eqb reg_get mkR]. replace (G + Z.of_nat 16) with (G + 16) in FRb1 by lia.
apply (rw_cells_CB_store_ok rsegs m1 (G + 16) 128 sb (Z.to_nat 4) FRb1). cbn. lia.
-
intros bs Hb.
unfold regupd. rewrite mkR_set_a0. unfold v_addi. rewrite (unsigned_lit 395368) by lia. replace (395368 + 4) with 395372 by reflexivity.
rewrite <- write_to_mem_wbytes.
match goal with |- context [write_to_mem m1 ?a bs] => replace a with (wa (G + 16)) by reflexivity end.
eapply (child_data m1 A errv vf junk16 junk8 sb bs); try eassumption. lia.
-
intros _. exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. split; [reflexivity|]. exact gr_wf_witness.
Qed.
End SeedLoop.

Section Settle.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Hypothesis AUXV_HI : forall A LB m md, HEAPx A LB m md -> exists aw keys, auxv_at m aw keys /\ hi_top S4L HIx <= aw.

Lemma seed_settle : forall SD, 400 <= SD -> seed_settle_stmt HIx SD.
Proof using AUXV_HI.
intros SD HSD. unfold seed_settle_stmt. intros until seedv. intros HP G GC SEEDM1 ST LO LOS SPA HT ERR K.
unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof G as ([seed0 G1] & G2 & (vf & G3 & VF)). clear G1.
pose proof (heap_presx_refl S4L s4_volatile LB (bv_unsigned sp) m) as HPX.
pose proof (proj1 (proj1 (rw_cells_app rsegs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F))] [C4 seedv]) GC)) as GH8.
pose proof (proj2 (proj1 (rw_cells_app rsegs m GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F))] [C4 seedv]) GC)) as GS.
cbn [cells_size csize Nat.add] in GS. replace (GHASH4 + Z.of_nat 8) with (GHASH4 + 8) in GS by lia. clear GC.
assert (BF : basef HIx sp md LB m m A) by (split; [exact HP | split; [exact GH8 | split; [exact G2 | exact HPX]]]).
unfold GHASH4, GGOT4, GVDSO4, lh_seed_addr in *.
pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
step.
carve_frame 176%nat ST.
step. stepz. step. stepz. stepz. stepz. step. step.
lazymatch goal with |- evt _ _ (QEpW.MS _ _ _ _ _ ?mx _) =>
match goal with H : rw_cells rsegs mx (bv_unsigned sp + -176) (?c16 :: ?c4 :: ?c124 :: ?tl) |- _ =>
change (rw_cells rsegs mx (bv_unsigned sp + -176) ([c16] ++ [c4; c124] ++ tl)) in H; rename H into FRN
end; rename mx into m1 end.
replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) in FRN by (apply bv_eq; reflexivity).
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
apply evt_RZ_done.
apply (rz_loop_w rsegs (Vinv HIx sp gp s0v s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc md LB lo m seedv (bv_unsigned sp + -176))).
-
pose proof (basef_step HIx sp md LB lo m (bv_unsigned sp + -176) ltac:(lia) LO ltac:(lia) HT m m1 A _ BF MU WM MI1
ltac:(apply Forall_cons; [left; cbn [fst snd]; unfold_consts; lia | apply Forall_nil]) (or_intror I)) as (HP1 & GH1 & GG1 & HPX1).
unfold Vinv. do 16 eexists. exists m1, A, errv. eexists. eexists. exists vf.
split; [unfold grs_head_st, grs_head; reflexivity|].
split; [exact HP1|]. split; [unfold grs_frame, grs_ret_pc, lh_seed_addr; exact FRN|]. split; [reflexivity|]. split; [exact ST|].
split; [first [exact ERR | eapply rw_cells_transport; [exact ERR | exact MU | exact WM | cbn; lia]]|].
split.
{ apply (proj2 (rw_cells_app rsegs m1 GHASH4 [C8 (Z_to_bv 64 (fn_lh_char_hash S4F))] [C4 seedv])). split; [exact GH1|].
cbn [cells_size csize Nat.add]. unfold GHASH4. first [exact GS | eapply rw_cells_transport; [exact GS | exact MU | exact WM | cbn; lia]]. }
split; [exact GG1|]. split; [unfold GVDSO4; first [exact G3 | eapply rw_cells_transport; [exact G3 | exact MU | exact WM | cbn; lia]]|].
split; [exact VF | exact HPX1].
-
intros c Hc. eapply seed_body; try eassumption; try reflexivity; try lia.
all: match goal with |- ?g => idtac "LEFT-SETTLE" g end.
Qed.
End Settle.

End RC__1.
