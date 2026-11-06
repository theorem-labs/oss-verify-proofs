(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvsx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvsx.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGaR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGaR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVJy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVJy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QK1W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QK1W. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3rp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3rp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFL8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFL8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmAH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmAH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF.
Import ListNotations.
Open Scope Z_scope.

Module RC := Q6q3.
Module HI := QCcH.
Module JH := QZsi.
Module OSA := QRjH.

Section Hide.
Variable segs : list Segment.
Variable F : word -> bool.
Hypothesis F_off : H_off_segments segs F.

Lemma seg_rom_off : forall x, F x = true -> seg_rom segs x = None.
Proof.
intros x Fx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite (F_off x Fx). reflexivity.
Qed.

Lemma mrd_unhide : forall m x b, mrd segs (mrestrict F m) x = Some b -> mrd segs m x = Some b.
Proof.
intros m x b H. unfold mrd, mrestrict in *. destruct (F x) eqn:Fx; [rewrite (seg_rom_off x Fx) in H; discriminate| exact H].
Qed.

Lemma wview_unhide : forall m x, wview segs (mrestrict F m) x <> None -> wview segs m x <> None.
Proof.
intros m x H. unfold wview, mrestrict in *. destruct (F x) eqn:Fx; [| exact H].
rewrite (F_off x Fx) in H. contradiction.
Qed.

Lemma bytes_at_unhide : forall m a bs, bytes_at segs (mrestrict F m) a bs -> bytes_at segs m a bs.
Proof.
intros m a bs (H0 & H1 & HB). split; [exact H0|]. split; [exact H1|]. intros i Hi. specialize (HB i Hi).
destruct (nth_error bs i) as [b|] eqn:E; [apply mrd_unhide; exact HB|]. apply nth_error_None in E. lia.
Qed.

Lemma wr_at_unhide : forall m a n, wr_at segs (mrestrict F m) a n -> wr_at segs m a n.
Proof. intros m a n (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|]. intros i Hi. apply wview_unhide. exact (HW i Hi). Qed.

Lemma stk_unhide : forall m lo hi, stk segs (mrestrict F m) lo hi -> stk segs m lo hi.
Proof.
intros m lo hi (H0 & H1 & HS). split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (HS a Ha) as [W [b Hb]].
split; [apply wview_unhide; exact W| exists b; apply mrd_unhide; exact Hb].
Qed.

Lemma mem_inv_hide : forall m, mem_inv segs m -> mem_inv segs (mrestrict F m).
Proof. intros m H a b E. unfold mrestrict in E. destruct (F a); [discriminate| exact (H a b E)]. Qed.

Lemma mrestrict_off : forall m x, F x = false -> mrestrict F m x = m x.
Proof. intros m x Fx. unfold mrestrict. rewrite Fx. reflexivity. Qed.

Lemma bytes_at_hide : forall m a bs, (forall x, a <= x < a + Z.of_nat (length bs) -> F (wa x) = false) ->
bytes_at segs m a bs -> bytes_at segs (mrestrict F m) a bs.
Proof.
intros m a bs HF (H0 & H1 & HB). split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (HB i Hi).
unfold mrd. rewrite mrestrict_off by (apply HF; lia). reflexivity.
Qed.

Lemma stk_hide : forall m lo hi, (forall x, lo <= x < hi -> F (wa x) = false) -> stk segs m lo hi -> stk segs (mrestrict F m) lo hi.
Proof.
intros m lo hi HF (H0 & H1 & HS). split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (HS a Ha) as [W [b Hb]].
unfold wview, mrd in *. rewrite mrestrict_off by (apply HF; exact Ha). split; [exact W| exists b; exact Hb].
Qed.

End Hide.

Section Inst0.
Context {RC__ : RC.RunConsts}.
Variable L : JH.heap_layout_A.
Notation HL := (JH.hla_base L).
Notation segs := (HI.hl_segs HL).

Variable LA : ALay.
Variable LV : lvp.
Variable BUDGET : Z.
Variable PERM : list (Z * Z).
Variables TOT0 N0 : Z.
Hypothesis LL : ll_ok LA LV BUDGET PERM TOT0 N0.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.
Variable DL : dlayout.
Variable RE : aentry.
Hypothesis RE_L : ae_L RE = LA.
Variable DCo : donor_core RC.alloc_ceiling segs (at_nodeA LV segs) DL.

Variable FRl : list (Z * Z).
Hypothesis HFR : Forall (fr_ok LA PERM) FRl.
Notation F := (Fof LV FRl).
Hypothesis F_off : H_off_segments segs F.
Hypothesis F_low : forall x, F x = true -> bv_unsigned x < RC.alloc_ceiling.

Hypothesis L_malloc : HI.hl_malloc HL = dl_malloc DL.
Hypothesis L_free : HI.hl_free HL = dl_free DL.
Hypothesis L_calloc : HI.hl_calloc HL = dl_calloc DL.
Hypothesis L_tp : HI.hl_tp HL = dl_tp DL.
Hypothesis L_gp : JH.hl_gp L = dl_gp DL.
Hypothesis L_errno : dl_errno DL = HI.hl_tp HL - 164.
Hypothesis L_stack : dl_malloc_stack DL <= JH.hl_stack_A L /\ dl_free_stack DL <= JH.hl_stack_A L /\ dl_calloc_stack DL <= JH.hl_stack_A L.
Hypothesis L_static : forall a, HI.hl_client_static HL a -> dl_client_data DL a.
Hypothesis L_stackA : 64 <= JH.hl_stack_A L.
Hypothesis L_sb : JH.hl_sb L = kShadowOffset.

Hypothesis L_dpn : 0 <= dl_depot_n DL /\ dl_depot_n DL + 4 <= RC.alloc_ceiling.

Definition hi_top : Z := ae_stack_top RE.

Definition blk_of (b : ablock) : HI.blk := (ablk_addr b, ablk_size b).
Definition fr_of (f : fframe) : JH.frame := (ff_addr f, ff_cls f).

Notation KIx := (KI LV BUDGET PERM TOT0 N0).

Variable RSV : Z.
Hypothesis HRSV : 0 <= RSV.

Definition qliveX (X : list aptr) : Z := zsum (map (fun p => aptr_used p + kBatchBytes) X).
Definition QBA (ps : PStateA) (LBd : list ablock) (B : JH.bud) : Prop :=
0 <= JH.bQ B /\ qtot (ps_a ps) + qliveX (map ablk_id LBd) + JH.bQ B <= kQMaxSize.

Lemma qwf_nonneg : forall q, qwf q -> 0 <= q_bytes q.
Proof.
intros q [HF E]. rewrite E. clear E. induction HF as [|b l Hb _ IH]; [cbn; lia|]. cbn [map]. rewrite zsum_cons.
destruct Hb as (_ & _ & Es). rewrite Es.
assert (0 <= zsum (map aptr_used (b_chunks b))).
{ clear. induction (b_chunks b) as [|p l IH]; [cbn; lia|]. cbn [map]. rewrite zsum_cons. unfold aptr_used at 1, used_size. lia. }
unfold kBatchBytes. lia.
Qed.
Lemma qliveX_nonneg : forall X, 0 <= qliveX X.
Proof.
induction X as [|p X IH]; unfold qliveX in *; [cbn; lia|]. cbn [map]. rewrite zsum_cons.
assert (0 <= kBatchBytes) by (unfold kBatchBytes; lia). unfold aptr_used at 1, used_size. lia.
Qed.
Lemma ainv_q_nonneg : forall X a, ainv X a -> 0 <= q_bytes (as_gq a) /\ 0 <= q_bytes (as_tq a).
Proof. intros X a [AIx _]. split; apply qwf_nonneg; [exact (ai_gq _ _ _ _ AIx)| exact (ai_tq _ _ _ _ AIx)]. Qed.

Definition HEAPA0g (g : ghost) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (m : word -> option byte) (c : config) : Prop :=
exists (ps : PStateA) (LBd : list ablock) (FSd : list fframe),
dc_run _ _ _ _ DCo ps LBd FSd RE (mrestrict F m)
/\ LB = map blk_of LBd /\ FR = map fr_of FSd
/\ ainv (map ablk_id LBd) (ps_a ps) /\ GS (ps_a ps) g
/\ zlen LBd + JH.bN B <= kCapN
/\ CAPS + as_spent (ps_a ps) + JH.bB B + RSV <= BUDGET
/\ KIx g (cfg_model c)
/\ cinvA LV (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None
/\ mem_inv segs m
/\ Forall (fun b => wr_at segs m (ablk_addr b) (ablk_size b)
/\ forall x, ablk_addr b <= x < ablk_addr b + ablk_size b -> F (wa x) = false) LBd
/\ (forall a n x, In (a, n) LM -> a <= x < a + n -> F (wa x) = true)
/\ 0 <= JH.bB B /\ 0 <= JH.bD B /\ 0 <= JH.bN B

/\ (exists dn, depot_n segs DL (mrestrict F m) dn /\ dn + zlen LBd + 2 * JH.bN B <= DEPOT_CAP)
/\ stk segs m RC.alloc_ceiling hi_top
/\ QBA ps LBd B.

Definition HEAPA0 (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (m : word -> option byte) (c : config) : Prop :=
exists g, HEAPA0g g LB LM FR B m c.

Lemma F_above : forall x, RC.alloc_ceiling <= x < 2^64 -> F (wa x) = false.
Proof.
intros x Hx. destruct (F (wa x)) eqn:E; [|reflexivity]. pose proof (F_low _ E) as H. rewrite wa_unsigned in H by lia. lia.
Qed.

Definition fr_ivs0 (FR : list JH.frame) : list HI.blk :=
flat_map (fun f => [(JH.fr_base f, JH.fr_size (JH.fr_class f) - 8); (JH.shad L (JH.fr_base f), JH.fr_shadow_len (JH.fr_class f))]) FR.

Lemma restrict_MS_inv : forall (H : word -> bool) ms R Fr pc fc rv m1 ro,
restrict H ms = MS R Fr pc fc rv m1 ro -> ms = MS R Fr pc fc rv (ms_mem ms) ro /\ mrestrict H (ms_mem ms) = m1.
Proof.
intros H [r f p sv rs fcs mm ro0] R Fr pc fc rv m1 ro E. unfold restrict, MS in *. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
injection E as -> -> -> -> -> -> E ->. split; [reflexivity| exact E].
Qed.

Lemma mem_inv_unhide : forall m, mem_inv segs (mrestrict F m) -> mem_inv segs m.
Proof.
intros m H a b E. destruct (F a) eqn:Fa.
- unfold ro_addr. rewrite (F_off a Fa). reflexivity.
- apply (H a b). unfold mrestrict. rewrite Fa. exact E.
Qed.

Lemma wview_off : forall m x, F x = false -> wview segs (mrestrict F m) x = wview segs m x.
Proof. intros m x Fx. unfold wview. rewrite (mrestrict_off F m x Fx). reflexivity. Qed.

Lemma in_block_map : forall LBd a, HI.in_block (map blk_of LBd) a -> in_ablock LBd a.
Proof.
intros LBd a (b & Hb & Hr). apply in_map_iff in Hb as (bd & <- & Hbd). exists bd. split; [exact Hbd| exact Hr].
Qed.

Lemma in_fr_ivs0 : forall FSd a, HI.in_block (fr_ivs0 (map fr_of FSd)) a -> in_fframe_body FSd a \/ in_fframe_shadow FSd a.
Proof.
intros FSd a (b & Hb & Hr). unfold fr_ivs0 in Hb. apply in_flat_map in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (fd & <- & Hfd).
cbn [In] in Hb. destruct Hb as [<-|[<-|[]]]; unfold HI.blk_addr, HI.blk_size, fr_of, JH.fr_base, JH.fr_class in Hr; cbn [fst snd] in Hr.
- left. exists fd. split; [exact Hfd|]. unfold JH.fr_size in Hr. unfold ff_size. lia.
- right. exists fd. split; [exact Hfd|]. unfold JH.shad, JH.fr_shadow_len in Hr. rewrite L_sb in Hr. unfold SH, ff_size.
replace (64 * 2 ^ ff_cls fd / 8) with (8 * 2 ^ ff_cls fd) by (replace (64 * 2 ^ ff_cls fd) with (8 * 2 ^ ff_cls fd * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
exact Hr.
Qed.

Lemma gen_pres : forall LBd' FSd SP m m'',
aheap_presA RC.alloc_ceiling segs DL LBd' FSd SP (mrestrict F m) (mrestrict F m'') ->
(forall x, F x = true -> m'' x = m x) ->
forall a, 0 <= a < 2^64 -> (F (wa a) = false -> aclient_addrA RC.alloc_ceiling DL LBd' FSd SP a) ->
m'' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m'' (wa a) <> None).
Proof.
intros LBd' FSd SP m m'' Hpres HFm a Ha Hcl. destruct (F (wa a)) eqn:Fa.
- pose proof (HFm _ Fa) as E. split; [exact E|]. unfold wview. rewrite E. auto.
- destruct (Hpres a Ha (Hcl eq_refl)) as [E W]. rewrite (mrestrict_off F m'' _ Fa), (mrestrict_off F m _ Fa) in E.
split; [exact E|]. rewrite !(wview_off _ _ Fa) in W. exact W.
Qed.

Lemma wr_keep : forall LBd' FSd SP m m'' (LBk : list ablock),
(forall a, 0 <= a < 2^64 -> (F (wa a) = false -> aclient_addrA RC.alloc_ceiling DL LBd' FSd SP a) ->
m'' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m'' (wa a) <> None)) ->
(forall b, In b LBk -> In b LBd') ->
Forall (fun b => wr_at segs m (ablk_addr b) (ablk_size b) /\ forall x, ablk_addr b <= x < ablk_addr b + ablk_size b -> F (wa x) = false) LBk ->
Forall (fun b => wr_at segs m'' (ablk_addr b) (ablk_size b) /\ forall x, ablk_addr b <= x < ablk_addr b + ablk_size b -> F (wa x) = false) LBk.
Proof.
intros LBd' FSd SP m m'' LBk Hgen Hsub HW. apply Forall_forall. intros b Hb.
destruct (proj1 (Forall_forall _ _) HW b Hb) as ((W0 & W1 & HWb) & HFb). split; [| exact HFb]. split; [exact W0|]. split; [exact W1|]. intros i Hi.
apply (Hgen (ablk_addr b + i) ltac:(lia)); [| exact (HWb i Hi)].
intros _. right; right; left. exists b. split; [apply Hsub; exact Hb| lia].
Qed.

Lemma wr_at_hidden_off : forall m a n, wr_at segs (mrestrict F m) a n -> forall x, a <= x < a + n -> F (wa x) = false.
Proof.
intros m a n (_ & _ & HW) x Hx. destruct (F (wa x)) eqn:E; [|reflexivity]. exfalso.
apply (HW (x - a) ltac:(lia)). replace (a + (x - a)) with x by lia. unfold wview, mrestrict. rewrite E, (F_off _ E). reflexivity.
Qed.

Lemma stk_sub0 : forall m lo lo' hi, stk segs m lo hi -> lo <= lo' -> stk segs m lo' hi.
Proof. intros m lo lo' hi (H0 & H1 & HS) Hl. split; [lia|]. split; [exact H1|]. intros a Ha. apply HS. lia. Qed.

Lemma stk_join : forall m lo sp, stk segs m RC.alloc_ceiling hi_top -> stk segs m lo sp ->
RC.alloc_ceiling <= lo -> lo <= sp - JH.hl_stack_A L -> lo <= hi_top -> stk segs m RC.alloc_ceiling sp.
Proof.
intros m lo sp (I0 & I1 & HI) (S0 & S1 & HS) Hlo Hlo2 Htop. split; [exact I0|]. split; [exact S1|]. intros a Ha.
destruct (Z.lt_ge_cases a hi_top) as [Hlt|Hge]; [apply HI; lia| apply HS; lia].
Qed.

Lemma unw_readable0 : forall m sp, stk segs m RC.alloc_ceiling hi_top -> RC.alloc_ceiling <= sp -> unw_readable segs RE (mrestrict F m) sp.
Proof.
intros m sp (_ & _ & HI) Hsp x Hx Hx64. destruct (HI x ltac:(unfold hi_top; lia)) as [_ [b Hb]]. exists b.
unfold mrd in *. rewrite (mrestrict_off F m _ (F_above x ltac:(lia))). exact Hb.
Qed.

Lemma stk_after : forall m m' sp, stk segs m RC.alloc_ceiling hi_top -> stk segs m' RC.alloc_ceiling sp ->
(forall a, 0 <= a < 2^64 -> sp <= a -> m' (wa a) = m (wa a)) -> stk segs m' RC.alloc_ceiling hi_top.
Proof.
intros m m' sp (I0 & I1 & HI) (S0 & S1 & HS) Hag. split; [exact I0|]. split; [exact I1|]. intros a Ha.
destruct (Z.lt_ge_cases a sp) as [Hlt|Hge]; [apply HS; lia|].
destruct (HI a Ha) as [W R]. pose proof (Hag a ltac:(lia) Hge) as E. unfold wview, mrd in *. rewrite E. split; assumption.
Qed.

Lemma zlen_nonneg0 : forall (A : Type) (l : list A), 0 <= zlen l. Proof. intros. unfold zlen. lia. Qed.

Lemma depot_n_agree : forall (m1 m2 : word -> option byte) dn, depot_n segs DL m1 dn ->
(forall x, dl_depot_n DL <= x < dl_depot_n DL + 4 -> m2 (wa x) = m1 (wa x)) -> depot_n segs DL m2 dn.
Proof.
intros m1 m2 dn [[[Hwf (B0 & B1 & HB)] (W0 & W1 & HW)] Hp] Hag. split; [| exact Hp].
assert (Hlen : length (cells_bytes [C4 (Z_to_bv 64 dn)]) = 4%nat) by (cbn [cells_bytes cbytes app]; rewrite app_nil_r; apply length_Z_to_le_bytes).
assert (E4 : Z.of_nat (cells_size [C4 (Z_to_bv 64 dn)]) = 4) by reflexivity. rewrite E4 in *.
split; [split; [exact Hwf|]|].
- split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (HB i Hi). rewrite Hlen in Hi. unfold mrd. rewrite (Hag (dl_depot_n DL + Z.of_nat i)) by lia. reflexivity.
- split; [exact W0|]. split; [exact W1|]. intros i Hi. specialize (HW i Hi). unfold wview in *. rewrite (Hag (dl_depot_n DL + i)) by lia. exact HW.
Qed.

Theorem hiA_malloc0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (n lo : Z) (u : JH.uwd) (g : ghost),
HEAPA0g g LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
lo <= hi_top ->
1 <= JH.bN B -> JH.acostA n <= JH.bB B -> JH.uw_cost u <= JH.bD B -> n + 8192 <= JH.bQ B ->
(forall ms' m' c' g' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m' ->
vmst (cfg_model c) (cfg_model c') ->
(forall x, F x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
r <> 0 -> (exists junk, OT.rw_cells segs m' r [OC.CB (Z.to_nat n) junk]) ->
HEAPA0g g' ((r, n) :: LB) LM FR (JH.chargeQ (JH.charge B (JH.acostA n) (JH.uw_cost u) 1) (n + 8192)) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_malloc HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T LB LM FR B n lo u g
HP Hstk Hlo Hlo2 Htp Hgp Ha0 Hn Htop HbN HbB HbD HbQ HK.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
destruct L_stack as (Ls1 & Ls2 & Ls3).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Hsp64 : bv_unsigned sp <= 2^64) by (destruct Hstk as (_ & H & _); exact H).
pose proof (stk_join m lo (bv_unsigned sp) HSTK Hstk Hlo Hlo2 Htop) as Hstk0. pose proof (unw_readable0 m (bv_unsigned sp) HSTK ltac:(lia)) as Hur.
destruct HDN as (dn & HDn & HDcap). pose proof (zlen_nonneg0 _ LBd) as Hz0.
assert (Hstk' : stk segs (mrestrict F m) RC.alloc_ceiling (bv_unsigned sp)) by (apply stk_hide; [intros x Hx; apply F_above; lia| exact Hstk0]).
pose proof (dc_malloc _ _ _ _ DCo LA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
Fr fc (mrestrict F m) ps LBd FSd RE n RC.alloc_ceiling dn RE_L RUN Hstk' (Z.le_refl _) ltac:(lia) (mem_inv_hide segs F m MI)
ltac:(rewrite <- L_tp; exact Htp) ltac:(rewrite <- L_gp; exact Hgp) Hur HDn ltac:(lia) Ha0 ltac:(lia)) as Himpl.
rewrite <- L_malloc in Himpl.
match goal with |- AJv _ _ _ _ ?st => set (msv := st) end.
match type of Himpl with implMG _ _ _ _ _ ?st => change st with (restrict F msv) in Himpl end.
set (X := map ablk_id LBd) in *.
assert (HlenX : zlen X <= kCapN) by (unfold X, zlen in *; rewrite length_map; lia).
pose proof (cap_ok_of_len X HlenX) as Hcapok.
pose proof (mcost_le_acost n ltac:(lia)) as Hmc. change (if n <=? 64512 then 0 else 3 * n + 45101) with (JH.acostA n) in Hmc.
unfold AJv.
apply (amalloc_vj_Fq segs LA LV BUDGET PERM TOT0 N0 LL Hwx Hsegs Hsh Hbx Hbc FRl HFR F_off T X n g ps _ c msv Himpl HC
ltac:(lia) ltac:(unfold kMaxReq; lia) (too_big_small n ltac:(lia)) AI G (cap_ok_room X _ n AI Hcapok ltac:(lia))
ltac:(lia) (cap_ok_reg X _ AI Hcapok) K).
intros p ps' c1 msv1 HQ (a' & g' & Eps & Hvo & K' & G' & Hsp' & AI' & Hnin & Hshape & KT & KG) HC1 Hh1 Hvm HF1.
apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply (evt_restrict_lift segs F F_off Hwx) in HQ. eapply evt_mono; [exact HQ|]. clear HQ.
intros ms'' [HPo Hhs].
destruct HPo as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & Ems & MI1 & Hstk1 & Hpres & _ & _ & HKo).
destruct HKo as [(dn' & HDn' & Hdn') HKo]. destruct HKo as (A & junk & -> & HrA & Hreq & RUN1 & Hcells & Hshadow & _).
destruct (restrict_MS_inv F ms'' _ _ _ _ _ _ _ Ems) as [Ems'' Em1]. set (m'' := ms_mem ms'') in *.
destruct (dc_errno _ _ _ _ DCo _ _ _ _ _ RUN1) as [errv' Herr].
subst m1'.
assert (HFm : forall x, F x = true -> m'' x = m x) by (intros x Fx; unfold m''; rewrite (Hhs _ Fx); exact (HF1 _ Fx)).
pose proof (gen_pres LBd FSd _ m m'' Hpres HFm) as Hgen0.
apply (HK ms'' m'' c1 g' A errv').
-
unfold HI.ret_state. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. exact Ems''.
-
destruct Hvo as (V1 & V2 & V3 & V4 & V5 & V6). unfold HI.model_vm_only. repeat split; try assumption. exact (vmst_init_sp _ _ Hvm).
- exact (stk_sub0 m'' _ lo _ (stk_unhide segs F F_off m'' _ _ Hstk1) Hlo).
-
intros a Ha Hcl. change (OM.wa a) with (wa a). destruct (F (wa a)) eqn:Fa.
+ assert (E : m'' (wa a) = m (wa a)) by (unfold m''; rewrite (Hhs _ Fa); exact (HF1 _ Fa)).
split; [exact E|]. unfold wview. rewrite E. auto.
+ assert (Hdc : aclient_addrA RC.alloc_ceiling DL LBd FSd (bv_unsigned sp) a).
{ destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
- right; right; left. apply in_block_map. rewrite <- ELB. exists b. auto.
- apply in_app_iff in Hb as [Hb|Hb].
+ exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa. discriminate.
+ rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H]. }
destruct (Hpres a Ha Hdc) as [E W]. rewrite (mrestrict_off F m'' _ Fa), (mrestrict_off F m _ Fa) in E.
split; [exact E|]. rewrite !(wview_off _ _ Fa) in W. exact W.
- exact Hvm.
- exact HFm.
- intros a Ha Hcd. apply (Hgen0 a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd).
-
rewrite L_errno in Herr. apply (rw_cells_D segs m'' _ [OC.C4 errv']). cbn [map cellD].
destruct Herr as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs F F_off m'' _ _ Hb)]| exact (wr_at_unhide segs F F_off m'' _ _ Hw)].
- destruct HrA as (((Hlh & _) & _) & _). destruct Hlh as [[H _]|H]; [lia| unfold KHI, Qqcs.Mq0.kHighMemBeg in H; lia].
- exists junk. apply (rw_cells_D segs m'' _ [OC.CB (Z.to_nat n) junk]). cbn [map cellD].
destruct Hcells as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs F F_off m'' _ _ Hb)]| exact (wr_at_unhide segs F F_off m'' _ _ Hw)].
-
exists ps', ((p, A, n) :: LBd), FSd.
assert (Ea : ps_a ps' = a') by (rewrite Eps; reflexivity).
split; [exact RUN1|]. split; [cbn [map]; unfold blk_of at 1; cbn [ablk_addr ablk_size fst snd]; rewrite ELB; reflexivity|].
split; [exact EFR|]. split; [rewrite Ea; exact AI'|]. split; [rewrite Ea; exact G'|].
split; [cbn [JH.chargeQ JH.charge JH.bN]; rewrite zlen_cons; lia|].
split; [rewrite Ea; cbn [JH.chargeQ JH.charge JH.bB]; lia|].
split; [exact K'|]. split; [exact HC1|]. split; [exact Hh1|]. split; [exact (mem_inv_unhide m'' MI1)|].
split.
{ constructor; [| exact (wr_keep LBd FSd _ m m'' LBd Hgen0 (fun b H => H) HWR)].
cbn [ablk_addr ablk_size fst snd]. destruct Hcells as [_ Hw].
cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
split; [exact (wr_at_unhide segs F F_off _ _ _ Hw)| exact (wr_at_hidden_off _ _ _ Hw)]. }
split; [exact HLM|]. cbn [JH.chargeQ JH.charge JH.bB JH.bD JH.bN]. split; [lia|]. split; [lia|]. split; [lia|].

split; [exists dn'; split; [exact HDn'| cbn [JH.chargeQ JH.charge JH.bN]; rewrite zlen_cons; lia]|]. split; [exact (stk_after m m'' (bv_unsigned sp) HSTK (stk_unhide segs F F_off m'' _ _ Hstk1) (fun a Ha Hsp => proj1 (Hgen0 a Ha (fun _ => or_introl Hsp))))|].
unfold QBA in *. rewrite Ea. unfold qtot in *. rewrite KT, KG. cbn [map ablk_id fst JH.chargeQ JH.charge JH.bQ]. unfold qliveX in *. cbn [map]. rewrite zsum_cons.
unfold aptr_used at 1. rewrite Hreq. unfold used_size. unfold kBatchBytes in *. lia.
Qed.

Theorem hiA_calloc0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (cnt sz lo : Z) (u : JH.uwd) (g : ghost),
let n := cnt * sz in
HEAPA0g g LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> 1 <= n <= 2^26 ->
lo <= hi_top ->
1 <= JH.bN B -> JH.acostA n <= JH.bB B -> JH.uw_cost u <= JH.bD B -> n + 8192 <= JH.bQ B ->
(forall ms' m' c' g' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m' ->
vmst (cfg_model c) (cfg_model c') ->
(forall x, F x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
r <> 0 -> OT.rw_cells segs m' r [OC.CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
HEAPA0g g' ((r, n) :: LB) LM FR (JH.chargeQ (JH.charge B (JH.acostA n) (JH.uw_cost u) 1) (n + 8192)) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_calloc HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T LB LM FR B cnt sz lo u g n
HP Hstk Hlo Hlo2 Htp Hgp Ha0 Ha1 Hcnt Hsz Hn Htop HbN HbB HbD HbQ HK.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
destruct L_stack as (Ls1 & Ls2 & Ls3).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Hsp64 : bv_unsigned sp <= 2^64) by (destruct Hstk as (_ & H & _); exact H).
pose proof (stk_join m lo (bv_unsigned sp) HSTK Hstk Hlo Hlo2 Htop) as Hstk0. pose proof (unw_readable0 m (bv_unsigned sp) HSTK ltac:(lia)) as Hur.
destruct HDN as (dn & HDn & HDcap). pose proof (zlen_nonneg0 _ LBd) as Hz0.
assert (Hstk' : stk segs (mrestrict F m) RC.alloc_ceiling (bv_unsigned sp)) by (apply stk_hide; [intros x Hx; apply F_above; lia| exact Hstk0]).
pose proof (dc_calloc _ _ _ _ DCo LA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
Fr fc (mrestrict F m) ps LBd FSd RE cnt sz RC.alloc_ceiling dn RE_L RUN Hstk' (Z.le_refl _) ltac:(lia) (mem_inv_hide segs F m MI)
ltac:(rewrite <- L_tp; exact Htp) ltac:(rewrite <- L_gp; exact Hgp) Hur HDn ltac:(lia) Ha0 Ha1 Hcnt Hsz ltac:(unfold n in Hn; lia)) as Himpl.
assert (Hov : calloc_overflows cnt sz = false).
{ unfold calloc_overflows. destruct (Z.eqb_spec sz 0) as [->|Hz]; [reflexivity|]. cbn [negb andb]. apply Z.ltb_ge.
assert (2^32 <= (2^64 - 1) / sz) by (apply Z.div_le_lower_bound; [lia|]; nia). lia. }
rewrite Hov in Himpl. fold n in Himpl.
rewrite <- L_calloc in Himpl.
match goal with |- AJv _ _ _ _ ?st => set (msv := st) end.
match type of Himpl with implMG _ _ _ _ _ ?st => change st with (restrict F msv) in Himpl end.
set (X := map ablk_id LBd) in *.
assert (HlenX : zlen X <= kCapN) by (unfold X, zlen in *; rewrite length_map; lia).
pose proof (cap_ok_of_len X HlenX) as Hcapok.
pose proof (mcost_le_acost n ltac:(lia)) as Hmc. change (if n <=? 64512 then 0 else 3 * n + 45101) with (JH.acostA n) in Hmc.
unfold AJv.
apply (amalloc_vj_Fq segs LA LV BUDGET PERM TOT0 N0 LL Hwx Hsegs Hsh Hbx Hbc FRl HFR F_off T X n g ps _ c msv Himpl HC
ltac:(lia) ltac:(unfold kMaxReq; lia) (too_big_small n ltac:(lia)) AI G (cap_ok_room X _ n AI Hcapok ltac:(lia))
ltac:(lia) (cap_ok_reg X _ AI Hcapok) K).
intros p ps' c1 msv1 HQ (a' & g' & Eps & Hvo & K' & G' & Hsp' & AI' & Hnin & Hshape & KT & KG) HC1 Hh1 Hvm HF1.
apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply (evt_restrict_lift segs F F_off Hwx) in HQ. eapply evt_mono; [exact HQ|]. clear HQ.
intros ms'' [HPo Hhs].
destruct HPo as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & Ems & MI1 & Hstk1 & Hpres & _ & _ & HKo).
destruct HKo as [(dn' & HDn' & Hdn') HKo]. destruct HKo as (A & -> & HrA & Hreq & RUN1 & Hcells & Hshadow).
destruct (restrict_MS_inv F ms'' _ _ _ _ _ _ _ Ems) as [Ems'' Em1]. set (m'' := ms_mem ms'') in *.
destruct (dc_errno _ _ _ _ DCo _ _ _ _ _ RUN1) as [errv' Herr].
subst m1'.
assert (HFm : forall x, F x = true -> m'' x = m x) by (intros x Fx; unfold m''; rewrite (Hhs _ Fx); exact (HF1 _ Fx)).
pose proof (gen_pres LBd FSd _ m m'' Hpres HFm) as Hgen0.
apply (HK ms'' m'' c1 g' A errv').
-
unfold HI.ret_state. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. exact Ems''.
-
destruct Hvo as (V1 & V2 & V3 & V4 & V5 & V6). unfold HI.model_vm_only. repeat split; try assumption. exact (vmst_init_sp _ _ Hvm).
- exact (stk_sub0 m'' _ lo _ (stk_unhide segs F F_off m'' _ _ Hstk1) Hlo).
-
intros a Ha Hcl. change (OM.wa a) with (wa a). destruct (F (wa a)) eqn:Fa.
+ assert (E : m'' (wa a) = m (wa a)) by (unfold m''; rewrite (Hhs _ Fa); exact (HF1 _ Fa)).
split; [exact E|]. unfold wview. rewrite E. auto.
+ assert (Hdc : aclient_addrA RC.alloc_ceiling DL LBd FSd (bv_unsigned sp) a).
{ destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
- right; right; left. apply in_block_map. rewrite <- ELB. exists b. auto.
- apply in_app_iff in Hb as [Hb|Hb].
+ exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa. discriminate.
+ rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H]. }
destruct (Hpres a Ha Hdc) as [E W]. rewrite (mrestrict_off F m'' _ Fa), (mrestrict_off F m _ Fa) in E.
split; [exact E|]. rewrite !(wview_off _ _ Fa) in W. exact W.
- exact Hvm.
- exact HFm.
- intros a Ha Hcd. apply (Hgen0 a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd).
-
rewrite L_errno in Herr. apply (rw_cells_D segs m'' _ [OC.C4 errv']). cbn [map cellD].
destruct Herr as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs F F_off m'' _ _ Hb)]| exact (wr_at_unhide segs F F_off m'' _ _ Hw)].
- destruct HrA as (((Hlh & _) & _) & _). destruct Hlh as [[H _]|H]; [lia| unfold KHI, Qqcs.Mq0.kHighMemBeg in H; lia].
- apply (rw_cells_D segs m'' _ [OC.CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]). cbn [map cellD].
destruct Hcells as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs F F_off m'' _ _ Hb)]| exact (wr_at_unhide segs F F_off m'' _ _ Hw)].
-
exists ps', ((p, A, n) :: LBd), FSd.
assert (Ea : ps_a ps' = a') by (rewrite Eps; reflexivity).
split; [exact RUN1|]. split; [cbn [map]; unfold blk_of at 1; cbn [ablk_addr ablk_size fst snd]; rewrite ELB; reflexivity|].
split; [exact EFR|]. split; [rewrite Ea; exact AI'|]. split; [rewrite Ea; exact G'|].
split; [cbn [JH.chargeQ JH.charge JH.bN]; rewrite zlen_cons; lia|].
split; [rewrite Ea; cbn [JH.chargeQ JH.charge JH.bB]; lia|].
split; [exact K'|]. split; [exact HC1|]. split; [exact Hh1|]. split; [exact (mem_inv_unhide m'' MI1)|].
split.
{ constructor; [| exact (wr_keep LBd FSd _ m m'' LBd Hgen0 (fun b H => H) HWR)].
cbn [ablk_addr ablk_size fst snd]. destruct Hcells as [_ Hw].
cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
split; [exact (wr_at_unhide segs F F_off _ _ _ Hw)| exact (wr_at_hidden_off _ _ _ Hw)]. }
split; [exact HLM|]. cbn [JH.chargeQ JH.charge JH.bB JH.bD JH.bN]. split; [lia|]. split; [lia|]. split; [lia|].

split; [exists dn'; split; [exact HDn'| cbn [JH.chargeQ JH.charge JH.bN]; rewrite zlen_cons; lia]|]. split; [exact (stk_after m m'' (bv_unsigned sp) HSTK (stk_unhide segs F F_off m'' _ _ Hstk1) (fun a Ha Hsp => proj1 (Hgen0 a Ha (fun _ => or_introl Hsp))))|].
unfold QBA in *. rewrite Ea. unfold qtot in *. rewrite KT, KG. cbn [map ablk_id fst JH.chargeQ JH.charge JH.bQ]. unfold qliveX in *. cbn [map]. rewrite zsum_cons.
unfold aptr_used at 1. rewrite Hreq. unfold used_size. unfold kBatchBytes in *. lia.
Qed.

Lemma alb_remove_cons : forall bd LBd p,
alb_remove p (bd :: LBd) = if aptr_eqb (ablk_id bd) p then alb_remove p LBd else bd :: alb_remove p LBd.
Proof.
intros bd LBd p. unfold alb_remove. rewrite filter_cons.
destruct (aptr_eqb (ablk_id bd) p); cbn [negb]; destruct (decide _) as [H|H]; try reflexivity; exfalso; [exact H| apply H; exact I].
Qed.

Lemma alb_remove_notin : forall LBd p, ~ In p (map ablk_id LBd) -> alb_remove p LBd = LBd.
Proof.
induction LBd as [|bd LBd IH]; intros p Hnin; [reflexivity|]. rewrite alb_remove_cons. cbn [map In] in Hnin.
destruct (aptr_eqb (ablk_id bd) p) eqn:E; [apply aptr_eqb_eq in E; exfalso; apply Hnin; left; exact E|].
f_equal. apply IH. intros H. apply Hnin. right. exact H.
Qed.

Lemma alb_remove_map : forall LBd p A n,
List.NoDup (map ablk_id LBd) ->
(forall b1 b2, In b1 LBd -> In b2 LBd -> ablk_id b1 <> ablk_id b2 -> ablk_addr b1 <> ablk_addr b2) ->
In (p, A, n) LBd ->
map blk_of (alb_remove p LBd) = HI.lb_remove A (map blk_of LBd).
Proof.
induction LBd as [|bd LBd IH]; intros p A n ND Hdj Hin; [destruct Hin|].
cbn [map ablk_id] in ND. inversion ND as [|x l Hnin ND']; subst.
rewrite alb_remove_cons. cbn [map HI.lb_remove]. unfold HI.blk_addr at 1. unfold blk_of at 2. cbn [fst].
destruct (aptr_eqb (ablk_id bd) p) eqn:E.
- apply aptr_eqb_eq in E.
assert (Ebd : bd = (p, A, n)).
{ destruct Hin as [Hin|Hin]; [exact Hin|]. exfalso. apply Hnin. rewrite E. apply in_map_iff. exists (p, A, n). split; [reflexivity| exact Hin]. }
subst bd. cbn [ablk_addr ablk_id fst snd] in *. rewrite Z.eqb_refl. rewrite (alb_remove_notin LBd p Hnin). reflexivity.
- assert (Hne : ablk_id bd <> p) by (intros E'; rewrite E' in E; assert (aptr_eqb p p = true) by (apply aptr_eqb_eq; reflexivity); congruence).
destruct Hin as [Hin|Hin]; [subst bd; cbn [ablk_id fst] in Hne; contradiction|].
assert (Hna : ablk_addr bd <> A).
{ apply (Hdj bd (p, A, n)); [left; reflexivity| right; exact Hin| exact Hne]. }
destruct (Z.eqb_spec (ablk_addr bd) A); [contradiction|]. cbn [map]. f_equal.
apply (IH p A n ND'); [| exact Hin]. intros b1 b2 H1 H2. apply Hdj; right; assumption.
Qed.

Lemma alb_remove_perm : forall LBd p A n, List.NoDup (map ablk_id LBd) -> In (p, A, n) LBd ->
Permutation (map ablk_id LBd) (p :: map ablk_id (alb_remove p LBd)).
Proof.
induction LBd as [|bd LBd IH]; intros p A n ND Hin; [destruct Hin|].
cbn [map ablk_id] in ND. inversion ND as [|x l Hnin ND']; subst.
rewrite alb_remove_cons. cbn [map].
destruct (aptr_eqb (ablk_id bd) p) eqn:E.
- apply aptr_eqb_eq in E. rewrite E in *. rewrite (alb_remove_notin LBd p Hnin). apply Permutation_refl.
- destruct Hin as [Hin|Hin].
+ subst bd. cbn [ablk_id fst] in E. assert (aptr_eqb p p = true) by (apply aptr_eqb_eq; reflexivity). congruence.
+ cbn [map]. etransitivity; [apply perm_skip; exact (IH p A n ND' Hin)| apply perm_swap].
Qed.

Lemma alb_remove_In : forall LBd p b, In b (alb_remove p LBd) -> In b LBd.
Proof.
induction LBd as [|bd LBd IH]; intros p b Hb; [exact Hb|]. rewrite alb_remove_cons in Hb.
destruct (aptr_eqb (ablk_id bd) p); [right; exact (IH p b Hb)|]. destruct Hb as [Hb|Hb]; [left; exact Hb| right; exact (IH p b Hb)].
Qed.

Lemma zlen_alb_remove : forall LBd p, zlen (alb_remove p LBd) <= zlen LBd.
Proof.
induction LBd as [|bd LBd IH]; intros p; [apply Z.le_refl|]. rewrite alb_remove_cons. specialize (IH p).
destruct (aptr_eqb (ablk_id bd) p); rewrite ?zlen_cons; lia.
Qed.

Theorem hiA_free0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (p n lo : Z) (errv : word) (u : JH.uwd) (g : ghost),
HEAPA0g g LB LM FR B m c ->
In (p, n) LB ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
OT.rw_cells segs m (HI.hl_tp HL - 164) [OC.C4 errv] ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 p ->
lo <= hi_top ->
JH.uw_cost u <= JH.bD B ->
(forall ms' m' c' g' (r : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc r m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (HI.lb_remove p LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m' ->
vmst (cfg_model c) (cfg_model c') ->
(forall x, F x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv] ->
HEAPA0g g' (HI.lb_remove p LB) LM FR (JH.charge B 0 (JH.uw_cost u) 0) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_free HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T LB LM FR B p n lo errv u g
HP Hin Hstk Hlo Hlo2 Herr Htp Hgp Ha0 Htop HbD HK.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
destruct L_stack as (Ls1 & Ls2 & Ls3).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Hsp64 : bv_unsigned sp <= 2^64) by (destruct Hstk as (_ & H & _); exact H).
rewrite ELB in Hin. apply in_map_iff in Hin as ([[pid A] nd] & Eb & Hbd). unfold blk_of in Eb. cbn [ablk_addr ablk_size fst snd] in Eb. injection Eb as -> ->.
pose proof (stk_join m lo (bv_unsigned sp) HSTK Hstk Hlo Hlo2 Htop) as Hstk0. pose proof (unw_readable0 m (bv_unsigned sp) HSTK ltac:(lia)) as Hur.
destruct HDN as (dn & HDn & HDcap). pose proof (zlen_nonneg0 _ LBd) as Hz0.
assert (Hstk' : stk segs (mrestrict F m) RC.alloc_ceiling (bv_unsigned sp)) by (apply stk_hide; [intros x Hx; apply F_above; lia| exact Hstk0]).
pose proof (dc_blocks_nodup _ _ _ _ DCo _ _ _ _ _ RUN) as NDid0.
assert (Hz1 : zlen LBd = 1 + zlen (alb_remove pid LBd)).
{ pose proof (Permutation_length (alb_remove_perm LBd pid p n NDid0 Hbd)) as EL. cbn [length] in EL. rewrite !length_map in EL. unfold zlen. lia. }
pose proof (zlen_nonneg0 _ (alb_remove pid LBd)) as Hz2.
destruct (ainv_q_nonneg _ _ AI) as [Qg0 Qt0].
assert (QR : qroom (ps_a ps) pid).
{ pose proof (zsum_map_perm (fun q => aptr_used q + kBatchBytes) _ _ (alb_remove_perm LBd pid p n NDid0 Hbd)) as EP.
cbn [map] in EP. rewrite zsum_cons in EP. pose proof (qliveX_nonneg (map ablk_id (alb_remove pid LBd))) as Hq0.
unfold QBA, qtot, qliveX, qroom in *. unfold kBatchBytes in *. lia. }
pose proof (dc_free _ _ _ _ DCo LA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
Fr fc (mrestrict F m) ps LBd FSd RE pid p n RC.alloc_ceiling dn RE_L RUN Hbd QR Hstk' (Z.le_refl _) ltac:(lia) (mem_inv_hide segs F m MI)
ltac:(rewrite <- L_tp; exact Htp) ltac:(rewrite <- L_gp; exact Hgp) Hur HDn ltac:(lia) Ha0) as Himpl.
rewrite <- L_free in Himpl.
match goal with |- AJv _ _ _ _ ?st => set (msv := st) end.
match type of Himpl with implMG _ _ _ _ _ ?st => change st with (restrict F msv) in Himpl end.
set (X := map ablk_id LBd) in *.
pose proof (dc_blocks_nodup _ _ _ _ DCo _ _ _ _ _ RUN) as NDid.
assert (Hdj : forall b1 b2, In b1 LBd -> In b2 LBd -> ablk_id b1 <> ablk_id b2 -> ablk_addr b1 <> ablk_addr b2).
{ intros b1 b2 H1 H2 Hne. pose proof (dc_blocks_disjoint _ _ _ _ DCo _ _ _ _ _ b1 b2 RUN H1 H2 Hne). lia. }
assert (HlenX : zlen X <= kCapN) by (unfold X, zlen in *; rewrite length_map; lia).
pose proof (cap_ok_of_len X HlenX) as Hcapok.
unfold AJv.
apply (afree_vj_Fq segs LA LV BUDGET PERM TOT0 N0 LL Hwx Hsegs Hsh Hbx Hbc FRl HFR F_off T X (map ablk_id (alb_remove pid LBd)) pid g ps _ c msv Himpl HC
AI (alb_remove_perm LBd pid p n NDid Hbd) (cap_ok_room24 X _ AI Hcapok) G ltac:(lia) K Qg0 Qt0 QR).
intros ps' c1 msv1 HQ (a' & g' & Eps & Hvo & K' & G' & Hsp' & AI' & HQT) HC1 Hh1 Hvm HF1.
apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply (evt_restrict_lift segs F F_off Hwx) in HQ. eapply evt_mono; [exact HQ|]. clear HQ.
intros ms'' [HPo Hhs].
destruct HPo as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & Ems & MI1 & Hstk1 & Hpres & _ & _ & [(dn' & HDn' & Hdn') [EK RUN1]]).
destruct (restrict_MS_inv F ms'' _ _ _ _ _ _ _ Ems) as [Ems'' Em1]. set (m'' := ms_mem ms'') in *.
subst m1'.
assert (HPRES : HI.heap_pres HL (HI.lb_remove p LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m'' /\
(forall a, HI.hl_tp HL - 164 <= a < HI.hl_tp HL - 160 -> 0 <= a < 2^64 ->
m'' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m'' (wa a) <> None))).
{ assert (Hgen : forall a, 0 <= a < 2^64 ->
(F (wa a) = false -> aclient_addrA RC.alloc_ceiling DL (alb_remove pid LBd) FSd (bv_unsigned sp) a) ->
m'' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m'' (wa a) <> None)).
{ intros a Ha Hcl. destruct (F (wa a)) eqn:Fa.
- assert (E : m'' (wa a) = m (wa a)) by (unfold m''; rewrite (Hhs _ Fa); exact (HF1 _ Fa)).
split; [exact E|]. unfold wview. rewrite E. auto.
- destruct (Hpres a Ha (Hcl eq_refl)) as [E W]. rewrite (mrestrict_off F m'' _ Fa), (mrestrict_off F m _ Fa) in E.
split; [exact E|]. rewrite !(wview_off _ _ Fa) in W. exact W. }
split.
- intros a Ha Hcl. change (OM.wa a) with (wa a). apply (Hgen a Ha). intros Fa.
destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
+ right; right; left. apply in_block_map. rewrite (alb_remove_map LBd pid p n NDid Hdj Hbd), <- ELB. exists b. auto.
+ apply in_app_iff in Hb as [Hb|Hb].
* exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa. discriminate.
* rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H].
- intros a Ha Ha64.
assert (Fa : F (wa a) = false).
{ destruct (dc_errno _ _ _ _ DCo _ _ _ _ _ RUN) as [ev0 [_ Hev]]. rewrite L_errno in Hev. change (Z.of_nat (cells_size [C4 ev0])) with 4 in Hev.
apply (wr_at_hidden_off m _ _ Hev a). lia. }
destruct (EK a Ha64 ltac:(rewrite L_errno; lia)) as [E W]. rewrite (mrestrict_off F m'' _ Fa), (mrestrict_off F m _ Fa) in E.
split; [exact E|]. rewrite !(wview_off _ _ Fa) in W. exact W. }
destruct HPRES as [HPR HERR].
assert (HFm0 : forall x, F x = true -> m'' x = m x) by (intros x Fx; unfold m''; rewrite (Hhs _ Fx); exact (HF1 _ Fx)).
pose proof (gen_pres (alb_remove pid LBd) FSd _ m m'' Hpres HFm0) as Hgen0.
apply (HK ms'' m'' c1 g' a0').
- unfold HI.ret_state. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. exact Ems''.
- destruct Hvo as (V1 & V2 & V3 & V4 & V5 & V6). unfold HI.model_vm_only. repeat split; try assumption. exact (vmst_init_sp _ _ Hvm).
- exact (stk_sub0 m'' _ lo _ (stk_unhide segs F F_off m'' _ _ Hstk1) Hlo).
- exact HPR.
- exact Hvm.
- exact HFm0.
- intros a Ha Hcd. apply (Hgen0 a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd).
-
unfold OT.rw_cells, OC.cells_at, OM.bytes_at, OM.wr_at in Herr |- *.
destruct Herr as [[Hwf (B0 & B1 & HBy)] (W0 & W1 & HW)]. cbn [OC.cells_size OC.csize Nat.add] in *.
assert (Hlen : length (OC.cells_bytes [OC.C4 errv]) = 4%nat) by (cbn [OC.cells_bytes OC.cbytes app]; rewrite app_nil_r; apply length_Z_to_le_bytes).
split; [split; [exact Hwf|]|].
+ split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (HBy i Hi). rewrite Hlen in Hi, B1.
destruct (HERR (HI.hl_tp HL - 164 + Z.of_nat i) ltac:(lia) ltac:(lia)) as [E _]. unfold OM.mrd.
change (OM.wa (HI.hl_tp HL - 164 + Z.of_nat i)) with (wa (HI.hl_tp HL - 164 + Z.of_nat i)). rewrite E. reflexivity.
+ split; [exact W0|]. split; [exact W1|]. intros i Hi. change (Z.of_nat 4) with 4 in *.
destruct (HERR (HI.hl_tp HL - 164 + i) ltac:(lia) ltac:(lia)) as [_ W]. apply W. exact (HW i Hi).
- exists ps', (alb_remove pid LBd), FSd.
assert (Ea : ps_a ps' = a') by (rewrite Eps; reflexivity).
split; [exact RUN1|]. split; [rewrite (alb_remove_map LBd pid p n NDid Hdj Hbd), <- ELB; reflexivity|].
split; [exact EFR|]. split; [rewrite Ea; exact AI'|]. split; [rewrite Ea; exact G'|].
split; [cbn [JH.charge JH.bN]; pose proof (zlen_alb_remove LBd pid); lia|].
split; [rewrite Ea; cbn [JH.charge JH.bB]; lia|].
split; [exact K'|]. split; [exact HC1|]. split; [exact Hh1|]. split; [exact (mem_inv_unhide m'' MI1)|].
split.
{ apply (wr_keep (alb_remove pid LBd) FSd _ m m'' (alb_remove pid LBd) Hgen0 (fun b H => H)).
apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) HWR). exact (alb_remove_In LBd pid b Hb). }
split; [exact HLM|]. cbn [JH.charge JH.bB JH.bD JH.bN]. split; [lia|]. split; [lia|]. split; [lia|].

split; [exists dn'; split; [exact HDn'| cbn [JH.charge JH.bN]; lia]|]. split; [exact (stk_after m m'' (bv_unsigned sp) HSTK (stk_unhide segs F F_off m'' _ _ Hstk1) (fun a Ha Hsp => proj1 (Hgen0 a Ha (fun _ => or_introl Hsp))))|].
unfold QBA in *. rewrite Ea. pose proof (zsum_map_perm (fun q => aptr_used q + kBatchBytes) _ _ (alb_remove_perm LBd pid p n NDid Hbd)) as EP.
cbn [map] in EP. rewrite zsum_cons in EP. unfold qliveX in *. cbn [JH.charge JH.bQ]. lia.
Qed.

Theorem hiA_free_null0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (lo : Z) (errv : word) (u : JH.uwd) (g : ghost),
HEAPA0g g LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
OT.rw_cells segs m (HI.hl_tp HL - 164) [OC.C4 errv] ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 0 ->
lo <= hi_top ->
(forall ms' m' (r : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc r m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m' ->
(forall x, F x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv] ->
HEAPA0g g LB LM FR (JH.charge B 0 0 0) m' c ->
AJv segs LV T c ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_free HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T LB LM FR B lo errv u g
HP Hstk Hlo Hlo2 Herr Htp Hgp Ha0 Htop HK.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
destruct L_stack as (Ls1 & Ls2 & Ls3).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Hsp64 : bv_unsigned sp <= 2^64) by (destruct Hstk as (_ & H & _); exact H).
pose proof (stk_join m lo (bv_unsigned sp) HSTK Hstk Hlo Hlo2 Htop) as Hstk0. pose proof (unw_readable0 m (bv_unsigned sp) HSTK ltac:(lia)) as Hur.
destruct HDN as (dn & HDn & HDcap). pose proof (zlen_nonneg0 _ LBd) as Hz0.
assert (Hstk' : stk segs (mrestrict F m) RC.alloc_ceiling (bv_unsigned sp)) by (apply stk_hide; [intros x Hx; apply F_above; lia| exact Hstk0]).
pose proof (dc_free_null _ _ _ _ DCo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
Fr fc (mrestrict F m) ps LBd FSd RE RC.alloc_ceiling RUN Hstk' (Z.le_refl _) ltac:(lia) (mem_inv_hide segs F m MI)
ltac:(rewrite <- L_tp; exact Htp) ltac:(rewrite <- L_gp; exact Hgp) Hur Ha0) as Hevt.
rewrite <- L_free in Hevt.
match goal with |- AJv _ _ _ _ ?st => set (msv := st) end.
match type of Hevt with evt _ _ ?st => change st with (restrict F msv) in Hevt end.
unfold AJv. apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply (evt_restrict_lift segs F F_off Hwx) in Hevt. eapply evt_mono; [exact Hevt|]. clear Hevt.
intros ms'' [HPo Hhs].
destruct HPo as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & Ems & MI1 & Hstk1 & Hpres & _ & _ & [HDK [EK RUN1]]).
destruct (restrict_MS_inv F ms'' _ _ _ _ _ _ _ Ems) as [Ems'' Em1]. set (m'' := ms_mem ms'') in *.
subst m1'.
assert (Hgen : forall a, 0 <= a < 2^64 ->
(F (wa a) = false -> aclient_addrA RC.alloc_ceiling DL LBd FSd (bv_unsigned sp) a) ->
m'' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m'' (wa a) <> None)).
{ intros a Ha Hcl. destruct (F (wa a)) eqn:Fa.
- assert (E : m'' (wa a) = m (wa a)) by (unfold m''; exact (Hhs _ Fa)).
split; [exact E|]. unfold wview. rewrite E. auto.
- destruct (Hpres a Ha (Hcl eq_refl)) as [E W]. rewrite (mrestrict_off F m'' _ Fa), (mrestrict_off F m _ Fa) in E.
split; [exact E|]. rewrite !(wview_off _ _ Fa) in W. exact W. }
apply (HK ms'' m'' a0').
- unfold HI.ret_state. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. exact Ems''.
- exact (stk_sub0 m'' _ lo _ (stk_unhide segs F F_off m'' _ _ Hstk1) Hlo).
- intros a Ha Hcl. change (OM.wa a) with (wa a). apply (Hgen a Ha). intros Fa.
destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
+ right; right; left. apply in_block_map. rewrite <- ELB. exists b. auto.
+ apply in_app_iff in Hb as [Hb|Hb].
* exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa. discriminate.
* rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H].
- intros x Fx. unfold m''. exact (Hhs x Fx).
- intros a Ha Hcd. apply (Hgen a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd).
- unfold OT.rw_cells, OC.cells_at, OM.bytes_at, OM.wr_at in Herr |- *.
destruct Herr as [[Hwf (B0 & B1 & HBy)] (W0 & W1 & HW)]. cbn [OC.cells_size OC.csize Nat.add] in *.
assert (Hlen : length (OC.cells_bytes [OC.C4 errv]) = 4%nat) by (cbn [OC.cells_bytes OC.cbytes app]; rewrite app_nil_r; apply length_Z_to_le_bytes).
assert (HERR : forall a, HI.hl_tp HL - 164 <= a < HI.hl_tp HL - 160 -> 0 <= a < 2^64 ->
m'' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m'' (wa a) <> None)).
{ intros a Ha Ha64.
assert (Fa : F (wa a) = false).
{ destruct (dc_errno _ _ _ _ DCo _ _ _ _ _ RUN) as [ev0 [_ Hev]]. rewrite L_errno in Hev. change (Z.of_nat (cells_size [C4 ev0])) with 4 in Hev.
apply (wr_at_hidden_off m _ _ Hev a). lia. }
destruct (EK a Ha64 ltac:(rewrite L_errno; lia)) as [E W]. rewrite (mrestrict_off F m'' _ Fa), (mrestrict_off F m _ Fa) in E.
split; [exact E|]. rewrite !(wview_off _ _ Fa) in W. exact W. }
split; [split; [exact Hwf|]|].
+ split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (HBy i Hi). rewrite Hlen in Hi, B1.
destruct (HERR (HI.hl_tp HL - 164 + Z.of_nat i) ltac:(lia) ltac:(lia)) as [E _]. unfold OM.mrd.
change (OM.wa (HI.hl_tp HL - 164 + Z.of_nat i)) with (wa (HI.hl_tp HL - 164 + Z.of_nat i)). rewrite E. reflexivity.
+ split; [exact W0|]. split; [exact W1|]. intros i Hi. change (Z.of_nat 4) with 4 in *.
destruct (HERR (HI.hl_tp HL - 164 + i) ltac:(lia) ltac:(lia)) as [_ W]. apply W. exact (HW i Hi).
- exists ps, LBd, FSd.
split; [exact RUN1|]. split; [exact ELB|]. split; [exact EFR|]. split; [exact AI|]. split; [exact G|].
split; [cbn [JH.charge JH.bN]; lia|]. split; [cbn [JH.charge JH.bB]; lia|].
split; [exact K|]. split; [exact HC|]. split; [exact Hh|]. split; [exact (mem_inv_unhide m'' MI1)|].
split; [exact (wr_keep LBd FSd _ m m'' LBd Hgen (fun b H => H) HWR)|].
split; [exact HLM|]. cbn [JH.charge JH.bB JH.bD JH.bN]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exists dn; split; [exact (HDK dn HDn)| cbn [JH.charge JH.bN]; lia]|]. split; [exact (stk_after m m'' (bv_unsigned sp) HSTK (stk_unhide segs F F_off m'' _ _ Hstk1) (fun a Ha Hsp => proj1 (Hgen a Ha (fun _ => or_introl Hsp))))|]. unfold QBA in *. cbn [JH.charge JH.bQ]. lia.
Qed.

Hypothesis L_img : HI.hl_img_lo HL = dl_img_lo DL /\ HI.hl_img_hi HL = dl_img_hi DL.

Lemma heapA0_cok : forall LB LM FR B m c, HEAPA0 LB LM FR B m c -> CKv LV c.
Proof. intros LB LM FR B m c (g & ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & _ & HC & Hh & _). split; assumption. Qed.

Lemma heapA0_mem_inv : forall LB LM FR B m c, HEAPA0 LB LM FR B m c -> mem_inv segs m.
Proof. intros LB LM FR B m c (g & ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _). exact MI. Qed.

Lemma heapA0_budget : forall LB LM FR B m c, HEAPA0 LB LM FR B m c -> 0 <= JH.bB B /\ 0 <= JH.bD B /\ 0 <= JH.bN B.
Proof. intros LB LM FR B m c (g & ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _). auto. Qed.

Lemma heapA0_blk_in : forall LB LM FR B m c a n, HEAPA0 LB LM FR B m c -> In (a, n) LB ->
exists ps LBd FSd pid, dc_run _ _ _ _ DCo ps LBd FSd RE (mrestrict F m) /\ LB = map blk_of LBd /\ In (pid, a, n) LBd /\
wr_at segs m a n.
Proof.
intros LB LM FR B m c a n (g & ps & LBd & FSd & RUN & ELB & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWR & _) Hin.
rewrite ELB in Hin. apply in_map_iff in Hin as ([[pid A] nd] & Eb & Hbd). unfold blk_of in Eb. cbn [ablk_addr ablk_size fst snd] in Eb. injection Eb as -> ->.
exists ps, LBd, FSd, pid. split; [exact RUN|]. split; [exact ELB|]. split; [exact Hbd|].
exact (proj1 (proj1 (Forall_forall _ _) HWR _ Hbd)).
Qed.

Lemma heapA0_blk : forall LB LM FR B m c a n, HEAPA0 LB LM FR B m c -> In (a, n) LB ->
0 <= n /\ a mod 16 = 0 /\ 0 < a /\ a + n <= RC.alloc_ceiling /\ wr_at segs m a n.
Proof.
intros LB LM FR B m c a n HP Hin. destruct (heapA0_blk_in _ _ _ _ _ _ a n HP Hin) as (ps & LBd & FSd & pid & RUN & _ & Hbd & HW).
destruct (dc_block_range _ _ _ _ DCo _ _ _ _ _ _ RUN Hbd) as (((Hlh & _) & _) & R2 & R3 & R4 & _). cbn [ablk_addr ablk_size fst snd] in *.
split; [exact R3|]. split; [exact R2|]. split; [destruct Hlh as [[H _]|H]; [exact H| unfold KHI, Qqcs.Mq0.kHighMemBeg in H; lia]|].
split; [exact R4| exact HW].
Qed.

Lemma heapA0_blk_le26 : forall LB LM FR B m c a n, HEAPA0 LB LM FR B m c -> In (a, n) LB -> n <= 2^26.
Proof.
intros LB LM FR B m c a n HP Hin. destruct (heapA0_blk_in _ _ _ _ _ _ a n HP Hin) as (ps & LBd & FSd & pid & RUN & _ & Hbd & _).
exact (dc_block_small _ _ _ _ DCo _ _ _ _ _ _ RUN Hbd).
Qed.

Lemma heapA0_blk_img : forall LB LM FR B m c a n, HEAPA0 LB LM FR B m c -> In (a, n) LB ->
a + n <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= a.
Proof.
intros LB LM FR B m c a n HP Hin. destruct (heapA0_blk_in _ _ _ _ _ _ a n HP Hin) as (ps & LBd & FSd & pid & RUN & _ & Hbd & _).
destruct (dc_block_range _ _ _ _ DCo _ _ _ _ _ _ RUN Hbd) as (((_ & Hoff) & _) & _). cbn [ablk_addr ablk_size fst snd] in *.
destruct L_img as [-> ->]. exact Hoff.
Qed.

Lemma heapA0_blk_disjoint : forall LB LM FR B m c a n a' n', HEAPA0 LB LM FR B m c ->
In (a, n) LB -> In (a', n') LB -> a <> a' -> a + n <= a' \/ a' + n' <= a.
Proof.
intros LB LM FR B m c a n a' n' (g & ps & LBd & FSd & RUN & ELB & _) H1 H2 Hne.
rewrite ELB in H1, H2. apply in_map_iff in H1 as ([[p1 A1] N1] & E1 & Hb1). apply in_map_iff in H2 as ([[p2 A2] N2] & E2 & Hb2).
unfold blk_of in E1, E2. cbn [ablk_addr ablk_size fst snd] in E1, E2. injection E1 as -> ->. injection E2 as -> ->.
assert (Hid : ablk_id (p1, a, n) <> ablk_id (p2, a', n')).
{ cbn [ablk_id fst]. intros ->. apply Hne.
pose proof (dc_blocks_nodup _ _ _ _ DCo _ _ _ _ _ RUN) as ND.
clear - ND Hb1 Hb2. induction LBd as [|bd LBd IH]; [destruct Hb1|]. cbn [map] in ND. inversion ND as [|x l Hnin ND']; subst.
destruct Hb1 as [E1|Hb1]; destruct Hb2 as [E2|Hb2].
- rewrite E1 in E2. injection E2 as ->. reflexivity.
- exfalso. apply Hnin. subst bd. cbn [ablk_id fst]. apply in_map_iff. exists (p2, a', n'). split; [reflexivity| exact Hb2].
- exfalso. apply Hnin. subst bd. cbn [ablk_id fst]. apply in_map_iff. exists (p2, a, n). split; [reflexivity| exact Hb1].
- exact (IH Hb1 Hb2 ND'). }
pose proof (dc_blocks_disjoint _ _ _ _ DCo _ _ _ _ _ _ _ RUN Hb1 Hb2 Hid) as D. cbn [ablk_addr ablk_size fst snd] in D. lia.
Qed.

Lemma heapA0_blk_nodup : forall LB LM FR B m c, HEAPA0 LB LM FR B m c -> List.NoDup (map HI.blk_addr LB).
Proof.
intros LB LM FR B m c (g & ps & LBd & FSd & RUN & ELB & _). subst LB.
pose proof (dc_blocks_nodup _ _ _ _ DCo _ _ _ _ _ RUN) as ND.
assert (Hdj : forall b1 b2, In b1 LBd -> In b2 LBd -> ablk_id b1 <> ablk_id b2 -> ablk_addr b1 <> ablk_addr b2).
{ intros b1 b2 H1 H2 Hne. pose proof (dc_blocks_disjoint _ _ _ _ DCo _ _ _ _ _ b1 b2 RUN H1 H2 Hne). lia. }
clear RUN. induction LBd as [|bd LBd IH]; [constructor|]. cbn [map] in *. inversion ND as [|x l Hnin ND']; subst.
constructor; [| apply IH; [exact ND'| intros b1 b2 H1 H2; apply Hdj; right; assumption]].
intros Hin. apply in_map_iff in Hin as (b' & Eb & Hb'). apply in_map_iff in Hb' as (bd' & <- & Hbd').
unfold HI.blk_addr, blk_of in Eb. cbn [fst] in Eb.
apply (Hdj bd' bd (or_intror Hbd') (or_introl eq_refl)); [| exact Eb].
intros Eid. apply Hnin. rewrite <- Eid. apply in_map. exact Hbd'.
Qed.

Lemma bytes_at_singles : forall m a (bs : list byte) d, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(forall i, (i < length bs)%nat -> bytes_at segs m (a + Z.of_nat i) [nth i bs d]) -> bytes_at segs m a bs.
Proof.
intros m a bs d Ha Hl H. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
destruct (H i Hi) as (_ & _ & H1). specialize (H1 0%nat ltac:(cbn; lia)). cbn [nth_error] in H1.
rewrite Z.add_0_r in H1. rewrite H1. symmetry. apply nth_error_nth'. exact Hi.
Qed.

Lemma heapA0_shadow_blk : forall LB LM FR B m c a n, HEAPA0 LB LM FR B m c -> In (a, n) LB ->
bytes_at segs m (JH.shad L a) (JH.shadow_bytes n).
Proof.
intros LB LM FR B m c a n HP Hin. destruct (heapA0_blk_in _ _ _ _ _ _ a n HP Hin) as (ps & LBd & FSd & pid & RUN & _ & Hbd & _).
pose proof (dc_block_shadow _ _ _ _ DCo _ _ _ _ _ _ _ _ RUN Hbd) as (S0 & S1 & S2 & S3 & SB).
unfold JH.shad. rewrite L_sb. fold (SH a).
assert (Hq : 0 <= n / 8) by (apply Z.div_pos; lia).
assert (Hlen : Z.of_nat (length (JH.shadow_bytes n)) = n / 8 + (if n mod 8 =? 0 then 0 else 1)).
{ unfold JH.shadow_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, Z2Nat.id by lia. destruct (n mod 8 =? 0); reflexivity. }
assert (Hsh0 : 0 <= SH a) by (unfold SH, kShadowOffset; pose proof (Z.div_pos a 8 S0 ltac:(lia)); lia).
assert (Hle : n / 8 + (if n mod 8 =? 0 then 0 else 1) <= (n + 7) / 8).
{ pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mb.
destruct (Z.eqb_spec (n mod 8) 0); [rewrite Z.add_0_r; apply Z.div_le_mono; lia|].
apply Z.div_le_lower_bound; lia. }
apply (bytes_at_singles m (SH a) _ (Z_to_bv 8 0)); [exact Hsh0| unfold KHI, Qqcs.Mq0.kHighMemBeg in S3; lia|].
intros i Hi. assert (Hi' : Z.of_nat i < n / 8 + (if n mod 8 =? 0 then 0 else 1)) by lia.
pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mb.
assert (Hk : 8 * Z.of_nat i < n) by (destruct (Z.eqb_spec (n mod 8) 0); lia).
apply (bytes_at_unhide segs F F_off). pose proof (SB (Z.of_nat i) ltac:(lia) Hk) as Hb.
replace (nth i (JH.shadow_bytes n) (Z_to_bv 8 0)) with (Z_to_bv 8 (gran n (Z.of_nat i))); [exact Hb|].
unfold JH.shadow_bytes, gran. destruct (Z.lt_ge_cases (Z.of_nat i) (n / 8)) as [Hlt|Hge].
- rewrite app_nth1 by (rewrite repeat_length; lia). rewrite nth_repeat.
destruct (Z.leb_spec (8 * Z.of_nat i + 8) n); [reflexivity| lia].
- assert (Ei : Z.of_nat i = n / 8) by (destruct (Z.eqb_spec (n mod 8) 0); lia).
rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
replace (i - Z.to_nat (n / 8))%nat with 0%nat by lia.
destruct (Z.eqb_spec (n mod 8) 0) as [E0|E0]; [lia|]. cbn [nth].
destruct (Z.leb_spec (8 * Z.of_nat i + 8) n); [lia|]. f_equal. lia.
Qed.

Variable SIVS : list (Z * Z).
Hypothesis L_sivs_cover : forall a, HI.hl_client_static HL a -> exists iv, In iv SIVS /\ fst iv <= a < snd iv.
Hypothesis L_sivs_data : forall iv a, In iv SIVS -> fst iv <= a < snd iv -> dl_client_data DL a.
Hypothesis L_scratch : forall a, HI.hl_scratch HL a -> HI.hl_tp HL - 164 <= a < HI.hl_tp HL - 160.
Hypothesis IMG_errno_any : forall m : word -> option byte, exists v : word, rw_cells segs m (HI.hl_tp HL - 164) [C4 v].

Definition frameW (LBd : list ablock) (FSd : list fframe) : list (Z * Z) :=
(RC.alloc_ceiling, 2^64) :: SIVS
++ map (fun b => (ablk_addr b, ablk_addr b + ablk_size b)) LBd
++ flat_map (fun f => [(ff_addr f, ff_addr f + ff_size (ff_cls f) - 8); (SH (ff_addr f), SH (ff_addr f) + ff_size (ff_cls f) / 8)]) FSd.

Lemma outside_In : forall W x, (forall iv, In iv W -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
induction W as [|[lo hi] W IH]; intros x H; cbn [outside]; [exact I|]. split.
- specialize (H (lo, hi) (or_introl eq_refl)). cbn [fst snd] in H. lia.
- apply IH. intros iv Hiv. apply H. right. exact Hiv.
Qed.

Lemma outside_not_In : forall W x iv, outside W x -> In iv W -> ~ (fst iv <= x < snd iv).
Proof.
induction W as [|[lo hi] W IH]; intros x iv Ho Hin; [destruct Hin|]. cbn [outside] in Ho. destruct Ho as [H1 H2].
destruct Hin as [<-|Hin]; [cbn [fst snd]; lia| exact (IH x iv H2 Hin)].
Qed.

Definition in_errno (x : word) : bool := (HI.hl_tp HL - 164 <=? bv_unsigned x) && (bv_unsigned x <? HI.hl_tp HL - 160).
Definition merrno (m m' : word -> option byte) : word -> option byte := fun x => if in_errno x then m x else m' x.

Lemma heapA0g_client_frame : forall g LB LM FR B m m' c, HEAPA0g g LB LM FR B m c ->
(forall a, 0 <= a < 2^64 ->
~ HI.client_addr HL (LB ++ LM) RC.alloc_ceiling a -> ~ HI.hl_scratch HL a ->
~ (exists Fa k, In (Fa, k) FR /\ (Fa <= a < Fa + JH.fr_size k - 8 \/ JH.shad L Fa <= a < JH.shad L Fa + JH.fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
mem_inv segs m' ->
depot_keep segs DL (mrestrict F m) (mrestrict F m') -> stk segs m' RC.alloc_ceiling hi_top ->
HEAPA0g g LB LM FR B m' c.
Proof.
intros g LB LM FR B m m' c (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb) Hsame Hwm MI' HDK' HSTK'.
exists ps, LBd, FSd.
split.
{
destruct (IMG_errno_any (mrestrict F m')) as [v Hv]. rewrite <- L_errno in Hv.
apply (dc_errno_frame _ _ _ _ DCo ps LBd FSd RE (mrestrict F (merrno m m')) (mrestrict F m') v); [| | | exact Hv].
-
apply (dc_run_frame _ _ _ _ DCo ps LBd FSd RE (mrestrict F m) (mrestrict F (merrno m m')) (frameW LBd FSd) RUN).
+
intros x Hout. unfold mrestrict, merrno. destruct (F x) eqn:Fx; [reflexivity|]. destruct (in_errno x) eqn:Ex; [reflexivity|].
pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64) with (2^64) in Hx.
assert (Exx : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
rewrite <- Exx. apply Hsame; [lia| | |].
* intros [H|[H|H]].
-- exact (outside_not_In _ _ (RC.alloc_ceiling, 2^64) Hout (or_introl eq_refl) ltac:(cbn [fst snd]; lia)).
-- destruct (L_sivs_cover _ H) as (iv & Hiv & Hr).
exact (outside_not_In _ _ iv Hout ltac:(right; apply in_app_iff; left; exact Hiv) Hr).
-- destruct H as (b & Hb0 & Hr). apply in_app_iff in Hb0 as [Hb0|Hb0].
++ rewrite ELB in Hb0. apply in_map_iff in Hb0 as (bd & <- & Hbd).
apply (outside_not_In _ _ (ablk_addr bd, ablk_addr bd + ablk_size bd) Hout); [| exact Hr].
right. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists bd. auto.
++ destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite <- Exx, (HLM ba bn _ Hb0 Hr) in Fx. discriminate.
* intros Hs. pose proof (L_scratch _ Hs) as Hr. unfold in_errno in Ex. apply andb_false_iff in Ex as [Ex|Ex]; [apply Z.leb_gt in Ex| apply Z.ltb_ge in Ex]; lia.
* intros (Fa & k & Hfk & Hr). rewrite EFR in Hfk. apply in_map_iff in Hfk as (fd & Efd & Hfd).
unfold fr_of in Efd. injection Efd as <- <-.
assert (Hin2 : forall iv, In iv [(ff_addr fd, ff_addr fd + ff_size (ff_cls fd) - 8); (SH (ff_addr fd), SH (ff_addr fd) + ff_size (ff_cls fd) / 8)] -> In iv (frameW LBd FSd)).
{ intros iv Hiv. right. apply in_app_iff. right. apply in_app_iff. right. apply in_flat_map. exists fd. auto. }
unfold JH.fr_size, JH.shad, JH.fr_shadow_len in Hr. rewrite L_sb in Hr. fold (SH (ff_addr fd)) in Hr.
assert (E8 : ff_size (ff_cls fd) / 8 = 8 * 2 ^ ff_cls fd).
{ unfold ff_size. replace (64 * 2 ^ ff_cls fd) with (8 * 2 ^ ff_cls fd * 8) by lia. apply Z.div_mul. lia. }
destruct Hr as [Hr|Hr].
-- apply (outside_not_In _ _ _ Hout (Hin2 _ (or_introl eq_refl))). cbn [fst snd]. unfold ff_size. lia.
-- apply (outside_not_In _ _ _ Hout (Hin2 _ (or_intror (or_introl eq_refl)))). cbn [fst snd]. rewrite E8. lia.
+
intros x Hx. destruct (F x) eqn:Fx.
* exfalso. apply Hx. unfold wview, mrestrict. rewrite Fx, (F_off x Fx). reflexivity.
* rewrite (wview_off m x Fx) in Hx. rewrite (wview_off (merrno m m') x Fx). unfold wview, merrno.
destruct (in_errno x); [exact Hx| exact (Hwm x Hx)].
+
unfold frameW. constructor; [left; cbn [fst]; lia|].
apply Forall_app. split; [apply Forall_forall; intros iv Hiv; right; left; intros a Ha; exact (L_sivs_data iv a Hiv Ha)|].
apply Forall_app. split.
* apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (bd & <- & Hbd). do 2 right; left. exists bd. split; [exact Hbd| cbn [fst snd]; lia].
* apply Forall_forall. intros iv Hiv. apply in_flat_map in Hiv as (fd & Hfd & Hiv). destruct Hiv as [<-|[<-|[]]]; cbn [fst snd].
-- do 3 right; left. exists fd. split; [exact Hfd| cbn [fst snd]; lia].
-- do 4 right; left. exists fd. split; [exact Hfd| cbn [fst snd]; lia].
-
intros x Hout. unfold mrestrict, merrno. destruct (F x); [reflexivity|]. destruct (in_errno x) eqn:Ex; [| reflexivity].
exfalso. unfold in_errno in Ex. apply andb_true_iff in Ex as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
cbn [outside] in Hout. rewrite L_errno in Hout. lia.
-
intros x Hx. destruct (F x) eqn:Fx.
+ exfalso. apply Hx. unfold wview, mrestrict. rewrite Fx, (F_off x Fx). reflexivity.
+ rewrite (wview_off (merrno m m') x Fx) in Hx. rewrite (wview_off m' x Fx). unfold wview, merrno in Hx.
destruct (in_errno x); [exact (Hwm x Hx)| exact Hx]. }
split; [exact ELB|]. split; [exact EFR|]. split; [exact AI|]. split; [exact G|]. split; [exact Hcap|]. split; [exact Hbud|].
split; [exact K|]. split; [exact HC|]. split; [exact Hh|]. split; [exact MI'|].
split.
{ apply Forall_forall. intros b Hb0. destruct (proj1 (Forall_forall _ _) HWR b Hb0) as ((W0 & W1 & HWb) & HFb).
split; [| exact HFb]. split; [exact W0|]. split; [exact W1|]. intros i Hi. apply Hwm. exact (HWb i Hi). }
split; [exact HLM|]. destruct Hb as (Hb1 & Hb2 & Hb3 & (dn & HDn & HDcap) & _ & HQ). split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb3|].
split; [exists dn; split; [exact (HDK' dn HDn)| exact HDcap]|]. split; [exact HSTK'| exact HQ].
Qed.

Lemma heapA0g_cfg_next : forall g LB LM FR B m c c', HEAPA0g g LB LM FR B m c -> CNEXTv LV c c' -> HEAPA0g g LB LM FR B m c'.
Proof.
intros g LB LM FR B m c c' (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & Rest) HN.
exists ps, LBd, FSd. pose proof HN as [[HC' Hh'] _].
split; [exact RUN|]. split; [exact ELB|]. split; [exact EFR|]. split; [exact AI|]. split; [exact G|]. split; [exact Hcap|].
split; [exact Hbud|]. split; [exact (KI_cnext LV BUDGET PERM TOT0 N0 g c c' HN K)|]. split; [exact HC'|]. split; [exact Hh'| exact Rest].
Qed.

Lemma heapA0g_perm_lm_fr : forall g LB LM LM' FR FR' B m c, HEAPA0g g LB LM FR B m c ->
Permutation LM LM' -> Permutation FR FR' -> HEAPA0g g LB LM' FR' B m c.
Proof.
intros g LB LM LM' FR FR' B m c (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb) P2 P3.
subst FR. apply Permutation_sym in P3. destruct (Permutation_map_inv _ _ P3) as (FSd' & -> & HPf).
exists ps, LBd, FSd'.
split; [exact (dc_run_perm _ _ _ _ DCo _ _ _ _ _ _ _ RUN (Permutation_refl _) HPf)|]. split; [exact ELB|]. split; [reflexivity|].
split; [exact AI|]. split; [exact G|]. split; [exact Hcap|]. split; [exact Hbud|]. split; [exact K|]. split; [exact HC|].
split; [exact Hh|]. split; [exact MI|]. split; [exact HWR|]. split; [| exact Hb].
intros a n x Hin. apply (HLM a n x). eapply Permutation_in; [apply Permutation_sym; exact P2| exact Hin].
Qed.

Lemma heapA0g_perm_lb : forall g LB LB' LM FR B m c, HEAPA0g g LB LM FR B m c -> Permutation LB LB' -> HEAPA0g g LB' LM FR B m c.
Proof.
intros g LB LB' LM FR B m c (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb) HP.
subst LB. apply Permutation_sym in HP. destruct (Permutation_map_inv _ _ HP) as (LBd' & -> & HPd).
exists ps, LBd', FSd.
split; [exact (dc_run_perm _ _ _ _ DCo _ _ _ _ _ _ _ RUN HPd (Permutation_refl _))|]. split; [reflexivity|]. split; [exact EFR|].
split.
{ destruct AI as [AIx QB]. split; [| exact QB]. eapply ainvx_perm; [| exact AIx]. rewrite !app_nil_r. apply Permutation_map. exact HPd. }
split; [exact G|]. split; [unfold zlen in *; rewrite <- (Permutation_length HPd); exact Hcap|].
split; [exact Hbud|]. split; [exact K|]. split; [exact HC|]. split; [exact Hh|]. split; [exact MI|].
split; [exact (Permutation_Forall HPd HWR)|]. split; [exact HLM|].
destruct Hb as (Hb1 & Hb2 & Hb3 & (dn & HDn & HDcap) & HSTK & HQ). split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb3|].
split; [exists dn; split; [exact HDn| unfold zlen in *; rewrite <- (Permutation_length HPd); exact HDcap]|]. split; [exact HSTK|].
unfold QBA, qliveX in *. rewrite <- (zsum_map_perm (fun q => aptr_used q + kBatchBytes) _ _ (Permutation_map ablk_id HPd)). exact HQ.
Qed.

Variable SM : Z -> Z.
Variable SM_stack : Z.
Hypothesis DFs : donor_fs RC.alloc_ceiling segs (at_nodeA LV segs) DL DCo SM SM_stack.
Hypothesis L_sm : forall k, 0 <= k <= 3 -> JH.hl_stack_malloc L k = SM k.
Hypothesis L_sm_stack : SM_stack <= JH.hl_stack_A L.
Hypothesis L_dpn_hull : dl_img_lo DL <= dl_depot_n DL /\ dl_depot_n DL + 4 <= dl_img_hi DL.

Lemma bytes_at_det0 : forall m a bs bs', bytes_at segs m a bs -> bytes_at segs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
intros m a bs bs' (_ & _ & H) (_ & _ & H') E. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs)).
- rewrite <- H, <- H' by lia. reflexivity.
- rewrite (proj2 (nth_error_None bs i)), (proj2 (nth_error_None bs' i)) by lia. reflexivity.
Qed.
Lemma le8_inj0 : forall v w : word, le8 v = le8 w -> v = w.
Proof. intros v w E. rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), E. reflexivity. Qed.

Lemma in_fr_of : forall FSd Fa k, In (Fa, k) (map fr_of FSd) -> In (k, Fa) FSd.
Proof.
intros FSd Fa k H. apply in_map_iff in H as ([c0 f] & E & Hin). unfold fr_of, ff_addr, ff_cls in E. cbn [fst snd] in E. injection E as -> ->. exact Hin.
Qed.

Lemma wview_hidden_off : forall m x, wview segs (mrestrict F m) x <> None -> F x = false.
Proof.
intros m x H. destruct (F x) eqn:E; [|reflexivity]. exfalso. apply H. unfold wview, mrestrict. rewrite E, (F_off _ E). reflexivity.
Qed.

Lemma write1_spec : forall (m : word -> option byte) (a : word) b x, write_to_mem m a [b] x = if bv_eqb x a then Some b else m x.
Proof. intros. reflexivity. Qed.
Lemma bv_eqb_true : forall x a : word, bv_eqb x a = true -> x = a.
Proof. intros x a E. unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq. exact E. Qed.

Lemma mrestrict_write1 : forall m (a : word) b, F a = false -> mrestrict F (write_to_mem m a [b]) = write_to_mem (mrestrict F m) a [b].
Proof.
intros m a b Fa. apply functional_extensionality. intros x. unfold mrestrict. rewrite !write1_spec.
destruct (bv_eqb x a) eqn:E; [| reflexivity]. apply bv_eqb_true in E. subst x. rewrite Fa. reflexivity.
Qed.

Lemma ffs_remove_cons : forall fd FSd Fa,
ffs_remove Fa (fd :: FSd) = if ff_addr fd =? Fa then ffs_remove Fa FSd else fd :: ffs_remove Fa FSd.
Proof.
intros fd FSd Fa. unfold ffs_remove. rewrite filter_cons.
destruct (ff_addr fd =? Fa); cbn [negb]; destruct (decide _) as [H|H]; try reflexivity; exfalso; [exact H| apply H; exact I].
Qed.
Lemma ffs_remove_notin : forall FSd Fa, ~ In Fa (map ff_addr FSd) -> ffs_remove Fa FSd = FSd.
Proof.
induction FSd as [|fd FSd IH]; intros Fa Hn; [reflexivity|]. rewrite ffs_remove_cons. cbn [map In] in Hn.
destruct (Z.eqb_spec (ff_addr fd) Fa) as [E|E]; [exfalso; apply Hn; left; exact E|]. f_equal. apply IH. intros H. apply Hn. right. exact H.
Qed.
Lemma fr_remove_ffs : forall FSd Fa, List.NoDup (map ff_addr FSd) -> JH.fr_remove Fa (map fr_of FSd) = map fr_of (ffs_remove Fa FSd).
Proof.
intros FSd Fa. induction FSd as [|fd FSd IH]; intros ND; [reflexivity|].
cbn [map] in ND. apply NoDup_cons_iff in ND as [Hn ND]. rewrite ffs_remove_cons. cbn [map JH.fr_remove]. unfold fr_of at 1, JH.fr_base. cbn [fst].
destruct (Z.eqb_spec (ff_addr fd) Fa) as [E|E].
- subst Fa. rewrite (ffs_remove_notin FSd _ Hn). reflexivity.
- cbn [map]. f_equal. exact (IH ND).
Qed.

Lemma heapA0g_frame_run : forall g LB LM FR B m c, HEAPA0g g LB LM FR B m c ->
exists ps LBd FSd, dc_run _ _ _ _ DCo ps LBd FSd RE (mrestrict F m) /\ LB = map blk_of LBd /\ FR = map fr_of FSd.
Proof. intros g LB LM FR B m c (ps & LBd & FSd & RUN & ELB & EFR & _). exists ps, LBd, FSd. auto. Qed.

Lemma heapA0g_entry_facts : forall g LB LM FR B m c, HEAPA0g g LB LM FR B m c ->
appr DL (ae_fs_base RE) 0xb09000 /\ ae_fs_base RE + 0xb09000 <= RC.alloc_ceiling.
Proof. intros g LB LM FR B m c HP. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & _). exact (df_entry_facts _ _ _ _ _ _ _ DFs _ _ _ _ _ RUN). Qed.

Lemma heapA0g_frame_range : forall g LB LM FR B m c Fa k, HEAPA0g g LB LM FR B m c -> In (Fa, k) FR ->
fframe_rangeA RC.alloc_ceiling DL RE k Fa /\ (k <= 6 -> Fa mod ff_size k = 0).
Proof.
intros g LB LM FR B m c Fa k HP Hin. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & _ & EFR).
rewrite EFR in Hin. apply in_fr_of in Hin. split.
- exact (df_fframe_range _ _ _ _ _ _ _ DFs _ _ _ _ _ (k, Fa) RUN Hin).
- intros Hk. exact (df_fframe_align _ _ _ _ _ _ _ DFs _ _ _ _ _ k Fa RUN Hin Hk).
Qed.

Lemma bytes_at_hidden_off : forall m a bs, bytes_at segs (mrestrict F m) a bs -> forall x, a <= x < a + Z.of_nat (length bs) -> F (wa x) = false.
Proof.
intros m a bs (_ & _ & HB) x Hx. destruct (F (wa x)) eqn:E; [|reflexivity]. exfalso.
specialize (HB (Z.to_nat (x - a)) ltac:(lia)). replace (a + Z.of_nat (Z.to_nat (x - a))) with x in HB by lia.
unfold mrd, mrestrict in HB. rewrite E, (seg_rom_off segs F F_off _ E) in HB.
destruct (nth_error bs (Z.to_nat (x - a))) eqn:En; [discriminate|]. apply nth_error_None in En. lia.
Qed.

Lemma heapA0g_frame_flag : forall g LB LM FR B m c Fa k, HEAPA0g g LB LM FR B m c -> In (Fa, k) FR ->
exists flag : word,
bytes_at segs m (Fa + ff_size k - 8) (le8 flag)
/\ ae_fs_base RE + 0x1000 <= bv_unsigned flag < ae_fs_base RE + 0x9000
/\ F flag = false /\ wview segs m flag <> None
/\ (forall x, Fa + ff_size k - 8 <= x < Fa + ff_size k -> F (wa x) = false).
Proof.
intros g LB LM FR B m c Fa k HP Hin. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & _ & EFR).
rewrite EFR in Hin. apply in_fr_of in Hin.
destruct (df_fframe_flag _ _ _ _ _ _ _ DFs k _ _ _ _ _ Fa RUN Hin) as (flag & [_ HB] & Hr).
cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
destruct (df_fframe_release _ _ _ _ _ _ _ DFs k _ _ _ _ _ Fa flag RUN Hin HB) as (_ & WV & _ & _).
exists flag. split; [exact (bytes_at_unhide segs F F_off m _ _ HB)|]. split; [exact Hr|].
split; [exact (wview_hidden_off m flag WV)|]. split; [exact (wview_unhide segs F F_off m flag WV)|].
intros x Hx. apply (bytes_at_hidden_off m _ _ HB x). rewrite length_le8. lia.
Qed.

Lemma heapA0g_frame_blk_disjoint : forall g LB LM FR B m c Fa k a n, HEAPA0g g LB LM FR B m c -> In (Fa, k) FR -> In (a, n) LB ->
Fa + ff_size k <= a \/ a + n <= Fa.
Proof.
intros g LB LM FR B m c Fa k a n HP Hin Hb. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & ELB & EFR).
rewrite EFR in Hin. apply in_fr_of in Hin. rewrite ELB in Hb. apply in_map_iff in Hb as (bd & Eb & Hbd). unfold blk_of in Eb. inversion Eb; subst a n.
exact (df_fframe_block_disjoint _ _ _ _ _ _ _ DFs _ _ _ _ _ (k, Fa) bd RUN Hin Hbd).
Qed.

Lemma heapA0g_fs_blk_disjoint : forall g LB LM FR B m c a n, HEAPA0g g LB LM FR B m c -> In (a, n) LB ->
a + n <= ae_fs_base RE \/ ae_fs_base RE + 0xb09000 <= a.
Proof.
intros g LB LM FR B m c a n HP Hb. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & ELB & EFR).
rewrite ELB in Hb. apply in_map_iff in Hb as (bd & Eb & Hbd). unfold blk_of in Eb. inversion Eb; subst a n.
exact (df_fs_block_disjoint _ _ _ _ _ _ _ DFs _ _ _ _ _ bd RUN Hbd).
Qed.

Lemma heapA0g_frame_apart : forall g LB LM FR B m c Fa k Fa' k', HEAPA0g g LB LM FR B m c -> In (Fa, k) FR -> In (Fa', k') FR -> Fa <> Fa' ->
Fa + ff_size k <= Fa' \/ Fa' + ff_size k' <= Fa.
Proof.
intros g LB LM FR B m c Fa k Fa' k' HP H1 H2 Hne. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & _ & EFR).
rewrite EFR in H1, H2. apply in_fr_of in H1. apply in_fr_of in H2.
exact (df_fframes_disjoint _ _ _ _ _ _ _ DFs _ _ _ _ _ (k, Fa) (k', Fa') RUN H1 H2 Hne).
Qed.

Lemma heapA0g_frame_nodup : forall g LB LM FR B m c, HEAPA0g g LB LM FR B m c -> List.NoDup (map JH.fr_base FR).
Proof.
intros g LB LM FR B m c HP. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & _ & EFR).
rewrite EFR, map_map. exact (df_fframes_nodup _ _ _ _ _ _ _ DFs _ _ _ _ _ RUN).
Qed.

Lemma heapA0g_blk_slack : forall g LB LM FR B m c a n, HEAPA0g g LB LM FR B m c -> In (a, n) LB ->
exists junk, bytes_at segs m (a + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16.
Proof.
intros g LB LM FR B m c a n HP Hb. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & ELB & _).
rewrite ELB in Hb. apply in_map_iff in Hb as ([[pid A] nd] & Eb & Hbd). unfold blk_of in Eb. cbn [ablk_addr ablk_size fst snd] in Eb. injection Eb as -> ->.
destruct (df_blk_slack _ _ _ _ _ _ _ DFs _ _ _ _ _ pid a n RUN Hbd) as (junk & HB & Hl).
exists junk. split; [exact (bytes_at_unhide segs F F_off m _ _ HB)| exact Hl].
Qed.

Lemma heapA0g_shadow_words : forall g LB LM FR B m c a n i, HEAPA0g g LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
exists w : list byte, length w = 8%nat /\ bytes_at segs m ((JH.shad L a + i) / 8 * 8) w.
Proof.
intros g LB LM FR B m c a n i HP Hb Hi. destruct (heapA0g_frame_run _ _ _ _ _ _ _ HP) as (ps & LBd & FSd & RUN & ELB & _).
rewrite ELB in Hb. apply in_map_iff in Hb as ([[pid A] nd] & Eb & Hbd). unfold blk_of in Eb. cbn [ablk_addr ablk_size fst snd] in Eb. injection Eb as -> ->.
assert (H8 : 8 * i + 1 <= n) by (pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia).
destruct (df_nbhd _ _ _ _ _ _ _ DFs _ _ _ _ _ (a + 8 * i) 1 RUN) as [(w & [[_ HBw] _]) _]; [| lia|].
{ left. exists pid, a, n. split; [exact Hbd|]. lia. }
cbn [cells_bytes cbytes app] in HBw. rewrite app_nil_r in HBw.
exists (le8 w). split; [apply length_le8|].
replace ((JH.shad L a + i) / 8 * 8) with (8 * (SH (a + 8 * i) / 8)).
- exact (bytes_at_unhide segs F F_off m _ _ HBw).
- unfold JH.shad, SH. rewrite L_sb. replace (a + 8 * i) with (a + i * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Lemma heapA0g_frame_release : forall g LB LM FR B m c Fa k (flag : word),
HEAPA0g g LB LM FR B m c -> In (Fa, k) FR ->
bytes_at segs m (Fa + ff_size k - 8) (le8 flag) ->
let m' := write_to_mem m flag [Z_to_bv 8 0] in
HEAPA0g g LB LM (JH.fr_remove Fa FR) B m' c
/\ wview segs m flag <> None /\ F flag = false
/\ (forall x, F x = true -> m' x = m x)
/\ (forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None))
/\ HI.heap_pres HL (LB ++ LM ++ fr_ivs0 FR) RC.alloc_ceiling m m'.
Proof.
intros g LB LM FR B m c Fa k flag HP Hin HBm m'.
destruct (heapA0g_frame_flag _ _ _ _ _ _ _ Fa k HP Hin) as (flag' & HB' & Hflr & _ & _ & _).
destruct (heapA0g_entry_facts _ _ _ _ _ _ _ HP) as [[_ Hfsimg] _].
assert (Ef : flag' = flag) by (apply le8_inj0; exact (bytes_at_det0 m _ _ _ HB' HBm ltac:(rewrite !length_le8; reflexivity))). subst flag'. clear HB'.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
pose proof Hin as Hin'. rewrite EFR in Hin'. apply in_fr_of in Hin'.
assert (HBh : bytes_at segs (mrestrict F m) (Fa + ff_size k - 8) (le8 flag)).
{ destruct (df_fframe_flag _ _ _ _ _ _ _ DFs k _ _ _ _ _ Fa RUN Hin') as (flag2 & [_ HB2] & _).
cbn [cells_bytes cbytes app] in HB2. rewrite app_nil_r in HB2.
assert (E2 : flag2 = flag) by (apply le8_inj0; exact (bytes_at_det0 m _ _ _ (bytes_at_unhide segs F F_off m _ _ HB2) HBm ltac:(rewrite !length_le8; reflexivity))).
subst flag2. exact HB2. }
destruct (df_fframe_release _ _ _ _ _ _ _ DFs k _ _ _ _ _ Fa flag RUN Hin' HBh) as (RUN' & WV & Hlow & PRES).
pose proof (wview_hidden_off m flag WV) as Fflag.
pose proof (wview_unhide segs F F_off m flag WV) as WVm.
rewrite <- (mrestrict_write1 m flag (Z_to_bv 8 0) Fflag) in RUN', PRES. fold m' in RUN', PRES.
assert (HFm : forall x, F x = true -> m' x = m x).
{ intros x Fx. unfold m'. rewrite write1_spec. destruct (bv_eqb x flag) eqn:E; [| reflexivity]. apply bv_eqb_true in E. subst x. rewrite Fflag in Fx. discriminate. }
pose proof (gen_pres LBd FSd _ m m' PRES HFm) as Hgen.
assert (Hst : store_ok segs m flag 1 = true) by (cbn [store_ok]; destruct (wview segs m flag); [reflexivity| contradiction]).
assert (Hne : forall x, 0 <= x < 2^64 -> x <> bv_unsigned flag -> m' (wa x) = m (wa x)).
{ intros x Hx Hn. unfold m'. rewrite write1_spec. destruct (bv_eqb (wa x) flag) eqn:E; [| reflexivity]. exfalso. apply Hn.
apply bv_eqb_true in E. rewrite <- E. rewrite wa_unsigned by lia. reflexivity. }
pose proof (@RC.alloc_ceiling_range RC__) as Hceil0.
split.
{ exists ps, LBd, (ffs_remove Fa FSd).
split; [exact RUN'|]. split; [exact ELB|].
split; [rewrite EFR; apply fr_remove_ffs; exact (df_fframes_nodup _ _ _ _ _ _ _ DFs _ _ _ _ _ RUN)|].
split; [exact AI|]. split; [exact G|]. split; [exact Hcap|]. split; [exact Hbud|]. split; [exact K|]. split; [exact HC|]. split; [exact Hh|].
split; [exact (mem_inv_store segs m flag [Z_to_bv 8 0] MI Hst)|].
split. { apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HWR b Hb) as [W Foff]. split; [exact (wr_at_write segs m _ _ flag _ W)| exact Foff]. }
split; [exact HLM|]. split; [exact Hb0|]. split; [exact Hd0|]. split; [exact Hn0|].
split.
{ destruct HDN as (dn & HDn & HDcap). exists dn. split; [| exact HDcap]. apply (depot_n_agree (mrestrict F m) _ dn HDn).
intros x Hx. unfold mrestrict. destruct (F (wa x)); [reflexivity|]. apply Hne; [destruct L_dpn; lia|]. destruct L_dpn_hull. lia. }
split; [| exact HQB].
apply (stk_after m m' RC.alloc_ceiling HSTK); [split; [lia|]; split; [lia|]; intros a Ha; lia|].
intros a Ha Hge. apply Hne; [exact Ha| lia]. }
split; [exact WVm|]. split; [exact Fflag|]. split; [exact HFm|].
split. { intros a Ha Hcd. apply (Hgen a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd). }
intros a Ha Hcl. change (OM.wa a) with (wa a). apply (Hgen a Ha). intros Fa0.
destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
- right; right; left. apply in_block_map. rewrite <- ELB. exists b. auto.
- apply in_app_iff in Hb as [Hb|Hb].
+ exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa0. discriminate.
+ rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H].
Qed.

Theorem hiA_stack_malloc0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (k size lo : Z) (g : ghost),
HEAPA0g g LB LM FR B m c ->
0 <= k <= 2 \/ (k = 3 /\ JH.hl_stack_malloc L 3 <> 0) -> 0 < size <= ff_size k -> size mod 8 = 0 ->
Z.of_nat (length FR) < fframe_cap k ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
lo <= hi_top ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 size ->
(forall ms' m' (Fa : Z) (junk : list byte),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 Fa) m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m' ->
(forall x, F x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
fframe_rangeA RC.alloc_ceiling DL RE k Fa ->
rw_cells segs (mrestrict F m') Fa [CB (Z.to_nat (ff_size k - 8)) junk] ->
rw_cells segs (mrestrict F m') (SH Fa) [CB (Z.to_nat (ff_size k / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ff_size k / 8)))] ->
HEAPA0g g LB LM ((Fa, k) :: FR) B m' c ->
AJv segs LV T c ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (JH.hl_stack_malloc L k)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T LB LM FR B k size lo g
HP Hk Hsz Hsz8 Hcap Hstk Hlo Hlo2 Htop Htp Hgp Ha0 HK.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcapn & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Hsp64 : bv_unsigned sp <= 2^64) by (destruct Hstk as (_ & H & _); exact H).
pose proof (stk_join m lo (bv_unsigned sp) HSTK Hstk Hlo Hlo2 Htop) as Hstk0. destruct HDN as (dn & HDn & HDcap).
assert (Hstk' : stk segs (mrestrict F m) RC.alloc_ceiling (bv_unsigned sp)) by (apply stk_hide; [intros x Hx; apply F_above; lia| exact Hstk0]).
assert (Hcnt : Z.of_nat (length (filter (fun f => ff_cls f =? k) FSd)) < fframe_cap k).
{ pose proof (length_filter (fun f : fframe => ff_cls f =? k) FSd) as Hl. rewrite EFR, length_map in Hcap. lia. }
assert (Hk3 : 0 <= k <= 3) by (clear - Hk; lia).
assert (HkS : 0 <= k <= 2 \/ (k = 3 /\ SM 3 <> 0)) by (rewrite <- (L_sm 3 ltac:(lia)); exact Hk).
pose proof (df_stack_malloc _ _ _ _ _ _ _ DFs k HkS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
Fr fc (mrestrict F m) ps LBd FSd RE size RC.alloc_ceiling RUN Hcnt Hstk' (Z.le_refl _) ltac:(lia) (mem_inv_hide segs F m MI)
ltac:(rewrite <- L_tp; exact Htp) ltac:(rewrite <- L_gp; exact Hgp) Ha0 Hsz Hsz8) as Hevt.
rewrite <- (L_sm k Hk3) in Hevt.
match goal with |- AJv _ _ _ _ ?st => set (msv := st) end.
match type of Hevt with evt _ _ ?st => change st with (restrict F msv) in Hevt end.
unfold AJv. apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply (evt_restrict_lift segs F F_off Hwx) in Hevt. eapply evt_mono; [exact Hevt|]. clear Hevt.
intros ms'' [HPo Hhs].
destruct HPo as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & Ems & MI1 & Hstk1 & Hpres & _ & _ & HKo).
destruct HKo as [HDK HKo]. destruct HKo as (Fa & junk & -> & Hrng & RUN1 & Hbody & Hshad).
destruct (restrict_MS_inv F ms'' _ _ _ _ _ _ _ Ems) as [Ems'' Em1]. set (m'' := ms_mem ms'') in *.
subst m1'.
assert (HFm : forall x, F x = true -> m'' x = m x) by (intros x Fx; unfold m''; exact (Hhs _ Fx)).
pose proof (gen_pres LBd FSd _ m m'' Hpres HFm) as Hgen.
apply (HK ms'' m'' Fa junk).
- unfold HI.ret_state. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. exact Ems''.
- exact (stk_sub0 m'' _ lo _ (stk_unhide segs F F_off m'' _ _ Hstk1) Hlo).
- intros a Ha Hcl. change (OM.wa a) with (wa a). apply (Hgen a Ha). intros Fa0.
destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
+ right; right; left. apply in_block_map. rewrite <- ELB. exists b. auto.
+ apply in_app_iff in Hb as [Hb|Hb].
* exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa0. discriminate.
* rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H].
- exact HFm.
- intros a Ha Hcd. apply (Hgen a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd).
- exact Hrng.
- exact Hbody.
- exact Hshad.
- exists ps, LBd, ((k, Fa) :: FSd).
split; [exact RUN1|]. split; [exact ELB|]. split; [cbn [map]; unfold fr_of at 1; cbn [ff_addr ff_cls fst snd]; rewrite EFR; reflexivity|].
split; [exact AI|]. split; [exact G|]. split; [exact Hcapn|]. split; [exact Hbud|].
split; [exact K|]. split; [exact HC|]. split; [exact Hh|]. split; [exact (mem_inv_unhide m'' MI1)|].
split; [exact (wr_keep LBd FSd _ m m'' LBd Hgen (fun b H => H) HWR)|].
split; [exact HLM|]. split; [exact Hb0|]. split; [exact Hd0|]. split; [exact Hn0|].
split; [exists dn; split; [exact (HDK dn HDn)| exact HDcap]|]. split; [exact (stk_after m m'' (bv_unsigned sp) HSTK (stk_unhide segs F F_off m'' _ _ Hstk1) (fun a Ha Hsp => proj1 (Hgen a Ha (fun _ => or_introl Hsp))))| exact HQB].
Qed.

Variables SD SD_stack RL RL_stack : Z.
Hypothesis DT2 : donor_t2 RC.alloc_ceiling segs (at_nodeA LV segs) DL DCo SD SD_stack RL RL_stack.
Hypothesis L_strdup : JH.hl_strdup L = SD.
Hypothesis L_realloc : HI.hl_realloc HL = RL.
Hypothesis L_t2_stack : SD_stack <= JH.hl_stack_A L /\ RL_stack <= JH.hl_stack_A L.

Lemma wr_at_hide0 : forall m a n, (forall x, a <= x < a + n -> F (wa x) = false) -> wr_at segs m a n -> wr_at segs (mrestrict F m) a n.
Proof.
intros m a n HF (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|]. intros i Hi. specialize (HW i Hi).
unfold wview in *. rewrite (mrestrict_off F m _ (HF (a + i) ltac:(lia))). exact HW.
Qed.

Theorem hiA_strdup0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (src ab nb lo : Z) (str : list byte) (u : JH.uwd) (g : ghost),
let n := Z.of_nat (length str) + 1 in
HEAPA0g g LB LM FR B m c ->
In (ab, nb) LB -> ab <= src -> src + Z.of_nat (length str) + 1 <= ab + nb ->
bytes_at segs m src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> n <= 2^26 ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 src ->
lo <= hi_top ->
1 <= JH.bN B -> JH.acostA n <= JH.bB B -> JH.uw_cost u <= JH.bD B -> n + 8192 <= JH.bQ B ->
(forall ms' m' c' g' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m' ->
vmst (cfg_model c) (cfg_model c') ->
(forall x, F x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
r <> 0 -> bytes_at segs m' r (str ++ [Z_to_bv 8 0]) ->
HEAPA0g g' ((r, n) :: LB) LM FR (JH.chargeQ (JH.charge B (JH.acostA n) (JH.uw_cost u) 1) (n + 8192)) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (JH.hl_strdup L)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T LB LM FR B src ab nb lo str u g n
HP Hinb Hs1 Hs2 Hsrc Hnz Hn Hstk Hlo Hlo2 Htp Hgp Ha0 Htop HbN HbB HbD HbQ HK.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
destruct L_t2_stack as (Ls1 & Ls2).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Hn1 : 1 <= n) by (unfold n; lia).
assert (Hsp64 : bv_unsigned sp <= 2^64) by (destruct Hstk as (_ & H & _); exact H).
pose proof (stk_join m lo (bv_unsigned sp) HSTK Hstk Hlo Hlo2 Htop) as Hstk0. pose proof (unw_readable0 m (bv_unsigned sp) HSTK ltac:(lia)) as Hur.
destruct HDN as (dn & HDn & HDcap). pose proof (zlen_nonneg0 _ LBd) as Hz0.
assert (Hstk' : stk segs (mrestrict F m) RC.alloc_ceiling (bv_unsigned sp)) by (apply stk_hide; [intros x Hx; apply F_above; lia| exact Hstk0]).
rewrite ELB in Hinb. apply in_map_iff in Hinb as (bd & Eb & Hbd). unfold blk_of in Eb. injection Eb as Eab Enb.
destruct (proj1 (Forall_forall _ _) HWR bd Hbd) as [_ Hoffb].
assert (Hsrc' : bytes_at segs (mrestrict F m) src (str ++ [Z_to_bv 8 0])).
{ apply bytes_at_hide; [| exact Hsrc]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply Hoffb. lia. }
pose proof (dt_strdup _ _ _ _ _ _ _ _ _ DT2 LA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
Fr fc (mrestrict F m) ps LBd FSd RE bd src RC.alloc_ceiling dn str RE_L RUN Hbd ltac:(lia) ltac:(lia) Hsrc' Hnz Hn Hstk' (Z.le_refl _) ltac:(lia) (mem_inv_hide segs F m MI)
ltac:(rewrite <- L_tp; exact Htp) ltac:(rewrite <- L_gp; exact Hgp) Hur HDn ltac:(lia) Ha0) as Himpl.
rewrite <- L_strdup in Himpl. fold n in Himpl.
match goal with |- AJv _ _ _ _ ?st => set (msv := st) end.
match type of Himpl with implMG _ _ _ _ _ ?st => change st with (restrict F msv) in Himpl end.
set (X := map ablk_id LBd) in *.
assert (HlenX : zlen X <= kCapN) by (unfold X, zlen in *; rewrite length_map; lia).
pose proof (cap_ok_of_len X HlenX) as Hcapok.
pose proof (mcost_le_acost n ltac:(lia)) as Hmc. change (if n <=? 64512 then 0 else 3 * n + 45101) with (JH.acostA n) in Hmc.
unfold AJv.
apply (amalloc_vj_Fq segs LA LV BUDGET PERM TOT0 N0 LL Hwx Hsegs Hsh Hbx Hbc FRl HFR F_off T X n g ps _ c msv Himpl HC
ltac:(lia) ltac:(unfold kMaxReq; lia) (too_big_small n ltac:(lia)) AI G (cap_ok_room X _ n AI Hcapok ltac:(lia))
ltac:(lia) (cap_ok_reg X _ AI Hcapok) K).
intros p ps' c1 msv1 HQ (a' & g' & Eps & Hvo & K' & G' & Hsp' & AI' & Hnin & Hshape & KT & KG) HC1 Hh1 Hvm HF1.
apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply (evt_restrict_lift segs F F_off Hwx) in HQ. eapply evt_mono; [exact HQ|]. clear HQ.
intros ms'' [HPo Hhs].
destruct HPo as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & Ems & MI1 & Hstk1 & Hpres & _ & _ & HKo).
destruct HKo as [(dn' & HDn' & Hdn') HKo]. destruct HKo as (A & -> & HrA & Hreq & RUN1 & Hcells & Hshadow). fold n in HrA, Hreq, RUN1, Hshadow.
destruct (restrict_MS_inv F ms'' _ _ _ _ _ _ _ Ems) as [Ems'' Em1]. set (m'' := ms_mem ms'') in *.
destruct (dc_errno _ _ _ _ DCo _ _ _ _ _ RUN1) as [errv' Herr].
subst m1'.
assert (HFm : forall x, F x = true -> m'' x = m x) by (intros x Fx; unfold m''; rewrite (Hhs _ Fx); exact (HF1 _ Fx)).
pose proof (gen_pres LBd FSd _ m m'' Hpres HFm) as Hgen0.
assert (Hlenc : Z.of_nat (cells_size [CB (S (length str)) (str ++ [Z_to_bv 8 0])]) = n) by (cbn [cells_size csize]; unfold n; lia).
apply (HK ms'' m'' c1 g' A errv').
- unfold HI.ret_state. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. exact Ems''.
- destruct Hvo as (V1 & V2 & V3 & V4 & V5 & V6). unfold HI.model_vm_only. repeat split; try assumption. exact (vmst_init_sp _ _ Hvm).
- exact (stk_sub0 m'' _ lo _ (stk_unhide segs F F_off m'' _ _ Hstk1) Hlo).
- intros a Ha Hcl. change (OM.wa a) with (wa a). apply (Hgen0 a Ha). intros Fa.
destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
+ right; right; left. apply in_block_map. rewrite <- ELB. exists b. auto.
+ apply in_app_iff in Hb as [Hb|Hb].
* exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa. discriminate.
* rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H].
- exact Hvm.
- exact HFm.
- intros a Ha Hcd. apply (Hgen0 a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd).
- rewrite L_errno in Herr. apply (rw_cells_D segs m'' _ [OC.C4 errv']). cbn [map cellD].
destruct Herr as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs F F_off m'' _ _ Hb)]| exact (wr_at_unhide segs F F_off m'' _ _ Hw)].
- destruct HrA as (((Hlh & _) & _) & _). destruct Hlh as [[H _]|H]; [lia| unfold KHI, Qqcs.Mq0.kHighMemBeg in H; lia].
- destruct Hcells as [[_ Hb] _]. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. exact (bytes_at_unhide segs F F_off m'' _ _ Hb).
- exists ps', ((p, A, n) :: LBd), FSd.
assert (Ea : ps_a ps' = a') by (rewrite Eps; reflexivity).
split; [exact RUN1|]. split; [cbn [map]; unfold blk_of at 1; cbn [ablk_addr ablk_size fst snd]; rewrite ELB; reflexivity|].
split; [exact EFR|]. split; [rewrite Ea; exact AI'|]. split; [rewrite Ea; exact G'|].
split; [cbn [JH.chargeQ JH.charge JH.bN]; rewrite zlen_cons; lia|].
split; [rewrite Ea; cbn [JH.chargeQ JH.charge JH.bB]; lia|].
split; [exact K'|]. split; [exact HC1|]. split; [exact Hh1|]. split; [exact (mem_inv_unhide m'' MI1)|].
split.
{ constructor; [| exact (wr_keep LBd FSd _ m m'' LBd Hgen0 (fun b H => H) HWR)].
cbn [ablk_addr ablk_size fst snd]. destruct Hcells as [_ Hw]. rewrite Hlenc in Hw.
split; [exact (wr_at_unhide segs F F_off _ _ _ Hw)| exact (wr_at_hidden_off _ _ _ Hw)]. }
split; [exact HLM|]. cbn [JH.chargeQ JH.charge JH.bB JH.bD JH.bN]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exists dn'; split; [exact HDn'| cbn [JH.chargeQ JH.charge JH.bN]; rewrite zlen_cons; lia]|]. split; [exact (stk_after m m'' (bv_unsigned sp) HSTK (stk_unhide segs F F_off m'' _ _ Hstk1) (fun a Ha Hsp => proj1 (Hgen0 a Ha (fun _ => or_introl Hsp))))|].
unfold QBA in *. rewrite Ea. unfold qtot in *. rewrite KT, KG. cbn [map ablk_id fst JH.chargeQ JH.charge JH.bQ]. unfold qliveX in *. cbn [map]. rewrite zsum_cons.
unfold aptr_used at 1. rewrite Hreq. unfold used_size. unfold kBatchBytes in *. lia.
Qed.

Theorem hiA_realloc0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (p n0 n lo : Z) (old junk0 : list byte) (u : JH.uwd) (g : ghost),
HEAPA0g g LB LM FR B m c ->
In (p, n0) LB ->
OT.rw_cells segs m p [OC.CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
lo <= hi_top ->
1 <= JH.bN B -> JH.acostA n <= JH.bB B -> JH.uw_cost u <= JH.bD B -> n + 8192 <= JH.bQ B ->
(forall ms' m' c' g' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (HI.lb_remove p LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m' ->
vmst (cfg_model c) (cfg_model c') ->
(forall x, F x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
r <> 0 ->
(exists junk, OT.rw_cells segs m' r [OC.CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]) ->
HEAPA0g g' ((r, n) :: HI.lb_remove p LB) LM FR (JH.chargeQ (JH.charge B (JH.acostA n) (JH.uw_cost u) 1) (n + 8192)) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_realloc HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T LB LM FR B p n0 n lo old junk0 u g
HP Hin Hold Hstk Hlo Hlo2 Htp Hgp Ha0 Ha1 Hn Htop HbN HbB HbD HbQ HK.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
destruct L_t2_stack as (Ls1 & Ls2).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Hsp64 : bv_unsigned sp <= 2^64) by (destruct Hstk as (_ & H & _); exact H).
rewrite ELB in Hin. apply in_map_iff in Hin as ([[pid A0] nd] & Eb & Hbd). unfold blk_of in Eb. cbn [ablk_addr ablk_size fst snd] in Eb. injection Eb as -> ->.
pose proof (stk_join m lo (bv_unsigned sp) HSTK Hstk Hlo Hlo2 Htop) as Hstk0. pose proof (unw_readable0 m (bv_unsigned sp) HSTK ltac:(lia)) as Hur.
destruct HDN as (dn & HDn & HDcap). pose proof (zlen_nonneg0 _ LBd) as Hz0.
assert (Hstk' : stk segs (mrestrict F m) RC.alloc_ceiling (bv_unsigned sp)) by (apply stk_hide; [intros x Hx; apply F_above; lia| exact Hstk0]).
pose proof (dc_blocks_nodup _ _ _ _ DCo _ _ _ _ _ RUN) as NDid.
assert (Hz1 : zlen LBd = 1 + zlen (alb_remove pid LBd)).
{ pose proof (Permutation_length (alb_remove_perm LBd pid p n0 NDid Hbd)) as EL. cbn [length] in EL. rewrite !length_map in EL. unfold zlen. lia. }
destruct (ainv_q_nonneg _ _ AI) as [Qg0 Qt0].
assert (QR : qroom (ps_a ps) pid).
{ pose proof (zsum_map_perm (fun q => aptr_used q + kBatchBytes) _ _ (alb_remove_perm LBd pid p n0 NDid Hbd)) as EP.
cbn [map] in EP. rewrite zsum_cons in EP. pose proof (qliveX_nonneg (map ablk_id (alb_remove pid LBd))) as Hq0.
unfold QBA, qtot, qliveX, qroom in *. unfold kBatchBytes in *. lia. }
destruct (proj1 (Forall_forall _ _) HWR _ Hbd) as [_ Hoffb]. cbn [ablk_addr ablk_size fst snd] in Hoffb.
assert (Hold' : rw_cells segs (mrestrict F m) p [CB (Z.to_nat n0) (old ++ junk0)]).
{ apply (rw_cells_D segs m p [OC.CB (Z.to_nat n0) (old ++ junk0)]) in Hold. cbn [map cellD] in Hold. destruct Hold as [[Hwf Hb] Hw].
pose proof Hw as (W0 & W1 & _). cbn [cells_size csize] in W0, W1, Hw |- *.
assert (Hsz : forall x, p <= x < p + Z.of_nat (Z.to_nat n0 + 0) -> F (wa x) = false).
{ intros x Hx. apply Hoffb. destruct (Z.le_gt_cases 0 n0); [rewrite Nat.add_0_r, Z2Nat.id in Hx by lia; lia| rewrite Z2Nat.nonpos in Hx by lia; cbn in Hx; lia]. }
split; [split; [exact Hwf|]|].
- apply bytes_at_hide; [| exact Hb]. intros x Hx. apply Hsz. destruct Hwf as [Hl _]. cbn [cell_wf] in Hl. cbn [cells_bytes cbytes app] in Hx. rewrite app_nil_r, Hl in Hx. lia.
- apply wr_at_hide0; [| exact Hw]. exact Hsz. }
pose proof (dt_realloc _ _ _ _ _ _ _ _ _ DT2 LA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
Fr fc (mrestrict F m) ps LBd FSd RE pid p n0 n RC.alloc_ceiling dn old junk0 RE_L RUN Hbd QR Hold' Hstk' (Z.le_refl _) ltac:(lia) (mem_inv_hide segs F m MI)
ltac:(rewrite <- L_tp; exact Htp) ltac:(rewrite <- L_gp; exact Hgp) Hur HDn ltac:(lia) Ha0 Ha1 Hn) as Himpl.
rewrite <- L_realloc in Himpl.
match goal with |- AJv _ _ _ _ ?st => set (msv := st) end.
match type of Himpl with implMG _ _ _ _ _ ?st => change st with (restrict F msv) in Himpl end.
set (X := map ablk_id LBd) in *.
assert (Hdj : forall b1 b2, In b1 LBd -> In b2 LBd -> ablk_id b1 <> ablk_id b2 -> ablk_addr b1 <> ablk_addr b2).
{ intros b1 b2 H1 H2 Hne. pose proof (dc_blocks_disjoint _ _ _ _ DCo _ _ _ _ _ b1 b2 RUN H1 H2 Hne). lia. }
assert (HlenX : zlen X <= kCapN) by (unfold X, zlen in *; rewrite length_map; lia).
pose proof (cap_ok_of_len X HlenX) as Hcapok.
assert (HFRA : free_room_after X).
{ intros q a1' AIq. apply (cap_ok_room24 (q :: X) a1' AIq). apply cap_ok_of_len. rewrite zlen_cons. unfold X, zlen in *. rewrite length_map. lia. }
pose proof (mcost_le_acost n ltac:(lia)) as Hmc. change (if n <=? 64512 then 0 else 3 * n + 45101) with (JH.acostA n) in Hmc.
unfold AJv.
apply (arealloc_vj_Fq segs LA LV BUDGET PERM TOT0 N0 LL Hwx Hsegs Hsh Hbx Hbc FRl HFR F_off T X (map ablk_id (alb_remove pid LBd)) pid n g ps _ c msv Himpl HC
ltac:(lia) ltac:(unfold kMaxReq; lia) (too_big_small n ltac:(lia)) AI G (cap_ok_room X _ n AI Hcapok ltac:(lia))
ltac:(lia) (cap_ok_reg X _ AI Hcapok) K (alb_remove_perm LBd pid p n0 NDid Hbd) HFRA Qg0 Qt0 QR).
intros q ps' c1 msv1 HQ (a' & g' & Eps & Hvo & K' & G' & Hsp' & AI' & Hnin & Hshape & HQT) HC1 Hh1 Hvm HF1.
apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply (evt_restrict_lift segs F F_off Hwx) in HQ. eapply evt_mono; [exact HQ|]. clear HQ.
intros ms'' [HPo Hhs].
destruct HPo as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & Ems & MI1 & Hstk1 & Hpres & _ & _ & HKo).
destruct HKo as [(dn' & HDn' & Hdn') HKo]. destruct HKo as (A & junk & -> & HrA & Hreq & RUN1 & Hcells & Hshadow).
destruct (restrict_MS_inv F ms'' _ _ _ _ _ _ _ Ems) as [Ems'' Em1]. set (m'' := ms_mem ms'') in *.
destruct (dc_errno _ _ _ _ DCo _ _ _ _ _ RUN1) as [errv' Herr].
subst m1'.
assert (HFm : forall x, F x = true -> m'' x = m x) by (intros x Fx; unfold m''; rewrite (Hhs _ Fx); exact (HF1 _ Fx)).
pose proof (gen_pres (alb_remove pid LBd) FSd _ m m'' Hpres HFm) as Hgen0.
apply (HK ms'' m'' c1 g' A errv').
- unfold HI.ret_state. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. exact Ems''.
- destruct Hvo as (V1 & V2 & V3 & V4 & V5 & V6). unfold HI.model_vm_only. repeat split; try assumption. exact (vmst_init_sp _ _ Hvm).
- exact (stk_sub0 m'' _ lo _ (stk_unhide segs F F_off m'' _ _ Hstk1) Hlo).
- intros a Ha Hcl. change (OM.wa a) with (wa a). apply (Hgen0 a Ha). intros Fa.
destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
+ right; right; left. apply in_block_map. rewrite (alb_remove_map LBd pid p n0 NDid Hdj Hbd), <- ELB. exists b. auto.
+ apply in_app_iff in Hb as [Hb|Hb].
* exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa. discriminate.
* rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H].
- exact Hvm.
- exact HFm.
- intros a Ha Hcd. apply (Hgen0 a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd).
- rewrite L_errno in Herr. apply (rw_cells_D segs m'' _ [OC.C4 errv']). cbn [map cellD].
destruct Herr as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs F F_off m'' _ _ Hb)]| exact (wr_at_unhide segs F F_off m'' _ _ Hw)].
- destruct HrA as (((Hlh & _) & _) & _). destruct Hlh as [[H _]|H]; [lia| unfold KHI, Qqcs.Mq0.kHighMemBeg in H; lia].
- exists junk. apply (rw_cells_D segs m'' _ [OC.CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]). cbn [map cellD].
destruct Hcells as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs F F_off m'' _ _ Hb)]| exact (wr_at_unhide segs F F_off m'' _ _ Hw)].
- exists ps', ((q, A, n) :: alb_remove pid LBd), FSd.
assert (Ea : ps_a ps' = a') by (rewrite Eps; reflexivity).
split; [exact RUN1|].
split; [cbn [map]; unfold blk_of at 1; cbn [ablk_addr ablk_size fst snd]; rewrite (alb_remove_map LBd pid p n0 NDid Hdj Hbd), <- ELB; reflexivity|].
split; [exact EFR|]. split; [rewrite Ea; exact AI'|]. split; [rewrite Ea; exact G'|].
split; [cbn [JH.chargeQ JH.charge JH.bN]; rewrite zlen_cons; pose proof (zlen_alb_remove LBd pid); lia|].
split; [rewrite Ea; cbn [JH.chargeQ JH.charge JH.bB]; lia|].
split; [exact K'|]. split; [exact HC1|]. split; [exact Hh1|]. split; [exact (mem_inv_unhide m'' MI1)|].
split.
{ constructor.
- cbn [ablk_addr ablk_size fst snd]. destruct Hcells as [_ Hw].
cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
split; [exact (wr_at_unhide segs F F_off _ _ _ Hw)| exact (wr_at_hidden_off _ _ _ Hw)].
- apply (wr_keep (alb_remove pid LBd) FSd _ m m'' (alb_remove pid LBd) Hgen0 (fun b H => H)).
apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) HWR). exact (alb_remove_In LBd pid b Hb). }
split; [exact HLM|]. cbn [JH.chargeQ JH.charge JH.bB JH.bD JH.bN]. split; [lia|]. split; [lia|]. split; [lia|].

split; [exists dn'; split; [exact HDn'| cbn [JH.chargeQ JH.charge JH.bN]; rewrite zlen_cons; lia]|]. split; [exact (stk_after m m'' (bv_unsigned sp) HSTK (stk_unhide segs F F_off m'' _ _ Hstk1) (fun a Ha Hsp => proj1 (Hgen0 a Ha (fun _ => or_introl Hsp))))|].
unfold QBA in *. rewrite Ea. pose proof (zsum_map_perm (fun q0 => aptr_used q0 + kBatchBytes) _ _ (alb_remove_perm LBd pid p n0 NDid Hbd)) as EP.
cbn [map] in EP. rewrite zsum_cons in EP. unfold qliveX in *. cbn [map ablk_id fst JH.chargeQ JH.charge JH.bQ]. rewrite zsum_cons.
unfold aptr_used at 1. rewrite Hreq. unfold used_size. unfold kBatchBytes in *. lia.
Qed.

Theorem hiA_stack_malloc0_G : forall (Jf : OSA.TSet -> config -> Prop) (Jf_sc : forall T, silent_closed LV segs (Jf T)),
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (k size lo : Z) (g : ghost),
HEAPA0g g LB LM FR B m c ->
0 <= k <= 2 \/ (k = 3 /\ JH.hl_stack_malloc L 3 <> 0) -> 0 < size <= ff_size k -> size mod 8 = 0 ->
Z.of_nat (length FR) < fframe_cap k ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
lo <= hi_top ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 size ->
(forall ms' m' (Fa : Z) (junk : list byte),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 Fa) m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 FR) (bv_unsigned sp) m m' ->
(forall x, F x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
fframe_rangeA RC.alloc_ceiling DL RE k Fa ->
rw_cells segs (mrestrict F m') Fa [CB (Z.to_nat (ff_size k - 8)) junk] ->
rw_cells segs (mrestrict F m') (SH Fa) [CB (Z.to_nat (ff_size k / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ff_size k / 8)))] ->
HEAPA0g g LB LM ((Fa, k) :: FR) B m' c ->
VJ LV (Jf T) c ms') ->
VJ LV (Jf T) c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (JH.hl_stack_malloc L k)) fc None m (seg_rom segs)).
Proof.
intros Jf Jf_sc.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T LB LM FR B k size lo g
HP Hk Hsz Hsz8 Hcap Hstk Hlo Hlo2 Htop Htp Hgp Ha0 HK.
destruct HP as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcapn & Hbud & K & HC & Hh & MI & HWR & HLM & Hb0 & Hd0 & Hn0 & HDN & HSTK & HQB).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (Hsp64 : bv_unsigned sp <= 2^64) by (destruct Hstk as (_ & H & _); exact H).
pose proof (stk_join m lo (bv_unsigned sp) HSTK Hstk Hlo Hlo2 Htop) as Hstk0. destruct HDN as (dn & HDn & HDcap).
assert (Hstk' : stk segs (mrestrict F m) RC.alloc_ceiling (bv_unsigned sp)) by (apply stk_hide; [intros x Hx; apply F_above; lia| exact Hstk0]).
assert (Hcnt : Z.of_nat (length (filter (fun f => ff_cls f =? k) FSd)) < fframe_cap k).
{ pose proof (length_filter (fun f : fframe => ff_cls f =? k) FSd) as Hl. rewrite EFR, length_map in Hcap. lia. }
assert (Hk3 : 0 <= k <= 3) by (clear - Hk; lia).
assert (HkS : 0 <= k <= 2 \/ (k = 3 /\ SM 3 <> 0)) by (rewrite <- (L_sm 3 ltac:(lia)); exact Hk).
pose proof (df_stack_malloc _ _ _ _ _ _ _ DFs k HkS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
Fr fc (mrestrict F m) ps LBd FSd RE size RC.alloc_ceiling RUN Hcnt Hstk' (Z.le_refl _) ltac:(lia) (mem_inv_hide segs F m MI)
ltac:(rewrite <- L_tp; exact Htp) ltac:(rewrite <- L_gp; exact Hgp) Ha0 Hsz Hsz8) as Hevt.
rewrite <- (L_sm k Hk3) in Hevt.
match goal with |- VJ _ _ _ ?st => set (msv := st) end.
match type of Hevt with evt _ _ ?st => change st with (restrict F msv) in Hevt end.
apply (vj_evt segs LV Hwx Hsegs _ (Jf_sc T)).
apply (evt_restrict_lift segs F F_off Hwx) in Hevt. eapply evt_mono; [exact Hevt|]. clear Hevt.
intros ms'' [HPo Hhs].
destruct HPo as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1' & Ems & MI1 & Hstk1 & Hpres & _ & _ & HKo).
destruct HKo as [HDK HKo]. destruct HKo as (Fa & junk & -> & Hrng & RUN1 & Hbody & Hshad).
destruct (restrict_MS_inv F ms'' _ _ _ _ _ _ _ Ems) as [Ems'' Em1]. set (m'' := ms_mem ms'') in *.
subst m1'.
assert (HFm : forall x, F x = true -> m'' x = m x) by (intros x Fx; unfold m''; exact (Hhs _ Fx)).
pose proof (gen_pres LBd FSd _ m m'' Hpres HFm) as Hgen.
apply (HK ms'' m'' Fa junk).
- unfold HI.ret_state. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. exact Ems''.
- exact (stk_sub0 m'' _ lo _ (stk_unhide segs F F_off m'' _ _ Hstk1) Hlo).
- intros a Ha Hcl. change (OM.wa a) with (wa a). apply (Hgen a Ha). intros Fa0.
destruct Hcl as [H|[H|H]]; [left; exact H| right; left; exact (L_static a H)|].
unfold HI.in_block in H. destruct H as (b & Hb & Hr). apply in_app_iff in Hb as [Hb|Hb].
+ right; right; left. apply in_block_map. rewrite <- ELB. exists b. auto.
+ apply in_app_iff in Hb as [Hb|Hb].
* exfalso. destruct b as [ba bn]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
rewrite (HLM ba bn a Hb Hr) in Fa0. discriminate.
* rewrite EFR in Hb. destruct (in_fr_ivs0 FSd a (ex_intro _ b (conj Hb Hr))) as [H|H]; [do 3 right; left; exact H| do 4 right; left; exact H].
- exact HFm.
- intros a Ha Hcd. apply (Hgen a Ha). intros _. exact (dkeepA_client _ _ _ _ _ _ Hcd).
- exact Hrng.
- exact Hbody.
- exact Hshad.
- exists ps, LBd, ((k, Fa) :: FSd).
split; [exact RUN1|]. split; [exact ELB|]. split; [cbn [map]; unfold fr_of at 1; cbn [ff_addr ff_cls fst snd]; rewrite EFR; reflexivity|].
split; [exact AI|]. split; [exact G|]. split; [exact Hcapn|]. split; [exact Hbud|].
split; [exact K|]. split; [exact HC|]. split; [exact Hh|]. split; [exact (mem_inv_unhide m'' MI1)|].
split; [exact (wr_keep LBd FSd _ m m'' LBd Hgen (fun b H => H) HWR)|].
split; [exact HLM|]. split; [exact Hb0|]. split; [exact Hd0|]. split; [exact Hn0|].
split; [exists dn; split; [exact (HDK dn HDn)| exact HDcap]|]. split; [exact (stk_after m m'' (bv_unsigned sp) HSTK (stk_unhide segs F F_off m'' _ _ Hstk1) (fun a Ha Hsp => proj1 (Hgen a Ha (fun _ => or_introl Hsp))))| exact HQB].
Qed.

End Inst0.
