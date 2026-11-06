(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QZDE QWxq_c1 QbrW Qfw3_c1 QRjH QuJV Qnhz QHnV QCcH QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg QZDE QWxq_c1 QbrW Qfw3_c1.Mq2.
Import QRjH QuJV.Mq1 Qnhz.Mq0.
Import QHnV QCcH QfLs.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma inside_shrink : forall W a n a' n', inside W a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> inside W a' n'.
Proof.
induction W as [|[lo hi] W IH]; intros a n a' n' H Ha Hn; cbn in *; [exact H|].
destruct H as [H|H]; [left; lia | right; eapply IH; eauto].
Qed.

Section Glue.
Variable segs : list Segment.

#[using="Type"] Lemma lbw_mstep : forall V T p ms ms' md,
model_ok md -> mstep segs ms ms' -> lbw segs V T p (mkCfg ms' md) -> lbw segs V T p (mkCfg ms md).
Proof.
intros V T p ms ms' md [Hh Hl] [Hsvc Hst] H.
eapply lbw_silent1; [apply node_instr; eassumption | exact H].
Qed.

#[using="Type"] Lemma lbw_evt : forall V T p (Q : machine_state -> Prop) ms md,
model_ok md -> evt segs Q ms -> (forall ms', Q ms' -> lbw segs V T p (mkCfg ms' md)) -> lbw segs V T p (mkCfg ms md).
Proof.
intros V T p Q ms md MOK (ms' & STEPS & HQ) K.
induction STEPS as [ms0 | ms0 ms1 ms2 H1 H2 IH].
- apply K. exact HQ.
- eapply lbw_mstep; [exact MOK | exact H1 | apply IH; exact HQ].
Qed.

#[using="Type"] Lemma lbw_back_steps : forall V T ms ms1 msV md,
model_ok md -> mstep segs ms ms1 -> msteps segs ms1 msV -> V (mkCfg msV md) -> lbw segs V T false (mkCfg ms md).
Proof.
intros V T ms ms1 msV md MOK H1 STEPS. revert ms H1.
induction STEPS as [ms0 | ms0 msa msb Ha Hb IH]; intros ms H1 HV.
- destruct MOK as [Hh Hl]. destruct H1 as [Hsvc Hst]. eapply lbw_back1; [apply node_instr; eassumption | exact HV].
- eapply lbw_mstep; [exact MOK | exact H1 | apply IH; [exact Ha | exact HV]].
Qed.

#[using="Type"] Lemma lbw_of_evt_V : forall V T (Q : machine_state -> Prop) ms md,
model_ok md -> evt segs Q ms -> (forall ms', Q ms' -> V (mkCfg ms' md) /\ ms' <> ms) -> lbw segs V T false (mkCfg ms md).
Proof.
intros V T Q ms md MOK (ms' & STEPS & HQ) K. destruct (K ms' HQ) as [HV NE].
inversion STEPS; subst; [exfalso; apply NE; reflexivity|].
eapply lbw_back_steps; eassumption.
Qed.

#[using="Type"] Lemma lbw_exit_rz : forall V T p ms md, realizes segs (mkCfg ms md) T -> lbw segs V T p (mkCfg ms md).
Proof. intros. apply lbw_exit. assumption. Qed.

#[using="Type"] Lemma syswrite_facts : forall m A n junk bs W m0,
rw_cells segs m A [CB n junk] -> (length bs <= n)%nat -> mem_inv segs m ->
munch W m0 m -> wmono segs m0 m -> inside W A (Z.of_nat n) ->
rw_cells segs (write_to_mem m (wa A) bs) A [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
/\ mem_inv segs (write_to_mem m (wa A) bs)
/\ munch W m0 (write_to_mem m (wa A) bs) /\ wmono segs m0 (write_to_mem m (wa A) bs).
Proof.
intros m A n junk bs W m0 C Hlen MI MU WM HIN.
pose proof (rw_cells_bound segs m A _ C) as B. cbn [cells_size csize Nat.add] in B.
split; [apply rw_cells_CB_prefix_write; assumption|].
split; [eapply mem_inv_syswrite; eassumption|].
split.
- apply munch_write; [exact MU | lia | lia |]. eapply inside_shrink; [exact HIN | lia | lia].
- apply wmono_write. exact WM.
Qed.
End Glue.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QsRG.Mq0 Qnhz.Mq0 QRjH QSpR.Mq1 QuJV.Mq1.
Import ListNotations.
Open Scope bv_scope.

Section Node.
Variable segs : list Segment.
Variables (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
(m : word -> option byte) (model : Model) (w : bv 32).
Hypothesis HF : fetch_word segs pc = Some w.
Hypothesis HE : is_ecall w = true.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].

Let pre : machine_state := MS R F pc fc rv m (seg_rom segs).
Let ms : machine_state := MSsvc R F pc (getr R 17) fc rv m (seg_rom segs).
Let post (r : word) : machine_state := MS (regupd R 10 r) F (v_addi pc 4) fc rv m (seg_rom segs).
Let postm (r : word) (m' : word -> option byte) : machine_state :=
MS (regupd R 10 r) F (v_addi pc 4) fc rv m' (seg_rom segs).

Variable buflen : Z.
Hypothesis H17 : getr R 17 = Z_to_bv 64 278.
Hypothesis H11 : getr R 11 = Z_to_bv 64 buflen.
Hypothesis Hbl : (1 <= buflen)%Z.
Hypothesis Hblmax : (buflen <= 256)%Z.
Hypothesis H12 : getr R 12 = Z_to_bv 64 0 \/ getr R 12 = Z_to_bv 64 GRND_NONBLOCK.
Hypothesis Hok : store_ok segs m (getr R 10) (Z.to_nat buflen) = true.

#[using="w HF HE Hh Hlazy ms H17 H11 Hbl Hblmax H12 Hok"] Lemma lbw_getrandom_k : forall (V : config -> Prop) (T : TSet) (p : bool) (wf : list byte -> bool),
(forall bs, Z.of_nat (length bs) = buflen ->
lbw segs V T (wf bs) (mkCfg (postm (len_word bs) (wbytes m (getr R 10) bs)) model)) ->
(p = true -> exists bs0, Z.of_nat (length bs0) = buflen /\ wf bs0 = true) ->
lbw segs V T p (mkCfg pre model).
Proof.
intros V T p wf HB Hw.
eapply ncl_ecall; [apply nclosed_lbw | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
apply (lbw_node segs V T p (mkCfg ms model) (getrandom_I buflen) (getrandom_nx segs R F pc fc rv m model buflen)
(fun i => match i with exist _ bs _ => Some (wf bs) end)
(node_getrandom segs R F pc fc rv m model Hh Hlazy buflen H17 H11 Hbl Hblmax H12 Hok)).
- intros [bs Hb] q Hq; injection Hq as <-; cbn [getrandom_nx]. apply HB; assumption.
- intros [bs Hbs] Hq; discriminate Hq.
- intros Hp. destruct (Hw Hp) as (bs0 & H1 & H3). exists (exist _ bs0 H1). rewrite H3. reflexivity.
Qed.
End Node.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

#[using="Type"] Lemma slot_cells_size : forall s, cells_size (slot_cells s) = 40%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma lh_slot_at : forall m tbl svs i s, lh_slots segs m tbl svs -> nth_error svs i = Some s ->
rw_cells segs m (ent_addr tbl i) (slot_cells s).
Proof. intros m tbl svs i s H E. exact (H i s E). Qed.

#[using="Type"] Lemma lh_slots_frame : forall m m' tbl svs W,
lh_slots segs m tbl svs -> munch W m m' -> wmono segs m m' ->
(forall i, (i < length svs)%nat -> Forall (fun iv => ent_addr tbl i + 40 <= fst iv \/ snd iv <= ent_addr tbl i) W) ->
lh_slots segs m' tbl svs.
Proof.
intros m m' tbl svs W SL MU WM DJ i s E.
pose proof (SL i s E) as C.
eapply (rw_cells_transport segs W m m'); [exact C | exact MU | exact WM |].
rewrite slot_cells_size. change (Z.of_nat 40) with 40.
specialize (DJ i (proj1 (nth_error_Some svs i) ltac:(rewrite E; discriminate))).
clear -DJ. induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in DJ as [D1 DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
Qed.

#[using="Type"] Lemma lh_slots_upd : forall m tbl svs n s',
(forall i s, i <> n -> nth_error svs i = Some s -> rw_cells segs m (ent_addr tbl i) (slot_cells s)) ->
rw_cells segs m (ent_addr tbl n) (slot_cells s') -> (n < length svs)%nat ->
lh_slots segs m tbl (upd svs n s').
Proof.
intros m tbl svs n s' OTH NEW Hn i s E.
destruct (Nat.eq_dec i n) as [->|NE].
- rewrite nth_error_upd_same in E by exact Hn. injection E as <-. exact NEW.
- rewrite nth_error_upd_other in E by (intros X; apply NE; symmetry; exact X). exact (OTH i s NE E).
Qed.
End WithSegs.

Definition ZSLOT : slotv := SV 0 0 0 0 0 0.
Definition ESLOT : slotv := SV LH_EMPTYv 0 0 0 0 0.

#[using="Type"] Lemma firstn_repeat' : forall {A} (x : A) n k, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof.
intros A x n k Hk. replace n with (k + (n - k))%nat by lia. rewrite repeat_app, firstn_app, firstn_all2 by (rewrite repeat_length; lia).
rewrite repeat_length, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
#[using="Type"] Lemma skipn_repeat' : forall {A} (x : A) n k, (k <= n)%nat -> skipn k (repeat x n) = repeat x (n - k).
Proof.
intros A x n k Hk. replace n with (k + (n - k))%nat at 1 by lia. rewrite repeat_app, skipn_app, skipn_all2 by (rewrite repeat_length; lia).
rewrite repeat_length, Nat.sub_diag, skipn_O. reflexivity.
Qed.

Section Init.
Variable segs : list Segment.

#[using="Type"] Lemma zslot_bytes : cells_bytes (slot_cells ZSLOT) = repeat (Z_to_bv 8 0) 40.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma zeros_slots : forall n m tbl,
rw_cells segs m tbl [CB (Z.to_nat (40 * Z.of_nat n)) (repeat (Z_to_bv 8 0) (Z.to_nat (40 * Z.of_nat n)))] ->
lh_slots segs m tbl (repeat ZSLOT n).
Proof.
induction n as [|n IH]; intros m tbl H i s E.
- destruct i; discriminate.
- replace (Z.to_nat (40 * Z.of_nat (S n))) with (40 + Z.to_nat (40 * Z.of_nat n))%nat in H by lia.
apply (rw_cells_CB_cut segs m _ _ _ 40) in H; [|lia]. destruct H as [H1 H2].
rewrite firstn_repeat' in H1 by lia. rewrite skipn_repeat' in H2 by lia.
replace (40 + Z.to_nat (40 * Z.of_nat n) - 40)%nat with (Z.to_nat (40 * Z.of_nat n)) in H2 by lia.
destruct i as [|i].
+ cbn in E. injection E as <-. unfold ent_addr. rewrite Z.mul_0_r, Z.add_0_r.
eapply (rw_cells_recast segs m tbl _ (slot_cells ZSLOT)) in H1; [exact H1 | cbn; repeat split; reflexivity | rewrite zslot_bytes; reflexivity | reflexivity].
+ cbn in E. pose proof (IH _ _ H2 i s E) as X. unfold ent_addr in *.
replace (tbl + 40 * Z.of_nat (S i)) with (tbl + Z.of_nat 40 + 40 * Z.of_nat i) by lia. exact X.
Qed.

Definition init_svs (i n : nat) : list slotv := repeat ESLOT i ++ repeat ZSLOT (n - i).
#[using="Type"] Lemma init_svs_length : forall i n, (i <= n)%nat -> length (init_svs i n) = n.
Proof. intros. unfold init_svs. rewrite length_app, !repeat_length. lia. Qed.
#[using="Type"] Lemma upd_app_len : forall {X} (a b : list X) x y, upd (a ++ x :: b) (length a) y = a ++ y :: b.
Proof. intros X a. induction a as [|z a IH]; intros b x y; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
#[using="Type"] Lemma init_svs_step : forall i n, (i < n)%nat -> upd (init_svs i n) i ESLOT = init_svs (S i) n.
Proof.
intros i n Hi. unfold init_svs.
replace (n - i)%nat with (S (n - S i)) by lia. cbn [repeat].
pose proof (upd_app_len (repeat ESLOT i) (repeat ZSLOT (n - S i)) ZSLOT ESLOT) as X.
rewrite repeat_length in X. rewrite X.
change (ESLOT :: repeat ZSLOT (n - S i)) with ([ESLOT] ++ repeat ZSLOT (n - S i)). rewrite app_assoc.
replace (repeat ESLOT i ++ [ESLOT]) with (repeat ESLOT (S i)); [reflexivity|].
clear. induction i as [|i IH]; [reflexivity|]. cbn [repeat app]. rewrite <- IH. reflexivity.
Qed.
#[using="Type"] Lemma init_svs_nth_ge : forall i n j, (i <= j < n)%nat -> nth_error (init_svs i n) j = Some ZSLOT.
Proof.
intros i n j Hj. unfold init_svs. rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length.
apply nth_error_repeat. lia.
Qed.
#[using="Type"] Lemma init_svs_0 : forall n, init_svs 0 n = repeat ZSLOT n.
Proof. intros. unfold init_svs. cbn. rewrite Nat.sub_0_r. reflexivity. Qed.
#[using="Type"] Lemma init_svs_all : forall n, init_svs n n = repeat ESLOT n.
Proof. intros. unfold init_svs. rewrite Nat.sub_diag. cbn. rewrite app_nil_r. reflexivity. Qed.
End Init.

Section Glob.
Variable segs : list Segment.
Variable fn : fnaddrs.
Variables (ghash ggot gvdso : Z).
Variable vdso_ok : Z -> Prop.
Definition lh_glob (m : word -> option byte) : Prop :=
(exists seed : word, rw_cells segs m ghash [C8 (Z_to_bv 64 (fn_lh_char_hash fn)); C4 seed])
/\ rw_cells segs m ggot [C8 (Z_to_bv 64 (fn_lh_char_equal fn))]
/\ (exists vf : Z, rw_cells segs m gvdso [C8 (Z_to_bv 64 vf)] /\ vdso_ok vf).
End Glob.

Section SlotWrite.
Variable segs : list Segment.

#[using="Type"] Lemma lh_slots_write_slot : forall m m' tbl svs n s',
lh_slots segs m tbl svs -> (n < length svs)%nat ->
munch [(ent_addr tbl n, ent_addr tbl n + 40)] m m' -> wmono segs m m' ->
rw_cells segs m' (ent_addr tbl n) (slot_cells s') ->
lh_slots segs m' tbl (upd svs n s').
Proof.
intros m m' tbl svs n s' SL Hn MU WM NEW i s E.
destruct (Nat.eq_dec i n) as [->|NE].
- rewrite nth_error_upd_same in E by exact Hn. injection E as <-. exact NEW.
- rewrite nth_error_upd_other in E by (intros X; apply NE; symmetry; exact X).
eapply (rw_cells_transport segs _ m m'); [exact (SL i s E) | exact MU | exact WM |].
rewrite slot_cells_size. cbn. unfold ent_addr. split; [|exact I]. nia.
Qed.
End SlotWrite.

Section Blocks2.

#[using="Type"] Lemma blocks2 : forall L (HIx : heap_iface L) A a na b nb LB m md,
HEAP L HIx A ((a, na) :: (b, nb) :: LB) m md ->
(a mod 16 = 0 /\ 0 < a /\ a + na <= alloc_ceiling /\ (a + na <= hl_img_lo L \/ hl_img_hi L <= a))
/\ (b mod 16 = 0 /\ 0 < b /\ b + nb <= alloc_ceiling /\ (b + nb <= hl_img_lo L \/ hl_img_hi L <= b))
/\ (a + na <= b \/ b + nb <= a).
Proof.
intros L HIx A a na b nb LB m md HP.
pose proof (heap_blk L HIx _ _ _ _ a na HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img L HIx _ _ _ _ a na HP ltac:(left; reflexivity)) as Hia.
pose proof (heap_blk L HIx _ _ _ _ b nb HP ltac:(right; left; reflexivity)) as (_ & Hal2 & Hlo2 & Hhi2 & _).
pose proof (heap_blk_img L HIx _ _ _ _ b nb HP ltac:(right; left; reflexivity)) as Hia2.
pose proof (blk_ne_01 L HIx _ _ _ _ _ _ _ _ HP) as Hne.
pose proof (heap_blk_disjoint L HIx _ _ _ _ a na b nb HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hne) as Hdj.
repeat split; try assumption.
Qed.
End Blocks2.

Section Pres.
Variable L : heap_layout.

#[using="Type"] Lemma lh_slots_presx : forall X LB SP m m' tbl svs size,
heap_presx L X LB SP m m' -> In (tbl, 40 * size) LB -> Z.of_nat (length svs) = size ->
lh_slots (hl_segs L) m tbl svs -> lh_slots (hl_segs L) m' tbl svs.
Proof.
intros X LB SP m m' tbl svs size HPR Hin Hlen SL i s E.
pose proof (proj1 (nth_error_Some svs i) ltac:(rewrite E; discriminate)) as Hi.
eapply (heap_presx_rw_cells L); [exact HPR | exact (SL i s E) |].
eapply client_rangex_block; [exact Hin | unfold ent_addr; lia | rewrite slot_cells_size; unfold ent_addr; lia].
Qed.
#[using="Type"] Lemma lh_slots_pres : forall LB SP m m' tbl svs size,
heap_pres L LB SP m m' -> In (tbl, 40 * size) LB -> Z.of_nat (length svs) = size ->
lh_slots (hl_segs L) m tbl svs -> lh_slots (hl_segs L) m' tbl svs.
Proof. intros LB SP m m' tbl svs size HPR. apply (lh_slots_presx (fun _ => False) LB SP). apply heap_pres_presx. exact HPR. Qed.
#[using="Type"] Lemma lh_keys_presx : forall X LB SP m m' es,
heap_presx L X LB SP m m' -> (forall e, In e es -> In (le_k e, le_kn e) LB) ->
lh_keys (hl_segs L) m es -> lh_keys (hl_segs L) m' es.
Proof.
intros X LB SP m m' es HPR Hin KS. unfold lh_keys in *. rewrite Forall_forall in *.
intros e He. destruct (KS e He) as (Hl & Hnz & junk & C). split; [exact Hl|]. split; [exact Hnz|]. exists junk.
eapply (heap_presx_rw_cells L); [exact HPR | exact C |].
assert (LJ : length ((le_ks e ++ [Z_to_bv 8 0]) ++ junk) = Z.to_nat (le_kn e)) by (destruct C as [[[W _] _] _]; rewrite <- app_assoc; exact W).
eapply client_rangex_block; [exact (Hin e He) | lia | cbn; rewrite length_app in LJ; cbn in LJ; lia].
Qed.
#[using="Type"] Lemma lh_keys_pres : forall LB SP m m' es,
heap_pres L LB SP m m' -> (forall e, In e es -> In (le_k e, le_kn e) LB) ->
lh_keys (hl_segs L) m es -> lh_keys (hl_segs L) m' es.
Proof. intros LB SP m m' es HPR. apply (lh_keys_presx (fun _ => False) LB SP). apply heap_pres_presx. exact HPR. Qed.
End Pres.

#[using="Type"] Lemma hd_of_nth : forall tbl es, hd_of tbl es = match nth_error es 0 with Some e => ent_addr tbl (le_ix e) | None => 0 end.
Proof. intros tbl [|e es]; reflexivity. Qed.

Section Frame.
Variable segs : list Segment.
Variable fn : fnaddrs.

Definition lh_below (lo t tbl size : Z) (es : list lent) : Prop :=
0 <= t /\ t + 56 <= lo /\ 0 <= tbl /\ tbl + 40 * size <= lo /\ (forall e, In e es -> le_k e + le_kn e <= lo).

#[using="Type"] Lemma lh_keys_frame : forall m m' es W,
lh_keys segs m es -> munch W m m' -> wmono segs m m' ->
(forall e, In e es -> Forall (fun iv => le_k e + le_kn e <= fst iv \/ snd iv <= le_k e) W) ->
lh_keys segs m' es.
Proof.
intros m m' es W KS MU WM DJ. unfold lh_keys in *. rewrite Forall_forall in *.
intros e He. destruct (KS e He) as (Hl & Hnz & junk & C). split; [exact Hl|]. split; [exact Hnz|]. exists junk.
assert (LJ : length ((le_ks e ++ [Z_to_bv 8 0]) ++ junk) = Z.to_nat (le_kn e)) by (destruct C as [[[Wf _] _] _]; rewrite <- app_assoc; exact Wf).
rewrite length_app in LJ. cbn in LJ.
eapply (rw_cells_transport segs W m m'); [exact C | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. specialize (DJ e He). clear -DJ LJ Hl.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in DJ as [D1 DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
Qed.

#[using="Type"] Lemma lh_open_frame : forall ffn m m' t tbl size es svs W lo,
lh_openf segs fn ffn m t tbl size es svs -> lh_below lo t tbl size es ->
munch W m m' -> wmono segs m m' -> Forall (fun iv => lo <= fst iv) W ->
lh_openf segs fn ffn m' t tbl size es svs.
Proof.
intros ffn m m' t tbl size es svs W lo (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen) (Ht0 & Ht & Hb0 & Hb & Hk) MU WM HW.
split; [| split; [| split; [exact LINK | split; [| split; [exact Hsz | split; [exact Hcnt | exact Hlen]]]]]].
- unfold lh_hdrf in *. eapply (rw_cells_transport segs W m m'); [exact HDR | exact MU | exact WM |].
cbn [cells_size csize Nat.add]. clear -HW Ht. induction W as [|[a b] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn in H1. split; [lia | apply IH; exact HW].
- eapply lh_slots_frame; [exact SL | exact MU | exact WM |]. intros i Hi. rewrite <- Hlen in Hb.
clear -HW Hb Hi. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [H1 HW]. cbn in H1. apply Forall_cons; [| apply IH; exact HW]. cbn. unfold ent_addr. left. nia.
- eapply lh_keys_frame; [exact KEYS | exact MU | exact WM |]. intros e He. specialize (Hk e He).
clear -HW Hk. induction W as [|[a b] W IH]; [apply Forall_nil|].
apply Forall_cons_iff in HW as [H1 HW]. cbn in H1. apply Forall_cons; [| apply IH; exact HW]. cbn. lia.
Qed.

#[using="Type"] Lemma lh_key_bytes : forall m es e, lh_keys segs m es -> In e es ->
bytes_at segs m (le_k e) (le_ks e ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) (le_ks e) /\ Z.of_nat (length (le_ks e)) + 1 <= le_kn e.
Proof.
intros m es e KS He. unfold lh_keys in KS. rewrite Forall_forall in KS. destruct (KS e He) as (Hl & Hnz & junk & [[[Wf _] B] _]).
cbn in B. rewrite ?app_nil_r in B.
replace (le_ks e ++ Z_to_bv 8 0 :: junk) with ((le_ks e ++ [Z_to_bv 8 0]) ++ junk) in B by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in B. destruct B as [B _].
split; [exact B|]. split; [|exact Hl].
intros Hin. rewrite Forall_forall in Hnz. specialize (Hnz _ Hin). apply Hnz. reflexivity.
Qed.
End Frame.

Section SlotWriteW.
Variable segs : list Segment.
Definition ivs_miss_slot (tbl : Z) (i : nat) (W : list (Z * Z)) : Prop :=
Forall (fun iv => ent_addr tbl i + 40 <= fst iv \/ snd iv <= ent_addr tbl i) W.

#[using="Type"] Lemma lh_slot_keep : forall m m' tbl svs W i s,
lh_slots segs m tbl svs -> munch W m m' -> wmono segs m m' -> nth_error svs i = Some s -> ivs_miss_slot tbl i W ->
rw_cells segs m' (ent_addr tbl i) (slot_cells s).
Proof.
intros m m' tbl svs W i s SL MU WM E DJ.
eapply (rw_cells_transport segs W m m'); [exact (SL i s E) | exact MU | exact WM |].
rewrite slot_cells_size. change (Z.of_nat 40) with 40. clear -DJ.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in DJ as [D1 DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
Qed.

#[using="Type"] Lemma lh_slots_write1 : forall m m' tbl svs W n s',
lh_slots segs m tbl svs -> (n < length svs)%nat -> munch W m m' -> wmono segs m m' ->
(forall i, i <> n -> (i < length svs)%nat -> ivs_miss_slot tbl i W) ->
rw_cells segs m' (ent_addr tbl n) (slot_cells s') ->
lh_slots segs m' tbl (upd svs n s').
Proof.
intros m m' tbl svs W n s' SL Hn MU WM DJ NEW i s E.
destruct (Nat.eq_dec i n) as [->|NE].
- rewrite nth_error_upd_same in E by exact Hn. injection E as <-. exact NEW.
- rewrite nth_error_upd_other in E by (intros X; apply NE; symmetry; exact X).
eapply lh_slot_keep; [exact SL | exact MU | exact WM | exact E | apply DJ; [exact NE | apply (proj1 (nth_error_Some svs i)); rewrite E; discriminate]].
Qed.

#[using="Type"] Lemma lh_slots_write2 : forall m m' tbl svs W n1 s1 n2 s2,
lh_slots segs m tbl svs -> (n1 < length svs)%nat -> (n2 < length svs)%nat -> n1 <> n2 ->
munch W m m' -> wmono segs m m' ->
(forall i, i <> n1 -> i <> n2 -> (i < length svs)%nat -> ivs_miss_slot tbl i W) ->
rw_cells segs m' (ent_addr tbl n1) (slot_cells s1) -> rw_cells segs m' (ent_addr tbl n2) (slot_cells s2) ->
lh_slots segs m' tbl (upd (upd svs n1 s1) n2 s2).
Proof.
intros m m' tbl svs W n1 s1 n2 s2 SL H1 H2 NE MU WM DJ C1 C2 i s E.
destruct (Nat.eq_dec i n2) as [->|NE2].
- rewrite nth_error_upd_same in E by (rewrite upd_length; exact H2). injection E as <-. exact C2.
- rewrite nth_error_upd_other in E by (intros X; apply NE2; symmetry; exact X).
destruct (Nat.eq_dec i n1) as [->|NE1].
+ rewrite nth_error_upd_same in E by exact H1. injection E as <-. exact C1.
+ rewrite nth_error_upd_other in E by (intros X; apply NE1; symmetry; exact X).
eapply lh_slot_keep; [exact SL | exact MU | exact WM | exact E | apply DJ; [exact NE1 | exact NE2 | apply (proj1 (nth_error_Some svs i)); rewrite E; discriminate]].
Qed.
End SlotWriteW.

Section HeapFacts.

Definition kblk (e : lent) : blk := (le_k e, le_kn e).

#[using="Type"] Lemma lh_heap_facts : forall L (HIx : heap_iface L) A t tbl size es LB m md,
HEAP L HIx A (lh_blocks t tbl size es ++ LB) m md ->
(t mod 16 = 0 /\ 0 < t /\ t + 56 <= alloc_ceiling /\ (t + 56 <= hl_img_lo L \/ hl_img_hi L <= t))
/\ (tbl mod 16 = 0 /\ 0 < tbl /\ tbl + 40 * size <= alloc_ceiling /\ (tbl + 40 * size <= hl_img_lo L \/ hl_img_hi L <= tbl))
/\ (t + 56 <= tbl \/ tbl + 40 * size <= t)
/\ (forall e, In e es ->
0 <= le_kn e /\ 0 < le_k e /\ le_k e + le_kn e <= alloc_ceiling /\ (le_k e + le_kn e <= hl_img_lo L \/ hl_img_hi L <= le_k e)
/\ (t + 56 <= le_k e \/ le_k e + le_kn e <= t) /\ (tbl + 40 * size <= le_k e \/ le_k e + le_kn e <= tbl)).
Proof.
intros L HIx A t tbl size es LB m md HP. unfold lh_blocks in HP. cbn [app] in HP.
destruct (blocks2 L HIx _ _ _ _ _ _ _ _ HP) as (F1 & F2 & F12). split; [exact F1|]. split; [exact F2|]. split; [exact F12|].
intros e He.
assert (Hin : In (le_k e, le_kn e) ((t, 56) :: (tbl, 40 * size) :: map (fun e => (le_k e, le_kn e)) es ++ LB)).
{ right; right. apply in_or_app. left. apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heap_blk L HIx _ _ _ _ _ _ HP Hin) as (Hn & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img L HIx _ _ _ _ _ _ HP Hin) as Himg.
pose proof (heap_blk_nodup L HIx _ _ _ _ HP) as ND. cbn [map blk_addr fst] in ND.
inversion ND as [|x l Hnt ND1]; subst. inversion ND1 as [|y l' Hntb ND2]; subst.
assert (NEt : t <> le_k e).
{ intros E. apply Hnt. rewrite E. right. rewrite map_app. apply in_or_app. left. apply in_map_iff. exists (le_k e, le_kn e). split; [reflexivity|].
apply in_map_iff. exists e. split; [reflexivity | exact He]. }
assert (NEb : tbl <> le_k e).
{ intros E. apply Hntb. rewrite E. rewrite map_app. apply in_or_app. left. apply in_map_iff. exists (le_k e, le_kn e). split; [reflexivity|].
apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heap_blk_disjoint L HIx _ _ _ _ t 56 (le_k e) (le_kn e) HP ltac:(left; reflexivity) Hin NEt) as D1.
pose proof (heap_blk_disjoint L HIx _ _ _ _ tbl (40 * size) (le_k e) (le_kn e) HP ltac:(right; left; reflexivity) Hin NEb) as D2.
repeat split; try assumption; lia.
Qed.
End HeapFacts.

Section GlobFrame.
Variable segs : list Segment.
Variable fn : fnaddrs.
Variables (ghash ggot gvdso : Z).
Variable vdso_ok : Z -> Prop.
#[using="Type"] Lemma lh_glob_frame : forall m m' W,
lh_glob segs fn ghash ggot gvdso vdso_ok m -> munch W m m' -> wmono segs m m' ->
Forall (fun iv => (ghash + 12 <= fst iv \/ snd iv <= ghash) /\ (ggot + 8 <= fst iv \/ snd iv <= ggot) /\ (gvdso + 8 <= fst iv \/ snd iv <= gvdso)) W ->
lh_glob segs fn ghash ggot gvdso vdso_ok m'.
Proof.
intros m m' W ([seed G1] & G2 & (vf & G3 & VF)) MU WM DJ. split; [| split].
- exists seed. eapply (rw_cells_transport segs W m m'); [exact G1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
clear -DJ. induction W as [|[a b] W IH]; cbn; [exact I|]. apply Forall_cons_iff in DJ as [(D1 & _ & _) DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
- eapply (rw_cells_transport segs W m m'); [exact G2 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
clear -DJ. induction W as [|[a b] W IH]; cbn; [exact I|]. apply Forall_cons_iff in DJ as [(_ & D1 & _) DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
- exists vf. split; [| exact VF]. eapply (rw_cells_transport segs W m m'); [exact G3 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
clear -DJ. induction W as [|[a b] W IH]; cbn; [exact I|]. apply Forall_cons_iff in DJ as [(_ & _ & D1) DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
Qed.

#[using="Type"] Lemma lh_newkey_facts : forall L (HIx : heap_iface L) A t tbl size es k kn LB m md,
HEAP L HIx A (lh_blocks t tbl size es ++ (k, kn) :: LB) m md ->
0 <= kn /\ 0 < k /\ k + kn <= alloc_ceiling /\ (k + kn <= hl_img_lo L \/ hl_img_hi L <= k)
/\ (t + 56 <= k \/ k + kn <= t) /\ (tbl + 40 * size <= k \/ k + kn <= tbl) /\ ~ In k (map le_k es).
Proof.
intros L HIx A t tbl size es k kn LB m md HP.
assert (HinK : In (k, kn) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; right; left; reflexivity).
pose proof (heap_blk L HIx _ _ _ _ k kn HP HinK) as (Hn & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img L HIx _ _ _ _ k kn HP HinK) as Himg.
pose proof (heap_blk_nodup L HIx _ _ _ _ HP) as ND.
assert (NT : t <> k).
{ intros ->. eapply (nodup_prefix_suffix (lh_blocks k tbl size es) ((k, kn) :: LB) k 56 kn ND); [left; reflexivity | left; reflexivity]. }
assert (NB : tbl <> k).
{ intros ->. eapply (nodup_prefix_suffix (lh_blocks t k size es) ((k, kn) :: LB) k (40 * size) kn ND); [right; left; reflexivity | left; reflexivity]. }
assert (NK : ~ In k (map le_k es)).
{ intros IN. apply in_map_iff in IN as (e & <- & He).
eapply (nodup_prefix_suffix (lh_blocks t tbl size es) ((le_k e, kn) :: LB) (le_k e) (le_kn e) kn ND); [| left; reflexivity].
right; right. apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heap_blk_disjoint L HIx _ _ _ _ t 56 k kn HP ltac:(left; reflexivity) HinK NT) as D1.
pose proof (heap_blk_disjoint L HIx _ _ _ _ tbl (40 * size) k kn HP ltac:(right; left; reflexivity) HinK NB) as D2.
repeat split; try assumption; lia.
Qed.
End GlobFrame.

Section OpenPres.
Variable L : heap_layout.
Variable fn : fnaddrs.

#[using="Type"] Lemma lh_open_presx : forall X ffn LB SP m m' t tbl size es svs,
heap_presx L X LB SP m m' -> (forall b, In b (lh_blocks t tbl size es) -> In b LB) ->
lh_openf (hl_segs L) fn ffn m t tbl size es svs -> lh_openf (hl_segs L) fn ffn m' t tbl size es svs.
Proof.
intros X ffn LB SP m m' t tbl size es svs HPR SUB (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
split; [| split; [| split; [exact LINK | split; [| split; [exact Hsz | split; [exact Hcnt | exact Hlen]]]]]].
- unfold lh_hdrf in *. eapply (heap_presx_rw_cells L); [exact HPR | exact HDR |].
eapply client_rangex_block; [apply SUB; left; reflexivity | lia | cbn; lia].
- eapply lh_slots_presx; [exact HPR | apply SUB; right; left; reflexivity | exact Hlen | exact SL].
- eapply lh_keys_presx; [exact HPR | | exact KEYS]. intros e He. apply SUB. right; right. apply in_map_iff. exists e. split; [reflexivity | exact He].
Qed.
#[using="Type"] Lemma lh_open_pres : forall ffn LB SP m m' t tbl size es svs,
heap_pres L LB SP m m' -> (forall b, In b (lh_blocks t tbl size es) -> In b LB) ->
lh_openf (hl_segs L) fn ffn m t tbl size es svs -> lh_openf (hl_segs L) fn ffn m' t tbl size es svs.
Proof. intros ffn LB SP m m' t tbl size es svs HPR. apply (lh_open_presx (fun _ => False) ffn LB SP). apply heap_pres_presx. exact HPR. Qed.
End OpenPres.

End RC__1.
