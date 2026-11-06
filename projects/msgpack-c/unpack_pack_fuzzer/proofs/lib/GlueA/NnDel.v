(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AmallocNnC.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX AmallocNnC.

Lemma den_prist_lo : forall E, bv_unsigned (den E PRIST_LO) = PRIST_BASE.
Proof. intros E. unfold PRIST_LO. rewrite unsigned_VL. vm_compute. reflexivity. Qed.
Lemma den_VL0 : forall E, bv_unsigned (den E (VL wzero)) = 0.
Proof. intros E. rewrite unsigned_VL. vm_compute. reflexivity. Qed.

Lemma del_win3_split : forall E0 m ws ws',
  del_win3 m ws PRIST_LO (VL wzero) (VL wzero) = Some ws' -> (3 * m <= length ws)%nat ->
  exists l1 l2, wins_of E0 m ws = l1 ++ prist_win :: l2 /\ wins_of E0 (pred m) ws' = l1 ++ l2
    /\ length ws' = (length ws - 3)%nat /\ (1 <= m)%nat.
Proof.
  intros E0 m. induction m as [|m IH]; intros ws ws' H L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_win3] in H. cbn [length] in L |- *.
  destruct (sv_eqb wlo PRIST_LO && sv_eqb ln (VL wzero) && sv_eqb kdv (VL wzero)) eqn:C.
  - injection H as <-. apply andb_prop in C as [C12 C3]. apply andb_prop in C12 as [C1 C2].
    apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. apply sv_eqb_eq in C3. subst wlo ln kdv.
    exists [], (wins_of E0 m ws0). rewrite wins_of_cons, den_prist_lo, den_VL0. cbn [app pred].
    split; [reflexivity|]. split; [reflexivity|]. split; lia.
  - destruct (del_win3 m ws0 PRIST_LO (VL wzero) (VL wzero)) as [ws''|] eqn:D; [|discriminate]. injection H as <-.
    destruct (IH ws0 ws'' D ltac:(lia)) as (l1 & l2 & W1 & W2 & LEN & M1).
    destruct m as [|m']; [lia|]. cbn [pred] in *.
    exists (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 kdv)) :: l1), l2.
    rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|]. rewrite wins_of_cons, W2. split; [reflexivity|]. cbn [length]. split; lia.
Qed.

Lemma heap_del_prist_facts : forall E0 hargs h',
  heap_del_prist hargs = Some h' ->
  exists md A nw rest n ws' l1 l2,
    hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat
    /\ h' = VL md :: A :: VL (wsub nw wone) :: ws' ++ skipn (3 * n) rest
    /\ wins_of E0 n rest = l1 ++ prist_win :: l2
    /\ decode (map (den E0) hargs) = Some (w2Z md, den E0 A, l1 ++ prist_win :: l2, map (den E0) (skipn (3 * n) rest))
    /\ decode (map (den E0) h') = Some (w2Z md, den E0 A, l1 ++ l2, map (den E0) (skipn (3 * n) rest)).
Proof.
  intros E0 hargs h' H. unfold heap_del_prist in H.
  destruct (heap_nwin hargs) as [n|] eqn:HN; [|discriminate].
  destruct (heap_nwin_shape hargs n HN) as (md & A & nw & rest & -> & T & N & L).
  destruct (del_win3 n (firstn (3 * n) rest) PRIST_LO (VL wzero) (VL wzero)) as [ws'|] eqn:D; [|discriminate]. injection H as <-.
  destruct (del_win3_split E0 n (firstn (3 * n) rest) ws' D ltac:(rewrite firstn_length_le by lia; lia)) as (l1 & l2 & W1 & W2 & LEN & M1).
  rewrite firstn_length_le in LEN by lia.
  destruct (HeapCtrB.wsub_one_small nw T ltac:(pose proof (Uint63.to_Z_bounded (wl nw)); lia)) as [T' E'].
  assert (W1' : wins_of E0 n rest = l1 ++ prist_win :: l2).
  { rewrite <- W1. rewrite <- (app_nil_r (firstn (3 * n) rest)) at 1. symmetry. apply (wins_of_firstn E0 n rest []). lia. }
  exists md, A, nw, rest, n, ws', l1, l2.
  split; [reflexivity|]. split; [exact T|]. split; [exact N|]. split; [exact L|]. split; [reflexivity|]. split; [exact W1'|].
  split; [rewrite <- W1'; exact (decode_hargs E0 md A nw rest n T N L)|].
  assert (SK : skipn (3 * pred n) (ws' ++ skipn (3 * n) rest) = skipn (3 * n) rest) by (apply skipn_app_exact; lia).
  change (n + (n + (n + 0)))%nat with (3 * n)%nat.
  rewrite (decode_hargs E0 md A (wsub nw wone) (ws' ++ skipn (3 * n) rest) (pred n) T' ltac:(rewrite E', N; lia) ltac:(rewrite length_app; lia)).
  rewrite SK, (HeapCtrB.wins_of_prefix E0 (pred n) ws' _ ltac:(lia)), W2. reflexivity.
Qed.

Fixpoint zmax (ws : list window) : Z := match ws with [] => 0 | w :: l => Z.max (w_lo w) (zmax l) end.
Lemma zmax_ge : forall ws w, In w ws -> w_lo w <= zmax ws.
Proof. induction ws as [|x l IH]; intros w H; [destruct H|]. destruct H as [<-|H]; cbn [zmax]; [lia| specialize (IH w H); lia]. Qed.
Lemma fresh_k0 : forall ws, exists w0, w_kind w0 = K_STACK /\ ~ In w0 ws.
Proof. intros ws. exists (Win (zmax ws + 1) 0 K_STACK). split; [reflexivity|]. intros H. apply zmax_ge in H. cbn [w_lo] in H. lia. Qed.

Section NnDel.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.

Hypothesis Cw_k0_del : forall md ca LB ws ws' m w0, cw_holds Cw md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cw_holds Cw md ca LB ws' m.

Let ties_prist_del := Op.ties_prist_del AI ACCT UNIV.

Lemma cw_del_one : forall md ca LB l1 l2 m, cw_holds Cw md ca LB (l1 ++ prist_win :: l2) m -> cw_holds Cw md ca LB (l1 ++ l2) m.
Proof.
  intros md ca LB l1 l2 m H.
  destruct (in_dec window_eq_dec prist_win (l1 ++ l2)) as [I|NI].
  - destruct (fresh_k0 (l1 ++ prist_win :: l2)) as (w0 & K0 & NW).
    apply (Cw_k0_del md ca LB _ (l1 ++ l2) m w0 H K0). intros w. split.
    + intros Hw. split; [apply in_app_iff; apply in_app_iff in Hw as [X|X]; [left; exact X| right; right; exact X]|].
      intros ->. apply NW. apply in_app_iff. apply in_app_iff in Hw as [X|X]; [left; exact X| right; right; exact X].
    + intros [Hw _]. apply in_app_iff in Hw as [X|[<-|X]]; [apply in_app_iff; left; exact X| exact I| apply in_app_iff; right; exact X].
  - apply (Cw_k0_del md ca LB _ (l1 ++ l2) m prist_win H eq_refl). intros w. split.
    + intros Hw. split; [apply in_app_iff; apply in_app_iff in Hw as [X|X]; [left; exact X| right; right; exact X]|].
      intros ->. exact (NI Hw).
    + intros [Hw NE]. apply in_app_iff in Hw as [X|[X|X]]; [apply in_app_iff; left; exact X| exfalso; exact (NE (eq_sym X))| apply in_app_iff; right; exact X].
Qed.

Lemma in_ws_del : forall l1 l2 a, in_ws (l1 ++ prist_win :: l2) a <-> in_ws (l1 ++ l2) a.
Proof.
  intros l1 l2 a. unfold in_ws. rewrite !map_app. cbn [map]. rewrite !in_ivs_app, in_ivs_cons.
  unfold in_iv, w_iv, prist_win. cbn [fst snd w_lo w_len]. split; [intros [X|[X|X]]; [left; exact X| lia| right; exact X]| intros [X|X]; [left; exact X| right; right; exact X]].
Qed.
Lemma heap_ws_del : forall l1 l2, heap_ws (l1 ++ prist_win :: l2) = heap_ws (l1 ++ l2).
Proof. intros l1 l2. unfold heap_ws. rewrite !filter_app. cbn [filter prist_win w_kind]. reflexivity. Qed.

Theorem del_prist_ok : forall E st ms mo, st_ok asegs OPS E st ms mo -> st_ok asegs OPS E (del_prist st) ms mo.
Proof.
  intros E st ms mo HS. unfold del_prist.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [| exact HS].
  destruct (heap_del_prist hargs) as [h'|] eqn:HD; [| exact HS].
  destruct (heap_del_prist_facts E hargs h' HD) as (md & A & nw & rest & n & ws' & l1 & l2 & EH & T & N & L & EH' & W1 & DEC & DEC').
  destruct (find_op_split HEAP_ID (s_ops st) hargs Hf) as (o1 & o2 & EO & F1).
  assert (SO : set_op HEAP_ID h' (s_ops st) = o1 ++ OpI HEAP_ID h' :: o2) by (rewrite EO; exact (set_op_split HEAP_ID h' o1 o2 hargs F1)).
  pose proof (so_ops _ _ _ _ _ _ HS) as HO. pose proof (so_apart _ _ _ _ _ _ HS) as HA. pose proof (so_cover _ _ _ _ _ _ HS) as HC.
  destruct HS. constructor; try assumption; destruct st as [pc0 rf ff resv regs facts ops priv nx]; cbn [set_ops s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *; try assumption.
  -   rewrite SO. rewrite EO in HO. unfold ops_hold in *. apply Forall_app3 in HO as (H1 & H2 & H3). apply Forall_app3.
    split; [exact H1|]. split; [| exact H3]. cbn [op_id op_args] in *.
    apply OPS_holds1 in H2. apply OPS_holds1. destruct H2 as (md0 & aw & ws & ca & LB & W & D & AW & WF & CWH & TI).
    rewrite DEC in D. injection D as <- <- <- <-.
    exists (w2Z md), (den E A), (l1 ++ l2), (map (den E) (skipn (3 * n) rest)), LB, W.
    split; [exact DEC'|]. split; [exact AW|].
    split. { unfold windows_wf in *. apply Forall_app in WF as [WF1 WF2]. apply Forall_app. split; [exact WF1| inversion WF2; assumption]. }
    split; [exact (cw_del_one _ _ _ _ _ _ CWH)|].
    apply (ties_prist_del W _ _ _ _ _ (l1 ++ l2) AW TI).
    + intros w Hw. apply in_app_iff. apply in_app_iff in Hw as [X|X]; [left; exact X| right; right; exact X].
    + intros w Hw NE. apply in_app_iff. apply in_app_iff in Hw as [X|[X|X]]; [left; exact X| exfalso; exact (NE (eq_sym X))| right; exact X].
  -   rewrite SO. rewrite EO in HA. unfold ops_apart in *. apply Forall_app3 in HA as (H1 & H2 & H3). apply Forall_app3.
    split; [exact H1|]. split; [| exact H3]. cbn [op_id op_args] in *. intros a Ha. apply H2.
    rewrite OPS_fp1 in Ha |- *. apply (fp_spec IMGX _ _ _ _ _ a DEC). apply (fp_spec IMGX _ _ _ _ _ a DEC') in Ha as (R & NI & NW).
    split; [exact R|]. split; [exact NI|]. intros X. apply NW. apply in_ws_del. exact X.
  -   intros a Ha. specialize (HC a Ha). destruct HC as [C0|C1]; [left; exact C0| right].
    rewrite SO. rewrite EO in C1. unfold insts in *. rewrite map_app in *. cbn [map op_id op_args] in *.
    apply Exists_app in C1 as [X|X]; [apply Exists_app; left; exact X|]. apply Exists_app. right.
    apply Exists_cons in X as [X|X]; [| apply Exists_cons; right; exact X]. apply Exists_cons. left. cbn [fst snd] in *.
    apply OPS_cov1 in X. apply OPS_cov1. destruct X as (ID & md0 & aw & ws & ca & D & CV). split; [exact ID|].
    rewrite DEC in D. injection D as <- <- <- <-.
    exists (w2Z md), (den E A), (l1 ++ l2), (map (den E) (skipn (3 * n) rest)). split; [exact DEC'|].
    destruct CV as [CV|CV]; [left| right; exact CV]. rewrite <- heap_ws_del. exact CV.
Qed.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Theorem prist_drop_sound : forall pc, contract_sound asegs OPS MP PB (prist_drop_c pc).
Proof.
  intros pc st sts Hpc HAP K E ms mo HS HMP HPB HK. cbn [prist_drop_c c_apply] in HAP. unfold prist_drop_apply in HAP. injection HAP as <-.
  apply (HK (del_prist st) (or_introl eq_refl) E ms mo); [| exact HMP| exact (del_prist_ok E st ms mo HS)].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.

Lemma del_prist_pc : forall st, s_pc (del_prist st) = s_pc st.
Proof. intros st. unfold del_prist. destruct (find_op HEAP_ID (s_ops st)); [| reflexivity]. destruct (heap_del_prist l); [| reflexivity]. destruct st; reflexivity. Qed.
Lemma del_prist_facts : forall st, s_facts (del_prist st) = s_facts st.
Proof. intros st. unfold del_prist. destruct (find_op HEAP_ID (s_ops st)); [| reflexivity]. destruct (heap_del_prist l); [| reflexivity]. destruct st; reflexivity. Qed.
Lemma del_prist_getr : forall st r, getr (del_prist st) r = getr st r.
Proof. intros st r. unfold del_prist. destruct (find_op HEAP_ID (s_ops st)); [| reflexivity]. destruct (heap_del_prist l); [| reflexivity]. destruct st; reflexivity. Qed.
Lemma del_prist_next : forall st, s_next (del_prist st) = s_next st.
Proof. intros st. unfold del_prist. destruct (find_op HEAP_ID (s_ops st)); [| reflexivity]. destruct (heap_del_prist l); [| reflexivity]. destruct st; reflexivity. Qed.
End NnDel.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import AmallocNnC.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX AmallocNnC.TwinB.AmallocNnC.

Lemma den_prist_lo : forall E, bv_unsigned (den E PRIST_LO) = PRIST_BASE.
Proof. intros E. unfold PRIST_LO. rewrite unsigned_VL. vm_compute. reflexivity. Qed.
Lemma den_VL0 : forall E, bv_unsigned (den E (VL wzero)) = 0.
Proof. intros E. rewrite unsigned_VL. vm_compute. reflexivity. Qed.

Lemma del_win3_split : forall E0 m ws ws',
  del_win3 m ws PRIST_LO (VL wzero) (VL wzero) = Some ws' -> (3 * m <= length ws)%nat ->
  exists l1 l2, wins_of E0 m ws = l1 ++ prist_win :: l2 /\ wins_of E0 (pred m) ws' = l1 ++ l2
    /\ length ws' = (length ws - 3)%nat /\ (1 <= m)%nat.
Proof.
  intros E0 m. induction m as [|m IH]; intros ws ws' H L; [cbn in H; destruct ws; discriminate|].
  destruct ws as [|wlo [|ln [|kdv ws0]]]; try (cbn in H; discriminate). cbn [del_win3] in H. cbn [length] in L |- *.
  destruct (sv_eqb wlo PRIST_LO && sv_eqb ln (VL wzero) && sv_eqb kdv (VL wzero)) eqn:C.
  - injection H as <-. apply andb_prop in C as [C12 C3]. apply andb_prop in C12 as [C1 C2].
    apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. apply sv_eqb_eq in C3. subst wlo ln kdv.
    exists [], (wins_of E0 m ws0). rewrite wins_of_cons, den_prist_lo, den_VL0. cbn [app pred].
    split; [reflexivity|]. split; [reflexivity|]. split; lia.
  - destruct (del_win3 m ws0 PRIST_LO (VL wzero) (VL wzero)) as [ws''|] eqn:D; [|discriminate]. injection H as <-.
    destruct (IH ws0 ws'' D ltac:(lia)) as (l1 & l2 & W1 & W2 & LEN & M1).
    destruct m as [|m']; [lia|]. cbn [pred] in *.
    exists (Win (bv_unsigned (den E0 wlo)) (bv_unsigned (den E0 ln)) (bv_unsigned (den E0 kdv)) :: l1), l2.
    rewrite wins_of_cons, W1. cbn [app]. split; [reflexivity|]. rewrite wins_of_cons, W2. split; [reflexivity|]. cbn [length]. split; lia.
Qed.

Lemma heap_del_prist_facts : forall E0 hargs h',
  heap_del_prist hargs = Some h' ->
  exists md A nw rest n ws' l1 l2,
    hargs = VL md :: A :: VL nw :: rest /\ wt nw = false /\ n = Z.to_nat (to_Z (wl nw)) /\ (3 * n <= length rest)%nat
    /\ h' = VL md :: A :: VL (wsub nw wone) :: ws' ++ skipn (3 * n) rest
    /\ wins_of E0 n rest = l1 ++ prist_win :: l2
    /\ decode (map (den E0) hargs) = Some (w2Z md, den E0 A, l1 ++ prist_win :: l2, map (den E0) (skipn (3 * n) rest))
    /\ decode (map (den E0) h') = Some (w2Z md, den E0 A, l1 ++ l2, map (den E0) (skipn (3 * n) rest)).
Proof.
  intros E0 hargs h' H. unfold heap_del_prist in H.
  destruct (heap_nwin hargs) as [n|] eqn:HN; [|discriminate].
  destruct (heap_nwin_shape hargs n HN) as (md & A & nw & rest & -> & T & N & L).
  destruct (del_win3 n (firstn (3 * n) rest) PRIST_LO (VL wzero) (VL wzero)) as [ws'|] eqn:D; [|discriminate]. injection H as <-.
  destruct (del_win3_split E0 n (firstn (3 * n) rest) ws' D ltac:(rewrite firstn_length_le by lia; lia)) as (l1 & l2 & W1 & W2 & LEN & M1).
  rewrite firstn_length_le in LEN by lia.
  destruct (HeapCtrB.TwinB.wsub_one_small nw T ltac:(pose proof (Uint63.to_Z_bounded (wl nw)); lia)) as [T' E'].
  assert (W1' : wins_of E0 n rest = l1 ++ prist_win :: l2).
  { rewrite <- W1. rewrite <- (app_nil_r (firstn (3 * n) rest)) at 1. symmetry. apply (wins_of_firstn E0 n rest []). lia. }
  exists md, A, nw, rest, n, ws', l1, l2.
  split; [reflexivity|]. split; [exact T|]. split; [exact N|]. split; [exact L|]. split; [reflexivity|]. split; [exact W1'|].
  split; [rewrite <- W1'; exact (decode_hargs E0 md A nw rest n T N L)|].
  assert (SK : skipn (3 * pred n) (ws' ++ skipn (3 * n) rest) = skipn (3 * n) rest) by (apply skipn_app_exact; lia).
  change (n + (n + (n + 0)))%nat with (3 * n)%nat.
  rewrite (decode_hargs E0 md A (wsub nw wone) (ws' ++ skipn (3 * n) rest) (pred n) T' ltac:(rewrite E', N; lia) ltac:(rewrite length_app; lia)).
  rewrite SK, (HeapCtrB.TwinB.wins_of_prefix E0 (pred n) ws' _ ltac:(lia)), W2. reflexivity.
Qed.

Fixpoint zmax (ws : list window) : Z := match ws with [] => 0 | w :: l => Z.max (w_lo w) (zmax l) end.
Lemma zmax_ge : forall ws w, In w ws -> w_lo w <= zmax ws.
Proof. induction ws as [|x l IH]; intros w H; [destruct H|]. destruct H as [<-|H]; cbn [zmax]; [lia| specialize (IH w H); lia]. Qed.
Lemma fresh_k0 : forall ws, exists w0, w_kind w0 = K_STACK /\ ~ In w0 ws.
Proof. intros ws. exists (Win (zmax ws + 1) 0 K_STACK). split; [reflexivity|]. intros H. apply zmax_ge in H. cbn [w_lo] in H. lia. Qed.

Section NnDel.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.

Hypothesis Cw_k0_del : forall md ca LB ws ws' m w0, cw_holds Cw md ca LB ws m -> w_kind w0 = K_STACK ->
  (forall w, In w ws' <-> In w ws /\ w <> w0) -> cw_holds Cw md ca LB ws' m.

Let ties_prist_del := Op.TwinB.ties_prist_del AI ACCT UNIV.

Lemma cw_del_one : forall md ca LB l1 l2 m, cw_holds Cw md ca LB (l1 ++ prist_win :: l2) m -> cw_holds Cw md ca LB (l1 ++ l2) m.
Proof.
  intros md ca LB l1 l2 m H.
  destruct (in_dec window_eq_dec prist_win (l1 ++ l2)) as [I|NI].
  - destruct (fresh_k0 (l1 ++ prist_win :: l2)) as (w0 & K0 & NW).
    apply (Cw_k0_del md ca LB _ (l1 ++ l2) m w0 H K0). intros w. split.
    + intros Hw. split; [apply in_app_iff; apply in_app_iff in Hw as [X|X]; [left; exact X| right; right; exact X]|].
      intros ->. apply NW. apply in_app_iff. apply in_app_iff in Hw as [X|X]; [left; exact X| right; right; exact X].
    + intros [Hw _]. apply in_app_iff in Hw as [X|[<-|X]]; [apply in_app_iff; left; exact X| exact I| apply in_app_iff; right; exact X].
  - apply (Cw_k0_del md ca LB _ (l1 ++ l2) m prist_win H eq_refl). intros w. split.
    + intros Hw. split; [apply in_app_iff; apply in_app_iff in Hw as [X|X]; [left; exact X| right; right; exact X]|].
      intros ->. exact (NI Hw).
    + intros [Hw NE]. apply in_app_iff in Hw as [X|[X|X]]; [apply in_app_iff; left; exact X| exfalso; exact (NE (eq_sym X))| apply in_app_iff; right; exact X].
Qed.

Lemma in_ws_del : forall l1 l2 a, in_ws (l1 ++ prist_win :: l2) a <-> in_ws (l1 ++ l2) a.
Proof.
  intros l1 l2 a. unfold in_ws. rewrite !map_app. cbn [map]. rewrite !in_ivs_app, in_ivs_cons.
  unfold in_iv, w_iv, prist_win. cbn [fst snd w_lo w_len]. split; [intros [X|[X|X]]; [left; exact X| lia| right; exact X]| intros [X|X]; [left; exact X| right; right; exact X]].
Qed.
Lemma heap_ws_del : forall l1 l2, heap_ws (l1 ++ prist_win :: l2) = heap_ws (l1 ++ l2).
Proof. intros l1 l2. unfold heap_ws. rewrite !filter_app. cbn [filter prist_win w_kind]. reflexivity. Qed.

Theorem del_prist_ok : forall E st ms mo, st_ok bsegs OPS E st ms mo -> st_ok bsegs OPS E (del_prist st) ms mo.
Proof.
  intros E st ms mo HS. unfold del_prist.
  destruct (find_op HEAP_ID (s_ops st)) as [hargs|] eqn:Hf; [| exact HS].
  destruct (heap_del_prist hargs) as [h'|] eqn:HD; [| exact HS].
  destruct (heap_del_prist_facts E hargs h' HD) as (md & A & nw & rest & n & ws' & l1 & l2 & EH & T & N & L & EH' & W1 & DEC & DEC').
  destruct (find_op_split HEAP_ID (s_ops st) hargs Hf) as (o1 & o2 & EO & F1).
  assert (SO : set_op HEAP_ID h' (s_ops st) = o1 ++ OpI HEAP_ID h' :: o2) by (rewrite EO; exact (set_op_split HEAP_ID h' o1 o2 hargs F1)).
  pose proof (so_ops _ _ _ _ _ _ HS) as HO. pose proof (so_apart _ _ _ _ _ _ HS) as HA. pose proof (so_cover _ _ _ _ _ _ HS) as HC.
  destruct HS. constructor; try assumption; destruct st as [pc0 rf ff resv regs facts ops priv nx]; cbn [set_ops s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next] in *; try assumption.
  -   rewrite SO. rewrite EO in HO. unfold ops_hold in *. apply Forall_app3 in HO as (H1 & H2 & H3). apply Forall_app3.
    split; [exact H1|]. split; [| exact H3]. cbn [op_id op_args] in *.
    apply OPS_holds1 in H2. apply OPS_holds1. destruct H2 as (md0 & aw & ws & ca & LB & W & D & AW & WF & CWH & TI).
    rewrite DEC in D. injection D as <- <- <- <-.
    exists (w2Z md), (den E A), (l1 ++ l2), (map (den E) (skipn (3 * n) rest)), LB, W.
    split; [exact DEC'|]. split; [exact AW|].
    split. { unfold windows_wf in *. apply Forall_app in WF as [WF1 WF2]. apply Forall_app. split; [exact WF1| inversion WF2; assumption]. }
    split; [exact (cw_del_one _ _ _ _ _ _ CWH)|].
    apply (ties_prist_del W _ _ _ _ _ (l1 ++ l2) AW TI).
    + intros w Hw. apply in_app_iff. apply in_app_iff in Hw as [X|X]; [left; exact X| right; right; exact X].
    + intros w Hw NE. apply in_app_iff. apply in_app_iff in Hw as [X|[X|X]]; [left; exact X| exfalso; exact (NE (eq_sym X))| right; exact X].
  -   rewrite SO. rewrite EO in HA. unfold ops_apart in *. apply Forall_app3 in HA as (H1 & H2 & H3). apply Forall_app3.
    split; [exact H1|]. split; [| exact H3]. cbn [op_id op_args] in *. intros a Ha. apply H2.
    rewrite OPS_fp1 in Ha |- *. apply (fp_spec IMGX _ _ _ _ _ a DEC). apply (fp_spec IMGX _ _ _ _ _ a DEC') in Ha as (R & NI & NW).
    split; [exact R|]. split; [exact NI|]. intros X. apply NW. apply in_ws_del. exact X.
  -   intros a Ha. specialize (HC a Ha). destruct HC as [C0|C1]; [left; exact C0| right].
    rewrite SO. rewrite EO in C1. unfold insts in *. rewrite map_app in *. cbn [map op_id op_args] in *.
    apply Exists_app in C1 as [X|X]; [apply Exists_app; left; exact X|]. apply Exists_app. right.
    apply Exists_cons in X as [X|X]; [| apply Exists_cons; right; exact X]. apply Exists_cons. left. cbn [fst snd] in *.
    apply OPS_cov1 in X. apply OPS_cov1. destruct X as (ID & md0 & aw & ws & ca & D & CV). split; [exact ID|].
    rewrite DEC in D. injection D as <- <- <- <-.
    exists (w2Z md), (den E A), (l1 ++ l2), (map (den E) (skipn (3 * n) rest)). split; [exact DEC'|].
    destruct CV as [CV|CV]; [left| right; exact CV]. rewrite <- heap_ws_del. exact CV.
Qed.

Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Theorem prist_drop_sound : forall pc, contract_sound bsegs OPS MP PB (prist_drop_c pc).
Proof.
  intros pc st sts Hpc HAP K E ms mo HS HMP HPB HK. cbn [prist_drop_c c_apply] in HAP. unfold prist_drop_apply in HAP. injection HAP as <-.
  apply (HK (del_prist st) (or_introl eq_refl) E ms mo); [| exact HMP| exact (del_prist_ok E st ms mo HS)].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.

Lemma del_prist_pc : forall st, s_pc (del_prist st) = s_pc st.
Proof. intros st. unfold del_prist. destruct (find_op HEAP_ID (s_ops st)); [| reflexivity]. destruct (heap_del_prist l); [| reflexivity]. destruct st; reflexivity. Qed.
Lemma del_prist_facts : forall st, s_facts (del_prist st) = s_facts st.
Proof. intros st. unfold del_prist. destruct (find_op HEAP_ID (s_ops st)); [| reflexivity]. destruct (heap_del_prist l); [| reflexivity]. destruct st; reflexivity. Qed.
Lemma del_prist_getr : forall st r, getr (del_prist st) r = getr st r.
Proof. intros st r. unfold del_prist. destruct (find_op HEAP_ID (s_ops st)); [| reflexivity]. destruct (heap_del_prist l); [| reflexivity]. destruct st; reflexivity. Qed.
Lemma del_prist_next : forall st, s_next (del_prist st) = s_next st.
Proof. intros st. unfold del_prist. destruct (find_op HEAP_ID (s_ops st)); [| reflexivity]. destruct (heap_del_prist l); [| reflexivity]. destruct st; reflexivity. Qed.
End NnDel.
End TwinB.
