(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 649 of its 741 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/CF/WriterRet.v, with its module paths and module names changed; 1746 of its 1850 lines of code are new or changed and 637 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require PropExec Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import MState Mem Exec Frame Cells Regs6ss RegisterBridge FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import put_c put_kb WriterRet WriterCall indent_c indent.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import snprintf_c strlen_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import put_string_c write_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import write_value_blocks WriterNode.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import WVEntry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma resume_mkR : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) F pc fc rv m ro x regs1,
  ms_eqv (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31) F pc fc rv m ro) x ->
  regs_preserved (ms_regs x) regs1 ->
  mkR_of regs1 =
  mkR (reg_get regs1 1) x2 x3 x4 (reg_get regs1 5) (reg_get regs1 6) (reg_get regs1 7) x8 x9 (reg_get regs1 10)
      (reg_get regs1 11) (reg_get regs1 12) (reg_get regs1 13) (reg_get regs1 14) (reg_get regs1 15) (reg_get regs1 16)
      (reg_get regs1 17) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (reg_get regs1 28) (reg_get regs1 29)
      (reg_get regs1 30) (reg_get regs1 31).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 F pc fc rv m ro x regs1 HE RP.
  set (R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
              x28 x29 x30 x31) in HE.
  assert (H : forall q, callee_saved q -> getr regs1 (Z_to_bv 5 q) = getr R (Z_to_bv 5 q)).
  { intros q Hq. rewrite (RP q Hq). exact (eqv_getr _ _ _ _ _ _ _ _ (Z_to_bv 5 q) HE). }
  unfold mkR_of. f_equal;
    (etransitivity;
     [ apply (agree_get regs1 R _ H); unfold callee_saved;
       match goal with |- context [bv_unsigned ?k] => let v := eval vm_compute in (bv_unsigned k) in
         change (bv_unsigned k) with v end; lia
     | reflexivity ]).
Qed.

Ltac resume HEQ RP :=
  rewrite (resume_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEQ RP).

Lemma regs_pres_trans : forall r1 r2 r3, regs_preserved r1 r2 -> regs_preserved r2 r3 -> regs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 q Hq. rewrite (H2 q Hq). exact (H1 q Hq). Qed.


Lemma need_app : forall st P P2 Rest,
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ P2 ++ Rest))) + 1 <= WMAX ->
  Z.of_nat (length (w_text (putN st P))) + Z.of_nat (length (concat P2)) + 1 <= WMAX.
Proof.
  intros st P P2 Rest H. pose proof (putN_text P st) as T. rewrite !concat_app, !length_app in H. lia.
Qed.

Lemma rooms_app : forall F st b P P2 Rest bk, wr_rooms F b st (P ++ P2 ++ Rest) -> bk = wfold F b st P ->
  wr_rooms F bk (putN st P) P2.
Proof.
  intros F st b P P2 Rest bk H E. apply wr_rooms_app in H. destruct H as [_ H]. apply wr_rooms_app in H.
  subst bk. exact (proj1 H).
Qed.

Lemma wvk : forall t, 128 + PUT_K <= WV_K t /\ 128 + PS_K <= WV_K t /\ 128 + IND_K <= WV_K t /\ 0 < PUT_K.
Proof.
  intros t. unfold WV_K, WV_KMAX, WV_FR, PS_K, IND_K, PUT_K, REALLOC_STACK, ALLOC_STACK.
  pose proof (Zle_0_nat (PjTree.depth t)). lia.
Qed.

Lemma wvk_sub : forall t u, (PjTree.depth u < PjTree.depth t)%nat -> WV_K u + 128 <= WV_K t.
Proof. intros t u H. unfold WV_K, WV_FR. lia. Qed.

Lemma node_hdr : forall segs m lblk v t D, pj_node segs m lblk v t D ->
  exists num str kids keys n cap, pj_hdr segs m v (tag t) num str kids keys n cap.
Proof.
  intros segs m lblk v t D H.
  destruct t; cbn [pj_node] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & _);
    exists num, str, kids, keys, n, cap; exact Hh.
Qed.

Lemma present_bytes : forall m a n, 0 <= a -> a + n <= 2 ^ 64 -> 0 <= n ->
  (forall i, 0 <= i < n -> present m (a + i)) -> exists bs, Z.of_nat (length bs) = n /\ bytes_at rsegs m a bs.
Proof.
  intros m a n Ha Hn H0 H.
  assert (ST : stk rsegs m a (a + n)).
  { split; [exact Ha|]. split; [exact Hn|]. intros x Hx.
    destruct (H (x - a) ltac:(lia)) as (b0 & Hb). replace (a + (x - a)) with x in Hb by lia.
    unfold wview, Mem.mrd, Mem.wa. rewrite Hb. split; [discriminate | exists b0; reflexivity]. }
  destruct (stk_bytes rsegs m a (a + n) ST ltac:(lia)) as (bs & Hl & Hb).
  exists bs. split; [rewrite Hl; lia | exact Hb].
Qed.

Lemma slack_bound : forall x y, x <= y -> x + (- x) mod 8 <= 8 * ((y + 7) / 8).
Proof. intros x y H. Z.div_mod_to_equations. lia. Qed.

Lemma bytes_ok_lt : forall l, Forall (fun c => 0 < c < 256) l -> bytes_ok l.
Proof. intros l H. unfold bytes_ok. eapply Forall_impl; [|exact H]. intros c Hc. cbv beta in *. lia. Qed.

Lemma no_zero_lt : forall l, Forall (fun c => 0 < c < 256) l -> no_zero l.
Proof. intros l H. unfold no_zero. eapply Forall_impl; [|exact H]. intros c Hc. cbv beta in *. lia. Qed.

Definition wv_ob (ty : Z) : list Z := [if ty =? 6 then 123 else 91].
Definition wv_cb (ty : Z) : list Z := [if ty =? 6 then 125 else 93].

Lemma oc_facts : forall ty, ty = 5 \/ ty = 6 ->
  (img_ok (wv_open ty) (wv_ob ty) = true /\
   existsb (fun sg => (bv_unsigned (fst sg) <=? wv_open ty) && (wv_open ty <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
     (segments_reserved rsegs) = true /\
   bytes_ok (wv_ob ty) /\ 0 <= wv_open ty /\ wv_open ty + Z.of_nat (length (wv_ob ty)) <= IMG_TOP) /\
  (img_ok (wv_close ty) (wv_cb ty) = true /\
   existsb (fun sg => (bv_unsigned (fst sg) <=? wv_close ty) && (wv_close ty <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
     (segments_reserved rsegs) = true /\
   bytes_ok (wv_cb ty) /\ 0 <= wv_close ty /\ wv_close ty + Z.of_nat (length (wv_cb ty)) <= IMG_TOP).
Proof.
  intros ty [-> | ->].
  - change (wv_open 5) with WV_S_LBRACKET. change (wv_close 5) with WV_S_RBRACKET.
    change (wv_ob 5) with [91]. change (wv_cb 5) with [93].
    split; (split; [vm_compute; reflexivity|]; split; [vm_compute; reflexivity|];
      split; [unfold bytes_ok; repeat constructor; lia|];
      unfold WV_S_LBRACKET, WV_S_RBRACKET, IMG_TOP; cbn [length Z.of_nat]; lia).
  - change (wv_open 6) with WV_S_LBRACE. change (wv_close 6) with WV_S_RBRACE.
    change (wv_ob 6) with [123]. change (wv_cb 6) with [125].
    split; (split; [vm_compute; reflexivity|]; split; [vm_compute; reflexivity|];
      split; [unfold bytes_ok; repeat constructor; lia|];
      unfold WV_S_LBRACE, WV_S_RBRACE, IMG_TOP; cbn [length Z.of_nat]; lia).
Qed.

Lemma sep_facts : forall pretty,
  wv_seplen pretty = Z.of_nat (length (wsep (negb (pretty =? 0)))) /\
  img_ok (wv_sep pretty) (wsep (negb (pretty =? 0))) = true /\
  existsb (fun sg => (bv_unsigned (fst sg) <=? wv_sep pretty) && (wv_sep pretty <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
    (segments_reserved rsegs) = true /\
  bytes_ok (wsep (negb (pretty =? 0))) /\ 0 <= wv_sep pretty /\
  wv_sep pretty + Z.of_nat (length (wsep (negb (pretty =? 0)))) <= IMG_TOP.
Proof.
  intros pretty. unfold wv_seplen, wv_sep, wsep. destruct (pretty =? 0); cbn [negb];
    (split; [reflexivity|]); (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
    (split; [unfold bytes_ok; repeat constructor; lia|]);
    unfold WV_S_COLON, WV_S_COLON_SP, IMG_TOP; cbn [length Z.of_nat]; lia.
Qed.

Definition arr_go (p : bool) (dd : Z) : nat -> list jv -> list (list Z) :=
  fix go (i : nat) (l : list jv) {struct l} : list (list Z) :=
    match l with
    | [] => []
    | x :: r => wcomma i ++ wind p (dd + 1) ++ wvpieces x p (dd + 1) ++ go (S i) r
    end.

Definition obj_go (p : bool) (dd : Z) : nat -> list (list Z * jv) -> list (list Z) :=
  fix go (i : nat) (l : list (list Z * jv)) {struct l} : list (list Z) :=
    match l with
    | [] => []
    | (k, x) :: r => wcomma i ++ wind p (dd + 1) ++ spieces k ++ [wsep p] ++ wvpieces x p (dd + 1) ++ go (S i) r
    end.

Definition aq (p : bool) (dd : Z) (pre : list jv) : list (list Z) := [91] :: arr_go p dd 0 pre.
Definition oq (p : bool) (dd : Z) (pre : list (list Z * jv)) : list (list Z) := [123] :: obj_go p dd 0 pre.

Lemma wvp_arr : forall items p dd, wvpieces (JArr items) p dd =
  [91] :: arr_go p dd 0 items ++ (match items with [] => [] | _ :: _ => wind p dd end) ++ [[93]].
Proof. intros. reflexivity. Qed.

Lemma wvp_obj : forall members p dd, wvpieces (JObj members) p dd =
  [123] :: obj_go p dd 0 members ++ (match members with [] => [] | _ :: _ => wind p dd end) ++ [[125]].
Proof. intros. reflexivity. Qed.

Lemma arr_go_nil : forall p dd i, arr_go p dd i [] = [].
Proof. intros. reflexivity. Qed.

Lemma arr_go_cons : forall p dd i x r,
  arr_go p dd i (x :: r) = wcomma i ++ wind p (dd + 1) ++ wvpieces x p (dd + 1) ++ arr_go p dd (S i) r.
Proof. intros. reflexivity. Qed.

Lemma obj_go_nil : forall p dd i, obj_go p dd i [] = [].
Proof. intros. reflexivity. Qed.

Lemma obj_go_cons : forall p dd i k x r, obj_go p dd i ((k, x) :: r) =
  wcomma i ++ wind p (dd + 1) ++ spieces k ++ [wsep p] ++ wvpieces x p (dd + 1) ++ obj_go p dd (S i) r.
Proof. intros. reflexivity. Qed.

Lemma arr_go_app : forall p dd l1 l2 i,
  arr_go p dd i (l1 ++ l2) = arr_go p dd i l1 ++ arr_go p dd (i + length l1) l2.
Proof.
  intros p dd l1. induction l1 as [|x l1 IH]; intros l2 i.
  - cbn [app length]. rewrite Nat.add_0_r. reflexivity.
  - cbn [app length]. rewrite !arr_go_cons, IH, <- !app_assoc, Nat.add_succ_r. reflexivity.
Qed.

Lemma obj_go_app : forall p dd l1 l2 i,
  obj_go p dd i (l1 ++ l2) = obj_go p dd i l1 ++ obj_go p dd (i + length l1) l2.
Proof.
  intros p dd l1. induction l1 as [|[k x] l1 IH]; intros l2 i.
  - cbn [app length]. rewrite Nat.add_0_r. reflexivity.
  - cbn [app length]. rewrite !obj_go_cons, IH, <- !app_assoc, Nat.add_succ_r. reflexivity.
Qed.

Lemma nth_mid : forall {T : Type} (l l' : list T) (a z : T), nth (length l) (l ++ a :: l') z = a.
Proof. intros T l. induction l as [|x l IH]; intros l' a z; [reflexivity | exact (IH l' a z)]. Qed.

Lemma wcomma_S : forall {T : Type} (pre : list T) (u : T), wcomma (length (pre ++ [u])) = [[44]].
Proof. intros T pre u. rewrite length_app, Nat.add_comm. reflexivity. Qed.

Lemma arr_wp : forall items pre u r p dd, items = pre ++ u :: r ->
  wvpieces (JArr items) p dd = (aq p dd pre ++ wcomma (length pre)) ++ wind p (dd + 1) ++ wvpieces u p (dd + 1) ++
    arr_go p dd (S (length pre)) r ++ wind p dd ++ [[93]].
Proof.
  intros items pre u r p dd ->. rewrite wvp_arr, arr_go_app, arr_go_cons.
  replace (match pre ++ u :: r with [] => [] | _ :: _ => wind p dd end) with (wind p dd)
    by (destruct pre; reflexivity).
  unfold aq. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma arr_after : forall pre u p dd,
  ((aq p dd pre ++ wcomma (length pre)) ++ wind p (dd + 1)) ++ wvpieces u p (dd + 1) = aq p dd (pre ++ [u]).
Proof.
  intros pre u p dd. unfold aq. rewrite arr_go_app, arr_go_cons, arr_go_nil, app_nil_r. cbn [app].
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma obj_wp : forall members pre nm u r p dd, members = pre ++ (nm, u) :: r ->
  wvpieces (JObj members) p dd = (oq p dd pre ++ wcomma (length pre)) ++ wind p (dd + 1) ++ spieces nm ++
    [wsep p] ++ wvpieces u p (dd + 1) ++ obj_go p dd (S (length pre)) r ++ wind p dd ++ [[125]].
Proof.
  intros members pre nm u r p dd ->. rewrite wvp_obj, obj_go_app, obj_go_cons.
  replace (match pre ++ (nm, u) :: r with [] => [] | _ :: _ => wind p dd end) with (wind p dd)
    by (destruct pre; reflexivity).
  rewrite <- !app_assoc. unfold oq. cbn [app]. reflexivity.
Qed.

Lemma obj_after : forall pre nm u p dd,
  ((((oq p dd pre ++ wcomma (length pre)) ++ wind p (dd + 1)) ++ spieces nm) ++ [wsep p]) ++ wvpieces u p (dd + 1) =
  oq p dd (pre ++ [(nm, u)]).
Proof.
  intros pre nm u p dd. rewrite <- !app_assoc. unfold oq.
  rewrite obj_go_app, obj_go_cons, obj_go_nil, app_nil_r. cbn [app]. reflexivity.
Qed.

Section W.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.

Definition wv_env (K : Z) (regs : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (o : Z) (st : wst) : Prop :=
  aa_MR API L A mem md /\ st_init_done A = true /\ 0 <= w_cap st /\ 0 <= K /\
  alloc_ceiling + K <= spZ regs /\ spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0 /\
  (forall a, spZ regs - K <= a < spZ regs -> writable_at (ms_segs B) mem a) /\
  (forall a, errno_at B a -> writable_at (ms_segs B) mem a) /\
  spZ regs <= o /\ off_errno B o 32 /\ off_errno B (spZ regs - K) K /\
  getr regs 4 = Z_to_bv 64 (ms_tp B) /\ spZ regs <= TASK_SIZE.

Lemma chain_pre : forall K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk Kc,
  wv_env K regs L A mem md o st ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  spZ regs - K <= spZ regsk - Kc -> spZ regsk <= spZ regs -> spZ regsk mod 16 = 0 ->
  getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) ->
  call_pre_t B API Kc Lk Ak regsk memk mdk /\ st_init_done Ak = true /\ ro_agree (ms_segs B) memk /\
  pj_out_ok B memk Lamk o bufk (Z.of_nat (length (w_text (putN st P)))) (w_cap (putN st P))
    (w_failed (putN st P)) (w_text (putN st P)) /\
  ledger B Lk Ak memk Lamk peakk (w_cnt (putN st P)) (w_fail (putN st P)) /\ rf_ok RF Ak bk /\
  bk = wfold RF b st P /\ spZ regsk <= o /\ off_errno B (spZ regsk - Kc) Kc.
Proof.
  intros K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk Kc ENV RC H1 H2 H16 H4 HRA.
  destruct ENV as (HM & INIT & CAP0 & K0 & CEIL & S63 & S16 & WS & WE & SO & EO & ES & TP & TS).
  pose proof RC as (HMk & HWk & HBk & [ROk GKk] & PJk & LGk & RSk & EBk & _ & _ & _ & INk & _).
  destruct (wr_writable B API RF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - K) (spZ regs) RC
    ltac:(lia) ltac:(lia) WS WE) as [WSk WEk].
  split.
  { unfold call_pre_t. split; [|lia].
    unfold call_pre_k. split; [exact HMk|]. split; [exact HWk|]. split; [exact HBk|]. split; [exact HRA|].
    split; [exact H16|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply WSk; lia|].
    split; [rewrite H4; exact TP|]. split; [exact WEk|]. intros Hf. rewrite (INk INIT) in Hf. discriminate. }
  split; [exact (INk INIT)|]. split; [exact ROk|]. split; [exact PJk|]. split; [exact LGk|]. split; [exact RSk|].
  split; [exact EBk|]. split; [lia|]. eapply off_errno_sub; [exact ES | lia | lia].
Qed.

Lemma chain_ext : forall K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk lo hi P2
    L1 A1 mem1 md1 buf1 Lam1 peak1 b1,
  wv_env K regs L A mem md o st ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  spZ regs - K <= lo -> hi <= spZ regs ->
  wr_rel B API RF lo hi Lk Ak memk mdk o bufk (putN st P) Lamk peakk bk P2 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b (P ++ P2) L1 A1 mem1 md1 buf1 Lam1 peak1 b1.
Proof using SEGS AX CTX.
  intros K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk lo hi P2 L1 A1 mem1 md1 buf1 Lam1
    peak1 b1 ENV RC H1 H2 R1.
  destruct ENV as (HM & _ & CAP0 & _ & CEIL & S63 & _).
  pose proof RC as (HMk & _).
  apply (wr_rel_app B API RF SEGS AX CTX _ _ L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk P2
    L1 A1 mem1 md1 buf1 Lam1 peak1 b1 HM CAP0 RC).
  apply (wr_rel_widen B API RF lo hi); [exact HMk | lia | lia | lia | lia | exact R1].
Qed.

Lemma put_chain : forall (fxk : FPState) (PUTC : @put_contract fxk rc B API RF)
    K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk s bs Rest Q,
  wv_env K regs L A mem md o st ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  wr_rooms RF b st (P ++ [bs] ++ Rest) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ [bs] ++ Rest))) + 1 <= WMAX ->
  spZ regs - K <= spZ regsk - PUT_K -> spZ regsk <= spZ regs -> spZ regsk mod 16 = 0 ->
  getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) ->
  getr regsk 10 = Z_to_bv 64 o -> getr regsk 11 = Z_to_bv 64 s ->
  getr regsk 12 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  zbytes_at B memk s bs -> bytes_ok bs -> 0 <= s < 2 ^ 64 -> s + Z.of_nat (length bs) <= 2 ^ 64 ->
  s_where B regsk Lamk s (Z.of_nat (length bs)) bufk -> (s + Z.of_nat (length bs) <= o \/ o + 32 <= s) ->
  (forall regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, regs_preserved regsk regs1 ->
     wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b (P ++ [bs])
       L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     wr_rel B API RF (spZ regsk - PUT_K) (spZ regsk) Lk Ak memk mdk o bufk (putN st P) Lamk peakk bk [bs]
       L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fxk regs1 (getr regsk 1) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg (@mkst fxk regsk (Z_to_bv 64 put_c.PUT) memk (seg_rom (ms_segs B))) mdk) Q.
Proof using SEGS AX CTX.
  intros fxk PUTC K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk s bs Rest Q
    ENV RC ROOMS NEED H1 H2 H16 H4 HRA Q10 Q11 Q12 ZB BO S0 SN SW SO K'.
  pose proof ENV as (HM & INIT & CAP0 & K0 & CEIL & S63 & S16 & WS & WE & SPO & EO & ES & TP & TS).
  destruct (chain_pre K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk PUT_K ENV RC
    H1 H2 H16 H4 HRA) as (PRE & INk & ROk & PJk & LGk & RSk & EBk & SOk & ESk).
  pose proof RC as (HMk & HWk & HBk & _).
  destruct (wr_writable B API RF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - K) (spZ regs) RC
    ltac:(lia) ltac:(lia) WS WE) as [WSk WEk].
  apply (@put_call fxk rc B API RF SEGS AX PUTC K (spZ regs) Lk Ak regsk memk mdk o s (Z.of_nat (length bs)) bs bufk
    (putN st P) Lamk peakk bk Q); try assumption.
  - rewrite H4. exact TP.
  - reflexivity.
  - pose proof (need_app st P [bs] Rest NEED) as N. cbn [concat] in N. rewrite app_nil_r in N. exact N.
  - pose proof (rooms_app RF st b P [bs] Rest bk ROOMS EBk) as RM. exact (proj1 RM).
  - intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP R1.
    apply (K' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP); [|exact R1].
    exact (chain_ext K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk
      (spZ regsk - PUT_K) (spZ regsk) [bs] L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ENV RC H1 H2 R1).
Qed.

Lemma indent_chain : forall (fxk : FPState) (INDC : @indent_contract fxk rc B API RF)
    K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk pretty dd Rest Q,
  wv_env K regs L A mem md o st ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  wr_rooms RF b st (P ++ wind (negb (pretty =? 0)) dd ++ Rest) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ wind (negb (pretty =? 0)) dd ++ Rest))) + 1
    <= WMAX ->
  spZ regs - K <= spZ regsk - IND_K -> spZ regsk <= spZ regs -> spZ regsk mod 16 = 0 ->
  getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) ->
  getr regsk 10 = Z_to_bv 64 o -> getr regsk 11 = Z_to_bv 64 pretty -> getr regsk 12 = Z_to_bv 64 dd ->
  0 <= pretty < 2 ^ 64 -> - 2 ^ 31 <= dd < 2 ^ 31 ->
  (forall regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, regs_preserved regsk regs1 ->
     wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b (P ++ wind (negb (pretty =? 0)) dd)
       L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     wr_rel B API RF (spZ regsk - IND_K) (spZ regsk) Lk Ak memk mdk o bufk (putN st P) Lamk peakk bk
       (wind (negb (pretty =? 0)) dd) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fxk regs1 (getr regsk 1) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg (@mkst fxk regsk (Z_to_bv 64 INDENT_PC) memk (seg_rom (ms_segs B))) mdk) Q.
Proof using SEGS AX CTX.
  intros fxk INDC K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk pretty dd Rest Q
    ENV RC ROOMS NEED H1 H2 H16 H4 HRA Q10 Q11 Q12 HP HD K'.
  destruct (chain_pre K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk IND_K ENV RC
    H1 H2 H16 H4 HRA) as ([PRE _] & INk & ROk & PJk & LGk & RSk & EBk & SOk & ESk).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EO & _).
  eapply SR_bind.
  { exact (INDC Lk Ak regsk memk mdk bk o pretty dd bufk (putN st P) Lamk peakk SEGS PRE INk ROk Q10 Q11 Q12 HP HD
      PJk LGk SOk EO ESk (need_app st P _ Rest NEED) RSk (rooms_app RF st b P _ Rest bk ROOMS EBk)). }
  intros c' (L1 & A1 & regs1 & mem1 & md1 & buf1 & Lam1 & peak1 & b1 & Ec & RP & R1). subst c'.
  apply (K' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP); [|exact R1].
  exact (chain_ext K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk
    (spZ regsk - IND_K) (spZ regsk) _ L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ENV RC H1 H2 R1).
Qed.

Lemma ps_chain : forall (fxk : FPState) (PSC : @put_string_contract fxk rc B API RF)
    K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk s bs Rest Q,
  ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD -> frm0 (@fp_csr fxk) ->
  wv_env K regs L A mem md o st ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  wr_rooms RF b st (P ++ spieces bs ++ Rest) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ spieces bs ++ Rest))) + 1 <= WMAX ->
  spZ regs - K <= spZ regsk - PS_K -> spZ regsk <= spZ regs -> spZ regsk mod 16 = 0 ->
  getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) ->
  getr regsk 10 = Z_to_bv 64 o -> getr regsk 11 = Z_to_bv 64 s ->
  zbytes_at B memk s (bs ++ [0]) -> bytes_ok bs -> no_zero bs ->
  str_where B Lamk s (Z.of_nat (length bs) + 1) bufk ->
  (forall (fx' : FPState) regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1,
     (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fxk) k) ->
     frm0 (@fp_csr fx') -> regs_preserved regsk regs1 ->
     wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b (P ++ spieces bs)
       L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     wr_rel B API RF (spZ regsk - PS_K) (spZ regsk) Lk Ak memk mdk o bufk (putN st P) Lamk peakk bk (spieces bs)
       L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fx' regs1 (getr regsk 1) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg (@mkst fxk regsk (Z_to_bv 64 PUT_STRING) memk (seg_rom (ms_segs B))) mdk) Q.
Proof using SEGS AX CTX.
  intros fxk PSC K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk s bs Rest Q
    GG GD FM ENV RC ROOMS NEED H1 H2 H16 H4 HRA Q10 Q11 ZB BO NZ SW K'.
  pose proof ENV as (HM & INIT & CAP0 & K0 & CEIL & S63 & S16 & WS & WE & SPO & EO & ES & TP & TS).
  destruct (chain_pre K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk PS_K ENV RC
    H1 H2 H16 H4 HRA) as (PRE & INk & ROk & PJk & LGk & RSk & EBk & SOk & ESk).
  pose proof (need_app st P _ Rest NEED) as NEEDk. pose proof (rooms_app RF st b P _ Rest bk ROOMS EBk) as RMk.
  destruct (putN st P) as [failed text cap cnt fail calls] eqn:Est.
  rewrite ?Est in PJk, LGk, NEEDk, RMk. cbn [w_text w_cap w_failed w_cnt w_fail] in PJk, LGk, NEEDk.
  eapply SR_bind.
  { exact (PSC Lk Ak regsk memk mdk bk o s bufk (Z.of_nat (length text)) cap failed text bs Lamk peakk cnt fail calls
      SEGS GG GD PRE ROk INk FM Q10 Q11 PJk LGk SOk EO ESk ZB BO NZ SW NEEDk RSk RMk). }
  intros c' (fx' & FR & FM' & _ & L1 & A1 & regs1 & mem1 & md1 & buf1 & Lam1 & peak1 & b1 & Ec & RP & R1). subst c'.
  pose proof R1 as R1'. rewrite <- Est in R1'.
  apply (K' fx' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 FR FM' RP); [|exact R1].
  exact (chain_ext K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk
    (spZ regsk - PS_K) (spZ regsk) _ L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ENV RC H1 H2 R1').
Qed.

Lemma lam_keep : forall lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 x y,
  wr_rel B API RF lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  ledger B L A mem Lam peak (w_cnt st) (w_fail st) ->
  In (x, y) Lam -> x <> buf -> In (x, y) Lam1 /\ x <> buf1.
Proof.
  intros lo hi L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 x y R1 LG Hin Hne.
  pose proof R1 as (_ & _ & _ & _ & _ & _ & _ & _ & LM & _ & _ & _ & _ & _ & _ & FM & _).
  destruct (lblock_in B _ _ _ _ _ _ _ _ _ LG Hin) as [Hy Hb].
  assert (Nb : x <> buf1).
  { intros E. apply (FM (x - 16) (y + 16) Hb ltac:(lia) ltac:(intros E2; injection E2 as E3 _; lia)). lia. }
  split; [|exact Nb].
  destruct LM as [(_ & _ & -> & _) | (_ & l1 & l2 & Hl & -> & _)]; [exact Hin|].
  right. destruct Hl as [(_ & -> & ->) | (_ & ->)]; [exact Hin|].
  apply (in_mid _ _ _ _ Hin). intros E. injection E as E. contradiction.
Qed.

Lemma guard_of : forall L A mem md, ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
  aa_MR API L A mem md -> guard_cells mem.
Proof using SEGS AX.
  intros L A mem md GG GD HM.
  destruct (ax_statics AX L A mem md HM) as (W1 & (g & Hg & W2) & _).
  rewrite GG, GD, SEGS in W1. rewrite GD, SEGS in W2.
  split.
  - apply (proj1 (word_mem_iff mem GOT_GUARD GUARD ltac:(unfold GOT_GUARD; lia) ltac:(unfold GOT_GUARD; lia))).
    exact W1.
  - exists (Z_to_bv 64 g).
    apply (proj1 (word_mem_iff mem GUARD g ltac:(unfold GUARD; lia) ltac:(unfold GUARD; lia))). exact W2.
Qed.

Definition wv_pre (fx : FPState) (t : jv) L A regs mem md b o v pretty d D buf (st : wst) Lam peak : Prop :=
  ms_got_guard B = GOT_GUARD /\ ms_guard B = GUARD /\
  call_pre_t B API (WV_K t) L A regs mem md /\ st_init_done A = true /\
  ro_agree (ms_segs B) mem /\ frm0 (@fp_csr fx) /\
  getr regs 10 = Z_to_bv 64 o /\ getr regs 11 = Z_to_bv 64 v /\
  getr regs 12 = Z_to_bv 64 pretty /\ getr regs 13 = Z_to_bv 64 d /\
  0 <= pretty < 2 ^ 64 /\ 0 <= d < 2 ^ 31 /\ d + Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 /\
  pj_out_ok B mem Lam o buf (Z.of_nat (length (w_text st))) (w_cap st) (w_failed st) (w_text st) /\
  ledger B L A mem Lam peak (w_cnt st) (w_fail st) /\
  spZ regs <= o /\ off_errno B o 32 /\ off_errno B (spZ regs - WV_K t) (WV_K t) /\
  pj_node rsegs mem (wv_lblk Lam) v t D /\ wv_where B regs Lam v buf /\
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) /\
  (forall x, o <= x < o + 32 -> ~ pj_foot v D x) /\
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (wvpieces t (negb (pretty =? 0)) d))) + 1 <= WMAX /\
  rf_ok RF A b /\ wr_rooms RF b st (wvpieces t (negb (pretty =? 0)) d).

Lemma mk_wv_pre : forall (fx : FPState) t L A regs mem md b o v pretty d D buf st Lam peak,
  ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
  call_pre_t B API (WV_K t) L A regs mem md -> st_init_done A = true ->
  ro_agree (ms_segs B) mem -> frm0 (@fp_csr fx) ->
  getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 v ->
  getr regs 12 = Z_to_bv 64 pretty -> getr regs 13 = Z_to_bv 64 d ->
  0 <= pretty < 2 ^ 64 -> 0 <= d < 2 ^ 31 -> d + Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
  pj_out_ok B mem Lam o buf (Z.of_nat (length (w_text st))) (w_cap st) (w_failed st) (w_text st) ->
  ledger B L A mem Lam peak (w_cnt st) (w_fail st) ->
  spZ regs <= o -> off_errno B o 32 -> off_errno B (spZ regs - WV_K t) (WV_K t) ->
  pj_node rsegs mem (wv_lblk Lam) v t D -> wv_where B regs Lam v buf ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_foot v D x) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (wvpieces t (negb (pretty =? 0)) d))) + 1 <= WMAX ->
  rf_ok RF A b -> wr_rooms RF b st (wvpieces t (negb (pretty =? 0)) d) ->
  @wv_pre fx t L A regs mem md b o v pretty d D buf st Lam peak.
Proof. intros. unfold wv_pre. repeat (split; [assumption|]). assumption. Qed.

Definition wv_P (t : jv) : Prop :=
  forall (fx : FPState) L A regs mem md b o v pretty d D buf (st : wst) Lam peak,
    @wv_pre fx t L A regs mem md b o v pretty d D buf st Lam peak ->
    SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
      (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
         (wvpieces t (negb (pretty =? 0)) d)).

Lemma wv_chain : forall (fxk : FPState) u (IH : wv_P u)
    K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk vi pretty dd Du Rest Q,
  ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD -> frm0 (@fp_csr fxk) ->
  wv_env K regs L A mem md o st ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  wr_rooms RF b st (P ++ wvpieces u (negb (pretty =? 0)) dd ++ Rest) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ wvpieces u (negb (pretty =? 0)) dd ++ Rest))) + 1
    <= WMAX ->
  spZ regs - K <= spZ regsk - WV_K u -> spZ regsk <= spZ regs -> spZ regsk mod 16 = 0 ->
  getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) ->
  getr regsk 10 = Z_to_bv 64 o -> getr regsk 11 = Z_to_bv 64 vi ->
  getr regsk 12 = Z_to_bv 64 pretty -> getr regsk 13 = Z_to_bv 64 dd ->
  0 <= pretty < 2 ^ 64 -> 0 <= dd < 2 ^ 31 -> dd + Z.of_nat (PjTree.depth u) <= 2 ^ 31 - 1 ->
  pj_node rsegs memk (wv_lblk Lamk) vi u Du -> wv_where B regsk Lamk vi bufk ->
  (forall a k, In (a, k) Du -> In (a, k) Lamk /\ a <> bufk) ->
  (forall x, o <= x < o + 32 -> ~ pj_foot vi Du x) ->
  (forall (fx' : FPState) regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1,
     (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fxk) k) ->
     frm0 (@fp_csr fx') -> regs_preserved regsk regs1 ->
     wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b
       (P ++ wvpieces u (negb (pretty =? 0)) dd) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     wr_rel B API RF (spZ regsk - WV_K u) (spZ regsk) Lk Ak memk mdk o bufk (putN st P) Lamk peakk bk
       (wvpieces u (negb (pretty =? 0)) dd) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fx' regs1 (getr regsk 1) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg (@mkst fxk regsk (Z_to_bv 64 WRITE_VALUE_PC) memk (seg_rom (ms_segs B))) mdk) Q.
Proof using SEGS AX CTX.
  intros fxk u IH K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk vi pretty dd Du
    Rest Q GG GD FM ENV RC ROOMS NEED H1 H2 H16 H4 HRA Q10 Q11 Q12 Q13 HP HD HDD ND WH DL OF K'.
  pose proof ENV as (HM & INIT & CAP0 & K0 & CEIL & S63 & S16 & WS & WE & SPO & EO & ES & TP & TS).
  destruct (chain_pre K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk regsk (WV_K u) ENV
    RC H1 H2 H16 H4 HRA) as (PRE & INk & ROk & PJk & LGk & RSk & EBk & SOk & ESk).
  eapply SR_bind.
  { exact (IH fxk Lk Ak regsk memk mdk bk o vi pretty dd Du bufk (putN st P) Lamk peakk
      (mk_wv_pre fxk u Lk Ak regsk memk mdk bk o vi pretty dd Du bufk (putN st P) Lamk peakk GG GD PRE INk ROk FM
      Q10 Q11 Q12 Q13 HP HD HDD PJk LGk SOk EO ESk ND WH DL OF (need_app st P _ Rest NEED) RSk
      (rooms_app RF st b P _ Rest bk ROOMS EBk))). }
  intros c' (fx' & FR & FM' & _ & _ & L1 & A1 & regs1 & mem1 & md1 & buf1 & Lam1 & peak1 & b1 & Ec & RP & R1).
  subst c'.
  apply (K' fx' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 FR FM' RP); [|exact R1].
  exact (chain_ext K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk
    (spZ regsk - WV_K u) (spZ regsk) _ L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ENV RC H1 H2 R1).
Qed.

Lemma present_wview : forall m a, present m a -> wview rsegs m (wa a) <> None.
Proof. intros m a (b0 & H). unfold wview, wa. rewrite H. discriminate. Qed.

Lemma node_keep : forall K regs L A mem md o st buf Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 v t D
    (lblk' : Z -> Z -> Prop),
  wv_env K regs L A mem md o st ->
  ledger B L A mem Lam peak (w_cnt st) (w_fail st) ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  pj_node rsegs mem (wv_lblk Lam) v t D -> wv_where B regs Lam v buf ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_foot v D x) ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  pj_node rsegs mem1 lblk' v t D.
Proof using SEGS.
  intros K regs L A mem md o st buf Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 v t D lblk' ENV LG R1 ND WH DL OF HL.
  destruct ENV as (HM & _ & _ & K0 & CEIL & S63 & _).
  pose proof R1 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PT & KP & _ & FR & _).
  pose proof ceil_big as CB. unfold IMG_TOP in CB.
  assert (BLK : forall x y z, In (x, y) Lam -> x <> buf -> x <= z < x + y ->
            mbyte (ms_segs B) mem1 z = mbyte (ms_segs B) mem z /\ present mem1 z).
  { intros x y z Hin Hne Hz. destruct (lblock_in B _ _ _ _ _ _ _ _ _ LG Hin) as [Hy Hb].
    split.
    - replace z with ((x - 16) + (z - x + 16)) by lia. apply (KP (x - 16) (y + 16) (z - x + 16) Hb); lia.
    - destruct (blocks_user L A (x - 16) (y + 16) Hb) as (q & Hq & Eq).
      destruct (PT q (y + 16) Hq ltac:(intros E2; injection E2 as E3 _; lia)) as [Hq1 Ep].
      assert (Hb1 : In (x - 16, y + 16) (blocks L1 A1)).
      { unfold blocks. apply in_map_iff. exists (q, y + 16). cbn [fst snd]. rewrite Ep, Eq.
        split; [reflexivity | exact Hq1]. }
      destruct (block_facts B API L1 A1 mem1 md1 (x - 16) (y + 16) (z - x + 16) HM1 Hb1 ltac:(lia)) as (Pz & _).
      replace z with (x - 16 + (z - x + 16)) by lia. exact Pz. }
  assert (STK : spZ regs <= v -> off_errno B v 56 -> forall z, v <= z < v + 56 -> z < 2 ^ 64 ->
            mbyte (ms_segs B) mem1 z = mbyte (ms_segs B) mem z /\
            (writable_at (ms_segs B) mem z <-> writable_at (ms_segs B) mem1 z)).
  { intros Hv Ho z Hz Hz64. apply FR.
    - left. lia.
    - apply (not_owned_hi B API L A mem md z HM). lia.
    - apply (not_owned_hi B API L1 A1 mem1 md1 z HM1). lia.
    - lia.
    - unfold errno_at. unfold off_errno in Ho. lia.
    - intros Hr. exact (OF z Hr (or_introl Hz)).
    - intros S. pose proof (statics_low z S). lia. }
  apply (pj_node_mrd rsegs t mem (wv_lblk Lam) mem1 lblk' v D ND HL).
  - intros x Hx Hf. rewrite <- !mbyte_mrd. rewrite <- SEGS.
    destruct Hf as [Hn | ([a k] & Hbb & Hh)].
    + destruct WH as [[Hv Ho] | (x' & y' & Hin & Hne & H1 & H2)].
      * exact (proj1 (STK Hv Ho x Hn ltac:(lia))).
      * exact (proj1 (BLK x' y' x Hin Hne ltac:(lia))).
    + destruct (DL a k Hbb) as [Hin Hne]. unfold pj_holds in Hh. cbn [fst snd] in Hh.
      exact (proj1 (BLK a k x Hin Hne Hh)).
  - intros x Hx Hf W.
    destruct Hf as [Hn | ([a k] & Hbb & Hh)].
    + destruct WH as [[Hv Ho] | (x' & y' & Hin & Hne & H1 & H2)].
      * pose proof (proj2 (STK Hv Ho x Hn ltac:(lia))) as E. unfold writable_at in E. rewrite SEGS in E.
        exact (proj1 E W).
      * exact (present_wview mem1 x (proj2 (BLK x' y' x Hin Hne ltac:(lia)))).
    + destruct (DL a k Hbb) as [Hin Hne]. unfold pj_holds in Hh. cbn [fst snd] in Hh.
      exact (present_wview mem1 x (proj2 (BLK a k x Hin Hne Hh))).
Qed.

Lemma wv_fin : forall (fx fx' : FPState) t K regs L A mem md o buf st Lam peak b v D P
    regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1,
  ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
  wv_env K regs L A mem md o st -> ledger B L A mem Lam peak (w_cnt st) (w_fail st) ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) ->
  frm0 (@fp_csr fx') -> regs_preserved regs regs1 ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  pj_node rsegs mem (wv_lblk Lam) v t D -> wv_where B regs Lam v buf ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) ->
  (forall x, o <= x < o + 32 -> ~ pj_foot v D x) ->
  SR (ms_segs B) (mkCfg (@mkst fx' regs1 (getr regs 1) mem1 (seg_rom (ms_segs B))) md1)
    (@write_value_ret fx rc B API RF K L A regs mem md o buf st Lam peak b v t D P).
Proof using SEGS AX.
  intros fx fx' t K regs L A mem md o buf st Lam peak b v D P regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1
    GG GD ENV LG FR FM RP R1 ND WH DL OF.
  apply SR_ret. unfold write_value_ret. exists fx'. split; [exact FR|]. split; [exact FM|].
  pose proof R1 as (HM1 & _).
  split; [exact (guard_of L1 A1 mem1 md1 GG GD HM1)|].
  split.
  { exact (node_keep K regs L A mem md o st buf Lam peak b P L1 A1 mem1 md1 buf1 Lam1 peak1 b1 v t D (wv_lblk Lam)
      ENV LG R1 ND WH DL OF (fun a k H => proj1 (DL a k H))). }
  exists L1, A1, regs1, mem1, md1, buf1, Lam1, peak1, b1. split; [reflexivity|]. split; [exact RP | exact R1].
Qed.

Lemma wv_entry_facts : forall (fx : FPState) t L A regs mem md b o v pretty d D buf st Lam peak,
  @wv_pre fx t L A regs mem md b o v pretty d D buf st Lam peak ->
  wv_env (WV_K t) regs L A mem md o st /\ m_halted md = None /\ m_vm_lazy md = [] /\
  YK0s.ret_ok (getr regs 1) /\ ret_pc (reg_get regs 1) = getr regs 1 /\
  reg_get regs 10 = Z_to_bv 64 o /\ reg_get regs 11 = Z_to_bv 64 v /\
  reg_get regs 12 = Z_to_bv 64 pretty /\ reg_get regs 13 = Z_to_bv 64 d /\
  bv_unsigned (reg_get regs 2) = spZ regs /\
  stk rsegs mem (spZ regs - WV_K t) (spZ regs) /\ IMG_TOP <= spZ regs - WV_K t /\
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) /\
  (v + 56 <= spZ regs - WV_FRAME \/ spZ regs <= v) /\
  wr_rel B API RF (spZ regs - WV_K t) (spZ regs) L A mem md o buf st Lam peak b [] L A mem md buf Lam peak b /\
  ro_agree rsegs mem /\ (0 < v /\ v mod 8 = 0) /\ v + 56 <= 2 ^ 64.
Proof using SEGS AX.
  intros fx t L A regs mem md b o v pretty d D buf st Lam peak PRE0.
  destruct PRE0 as (GG & GD & [PRE TS] & INIT & RO & FM & R10 & R11 & R12 & R13 & HP & HD & HDD & PJ & LG & SPO & EO
    & ES & ND & WH & DL & OF & NEED & RS & ROOMS).
  pose proof PRE as (HM & HWF & HB & Hra & Hal & Hceil & Hsp & HWs & Htp & HWe & Haux).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof ceil_big as CB. unfold IMG_TOP in CB.
  destruct (wvk t) as (EK & EP & EI & ES').
  pose proof (Zle_0_nat (PjTree.depth t)) as D0.
  assert (CAP0 : 0 <= w_cap st) by (destruct PJ as (_ & _ & _ & _ & _ & _ & Rc & _); lia).
  destruct (node_hdr _ _ _ _ _ _ ND) as (num & str & kids & keys & n & cap & HH).
  destruct HH as ((Hv8 & (Hv0 & Hv56 & _)) & _).
  assert (ENV : wv_env (WV_K t) regs L A mem md o st).
  { unfold wv_env. repeat (split; [first [assumption | lia]|]). assumption. }
  split; [exact ENV|]. split; [exact Hh|]. split; [exact Hl|]. split; [exact Hra|].
  split; [rewrite <- getr_reg by reflexivity; apply ret_pc_ok; exact Hra|].
  split; [rewrite <- getr_reg by reflexivity; exact R10|].
  split; [rewrite <- getr_reg by reflexivity; exact R11|].
  split; [rewrite <- getr_reg by reflexivity; exact R12|].
  split; [rewrite <- getr_reg by reflexivity; exact R13|].
  split; [apply sp2|].
  split.
  { apply stk_hi; [unfold IMG_TOP; lia | lia |]. intros a Ha. rewrite <- SEGS. apply HWs. exact Ha. }
  split; [unfold IMG_TOP; lia|].
  split.
  { destruct WH as [[Hv Ho] | (x & y & Hin & Hne & H1 & H2)].
    - intros i Hi. apply ro_false_hi. unfold IMG_TOP. lia.
    - intros i Hi. destruct (lblock_in B _ _ _ _ _ _ _ _ _ LG Hin) as [Hy Hb].
      pose proof (block_range B API _ _ _ _ _ _ HM Hb) as BR.
      apply (ro_false_noimg B SEGS); [lia|].
      replace (v + i) with ((x - 16) + (v + i - x + 16)) by lia.
      apply (block_not_img B API AX L A mem md (x - 16) (y + 16) _ HM Hb). lia. }
  split.
  { destruct WH as [[Hv Ho] | (x & y & Hin & Hne & H1 & H2)]; [right; exact Hv|left].
    destruct (lblock_in B _ _ _ _ _ _ _ _ _ LG Hin) as [Hy Hb].
    pose proof (block_range B API _ _ _ _ _ _ HM Hb) as BR. unfold WV_FRAME. lia. }
  split; [exact (wr_rel_nil B API RF _ _ L A mem md o buf st Lam peak b HM HWF HB RO PJ LG RS)|].
  split; [rewrite <- SEGS; exact RO|]. split; [split; [|exact Hv8] | lia].
  destruct WH as [[Hv Ho] | (x & y & Hin & Hne & H1 & H2)]; [lia|].
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin) as BR. lia.
Qed.

Lemma munch_step : forall K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk m',
  wv_env K regs L A mem md o st -> 128 <= K ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  munch [(spZ regs - 128, spZ regs)] memk m' -> wmono rsegs memk m' -> rm memk m' ->
  wr_rel B API RF (spZ regs - K) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak m' mdk bufk Lamk peakk bk.
Proof using SEGS.
  intros K regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk m' ENV HK RC MU WM RM.
  pose proof ENV as (HM & _ & _ & _ & CEIL & _ & _ & _ & _ & SPO & _).
  pose proof ceil_big as CB. unfold IMG_TOP in CB.
  apply (wr_rel_munch B API RF SEGS _ _ L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk _ m' RC MU WM RM).
  - intros z Hz Hn. cbn [outside] in Hn.
    assert (Hw : spZ regs - 128 <= z < spZ regs).
    { destruct (Z_le_gt_dec (spZ regs - 128) z) as [G1|G1];
        [destruct (Z_lt_ge_dec z (spZ regs)) as [G2|G2]|];
        [lia | exfalso; apply Hn; split; [lia | exact I] | exfalso; apply Hn; split; [lia | exact I]]. }
    lia.
  - lia.
Qed.

Lemma tail_put : forall (fxo fxk : FPState) t regs L A mem md o buf st Lam peak b v D P Lk Ak memk mdk bufk Lamk
    peakk bk x R m' s bs,
  @put_contract fxk rc B API RF ->
  ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
  wv_env (WV_K t) regs L A mem md o st -> ledger B L A mem Lam peak (w_cnt st) (w_fail st) ->
  pj_node rsegs mem (wv_lblk Lam) v t D -> wv_where B regs Lam v buf ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) -> (forall z, o <= z < o + 32 -> ~ pj_foot v D z) ->
  (forall q : reg, bv_unsigned q <> 10 -> reg_get (@fp_regs fxk) q = reg_get (@fp_regs fxo) q) ->
  frm0 (@fp_csr fxk) -> YK0s.ret_ok (getr regs 1) ->
  wr_rel B API RF (spZ regs - WV_K t) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  wr_rooms RF b st (P ++ [bs]) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ [bs]))) + 1 <= WMAX ->
  ms_eqv (MS R (@fp_regs fxk) (Z_to_bv 64 WV_PUT) (@fp_csr fxk) None m' (PropExec.seg_rom rsegs)) x ->
  (forall q, callee_saved q -> getr R (Z_to_bv 5 q) = getr (mkR_of regs) (Z_to_bv 5 q)) ->
  getr R 1 = getr regs 1 -> getr R 10 = Z_to_bv 64 o -> getr R 11 = Z_to_bv 64 s ->
  getr R 12 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  munch [(spZ regs - 128, spZ regs)] memk m' -> wmono rsegs memk m' -> rm memk m' ->
  zbytes_at B m' s bs -> bytes_ok bs -> 0 <= s < 2 ^ 64 -> s + Z.of_nat (length bs) <= 2 ^ 64 ->
  s_where B (ms_regs x) Lamk s (Z.of_nat (length bs)) bufk -> (s + Z.of_nat (length bs) <= o \/ o + 32 <= s) ->
  SR (ms_segs B) (mkCfg x mdk)
    (@write_value_ret fxo rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D (P ++ [bs])).
Proof using SEGS AX CTX.
  intros fxo fxk t regs L A mem md o buf st Lam peak b v D P Lk Ak memk mdk bufk Lamk peakk bk x R m' s bs
    PUTC GG GD ENV LG ND WH DL OF FR FM HRA RC ROOMS NEED HEQ HCS H1 H10 H11 H12 MU WM RM ZB BO S0 SN SW SO.
  pose proof ENV as (HM & INIT & CAP0 & K0 & CEIL & S63 & S16 & WS & WE & SPO & EO & ES & TP & TS).
  destruct (wvk t) as (EK & EP & EI & ES').
  pose proof (Zle_0_nat (PjTree.depth t)) as D0.
  pose proof (munch_step (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk m' ENV
    ltac:(lia) RC MU WM RM) as RC'.
  assert (G : forall k, getr (ms_regs x) k = getr R k) by (intros k; exact (eqv_getr _ _ _ _ _ _ _ _ k HEQ)).
  assert (SPx : spZ (ms_regs x) = spZ regs).
  { unfold spZ. rewrite G. change (getr R 2) with (getr R (Z_to_bv 5 2)).
    rewrite (HCS 2 ltac:(unfold callee_saved; lia)), getr_mkR_of. reflexivity. }
  assert (G4 : getr (ms_regs x) 4 = getr regs 4).
  { rewrite G. change (getr R 4) with (getr R (Z_to_bv 5 4)).
    rewrite (HCS 4 ltac:(unfold callee_saved; lia)), getr_mkR_of. reflexivity. }
  rewrite (eqv_shape _ _ _ _ HEQ).
  replace (YK11.seg_rom rsegs) with (YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  apply (put_chain fxk PUTC (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak m' mdk bufk Lamk peakk bk
    (ms_regs x) s bs []).
  - exact ENV.
  - exact RC'.
  - rewrite app_nil_r. exact ROOMS.
  - rewrite app_nil_r. exact NEED.
  - rewrite SPx. lia.
  - rewrite SPx. lia.
  - rewrite SPx. exact S16.
  - exact G4.
  - rewrite G, H1. exact HRA.
  - rewrite G. exact H10.
  - rewrite G. exact H11.
  - rewrite G. exact H12.
  - exact ZB.
  - exact BO.
  - exact S0.
  - exact SN.
  - exact SW.
  - exact SO.
  - intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP R1 _.
    rewrite G, H1.
    apply (wv_fin fxo fxk t (WV_K t) regs L A mem md o buf st Lam peak b v D (P ++ [bs]) regs1 L1 A1 mem1 md1
      buf1 Lam1 peak1 b1 GG GD ENV LG FR FM); [| exact R1 | exact ND | exact WH | exact DL | exact OF].
    exact (regs_pres_trans _ _ _ (regs_kept regs R _ _ _ _ _ _ x HEQ HCS) RP).
Qed.

Lemma entry_tail : forall (fx : FPState) t L A regs mem md b o v pretty d D buf st Lam peak s bs,
  (forall fx' : FPState, @put_contract fx' rc B API RF) ->
  @wv_pre fx t L A regs mem md b o v pretty d D buf st Lam peak ->
  wvpieces t (negb (pretty =? 0)) d = [bs] ->
  Exec.evt rsegs (fun y => wv_exitr (Z_to_bv 64 WV_PUT) (reg_get regs 1) (reg_get regs 2) (reg_get regs 3)
      (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
      (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
      (reg_get regs 27) (@fp_regs fx) (@fp_csr fx) (spZ regs - WV_K t) mem
      (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 s /\ x2 = Z_to_bv 64 (Z.of_nat (length bs))) y /\
      ro_agree rsegs (ms_mem y))
    (MS (mkR_of regs) (@fp_regs fx) (Z_to_bv 64 WRITE_VALUE_PC) (@fp_csr fx) None mem (PropExec.seg_rom rsegs)) ->
  (forall m', ro_agree rsegs m' -> munch [(spZ regs - 128, spZ regs)] mem m' -> zbytes_at B m' s bs) ->
  bytes_ok bs -> 0 <= s < 2 ^ 64 -> s + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall regsx, s_where B regsx Lam s (Z.of_nat (length bs)) buf) -> (s + Z.of_nat (length bs) <= o \/ o + 32 <= s) ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
    (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
       (wvpieces t (negb (pretty =? 0)) d)).
Proof using SEGS AX CTX.
  intros fx t L A regs mem md b o v pretty d D buf st Lam peak s bs PUTC PRE0 EPc EV ZBH BO S0 SN SW SO.
  pose proof (wv_entry_facts fx t L A regs mem md b o v pretty d D buf st Lam peak PRE0)
    as (ENV & Hh & Hl & HRA & PC & Q10 & Q11 & Q12 & Q13 & SP2 & STK & LO & NRO & DV & R0 & RO & (V0 & V8) & V56).
  destruct PRE0 as (GG & GD & PRE & INIT & RO0 & FM & R10 & R11 & R12 & R13 & HP & HD & HDD & PJ & LG & SPO & EO & ES
    & ND & WH & DL & OF & NEED & RS & ROOMS).
  rewrite SEGS. eapply kA_lift; [exact Hh | exact Hl | exact EV |].
  intros x y [HQ ROy] HEQ HRM.
  destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Ey & (E0 & E1 & E2)
    & MU & WM & ST'). subst y.
  cbn [ms_mem MS] in ROy.
  rewrite SP2 in MU. unfold WV_FRAME in MU.
  assert (XM : ms_mem x = m') by (destruct HEQ as (_ & _ & _ & _ & _ & _ & HMx & _); cbn in HMx; congruence).
  rewrite XM in HRM. rewrite <- SEGS. rewrite EPc. change [bs] with ([] ++ [bs]).
  eapply (tail_put fx fx t regs L A mem md o buf st Lam peak b v D [] L A mem md buf Lam peak b x _ m' s bs
    (PUTC fx) GG GD ENV LG ND WH DL OF (fun q _ => eq_refl) FM HRA R0).
  - rewrite <- EPc. exact ROOMS.
  - rewrite <- EPc. exact NEED.
  - exact HEQ.
  - callee_cases.
  - reflexivity.
  - rewrite <- E0. reflexivity.
  - rewrite <- E1. reflexivity.
  - rewrite <- E2. reflexivity.
  - exact MU.
  - exact WM.
  - exact HRM.
  - exact (ZBH m' ROy MU).
  - exact BO.
  - exact S0.
  - exact SN.
  - apply SW.
  - exact SO.
Qed.

Lemma tail_ps : forall (fxo fxk : FPState) t regs L A mem md o buf st Lam peak b v D P Lk Ak memk mdk bufk Lamk
    peakk bk x R m' s bs,
  @put_string_contract fxk rc B API RF ->
  ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
  wv_env (WV_K t) regs L A mem md o st -> ledger B L A mem Lam peak (w_cnt st) (w_fail st) ->
  pj_node rsegs mem (wv_lblk Lam) v t D -> wv_where B regs Lam v buf ->
  (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) -> (forall z, o <= z < o + 32 -> ~ pj_foot v D z) ->
  (forall q : reg, bv_unsigned q <> 10 -> reg_get (@fp_regs fxk) q = reg_get (@fp_regs fxo) q) ->
  frm0 (@fp_csr fxk) -> YK0s.ret_ok (getr regs 1) ->
  wr_rel B API RF (spZ regs - WV_K t) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk ->
  wr_rooms RF b st (P ++ spieces bs) ->
  Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (P ++ spieces bs))) + 1 <= WMAX ->
  ms_eqv (MS R (@fp_regs fxk) (Z_to_bv 64 WV_PUT_STRING) (@fp_csr fxk) None m' (PropExec.seg_rom rsegs)) x ->
  (forall q, callee_saved q -> getr R (Z_to_bv 5 q) = getr (mkR_of regs) (Z_to_bv 5 q)) ->
  getr R 1 = getr regs 1 -> getr R 10 = Z_to_bv 64 o -> getr R 11 = Z_to_bv 64 s ->
  munch [(spZ regs - 128, spZ regs)] memk m' -> wmono rsegs memk m' -> rm memk m' ->
  zbytes_at B m' s (bs ++ [0]) -> bytes_ok bs -> no_zero bs ->
  str_where B Lamk s (Z.of_nat (length bs) + 1) bufk ->
  SR (ms_segs B) (mkCfg x mdk)
    (@write_value_ret fxo rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D (P ++ spieces bs)).
Proof using SEGS AX CTX.
  intros fxo fxk t regs L A mem md o buf st Lam peak b v D P Lk Ak memk mdk bufk Lamk peakk bk x R m' s bs
    PSC GG GD ENV LG ND WH DL OF FR FM HRA RC ROOMS NEED HEQ HCS H1 H10 H11 MU WM RM ZB BO NZ SW.
  pose proof ENV as (HM & INIT & CAP0 & K0 & CEIL & S63 & S16 & WS & WE & SPO & EO & ES & TP & TS).
  destruct (wvk t) as (EK & EP & EI & ES').
  pose proof (Zle_0_nat (PjTree.depth t)) as D0.
  pose proof (munch_step (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk m' ENV
    ltac:(lia) RC MU WM RM) as RC'.
  assert (G : forall k, getr (ms_regs x) k = getr R k) by (intros k; exact (eqv_getr _ _ _ _ _ _ _ _ k HEQ)).
  assert (SPx : spZ (ms_regs x) = spZ regs).
  { unfold spZ. rewrite G. change (getr R 2) with (getr R (Z_to_bv 5 2)).
    rewrite (HCS 2 ltac:(unfold callee_saved; lia)), getr_mkR_of. reflexivity. }
  assert (G4 : getr (ms_regs x) 4 = getr regs 4).
  { rewrite G. change (getr R 4) with (getr R (Z_to_bv 5 4)).
    rewrite (HCS 4 ltac:(unfold callee_saved; lia)), getr_mkR_of. reflexivity. }
  rewrite (eqv_shape _ _ _ _ HEQ).
  replace (YK11.seg_rom rsegs) with (YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  apply (ps_chain fxk PSC (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak m' mdk bufk Lamk peakk bk
    (ms_regs x) s bs []).
  - exact GG.
  - exact GD.
  - exact FM.
  - exact ENV.
  - exact RC'.
  - rewrite app_nil_r. exact ROOMS.
  - rewrite app_nil_r. exact NEED.
  - rewrite SPx. lia.
  - rewrite SPx. lia.
  - rewrite SPx. exact S16.
  - exact G4.
  - rewrite G, H1. exact HRA.
  - rewrite G. exact H10.
  - rewrite G. exact H11.
  - exact ZB.
  - exact BO.
  - exact NZ.
  - exact SW.
  - intros fx' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 FR' FM' RP R1 _.
    rewrite G, H1.
    apply (wv_fin fxo fx' t (WV_K t) regs L A mem md o buf st Lam peak b v D (P ++ spieces bs) regs1 L1 A1 mem1 md1
      buf1 Lam1 peak1 b1 GG GD ENV LG); [| exact FM' | | exact R1 | exact ND | exact WH | exact DL | exact OF].
    + intros q Hq. rewrite (FR' q Hq). exact (FR q Hq).
    + exact (regs_pres_trans _ _ _ (regs_kept regs R _ _ _ _ _ _ x HEQ HCS) RP).
Qed.

Section Body.
Variables (fx : FPState) (t : jv) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (b : rf_R RF) (o v pretty d : Z) (D : list (Z * Z)) (buf : Z) (st : wst) (Lam : list (Z * Z))
  (peak : Z).
Hypothesis PRE0 : @wv_pre fx t L A regs mem md b o v pretty d D buf st Lam peak.
Hypothesis PUTC : forall fx' : FPState, @put_contract fx' rc B API RF.
Hypothesis INDC : forall fx' : FPState, @indent_contract fx' rc B API RF.
Hypothesis PSC : forall fx' : FPState, @put_string_contract fx' rc B API RF.
Hypothesis SLC : strlen_contract.
Hypothesis BSP : block_slack_present B API.

Ltac ents :=
  pose proof (wv_entry_facts fx t L A regs mem md b o v pretty d D buf st Lam peak PRE0)
    as (ENV & Hh & Hl & HRA & PC & Q10 & Q11 & Q12 & Q13 & SP2 & STK & LO & NRO & DV & R0 & RO & (V0 & V8) & V56);
  pose proof PRE0 as (GG & GD & [PRE TS] & INIT & RO0 & FM & R10 & R11 & R12 & R13 & HP & HD & HDD & PJ & LG & SPO
    & EO & ES & ND & WH & DL & OF & NEED & RS & ROOMS);
  pose proof ENV as (HM & _ & CAP0 & K0 & CEIL & S63 & S16 & WS & WE & _ & _ & _ & TP & _);
  pose proof ceil_big as CEB; unfold IMG_TOP in CEB;
  destruct (wvk t) as (EK & EP & EI & EPK).

Lemma img_case : forall s bs,
  wvpieces t (negb (pretty =? 0)) d = [bs] ->
  img_ok s bs = true ->
  existsb (fun sg => (bv_unsigned (fst sg) <=? s) && (s <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
    (segments_reserved rsegs) = true ->
  bytes_ok bs -> 0 <= s -> s + Z.of_nat (length bs) <= IMG_TOP ->
  Exec.evt rsegs (fun y => wv_exitr (Z_to_bv 64 WV_PUT) (reg_get regs 1) (reg_get regs 2) (reg_get regs 3)
      (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
      (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
      (reg_get regs 27) (@fp_regs fx) (@fp_csr fx) (spZ regs - WV_K t) mem
      (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 s /\ x2 = Z_to_bv 64 (Z.of_nat (length bs))) y /\
      ro_agree rsegs (ms_mem y))
    (MS (mkR_of regs) (@fp_regs fx) (Z_to_bv 64 WRITE_VALUE_PC) (@fp_csr fx) None mem (PropExec.seg_rom rsegs)) ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
    (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
       (wvpieces t (negb (pretty =? 0)) d)).
Proof.
  intros s bs EPc IMG SEG BO S0 SN EV. ents.
  apply (entry_tail fx t L A regs mem md b o v pretty d D buf st Lam peak s bs PUTC PRE0 EPc EV).
  - intros m' RO' _. exact (img_zbytes B SEGS m' s bs RO' IMG).
  - exact BO.
  - lia.
  - lia.
  - intros regsx. exact (img_where B SEGS regsx Lam s _ buf bs SEG IMG eq_refl).
  - left. lia.
Qed.

Lemma hdr_node : forall ty, tag t = ty -> exists str kids keys n pa pb, wv_node mem v ty str kids keys n pa pb.
Proof.
  intros ty Ht. ents.
  destruct (node_hdr _ _ _ _ _ _ ND) as (num & str & kids & keys & n & cap & HH).
  destruct (pj_hdr_wv_node _ _ _ _ _ _ _ _ _ HH) as (pa & pb & WN). rewrite Ht in WN.
  exists str, kids, keys, n, pa, pb. exact WN.
Qed.

Lemma case_null : t = JNull ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
    (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
       (wvpieces t (negb (pretty =? 0)) d)).
Proof.
  intros Ht. destruct (hdr_node 0 ltac:(rewrite Ht; reflexivity)) as (str & kids & keys & n & pa & pb & WN). ents.
  apply (img_case WV_S_NULL [110; 117; 108; 108]).
  - rewrite Ht. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold bytes_ok. repeat constructor; lia.
  - unfold WV_S_NULL. lia.
  - unfold WV_S_NULL, IMG_TOP. cbn [length Z.of_nat]. lia.
  - unfold mkR_of. rewrite Q10, Q11, Q12, Q13.
    eapply wv_null_ro; [exact RO | exact WN | exact NRO | exact V0 | exact V8 | rewrite SP2; exact STK
      | rewrite SP2; unfold WV_FRAME; lia | exact LO | rewrite SP2; exact DV].
Qed.

Lemma case_false : t = JFalse ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
    (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
       (wvpieces t (negb (pretty =? 0)) d)).
Proof.
  intros Ht. destruct (hdr_node 1 ltac:(rewrite Ht; reflexivity)) as (str & kids & keys & n & pa & pb & WN). ents.
  apply (img_case WV_S_FALSE [102; 97; 108; 115; 101]).
  - rewrite Ht. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold bytes_ok. repeat constructor; lia.
  - unfold WV_S_FALSE. lia.
  - unfold WV_S_FALSE, IMG_TOP. cbn [length Z.of_nat]. lia.
  - unfold mkR_of. rewrite Q10, Q11, Q12, Q13.
    eapply wv_false_ro; [exact RO | exact WN | exact NRO | exact V0 | exact V8 | rewrite SP2; exact STK
      | rewrite SP2; unfold WV_FRAME; lia | exact LO | rewrite SP2; exact DV].
Qed.

Lemma case_true : t = JTrue ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
    (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
       (wvpieces t (negb (pretty =? 0)) d)).
Proof.
  intros Ht. destruct (hdr_node 2 ltac:(rewrite Ht; reflexivity)) as (str & kids & keys & n & pa & pb & WN). ents.
  apply (img_case WV_S_TRUE [116; 114; 117; 101]).
  - rewrite Ht. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - unfold bytes_ok. repeat constructor; lia.
  - unfold WV_S_TRUE. lia.
  - unfold WV_S_TRUE, IMG_TOP. cbn [length Z.of_nat]. lia.
  - unfold mkR_of. rewrite Q10, Q11, Q12, Q13.
    eapply wv_true_ro; [exact RO | exact WN | exact NRO | exact V0 | exact V8 | rewrite SP2; exact STK
      | rewrite SP2; unfold WV_FRAME; lia | exact LO | rewrite SP2; exact DV].
Qed.

Lemma cstr_zbytes : forall s k bs m', pj_cstr rsegs mem (wv_lblk Lam) s k bs -> In (s, k) Lam ->
  munch [(spZ regs - 128, spZ regs)] mem m' -> zbytes_at B m' s (bs ++ [0]).
Proof.
  intros s k bs m' (_ & Hk & TXT & BS) Hin MU. ents.
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin) as BR.
  assert (HL0 : Z.of_nat (length (bs ++ [0])) <= k) by (rewrite length_app; cbn [length]; lia).
  pose proof (proj2 (zbytes_core mem s (bs ++ [0]) ltac:(lia) ltac:(lia)) BS) as ZM.
  intros i Hi. rewrite SEGS.
  destruct (raw_mbyte rsegs mem m' (s + i) (munch_raw _ mem m' (s + i) MU ltac:(lia)
    ltac:(cbn [outside]; split; [lia | exact I]))) as [E _].
  rewrite E. apply ZM. exact Hi.
Qed.

Lemma case_num : forall txt bits, t = JNum txt bits ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
    (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
       (wvpieces t (negb (pretty =? 0)) d)).
Proof.
  intros txt bits Ht. ents.
  pose proof ND as ND'. rewrite Ht in ND'. cbn [pj_node] in ND'.
  destruct ND' as (_ & _ & num & str & kids & keys & n & cap & HH & _ & _ & _ & _ & _ & k & CS & ED).
  destruct (pj_hdr_wv_node _ _ _ _ _ _ _ _ _ HH) as (pa & pb & WN). cbn [tag] in WN.
  destruct (DL str k ltac:(rewrite ED; left; reflexivity)) as [Hin Hne].
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin) as BR.
  pose proof CS as (_ & Hk & TXT & BS).
  destruct (lblock_in B _ _ _ _ _ _ _ _ _ LG Hin) as [Hk0 Hb].
  set (len := Z.of_nat (length txt)) in *.
  set (r := (- (str + len + 1)) mod 8).
  assert (Hr : 0 <= r < 8) by (unfold r; apply Z.mod_pos_bound; lia).
  pose proof (slack_bound (str + len + 1) (str + k) ltac:(lia)) as SB.
  fold r in SB.
  destruct (present_bytes mem (str + len + 1) r ltac:(lia) ltac:(lia) ltac:(lia)) as (sl & Hsl & BSL).
  { intros i Hi. destruct (Z_lt_ge_dec (str + len + 1 + i) (str + k)) as [Hlt|Hge].
    - replace (str + len + 1 + i) with (str + (len + 1 + i)) by lia.
      exact (ledger_block_present B API _ _ _ _ _ _ _ _ _ _ (len + 1 + i) HM LG Hin ltac:(lia)).
    - apply (BSP L A mem md (str - 16) (k + 16) _ HM Hb). lia. }
  assert (BS2 : bytes_at rsegs mem str (map (Z_to_bv 8) txt ++ Z_to_bv 8 0 :: sl)).
  { replace (map (Z_to_bv 8) txt ++ Z_to_bv 8 0 :: sl) with (map (Z_to_bv 8) (txt ++ [0]) ++ sl)
      by (rewrite map_app, <- app_assoc; reflexivity).
    apply (wnd_app mem str (str + len + 1)); [exact BS | rewrite length_map, length_app; cbn [length]; lia | exact BSL]. }
  assert (EPc : wvpieces t (negb (pretty =? 0)) d = [txt]) by (rewrite Ht; reflexivity).
  apply (entry_tail fx t L A regs mem md b o v pretty d D buf st Lam peak str txt PUTC PRE0 EPc).
  - unfold mkR_of. rewrite Q10, Q11, Q12, Q13.
    eapply (wv_num_ro SLC); [exact RO | exact WN | exact NRO | exact V0 | exact V8 | lia | rewrite SP2; exact STK
      | rewrite SP2; unfold WV_FRAME; lia | exact LO | rewrite SP2; exact DV | exact BS2 | exact TXT
      | rewrite Hsl; unfold r; lia | rewrite Hsl, SP2; unfold WV_FRAME; lia].
  - intros m' _ MU i Hi. pose proof (cstr_zbytes str k txt m' CS Hin MU i) as Z1.
    rewrite length_app in Z1. cbn [length] in Z1. rewrite app_nth1 in Z1 by lia. apply Z1. lia.
  - exact (bytes_ok_lt txt TXT).
  - lia.
  - lia.
  - intros regsx. right. right. exists str, k. split; [exact Hin|]. split; [exact Hne|]. lia.
  - left. lia.
Qed.

Lemma case_str : forall s, t = JStr s ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
    (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
       (wvpieces t (negb (pretty =? 0)) d)).
Proof.
  intros s Ht. ents.
  pose proof ND as ND'. rewrite Ht in ND'. cbn [pj_node] in ND'.
  destruct ND' as (_ & _ & num & str & kids & keys & n & cap & HH & _ & _ & _ & _ & k & CS & ED).
  destruct (pj_hdr_wv_node _ _ _ _ _ _ _ _ _ HH) as (pa & pb & WN). cbn [tag] in WN.
  destruct (DL str k ltac:(rewrite ED; left; reflexivity)) as [Hin Hne].
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG Hin) as BR.
  pose proof CS as (_ & Hk & TXT & BS).
  assert (NZ : wv_nz str WV_S_EMPTY = str) by (unfold wv_nz; rewrite (proj2 (Z.eqb_neq str 0)) by lia; reflexivity).
  assert (EPc : wvpieces t (negb (pretty =? 0)) d = [] ++ spieces s) by (rewrite Ht; reflexivity).
  rewrite EPc. rewrite SEGS. eapply kA_lift; [exact Hh | exact Hl | |].
  { unfold mkR_of. rewrite Q10, Q11, Q12, Q13.
    eapply wv_str_ro; [exact RO | exact WN | exact NRO | exact V0 | exact V8 | lia | rewrite SP2; exact STK
      | rewrite SP2; unfold WV_FRAME; lia | exact LO | rewrite SP2; exact DV]. }
  intros x y [HQ ROy] HEQ HRM.
  destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Ey & (E0 & E1)
    & MU & WM & ST'). subst y.
  rewrite SP2 in MU. unfold WV_FRAME in MU.
  assert (XM : ms_mem x = m') by (destruct HEQ as (_ & _ & _ & _ & _ & _ & HMx & _); cbn in HMx; congruence).
  rewrite XM in HRM. rewrite <- SEGS.
  eapply (tail_ps fx fx t regs L A mem md o buf st Lam peak b v D [] L A mem md buf Lam peak b x _ m' str s
    (PSC fx) GG GD ENV LG ND WH DL OF (fun q _ => eq_refl) FM HRA R0).
  - rewrite <- EPc. exact ROOMS.
  - rewrite <- EPc. exact NEED.
  - exact HEQ.
  - callee_cases.
  - reflexivity.
  - rewrite <- E0. reflexivity.
  - rewrite <- NZ, <- E1. reflexivity.
  - exact MU.
  - exact WM.
  - exact HRM.
  - exact (cstr_zbytes str k s m' CS Hin MU).
  - exact (bytes_ok_lt s TXT).
  - exact (no_zero_lt s TXT).
  - right. exists str, k. split; [exact Hin|]. split; [exact Hne|]. lia.
Qed.

Local Abbreviation WP := (wvpieces t (negb (pretty =? 0)) d).
Local Abbreviation PB := (negb (pretty =? 0)).
Local Abbreviation GOALQ := (@write_value_ret fx rc B API RF (WV_K t) L A regs mem md o buf st Lam peak b v t D
  (wvpieces t (negb (pretty =? 0)) d)).

Definition c16ok (c : cell) : Prop := (exists j, c = CB 8 j) \/ (exists w, c = C8 w).

Definition FI (fxk : FPState) (c16 : cell) (P : list (list Z)) (Lk : layout) (Ak : astate) (memk : word -> option byte)
    (mdk : Model) (bufk : Z) (Lamk : list (Z * Z)) (peakk : Z) (bk : rf_R RF) : Prop :=
  (forall q : reg, bv_unsigned q <> 10 -> reg_get (@fp_regs fxk) q = reg_get (@fp_regs fx) q) /\
  frm0 (@fp_csr fxk) /\
  wr_rel B API RF (spZ regs - WV_K t) (spZ regs) L A mem md o buf st Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk /\
  c16ok c16 /\
  exists junk, wv_frame memk (reg_get regs 2) junk (Z_to_bv 64 d) c16 (reg_get regs 1) (reg_get regs 8) (reg_get regs 9)
    (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27).

Local Abbreviation SEPC := (C8 (Z_to_bv 64 (wv_sep pretty))).

Lemma fi_facts : forall {c16} fxk P Lk Ak memk mdk bufk Lamk peakk bk, FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk ->
  aa_MR API Lk Ak memk mdk /\ m_halted mdk = None /\ m_vm_lazy mdk = [] /\
  stk rsegs memk (spZ regs - WV_K t) (bv_unsigned (reg_get regs 2) - WV_FRAME) /\
  pj_node rsegs memk (wv_lblk Lamk) v t D /\
  (forall a k, In (a, k) D -> In (a, k) Lamk /\ a <> bufk) /\ ro_agree rsegs memk.
Proof.
  intros c16 fxk P Lk Ak memk mdk bufk Lamk peakk bk (FRk & FMk & RC & C16 & junk & FRM). ents.
  pose proof RC as (HMk & _ & _ & [ROk _] & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMk) as (Hhk & Hlk & _).
  destruct (wr_writable B API RF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - WV_K t) (spZ regs) RC
    ltac:(lia) ltac:(lia) WS WE) as [WSk _].
  assert (DLk : forall a k, In (a, k) D -> In (a, k) Lamk /\ a <> bufk).
  { intros a k H. destruct (DL a k H) as [H1 H2].
    exact (lam_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a k RC LG H1 H2). }
  split; [exact HMk|]. split; [exact Hhk|]. split; [exact Hlk|].
  split.
  { rewrite SP2. apply stk_hi; [unfold IMG_TOP; lia | unfold WV_FRAME; lia |].
    intros a Ha. rewrite <- SEGS. apply WSk. unfold WV_FRAME in Ha. lia. }
  split.
  { exact (node_keep (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk v t D
      (wv_lblk Lamk) ENV LG RC ND WH DL OF (fun a k H => proj1 (DLk a k H))). }
  split; [exact DLk|]. rewrite <- SEGS. exact ROk.
Qed.

Lemma frame_keep : forall junk c16 Lk Ak memk mdk bufk stk' Lamk peakk bk P1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 lo hi,
  aa_MR API Lk Ak memk mdk ->
  wr_rel B API RF lo hi Lk Ak memk mdk o bufk stk' Lamk peakk bk P1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  hi <= spZ regs - 128 -> c16ok c16 ->
  wv_frame memk (reg_get regs 2) junk (Z_to_bv 64 d) c16 (reg_get regs 1) (reg_get regs 8) (reg_get regs 9)
    (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) ->
  wv_frame mem1 (reg_get regs 2) junk (Z_to_bv 64 d) c16 (reg_get regs 1) (reg_get regs 8) (reg_get regs 9)
    (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27).
Proof.
  intros junk c16 Lk Ak memk mdk bufk stk' Lamk peakk bk P1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 lo hi HMk R1 Hhi C16 FRM.
  ents. unfold wv_frame in *.
  destruct C16 as [[j ->]|[w ->]];
    (eapply (wr_cells B API RF SEGS);
     [exact HMk | exact R1 | exact FRM
     | rewrite ?SP2; unfold WV_FRAME; lia
     | rewrite ?SP2; unfold WV_FRAME; lia
     | rewrite ?SP2; unfold WV_FRAME; left; cbn [cells_size csize]; lia
     | rewrite ?SP2; unfold WV_FRAME; cbn [cells_size csize]; eapply off_errno_sub; [exact ES | lia | lia]]).
Qed.

Definition LSR (i : Z) : bvmap 5 word :=
  mkR (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned (reg_get regs 2) - WV_FRAME)) (reg_get regs 3) (reg_get regs 4)
    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 o) (Z_to_bv 64 v)
    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
    (Z_to_bv 64 0) (Z_to_bv 64 56) (Z_to_bv 64 pretty) (Z_to_bv 64 0) (Z_to_bv 64 (d + 1))
    (Z_to_bv 64 (wv_seplen pretty)) (Z_to_bv 64 WV_S_COMMA) (Z_to_bv 64 (56 * i)) (Z_to_bv 64 (8 * i))
    (Z_to_bv 64 i) (Z_to_bv 64 6) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

Definition ls_cs (rg : bvmap 5 word) (i : Z) : Prop :=
  forall q, callee_saved q -> getr rg (Z_to_bv 5 q) = getr (LSR i) (Z_to_bv 5 q).

Lemma ls_cs_eqv : forall pc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc i m x rg,
  ms_eqv (wv_ls pc ra (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    t3 t4 t5 t6 F fc o v pretty d i m) x ->
  regs_preserved (ms_regs x) rg -> ls_cs rg i.
Proof.
  intros pc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc i m x rg HEQ RP. unfold wv_ls in HEQ.
  intros q Hq. rewrite (RP q Hq), (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). revert q Hq. callee_cases.
Qed.

Lemma ls_resume : forall rg i F fc pc m, ls_cs rg i ->
  MS (mkR_of rg) F (Z_to_bv 64 pc) fc None m (PropExec.seg_rom rsegs) =
  wv_ls pc (reg_get rg 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get rg 5) (reg_get rg 6)
    (reg_get rg 7) (reg_get rg 10) (reg_get rg 11) (reg_get rg 12) (reg_get rg 13) (reg_get rg 14) (reg_get rg 15)
    (reg_get rg 16) (reg_get rg 17) (reg_get rg 28) (reg_get rg 29) (reg_get rg 30) (reg_get rg 31) F fc o v
    pretty d i m.
Proof.
  intros rg i F fc pc m H. unfold wv_ls. f_equal. unfold mkR_of. f_equal;
    (etransitivity;
     [ apply (agree_get rg (LSR i) _ H); unfold callee_saved;
       match goal with |- context [bv_unsigned ?k] => let w := eval vm_compute in (bv_unsigned k) in
         change (bv_unsigned k) with w end; lia
     | reflexivity ]).
Qed.

Lemma st_put : forall {c16} (fxk : FPState) P Lk Ak memk mdk bufk Lamk peakk bk R x RA s bs Rest Q,
  FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk -> WP = P ++ [bs] ++ Rest ->
  ms_eqv (MS R (@fp_regs fxk) (Z_to_bv 64 WV_PUT) (@fp_csr fxk) None memk (PropExec.seg_rom rsegs)) x ->
  getr R 1 = Z_to_bv 64 RA -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
  getr R 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - WV_FRAME) -> getr R 4 = reg_get regs 4 ->
  getr R 10 = Z_to_bv 64 o -> getr R 11 = Z_to_bv 64 s -> getr R 12 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  img_ok s bs = true ->
  existsb (fun sg => (bv_unsigned (fst sg) <=? s) && (s <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
    (segments_reserved rsegs) = true ->
  bytes_ok bs -> 0 <= s -> s + Z.of_nat (length bs) <= IMG_TOP ->
  (forall regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, regs_preserved (ms_regs x) regs1 ->
     FI fxk c16 (P ++ [bs]) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fxk regs1 (Z_to_bv 64 RA) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg x mdk) Q.
Proof.
  intros c16 fxk P Lk Ak memk mdk bufk Lamk peakk bk R x RA s bs Rest Q (FRk & FMk & RC & C16 & junk & FRM) EW HEQ
    G1 RA0 RA2 G2 G4 G10 G11 G12 IMG SEG BO S0 SN K'. ents.
  assert (G : forall k, getr (ms_regs x) k = getr R k) by (intros k; exact (eqv_getr _ _ _ _ _ _ _ _ k HEQ)).
  assert (SPx : spZ (ms_regs x) = spZ regs - 128).
  { unfold spZ at 1. rewrite G, G2, SP2. unfold WV_FRAME. apply unsigned_lit. lia. }
  pose proof RC as (HMk & _ & _ & [ROk _] & _).
  rewrite (eqv_shape _ _ _ _ HEQ).
  replace (YK11.seg_rom rsegs) with (YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  apply (put_chain fxk (PUTC fxk) (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk
    (ms_regs x) s bs Rest Q ENV RC).
  - rewrite <- EW. exact ROOMS.
  - rewrite <- EW. exact NEED.
  - rewrite SPx. lia.
  - rewrite SPx. lia.
  - rewrite SPx. Z.div_mod_to_equations. lia.
  - rewrite G, G4. symmetry. apply getr_reg. reflexivity.
  - rewrite G, G1. exact (ret_ok_lit RA RA0 RA2).
  - rewrite G. exact G10.
  - rewrite G. exact G11.
  - rewrite G. exact G12.
  - assert (ROr : ro_agree rsegs memk) by (rewrite <- SEGS; exact ROk). exact (img_zbytes B SEGS memk s bs ROr IMG).
  - exact BO.
  - lia.
  - lia.
  - exact (img_where B SEGS (ms_regs x) Lamk s _ bufk bs SEG IMG eq_refl).
  - left. lia.
  - intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP R1 R1'.
    rewrite G, G1. apply (K' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP).
    split; [exact FRk|]. split; [exact FMk|]. split; [exact R1|]. split; [exact C16|].
    exists junk. rewrite SPx in R1'. eapply frame_keep; [exact HMk | exact R1' | lia | exact C16 | exact FRM].
Qed.

Lemma st_ind : forall {c16} (fxk : FPState) P Lk Ak memk mdk bufk Lamk peakk bk R x RA dd Rest Q,
  FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk -> WP = P ++ wind PB dd ++ Rest ->
  ms_eqv (MS R (@fp_regs fxk) (Z_to_bv 64 WV_INDENT) (@fp_csr fxk) None memk (PropExec.seg_rom rsegs)) x ->
  getr R 1 = Z_to_bv 64 RA -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
  getr R 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - WV_FRAME) -> getr R 4 = reg_get regs 4 ->
  getr R 10 = Z_to_bv 64 o -> getr R 11 = Z_to_bv 64 pretty -> getr R 12 = Z_to_bv 64 dd ->
  - 2 ^ 31 <= dd < 2 ^ 31 ->
  (forall regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, regs_preserved (ms_regs x) regs1 ->
     FI fxk c16 (P ++ wind PB dd) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fxk regs1 (Z_to_bv 64 RA) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg x mdk) Q.
Proof.
  intros c16 fxk P Lk Ak memk mdk bufk Lamk peakk bk R x RA dd Rest Q (FRk & FMk & RC & C16 & junk & FRM) EW HEQ
    G1 RA0 RA2 G2 G4 G10 G11 G12 HDd K'. ents.
  assert (G : forall k, getr (ms_regs x) k = getr R k) by (intros k; exact (eqv_getr _ _ _ _ _ _ _ _ k HEQ)).
  assert (SPx : spZ (ms_regs x) = spZ regs - 128).
  { unfold spZ at 1. rewrite G, G2, SP2. unfold WV_FRAME. apply unsigned_lit. lia. }
  pose proof RC as (HMk & _).
  rewrite (eqv_shape _ _ _ _ HEQ).
  replace (YK11.seg_rom rsegs) with (YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 WV_INDENT) with (Z_to_bv 64 INDENT_PC).
  apply (indent_chain fxk (INDC fxk) (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk
    (ms_regs x) pretty dd Rest Q ENV RC).
  - rewrite <- EW. exact ROOMS.
  - rewrite <- EW. exact NEED.
  - rewrite SPx. lia.
  - rewrite SPx. lia.
  - rewrite SPx. Z.div_mod_to_equations. lia.
  - rewrite G, G4. symmetry. apply getr_reg. reflexivity.
  - rewrite G, G1. exact (ret_ok_lit RA RA0 RA2).
  - rewrite G. exact G10.
  - rewrite G. exact G11.
  - rewrite G. exact G12.
  - exact HP.
  - exact HDd.
  - intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP R1 R1'.
    rewrite G, G1. apply (K' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP).
    split; [exact FRk|]. split; [exact FMk|]. split; [exact R1|]. split; [exact C16|].
    exists junk. rewrite SPx in R1'. eapply frame_keep; [exact HMk | exact R1' | lia | exact C16 | exact FRM].
Qed.

Lemma st_ps : forall {c16} (fxk : FPState) P Lk Ak memk mdk bufk Lamk peakk bk R x RA s k nm Rest Q,
  FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk -> WP = P ++ spieces nm ++ Rest ->
  ms_eqv (MS R (@fp_regs fxk) (Z_to_bv 64 WV_PUT_STRING) (@fp_csr fxk) None memk (PropExec.seg_rom rsegs)) x ->
  getr R 1 = Z_to_bv 64 RA -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
  getr R 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - WV_FRAME) -> getr R 4 = reg_get regs 4 ->
  getr R 10 = Z_to_bv 64 o -> getr R 11 = Z_to_bv 64 s ->
  In (s, k) D -> pj_cstr rsegs memk (wv_lblk Lamk) s k nm ->
  (forall (fx' : FPState) regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, regs_preserved (ms_regs x) regs1 ->
     FI fx' c16 (P ++ spieces nm) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fx' regs1 (Z_to_bv 64 RA) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg x mdk) Q.
Proof.
  intros c16 fxk P Lk Ak memk mdk bufk Lamk peakk bk R x RA s k nm Rest Q FIk EW HEQ
    G1 RA0 RA2 G2 G4 G10 G11 HinD CS K'.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FIk) as (_ & _ & _ & _ & _ & DLk & _).
  destruct FIk as (FRk & FMk & RC & C16 & junk & FRM). ents.
  assert (G : forall k, getr (ms_regs x) k = getr R k) by (intros k'; exact (eqv_getr _ _ _ _ _ _ _ _ k' HEQ)).
  assert (SPx : spZ (ms_regs x) = spZ regs - 128).
  { unfold spZ at 1. rewrite G, G2, SP2. unfold WV_FRAME. apply unsigned_lit. lia. }
  pose proof RC as (HMk & _).
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG (proj1 (DL s k HinD))) as BR.
  destruct (DLk s k HinD) as [Hink Hnek].
  pose proof CS as (_ & Hk & TXT & BS).
  rewrite (eqv_shape _ _ _ _ HEQ).
  replace (YK11.seg_rom rsegs) with (YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 WV_PUT_STRING) with (Z_to_bv 64 PUT_STRING).
  apply (ps_chain fxk (PSC fxk) (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk bk
    (ms_regs x) s nm Rest Q GG GD FMk ENV RC).
  - rewrite <- EW. exact ROOMS.
  - rewrite <- EW. exact NEED.
  - rewrite SPx. lia.
  - rewrite SPx. lia.
  - rewrite SPx. Z.div_mod_to_equations. lia.
  - rewrite G, G4. symmetry. apply getr_reg. reflexivity.
  - rewrite G, G1. exact (ret_ok_lit RA RA0 RA2).
  - rewrite G. exact G10.
  - rewrite G. exact G11.
  - intros i Hi. rewrite SEGS.
    apply (proj2 (zbytes_core memk s (nm ++ [0]) ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia)) BS).
    exact Hi.
  - exact (bytes_ok_lt nm TXT).
  - exact (no_zero_lt nm TXT).
  - right. exists s, k. split; [exact Hink|]. split; [exact Hnek|]. lia.
  - intros fx' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 FR' FM' RP R1 R1'.
    rewrite G, G1. apply (K' fx' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP).
    split; [intros q Hq; rewrite (FR' q Hq); exact (FRk q Hq)|]. split; [exact FM'|]. split; [exact R1|].
    split; [exact C16|].
    exists junk. rewrite SPx in R1'. eapply frame_keep; [exact HMk | exact R1' | lia | exact C16 | exact FRM].
Qed.

Hypothesis IHC : forall u, (PjTree.depth u < PjTree.depth t)%nat -> wv_P u.

Lemma st_wv : forall {c16} (fxk : FPState) P Lk Ak memk mdk bufk Lamk peakk bk R x RA u vi Du Rest Q,
  (PjTree.depth u < PjTree.depth t)%nat ->
  FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk -> WP = P ++ wvpieces u PB (d + 1) ++ Rest ->
  ms_eqv (MS R (@fp_regs fxk) (Z_to_bv 64 WRITE_VALUE) (@fp_csr fxk) None memk (PropExec.seg_rom rsegs)) x ->
  getr R 1 = Z_to_bv 64 RA -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
  getr R 2 = Z_to_bv 64 (bv_unsigned (reg_get regs 2) - WV_FRAME) -> getr R 4 = reg_get regs 4 ->
  getr R 10 = Z_to_bv 64 o -> getr R 11 = Z_to_bv 64 vi -> getr R 12 = Z_to_bv 64 pretty ->
  getr R 13 = Z_to_bv 64 (d + 1) ->
  pj_node rsegs memk (wv_lblk Lamk) vi u Du ->
  (exists x0 y0, In (x0, y0) D /\ x0 <= vi /\ vi + 56 <= x0 + y0) ->
  (forall a k, In (a, k) Du -> In (a, k) D) ->
  (forall (fx' : FPState) regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, regs_preserved (ms_regs x) regs1 ->
     FI fx' c16 (P ++ wvpieces u PB (d + 1)) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fx' regs1 (Z_to_bv 64 RA) mem1 (seg_rom (ms_segs B))) md1) Q) ->
  SR (ms_segs B) (mkCfg x mdk) Q.
Proof.
  intros c16 fxk P Lk Ak memk mdk bufk Lamk peakk bk R x RA u vi Du Rest Q Hdu FIk EW HEQ
    G1 RA0 RA2 G2 G4 G10 G11 G12 G13 NDu (x0 & y0 & Hin0 & Hx0 & Hy0) DU K'.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FIk) as (_ & _ & _ & _ & _ & DLk & _).
  destruct FIk as (FRk & FMk & RC & C16 & junk & FRM). ents.
  assert (G : forall k, getr (ms_regs x) k = getr R k) by (intros k; exact (eqv_getr _ _ _ _ _ _ _ _ k HEQ)).
  assert (SPx : spZ (ms_regs x) = spZ regs - 128).
  { unfold spZ at 1. rewrite G, G2, SP2. unfold WV_FRAME. apply unsigned_lit. lia. }
  pose proof RC as (HMk & _).
  pose proof (wvk_sub t u Hdu) as KS. pose proof (Zle_0_nat (PjTree.depth u)) as DU0.
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG (proj1 (DL x0 y0 Hin0))) as BR0.
  rewrite (eqv_shape _ _ _ _ HEQ).
  replace (YK11.seg_rom rsegs) with (YK11.seg_rom (ms_segs B)) by (rewrite SEGS; reflexivity).
  change (Z_to_bv 64 WRITE_VALUE) with (Z_to_bv 64 WRITE_VALUE_PC).
  apply (wv_chain fxk u (IHC u Hdu) (WV_K t) regs L A mem md o st buf Lam peak b P Lk Ak memk mdk bufk Lamk peakk
    bk (ms_regs x) vi pretty (d + 1) Du Rest Q GG GD FMk ENV RC).
  - rewrite <- EW. exact ROOMS.
  - rewrite <- EW. exact NEED.
  - rewrite SPx. lia.
  - rewrite SPx. lia.
  - rewrite SPx. Z.div_mod_to_equations. lia.
  - rewrite G, G4. symmetry. apply getr_reg. reflexivity.
  - rewrite G, G1. exact (ret_ok_lit RA RA0 RA2).
  - rewrite G. exact G10.
  - rewrite G. exact G11.
  - rewrite G. exact G12.
  - rewrite G. exact G13.
  - exact HP.
  - lia.
  - lia.
  - exact NDu.
  - unfold wv_where. right. exists x0, y0. destruct (DLk x0 y0 Hin0) as [H1 H2].
    split; [exact H1|]. split; [exact H2|]. lia.
  - intros a k H. exact (DLk a k (DU a k H)).
  - intros z Hz Hf. apply (OF z Hz). destruct Hf as [Hf | ([a k] & Hbb & Hhd)].
    + right. exists (x0, y0). split; [exact Hin0 | unfold pj_holds; cbn [fst snd]; lia].
    + right. exists (a, k). split; [exact (DU a k Hbb) | exact Hhd].
  - intros fx' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 FR' FM' RP R1 R1'.
    rewrite G, G1. apply (K' fx' regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP).
    split; [intros q Hq; rewrite (FR' q Hq); exact (FRk q Hq)|]. split; [exact FM'|]. split; [exact R1|].
    split; [exact C16|].
    exists junk. rewrite SPx in R1'. eapply frame_keep; [exact HMk | exact R1' | lia | exact C16 | exact FRM].
Qed.

Lemma exit_put : forall {c16} (fxk : FPState) P Lk Ak memk mdk bufk Lamk peakk bk regs1 pc s bs,
  FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk -> WP = P ++ [bs] ->
  img_ok s bs = true ->
  existsb (fun sg => (bv_unsigned (fst sg) <=? s) && (s <? bv_unsigned (fst sg) + bv_unsigned (snd sg)))
    (segments_reserved rsegs) = true ->
  bytes_ok bs -> 0 <= s -> s + Z.of_nat (length bs) <= IMG_TOP ->
  Exec.evt rsegs (fun y => wv_exitr (Z_to_bv 64 WV_PUT) (reg_get regs 1) (reg_get regs 2) (reg_get regs 3)
      (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
      (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
      (reg_get regs 27) (@fp_regs fxk) (@fp_csr fxk) (spZ regs - WV_K t) memk
      (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 s /\ x2 = Z_to_bv 64 (Z.of_nat (length bs))) y /\
      ro_agree rsegs (ms_mem y))
    (MS (mkR_of regs1) (@fp_regs fxk) (Z_to_bv 64 pc) (@fp_csr fxk) None memk (PropExec.seg_rom rsegs)) ->
  SR (ms_segs B) (mkCfg (@mkst fxk regs1 (Z_to_bv 64 pc) memk (seg_rom (ms_segs B))) mdk) GOALQ.
Proof.
  intros c16 fxk P Lk Ak memk mdk bufk Lamk peakk bk regs1 pc s bs FIk EW IMG SEG BO S0 SN EV.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FIk) as (HMk & Hhk & Hlk & _ & _ & _ & ROk).
  destruct FIk as (FRk & FMk & RC & C16 & junk & FRM). ents.
  rewrite SEGS. eapply (@kA_lift fxk); [exact Hhk | exact Hlk | exact EV |].
  intros x y [HQ _] HEQ HRM.
  destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Ey & (E0 & E1 & E2)
    & MU & WM & ST'). subst y.
  rewrite SP2 in MU. unfold WV_FRAME in MU.
  assert (XM : ms_mem x = m') by (destruct HEQ as (_ & _ & _ & _ & _ & _ & HMx & _); cbn in HMx; congruence).
  rewrite XM in HRM. rewrite <- SEGS. rewrite EW.
  assert (RO' : ro_agree rsegs m') by (apply (ro_munch_hi (spZ regs - 128) (spZ regs) memk m' ROk MU); unfold IMG_TOP; lia).
  eapply (tail_put fx fxk t regs L A mem md o buf st Lam peak b v D P Lk Ak memk mdk bufk Lamk peakk bk x _ m' s bs
    (PUTC fxk) GG GD ENV LG ND WH DL OF FRk FMk HRA RC).
  - rewrite <- EW. exact ROOMS.
  - rewrite <- EW. exact NEED.
  - exact HEQ.
  - callee_cases.
  - reflexivity.
  - rewrite <- E0. reflexivity.
  - rewrite <- E1. reflexivity.
  - rewrite <- E2. reflexivity.
  - exact MU.
  - exact WM.
  - exact HRM.
  - exact (img_zbytes B SEGS m' s bs RO' IMG).
  - exact BO.
  - lia.
  - lia.
  - exact (img_where B SEGS (ms_regs x) Lamk s _ bufk bs SEG IMG eq_refl).
  - left. lia.
Qed.

Lemma d1_bound : (1 <= PjTree.depth t)%nat -> d + 1 < 2 ^ 31.
Proof. intros H1. ents. lia. Qed.

Lemma fi_node : forall {c16} fxk P Lk Ak memk mdk bufk Lamk peakk bk, FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk ->
  exists str kids keys n pa pb, wv_node memk v (tag t) str kids keys n pa pb.
Proof.
  intros c16 fxk P Lk Ak memk mdk bufk Lamk peakk bk FIk.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FIk) as (_ & _ & _ & _ & NDk & _).
  destruct (node_hdr _ _ _ _ _ _ NDk) as (num & str & kids & keys & n & cap & HH).
  destruct (pj_hdr_wv_node _ _ _ _ _ _ _ _ _ HH) as (pa & pb & WN).
  exists str, kids, keys, n, pa, pb. exact WN.
Qed.

Lemma arr_at : forall {c16} items, t = JArr items ->
  forall fxk P Lk Ak memk mdk bufk Lamk peakk bk, FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk ->
  exists str kids keys n cap pa pb Di, wv_node memk v 5 str kids keys n pa pb /\ n = Z.of_nat (length items) /\
    n <= cap /\ (forall q, In q Di -> In q D) /\ pj_items (pj_node rsegs memk (wv_lblk Lamk)) kids items Di /\
    (0 < cap -> In (kids, 56 * cap) D /\ 4112 <= kids /\ kids + 56 * cap < 2 ^ 47).
Proof.
  intros c16 items Ht fxk P Lk Ak memk mdk bufk Lamk peakk bk FIk.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FIk) as (_ & _ & _ & _ & NDk & _). ents.
  rewrite Ht in NDk. cbn [pj_node] in NDk.
  destruct NDk as (_ & _ & num & str & kids & keys & n & cap & HH & _ & _ & En & Hc & _ & Di & ED & Hi).
  destruct (pj_hdr_wv_node _ _ _ _ _ _ _ _ _ HH) as (pa & pb & WN). cbn [tag] in WN.
  exists str, kids, keys, n, cap, pa, pb, Di.
  split; [exact WN|]. split; [exact En|]. split; [exact Hc|].
  split; [intros q Hq; rewrite ED; apply in_or_app; right; exact Hq|].
  split; [exact Hi|].
  intros Hc0. rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
  assert (H1 : In (kids, 56 * cap) D) by (rewrite ED; left; reflexivity).
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG (proj1 (DL _ _ H1))) as BR1.
  split; [exact H1|]. lia.
Qed.

Lemma obj_at : forall {c16} members, t = JObj members ->
  forall fxk P Lk Ak memk mdk bufk Lamk peakk bk, FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk ->
  exists str kids keys n cap pa pb Di, wv_node memk v 6 str kids keys n pa pb /\ n = Z.of_nat (length members) /\
    n <= cap /\ (forall q, In q Di -> In q D) /\
    pj_mems rsegs memk (wv_lblk Lamk) (pj_node rsegs memk (wv_lblk Lamk)) kids keys members Di /\
    (0 < cap -> In (kids, 56 * cap) D /\ 4112 <= kids /\ kids + 56 * cap < 2 ^ 47 /\ 4112 <= keys /\ keys mod 16 = 0).
Proof.
  intros c16 members Ht fxk P Lk Ak memk mdk bufk Lamk peakk bk FIk.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FIk) as (_ & _ & _ & _ & NDk & _). ents.
  rewrite Ht in NDk. cbn [pj_node] in NDk.
  destruct NDk as (_ & _ & num & str & kids & keys & n & cap & HH & _ & En & Hc & _ & Di & ED & Hi).
  destruct (pj_hdr_wv_node _ _ _ _ _ _ _ _ _ HH) as (pa & pb & WN). cbn [tag] in WN.
  exists str, kids, keys, n, cap, pa, pb, Di.
  split; [exact WN|]. split; [exact En|]. split; [exact Hc|].
  split; [intros q Hq; rewrite ED; apply in_or_app; right; exact Hq|].
  split; [exact Hi|].
  intros Hc0. rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
  assert (H1 : In (kids, 56 * cap) D) by (rewrite ED; left; reflexivity).
  assert (H2 : In (keys, 8 * cap) D) by (rewrite ED; right; left; reflexivity).
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG (proj1 (DL _ _ H1))) as BR1.
  pose proof (ledger_block_range B API _ _ _ _ _ _ _ _ _ _ HM LG (proj1 (DL _ _ H2))) as BR2.
  pose proof (ledger_block_aligned B API _ _ _ _ _ _ _ _ _ _ HM LG (proj1 (DL _ _ H2))) as AL2.
  split; [exact H1|]. lia.
Qed.

Definition LH (fxk : FPState) (i : Z) (memk : word -> option byte) (x : machine_state) : Prop :=
  exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word,
    ms_eqv (wv_ls WV_INDENT (Z_to_bv 64 WV_R_INDENT) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2
      (Z_to_bv 64 o) (Z_to_bv 64 pretty) (Z_to_bv 64 (d + 1)) a3 a4 a5 a6 a7 t3 t4 t5 t6 (@fp_regs fxk) (@fp_csr fxk)
      o v pretty d i memk) x.

Definition OSR : bvmap 5 word :=
  mkR (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned (reg_get regs 2) - WV_FRAME)) (reg_get regs 3) (reg_get regs 4)
    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 o) (Z_to_bv 64 v)
    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
    (Z_to_bv 64 0) (reg_get regs 18) (Z_to_bv 64 pretty) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
    (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
    (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

Definition op_cs (rg : bvmap 5 word) : Prop :=
  forall q, callee_saved q -> getr rg (Z_to_bv 5 q) = getr OSR (Z_to_bv 5 q).

Lemma op_cs_eqv : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pc fc m ro x rg,
  ms_eqv (MS (mkR ra (Z_to_bv 64 (bv_unsigned (reg_get regs 2) - WV_FRAME)) (reg_get regs 3) (reg_get regs 4)
    t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 v) a0 a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (Z_to_bv 64 pretty)
    (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
    (reg_get regs 26) (reg_get regs 27) t3 t4 t5 t6) F pc fc None m ro) x ->
  regs_preserved (ms_regs x) rg -> op_cs rg.
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F pc fc m ro x rg HEQ RP.
  intros q Hq. rewrite (RP q Hq), (eqv_getr _ _ _ _ _ _ _ _ _ HEQ). revert q Hq. callee_cases.
Qed.

Lemma op_resume : forall rg F fc pc m, op_cs rg ->
  MS (mkR_of rg) F (Z_to_bv 64 pc) fc None m (PropExec.seg_rom rsegs) =
  MS (mkR (reg_get rg 1) (Z_to_bv 64 (bv_unsigned (reg_get regs 2) - WV_FRAME)) (reg_get regs 3) (reg_get regs 4)
    (reg_get rg 5) (reg_get rg 6) (reg_get rg 7) (Z_to_bv 64 o) (Z_to_bv 64 v) (reg_get rg 10) (reg_get rg 11)
    (reg_get rg 12) (reg_get rg 13) (reg_get rg 14) (reg_get rg 15) (reg_get rg 16) (reg_get rg 17)
    (reg_get regs 18) (Z_to_bv 64 pretty) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get rg 28) (reg_get rg 29)
    (reg_get rg 30) (reg_get rg 31)) F (Z_to_bv 64 pc) fc None m (PropExec.seg_rom rsegs).
Proof.
  intros rg F fc pc m H. f_equal. unfold mkR_of. f_equal;
    (etransitivity;
     [ apply (agree_get rg OSR _ H); unfold callee_saved;
       match goal with |- context [bv_unsigned ?k] => let w := eval vm_compute in (bv_unsigned k) in
         change (bv_unsigned k) with w end; lia
     | reflexivity ]).
Qed.

Lemma head_ind : forall {c16} (fxk : FPState) P Lk Ak memk mdk bufk Lamk peakk bk x i Rest,
  FI fxk c16 P Lk Ak memk mdk bufk Lamk peakk bk -> LH fxk i memk x -> WP = P ++ wind PB (d + 1) ++ Rest ->
  d + 1 < 2 ^ 31 ->
  (forall regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, ls_cs regs1 i ->
     FI fxk c16 (P ++ wind PB (d + 1)) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fxk regs1 (Z_to_bv 64 WV_R_INDENT) mem1 (seg_rom (ms_segs B))) md1) GOALQ) ->
  SR (ms_segs B) (mkCfg x mdk) GOALQ.
Proof.
  intros c16 fxk P Lk Ak memk mdk bufk Lamk peakk bk x i Rest FIk
    (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & HEQ) EW HD1 K. ents.
  pose proof HEQ as HEQ'. unfold wv_ls in HEQ'.
  eapply (st_ind fxk P Lk Ak memk mdk bufk Lamk peakk bk _ x WV_R_INDENT (d + 1) Rest GOALQ FIk EW HEQ');
    [reflexivity | unfold WV_R_INDENT; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | lia |].
  intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP FI1.
  apply (K regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1); [eapply ls_cs_eqv; [exact HEQ | exact RP] | exact FI1].
Qed.

Lemma item_ret : forall {c16} (fxk : FPState) Pq Lk Ak memk mdk bufk Lamk peakk bk regsk i ty str kids keys n pa pb,
  FI fxk c16 Pq Lk Ak memk mdk bufk Lamk peakk bk -> ls_cs regsk i -> tag t = ty -> (ty = 5 \/ ty = 6) ->
  wv_node memk v ty str kids keys n pa pb -> 0 <= i -> i + 1 <= n -> 56 * n < 2 ^ 63 ->
  (i + 1 = n -> WP = Pq ++ wind PB d ++ [wv_cb ty]) ->
  (i + 1 < n -> (exists Rest, WP = Pq ++ [[44]] ++ Rest) /\
     forall Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x',
       FI fxk c16 (Pq ++ [[44]]) Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' ->
       LH fxk (i + 1) memk' x' -> SR (ms_segs B) (mkCfg x' mdk') GOALQ) ->
  SR (ms_segs B) (mkCfg (@mkst fxk regsk (Z_to_bv 64 WV_R_ITEM) memk (seg_rom (ms_segs B))) mdk) GOALQ.
Proof.
  intros c16 fxk Pq Lk Ak memk mdk bufk Lamk peakk bk regsk i ty str kids keys n pa pb FIk LSk Ht HT WN Hi Hin HN
    ELAST KNEXT.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FIk) as (_ & Hhk & Hlk & _). ents.
  pose proof FIk as (_ & _ & _ & _ & junkk & FRMk).
  destruct (Z.lt_ge_cases (i + 1) n) as [Hlt | Hge].
  - destruct (KNEXT Hlt) as [[Rest EW] KN].
    rewrite SEGS. eapply (@kA_lift fxk); [exact Hhk | exact Hlk | |].
    { rewrite (ls_resume regsk i _ _ _ _ LSk). eapply wv_after_item_next; [exact WN | lia | lia | lia]. }
    intros x y (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & Ey) HEQ _. subst y. rewrite <- SEGS.
    pose proof HEQ as HEQ'. unfold wv_ls in HEQ'.
    eapply (st_put fxk Pq Lk Ak memk mdk bufk Lamk peakk bk _ x WV_R_COMMA WV_S_COMMA [44] Rest GOALQ FIk EW HEQ');
      [reflexivity | unfold WV_R_COMMA; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | unfold bytes_ok; repeat constructor; lia
      | unfold WV_S_COMMA; lia | unfold WV_S_COMMA, IMG_TOP; cbn [length Z.of_nat]; lia |].
    intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP FI1.
    assert (LS1 : ls_cs regs1 (i + 1)) by (eapply ls_cs_eqv; [exact HEQ | exact RP]).
    destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FI1) as (_ & Hh1 & Hl1 & _).
    rewrite SEGS. eapply (@kA_lift fxk); [exact Hh1 | exact Hl1 | |].
    { rewrite (ls_resume regs1 (i + 1) _ _ _ _ LS1). apply wv_after_comma. }
    intros x2 y2 (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & Ey2) HEQ2 _. subst y2.
    rewrite <- SEGS.
    apply (KN L1 A1 mem1 md1 buf1 Lam1 peak1 b1 x2 FI1).
    exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11. exact HEQ2.
  - assert (E1 : i + 1 = n) by lia. pose proof (ELAST E1) as EW.
    rewrite SEGS. eapply (@kA_lift fxk); [exact Hhk | exact Hlk | |].
    { rewrite (ls_resume regsk i _ _ _ _ LSk). eapply wv_after_item_last; [exact WN | lia | exact E1 | lia | exact FRMk]. }
    intros x y (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & Ey) HEQ _. subst y. rewrite <- SEGS.
    pose proof HEQ as HEQ'. unfold wv_ls in HEQ'.
    eapply (st_ind fxk Pq Lk Ak memk mdk bufk Lamk peakk bk _ x WV_R_CLOSE d [wv_cb ty] GOALQ FIk EW HEQ');
      [reflexivity | unfold WV_R_CLOSE; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | lia |].
    intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP FI1.
    assert (LS1 : ls_cs regs1 (i + 1)) by (eapply ls_cs_eqv; [exact HEQ | exact RP]).
    destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FI1) as (_ & _ & _ & STK1 & _ & _ & ROk1).
    destruct (fi_node _ _ _ _ _ _ _ _ _ _ FI1) as (str1 & kids1 & keys1 & n1 & pa1 & pb1 & WN1). rewrite Ht in WN1.
    pose proof FI1 as (_ & _ & _ & C161 & junk1 & FRM1).
    destruct (oc_facts ty HT) as [_ (IMG & SEG & BO & S0 & SN)].
    apply (exit_put fxk (Pq ++ wind PB d) L1 A1 mem1 md1 buf1 Lam1 peak1 b1 regs1 WV_R_CLOSE (wv_close ty) (wv_cb ty)
      FI1); [rewrite <- app_assoc; exact EW | exact IMG | exact SEG | exact BO | exact S0 | exact SN |].
    rewrite (ls_resume regs1 (i + 1) _ _ _ _ LS1). unfold wv_ls.
    eapply wv_close_tail_ro; [exact ROk1 | exact WN1 | exact NRO | lia | exact FRM1 | exact C161 | exact STK1
      | rewrite SP2; unfold WV_FRAME; lia | exact LO].
Qed.

Lemma node_open : forall ty Rest,
  (forall j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1, op_cs regs1 ->
     FI fx (CB 8 j16) [wv_ob ty] L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
     SR (ms_segs B) (mkCfg (@mkst fx regs1 (Z_to_bv 64 WV_R_OPEN) mem1 (seg_rom (ms_segs B))) md1) GOALQ) ->
  tag t = ty -> (ty = 5 \/ ty = 6) -> WP = [] ++ [wv_ob ty] ++ Rest ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md) GOALQ.
Proof.
  intros ty Rest K Ht HT EW.
  destruct (hdr_node ty Ht) as (str & kids & keys & n & pa & pb & WN). ents.
  destruct (oc_facts ty HT) as [(IMG & SEG & BO & S0 & SN) _].
  rewrite SEGS. eapply kA_lift; [exact Hh | exact Hl | |].
  { unfold mkR_of. rewrite Q10, Q11, Q12, Q13.
    eapply wv_open_call_ro; [exact RO | exact WN | exact NRO | exact HT | exact V0 | exact V8 | rewrite SP2; exact STK
      | rewrite SP2; unfold WV_FRAME; lia | exact LO | rewrite SP2; exact DV]. }
  intros x y [HQ ROy] HEQ HRM.
  destruct HQ as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & m' & junk & j16 & Ey & (MU & WM & ST' & FRM)
    & WN').
  subst y.
  rewrite SP2 in MU. unfold WV_FRAME in MU.
  assert (XM : ms_mem x = m') by (destruct HEQ as (_ & _ & _ & _ & _ & _ & HMx & _); cbn in HMx; congruence).
  rewrite XM in HRM. rewrite <- SEGS.
  assert (FI0 : FI fx (CB 8 j16) [] L A m' md buf Lam peak b).
  { split; [intros q _; reflexivity|]. split; [exact FM|]. split.
    - exact (munch_step (WV_K t) regs L A mem md o st buf Lam peak b [] L A mem md buf Lam peak b m' ENV ltac:(lia)
        R0 MU WM HRM).
    - split; [left; eexists; reflexivity|]. exists junk. exact FRM. }
  eapply (st_put fx [] L A m' md buf Lam peak b _ x WV_R_OPEN (wv_open ty) (wv_ob ty) Rest GOALQ FI0 EW HEQ);
    [reflexivity | unfold WV_R_OPEN; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | exact IMG | exact SEG | exact BO | exact S0 | exact SN |].
  intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 RP FI1.
  apply (K j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1); [eapply op_cs_eqv; [exact HEQ | exact RP] | exact FI1].
Qed.

Lemma open_empty : forall (fxk : FPState) j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ty str kids keys pa pb,
  op_cs regs1 -> FI fxk (CB 8 j16) [wv_ob ty] L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  wv_node mem1 v ty str kids keys 0 pa pb -> (ty = 5 \/ ty = 6) -> WP = [wv_ob ty] ++ [wv_cb ty] ->
  SR (ms_segs B) (mkCfg (@mkst fxk regs1 (Z_to_bv 64 WV_R_OPEN) mem1 (seg_rom (ms_segs B))) md1) GOALQ.
Proof.
  intros fxk j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ty str kids keys pa pb OC FI1 WN HT EW.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FI1) as (_ & _ & _ & STK1 & _ & _ & ROk1).
  pose proof FI1 as (_ & _ & _ & _ & junk & FRM). ents.
  destruct (oc_facts ty HT) as [_ (IMG & SEG & BO & S0 & SN)].
  apply (exit_put fxk [wv_ob ty] L1 A1 mem1 md1 buf1 Lam1 peak1 b1 regs1 WV_R_OPEN (wv_close ty) (wv_cb ty) FI1 EW
    IMG SEG BO S0 SN).
  rewrite (op_resume regs1 _ _ _ _ OC).
  eapply wv_after_open_empty_ro; [exact ROk1 | exact WN | exact NRO | lia | exact HP | exact FRM | exact STK1
    | rewrite SP2; unfold WV_FRAME; lia | exact LO | rewrite SP2; exact DV].
Qed.

Lemma open_first : forall (fxk : FPState) j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ty str kids keys n pa pb,
  op_cs regs1 -> FI fxk (CB 8 j16) [wv_ob ty] L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ->
  wv_node mem1 v ty str kids keys n pa pb -> 0 < n < 2 ^ 64 -> d + 1 < 2 ^ 31 ->
  (forall mem2 x, FI fxk SEPC [wv_ob ty] L1 A1 mem2 md1 buf1 Lam1 peak1 b1 -> LH fxk 0 mem2 x ->
     SR (ms_segs B) (mkCfg x md1) GOALQ) ->
  SR (ms_segs B) (mkCfg (@mkst fxk regs1 (Z_to_bv 64 WV_R_OPEN) mem1 (seg_rom (ms_segs B))) md1) GOALQ.
Proof.
  intros fxk j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 ty str kids keys n pa pb OC FI1 WN HN HD1 K.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FI1) as (_ & Hh1 & Hl1 & STK1 & _ & _ & ROk1).
  pose proof FI1 as (FR1 & FM1 & RC1 & _ & junk & FRM1). ents.
  rewrite SEGS. eapply (@kA_lift fxk); [exact Hh1 | exact Hl1 | |].
  { rewrite (op_resume regs1 _ _ _ _ OC).
    eapply wv_after_open_first_ro with (depth := d);
      [exact ROk1 | exact WN | exact NRO | lia | exact HP | lia | lia | exact FRM1 | exact STK1
      | rewrite SP2; unfold WV_FRAME; lia | exact LO | rewrite SP2; exact DV]. }
  intros x y [(w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & m2 & Ey & (MU & WM & ST2 & FRM2) & WN2) _]
    HEQ HRM.
  subst y. rewrite <- SEGS.
  assert (XM : ms_mem x = m2)
    by (destruct HEQ as (_ & _ & _ & _ & _ & _ & HMx & _); unfold wv_ls in HMx; cbn in HMx; congruence).
  rewrite XM in HRM. rewrite SP2 in MU. unfold WV_FRAME in MU.
  apply (K m2 x).
  - split; [exact FR1|]. split; [exact FM1|]. split.
    + exact (munch_step (WV_K t) regs L A mem md o st buf Lam peak b [wv_ob ty] L1 A1 mem1 md1 buf1 Lam1 peak1 b1 m2
        ENV ltac:(lia) RC1 MU WM HRM).
    + split; [right; eexists; reflexivity|]. exists junk. exact FRM2.
  - exists w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11. exact HEQ.
Qed.

Lemma arr_iter : forall items pre u r, t = JArr items -> items = pre ++ u :: r ->
  forall (fxk : FPState) Lk Ak memk mdk bufk Lamk peakk bk x,
  FI fxk SEPC (aq PB d pre ++ wcomma (length pre)) Lk Ak memk mdk bufk Lamk peakk bk ->
  LH fxk (Z.of_nat (length pre)) memk x ->
  (r <> [] -> forall (fxk' : FPState) Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x',
     FI fxk' SEPC (aq PB d (pre ++ [u]) ++ [[44]]) Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' ->
     LH fxk' (Z.of_nat (length pre) + 1) memk' x' -> SR (ms_segs B) (mkCfg x' mdk') GOALQ) ->
  SR (ms_segs B) (mkCfg x mdk) GOALQ.
Proof.
  intros items pre u r Ht Eit fxk Lk Ak memk mdk bufk Lamk peakk bk x FIk LHx KN.
  assert (EW : WP = (aq PB d pre ++ wcomma (length pre)) ++ wind PB (d + 1) ++ wvpieces u PB (d + 1) ++
                    arr_go PB d (S (length pre)) r ++ wind PB d ++ [[93]])
    by (rewrite Ht; exact (arr_wp items pre u r PB d Eit)).
  assert (Hdu : (PjTree.depth u < PjTree.depth t)%nat)
    by (rewrite Ht; apply depth_item; rewrite Eit; apply in_or_app; right; left; reflexivity).
  assert (D1 : (1 <= PjTree.depth t)%nat) by (rewrite Ht; cbn [PjTree.depth]; lia).
  assert (Hlen : Z.of_nat (length items) = Z.of_nat (length pre) + 1 + Z.of_nat (length r))
    by (rewrite Eit, length_app; cbn [length]; lia).
  assert (Hj : (length pre < length items)%nat) by (rewrite Eit, length_app; cbn [length]; lia).
  apply (head_ind fxk _ Lk Ak memk mdk bufk Lamk peakk bk x _ _ FIk LHx EW (d1_bound D1)).
  intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 LS1 FI1.
  destruct (arr_at items Ht _ _ _ _ _ _ _ _ _ _ FI1)
    as (str & kids & keys & n & cap & pa & pb & Di & WN & En & Hc & DiD & Hi & HK).
  destruct (HK ltac:(lia)) as (Hin & Kk0 & Kk1).
  destruct (pj_items_nth _ items kids Di (length pre) Hi Hj) as (Du & DuD & NDu).
  rewrite Eit, nth_mid in NDu.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FI1) as (_ & Hh1 & Hl1 & _).
  rewrite SEGS. eapply (@kA_lift fxk); [exact Hh1 | exact Hl1 | |].
  { rewrite (ls_resume regs1 _ _ _ _ _ LS1).
    eapply wv_after_indent_arr; [exact WN | lia | lia | lia | lia | lia | lia]. }
  intros x2 y2 (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & Ey) HEQ _. subst y2. rewrite <- SEGS.
  pose proof HEQ as HEQ'. unfold wv_ls in HEQ'.
  assert (EWv : WP = ((aq PB d pre ++ wcomma (length pre)) ++ wind PB (d + 1)) ++ wvpieces u PB (d + 1) ++
                     (arr_go PB d (S (length pre)) r ++ wind PB d ++ [[93]]))
    by (rewrite EW; rewrite <- !app_assoc; reflexivity).
  eapply (st_wv fxk _ L1 A1 mem1 md1 buf1 Lam1 peak1 b1 _ x2 WV_R_ITEM u (kids + 56 * Z.of_nat (length pre)) Du _
    GOALQ Hdu FI1 EWv HEQ');
    [reflexivity | unfold WV_R_ITEM; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | exact NDu | exists kids, (56 * cap); split; [exact Hin | lia]
    | intros a k Hak; exact (DiD _ (DuD _ Hak)) |].
  intros fx' regs2 L2 A2 mem2 md2 buf2 Lam2 peak2 b2 RP2 FI2.
  assert (LS2 : ls_cs regs2 (Z.of_nat (length pre))) by (eapply ls_cs_eqv; [exact HEQ | exact RP2]).
  rewrite arr_after in FI2.
  destruct (arr_at items Ht _ _ _ _ _ _ _ _ _ _ FI2)
    as (str2 & kids2 & keys2 & n2 & cap2 & pa2 & pb2 & Di2 & WN2 & En2 & Hc2 & _ & _ & HK2).
  destruct (HK2 ltac:(lia)) as (_ & Kk20 & Kk21).
  apply (item_ret fx' (aq PB d (pre ++ [u])) L2 A2 mem2 md2 buf2 Lam2 peak2 b2 regs2 (Z.of_nat (length pre)) 5
    str2 kids2 keys2 n2 pa2 pb2 FI2 LS2 ltac:(rewrite Ht; reflexivity) (or_introl eq_refl) WN2); [lia | lia | lia | |].
  - intros E1. destruct r as [|u' r']; [|cbn [length] in Hlen; lia].
    rewrite EW, <- arr_after. rewrite <- !app_assoc. reflexivity.
  - intros Hlt. destruct r as [|u' r']; [cbn [length] in Hlen; lia|]. split.
    + exists (wind PB (d + 1) ++ wvpieces u' PB (d + 1) ++ arr_go PB d (S (length (pre ++ [u]))) r' ++
        wind PB d ++ [[93]]).
      rewrite Ht, (arr_wp items (pre ++ [u]) u' r' PB d ltac:(rewrite Eit, <- app_assoc; reflexivity)), wcomma_S.
      rewrite <- !app_assoc. reflexivity.
    + intros Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x' FI' LH'.
      exact (KN ltac:(discriminate) fx' Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x' FI' LH').
Qed.

Lemma arr_loop : forall items, t = JArr items -> forall r pre u, items = pre ++ u :: r ->
  forall (fxk : FPState) Lk Ak memk mdk bufk Lamk peakk bk x,
  FI fxk SEPC (aq PB d pre ++ wcomma (length pre)) Lk Ak memk mdk bufk Lamk peakk bk ->
  LH fxk (Z.of_nat (length pre)) memk x -> SR (ms_segs B) (mkCfg x mdk) GOALQ.
Proof.
  intros items Ht r. induction r as [|u' r IH];
    intros pre u Eit fxk Lk Ak memk mdk bufk Lamk peakk bk x FIk LHx;
    apply (arr_iter items pre u _ Ht Eit fxk Lk Ak memk mdk bufk Lamk peakk bk x FIk LHx).
  - intros C. exfalso. apply C. reflexivity.
  - intros _ fxk' Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x' FI' LH'.
    apply (IH (pre ++ [u]) u' ltac:(rewrite Eit, <- app_assoc; reflexivity)
      fxk' Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x').
    + rewrite wcomma_S. exact FI'.
    + replace (Z.of_nat (length (pre ++ [u]))) with (Z.of_nat (length pre) + 1)
        by (rewrite length_app; cbn [length]; lia).
      exact LH'.
Qed.

Lemma case_arr : forall items, t = JArr items ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md) GOALQ.
Proof.
  intros items Ht.
  assert (D1 : (1 <= PjTree.depth t)%nat) by (rewrite Ht; cbn [PjTree.depth]; lia).
  apply (node_open 5 (arr_go PB d 0 items ++ (match items with [] => [] | _ :: _ => wind PB d end) ++ [[93]]));
    [| rewrite Ht; reflexivity | left; reflexivity | rewrite Ht; reflexivity].
  intros j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 OC FI1.
  destruct (arr_at items Ht _ _ _ _ _ _ _ _ _ _ FI1)
    as (str & kids & keys & n & cap & pa & pb & Di & WN & En & Hc & _ & _ & HK).
  destruct items as [|u r].
  - cbn [length Z.of_nat] in En. subst n.
    apply (open_empty fx j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 5 str kids keys pa pb OC FI1 WN
      (or_introl eq_refl)).
    rewrite Ht. reflexivity.
  - destruct (HK ltac:(cbn [length] in En; lia)) as (_ & Kk0 & Kk1).
    apply (open_first fx j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 5 str kids keys n pa pb OC FI1 WN
      ltac:(cbn [length] in En; lia) (d1_bound D1)).
    intros mem2 x FI2 LHx.
    exact (arr_loop (u :: r) Ht r [] u eq_refl fx L1 A1 mem2 md1 buf1 Lam1 peak1 b1 x FI2 LHx).
Qed.

Lemma obj_iter : forall members pre nm u r, t = JObj members -> members = pre ++ (nm, u) :: r ->
  forall (fxk : FPState) Lk Ak memk mdk bufk Lamk peakk bk x,
  FI fxk SEPC (oq PB d pre ++ wcomma (length pre)) Lk Ak memk mdk bufk Lamk peakk bk ->
  LH fxk (Z.of_nat (length pre)) memk x ->
  (r <> [] -> forall (fxk' : FPState) Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x',
     FI fxk' SEPC (oq PB d (pre ++ [(nm, u)]) ++ [[44]]) Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' ->
     LH fxk' (Z.of_nat (length pre) + 1) memk' x' -> SR (ms_segs B) (mkCfg x' mdk') GOALQ) ->
  SR (ms_segs B) (mkCfg x mdk) GOALQ.
Proof.
  intros members pre nm u r Ht Eit fxk Lk Ak memk mdk bufk Lamk peakk bk x FIk LHx KN.
  assert (EW : WP = (oq PB d pre ++ wcomma (length pre)) ++ wind PB (d + 1) ++ spieces nm ++ [wsep PB] ++
                    wvpieces u PB (d + 1) ++ obj_go PB d (S (length pre)) r ++ wind PB d ++ [[125]])
    by (rewrite Ht; exact (obj_wp members pre nm u r PB d Eit)).
  assert (Hdu : (PjTree.depth u < PjTree.depth t)%nat)
    by (rewrite Ht; apply (depth_member members nm u); rewrite Eit; apply in_or_app; right; left; reflexivity).
  assert (D1 : (1 <= PjTree.depth t)%nat) by (rewrite Ht; cbn [PjTree.depth]; lia).
  assert (Hlen : Z.of_nat (length members) = Z.of_nat (length pre) + 1 + Z.of_nat (length r))
    by (rewrite Eit, length_app; cbn [length]; lia).
  assert (Hj : (length pre < length members)%nat) by (rewrite Eit, length_app; cbn [length]; lia).
  apply (head_ind fxk _ Lk Ak memk mdk bufk Lamk peakk bk x _ _ FIk LHx EW (d1_bound D1)).
  intros regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 LS1 FI1.
  destruct (obj_at members Ht _ _ _ _ _ _ _ _ _ _ FI1)
    as (str & kids & keys & n & cap & pa & pb & Di & WN & En & Hc & DiD & Hi & HK).
  destruct (HK ltac:(lia)) as (Hin & Kk0 & Kk1 & Ky0 & Ky16).
  assert (K8 : keys mod 8 = 0) by (clear - Ky16; Z.div_mod_to_equations; lia).
  destruct (pj_mems_nth rsegs _ _ _ members kids keys Di (length pre) Hi Hj) as (xk & kk & Dk & Hxk & _ & HU & CS & _).
  rewrite Eit, nth_mid in CS. cbn [fst] in CS.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FI1) as (_ & Hh1 & Hl1 & _).
  rewrite SEGS. eapply (@kA_lift fxk); [exact Hh1 | exact Hl1 | |].
  { rewrite (ls_resume regs1 _ _ _ _ _ LS1).
    eapply wv_after_indent_obj; [exact WN | lia | exact K8 | lia | lia | exact (proj2 HU)]. }
  intros x2 y2 (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & Ey) HEQ _. subst y2.
  rewrite <- SEGS.
  pose proof HEQ as HEQ'. unfold wv_ls in HEQ'.
  assert (EW2 : WP = ((oq PB d pre ++ wcomma (length pre)) ++ wind PB (d + 1)) ++ spieces nm ++
                     ([wsep PB] ++ wvpieces u PB (d + 1) ++ obj_go PB d (S (length pre)) r ++ wind PB d ++ [[125]]))
    by (rewrite EW; rewrite <- !app_assoc; reflexivity).
  eapply (st_ps fxk _ L1 A1 mem1 md1 buf1 Lam1 peak1 b1 _ x2 WV_R_KEY xk kk nm _ GOALQ FI1 EW2 HEQ');
    [reflexivity | unfold WV_R_KEY; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | exact (DiD _ Hxk) | exact CS |].
  intros fx2 regs2 L2 A2 mem2 md2 buf2 Lam2 peak2 b2 RP2 FI2.
  assert (LS2 : ls_cs regs2 (Z.of_nat (length pre))) by (eapply ls_cs_eqv; [exact HEQ | exact RP2]).
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FI2) as (_ & Hh2 & Hl2 & _).
  pose proof FI2 as (_ & _ & _ & _ & junk2 & FRM2).
  rewrite SEGS. eapply (@kA_lift fx2); [exact Hh2 | exact Hl2 | |].
  { rewrite (ls_resume regs2 _ _ _ _ _ LS2). eapply wv_after_key. exact FRM2. }
  intros x3 y3 (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & Ey3) HEQ3 _. subst y3.
  rewrite <- SEGS.
  pose proof HEQ3 as HEQ3'. unfold wv_ls in HEQ3'.
  destruct (sep_facts pretty) as (SL & IMG & SEG & BO & S0 & SN).
  assert (EW3 : WP = (((oq PB d pre ++ wcomma (length pre)) ++ wind PB (d + 1)) ++ spieces nm) ++ [wsep PB] ++
                     (wvpieces u PB (d + 1) ++ obj_go PB d (S (length pre)) r ++ wind PB d ++ [[125]]))
    by (rewrite EW; rewrite <- !app_assoc; reflexivity).
  eapply (st_put fx2 _ L2 A2 mem2 md2 buf2 Lam2 peak2 b2 _ x3 WV_R_SEP (wv_sep pretty) (wsep PB) _ GOALQ FI2 EW3
    HEQ3');
    [reflexivity | unfold WV_R_SEP; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | rewrite <- SL; reflexivity | exact IMG | exact SEG | exact BO | exact S0 | exact SN |].
  intros regs3 L3 A3 mem3 md3 buf3 Lam3 peak3 b3 RP3 FI3.
  assert (LS3 : ls_cs regs3 (Z.of_nat (length pre))) by (eapply ls_cs_eqv; [exact HEQ3 | exact RP3]).
  destruct (obj_at members Ht _ _ _ _ _ _ _ _ _ _ FI3)
    as (str3 & kids3 & keys3 & n3 & cap3 & pa3 & pb3 & Di3 & WN3 & En3 & Hc3 & DiD3 & Hi3 & HK3).
  destruct (HK3 ltac:(lia)) as (Hin3 & Kk30 & Kk31 & _).
  destruct (pj_mems_nth rsegs _ _ _ members kids3 keys3 Di3 (length pre) Hi3 Hj)
    as (xk3 & kk3 & Du & _ & DuD & _ & _ & NDu).
  rewrite Eit, nth_mid in NDu. cbn [snd] in NDu.
  destruct (fi_facts _ _ _ _ _ _ _ _ _ _ FI3) as (_ & Hh3 & Hl3 & _).
  rewrite SEGS. eapply (@kA_lift fx2); [exact Hh3 | exact Hl3 | |].
  { rewrite (ls_resume regs3 _ _ _ _ _ LS3). eapply wv_after_sep; [exact WN3 | lia | lia | lia | lia]. }
  intros x4 y4 (e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & Ey4) HEQ4 _. subst y4.
  rewrite <- SEGS.
  pose proof HEQ4 as HEQ4'. unfold wv_ls in HEQ4'.
  assert (EW4 : WP = ((((oq PB d pre ++ wcomma (length pre)) ++ wind PB (d + 1)) ++ spieces nm) ++ [wsep PB]) ++
                     wvpieces u PB (d + 1) ++ (obj_go PB d (S (length pre)) r ++ wind PB d ++ [[125]]))
    by (rewrite EW; rewrite <- !app_assoc; reflexivity).
  eapply (st_wv fx2 _ L3 A3 mem3 md3 buf3 Lam3 peak3 b3 _ x4 WV_R_ITEM u (kids3 + 56 * Z.of_nat (length pre)) Du _
    GOALQ Hdu FI3 EW4 HEQ4');
    [reflexivity | unfold WV_R_ITEM; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | exact NDu | exists kids3, (56 * cap3); split; [exact Hin3 | lia]
    | intros a k Hak; exact (DiD3 _ (DuD _ Hak)) |].
  intros fx4 regs4 L4 A4 mem4 md4 buf4 Lam4 peak4 b4 RP4 FI4.
  assert (LS4 : ls_cs regs4 (Z.of_nat (length pre))) by (eapply ls_cs_eqv; [exact HEQ4 | exact RP4]).
  rewrite obj_after in FI4.
  destruct (obj_at members Ht _ _ _ _ _ _ _ _ _ _ FI4)
    as (str4 & kids4 & keys4 & n4 & cap4 & pa4 & pb4 & Di4 & WN4 & En4 & Hc4 & _ & _ & HK4).
  destruct (HK4 ltac:(lia)) as (_ & Kk40 & Kk41 & _).
  apply (item_ret fx4 (oq PB d (pre ++ [(nm, u)])) L4 A4 mem4 md4 buf4 Lam4 peak4 b4 regs4 (Z.of_nat (length pre)) 6
    str4 kids4 keys4 n4 pa4 pb4 FI4 LS4 ltac:(rewrite Ht; reflexivity) (or_intror eq_refl) WN4);
    [lia | lia | lia | |].
  - intros E1. destruct r as [|[nm' u'] r']; [|cbn [length] in Hlen; lia].
    rewrite EW, <- obj_after. rewrite <- !app_assoc. reflexivity.
  - intros Hlt. destruct r as [|[nm' u'] r']; [cbn [length] in Hlen; lia|]. split.
    + exists (wind PB (d + 1) ++ spieces nm' ++ [wsep PB] ++ wvpieces u' PB (d + 1) ++
        obj_go PB d (S (length (pre ++ [(nm, u)]))) r' ++ wind PB d ++ [[125]]).
      rewrite Ht, (obj_wp members (pre ++ [(nm, u)]) nm' u' r' PB d ltac:(rewrite Eit, <- app_assoc; reflexivity)),
        wcomma_S.
      rewrite <- !app_assoc. reflexivity.
    + intros Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x' FI' LH'.
      exact (KN ltac:(discriminate) fx4 Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x' FI' LH').
Qed.

Lemma obj_loop : forall members, t = JObj members -> forall r pre nm u, members = pre ++ (nm, u) :: r ->
  forall (fxk : FPState) Lk Ak memk mdk bufk Lamk peakk bk x,
  FI fxk SEPC (oq PB d pre ++ wcomma (length pre)) Lk Ak memk mdk bufk Lamk peakk bk ->
  LH fxk (Z.of_nat (length pre)) memk x -> SR (ms_segs B) (mkCfg x mdk) GOALQ.
Proof.
  intros members Ht r. induction r as [|[nm' u'] r IH];
    intros pre nm u Eit fxk Lk Ak memk mdk bufk Lamk peakk bk x FIk LHx;
    apply (obj_iter members pre nm u _ Ht Eit fxk Lk Ak memk mdk bufk Lamk peakk bk x FIk LHx).
  - intros C. exfalso. apply C. reflexivity.
  - intros _ fxk' Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x' FI' LH'.
    apply (IH (pre ++ [(nm, u)]) nm' u' ltac:(rewrite Eit, <- app_assoc; reflexivity)
      fxk' Lk' Ak' memk' mdk' bufk' Lamk' peakk' bk' x').
    + rewrite wcomma_S. exact FI'.
    + replace (Z.of_nat (length (pre ++ [(nm, u)]))) with (Z.of_nat (length pre) + 1)
        by (rewrite length_app; cbn [length]; lia).
      exact LH'.
Qed.

Lemma case_obj : forall members, t = JObj members ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md) GOALQ.
Proof.
  intros members Ht.
  assert (D1 : (1 <= PjTree.depth t)%nat) by (rewrite Ht; cbn [PjTree.depth]; lia).
  apply (node_open 6 (obj_go PB d 0 members ++ (match members with [] => [] | _ :: _ => wind PB d end) ++ [[125]]));
    [| rewrite Ht; reflexivity | right; reflexivity | rewrite Ht; reflexivity].
  intros j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 OC FI1.
  destruct (obj_at members Ht _ _ _ _ _ _ _ _ _ _ FI1)
    as (str & kids & keys & n & cap & pa & pb & Di & WN & En & Hc & _ & _ & HK).
  destruct members as [|[nm u] r].
  - cbn [length Z.of_nat] in En. subst n.
    apply (open_empty fx j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 6 str kids keys pa pb OC FI1 WN
      (or_intror eq_refl)).
    rewrite Ht. reflexivity.
  - destruct (HK ltac:(cbn [length] in En; lia)) as (_ & Kk0 & Kk1 & _).
    apply (open_first fx j16 regs1 L1 A1 mem1 md1 buf1 Lam1 peak1 b1 6 str kids keys n pa pb OC FI1 WN
      ltac:(cbn [length] in En; lia) (d1_bound D1)).
    intros mem2 x FI2 LHx.
    exact (obj_loop ((nm, u) :: r) Ht r [] nm u eq_refl fx L1 A1 mem2 md1 buf1 Lam1 peak1 b1 x FI2 LHx).
Qed.

End Body.

Lemma wv_all : (forall fx' : FPState, @put_contract fx' rc B API RF) ->
  (forall fx' : FPState, @indent_contract fx' rc B API RF) ->
  (forall fx' : FPState, @put_string_contract fx' rc B API RF) ->
  strlen_contract -> block_slack_present B API -> forall t, wv_P t.
Proof.
  intros PUTC INDC PSC SLC BSP.
  assert (G : forall k t, (PjTree.depth t < k)%nat -> wv_P t).
  { induction k as [|k IH]; intros t Hk; [lia|].
    intros fx L A regs mem md b o v pretty d D buf st Lam peak PRE0.
    assert (IHC : forall u, (PjTree.depth u < PjTree.depth t)%nat -> wv_P u) by (intros u Hu; apply IH; lia).
    destruct t as [| | | txt bits | s | items | members].
    - eapply case_null; solve [eassumption | reflexivity].
    - eapply case_false; solve [eassumption | reflexivity].
    - eapply case_true; solve [eassumption | reflexivity].
    - eapply case_num; solve [eassumption | reflexivity].
    - eapply case_str; solve [eassumption | reflexivity].
    - eapply case_arr; solve [eassumption | reflexivity].
    - eapply case_obj; solve [eassumption | reflexivity]. }
  intros t. apply (G (S (PjTree.depth t)) t). lia.
Qed.

End W.

Section Q.
Context {fx : FPState} {rc : YM05.RunCeil}.

Theorem write_value_holds : forall (B : malloc_syms) (API : AllocAPI B) (RF : ResForm),
  AllocExtra B (aa_MR API) -> ctx_owned B API ->
  (forall fx' : FPState, @put_contract fx' rc B API RF) ->
  (forall fx' : FPState, @indent_contract fx' rc B API RF) ->
  (forall fx' : FPState, @put_string_contract fx' rc B API RF) ->
  strlen_contract -> block_slack_present B API ->
  write_value_contract B API RF.
Proof.
  intros B API RF AX CTX PUTC INDC PSC SLC BSP. unfold write_value_contract.
  intros L A regs mem md b o v pretty d t D buf st Lam peak SG GG GD PRE INIT RO FM R10 R11 R12 R13 HP HD HDD PJ LG
    SPO EO ES ND WH DL OF NEED RS ROOMS.
  apply (wv_all B API RF SG AX CTX PUTC INDC PSC SLC BSP t fx L A regs mem md b o v pretty d D buf st Lam peak).
  apply mk_wv_pre; assumption.
Qed.

End Q.
