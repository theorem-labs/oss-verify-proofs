From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO0x YO10 YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import pthread_mutex_lock_c pthread_mutex_unlock_c
  send_line_c gesture_end_c relay_event_c send_line_b_c gesture_end_b_c gestures_end_b_c
  relay_add_b_c relay_finish_b_c KindB relay_finish_seg relay_finish_aux relay_finish_b1.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- A trace read through its resolved addresses (lane C helpers). ---- *)

(* What the run and the room of a trace read: each request with its resolved address and the address it returns. *)
Fixpoint p3c_res (Q : list sptr) (j : nat) (tr : trF) : list (rev sptr * sptr) :=
  match tr with
  | [] => []
  | RMalloc n :: r => (RMalloc n, SP 0 0) :: p3c_res Q (S j) r
  | RFree n a :: r => (RFree n (Known (resolveF Q a)), SP 0 0) :: p3c_res Q j r
  | RRealloc k n a :: r => (RRealloc k n (Known (resolveF Q a)), nth j Q (SP 0 0)) :: p3c_res Q (S j) r
  end.

Fixpoint p3c_rrun (F : ResFormT) (b : rt_R F) (rs : list (rev sptr * sptr)) : rt_R F :=
  match rs with
  | [] => b
  | (RMalloc n, _) :: r => p3c_rrun F (rt_malloc F b n) r
  | (RFree n a, _) :: r => p3c_rrun F (rt_free F b n (resolveF [] a)) r
  | (RRealloc k n a, q) :: r => p3c_rrun F (rt_realloc F b k n (resolveF [] a) q) r
  end.

Fixpoint p3c_rroom (F : ResFormT) (b : rt_R F) (rs : list (rev sptr * sptr)) : Prop :=
  match rs with
  | [] => True
  | (RMalloc n, _) :: r => rt_room F b n /\ p3c_rroom F (rt_malloc F b n) r
  | (RFree n a, _) :: r => p3c_rroom F (rt_free F b n (resolveF [] a)) r
  | (RRealloc k n a, q) :: r => rt_room F b n /\ p3c_rroom F (rt_realloc F b k n (resolveF [] a) q) r
  end.

Abbreviation p3c_run F Q b j t := (run_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) Q b j t).
Abbreviation p3c_room F Q b j t :=
  (room_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (rt_room F) Q b j t).

Definition p3c_pad (n : nat) : list sptr := repeat (SP 0 0) n.

Lemma p3c_pad_len : forall n, length (p3c_pad n) = n.
Proof. intros n. apply repeat_length. Qed.

Lemma p3c_run_res : forall F Q t b j, p3c_run F Q b j t = p3c_rrun F b (p3c_res Q j t).
Proof.
  intros F Q t. induction t as [|[n|n a|k n a] t IH]; intros b j; cbn [run_from p3c_res p3c_rrun resolve];
    [reflexivity | apply IH ..].
Qed.

Lemma p3c_room_res : forall F Q t b j, p3c_room F Q b j t <-> p3c_rroom F b (p3c_res Q j t).
Proof.
  intros F Q t. induction t as [|[n|n a|k n a] t IH]; intros b j; cbn [room_from p3c_res p3c_rroom resolve].
  - tauto.
  - rewrite IH. tauto.
  - apply IH.
  - rewrite IH. tauto.
Qed.

Lemma p3c_runF : forall F Q b t, runF F Q b t = p3c_run F Q b 0 t.
Proof. reflexivity. Qed.

Lemma p3c_roomF : forall F Q b t, roomF F Q b t = p3c_room F Q b 0 t.
Proof. reflexivity. Qed.

Lemma p3c_nret_cons : forall (e : rev sptr) t, nretF (e :: t) = (rets sptr e + nretF t)%nat.
Proof. reflexivity. Qed.

Lemma p3c_res_app : forall Q t1 t2 j, p3c_res Q j (t1 ++ t2) = p3c_res Q j t1 ++ p3c_res Q (j + nretF t1) t2.
Proof.
  intros Q t1 t2. induction t1 as [|[n|n a|k n a] t1 IH]; intros j; cbn [app p3c_res].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH, p3c_nret_cons. cbn [rets]. replace (j + (1 + nretF t1))%nat with (S j + nretF t1)%nat by lia.
    reflexivity.
  - rewrite IH, p3c_nret_cons. cbn [rets]. replace (j + (0 + nretF t1))%nat with (j + nretF t1)%nat by lia.
    reflexivity.
  - rewrite IH, p3c_nret_cons. cbn [rets]. replace (j + (1 + nretF t1))%nat with (S j + nretF t1)%nat by lia.
    reflexivity.
Qed.

Lemma p3c_sl_cap : forall f mx no cap rem j o j' o',
  fst (snd (sl_run f mx no cap rem j o)) = fst (snd (sl_run f mx no cap rem j' o')).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [sl_run]; [reflexivity|].
  destruct (rem <=? 0); [reflexivity|]. cbv zeta.
  match goal with |- context [cap <? ?x] => destruct (cap <? x) end; cbn [fst snd]; apply IH.
Qed.

(* Two runs of fuzz_send's growth with the same model values read the same resolved requests when their buffers and
   the addresses their requests return resolve alike. *)
Lemma p3c_sl_res : forall f mx no cap rem Q Q' j j' o o',
  (cap <> 0 -> resolveF Q o = resolveF Q' o') ->
  (forall i, (i < nretF (fst (sl_run f mx no cap rem j' o')))%nat -> nth (j + i) Q (SP 0 0) = nth (j' + i) Q' (SP 0 0)) ->
  p3c_res Q j (fst (sl_run f mx no cap rem j o)) = p3c_res Q' j' (fst (sl_run f mx no cap rem j' o')) /\
  nretF (fst (sl_run f mx no cap rem j o)) = nretF (fst (sl_run f mx no cap rem j' o')) /\
  (fst (snd (sl_run f mx no cap rem j o)) <> 0 ->
     resolveF Q (snd (snd (sl_run f mx no cap rem j o))) = resolveF Q' (snd (snd (sl_run f mx no cap rem j' o')))).
Proof.
  induction f as [|f IH]; intros mx no cap rem Q Q' j j' o o' Ho HN; cbn [sl_run] in HN |- *.
  - cbn [fst snd p3c_res]. split; [reflexivity|]. split; [reflexivity | exact Ho].
  - destruct (rem <=? 0); [cbn [fst snd p3c_res]; split; [reflexivity|]; split; [reflexivity | exact Ho]|].
    cbv zeta in HN |- *.
    set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem) in *.
    destruct (cap <? no + n).
    + cbn [fst snd] in HN |- *.
      assert (HR : forall i, (i < S (nretF (fst (sl_run f mx (no + n) ((no + n) * 2) (rem - n) (S j') (Ret j')))))%nat ->
                     nth (j + i) Q (SP 0 0) = nth (j' + i) Q' (SP 0 0)).
      { intros i Hi. apply HN. destruct (cap =? 0); exact Hi. }
      clear HN.
      assert (H0 : nth j Q (SP 0 0) = nth j' Q' (SP 0 0)).
      { specialize (HR 0%nat ltac:(lia)). rewrite !Nat.add_0_r in HR. exact HR. }
      destruct (IH mx (no + n) ((no + n) * 2) (rem - n) Q Q' (S j) (S j') (Ret j) (Ret j')) as (R1 & R2 & R3).
      { intros _. cbn [resolve]. exact H0. }
      { intros i Hi. specialize (HR (S i) ltac:(lia)).
        replace (S j + i)%nat with (j + S i)%nat by lia. replace (S j' + i)%nat with (j' + S i)%nat by lia. exact HR. }
      split; [|split; [|exact R3]].
      * destruct (cap =? 0) eqn:C; cbn [p3c_res]; [rewrite R1; reflexivity|].
        rewrite (Ho ltac:(apply Z.eqb_neq; exact C)), H0, R1. reflexivity.
      * rewrite !p3c_nret_cons, R2. destruct (cap =? 0); reflexivity.
    + exact (IH mx (no + n) cap (rem - n) Q Q' j j' o o' Ho HN).
Qed.

Lemma p3c_send_res : forall live mx no cap len Q Q' j j' o o',
  (cap <> 0 -> resolveF Q o = resolveF Q' o') ->
  (forall i, (i < nretF (send_line_tr live mx no cap len j' o'))%nat -> nth (j + i) Q (SP 0 0) = nth (j' + i) Q' (SP 0 0)) ->
  p3c_res Q j (send_line_tr live mx no cap len j o) = p3c_res Q' j' (send_line_tr live mx no cap len j' o') /\
  nretF (send_line_tr live mx no cap len j o) = nretF (send_line_tr live mx no cap len j' o') /\
  (send_line_cap live mx no cap len <> 0 ->
     resolveF Q (send_line_out live mx no cap len j o) = resolveF Q' (send_line_out live mx no cap len j' o')).
Proof.
  intros [|] mx no cap len Q Q' j j' o o' Ho HN; unfold send_line_tr, send_line_cap, send_line_out in *.
  - destruct (p3c_sl_res (Z.to_nat len) mx no cap len Q Q' j j' o o' Ho HN) as (R1 & R2 & R3).
    split; [exact R1|]. split; [exact R2|].
    intros C. apply R3. rewrite (p3c_sl_cap _ _ _ _ _ j o 0%nat adr0). exact C.
  - cbn [p3c_res nret fold_right]. split; [reflexivity|]. split; [reflexivity | exact Ho].
Qed.

Lemma p3c_ge1_res : forall live mx no cap xl Q Q' j j' o o',
  (cap <> 0 -> resolveF Q o = resolveF Q' o') ->
  (forall i, (i < nretF (gesture_end_tr live mx no cap xl j' o'))%nat -> nth (j + i) Q (SP 0 0) = nth (j' + i) Q' (SP 0 0)) ->
  p3c_res Q j (gesture_end_tr live mx no cap xl j o) = p3c_res Q' j' (gesture_end_tr live mx no cap xl j' o') /\
  nretF (gesture_end_tr live mx no cap xl j o) = nretF (gesture_end_tr live mx no cap xl j' o') /\
  (gesture_end_cap live mx no cap xl <> 0 ->
     resolveF Q (gesture_end_out live mx no cap xl j o) = resolveF Q' (gesture_end_out live mx no cap xl j' o')).
Proof.
  intros live mx no cap xl Q Q' j j' o o' Ho HN. unfold gesture_end_tr, gesture_end_out, gesture_end_cap in *.
  cbv zeta in HN |- *. rewrite nret_app in HN.
  destruct (p3c_send_res live mx no cap xl Q Q' j j' o o' Ho ltac:(intros i Hi; apply HN; lia)) as (A1 & A2 & A3).
  destruct (p3c_send_res live mx (no + xl) (send_line_cap live mx no cap xl) 5 Q Q'
              (j + nretF (send_line_tr live mx no cap xl j o)) (j' + nretF (send_line_tr live mx no cap xl j' o'))
              (send_line_out live mx no cap xl j o) (send_line_out live mx no cap xl j' o') A3) as (B1 & B2 & B3).
  { intros i Hi. rewrite A2, <- !Nat.add_assoc. apply HN. lia. }
  rewrite !p3c_res_app, !nret_app, A1, B1, B2.
  split; [reflexivity|]. split; [rewrite A2; reflexivity | exact B3].
Qed.

Lemma p3c_ker_res : forall live mx xks xks' Q Q' no cap j j' o o',
  Forall2 (fun x x' => fst x = fst x' /\ resolveF Q (snd x) = resolveF Q' (snd x')) xks xks' ->
  (cap <> 0 -> resolveF Q o = resolveF Q' o') ->
  (forall i, (i < nretF (fst (keys_end_run live mx no cap xks' j' o')))%nat ->
     nth (j + i) Q (SP 0 0) = nth (j' + i) Q' (SP 0 0)) ->
  p3c_res Q j (fst (keys_end_run live mx no cap xks j o)) = p3c_res Q' j' (fst (keys_end_run live mx no cap xks' j' o')) /\
  nretF (fst (keys_end_run live mx no cap xks j o)) = nretF (fst (keys_end_run live mx no cap xks' j' o')) /\
  (fst (snd (keys_end_run live mx no cap xks j o)) <> 0 ->
     resolveF Q (snd (snd (keys_end_run live mx no cap xks j o))) =
     resolveF Q' (snd (snd (keys_end_run live mx no cap xks' j' o')))).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros xks' Q Q' no cap j j' o o' HF Ho HN.
  - inversion HF. subst. cbn [keys_end_run fst snd p3c_res]. split; [reflexivity|]. split; [reflexivity | exact Ho].
  - destruct xks' as [|[xl' ka'] r']; [inversion HF|].
    assert (HF2 : (fst (xl, ka) = fst (xl', ka') /\ resolveF Q (snd (xl, ka)) = resolveF Q' (snd (xl', ka'))) /\
                  Forall2 (fun x x' => fst x = fst x' /\ resolveF Q (snd x) = resolveF Q' (snd x')) r r')
      by (inversion HF; subst; split; assumption).
    destruct HF2 as [[Ex Ea] HF']. cbn [fst snd] in Ex, Ea. subst xl'.
    cbn [keys_end_run] in HN |- *. cbv zeta in HN |- *. cbn [fst snd] in HN |- *.
    rewrite nret_app, p3c_nret_cons in HN. cbn [rets] in HN.
    destruct (p3c_ge1_res live mx no cap xl Q Q' j j' o o' Ho ltac:(intros i Hi; apply HN; lia)) as (A1 & A2 & A3).
    destruct (IH r' Q Q' (no + xl + 5) (gesture_end_cap live mx no cap xl) (j + nretF (gesture_end_tr live mx no cap xl j o))%nat
                (j' + nretF (gesture_end_tr live mx no cap xl j' o'))%nat (gesture_end_out live mx no cap xl j o)
                (gesture_end_out live mx no cap xl j' o') HF' A3) as (B1 & B2 & B3).
    { intros i Hi. rewrite A2, <- !Nat.add_assoc. apply HN. lia. }
    rewrite !p3c_res_app, !nret_app, !p3c_nret_cons. cbn [p3c_res rets]. rewrite A1, Ea, B1, B2.
    split; [reflexivity|]. split; [rewrite A2; reflexivity | exact B3].
Qed.

Lemma p3c_ker_cap : forall live mx xks xks' no cap j o j' o', map fst xks = map fst xks' ->
  fst (snd (keys_end_run live mx no cap xks j o)) = fst (snd (keys_end_run live mx no cap xks' j' o')).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros [|[xl' ka'] r'] no cap j o j' o' E; cbn in E;
    try discriminate; [reflexivity|].
  injection E as <- E. cbn [keys_end_run]. cbv zeta. cbn [fst snd]. apply IH. exact E.
Qed.

Lemma p3c_gec : forall live mx no cap xks j o,
  gestures_end_cap live mx no cap (map fst xks) = fst (snd (keys_end_run live mx no cap xks j o)).
Proof.
  intros. unfold gestures_end_cap. apply p3c_ker_cap. rewrite map_map. cbn. apply map_id.
Qed.

Lemma p3c_ges_res : forall live mx no cap xks xks' hp kh Q Q' j j' o o' ha ha',
  Forall2 (fun x x' => fst x = fst x' /\ resolveF Q (snd x) = resolveF Q' (snd x')) xks xks' ->
  (cap <> 0 -> resolveF Q o = resolveF Q' o') -> (hp <> 0 -> resolveF Q ha = resolveF Q' ha') ->
  (forall i, (i < nretF (gestures_end_tr live mx no cap xks' hp kh j' o' ha'))%nat ->
     nth (j + i) Q (SP 0 0) = nth (j' + i) Q' (SP 0 0)) ->
  p3c_res Q j (gestures_end_tr live mx no cap xks hp kh j o ha) =
    p3c_res Q' j' (gestures_end_tr live mx no cap xks' hp kh j' o' ha') /\
  nretF (gestures_end_tr live mx no cap xks hp kh j o ha) = nretF (gestures_end_tr live mx no cap xks' hp kh j' o' ha') /\
  (gestures_end_cap live mx no cap (map fst xks) <> 0 ->
     resolveF Q (gestures_end_out live mx no cap xks j o) = resolveF Q' (gestures_end_out live mx no cap xks' j' o')).
Proof.
  intros live mx no cap xks xks' hp kh Q Q' j j' o o' ha ha' HF Ho Hh HN.
  unfold gestures_end_tr, gestures_end_out in *. rewrite nret_app in HN.
  destruct (p3c_ker_res live mx xks xks' Q Q' no cap j j' o o' HF Ho ltac:(intros i Hi; apply HN; lia))
    as (A1 & A2 & A3).
  rewrite !p3c_res_app, !nret_app, A1, A2.
  split; [|split; [|intros C; apply A3; rewrite <- (p3c_gec live mx no cap xks j o); exact C]].
  - f_equal. destruct (hp =? 0) eqn:E; [reflexivity|]. cbn [p3c_res].
    rewrite (Hh ltac:(apply Z.eqb_neq; exact E)). reflexivity.
  - destruct (hp =? 0); reflexivity.
Qed.

Lemma p3c_kr_f2 : forall nm nm' Q Q' ks,
  (forall k, In k ks -> resolveF Q (nm (key_addr k)) = resolveF Q' (nm' (key_addr k))) ->
  Forall2 (fun x x' => fst x = fst x' /\ resolveF Q (snd x) = resolveF Q' (snd x')) (key_runs nm ks) (key_runs nm' ks).
Proof.
  intros nm nm' Q Q' ks H. unfold key_runs. induction ks as [|k ks IH]; cbn [map]; constructor.
  - split; [reflexivity | apply H; left; reflexivity].
  - apply IH. intros k' Hk'. apply H. right. exact Hk'.
Qed.

Lemma p3c_kr_eq : forall nm ks ks', map key_addr ks' = map key_addr ks -> map key_text ks' = map key_text ks ->
  key_runs nm ks' = key_runs nm ks.
Proof.
  intros nm ks. unfold key_runs. induction ks as [|k ks IH]; intros [|k' ks'] HA HT; cbn [map] in HA, HT |- *;
    try discriminate; [reflexivity|].
  injection HA as HA1 HA2. injection HT as HT1 HT2. rewrite HA1, HT1, (IH ks' HA2 HT2). reflexivity.
Qed.

Lemma p3c_kr_fst : forall nm ks, map fst (key_runs nm ks) = key_lens ks.
Proof. intros nm ks. unfold key_runs, key_lens. rewrite map_map. reflexivity. Qed.

Lemma p3c_nodup_inj : forall {X Y : Type} (f : X -> Y) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y ->
  x = y.
Proof.
  intros X Y f l. induction l as [|z l IH]; intros x y HN Hx Hy E; [destruct Hx|].
  cbn [map] in HN. apply List.NoDup_cons_iff in HN as [Hz HN].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity | | | exact (IH x y HN Hx Hy E)].
  - exfalso. apply Hz. rewrite E. exact (in_map f l y Hy).
  - exfalso. apply Hz. rewrite <- E. exact (in_map f l x Hx).
Qed.

(* With the block addresses distinct, the live block at a is the one sptr_of names. *)
Lemma p3c_live_sptr : forall L A p a n, NoDup (map fst (blocks L A)) -> live_at L A p a n -> sptr_of L A a = p.
Proof.
  intros L A p a n HN [Hin Ha].
  assert (Hb : In (a, n) (blocks L A)).
  { unfold blocks. rewrite <- Ha. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hin). }
  destruct (sptr_of_spec L A a n HN Hb) as [Hs Hsa].
  apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN. unfold blocks in HN. rewrite map_map in HN.
  assert (E := p3c_nodup_inj _ _ _ _ HN Hs Hin ltac:(cbn [fst]; congruence)). congruence.
Qed.

Lemma fi_ker_false : forall mx no c xks j o,
  keys_end_run false mx no c xks j o = (map (fun xk => RFree (fst xk + 1) (snd xk)) xks, (c, o)).
Proof.
  intros mx no c xks. revert no c. induction xks as [|[xl ka] xks IH]; intros no c j o; [reflexivity|].
  cbn. rewrite IH. reflexivity.
Qed.

Lemma fi_gec_false : forall mx no c xls, gestures_end_cap false mx no c xls = c.
Proof. intros. unfold gestures_end_cap. rewrite fi_ker_false. reflexivity. Qed.

(* g_capout after closing the sources does not depend on the addresses. *)
Lemma p3c_eer_cap : forall nm nm' live mx l no c j o j' o',
  fst (snd (entries_end_run nm live mx no c l j o)) = fst (snd (entries_end_run nm' live mx no c l j' o')).
Proof.
  intros nm nm' live mx l. induction l as [|e l IH]; intros no c j o j' o'; [reflexivity|].
  cbn [entries_end_run]. cbv zeta. cbn [fst snd]. apply IH.
Qed.

Lemma p3c_run_free : forall F Q b j t n a,
  p3c_run F Q b j (t ++ [RFree n a]) = rt_free F (p3c_run F Q b j t) n (resolveF Q a).
Proof. intros. rewrite run_from_app. reflexivity. Qed.

Lemma p3c_runF_free : forall F Q b t n a, runF F Q b (t ++ [RFree n a]) = rt_free F (runF F Q b t) n (resolveF Q a).
Proof. intros. apply p3c_run_free. Qed.

Lemma fi_kl_nz : forall ks, key_lens ks <> [] -> keys_total ks <> 0.
Proof.
  intros [|k ks] H; [contradiction H; reflexivity|].
  pose proof (fi_kt_nonneg ks) as N. unfold keys_total in N |- *. cbn [fold_right]. lia.
Qed.

Lemma fi_kl_eq : forall ks ks', map key_text ks' = map key_text ks -> key_lens ks' = key_lens ks.
Proof.
  intros ks ks' H. unfold key_lens.
  transitivity (map (fun t : list byte => Z.of_nat (length t)) (map key_text ks')); [rewrite map_map; reflexivity|].
  rewrite H, map_map. reflexivity.
Qed.


Section FinB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTXO : ctx_owned Bm API.
Hypothesis SLK : block_slack_present Bm API.
Hypothesis FREEPC : ms_free Bm = 0x15f4c.
Hypothesis HND : forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A)).

(* A live block of positive size outside the moved set stays the same live block. *)
Lemma p3c_rp_live : forall K E Fq L A regs mem md L' A' regs' mem' md' p a n,
  relay_post Bm API K E Fq L A regs mem md L' A' regs' mem' md' -> live_at L A p a n -> 0 < n -> ~ Fq a ->
  live_at L' A' p a n.
Proof using.
  intros K E Fq L A regs mem md L' A' regs' mem' md' p a n RP [Hin Ha] Hn HF.
  destruct RP as (_ & _ & _ & _ & _ & AD & SV & _). subst a.
  pose proof (SV p n Hin Hn HF) as Hin'. split; [exact Hin' | exact (AD p n Hin Hin' HF)].
Qed.

Section Run.
Variable RFm : ResFormT.
Hypothesis SPL : pthread_mutex_lock_contract.
Hypothesis SPU : pthread_mutex_unlock_contract.
Hypothesis HFREE : free_contract_rt Bm API RFm.
Hypothesis HFREEN : free_null_contract Bm.
Hypothesis HGE : gestures_end_contract Bm API RFm.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (bnd : rt_R RFm) (es : list rentry) (C G : Z) (tail O junk : list byte) (lst cl br dd ei : Z)
  (mx nout cap out : word).

Local Notation N := (Z.of_nat (length es)).
Local Notation TOT := (entries_total es).
Local Notation ERR := (errno_addr Bm).
Local Notation NO := (bv_unsigned nout).
Local Notation CAP := (bv_unsigned cap).
Local Notation OUT := (bv_unsigned out).
Local Notation live := (send_live cl br dd TOT).
Local Notation SP := (bv_unsigned (reg_get regs0 2)).
Local Notation nm0 := (known_at L0 A0).
Local Notation TR := (relay_finish_tr (known_at L0 A0) (send_live cl br dd (entries_total es)) (bv_unsigned mx)
  (bv_unsigned nout) (bv_unsigned cap) es 0 (known_at L0 A0 (bv_unsigned out))).

Hypothesis SEGS : ms_segs Bm = rsegs.
Hypothesis PRE : call_pre_k Bm (aa_MR API) RELAY_FINISH_K L0 A0 regs0 mem0 md0.
Hypothesis INIT : st_init_done A0 = true.
Hypothesis TPE : ms_tp Bm + ERRNO_OFF = ERR.
Hypothesis HERR4 : ERR mod 4 = 0.
Hypothesis HERR : G_LOCK_HI <= ERR.
Hypothesis RA : ro_agree rsegs mem0.
Hypothesis IMGR : forall a, G_RELAY_LO <= a < G_LOCK_HI -> img_plain Bm a.
Hypothesis IMGL : forall a, G_LISTEN <= a < G_CLIENT + 4 -> img_plain Bm a.
Hypothesis IMGE : forall a, ERR <= a < ERR + 4 -> in_img Bm a.
Hypothesis IMG5 : forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a.
Hypothesis CTU : rw_cells rsegs mem0 G_THREAD_UP [C1 (Z_to_bv 8 0)].
Hypothesis CLK : rw_cells rsegs mem0 G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Hypothesis CNS : rw_cells rsegs mem0 G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)].
Hypothesis CSR : rw_cells rsegs mem0 G_SRC [C8 (Z_to_bv 64 G)].
Hypothesis CLS : rw_cells rsegs mem0 G_LISTEN [C4 (Z_to_bv 64 lst); C4 (Z_to_bv 64 cl)].
Hypothesis HN4 : N <= 4.
Hypothesis HTAB : (C = 0 /\ G = 0 /\ es = []) \/
  (C = 16 /\ In (G, SRC_TABLE) (blocks L0 A0) /\ fresh_block Bm G SRC_TABLE /\ G <> OUT /\
   ~ In G (concat (map entry_blocks es)) /\ table_at Bm mem0 G es tail).
Hypothesis HEOK : Forall (entry_ok Bm L0 A0 mem0) es.
Hypothesis HDJ : entries_disjoint OUT es.
Hypothesis Hcl : cl = 3 \/ cl = -1.
Hypothesis Hbr : br = 0 \/ br = 1.
Hypothesis Hdd : dd = 0 \/ dd = 1.
Hypothesis Hei : ei = 0 \/ ei = 1.
Hypothesis CBR : rw_cells rsegs mem0 G_BROKEN [C1 (Z_to_bv 8 br)].
Hypothesis CDD : rw_cells rsegs mem0 G_DEAD [C1 (Z_to_bv 8 dd)].
Hypothesis CEI : rw_cells rsegs mem0 G_EINTR [C1 (Z_to_bv 8 ei)].
Hypothesis COV : rw_cells rsegs mem0 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out].
Hypothesis CER : exists ev, rw_cells rsegs mem0 ERR [C4 ev].
Hypothesis HOUT : (CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
  (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L0 A0) /\ fresh_block Bm OUT CAP /\
   bytes_at rsegs mem0 OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO).
Hypothesis HREQ : 2 * (NO + TOT) < 2 ^ 63.
Hypothesis HRES : rt_ok RFm A0 bnd.
Hypothesis HROOM : forall qs, length qs = nretF TR -> roomF RFm qs bnd TR.

Local Notation Efin := (fun a : Z => send_writes live OUT CAP a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/
  G_NSRC <= a < G_NSRC + 4 \/ G_LISTEN <= a < G_CLIENT + 4 \/ (C = 16 /\ G <= a < G + SRC_TABLE)).
Local Notation Ffin := (fun q : Z => (live = true /\ q = OUT) \/ In q (concat (map entry_blocks es))).

Definition brT (T : Z) : Z := if send_off cl br T then br else dd.
Definition eiT (T : Z) : Z := if send_off cl br T then ei else 0.
Definition lvT (T : Z) : bool := send_live cl br dd T.

(* The requests of closing the sources l from g_nout = no, g_capout = c, base j, g_out at o: the requests, the final
   g_capout and g_out. *)
Definition er (l : list rentry) (no c : Z) (j : nat) (o : adrF) : trF * (Z * adrF) :=
  entries_end_run nm0 live (bv_unsigned mx) no c l j o.

(* The resource state after the requests tp made so far, which returned qs, g_out at o, and the requests rr still to
   come: together the whole trace of relay_finish, with its final g_capout and g_out. The output buffer and the
   start blocks not released (P) are the blocks the trace names. *)
Definition RSt (L1 : layout) (A1 : astate) (rr : nat -> adrF -> trF * (Z * adrF)) (cap1 out1 : Z) (P : list Z)
    : Prop :=
  exists tp qs o,
    nretF tp = length qs /\
    rt_ok RFm A1 (runF RFm qs bnd tp) /\
    (forall ext, p3c_run RFm (qs ++ ext) bnd 0 tp = runF RFm qs bnd tp) /\
    (cap1 <> 0 -> forall ext, resolveF (qs ++ ext) o = resolveF qs o) /\
    (forall rest, length rest = nretF (fst (rr (length qs) o)) ->
       p3c_room RFm (qs ++ rest) (runF RFm qs bnd tp) (length qs) (fst (rr (length qs) o))) /\
    tp ++ fst (rr (length qs) o) = TR /\
    (live = true -> fst (snd (rr (length qs) o)) = relay_finish_cap live (bv_unsigned mx) NO CAP es) /\
    snd (snd (rr (length qs) o)) = relay_finish_out nm0 live (bv_unsigned mx) NO CAP es 0 (nm0 OUT) /\
    (cap1 <> 0 -> live_at L1 A1 (resolveF qs o) out1 cap1) /\
    (forall q m, In (q, m) (blocks L0 A0) -> q <> OUT -> ~ In q P -> 0 < m -> live_at L1 A1 (sptr_of L0 A0 q) q m).

Lemma fi_RSt_ext : forall L1 A1 rr rr' cap1 out1 P, (forall j o, rr j o = rr' j o) ->
  RSt L1 A1 rr cap1 out1 P -> RSt L1 A1 rr' cap1 out1 P.
Proof using.
  intros L1 A1 rr rr' cap1 out1 P E (tp & qs & o & H). exists tp, qs, o. rewrite <- (E (length qs) o). exact H.
Qed.

(* The data invariant of a state of relay_finish after the lock is taken. P lists the
   original block addresses released so far, T1 the key bytes sent so far, Eo those bytes,
   tab the current table contents, rr the requests still to come. *)
Definition CI (L1 : layout) (A1 : astate) (m1 : word -> option byte) (md1 : Model)
    (rr : nat -> adrF -> trF * (Z * adrF))
    (nout1 cap1 out1 : word) (O1 junk1 : list byte) (P : list Z) (T1 : Z) (Eo : list byte)
    (tab : list rentry) : Prop :=
  relay_post Bm API RELAY_FINISH_K Efin Ffin L0 A0 regs0 mem0 md0 L1 A1 regs0 m1 md1 /\
  st_init_done A1 = true /\
  RSt L1 A1 rr (bv_unsigned cap1) (bv_unsigned out1) P /\
  ro_agree rsegs m1 /\
  rw_cells rsegs m1 G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
  rw_cells rsegs m1 G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] /\
  rw_cells rsegs m1 G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)] /\
  rw_cells rsegs m1 G_SRC [C8 (Z_to_bv 64 G)] /\
  rw_cells rsegs m1 G_LISTEN [C4 (Z_to_bv 64 lst); C4 (Z_to_bv 64 cl)] /\
  rw_cells rsegs m1 G_BROKEN [C1 (Z_to_bv 8 (brT T1))] /\
  rw_cells rsegs m1 G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells rsegs m1 G_EINTR [C1 (Z_to_bv 8 (eiT T1))] /\
  rw_cells rsegs m1 G_OUTV [C8 mx; C8 nout1; C8 cap1; C8 out1] /\
  (exists ev, rw_cells rsegs m1 ERR [C4 ev]) /\
  rw_cells rsegs m1 (SP + -40) [C8 (reg_get regs0 19); C8 (reg_get regs0 18);
                                C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)] /\
  (C = 16 -> table_at Bm m1 G tab tail /\ In (G, SRC_TABLE) (blocks L1 A1)) /\
  (forall q m, In (q, m) (blocks L1 A1) <->
     ((In (q, m) (blocks L0 A0) /\ q <> OUT /\ ~ In q P) \/
      (lvT T1 = true /\ q = bv_unsigned out1 /\ m = bv_unsigned cap1) \/
      (lvT T1 = false /\ 0 < CAP /\ q = OUT /\ m = CAP))) /\
  (lvT T1 = false -> nout1 = nout /\ cap1 = cap /\ out1 = out /\ O1 = O /\ junk1 = junk) /\
  (lvT T1 = true ->
     bv_unsigned nout1 = NO + T1 /\ fresh_block Bm (bv_unsigned out1) (bv_unsigned cap1) /\
     (forall q m, In (q, m) (blocks L0 A0) -> q <> OUT -> ~ In q P -> 0 < m -> q <> bv_unsigned out1) /\
     O1 = O ++ Eo) /\
  ((bv_unsigned cap1 = 0 /\ bv_unsigned out1 = 0 /\ bv_unsigned nout1 = 0 /\ O1 = []) \/
   (0 < bv_unsigned cap1 /\ bv_unsigned nout1 <= bv_unsigned cap1 /\
    In (bv_unsigned out1, bv_unsigned cap1) (blocks L1 A1) /\ fresh_block Bm (bv_unsigned out1) (bv_unsigned cap1) /\
    bytes_at rsegs m1 (bv_unsigned out1) (O1 ++ junk1) /\ Z.of_nat (length O1) = bv_unsigned nout1 /\
    Z.of_nat (length junk1) = bv_unsigned cap1 - bv_unsigned nout1)).

(* Registers kept by the loop. *)
Definition RL (R : bvmap 5 word) : Prop :=
  reg_get R 2 = Z_to_bv 64 (SP + -48) /\ reg_get R 3 = reg_get regs0 3 /\ reg_get R 4 = reg_get regs0 4 /\
  reg_get R 8 = Z_to_bv 64 203000 /\ reg_get R 9 = Z_to_bv 64 202912 /\ reg_get R 20 = reg_get regs0 20 /\
  reg_get R 21 = reg_get regs0 21 /\ reg_get R 22 = reg_get regs0 22 /\ reg_get R 23 = reg_get regs0 23 /\
  reg_get R 24 = reg_get regs0 24 /\ reg_get R 25 = reg_get regs0 25 /\ reg_get R 26 = reg_get regs0 26 /\
  reg_get R 27 = reg_get regs0 27.

Definition Pfx (i : nat) : list Z := concat (map entry_blocks (firstn i es)).
Definition Tfx (i : nat) : Z := entries_total (firstn i es).
Definition Efx (i : nat) : list byte := entries_out (firstn i es).
Definition Tab (i : nat) : list rentry := map entry_cleared (firstn i es) ++ skipn i es.
Definition bufl (e : rentry) : list Z := if re_cap e =? 0 then [] else [re_buf e].
Definition hpl (e : rentry) : list Z := if re_hp e =? 0 then [] else [re_hp e].
Definition bufree (e : rentry) : trF := if re_cap e =? 0 then [] else [RFree (re_cap e) (nm0 (re_buf e))].

(* The requests still to come after free (s->buf) of entry i = e, from g_capout = c, base j, g_out at o. *)
Definition fr (i : nat) (e : rentry) (c : Z) (j : nat) (o : adrF) : trF * (Z * adrF) :=
  let xks := key_runs nm0 (re_keys e) in
  let tg := gestures_end_tr live (bv_unsigned mx) (NO + Tfx i) c xks (re_hp e) (re_kh e) j o (nm0 (re_hp e)) in
  let p := er (skipn (S i) es) (NO + Tfx i + keys_total (re_keys e))
             (gestures_end_cap live (bv_unsigned mx) (NO + Tfx i) c (key_lens (re_keys e))) (j + nretF tg)
             (gestures_end_out live (bv_unsigned mx) (NO + Tfx i) c xks j o) in
  (tg ++ fst p, snd p).

Definition LoopSt (i : nat) (c : config) : Prop :=
  exists L1 A1 R1 m1 md1 nout1 cap1 out1 O1 junk1,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 78108) m1 (seg_rom rsegs)) md1 /\
    RL R1 /\ reg_get R1 18 = Z_to_bv 64 (56 * Z.of_nat i) /\ reg_get R1 19 = Z_to_bv 64 (Z.of_nat i) /\
    CI L1 A1 m1 md1 (er (skipn i es) (NO + Tfx i) (bv_unsigned cap1)) nout1 cap1 out1 O1 junk1
      (Pfx i) (Tfx i) (Efx i) (Tab i) /\
    Forall (fi_est L1 A1 m1) (skipn i es).

Definition FreeSt (i : nat) (e : rentry) (c : config) : Prop :=
  exists L1 A1 R1 m1 md1 nout1 cap1 out1 O1 junk1,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 78336) m1 (seg_rom rsegs)) md1 /\
    RL R1 /\ reg_get R1 18 = Z_to_bv 64 (56 * Z.of_nat i) /\ reg_get R1 19 = Z_to_bv 64 (Z.of_nat i) /\
    reg_get R1 1 = Z_to_bv 64 78196 /\ reg_get R1 10 = Z_to_bv 64 (G + 56 * Z.of_nat i) /\
    CI L1 A1 m1 md1 (fr i e (bv_unsigned cap1)) nout1 cap1 out1 O1 junk1 (Pfx i ++ bufl e) (Tfx i) (Efx i) (Tab i) /\
    fi_kst L1 A1 m1 e /\ Forall (fi_est L1 A1 m1) (skipn (S i) es).

Definition ExitSt (c : config) : Prop :=
  exists L1 A1 R1 m1 md1 nout1 cap1 out1 O1 junk1,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 78212) m1 (seg_rom rsegs)) md1 /\
    RL R1 /\
    CI L1 A1 m1 md1 (er (skipn (length es) es) (NO + Tfx (length es)) (bv_unsigned cap1)) nout1 cap1 out1 O1 junk1
      (Pfx (length es)) (Tfx (length es)) (Efx (length es)) (Tab (length es)).

Local Notation off := (send_off cl br TOT).
Local Notation br' := (if send_off cl br TOT then br else dd).
Local Notation ei' := (if send_off cl br TOT then ei else 0).

Definition Final (c' : config) : Prop :=
  exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' : list byte),
    c' = mkCfg (YK11.mkst regs' (getr regs0 1) mem' (seg_rom rsegs)) md' /\
    relay_post Bm API RELAY_FINISH_K Efin Ffin L0 A0 regs0 mem0 md0 L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF TR /\ rt_ok RFm A' (runF RFm qs bnd TR) /\
       (live = true ->
          live_at L' A' (resolveF qs (relay_finish_out nm0 live (bv_unsigned mx) NO CAP es 0 (nm0 OUT))) OUT' CAP')) /\
    ro_agree rsegs mem' /\
    rw_cells rsegs mem' G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
    rw_cells rsegs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
    rw_cells rsegs mem' G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 C)] /\
    rw_cells rsegs mem' G_SRC [C8 (Z_to_bv 64 G)] /\
    rw_cells rsegs mem' G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
    (C = 16 -> table_at Bm mem' G (map entry_cleared es) tail /\ In (G, SRC_TABLE) (blocks L' A')) /\
    rw_cells rsegs mem' G_BROKEN [C1 (Z_to_bv 8 br')] /\
    rw_cells rsegs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
    rw_cells rsegs mem' G_EINTR [C1 (Z_to_bv 8 ei')] /\
    (exists ev', rw_cells rsegs mem' ERR [C4 ev']) /\
    (forall q m, In (q, m) (blocks L' A') <->
       ((In (q, m) (blocks L0 A0) /\ q <> OUT /\ ~ In q (concat (map entry_blocks es))) \/
        (live = true /\ q = OUT' /\ m = CAP') \/
        (live = false /\ 0 < CAP /\ q = OUT /\ m = CAP))) /\
    (live = false ->
       rw_cells rsegs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
    (live = true ->
       NO + TOT <= CAP' /\ CAP' = relay_finish_cap live (bv_unsigned mx) NO CAP es /\ fresh_block Bm OUT' CAP' /\
       (forall q m, In (q, m) (blocks L0 A0) -> q <> OUT -> ~ In q (concat (map entry_blocks es)) -> 0 < m ->
          q <> OUT') /\
       bytes_at rsegs mem' OUT' (O ++ entries_out es ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - TOT /\
       rw_cells rsegs mem' G_OUTV
         [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]).


Ltac fi_out := unfold G_THREAD_UP, G_NSRC, G_SRC, G_LISTEN, G_BROKEN, G_DEAD, G_EINTR, G_OUTV, G_LOCK;
  cbn [outside]; repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.

Ltac rgx X := match goal with |- reg_get ?R ?r = ?rhs =>
  rewrite <- (X r eq_refl);
  first [ reflexivity
        | match goal with H : reg_get _ r = rhs |- _ => etransitivity; [|exact H]; reflexivity end ] end.

Definition IvOk (W : list (Z * Z)) : Prop :=
  Forall (fun iv => YM05.alloc_ceiling <= fst iv \/ (forall x, fst iv <= x < snd iv -> in_img Bm x)) W.

Lemma fi_lowout : forall a W, 0 <= a < YM05.alloc_ceiling -> ~ in_img Bm a -> IvOk W -> outside W a.
Proof using O es junk.
  intros a W Ha Hi. induction W as [|[lo hi] W IH]; intros HF; [exact I|].
  apply Forall_cons_iff in HF as [H1 H2]. cbn [outside fst snd] in *. split; [|exact (IH H2)].
  intros Hx. destruct H1 as [H1|H1]; [lia | exact (Hi (H1 a Hx))].
Qed.

Lemma fi_blk_low : forall L A mem md q k j, aa_MR API L A mem md -> In (q, k) (blocks L A) -> 0 <= j < k ->
  0 <= q + j < YM05.alloc_ceiling /\ ~ in_img Bm (q + j).
Proof using AX O es junk.
  intros L A mem md q k j HM Hq Hj.
  destruct (fi_blk Bm API L A mem md q k j HM Hq Hj) as (_ & H1 & H2 & _).
  apply fi_blocks_in in Hq as (p & <- & Hp). split; [lia|].
  exact (ax_blocks_img AX L A mem md p k j HM Hp Hj).
Qed.

Lemma fi_fresh_low : forall q k j, fresh_block Bm q k -> 0 <= j < k ->
  0 <= q + j < YM05.alloc_ceiling /\ ~ in_img Bm (q + j).
Proof using O es junk. intros q k j (F1 & F2 & F3) Hj. split; [lia | exact (F3 j Hj)]. Qed.

Lemma fi_pre_facts :
  YM05.alloc_ceiling + 8464 <= SP /\ SP mod 16 = 0 /\ SP < 2 ^ 63 /\
  (forall a, SP - 8464 <= a < SP -> YP09.writable_at rsegs mem0 a) /\
  reg_get regs0 4 = Z_to_bv 64 (ms_tp Bm) /\ YK0s.ret_ok (reg_get regs0 1) /\
  (forall a, ERR <= a < ERR + 4 -> YP09.writable_at rsegs mem0 a) /\
  m_halted md0 = None /\ m_vm_lazy md0 = [] /\ aa_MR API L0 A0 mem0 md0.
Proof using PRE SEGS.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERRW & HAUX).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & _).
  rewrite fi_K in HCEIL, HWS. rewrite SEGS in HWS, HERRW.
  split; [exact HCEIL|]. split; [exact HAL|]. split; [exact H63|]. split; [exact HWS|].
  split; [exact HTP|]. split; [exact HRA|]. split; [exact HERRW|]. split; [exact Hh|]. split; [exact Hl | exact HMR].
Qed.

Lemma fi_err_low : 203040 <= ERR /\ ERR + 4 <= 2 ^ 21.
Proof using HERR IMGE O SEGS es junk.
  pose proof (in_img_low Bm SEGS (ERR + 3) (IMGE (ERR + 3) ltac:(lia))) as E1.
  unfold G_LOCK_HI in HERR. lia.
Qed.

Definition Wh : list (Z * Z) := [(SP + -48, SP); (203004, 203008)].

Lemma fi_Wh_ok : IvOk Wh.
Proof using IMGR O PRE SEGS es junk.
  destruct fi_pre_facts as (HCE & _).
  constructor; [left; cbn; lia|]. constructor; [|constructor].
  right. intros x Hx. cbn in Hx. exact (proj1 (IMGR x ltac:(unfold G_RELAY_LO, G_LOCK_HI; lia))).
Qed.

Definition HeadSt (c : config) : Prop :=
  exists R1 m1, c = mkCfg (YK11.mkst R1 (Z_to_bv 64 78092) m1 (seg_rom rsegs)) md0 /\ RL R1 /\
    CI L0 A0 m1 md0 (er (skipn 0 es) (NO + Tfx 0) CAP) nout cap out O junk [] 0 [] es /\ Forall (fi_est L0 A0 m1) es.

Lemma fi_lv0 : lvT 0 = false.
Proof using. unfold lvT, send_live, send_off. rewrite Z.eqb_refl, !orb_true_r. reflexivity. Qed.

Lemma fi_br0 : brT 0 = br.
Proof using. unfold brT, send_off. rewrite Z.eqb_refl, !orb_true_r. reflexivity. Qed.

Lemma fi_ei0 : eiT 0 = ei.
Proof using. unfold eiT, send_off. rewrite Z.eqb_refl, !orb_true_r. reflexivity. Qed.

Lemma fi_s_head : SR rsegs (mkCfg (YK11.mkst regs0 (Z_to_bv 64 RELAY_FINISH) mem0 (seg_rom rsegs)) md0) HeadSt.
Proof using AX CBR CDD CEI CER CLK CLS CNS COV CSR CTU HEOK HERR HND HOUT HRES HROOM HTAB IMGE IMGR INIT PRE RA SEGS SPL.
  destruct fi_pre_facts as (HCE & HAL & H63 & HWS & HTP & HRA & HERRW & Hh & Hl & HMR).
  pose proof YM05.alloc_ceiling_val as AC.
  pose proof fi_err_low as EL.
  pose proof fi_Wh_ok as WOK.
  pose proof (bv_unsigned_in_range 64 (reg_get regs0 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (ST : stk rsegs mem0 (SP - 8464) SP).
  { split; [lia|]. split; [lia|]. intros a Ha. apply fi_wr_hi; [lia | apply HWS; lia]. }
  eapply fi_bridge; [exact RA | exact Hh | exact Hl | | ].
  { unfold Regs6ss.mkR_of.
    eapply (fi_head SPL) with (lo := SP - 8464).
    - apply fi_stk_norm; [exact ST | lia].
    - lia.
    - lia.
    - apply mem_inv_normalize.
    - apply fi_rw_norm; [exact RA | exact CTU |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia.
    - apply fi_rw_norm; [exact RA | exact CLK |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia. }
  intros s0 R' m' HQ X MRl RS.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mn & -> & MU
    & WM & MI & FRm & GLm).
  cbn [ms_regs ms_mem] in X, MRl.
  destruct (fi_back mem0 mn m' _ RA MRl RS MU WM) as (MU' & WM' & RA').
  change [(bv_unsigned (reg_get regs0 2) + -48, bv_unsigned (reg_get regs0 2)); (203004, 203008)] with Wh in MU'.
  apply SR_ret. exists R', m'. split; [reflexivity|].
  assert (OUTB : forall a, 0 <= a < YM05.alloc_ceiling -> ~ in_img Bm a -> outside Wh a)
    by (intros a Ha Hi; exact (fi_lowout a Wh Ha Hi WOK)).
  split.
  { unfold RL. repeat split; rgx X. }
  split.
  2: { rewrite Forall_forall in HEOK |- *. intros e He.
       eapply fi_est_tr; [exact (HEOK e He) | eapply fi_eok_est; [exact SEGS | exact (HEOK e He)] |].
       intros q k Hk Hq _. split; [exact Hq|]. intros j Hj.
       destruct (fi_blk_low L0 A0 mem0 md0 q k j HMR Hq Hj) as [Hb Hi].
       exact (munch_mbyte rsegs Wh mem0 m' (q + j) MU' ltac:(lia) (OUTB _ Hb Hi)). }
  unfold CI.
  split.
  { eapply (fi_kA Bm API AX) with (W := Wh); [exact SEGS | apply fi_rp_id; exact PRE | exact MU' |
      rewrite SEGS; exact WM' |].
    intros a Ha. destruct (fi_outside_dec Wh a) as [Ho|Ho]; [left; exact Ho|right].
    assert (D : SP + -48 <= a < SP \/ 203004 <= a < 203008) by (unfold Wh in Ho; cbn [outside] in Ho; lia).
    change (spZ regs0) with SP. rewrite fi_K.
    destruct D as [D|D]; [left; lia|right].
    split; [apply IMGR; unfold G_RELAY_LO, G_LOCK_HI; lia|]. cbv beta. right. left. unfold G_LOCK. lia. }
  split; [exact INIT|].
  split.
  { unfold RSt. exists [], [], (nm0 OUT). assert (E0 : Tfx 0 = 0) by reflexivity. cbn [length].
    rewrite E0, Z.add_0_r.
    split; [reflexivity|]. split; [exact HRES|]. split; [intros ext; reflexivity|].
    split; [intros _ ext; reflexivity|].
    split; [intros rest Hr; rewrite app_nil_l; exact (HROOM rest Hr)|].
    split; [reflexivity|]. split; [intros _; unfold er, relay_finish_cap; apply p3c_eer_cap|].
    split; [reflexivity|]. split.
    - intros HC. destruct HOUT as [(C0 & _) | (_ & _ & HIN & _)]; [lia|].
      exact (sptr_of_spec L0 A0 OUT CAP (HND L0 A0 mem0 md0 HMR) HIN).
    - intros q m Hq _ _ _. exact (sptr_of_spec L0 A0 q m (HND L0 A0 mem0 md0 HMR) Hq). }
  split; [exact RA'|].
  split; [apply (fi_tr_cells _ mem0 m' _ _ CTU MU' WM'); intros j Hj; cbn in Hj; unfold Wh; fi_out|].
  split; [exact (fi_rw_back _ _ _ _ MRl GLm)|].
  split; [apply (fi_tr_cells _ mem0 m' _ _ CNS MU' WM'); intros j Hj; cbn in Hj; unfold Wh, G_NSRC; fi_out|].
  split; [apply (fi_tr_cells _ mem0 m' _ _ CSR MU' WM'); intros j Hj; cbn in Hj; unfold Wh, G_SRC; fi_out|].
  split; [apply (fi_tr_cells _ mem0 m' _ _ CLS MU' WM'); intros j Hj; cbn in Hj; unfold Wh, G_LISTEN; fi_out|].
  split; [rewrite fi_br0; apply (fi_tr_cells _ mem0 m' _ _ CBR MU' WM'); intros j Hj; cbn in Hj;
          unfold Wh, G_BROKEN; fi_out|].
  split; [apply (fi_tr_cells _ mem0 m' _ _ CDD MU' WM'); intros j Hj; cbn in Hj; unfold Wh, G_DEAD; fi_out|].
  split; [rewrite fi_ei0; apply (fi_tr_cells _ mem0 m' _ _ CEI MU' WM'); intros j Hj; cbn in Hj;
          unfold Wh, G_EINTR; fi_out|].
  split; [apply (fi_tr_cells _ mem0 m' _ _ COV MU' WM'); intros j Hj; cbn in Hj; unfold Wh, G_OUTV; fi_out|].
  split.
  { destruct CER as [ev CE]. exists ev. apply (fi_tr_cells _ mem0 m' _ _ CE MU' WM'). intros j Hj. cbn in Hj.
    unfold Wh. fi_out. }
  split; [exact (fi_rw_back _ _ _ _ MRl FRm)|].
  split.
  { intros HC. destruct HTAB as [(C0 & _) | (C16 & HG & FG & GO & GN & TL & TR)]; [lia|].
    split; [|exact HG]. split; [exact TL|]. rewrite SEGS in TR |- *.
    apply (fi_tr_cells _ mem0 m' _ _ TR MU' WM'). intros j Hj. cbn in Hj.
    unfold SRC_TABLE, SRC_ENTRY in FG.
    destruct (fi_fresh_low G 896 j FG ltac:(lia)) as [Hb Hi]. exact (OUTB _ Hb Hi). }
  split.
  { intros q m. rewrite fi_lv0. split.
    - intros Hq. destruct (Z.eq_dec q OUT) as [E|E].
      + right. right. split; [reflexivity|]. subst q.
        destruct HOUT as [(C0 & O0 & _) | (CP & _ & HIN & _)].
        * exfalso. apply fi_blocks_in in Hq as (p & Ep & Hp).
          destruct (mr_blocks_range Bm _ (aa_laws API) L0 A0 mem0 md0 p m HMR Hp) as [Q1 _]. lia.
        * split; [exact CP|]. split; [reflexivity|].
          exact (fi_blk_eq L0 A0 OUT m CAP (fi_nodup _ (HND L0 A0 mem0 md0 HMR)) Hq HIN).
      + left. split; [exact Hq|]. split; [exact E | intros []].
    - intros [(Hq & _) | [(LV & _) | (_ & CP & -> & ->)]]; [exact Hq | discriminate LV |].
      destruct HOUT as [(C0 & _)|(_ & _ & HIN & _)]; [lia | exact HIN]. }
  split; [intros _; repeat split|].
  split; [rewrite fi_lv0; discriminate|].
  destruct HOUT as [H|(H1 & H2 & H3 & H4 & H5 & H6 & H7)]; [left; exact H | right].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [| split; [exact H6 | exact H7]].
  apply (fi_tr_bytes _ mem0 m' _ _ H5 MU'). intros j Hj. rewrite length_app in Hj.
  destruct (fi_fresh_low OUT CAP j H4 ltac:(lia)) as [Hb Hi]. exact (OUTB _ Hb Hi).
Qed.

Lemma fi_CI_tr0 : forall L1 A1 m1 md1 rr nout1 cap1 out1 O1 junk1 P T1 Eo tab m',
  CI L1 A1 m1 md1 rr nout1 cap1 out1 O1 junk1 P T1 Eo tab ->
  munch [] m1 m' -> wmono rsegs m1 m' -> ro_agree rsegs m' ->
  CI L1 A1 m' md1 rr nout1 cap1 out1 O1 junk1 P T1 Eo tab.
Proof using AX SEGS.
  intros L1 A1 m1 md1 rr nout1 cap1 out1 O1 junk1 P T1 Eo tab m' H MU WM RA'.
  destruct H as (RP & IN & RS & RA1 & CTU1 & CLK1 & CNS1 & CSR1 & CLS1 & CBR1 & CDD1 & CEI1 & COV1 & CER1 &
    FR1 & TAB1 & BLK1 & LVF1 & LVT1 & HO1).
  split.
  { eapply (fi_kA Bm API AX) with (W := []); [exact SEGS | exact RP | exact MU | rewrite SEGS; exact WM |].
    intros a _. left. exact I. }
  split; [exact IN|]. split; [exact RS|]. split; [exact RA'|].
  split; [exact (fi_rw0 _ _ _ _ CTU1 MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ CLK1 MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ CNS1 MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ CSR1 MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ CLS1 MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ CBR1 MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ CDD1 MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ CEI1 MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ COV1 MU WM)|].
  split; [destruct CER1 as [ev E]; exists ev; exact (fi_rw0 _ _ _ _ E MU WM)|].
  split; [exact (fi_rw0 _ _ _ _ FR1 MU WM)|].
  split.
  { intros HC. destruct (TAB1 HC) as [[TL TR] HG]. split; [|exact HG]. split; [exact TL|].
    rewrite SEGS in TR |- *. exact (fi_rw0 _ _ _ _ TR MU WM). }
  split; [exact BLK1|]. split; [exact LVF1|]. split; [exact LVT1|].
  destruct HO1 as [H|(H1 & H2 & H3 & H4 & H5 & H6 & H7)]; [left; exact H | right].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [exact (fi_by0 _ _ _ _ H5 MU)|]. split; [exact H6 | exact H7].
Qed.

Lemma fi_full : Pfx (length es) = concat (map entry_blocks es) /\ Tfx (length es) = TOT /\
  Efx (length es) = entries_out es /\ Tab (length es) = map entry_cleared es.
Proof using. unfold Pfx, Tfx, Efx, Tab. rewrite firstn_all, skipn_all, app_nil_r. auto. Qed.

Lemma fi_s_chk : forall c, HeadSt c ->
  SR rsegs c (fun c' => ((0 < length es)%nat /\ LoopSt 0 c') \/ (length es = 0%nat /\ ExitSt c')).
Proof using AX HN4 SEGS.
  intros c (R1 & m1 & -> & HRL & HCI & HEST).
  pose proof HRL as (R2 & R3 & R4 & R8 & R9 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof HCI as (RP & _ & _ & RA1 & _ & _ & NS1 & _).
  pose proof RP as (M1 & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (Nat.eq_dec (length es) 0) as [E0|E0].
  - eapply fi_bridge; [exact RA1 | exact Hh | exact Hl | |].
    { unfold Regs6ss.mkR_of. rewrite R9. apply fi_chk0 with (C := C).
      apply fi_rw_norm; [exact RA1 | |].
      - rewrite E0 in NS1. exact NS1.
      - intros j Hj. cbn in Hj. apply fi_ro_glob. lia. }
    intros s0 R' m' HQ X MRl RS. destruct HQ as [a0' ->].
    destruct (fi_rsame m1 m' _ RA1 MRl eq_refl RS) as (MU & WM & RA').
    apply SR_ret. right. split; [exact E0|].
    exists L0, A0, R', m', md0, nout, cap, out, O, junk. split; [reflexivity|].
    split; [unfold RL; repeat split; rgx X|].
    rewrite E0. exact (fi_CI_tr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCI MU WM RA').
  - eapply fi_bridge; [exact RA1 | exact Hh | exact Hl | |].
    { unfold Regs6ss.mkR_of. rewrite R9. eapply fi_chk1.
      - apply fi_rw_norm; [exact RA1 | exact NS1 |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia.
      - lia. }
    intros s0 R' m' HQ X MRl RS. destruct HQ as [a0' ->].
    destruct (fi_rsame m1 m' _ RA1 MRl eq_refl RS) as (MU & WM & RA').
    apply SR_ret. left. split; [lia|].
    exists L0, A0, R', m', md0, nout, cap, out, O, junk. split; [reflexivity|].
    split; [unfold RL; repeat split; rgx X|].
    split; [rgx X|]. split; [rgx X|].
    split; [exact (fi_CI_tr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCI MU WM RA')|].
    exact (fi_est_tr0 _ _ _ _ _ HEST MU).
Qed.

Definition We : list (Z * Z) := [(SP - 96, SP); (202936, 202940); (136736, 136744); (203004, 203008)].

Lemma fi_We_ok : IvOk We.
Proof using IMGL IMGR O PRE SEGS es junk.
  destruct fi_pre_facts as (HCE & _).
  constructor; [left; cbn; lia|].
  constructor; [right; intros x Hx; cbn in Hx; exact (proj1 (IMGR x ltac:(unfold G_RELAY_LO, G_LOCK_HI; lia)))|].
  constructor; [right; intros x Hx; cbn in Hx; exact (proj1 (IMGL x ltac:(unfold G_LISTEN, G_CLIENT; lia)))|].
  constructor; [right; intros x Hx; cbn in Hx; exact (proj1 (IMGR x ltac:(unfold G_RELAY_LO, G_LOCK_HI; lia)))|].
  constructor.
Qed.

Lemma fi_s_exit : forall c, ExitSt c -> SR rsegs c Final.
Proof using AX HERR HOUT HTAB IMGE IMGL IMGR PRE SEGS SPU.
  intros c (L1 & A1 & R1 & m1 & md1 & nout1 & cap1 & out1 & O1 & junk1 & -> & HRL & HCI).
  pose proof HRL as (R2 & R3 & R4 & R8 & R9 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  destruct fi_full as (EP & ET & EE & ETb). rewrite EP, ET, EE, ETb in HCI.
  destruct HCI as (RP & IN & RS & RA1 & CTU1 & CLK1 & CNS1 & CSR1 & CLS1 & CBR1 & CDD1 & CEI1 & COV1 & CER1 &
    FR1 & TAB1 & BLK1 & LVF1 & LVT1 & HO1).
  destruct RS as (tp & qs & o & RNq & RT1 & _ & _ & _ & RT3 & RT4 & RT5 & RT6 & _).
  unfold er in RT3, RT4, RT5. rewrite skipn_all in RT3, RT4, RT5. cbn [entries_end_run fst snd] in RT3, RT4, RT5.
  rewrite app_nil_r in RT3. rewrite RT3 in RT1, RNq.
  pose proof RP as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FM1 & BY1 & SC1).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct fi_pre_facts as (HCE & HAL & H63 & HWS & HTP & HRA & HERRW & _ & _ & HMR).
  pose proof YM05.alloc_ceiling_val as AC. pose proof fi_err_low as EL. pose proof fi_We_ok as WOK.
  pose proof (bv_unsigned_in_range 64 (reg_get regs0 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (ST : stk rsegs m1 (SP - 8464) SP).
  { split; [lia|]. split; [lia|]. intros a Ha. apply fi_wr_hi; [lia|]. rewrite <- SEGS. apply SC1.
    left. change (spZ regs0) with SP. rewrite fi_K. lia. }
  eapply fi_bridge; [exact RA1 | exact Hh | exact Hl | |].
  { unfold Regs6ss.mkR_of. rewrite R2, R8, R9.
    eapply (fi_exit SPU) with (lo := SP - 8464) (sp0 := reg_get regs0 2).
    - apply fi_stk_norm; [exact ST | lia].
    - lia.
    - lia.
    - apply mem_inv_normalize.
    - apply fi_rw_norm; [exact RA1 | exact FR1 |]. intros j Hj. cbn in Hj. apply fi_ro_hi. lia.
    - apply fi_rw_norm; [exact RA1 | exact CNS1 |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia.
    - apply fi_rw_norm; [exact RA1 | exact CLS1 |]. intros j Hj. cbn in Hj. apply fi_ro_lis. lia.
    - apply fi_rw_norm; [exact RA1 | exact CLK1 |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia. }
  intros s0 R' m' HQ X MRl RS'.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mn & -> & MU
    & WM & MI & STn & NSn & LSn & LKn).
  destruct (fi_back m1 mn m' _ RA1 MRl RS' MU WM) as (MU' & WM' & RA').
  change [(SP - 96, SP); (202936, 202940); (136736, 136744); (203004, 203008)] with We in MU'.
  assert (OUTB : forall a, 0 <= a < YM05.alloc_ceiling -> ~ in_img Bm a -> outside We a)
    by (intros a Ha Hi; exact (fi_lowout a We Ha Hi WOK)).
  assert (X2 : reg_get R' 2 = reg_get regs0 2) by rgx X.
  assert (X3 : reg_get R' 3 = reg_get regs0 3) by rgx X.
  assert (X4 : reg_get R' 4 = reg_get regs0 4) by rgx X.
  assert (X8 : reg_get R' 8 = reg_get regs0 8) by rgx X.
  assert (X9 : reg_get R' 9 = reg_get regs0 9) by rgx X.
  assert (X18 : reg_get R' 18 = reg_get regs0 18) by rgx X.
  assert (X19 : reg_get R' 19 = reg_get regs0 19) by rgx X.
  assert (X20 : reg_get R' 20 = reg_get regs0 20) by rgx X.
  assert (X21 : reg_get R' 21 = reg_get regs0 21) by rgx X.
  assert (X22 : reg_get R' 22 = reg_get regs0 22) by rgx X.
  assert (X23 : reg_get R' 23 = reg_get regs0 23) by rgx X.
  assert (X24 : reg_get R' 24 = reg_get regs0 24) by rgx X.
  assert (X25 : reg_get R' 25 = reg_get regs0 25) by rgx X.
  assert (X26 : reg_get R' 26 = reg_get regs0 26) by rgx X.
  assert (X27 : reg_get R' 27 = reg_get regs0 27) by rgx X.
  assert (XP : regs_preserved regs0 R').
  { intros r Hr. assert (E : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
      r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
    destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      match goal with H : reg_get R' _ = _ |- _ => exact H end. }
  apply SR_ret. unfold Final.
  exists L1, A1, R', m', md1, (bv_unsigned out1), (bv_unsigned cap1), junk1.
  split.
  { rewrite (ret_pc_of_ok _ HRA). reflexivity. }
  split.
  { apply (fi_rp_regs Bm API) with (R0 := regs0); [|exact XP].
    eapply (fi_kA Bm API AX) with (W := We); [exact SEGS | exact RP | exact MU' | rewrite SEGS; exact WM' |].
    intros a Ha. destruct (fi_outside_dec We a) as [Ho|Ho]; [left; exact Ho|right].
    assert (D : SP - 96 <= a < SP \/ 202936 <= a < 202940 \/ 136736 <= a < 136744 \/ 203004 <= a < 203008)
      by (unfold We in Ho; cbn [outside] in Ho; lia).
    change (spZ regs0) with SP. rewrite fi_K.
    destruct D as [D|[D|[D|D]]]; [left; lia | right .. ].
    - split; [apply IMGR; unfold G_RELAY_LO, G_LOCK_HI; lia|]. cbv beta. right. right. left. unfold G_NSRC. lia.
    - split; [apply IMGL; unfold G_LISTEN, G_CLIENT; lia|]. cbv beta. right. right. right. left.
      unfold G_LISTEN, G_CLIENT. lia.
    - split; [apply IMGR; unfold G_RELAY_LO, G_LOCK_HI; lia|]. cbv beta. right. left. unfold G_LOCK. lia. }
  split; [exact IN|].
  split.
  { exists qs. split; [lia|]. split; [exact RT1|]. intros LV. rewrite <- RT5. apply RT6.
    destruct (LVT1 LV) as (E1 & _).
    destruct HO1 as [(C0 & O0 & N0 & _)|(H1 & _)]; [|lia].
    exfalso. pose proof (fi_live_nz cl br dd TOT LV) as NZ. pose proof (fi_et_nonneg es) as TN.
    pose proof (bv_unsigned_in_range 64 nout) as RN0. lia. }
  split; [exact RA'|].
  split; [apply (fi_tr_cells _ m1 m' _ _ CTU1 MU' WM'); intros j Hj; cbn in Hj; unfold We; fi_out|].
  split; [exact (fi_rw_back _ _ _ _ MRl LKn)|].
  split; [exact (fi_rw_back _ _ _ _ MRl NSn)|].
  split; [apply (fi_tr_cells _ m1 m' _ _ CSR1 MU' WM'); intros j Hj; cbn in Hj; unfold We; fi_out|].
  split; [exact (fi_rw_back _ _ _ _ MRl LSn)|].
  split.
  { intros HC. destruct (TAB1 HC) as [[TL TR] HG]. split; [|exact HG]. split; [exact TL|].
    rewrite SEGS in TR |- *. apply (fi_tr_cells _ m1 m' _ _ TR MU' WM'). intros j Hj. cbn in Hj.
    destruct HTAB as [(C0 & _) | (C16 & HG0 & FG & _)]; [lia|]. unfold SRC_TABLE, SRC_ENTRY in FG.
    destruct (fi_fresh_low G 896 j FG ltac:(lia)) as [Hb Hi]. exact (OUTB _ Hb Hi). }
  split; [unfold brT in CBR1; apply (fi_tr_cells _ m1 m' _ _ CBR1 MU' WM'); intros j Hj; cbn in Hj; unfold We;
          fi_out|].
  split; [apply (fi_tr_cells _ m1 m' _ _ CDD1 MU' WM'); intros j Hj; cbn in Hj; unfold We; fi_out|].
  split; [unfold eiT in CEI1; apply (fi_tr_cells _ m1 m' _ _ CEI1 MU' WM'); intros j Hj; cbn in Hj; unfold We;
          fi_out|].
  split; [destruct CER1 as [ev E]; exists ev; apply (fi_tr_cells _ m1 m' _ _ E MU' WM'); intros j Hj; cbn in Hj;
          unfold We; fi_out|].
  split; [exact BLK1|].
  split.
  { intros LV. destruct (LVF1 LV) as (-> & -> & -> & -> & ->).
    apply (fi_tr_cells _ m1 m' _ _ COV1 MU' WM'). intros j Hj. cbn in Hj. unfold We. fi_out. }
  intros LV. destruct (LVT1 LV) as (E1 & FB & DJ & EO).
  destruct HO1 as [(C0 & O0 & N0 & _)|(H1 & H2 & H3 & H4 & H5 & H6 & H7)].
  { exfalso. pose proof (fi_live_nz cl br dd TOT LV) as NZ. pose proof (fi_et_nonneg es) as TN.
    pose proof (bv_unsigned_in_range 64 nout) as RN. lia. }
  split; [lia|]. split; [exact (RT4 LV)|]. split; [exact FB|]. split; [exact DJ|].
  split.
  { assert (LEN : Z.of_nat (length (O ++ entries_out es ++ junk1)) = bv_unsigned cap1)
      by (rewrite app_assoc, <- EO, length_app; lia).
    rewrite EO, <- app_assoc in H5. apply (fi_tr_bytes _ m1 m' _ _ H5 MU'). intros j Hj.
    destruct (fi_fresh_low _ _ j H4 ltac:(lia)) as [Hb Hi]. exact (OUTB _ Hb Hi). }
  split; [lia|].
  rewrite <- E1, !Z_to_bv_bv_unsigned.
  apply (fi_tr_cells _ m1 m' _ _ COV1 MU' WM'). intros j Hj. cbn in Hj. unfold We. fi_out.
Qed.

(* The loop body: entry i of the table. *)
Definition fi_e0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].

Lemma fi_nd_app : forall {X : Type} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof using.
  intros X l1. induction l1 as [|y l1 IH]; intros l2 x H Hx Hy; [destruct Hy|].
  apply List.NoDup_cons_iff in H as [Hn Hd]. destruct Hy as [<-|Hy].
  - apply Hn. apply in_or_app. right. exact Hx.
  - exact (IH l2 x Hd Hx Hy).
Qed.

Lemma fi_nd_app2 : forall {X : Type} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof using. intros X l1 l2 x H H1 H2. exact (fi_nd_app l1 l2 x H H2 H1). Qed.

Lemma fi_in_cat : forall l e q, In e l -> In q (entry_blocks e) -> In q (concat (map entry_blocks l)).
Proof using.
  induction l as [|e0 l IH]; intros e q He Hq; [destruct He|]. cbn [map concat].
  apply in_or_app. destruct He as [<-|He]; [left; exact Hq | right; exact (IH e q He Hq)].
Qed.

Lemma fi_len_fx : forall {X : Type} (l : list X) i, (i <= length l)%nat -> length (firstn i l) = i.
Proof using Bm O es junk.
  intros X l. induction l as [|x l IH]; intros [|i] H; cbn [length firstn] in *; try lia.
  f_equal. apply IH. lia.
Qed.

Lemma fi_es_split : forall i, (i < length es)%nat -> es = firstn i es ++ nth i es fi_e0 :: skipn (S i) es.
Proof using. intros i Hi. rewrite <- (fi_skipn_S es i fi_e0 Hi). symmetry. apply firstn_skipn. Qed.

Lemma fi_eok_i : forall i, (i < length es)%nat ->
  Forall (entry_ok Bm L0 A0 mem0) (firstn i es) /\ entry_ok Bm L0 A0 mem0 (nth i es fi_e0) /\
  Forall (entry_ok Bm L0 A0 mem0) (skipn (S i) es).
Proof using HEOK.
  intros i Hi. pose proof HEOK as H. rewrite (fi_es_split i Hi) in H.
  apply Forall_app in H as [H1 H2]. apply Forall_cons_iff in H2 as [H2 H3]. auto.
Qed.

Lemma fi_cat_split : forall i, (i < length es)%nat ->
  concat (map entry_blocks es) =
  Pfx i ++ entry_blocks (nth i es fi_e0) ++ concat (map entry_blocks (skipn (S i) es)).
Proof using. intros i Hi. unfold Pfx. rewrite (fi_es_split i Hi) at 1. rewrite fi_eb_app. reflexivity. Qed.

Lemma fi_ND : List.NoDup (concat (map entry_blocks es)).
Proof using HDJ. destruct HDJ as [N _]. exact (fi_nodup _ N). Qed.

Lemma fi_eb_fresh : forall i q, (i < length es)%nat -> In q (entry_blocks (nth i es fi_e0)) ->
  ~ In q (Pfx i) /\ ~ In q (concat (map entry_blocks (skipn (S i) es))) /\ q <> OUT /\
  In q (concat (map entry_blocks es)).
Proof using HDJ.
  intros i q Hi Hq. pose proof fi_ND as N. rewrite (fi_cat_split i Hi) in N.
  assert (HC : In q (concat (map entry_blocks es))).
  { rewrite (fi_cat_split i Hi). apply in_or_app. right. apply in_or_app. left. exact Hq. }
  split; [apply (fi_nd_app _ _ q N); apply in_or_app; left; exact Hq|].
  split; [exact (fi_nd_app2 _ _ q (List.NoDup_app_remove_l _ _ N) Hq)|].
  split; [|exact HC]. destruct HDJ as [_ NO]. intros ->. exact (NO HC).
Qed.

Lemma fi_eb_nd : forall i, (i < length es)%nat -> List.NoDup (entry_blocks (nth i es fi_e0)).
Proof using HDJ.
  intros i Hi. pose proof fi_ND as N. rewrite (fi_cat_split i Hi) in N.
  exact (List.NoDup_app_remove_r _ _ (List.NoDup_app_remove_l _ _ N)).
Qed.

Lemma fi_htab : forall i, (i < length es)%nat ->
  C = 16 /\ In (G, SRC_TABLE) (blocks L0 A0) /\ fresh_block Bm G SRC_TABLE /\ G <> OUT /\
  ~ In G (concat (map entry_blocks es)) /\ table_at Bm mem0 G es tail.
Proof using HTAB O junk.
  intros i Hi. destruct HTAB as [(_ & _ & E0) | H]; [|exact H].
  exfalso. rewrite E0 in Hi. cbn in Hi. lia.
Qed.

Lemma fi_tab_split : forall i, (i < length es)%nat ->
  Tab i = map entry_cleared (firstn i es) ++ nth i es fi_e0 :: skipn (S i) es /\
  Tab (S i) = map entry_cleared (firstn i es) ++ entry_cleared (nth i es fi_e0) :: skipn (S i) es /\
  length (map entry_cleared (firstn i es)) = i /\
  Forall fi_pads (map entry_cleared (firstn i es)) /\ fi_pads (nth i es fi_e0) /\
  Pfx (S i) = Pfx i ++ entry_blocks (nth i es fi_e0) /\
  Tfx (S i) = Tfx i + keys_total (re_keys (nth i es fi_e0)) /\
  Efx (S i) = Efx i ++ keys_out (re_keys (nth i es fi_e0)).
Proof using HEOK O junk.
  intros i Hi. destruct (fi_eok_i i Hi) as (E1 & E2 & _).
  unfold Tab, Pfx, Tfx, Efx. rewrite (fi_skipn_S es i fi_e0 Hi), (fi_firstn_S es i fi_e0 Hi).
  split; [reflexivity|].
  split; [rewrite map_app, <- app_assoc; reflexivity|].
  split; [rewrite length_map; apply fi_len_fx; lia|].
  split.
  { apply Forall_map. eapply Forall_impl; [|exact E1]. intros x (_ & _ & P1 & P2 & _).
    split; [exact P1 | exact P2]. }
  split; [destruct E2 as (_ & _ & P1 & P2 & _); split; [exact P1 | exact P2]|].
  split; [rewrite fi_eb_app; cbn [map concat]; rewrite app_nil_r; reflexivity|].
  split; [rewrite fi_et_app, fi_et_one; reflexivity|].
  rewrite fi_eo_app, fi_eo_one. reflexivity.
Qed.

Lemma fi_tab_len : forall i, length (Tab i) = length es.
Proof using.
  intros i. unfold Tab. rewrite length_app, length_map.
  rewrite <- (firstn_skipn i es) at 3. rewrite length_app. reflexivity.
Qed.

Lemma fi_RL_pres : forall R R', regs_preserved R R' -> RL R ->
  RL R' /\ reg_get R' 18 = reg_get R 18 /\ reg_get R' 19 = reg_get R 19.
Proof using Bm O es junk.
  intros R R' P (R2 & R3 & R4 & R8 & R9 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  unfold RL. repeat split.
  - rewrite <- R2. exact (P 2 ltac:(unfold callee_saved; lia)).
  - rewrite <- R3. exact (P 3 ltac:(unfold callee_saved; lia)).
  - rewrite <- R4. exact (P 4 ltac:(unfold callee_saved; lia)).
  - rewrite <- R8. exact (P 8 ltac:(unfold callee_saved; lia)).
  - rewrite <- R9. exact (P 9 ltac:(unfold callee_saved; lia)).
  - rewrite <- R20. exact (P 20 ltac:(unfold callee_saved; lia)).
  - rewrite <- R21. exact (P 21 ltac:(unfold callee_saved; lia)).
  - rewrite <- R22. exact (P 22 ltac:(unfold callee_saved; lia)).
  - rewrite <- R23. exact (P 23 ltac:(unfold callee_saved; lia)).
  - rewrite <- R24. exact (P 24 ltac:(unfold callee_saved; lia)).
  - rewrite <- R25. exact (P 25 ltac:(unfold callee_saved; lia)).
  - rewrite <- R26. exact (P 26 ltac:(unfold callee_saved; lia)).
  - rewrite <- R27. exact (P 27 ltac:(unfold callee_saved; lia)).
  - exact (P 18 ltac:(unfold callee_saved; lia)).
  - exact (P 19 ltac:(unfold callee_saved; lia)).
Qed.

Lemma fi_spR : forall R, RL R -> spZ R = SP - 48.
Proof using O PRE SEGS es junk.
  intros R HR. destruct fi_pre_facts as (HCE & _ & H63 & _). pose proof YM05.alloc_ceiling_lt as ACL.
  pose proof YM05.alloc_ceiling_val as AC.
  pose proof (bv_unsigned_in_range 64 (reg_get regs0 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  change (bv_unsigned (reg_get R 2) = SP - 48). rewrite (proj1 HR), unsigned_lit; lia.
Qed.

Lemma fi_cpre : forall K E F L1 A1 m1 md1 R,
  relay_post Bm API RELAY_FINISH_K E F L0 A0 regs0 mem0 md0 L1 A1 regs0 m1 md1 ->
  st_init_done A1 = true -> RL R -> YK0s.ret_ok (reg_get R 1) -> 0 <= K <= 8416 ->
  call_pre_k Bm (aa_MR API) K L1 A1 R m1 md1.
Proof using O PRE SEGS es junk.
  intros K E F L1 A1 m1 md1 R RP INI HRL HRA HK.
  destruct RP as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  destruct fi_pre_facts as (HCE & HAL & H63 & _ & HTP & _).
  pose proof YM05.alloc_ceiling_val as AC.
  pose proof (fi_spR R HRL) as SPR. pose proof (proj1 (proj2 (proj2 HRL))) as R4.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact HRA|].
  rewrite SPR.
  split; [replace (SP - 48) with (SP + (-3) * 16) by lia; rewrite Z.mod_add by lia; exact HAL|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply SC1; left; change (spZ regs0) with SP; rewrite fi_K; lia|].
  split; [change (reg_get R 4 = Z_to_bv 64 (ms_tp Bm)); rewrite R4; exact HTP|].
  split; [intros a Ha; apply SC1; right; exact Ha|].
  intros H. rewrite INI in H. discriminate H.
Qed.

Lemma fi_kst_tr2 : forall L1 A1 m1 L2 A2 m2 e L A m,
  entry_ok Bm L A m e -> fi_kst L1 A1 m1 e ->
  (forall q k, 0 < k -> In (q, k) (blocks L1 A1) ->
     In q ((if re_hp e =? 0 then [] else [re_hp e]) ++ map key_addr (re_keys e)) ->
     In (q, k) (blocks L2 A2) /\ (forall j, 0 <= j < k -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j))) ->
  fi_kst L2 A2 m2 e.
Proof using O es junk.
  intros L1 A1 m1 L2 A2 m2 e L A m EOK [KH KS] TR.
  destruct EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPK & _ & _ & KF).
  split.
  - intros Hh. destruct (KH Hh) as [IN BY].
    destruct HPK as [(H0 & _) | (_ & _ & K8 & K8' & _)]; [contradiction|].
    assert (HB : In (re_hp e) ((if re_hp e =? 0 then [] else [re_hp e]) ++ map key_addr (re_keys e))).
    { apply in_or_app. left. destruct (Z.eqb_spec (re_hp e) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (TR (re_hp e) (re_kh e) ltac:(lia) IN HB) as [IN2 KEEP].
    split; [exact IN2|].
    apply (fi_bytes_blk m1 m2 (re_hp e) (re_kh e)); [lia | | exact KEEP | exact BY].
    rewrite fi_key_ptrs_len. unfold re_nheld in K8. lia.
  - rewrite Forall_forall in KS, KF |- *. intros k Hk. destruct (KS k Hk) as [IN BY].
    destruct (KF k Hk) as (_ & _ & _ & _ & HL & _).
    assert (HB : In (key_addr k) ((if re_hp e =? 0 then [] else [re_hp e]) ++ map key_addr (re_keys e)))
      by (apply in_or_app; right; apply in_map; exact Hk).
    destruct (TR (key_addr k) (Z.of_nat (length (key_text k)) + 1) ltac:(lia) IN HB) as [IN2 KEEP].
    split; [exact IN2|].
    apply (fi_bytes_blk m1 m2 (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [lia | | exact KEEP | exact BY].
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma fi_CI_free : forall i L1 A1 m1 md1 rr1 rr2 nout1 cap1 out1 O1 junk1 R L2 A2 R2 m2 md2 p,
  (i < length es)%nat ->
  CI L1 A1 m1 md1 rr1 nout1 cap1 out1 O1 junk1 (Pfx i) (Tfx i) (Efx i) (Tab i) ->
  Forall (fi_est L1 A1 m1) (skipn i es) ->
  0 < re_cap (nth i es fi_e0) ->
  ptr_addr L1 p = re_buf (nth i es fi_e0) -> In (p, re_cap (nth i es fi_e0)) (user_blocks A1) ->
  RL R ->
  call_post Bm (aa_MR API) L1 A1 R m1 md1
    (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + re_cap (nth i es fi_e0)) L2 A2 R2 m2 md2 ->
  (exists b1 b2, blocks L1 A1 = b1 ++ (ptr_addr L1 p, re_cap (nth i es fi_e0)) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
  blocks_kept Bm L1 A1 m1 m2 (fun a => a = ptr_addr L1 p) ->
  ro_agree (ms_segs Bm) m2 ->
  (forall q k, In (q, k) (user_blocks A1) -> q <> p -> In (q, k) (user_blocks A2)) ->
  (st_init_done A1 = true -> st_init_done A2 = true) ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  RSt L2 A2 rr2 (bv_unsigned cap1) (bv_unsigned out1) (Pfx i ++ bufl (nth i es fi_e0)) ->
  CI L2 A2 m2 md2 rr2 nout1 cap1 out1 O1 junk1 (Pfx i ++ bufl (nth i es fi_e0)) (Tfx i) (Efx i) (Tab i) /\
  fi_kst L2 A2 m2 (nth i es fi_e0) /\ Forall (fi_est L2 A2 m2) (skipn (S i) es).
Proof using AX CTXO HDJ HEOK HERR HND HTAB IMGE IMGL IMGR PRE SEGS.
  intros i L1 A1 m1 md1 rr1 rr2 nout1 cap1 out1 O1 junk1 R L2 A2 R2 m2 md2 p Hi HCI HEST Hc Hp HpA HRL CP BL BK RA2
    SURV INI LNR RES.
  destruct (fi_eok_i i Hi) as (_ & EOK & EOK3).
  rewrite (fi_skipn_S es i fi_e0 Hi) in HEST. apply Forall_cons_iff in HEST as [ESTe EST3].
  assert (HBe : In (re_buf (nth i es fi_e0)) (entry_blocks (nth i es fi_e0))).
  { unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap (nth i es fi_e0)) 0) ltac:(lia)).
    apply in_or_app. left. left. reflexivity. }
  destruct (fi_eb_fresh i _ Hi HBe) as (NBP & NBS & NBO & NBC).
  pose proof (fi_eb_nd i Hi) as NDe.
  destruct (fi_htab i Hi) as (_ & _ & _ & _ & GN & _).
  set (e := nth i es fi_e0) in *.
  unfold entry_blocks in NDe. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)) in NDe. cbn [app] in NDe.
  apply List.NoDup_cons_iff in NDe as [NBK _].
  rewrite Hp in CP, BL, BK.
  destruct HCI as (RP & IN & RS & RA1 & CTU1 & CLK1 & CNS1 & CSR1 & CLS1 & CBR1 & CDD1 & CEI1 & COV1 & CER1 &
    FR1 & TAB1 & BLK1 & LVF1 & LVT1 & HO1).
  pose proof RP as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FM1 & BY1 & SC1).
  pose proof CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FRc & BYc & SCc).
  destruct fi_pre_facts as (HCE & HAL & H63 & HWS & HTP & HRA & HERRW & _ & _ & HMR).
  pose proof YM05.alloc_ceiling_val as AC. pose proof fi_err_low as EL.
  pose proof (bv_unsigned_in_range 64 (reg_get regs0 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (fi_spR R HRL) as SPR.
  pose proof EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BUF & _).
  destruct BUF as [(C0 & _) | (_ & BIN0 & FB & _)]; [lia|].
  assert (BNI : forall a, re_buf e <= a < re_buf e + re_cap e -> ~ in_img Bm a /\ a < YM05.alloc_ceiling).
  { destruct FB as (F1 & F2 & F3). intros a Ha. split; [|lia].
    replace a with (re_buf e + (a - re_buf e)) by lia. apply F3. lia. }
  assert (BIN1 : In (re_buf e, re_cap e) (blocks L1 A1)).
  { apply fi_blocks_in. exists p. split; [exact Hp | exact HpA]. }
  assert (BNO1 : re_buf e <> bv_unsigned out1).
  { destruct (lvT (Tfx i)) eqn:LV.
    - destruct (LVT1 eq_refl) as (_ & _ & DJ & _). exact (DJ _ _ BIN0 NBO NBP Hc).
    - destruct (LVF1 eq_refl) as (_ & _ & -> & _). exact NBO. }
  assert (FRP : relay_post Bm API ALLOC_STACK (fun a => re_buf e <= a < re_buf e + re_cap e)
                  (fun q => q = re_buf e) L1 A1 R m1 md1 L2 A2 R2 m2 md2).
  { pose proof (fi_free_rp Bm API AX CTXO L1 A1 R m1 md1 L2 A2 R2 m2 md2 p (re_cap e) W1 HpA Hc M1) as H.
    rewrite Hp in H. exact (H CP SURV LNR). }
  assert (RP2 : relay_post Bm API RELAY_FINISH_K Efin Ffin L0 A0 regs0 mem0 md0 L2 A2 regs0 m2 md2).
  { apply (fi_comp Bm API _ _ _ _ _ _ _ _ _ _ _ _ ALLOC_STACK R _ _ _ _ _ _ _ RP FRP).
    - intros a Ha. change (spZ regs0) with SP in Ha. rewrite fi_K in Ha. lia.
    - intros a Ha. unfold scratch_k in Ha |- *. rewrite SPR in Ha. change (spZ regs0) with SP. rewrite fi_K.
      unfold ALLOC_STACK in Ha. lia.
    - intros a Ha _ Hb. unfold scratch_k in Ha. change (spZ regs0) with SP in Ha. rewrite fi_K in Ha.
      destruct (BNI a Hb) as [N1 N2]. destruct Ha as [Ha|Ha]; [lia | exact (N1 (IMGE a Ha))].
    - intros p' n Hn H0 H1 NF E'. apply NF. right. rewrite E'. exact NBC.
    - intros a Ha _ _ Hb. destruct (BNI a Hb) as [N1 N2]. destruct Ha as [Ha|Ha]; [lia | contradiction].
    - intros p' n j H0 H1 NF Hj Hb. exfalso.
      pose proof (AD1 p' n H0 H1 NF) as EA.
      assert (IN1 : In (ptr_addr L0 p', n) (blocks L1 A1))
        by (apply fi_blocks_in; exists p'; split; [exact EA | exact H1]).
      assert (NE : ptr_addr L0 p' <> re_buf e) by (intros E'; apply NF; right; rewrite E'; exact NBC).
      destruct (fi_blk_disj Bm API L1 A1 m1 md1 _ _ _ _ M1 IN1 BIN1 NE) as [D|D]; lia. }
  assert (NDb : List.NoDup (map fst (blocks L1 A1))) by exact (fi_nodup _ (HND L1 A1 m1 md1 M1)).
  assert (KEEP : forall q k, In (q, k) (blocks L1 A1) -> q <> re_buf e ->
            In (q, k) (blocks L2 A2) /\
            (forall j, 0 <= j < k -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j)))
    by (intros q k Hq Hne; exact (fi_free_keep Bm SEGS L1 A1 m1 L2 A2 m2 (re_buf e) (re_cap e) q k BL BK Hq Hne)).
  assert (GLB : forall a, (G_RELAY_LO <= a < G_LOCK_HI \/ G_LISTEN <= a < G_CLIENT + 4 \/ SP - 48 <= a < SP) ->
            (img_plain Bm a \/ YM05.alloc_ceiling <= a < 2 ^ 64) /\ ~ (re_buf e <= a < re_buf e + re_cap e) /\
            ~ scratch Bm R a).
  { intros a Ha. unfold scratch. rewrite SPR. unfold ALLOC_STACK.
    destruct Ha as [Ha|[Ha|Ha]].
    - pose proof (IMGR a Ha) as Hi'. split; [left; exact Hi'|]. split.
      + intros Hb. destruct (BNI a Hb) as [N1 _]. exact (N1 (proj1 Hi')).
      + unfold G_RELAY_LO, G_LOCK_HI in Ha. lia.
    - pose proof (IMGL a Ha) as Hi'. split; [left; exact Hi'|]. split.
      + intros Hb. destruct (BNI a Hb) as [N1 _]. exact (N1 (proj1 Hi')).
      + unfold G_LISTEN, G_CLIENT in Ha. lia.
    - split; [right; lia|]. split; [intros Hb; destruct (BNI a Hb); lia | lia]. }
  split.
  { split; [exact RP2|].
    split; [exact (INI IN)|].
    split; [exact RES|].
    split; [rewrite SEGS in RA2; exact RA2|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact CTU1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_THREAD_UP, G_RELAY_LO, G_LOCK_HI; lia|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact CLK1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_LOCK, G_RELAY_LO, G_LOCK_HI; lia|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact CNS1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_NSRC, G_RELAY_LO, G_LOCK_HI; lia|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact CSR1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_SRC, G_RELAY_LO, G_LOCK_HI; lia|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact CLS1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_LISTEN, G_CLIENT; lia|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact CBR1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_BROKEN, G_RELAY_LO, G_LOCK_HI; lia|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact CDD1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_DEAD, G_RELAY_LO, G_LOCK_HI; lia|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact CEI1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_EINTR, G_RELAY_LO, G_LOCK_HI; lia|].
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact COV1];
            intros j Hj; cbn in Hj; apply GLB; unfold G_OUTV, G_RELAY_LO, G_LOCK_HI; lia|].
    split.
    { assert (HW : forall j, 0 <= j < 4 -> YP09.writable_at rsegs m2 (ERR + j))
        by (intros j Hj; rewrite <- SEGS; apply SCc; right; lia).
      destruct (fi_c4 m2 ERR ltac:(lia) ltac:(lia) HW) as [v Hv]. exists v. exact Hv. }
    split; [apply (fi_cp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ M1 CP); [|exact FR1];
            intros j Hj; cbn in Hj; apply GLB; lia|].
    split.
    { intros HC. destruct (TAB1 HC) as [[TL TR] HG1].
      assert (NG : G <> re_buf e) by (intros E'; apply GN; rewrite E'; exact NBC).
      destruct (KEEP G SRC_TABLE HG1 NG) as [HG2 KG].
      split; [|exact HG2]. split; [exact TL|]. rewrite SEGS in TR |- *.
      apply (fi_rw_blk m1 m2 G SRC_TABLE); [lia | cbn; unfold SRC_TABLE, SRC_ENTRY; lia | | exact TR].
      intros j Hj. split; [exact (KG j Hj)|].
      exact (proj1 (fi_blk Bm API L2 A2 m2 md2 G SRC_TABLE j M2 HG2 Hj)). }
    split.
    { assert (BUFL : bufl e = [re_buf e])
        by (unfold bufl; rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)); reflexivity).
      rewrite BUFL. intros q m. pose proof (fi_free_iff L1 A1 L2 A2 (re_buf e) (re_cap e) NDb BL q m) as FI.
      split.
      - intros H. apply FI in H as [H Hq]. apply BLK1 in H as [(H0 & H1 & H2) | [H3 | H4]].
        + left. split; [exact H0|]. split; [exact H1|]. intros Hin.
          apply in_app_or in Hin as [Hin|[Hin|[]]]; [exact (H2 Hin) | exact (Hq (eq_sym Hin))].
        + right. left. exact H3.
        + right. right. exact H4.
      - intros H. apply FI. destruct H as [(H0 & H1 & H2) | [(LV & -> & ->) | (LV & CP0 & -> & ->)]].
        + split.
          * apply BLK1. left. split; [exact H0|]. split; [exact H1|]. intros Hin. apply H2.
            apply in_or_app. left. exact Hin.
          * intros ->. apply H2. apply in_or_app. right. left. reflexivity.
        + split; [apply BLK1; right; left; auto|]. intros E'. exact (BNO1 (eq_sym E')).
        + split; [apply BLK1; right; right; auto|]. intros E'. exact (NBO (eq_sym E')). }
    split; [exact LVF1|].
    split.
    { intros LV. destruct (LVT1 LV) as (E1 & FB1 & DJ & EO).
      split; [exact E1|]. split; [exact FB1|]. split; [|exact EO].
      intros q m H0 H1 H2 Hm. apply (DJ q m H0 H1); [|exact Hm]. intros Hin. apply H2.
      apply in_or_app. left. exact Hin. }
    destruct HO1 as [H|(H1 & H2 & H3 & H4 & H5 & H6 & H7)]; [left; exact H | right].
    destruct (KEEP _ _ H3 (fun E' => BNO1 (eq_sym E'))) as [H3' K3].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3'|]. split; [exact H4|].
    split; [|split; [exact H6 | exact H7]].
    apply (fi_bytes_blk m1 m2 (bv_unsigned out1) (bv_unsigned cap1)); [lia | rewrite length_app; lia | exact K3 |
      exact H5]. }
  split.
  { destruct ESTe as [_ KS]. apply (fi_kst_tr2 L1 A1 m1 L2 A2 m2 e L0 A0 mem0 EOK KS).
    intros q k Hk Hq Hin. apply KEEP; [exact Hq|]. intros ->. exact (NBK Hin). }
  apply Forall_forall. intros e' He'. rewrite Forall_forall in EST3, EOK3.
  eapply fi_est_tr; [exact (EOK3 e' He') | exact (EST3 e' He') |].
  intros q k Hk Hq Hin. apply KEEP; [exact Hq|]. intros ->. apply NBS. exact (fi_in_cat _ _ _ He' Hin).
Qed.

Lemma fi_buf_rng : forall i, (i < length es)%nat -> 0 <= re_buf (nth i es fi_e0) < 2 ^ 64.
Proof using HEOK O junk.
  intros i Hi. destruct (fi_eok_i i Hi) as (_ & EOK & _). pose proof YM05.alloc_ceiling_lt as ACL.
  destruct EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BUF0 & _).
  destruct BUF0 as [(_ & B0 & _) | (CP0 & _ & (F1 & F2 & _) & _)].
  - rewrite B0. lia.
  - lia.
Qed.

Lemma fi_er_free : forall i c j o, (i < length es)%nat -> forall e, e = nth i es fi_e0 ->
  er (skipn i es) (NO + Tfx i) c j o = (bufree e ++ fst (fr i e c j o), snd (fr i e c j o)).
Proof using.
  intros i c j o Hi e ->. unfold er, fr, bufree. rewrite (fi_skipn_S es i fi_e0 Hi). cbn [entries_end_run]. cbv zeta.
  destruct (re_cap (nth i es fi_e0) =? 0).
  - cbn [app fst snd nret fold_right rets]. rewrite Nat.add_0_r. reflexivity.
  - cbn [app fst snd nret fold_right rets Nat.add]. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma fi_CI_rr : forall rr rr', (forall j o, rr j o = rr' j o) ->
  forall L1 A1 m1 md1 nout1 cap1 out1 O1 junk1 P T1 Eo tab,
  CI L1 A1 m1 md1 rr nout1 cap1 out1 O1 junk1 P T1 Eo tab -> CI L1 A1 m1 md1 rr' nout1 cap1 out1 O1 junk1 P T1 Eo tab.
Proof using.
  intros rr rr' E L1 A1 m1 md1 nout1 cap1 out1 O1 junk1 P T1 Eo tab (RP & IN & RS & REST).
  exact (conj RP (conj IN (conj (fi_RSt_ext _ _ _ _ _ _ _ E RS) REST))).
Qed.

Lemma fi_s_free : forall i c, (i < length es)%nat -> LoopSt i c -> SR rsegs c (FreeSt i (nth i es fi_e0)).
Proof using AX CTXO FREEPC HDJ HEOK HERR HFREE HFREEN HN4 HND HTAB IMGE IMGL IMGR PRE SEGS.
  intros i c Hi (L1 & A1 & R1 & m1 & md1 & nout1 & cap1 & out1 & O1 & junk1 & -> & HRL & R18 & R19 & HCI & HEST).
  pose proof HRL as (R2 & R3 & R4 & R8 & R9 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  pose proof HCI as (RP & IN & _ & RA1 & _ & _ & _ & CSR1 & _ & _ & _ & _ & _ & _ & _ & TAB1 & _).
  pose proof RP as (M1 & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct (fi_htab i Hi) as (C16 & HG0 & FG & GO & GN & _).
  destruct (TAB1 C16) as [[TL TR] HG1].
  destruct (fi_tab_split i Hi) as (TS & _ & TL1 & FP1 & FPe & _).
  destruct (fi_eok_i i Hi) as (_ & EOK & _).
  pose proof HEST as HEST0. rewrite (fi_skipn_S es i fi_e0 Hi) in HEST0.
  apply Forall_cons_iff in HEST0 as [ESTe EST3].
  rewrite TS, SEGS in TR.
  destruct (fi_tab_entry m1 G _ _ _ tail TR FP1 FPe) as (BUF8 & _).
  rewrite TL1 in BUF8.
  pose proof (fi_buf_rng i Hi) as HB.
  set (e := nth i es fi_e0) in *.
  pose proof YM05.alloc_ceiling_val as AC. pose proof YM05.alloc_ceiling_lt as ACL.
  destruct FG as (FG1 & FG2 & FG3). unfold SRC_TABLE, SRC_ENTRY in FG2.
  assert (Hi4 : Z.of_nat i < 4) by lia.
  destruct (proj1 (fi_blocks_in L1 A1 G SRC_TABLE) HG1) as (pG & EG & HpG).
  pose proof (proj1 (mr_blocks_range Bm _ (aa_laws API) L1 A1 m1 md1 pG SRC_TABLE M1 HpG)) as G4K.
  pose proof (mr_blocks_aligned Bm _ (aa_laws API) L1 A1 m1 md1 pG SRC_TABLE M1 HpG) as GAL.
  rewrite EG in G4K, GAL.
  assert (GA8 : G mod 8 = 0) by (Z.div_mod_to_equations; lia).
  eapply fi_kA0; [exact RA1 | exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. rewrite R9, R18.
    eapply fi_b1 with (G := G) (i := Z.of_nat i) (buf := re_buf e).
    - apply fi_rw_norm; [exact RA1 | exact CSR1 |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia.
    - apply fi_rd8. apply bytes_at_normalize; [exact RA1 | exact BUF8].
    - lia.
    - exact GA8.
    - lia.
    - lia.
    - exact HB. }
  { intros s0 (a1' & a2' & a3' & ->). do 2 eexists. reflexivity. }
  intros R0 pc0 R' m' HQ X MU WM RA'. cbv beta in HQ. destruct HQ as (a1' & a2' & a3' & HQ).
  injection HQ; intros; subst R0 pc0.
  assert (RL' : RL R') by (unfold RL; repeat split; rgx X).
  assert (X1 : reg_get R' 1 = Z_to_bv 64 78164) by rgx X.
  assert (X10 : reg_get R' 10 = Z_to_bv 64 (re_buf e)) by rgx X.
  assert (X18 : reg_get R' 18 = Z_to_bv 64 (56 * Z.of_nat i)) by rgx X.
  assert (X19 : reg_get R' 19 = Z_to_bv 64 (Z.of_nat i)) by rgx X.
  pose proof (fi_CI_tr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCI MU WM RA') as HCI'.
  pose proof (fi_est_tr0 _ _ _ _ _ HEST MU) as HEST'.
  pose proof (fi_est_tr0 _ _ _ _ _ EST3 MU) as EST3'.
  destruct ESTe as [BFe KSe]. pose proof (fi_kst_tr0 _ _ _ _ _ KSe MU) as KSe'.
  pose proof RL' as (Q2 & Q3 & Q4 & Q8 & Q9 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
  pose proof EOK as (_ & _ & _ & _ & _ & HCP & _ & _ & _ & BUF & _).
  destruct (Z.eq_dec (re_cap e) 0) as [C0|CN0].
  - assert (B0 : re_buf e = 0) by (destruct BUF as [(_ & -> & _) | (H & _)]; [reflexivity | lia]).
    assert (RR : forall j o, er (skipn i es) (NO + Tfx i) (bv_unsigned cap1) j o = fr i e (bv_unsigned cap1) j o).
    { intros j o. rewrite (fi_er_free i _ j o Hi e eq_refl). unfold bufree.
      rewrite (proj2 (Z.eqb_eq (re_cap e) 0) C0). cbn [app]. symmetry. apply surjective_pairing. }
    pose proof (fi_CI_rr _ _ RR _ _ _ _ _ _ _ _ _ _ _ _ _ HCI') as HCI2'. clear HCI'. rename HCI2' into HCI'.
    eapply SR_bind.
    { pose proof (HFREEN R' m' md1) as HF. rewrite SEGS, FREEPC in HF. apply HF.
      - change (YK0s.ret_ok (reg_get R' 1)). rewrite X1. exact fi_ra1.
      - change (reg_get R' 10 = Z_to_bv 64 0). rewrite X10, B0. reflexivity.
      - exact Hh.
      - exact Hl. }
    intros c' ->.
    replace (YK11.getr R' 1) with (Z_to_bv 64 78164) by (symmetry; exact X1).
    pose proof HCI' as (_ & _ & _ & _ & _ & _ & _ & CSR1' & _).
    eapply fi_kA0; [exact RA' | exact Hh | exact Hl | | |].
    { unfold Regs6ss.mkR_of. rewrite Q9, X18.
      eapply fi_b2 with (G := G) (i := Z.of_nat i).
      - apply fi_rw_norm; [exact RA' | exact CSR1' |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia.
      - lia.
      - lia.
      - lia. }
    { intros s0 (? & ? & ->). do 2 eexists. reflexivity. }
    intros R0 pc0 R'' m'' HQ' X' MU' WM' RA''. cbv beta in HQ'. destruct HQ' as (? & ? & HQ').
    injection HQ'; intros; subst R0 pc0.
    apply SR_ret. exists L1, A1, R'', m'', md1, nout1, cap1, out1, O1, junk1.
    split; [reflexivity|].
    split; [unfold RL; repeat split; rgx X'|].
    split; [rgx X'|]. split; [rgx X'|]. split; [rgx X'|]. split; [rgx X'|].
    assert (BUFL : bufl e = []) by (unfold bufl; rewrite (proj2 (Z.eqb_eq (re_cap e) 0) C0); reflexivity).
    rewrite BUFL, app_nil_r.
    split; [exact (fi_CI_tr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCI' MU' WM' RA'')|].
    split; [exact (fi_kst_tr0 _ _ _ _ _ KSe' MU')|].
    exact (fi_est_tr0 _ _ _ _ _ EST3' MU').
  - assert (Hc : 0 < re_cap e) by lia.
    pose proof HCI' as (RP' & IN' & RS' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LVF1 & LVT1 & _).
    destruct RS' as (tp & qs & o & RNq & RT1 & RST & RSO & RT2 & RT3 & RT4 & RT5 & RT6 & KN1).
    rewrite (fi_er_free i _ (length qs) o Hi e eq_refl) in RT2, RT3, RT4, RT5.
    unfold bufree in RT2, RT3. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) CN0) in RT2, RT3.
    cbn [fst snd] in RT2, RT3, RT4, RT5.
    destruct BUF as [(C0' & _) | (_ & BIN0 & FBb & _)]; [lia|].
    assert (HBe : In (re_buf e) (entry_blocks e)).
    { unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) CN0). apply in_or_app. left. left. reflexivity. }
    destruct (fi_eb_fresh i _ Hi HBe) as (NBP & NBS & NBO & NBC).
    destruct (KN1 (re_buf e) (re_cap e) BIN0 NBO NBP Hc) as [HpA Hp].
    set (p := sptr_of L0 A0 (re_buf e)) in *.
    assert (NOB1 : bv_unsigned out1 <> re_buf e).
    { destruct (lvT (Tfx i)) eqn:LV.
      - destruct (LVT1 eq_refl) as (_ & _ & DJ & _). intros E'.
        exact (DJ (re_buf e) (re_cap e) BIN0 NBO NBP Hc (eq_sym E')).
      - destruct (LVF1 eq_refl) as (_ & _ & -> & _). intros E'. exact (NBO (eq_sym E')). }
    eapply SR_bind.
    { pose proof (HFREE L1 A1 R' m' md1 p (re_cap e) (runF RFm qs bnd tp)) as HF.
      rewrite SEGS, FREEPC in HF. apply HF.
      - exact (fi_cpre ALLOC_STACK _ _ L1 A1 m' md1 R' RP' IN' RL' ltac:(rewrite X1; exact fi_ra1)
                 ltac:(unfold ALLOC_STACK; lia)).
      - exact RA'.
      - exact HpA.
      - change (reg_get R' 10 = Z_to_bv 64 (ptr_addr L1 p)). rewrite X10, Hp. reflexivity.
      - exact RT1. }
    intros c' (L2 & A2 & R2' & m2 & md2 & -> & CP & BL & BK & RA2 & _ & SURV & INI & LNR & RES2).
    assert (RS2 : RSt L2 A2 (fr i e (bv_unsigned cap1)) (bv_unsigned cap1) (bv_unsigned out1) (Pfx i ++ bufl e)).
    { pose proof CP as (_ & _ & _ & _ & ADf & _).
      exists (tp ++ [RFree (re_cap e) (nm0 (re_buf e))]), qs, o.
      split; [rewrite nret_app; change (nretF [RFree (re_cap e) (nm0 (re_buf e))]) with 0%nat; lia|].
      split; [rewrite p3c_runF_free; exact RES2|].
      split; [intros ext; rewrite p3c_run_free, p3c_runF_free, (RST ext); reflexivity|].
      split; [exact RSO|].
      split; [intros rest Hr; rewrite p3c_runF_free; exact (RT2 rest Hr)|].
      split; [rewrite <- app_assoc; exact RT3|]. split; [exact RT4|]. split; [exact RT5|].
      split.
      - intros HC. destruct (RT6 HC) as [Hin Ha].
        assert (NE : resolveF qs o <> p) by (intros E'; apply NOB1; rewrite <- Ha, E'; exact Hp).
        pose proof (SURV _ _ Hin NE) as Hin2. split; [exact Hin2|]. rewrite (ADf _ _ Hin Hin2). exact Ha.
      - intros q m Hq NOq NP Hm.
        assert (NP0 : ~ In q (Pfx i)) by (intros X'; apply NP; apply in_or_app; left; exact X').
        assert (NQB : q <> re_buf e).
        { intros ->. apply NP. apply in_or_app. right. unfold bufl.
          rewrite (proj2 (Z.eqb_neq (re_cap e) 0) CN0). left. reflexivity. }
        destruct (KN1 q m Hq NOq NP0 Hm) as [Hin Ha].
        assert (NE : sptr_of L0 A0 q <> p) by (intros E'; apply NQB; rewrite <- Ha, E'; exact Hp).
        pose proof (SURV _ _ Hin NE) as Hin2. split; [exact Hin2|]. rewrite (ADf _ _ Hin Hin2). exact Ha. }
    destruct (fi_CI_free i L1 A1 m' md1 _ _ nout1 cap1 out1 O1 junk1 R' L2 A2 R2' m2 md2 p Hi HCI' HEST' Hc Hp HpA
      RL' CP BL BK ltac:(rewrite SEGS; exact RA2) SURV INI LNR RS2) as (HCI2 & KS2 & EST2).
    pose proof CP as (M2 & _ & _ & _ & _ & RPr & _).
    destruct (fi_RL_pres R' R2' RPr RL') as (RL2 & Y18 & Y19).
    rewrite X18 in Y18. rewrite X19 in Y19.
    pose proof RL2 as (Y2 & Y3 & Y4 & Y8 & Y9 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
    destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
    replace (YK11.getr R' 1) with (Z_to_bv 64 78164) by (symmetry; exact X1).
    pose proof HCI2 as (_ & _ & _ & _ & _ & _ & _ & CSR2 & _).
    eapply fi_kA0; [exact RA2 | exact Hh2 | exact Hl2 | | |].
    { unfold Regs6ss.mkR_of. rewrite Y9, Y18.
      eapply fi_b2 with (G := G) (i := Z.of_nat i).
      - apply fi_rw_norm; [exact RA2 | exact CSR2 |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia.
      - lia.
      - lia.
      - lia. }
    { intros s0 (? & ? & ->). do 2 eexists. reflexivity. }
    intros R0 pc0 R3' m3 HQ' X3 MU3 WM3 RA3. cbv beta in HQ'. destruct HQ' as (? & ? & HQ').
    injection HQ'; intros; subst R0 pc0.
    apply SR_ret. exists L2, A2, R3', m3, md2, nout1, cap1, out1, O1, junk1.
    split; [reflexivity|].
    split; [unfold RL; repeat split; rgx X3|].
    split; [rgx X3|]. split; [rgx X3|]. split; [rgx X3|]. split; [rgx X3|].
    split; [exact (fi_CI_tr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCI2 MU3 WM3 RA3)|].
    split; [exact (fi_kst_tr0 _ _ _ _ _ KS2 MU3)|].
    exact (fi_est_tr0 _ _ _ _ _ EST2 MU3).
Qed.

(* The loop body after free: gestures_end on entry i, then the index step. *)
Lemma fi_ko_len : forall ks, Z.of_nat (length (keys_out ks)) = keys_total ks.
Proof using Bm O es junk.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold keys_out, keys_total in *. cbn [map concat fold_right]. rewrite !length_app.
  change (length END5) with 5%nat. lia.
Qed.

Lemma fi_blk_step : forall (B0 B1 B2 : Z -> Z -> Prop) (P P' Kl : Z -> Prop) (b l : bool)
    (OUT CAP o1 c1 o2 c2 hp : Z),
  (forall q m, B1 q m <-> (B0 q m /\ q <> OUT /\ ~ P q) \/ (b = true /\ q = o1 /\ m = c1) \/
                          (b = false /\ 0 < CAP /\ q = OUT /\ m = CAP)) ->
  (forall q m, B2 q m <-> (B1 q m /\ q <> o1 /\ q <> hp /\ ~ Kl q) \/ (l = true /\ q = o2 /\ m = c2) \/
                          (l = false /\ 0 < c1 /\ q = o1 /\ m = c1)) ->
  (forall q m, B0 q m -> (P' q <-> P q \/ q = hp \/ Kl q)) ->
  (b = false -> o1 = OUT /\ c1 = CAP) ->
  (b = true -> 0 < c1 /\ forall m, B1 o1 m -> m = c1) ->
  (b = true -> forall m, B0 o1 m -> o1 <> OUT -> ~ P o1 -> 0 < m -> False) ->
  forall q m, B2 q m <-> (B0 q m /\ q <> OUT /\ ~ P' q) \/
    (orb b l = true /\ q = (if l then o2 else o1) /\ m = (if l then c2 else c1)) \/
    (orb b l = false /\ 0 < CAP /\ q = OUT /\ m = CAP).
Proof using.
  intros B0 B1 B2 P P' Kl b l OUT CAP o1 c1 o2 c2 hp H1 H2 HP HB0 HB1 DJ q m.
  rewrite H2, H1. split.
  - intros [([Hq | [(Eb & Eq & Em) | (Eb & HC & Eq & Em)]] & N1 & N2 & N3) | [(El & Eq & Em) | (El & HC & Eq & Em)]].
    + left. destruct Hq as (Hq & NO & NP). split; [exact Hq|]. split; [exact NO|].
      intros X. apply (HP q m Hq) in X. destruct X as [X|[X|X]]; [exact (NP X) | exact (N2 X) | exact (N3 X)].
    + exfalso. exact (N1 Eq).
    + exfalso. destruct (HB0 Eb) as [E _]. apply N1. rewrite Eq. symmetry. exact E.
    + right. left. subst l. split; [destruct b; reflexivity | split; [exact Eq | exact Em]].
    + right. subst l. destruct b.
      * left. split; [reflexivity | split; [exact Eq | exact Em]].
      * right. destruct (HB0 eq_refl) as [E1 E2]. split; [reflexivity|].
        split; [rewrite <- E2; exact HC|]. split; [rewrite <- E1; exact Eq | rewrite <- E2; exact Em].
  - intros [(Hq & NO & NP) | [(Eo & Eq & Em) | (Eo & HC & Eq & Em)]].
    + assert (NP1 : ~ P q) by (intros X; apply NP; apply (HP q m Hq); left; exact X).
      assert (NH : q <> hp) by (intros X; apply NP; apply (HP q m Hq); right; left; exact X).
      assert (NK : ~ Kl q) by (intros X; apply NP; apply (HP q m Hq); right; right; exact X).
      destruct (Z.eq_dec q o1) as [E|E].
      * subst q. destruct b.
        -- destruct (HB1 eq_refl) as [HC1 U].
           assert (Em : m = c1) by (apply U; apply H1; left; split; [exact Hq | split; [exact NO | exact NP1]]).
           subst m. destruct l.
           ++ exfalso. exact (DJ eq_refl c1 Hq NO NP1 HC1).
           ++ right. right. split; [reflexivity|]. split; [exact HC1|]. split; reflexivity.
        -- exfalso. destruct (HB0 eq_refl) as [E1 _]. exact (NO E1).
      * left. split; [left; split; [exact Hq | split; [exact NO | exact NP1]]|].
        split; [exact E|]. split; [exact NH | exact NK].
    + destruct l.
      * right. left. split; [reflexivity|]. split; [exact Eq | exact Em].
      * destruct b; [|cbn in Eo; discriminate Eo].
        destruct (HB1 eq_refl) as [HC1 _].
        right. right. split; [reflexivity|]. split; [exact HC1|]. split; [exact Eq | exact Em].
    + destruct b; [cbn in Eo; discriminate Eo|]. destruct l; [cbn in Eo; discriminate Eo|].
      destruct (HB0 eq_refl) as [E1 E2].
      right. right. split; [reflexivity|]. split; [rewrite E2; exact HC|].
      split; [rewrite E1; exact Eq | rewrite E2; exact Em].
Qed.

Lemma fi_blk_4k : forall L A mem md q m, aa_MR API L A mem md -> In (q, m) (blocks L A) -> 4096 <= q.
Proof using.
  intros L A mem md q m HM Hq. apply fi_blocks_in in Hq as (p & <- & Hp).
  exact (proj1 (mr_blocks_range Bm _ (aa_laws API) L A mem md p m HM Hp)).
Qed.

Lemma fi_live_le : forall T, lvT T = true -> 0 <= T <= TOT -> live = true.
Proof using Bm Hbr O junk.
  intros T H HT. unfold lvT, send_live, send_off in H |- *. revert H.
  destruct (Z.eqb_spec T 0) as [E|E].
  - rewrite orb_true_r. intros H. cbn in H. discriminate H.
  - destruct (Z.eqb_spec TOT 0) as [E'|E']; [lia|]. intros H. exact H.
Qed.

(* A gestures_end with keys to send is live exactly when the whole run is. *)
Lemma fi_lv_same : forall T kt, 0 <= T -> 0 <= kt -> T + kt <= TOT -> kt <> 0 ->
  send_live cl (brT T) dd kt = live.
Proof using Bm Hbr Hcl Hdd O junk.
  intros T kt H1 H2 H3 H4. unfold brT, send_live, send_off.
  destruct Hcl as [Ec | Ec]; destruct Hbr as [Eb | Eb]; destruct Hdd as [Ed | Ed]; rewrite Ec, Eb, Ed;
    destruct (Z.eqb_spec T 0); destruct (Z.eqb_spec kt 0); destruct (Z.eqb_spec TOT 0); cbn; try lia; reflexivity.
Qed.

Lemma fi_eb_blk0 : forall e' q, entry_ok Bm L0 A0 mem0 e' -> In q (entry_blocks e') ->
  exists k0, 0 < k0 /\ In (q, k0) (blocks L0 A0).
Proof using O es junk.
  intros e' q EOK Hq.
  destruct EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BUF & _ & HPK & _ & _ & KF).
  unfold entry_blocks in Hq. apply in_app_or in Hq as [Hq|Hq]; [|apply in_app_or in Hq as [Hq|Hq]].
  - revert Hq. destruct (Z.eqb_spec (re_cap e') 0) as [E|E]; intros Hq; [destruct Hq|].
    destruct Hq as [<-|[]].
    destruct BUF as [(C0 & _) | (CP & BIN & _)]; [lia|]. exists (re_cap e'). split; [exact CP | exact BIN].
  - revert Hq. destruct (Z.eqb_spec (re_hp e') 0) as [E|E]; intros Hq; [destruct Hq|].
    destruct Hq as [<-|[]].
    destruct HPK as [(H0 & _) | (HIN & _ & _ & K8 & _)]; [contradiction|].
    exists (re_kh e'). split; [lia | exact HIN].
  - apply in_map_iff in Hq as (k & <- & Hk). rewrite Forall_forall in KF. destruct (KF k Hk) as (KIN & _).
    exists (Z.of_nat (length (key_text k)) + 1). split; [lia | exact KIN].
Qed.

Lemma fi_s_ge : forall i c, (i < length es)%nat -> FreeSt i (nth i es fi_e0) c ->
  SR rsegs c (fun c' => ((S i < length es)%nat /\ LoopSt (S i) c') \/ (S i = length es /\ ExitSt c')).
Proof using AX HDJ HEOK HERR HERR4 HGE HN4 HND HOUT HREQ HTAB Hbr Hcl Hdd Hei IMG5 IMGE IMGL IMGR PRE SEGS SLK TPE.
  intros i c Hi (L1 & A1 & R1 & m1 & md1 & nout1 & cap1 & out1 & O1 & junk1 & -> & HRL & R18 & R19 & R1a & R10 &
    HCI & KS1 & EST1).
  pose proof HRL as (Q2 & Q3 & Q4 & Q8 & Q9 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
  destruct HCI as (RP & IN & RS & RA1 & CTU1 & CLK1 & CNS1 & CSR1 & CLS1 & CBR1 & CDD1 & CEI1 & COV1 & CER1 &
    FR1 & TAB1 & BLK1 & LVF1 & LVT1 & HO1).
  pose proof RP as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & RP1 & MD1 & FM1 & BY1 & SC1).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  destruct fi_pre_facts as (HCE & HAL & H63 & HWS & HTP & HRA & HERRW & _ & _ & HMR).
  pose proof YM05.alloc_ceiling_val as AC. pose proof YM05.alloc_ceiling_lt as ACL. pose proof fi_err_low as EL.
  pose proof (bv_unsigned_in_range 64 (reg_get regs0 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 nout1) as RN1. unfold bv_modulus in RN1. cbn in RN1.
  pose proof (bv_unsigned_in_range 64 nout) as RN0. unfold bv_modulus in RN0. cbn in RN0.
  pose proof (fi_spR R1 HRL) as SPR.
  destruct (fi_htab i Hi) as (C16 & HG0 & FG & GO & GN & _).
  destruct (TAB1 C16) as [[TL TR] HG1].
  destruct (fi_tab_split i Hi) as (TS & TS1 & TL1 & FP1 & FPe & PS & TS' & ES).
  destruct (fi_eok_i i Hi) as (_ & EOK & EOK3).
  pose proof (fi_eb_nd i Hi) as NDe.
  rewrite TS, SEGS in TR.
  set (e := nth i es fi_e0) in *.
  destruct RS as (tp & qs & o & RNq & RT1 & RST & RSO & RT2 & RT3 & RT4 & RT5 & RT6 & KN1).
  unfold fr in RT2, RT3, RT4, RT5. cbv zeta in RT2, RT3, RT4, RT5. cbn [fst snd] in RT2, RT3, RT4, RT5.
  pose proof FG as FG0. destruct FG as (FG1 & FG2 & FG3). unfold SRC_TABLE, SRC_ENTRY in FG2.
  assert (Hi4 : Z.of_nat i < 4) by lia.
  pose proof EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NH26 & HPK & NDK & _ & KF0).
  fi_u_in HPK. fi_u_in NDK. fi_u_in KF0.
  assert (TN : 0 <= Tfx i) by (unfold Tfx; apply fi_et_nonneg).
  assert (KN : 0 <= keys_total (re_keys e)) by apply fi_kt_nonneg.
  assert (TT : Tfx (S i) <= TOT) by (unfold Tfx; apply fi_et_firstn_le).
  (* Block lists of entry i. *)
  assert (EBE : entry_blocks e = bufl e ++ hpl e ++ map key_addr (re_keys e)) by reflexivity.
  assert (HPL : re_hp e <> 0 -> In (re_hp e) (hpl e ++ map key_addr (re_keys e))).
  { intros HZ. apply in_or_app. left. unfold hpl. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) HZ). left. reflexivity. }
  assert (KL : forall q, In q (map key_addr (re_keys e)) -> In q (hpl e ++ map key_addr (re_keys e)))
    by (intros q X; apply in_or_app; right; exact X).
  assert (HPI : re_hp e <> 0 -> In (re_hp e) (entry_blocks e))
    by (intros HZ; rewrite EBE; apply in_or_app; right; exact (HPL HZ)).
  assert (KAI : forall q, In q (map key_addr (re_keys e)) -> In q (entry_blocks e))
    by (intros q X; rewrite EBE; apply in_or_app; right; exact (KL q X)).
  assert (BLI : forall q, In q (bufl e) -> In q (entry_blocks e))
    by (intros q X; rewrite EBE; apply in_or_app; left; exact X).
  assert (EBC : forall q, In q (entry_blocks e) -> In q (concat (map entry_blocks es)))
    by (intros q Hq; exact (proj2 (proj2 (proj2 (fi_eb_fresh i q Hi Hq))))).
  assert (PC : forall q, In q (Pfx i ++ bufl e) -> In q (concat (map entry_blocks es))).
  { intros q Hq. apply in_app_or in Hq as [Hq|Hq].
    - rewrite (fi_cat_split i Hi). apply in_or_app. left. exact Hq.
    - exact (EBC q (BLI q Hq)). }
  assert (PSI : forall q, In q (Pfx (S i)) <-> In q (Pfx i ++ bufl e) \/ In q (hpl e ++ map key_addr (re_keys e))).
  { intros q. rewrite PS, EBE, app_assoc. apply in_app_iff. }
  assert (PSub : forall q, In q (Pfx i ++ bufl e) -> In q (Pfx (S i)))
    by (intros q X; apply PSI; left; exact X).
  assert (NDe' : List.NoDup (bufl e ++ hpl e ++ map key_addr (re_keys e))) by exact NDe.
  assert (QNP : forall q, In q (hpl e ++ map key_addr (re_keys e)) -> ~ In q (Pfx i ++ bufl e)).
  { intros q Hq Hin. apply in_app_or in Hin as [Hin|Hin].
    - assert (HE : In q (entry_blocks e)) by (rewrite EBE; apply in_or_app; right; exact Hq).
      exact (proj1 (fi_eb_fresh i q Hi HE) Hin).
    - exact (fi_nd_app (bufl e) _ q NDe' Hq Hin). }
  assert (HPK2 : re_hp e <> 0 -> ~ In (re_hp e) (map key_addr (re_keys e))).
  { intros HZ X. refine (fi_nd_app2 _ _ (re_hp e) (List.NoDup_app_remove_l _ _ NDe') _ X).
    unfold hpl. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) HZ). left. reflexivity. }
  (* The output buffer before the call. *)
  assert (NOT1 : forall q k0, In (q, k0) (blocks L0 A0) -> 0 < k0 -> q <> OUT -> ~ In q (Pfx i ++ bufl e) ->
            q <> bv_unsigned out1).
  { intros q k0 Hq Hk NOq NP. destruct (lvT (Tfx i)) eqn:LV.
    - destruct (LVT1 eq_refl) as (_ & _ & DJ & _). exact (DJ q k0 Hq NOq NP Hk).
    - destruct (LVF1 eq_refl) as (_ & _ & -> & _). exact NOq. }
  assert (ENO1 : forall q, In q (hpl e ++ map key_addr (re_keys e)) -> q <> bv_unsigned out1).
  { intros q Hq. assert (HE : In q (entry_blocks e)) by (rewrite EBE; apply in_or_app; right; exact Hq).
    destruct (fi_eb_blk0 e q EOK HE) as (k0 & Hk0 & Hq0).
    exact (NOT1 q k0 Hq0 Hk0 (proj1 (proj2 (proj2 (fi_eb_fresh i q Hi HE)))) (QNP q Hq)). }
  assert (NOB : bv_unsigned nout1 <= NO + Tfx i).
  { destruct (lvT (Tfx i)) eqn:LV.
    - destruct (LVT1 eq_refl) as (E1 & _). lia.
    - destruct (LVF1 eq_refl) as (-> & _). lia. }
  assert (LO1 : Z.of_nat (length O1) = bv_unsigned nout1).
  { destruct HO1 as [(_ & _ & N0 & EO) | (_ & _ & _ & _ & _ & H6 & _)]; [rewrite EO; cbn; lia | exact H6]. }
  assert (GNO : G <> bv_unsigned out1).
  { apply (NOT1 G SRC_TABLE HG0 ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) GO). intros X. exact (GN (PC G X)). }
  assert (GNH : G <> re_hp e).
  { intros E'. destruct (Z.eq_dec (re_hp e) 0) as [Z0|Z0]; [lia|]. apply GN. rewrite E'. exact (EBC _ (HPI Z0)). }
  assert (GNK : ~ In G (map key_addr (re_keys e))) by (intros X; exact (GN (EBC _ (KAI _ X)))).
  assert (LT : lvT (Tfx i) = true -> live = true) by (intros X; apply (fi_live_le (Tfx i) X); lia).
  assert (LS : lvT (Tfx (S i)) = true -> live = true) by (intros X; apply (fi_live_le (Tfx (S i)) X); lia).
  (* The entry's held array and keys are the start blocks the trace names. *)
  assert (KSPT : forall q, In q (hpl e ++ map key_addr (re_keys e)) -> sptr_of L1 A1 q = sptr_of L0 A0 q).
  { intros q Hq. assert (HE : In q (entry_blocks e)) by (rewrite EBE; apply in_or_app; right; exact Hq).
    destruct (fi_eb_blk0 e q EOK HE) as (k0 & Hk0 & Hq0).
    destruct (fi_eb_fresh i q Hi HE) as (_ & _ & NOq & _).
    exact (p3c_live_sptr _ _ _ _ _ (HND L1 A1 m1 md1 M1) (KN1 q k0 Hq0 NOq (QNP q Hq) Hk0)). }
  (* The call to gestures_end. *)
  destruct CER1 as [ev CE1].
  destruct (fi_keys_slack Bm API SEGS SLK L1 A1 m1 md1 (re_keys e) M1 (proj2 KS1)) as (ks' & KA & KT & KSL).
  destruct (fi_ks_eq (re_keys e) ks' KA KT) as (KTE & KOE & KPE & KLE).
  assert (G10a : YK11.getr R1 10 = Z_to_bv 64 (G + 56 * Z.of_nat i)) by exact R10.
  assert (G10b : PropExec.getr R1 10 = Z_to_bv 64 (G + 56 * Z.of_nat i)) by exact R10.
  assert (G1a : YK11.getr R1 1 = Z_to_bv 64 78196) by exact R1a.
  assert (G1b : PropExec.getr R1 1 = Z_to_bv 64 78196) by exact R1a.
  assert (U10 : bv_unsigned (Z_to_bv 64 (G + 56 * Z.of_nat i)) = G + 56 * Z.of_nat i) by (apply unsigned_lit; lia).
  pose proof (HGE L1 A1 R1 m1 md1 (runF RFm qs bnd tp) ks' (re_hp e) (re_kh e) O1 junk1 cl (brT (Tfx i)) dd
    (eiT (Tfx i)) mx nout1 cap1 out1 ev) as HG.
  cbv zeta in HG. rewrite SEGS in HG. rewrite ?G10a, ?G10b in HG. rewrite U10, KTE, KOE, KPE, KLE, KA in HG.
  rewrite (fi_kl_eq (re_keys e) ks' KT) in HG.
  rewrite (p3c_kr_eq (known_at L1 A1) (re_keys e) ks' KA KT) in HG.
  assert (EXL : exists lv1, lv1 = send_live cl (brT (Tfx i)) dd (keys_total (re_keys e))) by (eexists; reflexivity).
  destruct EXL as [lv1 LV1]. rewrite <- LV1 in HG.
  (* The callee's requests and final g_capout are those of the run's model. *)
  assert (NOE : lv1 = true -> bv_unsigned nout1 = NO + Tfx i).
  { intros LVt. destruct (lvT (Tfx i)) eqn:LVo.
    - destruct (LVT1 eq_refl) as (E1 & _). exact E1.
    - destruct (LVF1 eq_refl) as (-> & _).
      pose proof (fi_live_t1 cl br dd (Tfx i) _ Hcl Hbr Hdd TN KN (eq_trans (eq_sym LV1) LVt) LVo) as T0. lia. }
  assert (KER : forall X j' o', keys_end_run lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1)
                   (key_runs X (re_keys e)) j' o' =
                 keys_end_run live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs X (re_keys e)) j' o').
  { intros X j' o'. destruct (key_lens (re_keys e)) as [|xl xls] eqn:KL0.
    - unfold key_lens in KL0. apply map_eq_nil in KL0. rewrite KL0. reflexivity.
    - assert (KZ : keys_total (re_keys e) <> 0) by (apply fi_kl_nz; rewrite KL0; discriminate).
      assert (LE : lv1 = live) by (rewrite LV1; apply fi_lv_same; lia).
      rewrite <- LE. destruct lv1.
      + rewrite (NOE eq_refl). reflexivity.
      + rewrite !fi_ker_false. reflexivity. }
  assert (GTR : forall X j' o' ha,
            gestures_end_tr lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1) (key_runs X (re_keys e))
              (re_hp e) (re_kh e) j' o' ha =
            gestures_end_tr live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs X (re_keys e))
              (re_hp e) (re_kh e) j' o' ha).
  { intros X j' o' ha. unfold gestures_end_tr. rewrite KER. reflexivity. }
  assert (GOUT : forall X j' o',
            gestures_end_out lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1) (key_runs X (re_keys e)) j' o' =
            gestures_end_out live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs X (re_keys e)) j' o').
  { intros X j' o'. unfold gestures_end_out. rewrite KER. reflexivity. }
  assert (GC : gestures_end_cap lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1) (key_lens (re_keys e)) =
               gestures_end_cap live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_lens (re_keys e))).
  { unfold gestures_end_cap.
    replace (map (fun xl => (xl, adr0)) (key_lens (re_keys e))) with (key_runs (fun _ => adr0) (re_keys e))
      by (unfold key_runs, key_lens; rewrite map_map; reflexivity).
    rewrite KER. reflexivity. }
  assert (GCAP : lv1 = true ->
            gestures_end_cap lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1) (key_lens (re_keys e)) =
            gestures_end_cap live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_lens (re_keys e))).
  { intros LVt. pose proof (fi_live_nz cl (brT (Tfx i)) dd _ (eq_trans (eq_sym LV1) LVt)) as KZ.
    assert (LE : lv1 = live) by (rewrite LV1; apply fi_lv_same; lia).
    rewrite <- LE, (NOE LVt). reflexivity. }
  assert (GCAP0 : lv1 = false ->
            gestures_end_cap live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_lens (re_keys e)) =
            bv_unsigned cap1).
  { intros LVf. destruct (key_lens (re_keys e)) as [|xl xls] eqn:KL0; [reflexivity|].
    assert (KZ : keys_total (re_keys e) <> 0) by (apply fi_kl_nz; rewrite KL0; discriminate).
    assert (LE : lv1 = live) by (rewrite LV1; apply fi_lv_same; lia).
    rewrite <- LE, LVf. apply fi_gec_false. }
  (* The callee's requests are the run's next requests, its returned addresses the run's next ones. *)
  assert (RESX : forall qc0 ext,
    length qc0 = nretF (gestures_end_tr lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1)
       (key_runs (known_at L1 A1) (re_keys e)) (re_hp e) (re_kh e) 0 (known_at L1 A1 (bv_unsigned out1))
       (known_at L1 A1 (re_hp e))) ->
    p3c_res (qs ++ qc0 ++ ext) (length qs)
      (gestures_end_tr live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs nm0 (re_keys e)) (re_hp e)
         (re_kh e) (length qs) o (nm0 (re_hp e))) =
    p3c_res qc0 0 (gestures_end_tr lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1)
       (key_runs (known_at L1 A1) (re_keys e)) (re_hp e) (re_kh e) 0 (known_at L1 A1 (bv_unsigned out1))
       (known_at L1 A1 (re_hp e))) /\
    nretF (gestures_end_tr live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs nm0 (re_keys e)) (re_hp e)
       (re_kh e) (length qs) o (nm0 (re_hp e))) = length qc0 /\
    (gestures_end_cap live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_lens (re_keys e)) <> 0 ->
       resolveF (qs ++ qc0 ++ ext) (gestures_end_out live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1)
         (key_runs nm0 (re_keys e)) (length qs) o) =
       resolveF qc0 (gestures_end_out lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1)
         (key_runs (known_at L1 A1) (re_keys e)) 0 (known_at L1 A1 (bv_unsigned out1))))).
  { intros qc0 ext QL0.
    destruct (p3c_ges_res lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1) (key_runs nm0 (re_keys e))
      (key_runs (known_at L1 A1) (re_keys e)) (re_hp e) (re_kh e) (qs ++ qc0 ++ ext) qc0 (length qs) 0%nat o
      (known_at L1 A1 (bv_unsigned out1)) (nm0 (re_hp e)) (known_at L1 A1 (re_hp e))) as (E1 & E2 & E3).
    - apply p3c_kr_f2. intros k Hk. unfold known_at. cbn [resolve]. symmetry. apply KSPT. apply KL.
      exact (in_map key_addr _ _ Hk).
    - intros HC. rewrite (RSO HC (qc0 ++ ext)). unfold known_at. cbn [resolve]. symmetry.
      exact (p3c_live_sptr _ _ _ _ _ (HND L1 A1 m1 md1 M1) (RT6 HC)).
    - intros HZ. unfold known_at. cbn [resolve]. symmetry. apply KSPT. exact (HPL HZ).
    - intros i0 Hi0. rewrite app_nth2 by lia. replace (length qs + i0 - length qs)%nat with i0 by lia.
      rewrite app_nth1 by lia. reflexivity.
    - rewrite (GTR nm0 (length qs) o (nm0 (re_hp e))) in E1, E2.
      rewrite (GOUT nm0 (length qs) o), p3c_kr_fst, GC in E3.
      split; [exact E1|]. split; [rewrite QL0; exact E2 | exact E3]. }
  eapply SR_bind.
  { apply HG.
    - reflexivity.
    - exact (fi_cpre GESTURES_END_K _ _ L1 A1 m1 md1 R1 RP IN HRL ltac:(rewrite R1a; exact fi_ra2)
        ltac:(rewrite fi_GK; lia)).
    - exact IN.
    - exact TPE.
    - exact HERR4.
    - unfold G_LOCK_HI in HERR. unfold G_RELAY_HI. lia.
    - exact RA1.
    - intros a Ha. apply IMGR. unfold G_RELAY_HI in Ha. unfold G_LOCK_HI. lia.
    - intros a Ha. apply IMGL. unfold G_CLIENT in Ha. unfold G_LISTEN, G_CLIENT. lia.
    - exact IMGE.
    - exact IMG5.
    - exists G, SRC_TABLE. split; [exact HG1|]. split; [exact FG0|]. split; [lia|].
      split; [unfold SRC_TABLE, SRC_ENTRY; lia|]. split; [exact GNO|]. split; [exact GNH | exact GNK].
    - destruct (proj1 (fi_blocks_in L1 A1 G SRC_TABLE) HG1) as (pG & EG & HpG).
      pose proof (mr_blocks_aligned Bm _ (aa_laws API) L1 A1 m1 md1 pG SRC_TABLE M1 HpG) as GAL.
      rewrite EG in GAL. Z.div_mod_to_equations. lia.
    - destruct (fi_tab_entry m1 G _ _ _ tail TR FP1 FPe) as (_ & HPC). rewrite TL1 in HPC. exact HPC.
    - unfold re_nheld in NH26. lia.
    - destruct HPK as [(H0 & H1) | (HIN0 & FBh & K8 & K8' & BYh)].
      + left. split; [exact H0|]. apply length_zero_iff_nil. rewrite KLE, H1. reflexivity.
      + right. assert (HZ : re_hp e <> 0) by (destruct FBh as (F1 & _); lia).
        destruct (proj1 KS1 HZ) as [HIN1 BYh1].
        split; [exact HIN1|]. split; [exact FBh|]. split; [unfold re_nheld in K8; lia|]. split; [exact K8'|].
        split; [exact (ENO1 _ (HPL HZ))|]. split; [exact (HPK2 HZ) | exact BYh1].
    - exact NDK.
    - assert (KF3 : Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L1 A1) /\
          fresh_block Bm (key_addr k) (Z.of_nat (length (key_text k)) + 1) /\ ~ In (Z_to_bv 8 0) (key_text k) /\
          1 <= Z.of_nat (length (key_text k)) <= 6000 /\ key_addr k <> bv_unsigned out1) ks').
      { apply (fi_ks_forall (fun a t => In (a, Z.of_nat (length t) + 1) (blocks L1 A1) /\
          fresh_block Bm a (Z.of_nat (length t) + 1) /\ ~ In (Z_to_bv 8 0) t /\
          1 <= Z.of_nat (length t) <= 6000 /\ a <> bv_unsigned out1) (re_keys e) ks' KA KT).
        pose proof (proj2 KS1) as KS2. rewrite Forall_forall in KF0, KS2 |- *. intros k Hk. cbv beta.
        destruct (KS2 k Hk) as [KIN1 _]. destruct (KF0 k Hk) as (_ & KFB & _ & KNZ & KLN & _).
        split; [exact KIN1|]. split; [exact KFB|]. split; [exact KNZ|]. split; [lia|].
        exact (ENO1 _ (KL _ (in_map key_addr _ _ Hk))). }
      rewrite Forall_forall in KF3, KSL |- *. intros k Hk.
      destruct (KF3 k Hk) as (X1 & X2 & X3 & X4 & X5). destruct (KSL k Hk) as [Y1 Y2].
      split; [exact X1|]. split; [exact X2|]. split; [exact Y1|]. split; [exact X3|]. split; [exact X4|].
      split; [exact Y2 | exact X5].
    - exact Hcl.
    - exact (fi_br_01 cl br dd (Tfx i) Hbr Hdd).
    - exact Hdd.
    - exact (fi_ei_01 cl br ei (Tfx i) Hei).
    - apply (fi_rw_at _ _ _ _ (proj2 (fi_cut m1 G_LISTEN [C4 (Z_to_bv 64 lst)] [C4 (Z_to_bv 64 cl)] CLS1))).
      cbn. unfold G_LISTEN, G_CLIENT. lia.
    - exact CBR1.
    - exact CDD1.
    - exact CEI1.
    - exact COV1.
    - exact CE1.
    - exact HO1.
    - lia.
    - exact RT1.
    - intros qc0 HL0.
      match type of RT2 with forall rest, length rest = nretF (?t1 ++ ?t2) -> _ =>
        destruct (RESX qc0 (p3c_pad (nretF t2)) HL0) as (E1 & E2 & _);
        pose proof (RT2 (qc0 ++ p3c_pad (nretF t2))
                      ltac:(rewrite length_app, p3c_pad_len, nret_app, E2; reflexivity)) as HR
      end.
      apply room_from_app in HR. destruct HR as [HR _].
      rewrite p3c_roomF, p3c_room_res, <- E1, <- p3c_room_res. exact HR. }
  intros c' (L2 & A2 & R2 & m2 & md2 & OUT' & CAP' & junk' & -> & RPg & IN2 & RS2 & RA2 & SA2 & CL2 &
    BR2 & DD2 & EI2 & ER2 & BLK2 & LF2 & LT2).
  destruct RS2 as (qc & QL & RS2 & LK2).
  pose proof RPg as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & RPr & _).
  (* What gestures_end leaves alone. *)
  assert (NE2 : forall q k0 j, In (q, k0) (blocks L1 A1) -> q <> G -> (lv1 = true -> q <> bv_unsigned out1) ->
            0 <= j < k0 -> ~ gestures_writes lv1 (bv_unsigned out1) (bv_unsigned cap1) (G + 56 * Z.of_nat i) (q + j)).
  { intros q k0 j Hq NG NOq Hj HE.
    destruct (fi_blk_low L1 A1 m1 md1 q k0 j M1 Hq Hj) as [Hb Hi'].
    unfold gestures_writes, send_writes in HE.
    destruct HE as [[X|[X|[X|(LV & X)]]]|X].
    - apply Hi'. exact (proj1 (IMGR (q + j) ltac:(unfold G_BROKEN in X; unfold G_RELAY_LO, G_LOCK_HI; lia))).
    - apply Hi'. exact (proj1 (IMGR (q + j) ltac:(unfold G_EINTR in X; unfold G_RELAY_LO, G_LOCK_HI; lia))).
    - apply Hi'. exact (proj1 (IMGR (q + j) ltac:(unfold G_OUTV in X; unfold G_RELAY_LO, G_LOCK_HI; lia))).
    - destruct HO1 as [(C0 & _) | (H1 & _ & H3 & _)]; [lia|].
      destruct (fi_blk_disj Bm API L1 A1 m1 md1 _ _ _ _ M1 Hq H3 (NOq LV)) as [D|D]; lia.
    - destruct (fi_blk_disj Bm API L1 A1 m1 md1 _ _ _ _ M1 Hq HG1 NG) as [D|D]; unfold SRC_TABLE, SRC_ENTRY in D;
        lia. }
  assert (KEEPB : forall q k0, In (q, k0) (blocks L1 A1) -> 0 < k0 -> q <> G -> (lv1 = true -> q <> bv_unsigned out1) ->
            q <> re_hp e -> ~ In q (map key_addr (re_keys e)) ->
            In (q, k0) (blocks L2 A2) /\
            (forall j, 0 <= j < k0 -> YP09.mbyte rsegs m2 (q + j) = YP09.mbyte rsegs m1 (q + j))).
  { intros q k0 Hq Hk NG NOq NH NK.
    apply (fi_rp_keep Bm API SEGS _ _ _ L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k0 RPg Hq Hk).
    - intros [(LV & E') | [E' | E']]; [exact (NOq LV E') | exact (NH E') | exact (NK E')].
    - intros j Hj. exact (NE2 q k0 j Hq NG NOq Hj). }
  assert (LATER : forall q, In q (concat (map entry_blocks (skipn (S i) es))) ->
            ~ In q (Pfx i ++ entry_blocks e) /\ q <> OUT /\ q <> G).
  { intros q Hq. pose proof fi_ND as ND. rewrite (fi_cat_split i Hi), app_assoc in ND.
    assert (HC : In q (concat (map entry_blocks es))).
    { rewrite (fi_cat_split i Hi). apply in_or_app. right. apply in_or_app. right. exact Hq. }
    split; [exact (fi_nd_app _ _ q ND Hq)|].
    split; [intros ->; exact (proj2 HDJ HC) | intros ->; exact (GN HC)]. }
  assert (EST2 : Forall (fi_est L2 A2 m2) (skipn (S i) es)).
  { apply Forall_forall. intros e' He'. rewrite Forall_forall in EST1, EOK3.
    eapply fi_est_tr; [exact (EOK3 e' He') | exact (EST1 e' He') |].
    intros q k0 Hk Hq Hin.
    assert (HC : In q (concat (map entry_blocks (skipn (S i) es)))) by exact (fi_in_cat _ _ _ He' Hin).
    destruct (LATER q HC) as (NP & NOq & NG).
    destruct (fi_eb_blk0 e' q (EOK3 e' He') Hin) as (k2 & Hk2 & Hq0).
    apply KEEPB; [exact Hq | exact Hk | exact NG | | |].
    - intros _. apply (NOT1 q k2 Hq0 Hk2 NOq). intros X. apply NP.
      apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X | right; exact (BLI q X)].
    - intros E'. destruct (Z.eq_dec (re_hp e) 0) as [Z0|Z0].
      + pose proof (fi_blk_4k _ _ _ _ _ _ M1 Hq). lia.
      + apply NP. apply in_or_app. right. rewrite E'. exact (HPI Z0).
    - intros X. apply NP. apply in_or_app. right. exact (KAI q X). }
  assert (GNF : ~ ((lv1 = true /\ G = bv_unsigned out1) \/ G = re_hp e \/ In G (map key_addr (re_keys e)))).
  { intros [(_ & E') | [E' | E']]; [exact (GNO E') | exact (GNH E') | exact (GNK E')]. }
  destruct (fi_rp_keep2 Bm API SEGS _ _ _ L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 G SRC_TABLE RPg HG1
    ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) GNF) as [HG2 KG].
  assert (TAB2 : C = 16 -> table_at Bm m2 G (Tab (S i)) tail /\ In (G, SRC_TABLE) (blocks L2 A2)).
  { intros _. split; [|exact HG2]. split.
    - rewrite (fi_tab_len (S i)), <- (fi_tab_len i). exact TL.
    - rewrite TS1, SEGS. apply (fi_tab_upd m1 m2 G _ _ _ tail TR FP1 FPe).
      + rewrite TL1. exact SA2.
      + intros j Hj Hn. rewrite TL1 in Hn. apply KG; [unfold SRC_TABLE, SRC_ENTRY; lia|].
        intros HE. unfold gestures_writes, send_writes in HE.
        destruct HE as [[X|[X|[X|(LV & X)]]]|X].
        * apply (FG3 j ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)).
          exact (proj1 (IMGR (G + j) ltac:(unfold G_BROKEN in X; unfold G_RELAY_LO, G_LOCK_HI; lia))).
        * apply (FG3 j ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)).
          exact (proj1 (IMGR (G + j) ltac:(unfold G_EINTR in X; unfold G_RELAY_LO, G_LOCK_HI; lia))).
        * apply (FG3 j ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)).
          exact (proj1 (IMGR (G + j) ltac:(unfold G_OUTV in X; unfold G_RELAY_LO, G_LOCK_HI; lia))).
        * destruct HO1 as [(C0 & _) | (H1 & _ & H3 & _)]; [lia|].
          destruct (fi_blk_disj Bm API L1 A1 m1 md1 _ _ _ _ M1 HG1 H3 GNO) as [D|D];
            unfold SRC_TABLE, SRC_ENTRY in D; lia.
        * lia.
      + intros j Hj. apply fi_pw. exact (proj1 (fi_blk Bm API L2 A2 m2 md2 G SRC_TABLE j M2 HG2 Hj)). }
  assert (GLB2 : forall a, (G_RELAY_LO <= a < G_LOCK_HI \/ G_LISTEN <= a < G_CLIENT + 4 \/ SP - 48 <= a < SP) ->
            ~ (G_BROKEN <= a < G_BROKEN + 1) -> ~ (G_EINTR <= a < G_EINTR + 1) -> ~ (G_OUTV + 8 <= a < G_OUTV + 32) ->
            (img_plain Bm a \/ YM05.alloc_ceiling <= a < 2 ^ 64) /\
            ~ gestures_writes lv1 (bv_unsigned out1) (bv_unsigned cap1) (G + 56 * Z.of_nat i) a /\
            ~ scratch_k Bm GESTURES_END_K R1 a).
  { intros a Ha N1 N2 N3.
    assert (HA : img_plain Bm a \/ YM05.alloc_ceiling <= a < 2 ^ 64).
    { destruct Ha as [Ha|[Ha|Ha]]; [left; exact (IMGR a Ha) | left; exact (IMGL a Ha) | right; lia]. }
    split; [exact HA|]. split.
    - intros HE. unfold gestures_writes, send_writes in HE.
      destruct HE as [[X|[X|[X|(LV & X)]]]|X]; [exact (N1 X) | exact (N2 X) | exact (N3 X) | |].
      + destruct HO1 as [(C0 & _) | (H1 & _ & H3 & _)]; [lia|].
        destruct (fi_blk_low L1 A1 m1 md1 _ _ (a - bv_unsigned out1) M1 H3 ltac:(lia)) as [Hb Hi'].
        replace (bv_unsigned out1 + (a - bv_unsigned out1)) with a in Hb, Hi' by lia.
        destruct HA as [HA|HA]; [exact (Hi' (proj1 HA)) | lia].
      + destruct HA as [HA|HA]; [|lia].
        apply (FG3 (a - G) ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)). replace (G + (a - G)) with a by lia.
        exact (proj1 HA).
    - unfold scratch_k. rewrite SPR, fi_GK.
      destruct Ha as [Ha|[Ha|Ha]]; unfold G_RELAY_LO, G_LOCK_HI, G_LISTEN, G_CLIENT in Ha; lia. }
  assert (CTU2 : rw_cells rsegs m2 G_THREAD_UP [C1 (Z_to_bv 8 0)]).
  { apply (fi_rp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RPg); [|exact CTU1].
    intros jj Hjj. cbn in Hjj. apply GLB2; unfold G_THREAD_UP, G_RELAY_LO, G_LOCK_HI, G_BROKEN, G_EINTR, G_OUTV; lia. }
  assert (CLK2 : rw_cells rsegs m2 G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)]).
  { apply (fi_rp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RPg); [|exact CLK1].
    intros jj Hjj. cbn in Hjj. apply GLB2; unfold G_LOCK, G_RELAY_LO, G_LOCK_HI, G_BROKEN, G_EINTR, G_OUTV; lia. }
  assert (CNS2 : rw_cells rsegs m2 G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 C)]).
  { apply (fi_rp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RPg); [|exact CNS1].
    intros jj Hjj. cbn in Hjj. apply GLB2; unfold G_NSRC, G_RELAY_LO, G_LOCK_HI, G_BROKEN, G_EINTR, G_OUTV; lia. }
  assert (CSR2 : rw_cells rsegs m2 G_SRC [C8 (Z_to_bv 64 G)]).
  { apply (fi_rp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RPg); [|exact CSR1].
    intros jj Hjj. cbn in Hjj. apply GLB2; unfold G_SRC, G_RELAY_LO, G_LOCK_HI, G_BROKEN, G_EINTR, G_OUTV; lia. }
  assert (CLS2 : rw_cells rsegs m2 G_LISTEN [C4 (Z_to_bv 64 lst); C4 (Z_to_bv 64 cl)]).
  { apply (fi_rp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RPg); [|exact CLS1].
    intros jj Hjj. cbn in Hjj. apply GLB2; unfold G_LISTEN, G_CLIENT, G_BROKEN, G_EINTR, G_OUTV; lia. }
  assert (FR2 : rw_cells rsegs m2 (SP + -40) [C8 (reg_get regs0 19); C8 (reg_get regs0 18);
                                C8 (reg_get regs0 9); C8 (reg_get regs0 8); C8 (reg_get regs0 1)]).
  { apply (fi_rp_cells Bm API SEGS AX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RPg); [|exact FR1].
    intros jj Hjj. cbn in Hjj. apply GLB2; unfold G_BROKEN, G_EINTR, G_OUTV; lia. }
  assert (CBR2 : rw_cells rsegs m2 G_BROKEN [C1 (Z_to_bv 8 (brT (Tfx (S i))))]).
  { replace (brT (Tfx (S i))) with (if send_off cl (brT (Tfx i)) (keys_total (re_keys e)) then brT (Tfx i) else dd);
      [exact BR2|]. unfold brT. rewrite TS'. apply fi_br_step; assumption. }
  assert (CEI2 : rw_cells rsegs m2 G_EINTR [C1 (Z_to_bv 8 (eiT (Tfx (S i))))]).
  { replace (eiT (Tfx (S i))) with (if send_off cl (brT (Tfx i)) (keys_total (re_keys e)) then eiT (Tfx i) else 0);
      [exact EI2|]. unfold eiT, brT. rewrite TS'. apply fi_ei_step; assumption. }
  assert (LVS : lvT (Tfx (S i)) = lvT (Tfx i) || lv1).
  { rewrite LV1. unfold lvT, brT. rewrite TS'. apply fi_live_step; assumption. }
  (* The frame of relay_finish after the call. *)
  assert (RP2 : relay_post Bm API RELAY_FINISH_K Efin Ffin L0 A0 regs0 mem0 md0 L2 A2 regs0 m2 md2).
  { apply (fi_comp Bm API _ _ _ _ _ _ _ _ _ _ _ _ GESTURES_END_K R1 _ _ _ _ _ _ _ RP RPg).
    - intros a Ha. change (spZ regs0) with SP in Ha. rewrite fi_K in Ha. lia.
    - intros a Ha. unfold scratch_k in Ha |- *. rewrite SPR, fi_GK in Ha. change (spZ regs0) with SP. rewrite fi_K.
      lia.
    - intros a Ha Hn HE. unfold scratch_k in Ha, Hn. rewrite SPR, fi_GK in Hn. change (spZ regs0) with SP in Ha.
      rewrite fi_K in Ha. unfold gestures_writes, send_writes in HE.
      destruct HE as [[X|[X|[X|(LV & X)]]]|X]; [unfold G_BROKEN in X; lia | unfold G_EINTR in X; lia |
        unfold G_OUTV in X; lia | | lia].
      destruct HO1 as [(C0 & _) | (_ & _ & _ & (F1 & F2 & _) & _)]; lia.
    - intros p n Hn H0 H1 NF HF.
      assert (Hq : In (ptr_addr L0 p, n) (blocks L0 A0))
        by (apply fi_blocks_in; exists p; split; [reflexivity | exact H0]).
      destruct HF as [(LV & E') | [E' | E']].
      + assert (LVt : live = true) by (apply LS; rewrite LVS, LV; apply orb_true_r).
        apply (NOT1 _ n Hq Hn).
        * intros E2'. apply NF. left. split; [exact LVt | exact E2'].
        * intros X. apply NF. right. exact (PC _ X).
        * exact E'.
      + apply NF. right. apply EBC. rewrite E'. apply HPI. intros Z0.
        pose proof (fi_blk_4k _ _ _ _ _ _ HMR Hq). lia.
      + apply NF. right. apply EBC. apply KAI. exact E'.
    - intros a Ha NO0 NS HE. unfold gestures_writes, send_writes in HE. cbv beta. unfold send_writes.
      destruct HE as [[X|[X|[X|(LV & X)]]]|X].
      + left. left. exact X.
      + left. right. left. exact X.
      + left. right. right. left. exact X.
      + destruct (lvT (Tfx i)) eqn:LVo.
        * exfalso. destruct (LVT1 eq_refl) as (_ & (F1 & F2 & F3) & _).
          destruct Ha as [Ha|Ha]; [lia|].
          apply (F3 (a - bv_unsigned out1)); [lia|]. replace (bv_unsigned out1 + (a - bv_unsigned out1)) with a by lia.
          exact Ha.
        * destruct (LVF1 eq_refl) as (_ & Ec & Eo & _). rewrite Ec, Eo in X.
          left. right. right. right. split; [apply LS; rewrite LVS, LV; apply orb_true_r | exact X].
      + right. right. right. right. split; [exact C16|]. unfold SRC_TABLE, SRC_ENTRY. lia.
    - intros p n i0 H0 H1 NF Hi0 HE. unfold gestures_writes, send_writes in HE. cbv beta. unfold send_writes.
      destruct HE as [[X|[X|[X|(LV & X)]]]|X].
      + left. left. exact X.
      + left. right. left. exact X.
      + left. right. right. left. exact X.
      + destruct (lvT (Tfx i)) eqn:LVo.
        * exfalso. destruct HO1 as [(C0 & _) | (_ & _ & H3 & _)]; [lia|].
          assert (Hq1 : In (ptr_addr L0 p, n) (blocks L1 A1))
            by (apply fi_blocks_in; exists p; split; [exact (AD1 p n H0 H1 NF) | exact H1]).
          assert (Hq0 : In (ptr_addr L0 p, n) (blocks L0 A0))
            by (apply fi_blocks_in; exists p; split; [reflexivity | exact H0]).
          assert (NE : ptr_addr L0 p <> bv_unsigned out1).
          { apply (NOT1 _ n Hq0 ltac:(lia)).
            - intros E'. apply NF. left. split; [exact (LT eq_refl) | exact E'].
            - intros Xp. apply NF. right. exact (PC _ Xp). }
          destruct (fi_blk_disj Bm API L1 A1 m1 md1 _ _ _ _ M1 Hq1 H3 NE) as [D|D]; lia.
        * destruct (LVF1 eq_refl) as (_ & Ec & Eo & _). rewrite Ec, Eo in X.
          left. right. right. right. split; [apply LS; rewrite LVS, LV; apply orb_true_r | exact X].
      + right. right. right. right. split; [exact C16|]. unfold SRC_TABLE, SRC_ENTRY. lia. }
  assert (BLKN : forall q m, In (q, m) (blocks L2 A2) <->
      (In (q, m) (blocks L0 A0) /\ q <> OUT /\ ~ In q (Pfx (S i))) \/
      (lvT (Tfx i) || lv1 = true /\ q = (if lv1 then OUT' else bv_unsigned out1) /\
       m = (if lv1 then CAP' else bv_unsigned cap1)) \/
      (lvT (Tfx i) || lv1 = false /\ 0 < CAP /\ q = OUT /\ m = CAP)).
  { apply (fi_blk_step (fun q m => In (q, m) (blocks L0 A0)) (fun q m => In (q, m) (blocks L1 A1))
      (fun q m => In (q, m) (blocks L2 A2)) (fun q => In q (Pfx i ++ bufl e)) (fun q => In q (Pfx (S i)))
      (fun q => In q (map key_addr (re_keys e))) (lvT (Tfx i)) lv1 OUT CAP (bv_unsigned out1) (bv_unsigned cap1)
      OUT' CAP' (re_hp e)).
    - exact BLK1.
    - exact BLK2.
    - intros q m Hq. cbv beta in Hq |- *. pose proof (fi_blk_4k _ _ _ _ _ _ HMR Hq) as QB. rewrite PSI. split.
      + intros [X|X]; [left; exact X | right]. apply in_app_or in X as [X|X]; [left | right; exact X].
        unfold hpl in X. revert X. destruct (Z.eqb_spec (re_hp e) 0) as [_|_]; intros X;
          [destruct X | destruct X as [X|[]]; symmetry; exact X].
      + intros [X|[X|X]]; [left; exact X | right; apply in_or_app; left | right; apply in_or_app; right; exact X].
        subst q. unfold hpl. destruct (Z.eqb_spec (re_hp e) 0) as [E0|E0]; [lia | left; reflexivity].
    - intros LV. destruct (LVF1 LV) as (_ & -> & -> & _). split; reflexivity.
    - intros LV. destruct (LVT1 LV) as (E1 & _).
      pose proof (fi_live_nz cl br dd (Tfx i) LV) as NZ.
      destruct HO1 as [(_ & _ & N0 & _) | (H1 & _ & H3 & _)]; [lia|].
      split; [exact H1|]. intros m Hm.
      exact (fi_blk_eq L1 A1 _ m _ (fi_nodup _ (HND L1 A1 m1 md1 M1)) Hm H3).
    - intros LV m Hm NOq NP Hm'. destruct (LVT1 LV) as (_ & _ & DJ & _). exact (DJ _ m Hm NOq NP Hm' eq_refl). }
  (* The resource state after the call. *)
  assert (RUNY : forall ext,
            p3c_run RFm (qs ++ qc ++ ext) (runF RFm qs bnd tp) (length qs)
              (gestures_end_tr live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs nm0 (re_keys e))
                 (re_hp e) (re_kh e) (length qs) o (nm0 (re_hp e))) =
            runF RFm qc (runF RFm qs bnd tp)
              (gestures_end_tr lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1)
                 (key_runs (known_at L1 A1) (re_keys e)) (re_hp e) (re_kh e) 0 (known_at L1 A1 (bv_unsigned out1))
                 (known_at L1 A1 (re_hp e)))).
  { intros ext. rewrite p3c_run_res, (proj1 (RESX qc ext QL)), <- p3c_run_res. reflexivity. }
  assert (RUNX : forall ext,
            p3c_run RFm (qs ++ qc ++ ext) bnd 0
              (tp ++ gestures_end_tr live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs nm0 (re_keys e))
                 (re_hp e) (re_kh e) (length qs) o (nm0 (re_hp e))) =
            runF RFm qc (runF RFm qs bnd tp)
              (gestures_end_tr lv1 (bv_unsigned mx) (bv_unsigned nout1) (bv_unsigned cap1)
                 (key_runs (known_at L1 A1) (re_keys e)) (re_hp e) (re_kh e) 0 (known_at L1 A1 (bv_unsigned out1))
                 (known_at L1 A1 (re_hp e)))).
  { intros ext. rewrite run_from_app, (RST (qc ++ ext)), RNq. exact (RUNY ext). }
  pose proof (RUNX []) as R0. rewrite app_nil_r in R0.
  (* The requests still to come after the call. *)
  assert (RSN : forall c2 out2,
            c2 = gestures_end_cap live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_lens (re_keys e)) ->
            (c2 <> 0 -> live_at L2 A2 (resolveF (qs ++ qc) (gestures_end_out live (bv_unsigned mx) (NO + Tfx i)
                         (bv_unsigned cap1) (key_runs nm0 (re_keys e)) (length qs) o)) out2 c2) ->
            RSt L2 A2 (er (skipn (S i) es) (NO + Tfx (S i)) c2) c2 out2 (Pfx (S i))).
  { intros c2 out2 Ec2 LKo. subst c2. unfold RSt.
    exists (tp ++ gestures_end_tr live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs nm0 (re_keys e))
                   (re_hp e) (re_kh e) (length qs) o (nm0 (re_hp e))), (qs ++ qc),
      (gestures_end_out live (bv_unsigned mx) (NO + Tfx i) (bv_unsigned cap1) (key_runs nm0 (re_keys e)) (length qs) o).
    rewrite length_app, TS'.
    replace (NO + (Tfx i + keys_total (re_keys e))) with (NO + Tfx i + keys_total (re_keys e)) by lia.
    destruct (RESX qc [] QL) as (_ & F2 & F3). rewrite app_nil_r in F3. rewrite <- F2.
    split; [rewrite nret_app, RNq; reflexivity|].
    split; [rewrite p3c_runF, R0; exact RS2|].
    split; [intros ext; rewrite <- app_assoc, RUNX, <- R0; reflexivity|].
    split; [intros HC ext; rewrite <- app_assoc, (proj2 (proj2 (RESX qc ext QL)) HC), (F3 HC); reflexivity|].
    split.
    { intros rest Hr. rewrite <- app_assoc.
      pose proof (RT2 (qc ++ rest) ltac:(rewrite length_app, nret_app, Hr, F2; reflexivity)) as HR.
      apply room_from_app in HR. destruct HR as [_ HR]. rewrite RUNY in HR. rewrite p3c_runF, R0. exact HR. }
    split; [rewrite <- app_assoc; exact RT3|]. split; [exact RT4|]. split; [exact RT5|].
    split; [exact LKo|].
    intros q m Hq NOq NP Hm.
    assert (NP1 : ~ In q (Pfx i ++ bufl e)) by (intros X; apply NP; apply PSub; exact X).
    assert (NHK : ~ In q (hpl e ++ map key_addr (re_keys e))) by (intros X; apply NP; apply PSI; right; exact X).
    apply (p3c_rp_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPg (KN1 q m Hq NOq NP1 Hm) Hm).
    intros HF. cbv beta in HF. destruct HF as [(LV & E') | [E' | E']].
    - exact (NOT1 q m Hq Hm NOq NP1 E').
    - apply NHK. subst q. apply HPL. pose proof (fi_blk_4k _ _ _ _ _ _ HMR Hq). lia.
    - apply NHK. apply KL. exact E'. }
  (* The invariant after the call. *)
  assert (HNEW : exists nout2 cap2 out2 O2 junk2,
      CI L2 A2 m2 md2 (er (skipn (S i) es) (NO + Tfx (S i)) (bv_unsigned cap2)) nout2 cap2 out2 O2 junk2
        (Pfx (S i)) (Tfx (S i)) (Efx (S i)) (Tab (S i))).
  { destruct lv1.
    - destruct (LT2 eq_refl) as (NC & ECAP & FB2 & DJ2 & BY2' & JL2 & OV2).
      pose proof (fi_live_nz cl (brT (Tfx i)) dd _ (eq_sym LV1)) as KNZ.
      pose proof FB2 as (F1' & F2' & _).
      assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned nout1 + keys_total (re_keys e))) =
                   bv_unsigned nout1 + keys_total (re_keys e)) by (apply unsigned_lit; lia).
      assert (U2 : bv_unsigned (Z_to_bv 64 CAP') = CAP') by (apply unsigned_lit; lia).
      assert (U3 : bv_unsigned (Z_to_bv 64 OUT') = OUT') by (apply unsigned_lit; lia).
      assert (NO1E : bv_unsigned nout1 + keys_total (re_keys e) = NO + Tfx (S i)).
      { rewrite TS'. destruct (lvT (Tfx i)) eqn:LVo.
        - destruct (LVT1 eq_refl) as (E1 & _). lia.
        - destruct (LVF1 eq_refl) as (-> & _).
          pose proof (fi_live_t1 cl br dd (Tfx i) _ Hcl Hbr Hdd TN KN (eq_sym LV1) LVo) as T0. lia. }
      assert (O1E : O1 ++ keys_out (re_keys e) = O ++ Efx (S i)).
      { rewrite ES. destruct (lvT (Tfx i)) eqn:LVo.
        - destruct (LVT1 eq_refl) as (_ & _ & _ & ->). rewrite <- app_assoc. reflexivity.
        - destruct (LVF1 eq_refl) as (_ & _ & _ & -> & _).
          pose proof (fi_live_t1 cl br dd (Tfx i) _ Hcl Hbr Hdd TN KN (eq_sym LV1) LVo) as T0.
          unfold Tfx in T0. unfold Efx. rewrite (fi_et_zero _ T0). reflexivity. }
      exists (Z_to_bv 64 (bv_unsigned nout1 + keys_total (re_keys e))), (Z_to_bv 64 CAP'),
        (Z_to_bv 64 OUT'), (O1 ++ keys_out (re_keys e)), junk'.
      assert (LKN : CAP' <> 0 -> live_at L2 A2 (resolveF (qs ++ qc) (gestures_end_out live (bv_unsigned mx)
                      (NO + Tfx i) (bv_unsigned cap1) (key_runs nm0 (re_keys e)) (length qs) o)) OUT' CAP').
      { intros HC. destruct (RESX qc [] QL) as (_ & _ & F3). rewrite app_nil_r in F3.
        rewrite F3 by (rewrite <- (GCAP eq_refl), <- ECAP; exact HC). exact (LK2 eq_refl). }
      unfold CI. rewrite U1, U2, U3, LVS.
      split; [exact RP2|]. split; [exact IN2|]. split; [exact (RSN CAP' OUT' (eq_trans ECAP (GCAP eq_refl)) LKN)|].
      split; [exact RA2|].
      split; [exact CTU2|]. split; [exact CLK2|]. split; [exact CNS2|]. split; [exact CSR2|]. split; [exact CLS2|].
      split; [exact CBR2|]. split; [exact DD2|]. split; [exact CEI2|]. split; [exact OV2|]. split; [exact ER2|].
      split; [exact FR2|]. split; [exact TAB2|]. split; [exact BLKN|].
      split; [intros X; rewrite orb_true_r in X; discriminate X|].
      split.
      + intros _. split; [exact NO1E|]. split; [exact FB2|]. split; [|exact O1E].
        intros q m Hq NOq NP Hm.
        assert (NP1 : ~ In q (Pfx i ++ bufl e)) by (intros X; apply NP; apply PSub; exact X).
        apply (DJ2 q m); [apply BLK1; left; split; [exact Hq | split; [exact NOq | exact NP1]] |
          exact (NOT1 q m Hq Hm NOq NP1) | | | exact Hm].
        * intros E'. apply NP. apply PSI. right. subst q. apply HPL.
          pose proof (fi_blk_4k _ _ _ _ _ _ HMR Hq). lia.
        * intros X. apply NP. apply PSI. right. exact (KL _ X).
      + right. split; [lia|]. split; [lia|].
        split; [apply BLK2; right; left; split; [reflexivity | split; reflexivity]|].
        split; [exact FB2|]. split; [rewrite <- app_assoc; exact BY2'|].
        split; [rewrite length_app; pose proof (fi_ko_len (re_keys e)); lia | lia].
    - pose proof (LF2 eq_refl) as OV2.
      exists nout1, cap1, out1, O1, junk1.
      assert (LKF : bv_unsigned cap1 <> 0 ->
                    live_at L2 A2 (resolveF (qs ++ qc) (gestures_end_out live (bv_unsigned mx) (NO + Tfx i)
                      (bv_unsigned cap1) (key_runs nm0 (re_keys e)) (length qs) o)) (bv_unsigned out1) (bv_unsigned cap1)).
      { intros HC. rewrite <- (GOUT nm0 (length qs) o). unfold gestures_end_out. rewrite fi_ker_false. cbn [fst snd].
        rewrite (RSO HC qc).
        destruct HO1 as [(C0 & _) | (H1 & _ & H3 & _)]; [lia|].
        assert (QO : 4096 <= bv_unsigned out1) by exact (fi_blk_4k _ _ _ _ _ _ M1 H3).
        apply (p3c_rp_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPg (RT6 HC) H1).
        intros HF. cbv beta in HF. destruct HF as [(LV & _) | [E' | E']]; [discriminate LV | |].
        - destruct (Z.eq_dec (re_hp e) 0) as [Z0|Z0]; [lia | exact (ENO1 _ (HPL Z0) (eq_sym E'))].
        - exact (ENO1 _ (KL _ E') eq_refl). }
      unfold CI. rewrite LVS.
      split; [exact RP2|]. split; [exact IN2|].
      split; [exact (RSN (bv_unsigned cap1) (bv_unsigned out1) (eq_sym (GCAP0 eq_refl)) LKF)|].
      split; [exact RA2|].
      split; [exact CTU2|]. split; [exact CLK2|]. split; [exact CNS2|]. split; [exact CSR2|]. split; [exact CLS2|].
      split; [exact CBR2|]. split; [exact DD2|]. split; [exact CEI2|]. split; [exact OV2|]. split; [exact ER2|].
      split; [exact FR2|]. split; [exact TAB2|]. split; [exact BLKN|].
      split; [intros X; rewrite orb_false_r in X; exact (LVF1 X)|].
      split.
      + intros X. pose proof (eq_trans LVS X) as XS. rewrite orb_false_r in X.
        destruct (LVT1 X) as (E1 & FB1 & DJ1 & EO1).
        assert (KT0 : keys_total (re_keys e) = 0).
        { apply (fi_live_t2 cl br dd (Tfx i) _ Hcl Hbr Hdd TN KN (eq_sym LV1)).
          unfold lvT in XS. rewrite TS' in XS. exact XS. }
        assert (KO0 : keys_out (re_keys e) = []) by (rewrite (fi_kt_zero _ KT0); reflexivity).
        split; [rewrite TS', KT0; lia|]. split; [exact FB1|].
        split; [intros q m Hq NOq NP Hm; apply (DJ1 q m Hq NOq); [intros Y; apply NP; apply PSub; exact Y | exact Hm]|].
        rewrite ES, KO0, app_nil_r. exact EO1.
      + destruct HO1 as [H|(H1 & H2 & H3 & H4 & H5 & H6 & H7)]; [left; exact H | right].
        assert (QO : 4096 <= bv_unsigned out1) by exact (fi_blk_4k _ _ _ _ _ _ M1 H3).
        assert (NH1 : bv_unsigned out1 <> re_hp e).
        { intros E'. destruct (Z.eq_dec (re_hp e) 0) as [Z0|Z0]; [lia | exact (ENO1 _ (HPL Z0) (eq_sym E'))]. }
        destruct (KEEPB _ _ H3 H1 (fun E' => GNO (eq_sym E')) ltac:(intros X; discriminate X) NH1
          (fun X => ENO1 _ (KL _ X) eq_refl)) as [H3' K3].
        split; [exact H1|]. split; [exact H2|]. split; [exact H3'|]. split; [exact H4|].
        split; [|split; [exact H6 | exact H7]].
        apply (fi_bytes_blk m1 m2 (bv_unsigned out1) (bv_unsigned cap1)); [lia | rewrite length_app; lia | exact K3 |
          exact H5]. }
  destruct HNEW as (nout2 & cap2 & out2 & O2 & junk2 & HCI2).
  (* The index step at 78196. *)
  destruct (fi_RL_pres R1 R2 RPr HRL) as (RL2 & Y18 & Y19). rewrite R18 in Y18. rewrite R19 in Y19.
  pose proof RL2 as (Y2 & Y3 & Y4 & Y8 & Y9 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
  rewrite ?G1a, ?G1b.
  assert (EZ : Z.of_nat (S i) = Z.of_nat i + 1) by lia.
  destruct (Nat.eq_dec (S i) (length es)) as [EN|EN].
  - eapply fi_bridge; [exact RA2 | exact Hh2 | exact Hl2 | |].
    { unfold Regs6ss.mkR_of. rewrite Y9, Y18, Y19. eapply fi_tl0.
      - apply fi_rw_norm; [exact RA2 | exact CNS2 |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia.
      - lia.
      - lia.
      - lia. }
    intros s0 R' m' HQ X MRl RSm. destruct HQ as (a0' & s2' & s3' & ->).
    destruct (fi_rsame m2 m' _ RA2 MRl eq_refl RSm) as (MU & WM & RA').
    apply SR_ret. right. split; [exact EN|].
    exists L2, A2, R', m', md2, nout2, cap2, out2, O2, junk2. split; [reflexivity|].
    split; [unfold RL; repeat split; rgx X|].
    rewrite <- EN. exact (fi_CI_tr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCI2 MU WM RA').
  - eapply fi_bridge; [exact RA2 | exact Hh2 | exact Hl2 | |].
    { unfold Regs6ss.mkR_of. rewrite Y9, Y18, Y19. eapply fi_tl1.
      - apply fi_rw_norm; [exact RA2 | exact CNS2 |]. intros j Hj. cbn in Hj. apply fi_ro_glob. lia.
      - lia.
      - lia.
      - lia. }
    intros s0 R' m' HQ X MRl RSm. destruct HQ as [a0' ->].
    destruct (fi_rsame m2 m' _ RA2 MRl eq_refl RSm) as (MU & WM & RA').
    apply SR_ret. left. split; [lia|].
    exists L2, A2, R', m', md2, nout2, cap2, out2, O2, junk2. split; [reflexivity|].
    split; [unfold RL; repeat split; rgx X|].
    rewrite EZ.
    split; [rgx X|]. split; [rgx X|].
    split; [exact (fi_CI_tr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCI2 MU WM RA')|].
    exact (fi_est_tr0 _ _ _ _ _ EST2 MU).
Qed.

Lemma fi_s_loop : forall n i c, (length es - i = n)%nat -> (i < length es)%nat -> LoopSt i c -> SR rsegs c ExitSt.
Proof using AX CTXO FREEPC HDJ HEOK HERR HERR4 HFREE HFREEN HGE HN4 HND HOUT HREQ HTAB Hbr Hcl Hdd Hei IMG5 IMGE IMGL IMGR PRE SEGS SLK TPE.
  induction n as [|n IH]; intros i c En Hi HL; [lia|].
  eapply SR_bind; [exact (fi_s_free i c Hi HL)|]. intros c1 HF.
  eapply SR_bind; [exact (fi_s_ge i c1 Hi HF)|]. intros c2 [(Hi' & HL2) | (_ & HX)].
  - exact (IH (S i) c2 ltac:(lia) Hi' HL2).
  - apply SR_ret. exact HX.
Qed.

Lemma fi_main : SR rsegs (mkCfg (YK11.mkst regs0 (Z_to_bv 64 RELAY_FINISH) mem0 (seg_rom rsegs)) md0) Final.
Proof using AX CBR CDD CEI CER CLK CLS CNS COV CSR CTU CTXO FREEPC HDJ HEOK HERR HERR4 HFREE HFREEN HGE HN4 HND HOUT HREQ HRES HROOM HTAB Hbr Hcl Hdd Hei IMG5 IMGE IMGL IMGR INIT PRE RA SEGS SLK SPL SPU TPE.
  eapply SR_bind; [exact fi_s_head|]. intros c1 HH.
  eapply SR_bind; [exact (fi_s_chk c1 HH)|]. intros c2 HC.
  eapply SR_bind with (R := ExitSt).
  - destruct HC as [(Hn & HL) | (_ & HX)].
    + exact (fi_s_loop _ 0 c2 eq_refl Hn HL).
    + apply SR_ret. exact HX.
  - intros c3 HX. exact (fi_s_exit c3 HX).
Qed.

End Run.

Theorem relay_finish_holds (Fm : ResFormT) : pthread_mutex_lock_contract -> pthread_mutex_unlock_contract ->
  free_contract_rt Bm API Fm -> free_null_contract Bm -> gestures_end_contract Bm API Fm ->
  relay_finish_contract Bm API Fm.
Proof using AX CTXO FREEPC HND SLK.
  intros SPL SPU HFREE HFREEN HGE. unfold relay_finish_contract. cbv zeta.
  intros L A regs mem md bnd es C G tail O junk lst cl br dd ei mx nout cap out SEGS PRE INIT TPE HERR4 HERR RA IMGR IMGL
    IMGE IMG5 CTU CLK CNS CSR CLS HN4 HTAB HEOK HDJ Hcl Hbr Hdd Hei CBR CDD CEI COV CER HOUT HREQ HRES HROOM.
  rewrite SEGS in *.
  eapply fi_main; eassumption.
Qed.
End FinB.
