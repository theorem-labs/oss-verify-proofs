(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallPure. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallWin_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmallW Require Import SmallPtW_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VKW.
Import PMR.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u8_feeds_app : forall v l1 l2, u8_feeds v (l1 ++ l2) = u8_feeds (u8_feeds v l1) l2.
Proof. intros v l1; revert v; induction l1 as [|b r IH]; intros v l2; cbn; [reflexivity | apply IH]. Qed.
Lemma b256_app : forall l1 l2, b256 (l1 ++ l2) = b256 l1 ++ b256 l2.
Proof. intros. unfold b256. apply map_app. Qed.
Lemma b256_firstn : forall n l, b256 (firstn n l) = firstn n (b256 l).
Proof. intros. unfold b256. rewrite firstn_map. reflexivity. Qed.
Lemma b256_skipn : forall n l, b256 (skipn n l) = skipn n (b256 l).
Proof. intros. unfold b256. rewrite skipn_map. reflexivity. Qed.
(* [comment removed for export] *)
Lemma validate_split : forall n txt, u8_feeds u8_init (b256 (firstn n txt)) = u8_init ->
  validate txt = u8_finish (u8_feeds u8_init (b256 (skipn n txt))).
Proof. intros n txt H. unfold validate. rewrite <- (firstn_skipn n txt) at 1. rewrite b256_app, u8_feeds_app, H. reflexivity. Qed.
(* [comment removed for export] *)
Lemma u8_feeds_err : forall v l, u_err v <> 0 -> u8_feeds v l = v.
Proof.
  intros v l H. induction l as [|b r IH]; cbn; [reflexivity|]. unfold u8_feed at 1.
  replace (negb (u_err v =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact H). exact IH.
Qed.
(* [comment removed for export] *)
Lemma u8_feeds_pend : forall p need l, p <> [] -> Z.of_nat (length p) + Z.of_nat (length l) < need ->
  u8_feeds (U8 0 p need) l = U8 0 (p ++ l) need.
Proof.
  intros p need l. revert p. induction l as [|b r IH]; intros p Hp Hl.
  - cbn. rewrite app_nil_r. reflexivity.
  - cbn [u8_feeds]. destruct p as [|p0 pr]; [congruence|]. cbn [length] in Hl.
    assert (E1 : u8_feed (U8 0 (p0 :: pr) need) b = U8 0 ((p0 :: pr) ++ [b]) need).
    { unfold u8_feed. cbn [u_err u_pend u_need Z.eqb negb]. replace (Z.of_nat (length ((p0 :: pr) ++ [b])) =? need) with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. rewrite length_app. cbn [length]. lia. }
    rewrite E1. rewrite IH; [| discriminate | rewrite length_app; cbn [length]; lia]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma finish_pend : forall p need, p <> [] -> u8_finish (U8 0 p need) = 5.
Proof. intros p need Hp. unfold u8_finish. cbn. destruct p; [congruence | reflexivity]. Qed.
(* [comment removed for export] *)
Definition canon1 (b : Z) : Z := if b <? 128 then 0 else if b <? 144 then 128 else if b <? 160 then 144 else if b <? 192 then 160 else 192.
Definition canon2 (b : Z) : Z := if is_cont b then 128 else 0.
Lemma is_cont_canon1 : forall b, is_cont (canon1 b) = is_cont b.
Proof. intros b. unfold canon1, is_cont. destruct (b <? 128) eqn:E1; [|destruct (b <? 144) eqn:E2; [|destruct (b <? 160) eqn:E3; [|destruct (b <? 192) eqn:E4]]]; cbn;
  apply Z.ltb_lt in E1 || apply Z.ltb_ge in E1; try (apply Z.ltb_lt in E2 || apply Z.ltb_ge in E2); try (apply Z.ltb_lt in E3 || apply Z.ltb_ge in E3); try (apply Z.ltb_lt in E4 || apply Z.ltb_ge in E4);
  symmetry; first [apply andb_false_intro1; apply Z.leb_gt; lia | apply andb_false_intro2; apply Z.leb_gt; lia | apply andb_true_intro; split; apply Z.leb_le; lia]. Qed.
Lemma is_cont_canon2 : forall b, is_cont (canon2 b) = is_cont b.
Proof. intros b. unfold canon2. destruct (is_cont b) eqn:E; cbn; reflexivity. Qed.
Lemma forallb_is_cont_canon2 : forall r, forallb is_cont (map canon2 r) = forallb is_cont r.
Proof. induction r as [|b r IH]; cbn; [reflexivity|]. rewrite is_cont_canon2, IH. reflexivity. Qed.
Lemma canon1_tests : forall b, (canon1 b <? 160) = (b <? 160) /\ (159 <? canon1 b) = (159 <? b) /\ (canon1 b <? 144) = (b <? 144) /\ (143 <? canon1 b) = (143 <? b) /\ (canon1 b <? 128) = (b <? 128).
Proof.
  intros b. unfold canon1.
  destruct (Z.ltb_spec b 128); [|destruct (Z.ltb_spec b 144); [|destruct (Z.ltb_spec b 160); [|destruct (Z.ltb_spec b 192)]]];
  repeat split; first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
    | (destruct (Z.ltb_spec b 160); [apply Z.ltb_lt | apply Z.ltb_ge]; lia)
    | (destruct (Z.ltb_spec 159 b); [apply Z.ltb_lt | apply Z.ltb_ge]; lia)
    | (destruct (Z.ltb_spec b 144); [apply Z.ltb_lt | apply Z.ltb_ge]; lia)
    | (destruct (Z.ltb_spec 143 b); [apply Z.ltb_lt | apply Z.ltb_ge]; lia)
    | (destruct (Z.ltb_spec b 128); [apply Z.ltb_lt | apply Z.ltb_ge]; lia)].
Qed.
Lemma legal_canon : forall l b1 r, legal (l :: b1 :: r) = legal (l :: canon1 b1 :: map canon2 r).
Proof.
  intros l b1 r. unfold legal. cbn [length forallb]. rewrite length_map, forallb_is_cont_canon2, is_cont_canon1.
  destruct (canon1_tests b1) as (T1 & T2 & T3 & T4 & T5). rewrite T1, T2, T3, T4, T5. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition JV : expr := EVar 32.
Definition CUR : expr := EAlu Instr.ALU_ADD (EVar 10) (EAlu Instr.ALU_ADD (EVar 11) (EMd Instr.M_MUL (ELit (-1)) JV)).
Definition bytes256 : list Z := map Z.of_nat (seq 0 256).
Definition named (cells : list kentry) (k : nat) : option (nat * Z * Z) :=
  match SPW.named_at cells (APC.eaddz CUR (Z.of_nat k)) with Some (_, EVar v, lo, hi) => Some (v, lo, hi) | _ => None end.
(* [comment removed for export] *)
Definition TAB : Z := 84398.
Definition tab_okb (bv : nat) (b : Z) (k : kentry) : bool :=
  match k with
  | KWord a 1 (ELit t) =>
      if (a_off a =? TAB) && RLF.closed_but bv (a_base a) then
        let bx := bv_unsigned (edenot RLF.E_nil (APC.esubst bv (ELit b) (a_base a))) in
        negb ((0 <=? bx) && (bx <? 256)) || negb ((0 <=? t) && (t <? 256)) || (trailing bx =? t)
      else true
  | _ => true
  end%bool.
(* [comment removed for export] *)
Definition relevant (bv : nat) (cells : list kentry) : list kentry :=
  List.filter (fun k => match k with KRange e _ _ => RLF.closed_but bv e | KWord a 1 (ELit _) => (a_off a =? TAB) && RLF.closed_but bv (a_base a) | _ => false end) cells.
Definition adm (bv : nat) (rel : list kentry) (b : Z) : bool := RLF.byte_adm bv rel b && forallb (tab_okb bv b) rel.
Definition range_vals (lo hi : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat (hi - lo + 1))).
Definition adm_vals (cells : list kentry) (v : nat) (lo hi : Z) : list Z := let rel := relevant v cells in List.filter (adm v rel) (range_vals lo hi).
(* [comment removed for export] *)
Definition canon0 (b : Z) : Z :=
  if b <? 128 then 0 else if b <? 192 then 128 else if b <? 194 then 192 else if b <? 224 then 194 else if b =? 224 then 224 else if b <? 237 then 225 else if b =? 237 then 237
  else if b <? 240 then 238 else if b =? 240 then 240 else if b <? 244 then 241 else if b =? 244 then 244 else if b <? 248 then 245 else if b <? 252 then 248 else 252.
Definition REPS0 : list Z := [0; 128; 192; 194; 224; 225; 237; 238; 240; 241; 244; 245; 248; 252].
Definition REPS1 : list Z := [0; 128; 144; 160; 192].
Definition REPS2 : list Z := [0; 128].
Definition canon_of (q : nat) : (Z -> Z) * list Z := match q with 0%nat => (canon0, REPS0) | 1%nat => (canon1, REPS1) | _ => (canon2, REPS2) end.
(* [comment removed for export] *)
Definition reps_at (cells : list kentry) (k q : nat) : list Z :=
  let '(canon, all) := canon_of q in
  match named cells k with
  | Some (v, lo, hi) => let av := adm_vals cells v lo hi in List.filter (fun rep => existsb (fun b => canon b =? rep) av) all
  | None => all
  end.
Definition RT := list (list Z * list Z * list Z).
Definition rtab (cells : list kentry) : RT :=
  map (fun k => match named cells k with
                | Some (v, lo, hi) => let av := adm_vals cells v lo hi in
                    (List.filter (fun rep => existsb (fun b => canon0 b =? rep) av) REPS0, List.filter (fun rep => existsb (fun b => canon1 b =? rep) av) REPS1, List.filter (fun rep => existsb (fun b => canon2 b =? rep) av) REPS2)
                | None => (REPS0, REPS1, REPS2) end) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]%nat.
Definition rget (rt : RT) (k q : nat) : list Z := let '(r0, r1, r2) := nth k rt ([], [], []) in match q with 0%nat => r0 | 1%nat => r1 | _ => r2 end.
(* [comment removed for export] *)
Definition dead (rt : RT) : bool := existsb (fun e : list Z * list Z * list Z => match e with ([], _, _) => true | _ => false end) rt.
(* [comment removed for export] *)
Inductive want := WClean (d : nat) (* [comment removed for export] *) | WErr (c : Z) (* [comment removed for export] *) | WPend (* [comment removed for export] *).
Fixpoint sim (fuel : nat) (rt : RT) (k q : nat) (v : u8v) (avail : nat) (w : want) : bool :=
  match fuel with
  | O => false
  | S f =>
      match w with
      | WClean d => if Nat.eqb k d then match v with U8 0 [] 0 => true | _ => false end else
                    if negb (u_err v =? 0) then false else
                    if Nat.leb avail k then false else
                    let q' := match u_pend v with [] => 0%nat | p => length p end in
                    forallb (fun b => sim f rt (S k) 0%nat (u8_feed v b) avail w) (rget rt k q')
      | WErr c => if negb (u_err v =? 0) then u_err v =? c else
                  if Nat.leb avail k then false else
                  let q' := match u_pend v with [] => 0%nat | p => length p end in
                  forallb (fun b => sim f rt (S k) 0%nat (u8_feed v b) avail w) (rget rt k q')
      | WPend => if negb (u_err v =? 0) then false else
                 if Nat.leb avail k then match u_pend v with [] => false | _ => true end else
                 let q' := match u_pend v with [] => 0%nat | p => length p end in
                 forallb (fun b => sim f rt (S k) 0%nat (u8_feed v b) avail w) (rget rt k q')
      end
  end.
Definition BIG : nat := 13.
Definition jrange (cells : list kentry) : option (Z * Z) := CX.range3 cells JV.
Definition goto_chk (cells : list kentry) (d : Z) : bool :=
  match jrange cells with
  | Some (lo, _) => let rt := rtab cells in (1 <=? d) && (d <=? lo) && (dead rt || sim 16 rt 0 0 u8_init (Z.to_nat d) (WClean (Z.to_nat d)))
  | None => false
  end.
Definition exit_chk (cells : list kentry) (c : Z) : bool :=
  match jrange cells with
  | Some (lo, hi) => let rt := rtab cells in
      dead rt ||
      if c =? 5 then (hi <=? 13) && (1 <=? lo) && forallb (fun j => sim 16 rt 0 0 u8_init (Z.to_nat j) WPend) (range_vals lo hi)
      else if c =? 0 then (hi =? lo) && (1 <=? lo) && (lo <=? 13) && sim 16 rt 0 0 u8_init (Z.to_nat lo) (WClean (Z.to_nat lo))
      else (1 <=? lo) && sim 16 rt 0 0 u8_init (Z.to_nat (Z.min lo 13)) (WErr c)
  | None => false
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition canonq (q : nat) (b : Z) : Z := match q with 0%nat => canon0 b | 1%nat => canon1 b | _ => canon2 b end.
Fixpoint canonr (q : nat) (l : list Z) : list Z := match l with [] => [] | b :: r => canonq q b :: canonr (S q) r end.
Definition canonp (l : list Z) : list Z := canonr 0 l.
Definition canon_st (v : u8v) : u8v := U8 (u_err v) (canonp (u_pend v)) (u_need v).
Definition inb (b : Z) : Prop := 0 <= b <= 255.
(* [comment removed for export] *)
Definition lead_sig (l : Z) : Z * bool * bool * bool * bool * bool * bool :=
  (trailing l, l =? 224, l =? 237, l =? 240, l =? 244, (128 <=? l) && (l <=? 193), 244 <? l).
Definition sig_eqb (x y : Z * bool * bool * bool * bool * bool * bool) : bool :=
  match x, y with (t, a, b, c, d, e, f), (t', a', b', c', d', e', f') =>
    (t =? t') && Bool.eqb a a' && Bool.eqb b b' && Bool.eqb c c' && Bool.eqb d d' && Bool.eqb e e' && Bool.eqb f f' end.
Lemma lead_sig_canon0 : forall l, inb l -> lead_sig (canon0 l) = lead_sig l.
Proof.
  intros l Hl.
  assert (X : RLF.all_bytes (fun b => sig_eqb (lead_sig (canon0 b)) (lead_sig b)) = true) by (vm_compute; reflexivity).
  pose proof (RLF.all_bytes_sound _ l X Hl) as Y. unfold sig_eqb, lead_sig in Y |- *.
  apply andb_prop in Y as [Y Y6]. apply andb_prop in Y as [Y Y5]. apply andb_prop in Y as [Y Y4]. apply andb_prop in Y as [Y Y3]. apply andb_prop in Y as [Y Y2]. apply andb_prop in Y as [Y0 Y1].
  apply Z.eqb_eq in Y0. apply eqb_prop in Y1. apply eqb_prop in Y2. apply eqb_prop in Y3. apply eqb_prop in Y4. apply eqb_prop in Y5. apply eqb_prop in Y6.
  rewrite Y0, Y1, Y2, Y3, Y4, Y5, Y6. reflexivity.
Qed.
Lemma legal_lead_canon0 : forall l r, inb l -> legal (canon0 l :: r) = legal (l :: r).
Proof.
  intros l r Hl. pose proof (lead_sig_canon0 l Hl) as S. unfold lead_sig in S. injection S as S0 S1 S2 S3 S4 S5 S6.
  unfold legal. rewrite S1, S2, S3, S4, S5, S6. reflexivity.
Qed.
Lemma trailing_canon0 : forall l, inb l -> trailing (canon0 l) = trailing l.
Proof. intros l Hl. pose proof (lead_sig_canon0 l Hl) as S. unfold lead_sig in S. injection S as S0 _ _ _ _ _ _. exact S0. Qed.
Lemma canonr_2 : forall q r, (2 <= q)%nat -> canonr q r = map canon2 r.
Proof. intros q r. revert q. induction r as [|b r IH]; intros q Hq; cbn; [reflexivity|]. rewrite (IH (S q)) by lia. destruct q as [|[|q]]; [lia|lia|reflexivity]. Qed.
Lemma legal_canonp : forall l, Forall inb l -> legal (canonp l) = legal l.
Proof.
  intros l Hl. destruct l as [|ld [|b1 r]]; [reflexivity| |].
  - cbn [canonp canonr canonq]. apply legal_lead_canon0. exact (Forall_inv Hl).
  - cbn [canonp canonr canonq]. rewrite canonr_2 by lia. rewrite (legal_lead_canon0 ld _ (Forall_inv Hl)). symmetry. apply legal_canon.
Qed.
Lemma canonr_app : forall q p b, canonr q (p ++ [b]) = canonr q p ++ [canonq (q + length p) b].
Proof. intros q p. revert q. induction p as [|x p IH]; intros q b; cbn; [rewrite Nat.add_0_r; reflexivity|]. rewrite IH. rewrite Nat.add_succ_r. reflexivity. Qed.
Lemma canonp_length : forall p, length (canonp p) = length p.
Proof. unfold canonp. intros p. generalize 0%nat. induction p as [|x p IH]; intros q; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
(* [comment removed for export] *)
Lemma u8_feed_canon : forall va b, inb b -> Forall inb (u_pend va) -> u8_feed (canon_st va) (canonq (length (u_pend va)) b) = canon_st (u8_feed va b).
Proof.
  intros [e p nd] b Hb Hp. unfold canon_st, u8_feed. cbn [u_err u_pend u_need].
  destruct (negb (e =? 0)); [reflexivity|].
  destruct p as [|p0 pr].
  - cbn [length canonp canonr canonq]. rewrite (trailing_canon0 b Hb). destruct (trailing b =? 0); cbn [canonp canonr canonq]; [|reflexivity].
    rewrite (legal_lead_canon0 b [] Hb). reflexivity.
  - destruct (canonp (p0 :: pr)) as [|z l] eqn:Hc; [pose proof (f_equal (@length Z) Hc) as X; rewrite canonp_length in X; discriminate X|].
    rewrite <- Hc. assert (E1 : canonp (p0 :: pr) ++ [canonq (length (p0 :: pr)) b] = canonp ((p0 :: pr) ++ [b])) by (unfold canonp; rewrite canonr_app; reflexivity).
    rewrite E1, canonp_length, !length_app. cbn [length]. destruct (Z.of_nat (S (length pr) + 1) =? nd); cbn [u_err u_pend u_need]; [|reflexivity].
    rewrite legal_canonp; [reflexivity|]. apply Forall_app. split; [exact Hp | constructor; [exact Hb | constructor]].
Qed.
Lemma u8_feed_pend_inb : forall va b, inb b -> Forall inb (u_pend va) -> Forall inb (u_pend (u8_feed va b)).
Proof.
  intros [e p nd] b Hb Hp. unfold u8_feed. cbn [u_err u_pend u_need]. destruct (negb (e =? 0)); [exact Hp|].
  destruct p as [|p0 pr]; [destruct (trailing b =? 0); cbn; [constructor | constructor; [exact Hb | constructor]]|].
  destruct (Z.of_nat (length ((p0 :: pr) ++ [b])) =? nd); [constructor|]. cbn [u_pend]. apply Forall_app. split; [exact Hp | constructor; [exact Hb | constructor]].
Qed.
Lemma canon_st_pend_length : forall v, length (u_pend (canon_st v)) = length (u_pend v).
Proof. intros v. unfold canon_st. cbn. apply canonp_length. Qed.
(* [comment removed for export] *)
Lemma canonq_in : forall q b, In (canonq q b) (snd (canon_of q)).
Proof.
  intros [|[|q]] b; cbn [canonq canon_of snd].
  - unfold canon0. repeat (first [destruct (b <? _) | destruct (b =? _)]); cbn; tauto.
  - unfold canon1. repeat (destruct (b <? _)); cbn; tauto.
  - unfold canon2. destruct (is_cont b); cbn; tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma trailing_range : forall b, 0 <= trailing b <= 5.
Proof. intros b. unfold trailing. repeat (destruct (b <? _)); lia. Qed.
(* [comment removed for export] *)
Lemma TABLE_ok : RLF.all_bytes (fun b => match know_bytes_lit RSEGS [KImg 65536 827984] (ELit 0) (TAB + b) 1 with Some [t] => t =? trailing b | _ => false end) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma table_read : forall E (M' : mem) bx, inb bx -> kentry_ok RSEGS E M' (KImg 65536 827984) ->
  rdn RSEGS M' (Z_to_bv 64 (TAB + bx)) 1 = Some [Z_to_bv 8 (trailing bx)].
Proof.
  intros E M' bx Hbx HK. pose proof (RLF.all_bytes_sound _ bx TABLE_ok Hbx) as X. cbv beta in X.
  destruct (know_bytes_lit RSEGS [KImg 65536 827984] (ELit 0) (TAB + bx) 1) as [[|t [|? ?]]|] eqn:Hl; try discriminate X. apply Z.eqb_eq in X. subst t.
  assert (HK1 : know_ok RSEGS E M' [KImg 65536 827984]) by (constructor; [exact HK | constructor]).
  assert (Hfl : flat E (SA (ELit 0) (TAB + bx)) (Z.of_nat 1)) by (unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; unfold TAB, inb in *; lia).
  destruct (know_bytes_lit_sound RSEGS E M' _ (ELit 0) 1%nat (TAB + bx) _ HK1 Hl Hfl) as (bs & Hr & Hm).
  rewrite (CL5.adenot_start E _ _ Hfl) in Hr. unfold estart in Hr. cbn [a_base a_off edenot] in Hr. rewrite (u64_of_Z 0), Z.add_0_l in Hr by lia. rewrite Hr.
  destruct bs as [|b0 [|? ?]]; try discriminate Hm. cbn in Hm. injection Hm as Hm. f_equal. f_equal. rewrite <- Hm. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* [comment removed for export] *)
Lemma relevant_sub : forall bv cells k, In k (relevant bv cells) -> In k cells.
Proof. intros bv cells k H. unfold relevant in H. apply filter_In in H as [H _]. exact H. Qed.
Lemma adm_sound : forall bv E (M' : mem) cells b, know_ok RSEGS E M' cells -> kentry_ok RSEGS E M' (KImg 65536 827984) -> ev E bv = Z_to_bv 64 b -> inb b ->
  adm bv (relevant bv cells) b = true.
Proof.
  intros bv E M' cells b HK HI Hv Hb. unfold adm. apply andb_true_intro. split.
  - apply (RLF.byte_adm_sound RSEGS bv E M' b). 2: exact Hv. unfold know_ok in *. apply Forall_forall. intros k Hk. exact (proj1 (Forall_forall _ _) HK k (relevant_sub _ _ _ Hk)).
  - apply forallb_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) HK k (relevant_sub _ _ _ Hk)) as Kk.
    destruct k as [a w v| | | | | | | | |]; cbn [tab_okb]; try reflexivity. destruct w as [|[|w]]; try reflexivity. destruct v as [t| | | | | | |]; try reflexivity.
    destruct ((a_off a =? TAB) && RLF.closed_but bv (a_base a))%bool eqn:C; [|reflexivity]. apply andb_prop in C as [C1 C2]. apply Z.eqb_eq in C1.
    set (bx := bv_unsigned (edenot RLF.E_nil (APC.esubst bv (ELit b) (a_base a)))).
    destruct ((0 <=? bx) && (bx <? 256))%bool eqn:R; [|reflexivity]. cbn [negb orb]. apply andb_prop in R as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
    assert (Ebx : bv_unsigned (edenot E (a_base a)) = bx).
    { unfold bx. rewrite APS.esubst_denot. cbn [edenot]. rewrite (RLF.edenot_closed_but bv (a_base a) (APS.upd RLF.E_nil bv (Z_to_bv 64 b)) E C2); [reflexivity|].
      unfold APS.upd. cbn. rewrite Nat.eqb_refl. symmetry. exact Hv. }
    cbn [kentry_ok] in Kk. destruct Kk as (_ & Hfl & Hr). rewrite (CL5.adenot_start E a _ Hfl) in Hr. unfold estart in Hr. rewrite Ebx, C1, (Z.add_comm bx TAB) in Hr. assert (Hbx : inb bx) by (unfold inb; clear -R1 R2; lia). rewrite (table_read E M' bx Hbx HI) in Hr.
    assert (W1 : word_to_le_bytes 1 (edenot E (ELit t)) = [Z_to_bv 8 (bv_unsigned (edenot E (ELit t)))]) by (unfold word_to_le_bytes; cbn; f_equal).
    rewrite W1 in Hr. cbn [edenot] in Hr.
    assert (E8 : bv_unsigned (Z_to_bv 8 (trailing bx)) = bv_unsigned (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 t)))) by congruence.
    destruct ((0 <=? t) && (t <? 256))%bool eqn:Rt; [|reflexivity]. cbn [negb orb].
    apply andb_prop in Rt as [Rt1 Rt2]. apply Z.leb_le in Rt1. apply Z.ltb_lt in Rt2.
    rewrite (u64_of_Z t) in E8 by lia. rewrite !Z_to_bv_unsigned in E8. unfold bv_wrap in E8. change (bv_modulus 8) with 256 in E8.
    rewrite !Z.mod_small in E8 by (pose proof (trailing_range bx); lia). apply Z.eqb_eq. exact E8.
Qed.

(* [comment removed for export] *)
Section SimSound.
Variable ab : nat -> Z.
Hypothesis Hab : forall k, inb (ab k).
Variable rt : RT.
Variable avail : nat.
Hypothesis HRT : forall k q, (k < avail)%nat -> In (canonq q (ab k)) (rget rt k q).
Definition arun (va : u8v) (k m : nat) : u8v := u8_feeds va (map ab (seq k (m - k))).
Lemma arun_nil : forall va k, arun va k k = va.
Proof. intros. unfold arun. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma arun_step : forall va k m, (k < m)%nat -> arun va k m = arun (u8_feed va (ab k)) (S k) m.
Proof. intros va k m H. unfold arun. replace (m - k)%nat with (S (m - S k)) by lia. reflexivity. Qed.
Lemma canon_st_clean : forall va, canon_st va = u8_init -> va = u8_init.
Proof. intros [e p nd] H. unfold canon_st, u8_init in H. cbn in H. injection H as -> Hp ->. destruct p as [|x p]; [reflexivity|]. discriminate Hp. Qed.
Lemma sim_sound : forall fuel k q va w,
  sim fuel rt k q (canon_st va) avail w = true -> Forall inb (u_pend va) -> (k <= avail)%nat ->
  match w with
  | WClean d => (k <= d)%nat /\ arun va k d = u8_init
  | WErr c => c <> 0 /\ exists m, (k <= m <= avail)%nat /\ u_err (arun va k m) = c
  | WPend => u_err (arun va k avail) = 0 /\ u_pend (arun va k avail) <> []
  end.
Proof.
  induction fuel as [|f IH]; intros k q va w HS Hp Hka; [discriminate HS|]. cbn [sim] in HS.
  assert (STEP : forall w', forallb (fun b => sim f rt (S k) 0%nat (u8_feed (canon_st va) b) avail w')
                              (rget rt k match u_pend (canon_st va) with [] => 0%nat | p => length p end) = true -> (k < avail)%nat ->
            let va' := u8_feed va (ab k) in sim f rt (S k) 0%nat (canon_st va') avail w' = true /\ Forall inb (u_pend va')).
  { intros w' HF Hk. rewrite forallb_forall in HF.
    assert (Hq : match u_pend (canon_st va) with [] => 0%nat | p => length p end = length (u_pend va)).
    { pose proof (canon_st_pend_length va) as L. destruct (u_pend (canon_st va)) eqn:E; [cbn in L; exact L | exact L]. }
    rewrite Hq in HF. specialize (HF _ (HRT k (length (u_pend va)) Hk)). rewrite (u8_feed_canon va (ab k) (Hab k) Hp) in HF.
    split; [exact HF | exact (u8_feed_pend_inb va (ab k) (Hab k) Hp)]. }
  destruct w as [d|c|].
  - destruct (Nat.eqb_spec k d) as [->|Hkd].
    + split; [lia|]. rewrite arun_nil. apply canon_st_clean. destruct (canon_st va) as [e p nd]. destruct e as [|pe|pe]; try discriminate HS; destruct p; try discriminate HS; destruct nd; try discriminate HS; reflexivity.
    + destruct (negb (u_err (canon_st va) =? 0)); [discriminate HS|]. destruct (Nat.leb_spec avail k) as [Hle|Hlt]; [discriminate HS|].
      destruct (STEP _ HS Hlt) as [HS' Hp']. specialize (IH (S k) 0%nat (u8_feed va (ab k)) (WClean d) HS' Hp' ltac:(lia)). cbv beta iota in IH. destruct IH as [Hk' Hr].
      split; [lia|]. rewrite (arun_step va k d) by lia. exact Hr.
  - destruct (negb (u_err (canon_st va) =? 0)) eqn:He.
    + apply Z.eqb_eq in HS. apply negb_true_iff in He. apply Z.eqb_neq in He. unfold canon_st in HS, He. cbn in HS, He. split; [congruence|]. exists k. split; [|rewrite arun_nil; exact HS].
      lia.
    + destruct (Nat.leb_spec avail k) as [Hle|Hlt]; [discriminate HS|].
      destruct (STEP _ HS Hlt) as [HS' Hp']. specialize (IH (S k) 0%nat (u8_feed va (ab k)) (WErr c) HS' Hp' ltac:(lia)). cbv beta iota in IH. destruct IH as (Hc & m & Hm & Hr).
      split; [exact Hc|]. exists m. split; [lia|]. rewrite (arun_step va k m) by lia. exact Hr.
  - destruct (negb (u_err (canon_st va) =? 0)) eqn:He; [discriminate HS|]. apply negb_false_iff in He. apply Z.eqb_eq in He.
    destruct (Nat.leb_spec avail k) as [Hle|Hlt].
    + unfold arun. replace (avail - k)%nat with 0%nat by lia. cbn [seq map u8_feeds]. unfold canon_st in HS, He. cbn in HS, He. split; [exact He|].
      destruct (u_pend va) eqn:Ep; [discriminate HS|]. congruence.
    + destruct (STEP _ HS Hlt) as [HS' Hp']. specialize (IH (S k) 0%nat (u8_feed va (ab k)) WPend HS' Hp' ltac:(lia)). cbv beta iota in IH.
      rewrite (arun_step va k avail) by lia. exact IH.
Qed.
End SimSound.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma map_nth_seq : forall (l : list Z) m n, (n + m <= length l)%nat -> map (fun k => nth (n + k) l 0) (seq 0 m) = firstn m (skipn n l).
Proof.
  intros l m. induction m as [|m IH]; intros n Hl; [cbn; destruct (skipn n l); reflexivity|].
  cbn [seq map]. rewrite <- seq_shift, map_map. rewrite (SPTW.skipn_nth_cons n l) by lia. cbn [firstn]. rewrite Nat.add_0_r. f_equal.
  rewrite <- (IH (S n)) by lia. apply map_ext. intros a. f_equal. lia.
Qed.
Lemma skipn_as_map : forall (l : list Z) n, (n <= length l)%nat -> skipn n l = map (fun k => nth (n + k) l 0) (seq 0 (length l - n)).
Proof. intros l n Hn. rewrite map_nth_seq by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. Qed.
Lemma firstn_add : forall (l : list Z) n m, firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  intros l n. revert l. induction n as [|n IH]; intros l m; [reflexivity|]. destruct l as [|x r]; [cbn; rewrite firstn_nil; reflexivity|]. cbn. f_equal. apply IH.
Qed.
Lemma b256_id : forall l, Forall inb l -> b256 l = l.
Proof. intros l H. unfold b256. induction H as [|b r Hb _ IH]; [reflexivity|]. cbn. rewrite IH. f_equal. unfold inb in Hb. apply Z.mod_small. lia. Qed.
Lemma Forall_nth0 : forall (l : list Z) i, Forall inb l -> inb (nth i l 0).
Proof. intros l i H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi]; [exact (proj1 (Forall_forall _ _) H _ (nth_In l 0 Hi)) | rewrite nth_overflow by lia; unfold inb; lia]. Qed.
Lemma range_vals_in : forall lo hi b, lo <= b <= hi -> In b (range_vals lo hi).
Proof.
  intros lo hi b Hb. unfold range_vals. apply in_map_iff. exists (Z.to_nat (b - lo)). split; [lia|]. apply in_seq. lia.
Qed.
(* [comment removed for export] *)
Lemma dead_sound : forall E' (M' : mem) cells, know_ok RSEGS E' M' cells -> kentry_ok RSEGS E' M' (KImg 65536 827984) -> dead (rtab cells) = true -> False.
Proof.
  intros E' M' cells HK HI H. unfold dead in H. apply existsb_exists in H as (e & Hin & He). unfold rtab in Hin. apply in_map_iff in Hin as (k & Hk & _). subst e.
  destruct (named cells k) as [[[v lo] hi]|] eqn:Hn; [|discriminate He].
  unfold named in Hn. destruct (SPW.named_at cells (APC.eaddz CUR (Z.of_nat k))) as [[[[a ve] lo'] hi']|] eqn:Hna; [|discriminate Hn]. destruct ve; try discriminate Hn. injection Hn as -> -> ->.
  destruct (SPW.named_sound E' M' _ _ _ _ _ _ HK Hna) as (_ & Hr & Hlo & Hhi).
  set (b := PB.uv E' (EVar v)) in *.
  assert (Hadm : In b (adm_vals cells v lo hi)).
  { unfold adm_vals. apply filter_In. split; [apply range_vals_in; exact Hr|]. apply (adm_sound v E' M' cells b HK HI); [|unfold inb; lia].
    unfold b, PB.uv. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Hin0 : In (canon0 b) (List.filter (fun rep => existsb (fun b' => canon0 b' =? rep) (adm_vals cells v lo hi)) REPS0)).
  { apply filter_In. split; [apply (canonq_in 0) | apply existsb_exists; exists b; split; [exact Hadm | apply Z.eqb_refl]]. }
  cbv zeta in He. destruct (List.filter _ REPS0); [destruct Hin0 | discriminate He].
Qed.
(* [comment removed for export] *)
Lemma rtab_sound : forall E' (M' : mem) cells p w (n0 : nat), know_ok RSEGS E' M' cells -> kentry_ok RSEGS E' M' (KImg 65536 827984) ->
  L5.bytes_at RSEGS M' p w -> Forall inb w -> PB.uv E' CUR = p + Z.of_nat n0 -> p + Z.of_nat (length w) < 2 ^ 64 ->
  forall k q, (k < 13)%nat -> (n0 + k < length w)%nat -> In (canonq q (nth (n0 + k) w 0)) (rget (rtab cells) k q).
Proof.
  intros E' M' cells p w n0 HK HI HB HF Hcur Hpw k q Hk Hkw.
  assert (Hrg : rget (rtab cells) k q = match named cells k with
                | Some (v, lo, hi) => let av := adm_vals cells v lo hi in
                    match q with 0%nat => List.filter (fun rep => existsb (fun b => canon0 b =? rep) av) REPS0 | 1%nat => List.filter (fun rep => existsb (fun b => canon1 b =? rep) av) REPS1
                               | _ => List.filter (fun rep => existsb (fun b => canon2 b =? rep) av) REPS2 end
                | None => match q with 0%nat => REPS0 | 1%nat => REPS1 | _ => REPS2 end end).
  { unfold rget, rtab. do 13 (destruct k as [|k]; [cbn [map nth]; destruct (named cells _) as [[[? ?] ?]|]; destruct q as [|[|?]]; reflexivity|]). lia. }
  destruct (named cells k) as [[[v lo] hi]|] eqn:Hn.
  - unfold named in Hn. destruct (SPW.named_at cells (APC.eaddz CUR (Z.of_nat k))) as [[[[a ve] lo'] hi']|] eqn:Hna; [|discriminate Hn]. destruct ve; try discriminate Hn. injection Hn as -> -> ->.
    assert (Hck : PB.uv E' (APC.eaddz CUR (Z.of_nat k)) = p + Z.of_nat (n0 + k)).
    { rewrite PB.uv_eaddz, Hcur. rewrite Z.mod_small; [lia|]. pose proof (PB.uv_range E' CUR). lia. }
    destruct (SPTW.named_byte cells _ a (EVar v) lo hi E' M' p w (n0 + k) Hna HK HB ltac:(apply Forall_impl with (P := inb); [intros z Hz; exact Hz | exact HF]) Hck Hkw) as [Hv Hr].
    set (b := nth (n0 + k) w 0) in *.
    assert (Hadm : In b (adm_vals cells v lo hi)).
    { unfold adm_vals. apply filter_In. split; [apply range_vals_in; rewrite Hv; exact Hr|]. apply (adm_sound v E' M' cells b HK HI); [|unfold b; apply Forall_nth0; exact HF].
      rewrite Hv. unfold PB.uv. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned. }
    rewrite Hrg. cbv zeta. destruct q as [|[|q]]; (apply filter_In; split; [apply (canonq_in 0) || apply (canonq_in 1) || apply (canonq_in 2) | apply existsb_exists; exists b; split; [exact Hadm | apply Z.eqb_refl]]).
  - rewrite Hrg. destruct q as [|[|q]]; [apply (canonq_in 0) | apply (canonq_in 1) | apply (canonq_in 2)].
Qed.
End VKW.
