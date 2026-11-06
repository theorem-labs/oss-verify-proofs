(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExecF AxSymExecFB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.

Module AX2E.
Import AX2 AX2B.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition ltab := list (expr * positive).
Fixpoint lt_find (lt : ltab) (b : expr) : option positive :=
  match lt with [] => None | (b', id) :: r => if expr_eqb b b' then Some id else lt_find r b end.
Record lst := LST { l_tab : ltab; l_next : positive; l_ids : list positive }.
Definition lst0 : lst := LST [] xH [].
Definition se_base (s : sentry) : expr := match s with SE a _ _ => a_base a end.
Definition l_push (s : lst) (b : expr) : lst :=
  match lt_find (l_tab s) b with
  | Some id => LST (l_tab s) (l_next s) (id :: l_ids s)
  | None => LST ((b, l_next s) :: l_tab s) (Pos.succ (l_next s)) (l_next s :: l_ids s)
  end.
(* [comment removed for export] *)
Fixpoint l_init (log : list sentry) : lst :=
  match log with [] => lst0 | s :: older => l_push (l_init older) (se_base s) end.

Definition TOK (t : ltab) (next : positive) : Prop :=
  (forall b id, In (b, id) t -> (id < next)%positive)
  /\ (forall b id id', In (b, id) t -> In (b, id') t -> id = id')
  /\ (forall b b' id, In (b, id) t -> In (b', id) t -> b = b').
Definition LOK (log : list sentry) (s : lst) : Prop :=
  TOK (l_tab s) (l_next s) /\ Forall2 (fun e id => In (se_base e, id) (l_tab s)) log (l_ids s).

Lemma lt_find_In : forall lt b id, lt_find lt b = Some id -> In (b, id) lt.
Proof.
  induction lt as [|[b' id'] r IH]; cbn [lt_find]; intros b id H; [discriminate|].
  destruct (expr_eqb b b') eqn:E; [injection H as <-; apply p_expr_eqb_eq in E; subst; left; reflexivity | right; apply IH; exact H].
Qed.
Lemma lt_find_None : forall lt b id, lt_find lt b = None -> ~ In (b, id) lt.
Proof.
  induction lt as [|[b' id'] r IH]; cbn [lt_find]; intros b id H Hin; [exact Hin|].
  destruct (expr_eqb b b') eqn:E; [discriminate|].
  destruct Hin as [Hin|Hin]; [injection Hin as -> ->; rewrite p_expr_eqb_refl in E; discriminate | exact (IH _ _ H Hin)].
Qed.
Lemma LOK_nil : LOK [] lst0.
Proof. split; [|constructor]. repeat split; intros; cbn in *; contradiction. Qed.
Lemma l_push_ok : forall log s e, LOK log s -> LOK (e :: log) (l_push s (se_base e)).
Proof.
  intros log s e [[T1 [T2 T3]] HF]. unfold l_push. destruct (lt_find (l_tab s) (se_base e)) as [id|] eqn:EF; cbn [l_tab l_next l_ids].
  - split; [repeat split; assumption|]. constructor; [exact (lt_find_In _ _ _ EF) | exact HF].
  - split.
    + repeat split.
      * intros b id [H|H]; [injection H as <- <-; apply Pos.lt_succ_diag_r | apply Pos.lt_lt_succ; exact (T1 _ _ H)].
      * intros b id id' [H|H] [H'|H'].
        -- congruence.
        -- injection H as <- <-. exfalso. exact (lt_find_None _ _ _ EF H').
        -- injection H' as <- <-. exfalso. exact (lt_find_None _ _ _ EF H).
        -- exact (T2 _ _ _ H H').
      * intros b b' id [H|H] [H'|H'].
        -- congruence.
        -- injection H as <- <-. pose proof (T1 _ _ H') as X. exfalso. exact (Pos.lt_irrefl _ X).
        -- injection H' as <- <-. pose proof (T1 _ _ H) as X. exfalso. exact (Pos.lt_irrefl _ X).
        -- exact (T3 _ _ _ H H').
    + constructor; [left; reflexivity|]. eapply Forall2_impl; [|exact HF]. intros a b H. right. exact H.
Qed.
Lemma l_init_ok : forall log, LOK log (l_init log).
Proof. induction log as [|e older IH]; [exact LOK_nil|]. cbn [l_init]. apply l_push_ok. exact IH. Qed.

(* [comment removed for export] *)
Definition rid_is (rid : option positive) (id : positive) : bool :=
  match rid with Some r => Pos.eqb r id | None => false end.
Fixpoint log_lookupRB5 (bc : bctx) (r1 : option (Z * Z)) (memo : list (positive * option (Z * Z))) (log : list sentry) (ids : list positive)
         (rid : option positive) (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match log, ids with
  | SE (SA kb kk) w v :: rest, id :: ids' =>
      if rid_is rid id then
        if (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w))%bool then LHit (mkExt sx (Z.to_nat (rk - kk)) n v) acc hints
        else if (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + Z.of_nat w) rk)%bool then log_lookupRB5 bc r1 memo rest ids' rid rb rk n sx hints acc
        else match log_bytes_lit log rb rk n with
             | Some bs => LHit (lit_of_bytes sx n bs) acc hints
             | None => LStuck
             end
      else
        let '(th, memo') := match alookupP memo id with
                            | Some th => (th, memo)
                            | None => let th := r1_thresh r1 rk (Z.of_nat n) (base_rangeB bc kb) in (th, (id, th) :: memo)
                            end in
        if thresh_apart th kk (Z.of_nat w) then log_lookupRB5 bc r1 memo' rest ids' rid rb rk n sx hints acc
        else if kdisj_apartB bc (bc_kd bc) rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB5 bc r1 memo' rest ids' rid rb rk n sx hints acc
        else if lin_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB5 bc r1 memo' rest ids' rid rb rk n sx hints acc
        else
        match hints with
        | false :: _ => LStuck
        | _ => log_lookupRB5 bc r1 memo' rest ids' rid rb rk n sx (tl hints)
                 (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
        end
  | _, _ => log_lookupRB bc r1 log rb rk n sx hints acc
  end.

Definition IMEMO_OK (bc : bctx) (t : ltab) (r1 : option (Z * Z)) (rk rn : Z) (memo : list (positive * option (Z * Z))) : Prop :=
  forall id th, alookupP memo id = Some th -> forall kb, In (kb, id) t -> th = r1_thresh r1 rk rn (base_rangeB bc kb).

Lemma rid_is_eq : forall t next rb kb id, TOK t next -> In (kb, id) t ->
  rid_is (lt_find t rb) id = expr_eqb rb kb.
Proof.
  intros t next rb kb id (T1 & T2 & T3) Hin. unfold rid_is. destruct (lt_find t rb) as [r|] eqn:EF.
  - pose proof (lt_find_In _ _ _ EF) as Hr. destruct (Pos.eqb_spec r id) as [->|NE].
    + rewrite (T3 _ _ _ Hr Hin). symmetry. apply p_expr_eqb_refl.
    + destruct (expr_eqb rb kb) eqn:E; [|reflexivity]. apply p_expr_eqb_eq in E. subst kb. exfalso. apply NE. exact (T2 _ _ _ Hr Hin).
  - destruct (expr_eqb rb kb) eqn:E; [|reflexivity]. apply p_expr_eqb_eq in E. subst kb. exfalso. exact (lt_find_None _ _ _ EF Hin).
Qed.

Lemma log_lookupRB5_eq : forall bc r1 t next log ids rb rk n sx hints acc memo,
  TOK t next -> Forall2 (fun e id => In (se_base e, id) t) log ids -> IMEMO_OK bc t r1 rk (Z.of_nat n) memo ->
  log_lookupRB5 bc r1 memo log ids (lt_find t rb) rb rk n sx hints acc = log_lookupRB bc r1 log rb rk n sx hints acc.
Proof.
  intros bc r1 t next log ids rb rk n sx hints acc memo HT HF. revert hints acc memo.
  induction HF as [|[[kb kk] w v] id rest ids' Hin HF IH]; intros hints acc memo HM; [reflexivity|].
  cbn [se_base a_base] in Hin. cbn [log_lookupRB5 log_lookupRB].
  rewrite (rid_is_eq t next rb kb id HT Hin). unfold rel_lit.
  destruct (expr_eqb rb kb) eqn:EB.
  - destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat n) (kk + Z.of_nat w))%bool; [reflexivity|].
    destruct (Z.leb (rk + Z.of_nat n) kk || Z.leb (kk + Z.of_nat w) rk)%bool; [apply IH; exact HM|reflexivity].
  - assert (STEP : forall th memo', th = r1_thresh r1 rk (Z.of_nat n) (base_rangeB bc kb) -> IMEMO_OK bc t r1 rk (Z.of_nat n) memo' ->
      (if thresh_apart th kk (Z.of_nat w) then log_lookupRB5 bc r1 memo' rest ids' (lt_find t rb) rb rk n sx hints acc
       else if kdisj_apartB bc (bc_kd bc) rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB5 bc r1 memo' rest ids' (lt_find t rb) rb rk n sx hints acc
       else if lin_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB5 bc r1 memo' rest ids' (lt_find t rb) rb rk n sx hints acc
       else match hints with
            | false :: _ => LStuck
            | _ => log_lookupRB5 bc r1 memo' rest ids' (lt_find t rb) rb rk n sx (tl hints) (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
            end)
      = (if ranges_apart_r1B bc r1 rb rk (Z.of_nat n) kb kk (Z.of_nat w) then log_lookupRB bc r1 rest rb rk n sx hints acc
         else match hints with
              | false :: _ => LStuck
              | _ => log_lookupRB bc r1 rest rb rk n sx (tl hints) (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
              end)).
    { intros th memo' -> HM'. rewrite thresh_apart_eq. unfold ranges_apart_r1B.
      destruct (match r1, base_rangeB bc kb with
                | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + rk + Z.of_nat n) (lo2 + kk) || Z.leb (hi2 + kk + Z.of_nat w) (lo1 + rk))%bool
                | _, _ => false end); [apply IH; exact HM'|].
      destruct (kdisj_apartB _ _ _ _ _ _ _ _); [apply IH; exact HM'|].
      destruct (lin_apartB _ _ _ _ _ _ _); [apply IH; exact HM'|].
      destruct hints as [|[|] hs]; first [reflexivity | apply IH; exact HM']. }
    destruct (alookupP memo id) as [th|] eqn:HL.
    + apply STEP; [exact (HM _ _ HL _ Hin)|exact HM].
    + apply STEP; [reflexivity|].
      intros id' th' H' kb' Hin'. cbn [alookupP] in H'. destruct (Pos.eqb id' id) eqn:E.
      * injection H' as <-. apply Pos.eqb_eq in E. subst id'. destruct HT as (_ & _ & T3). rewrite (T3 _ _ _ Hin' Hin). reflexivity.
      * exact (HM _ _ H' _ Hin').
Qed.

(* [comment removed for export] *)
Definition sym_readRBI5 (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (qm : qmemo) (ls : lst) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat * list kentry) * qmemo :=
  let r1 := base_rangeB bc (a_base a) in
  match log_lookupRB5 bc r1 [] (s_log ss) (l_ids ls) (lt_find (l_tab ls) (a_base a)) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => (None, qm)
  | LHit v scs hints =>
      (Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss, []), qm)
  | LMiss scs hints =>
      let '(r, qm') := know_lookupABRIq bc r1 kx qm segs (s_know ss) (a_base a) (a_off a) n sx' hints scs in
      (match r with
       | LStuck => None
       | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss, [])
       | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let rvx := match sc_reads scr with [] => mkExt sx' 0 n (EVar i) | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rvx, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i,
                if rec_onb (bc_fk bc) then [krec a n rv] else [])
       end, qm')
  end.
Lemma sym_readRBI5_eq : forall segs ss bc kx qm ls scr a n sx',
  LOK (s_log ss) ls -> sym_readRBI5 segs ss bc kx qm ls scr a n sx' = sym_readRBI3 segs ss bc kx qm scr a n sx'.
Proof.
  intros segs ss bc kx qm ls scr a n sx' [HT HF]. unfold sym_readRBI5, sym_readRBI3. cbv zeta.
  rewrite (log_lookupRB5_eq bc _ (l_tab ls) (l_next ls) _ _ _ _ _ _ _ _ [] HT HF) by (intros id th H; discriminate H).
  rewrite log_lookupRB2_eq by (intros kb th H; discriminate H). reflexivity.
Qed.
Definition sym_readBI5 (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (qm : qmemo) (ls : lst) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) * qmemo :=
  let '(r, qm') := sym_readRBI5 segs ss bc kx qm ls scr a n sx' in
  (match r with
   | Some (v, scs, scr', nx', _) => Some (v, scs, scr', nx')
   | None => None
   end, qm').
Lemma sym_readBI5_eq : forall segs ss bc kx qm ls scr a n sx',
  LOK (s_log ss) ls -> sym_readBI5 segs ss bc kx qm ls scr a n sx' = sym_readBI3 segs ss bc kx qm scr a n sx'.
Proof. intros. unfold sym_readBI5, sym_readBI3. rewrite sym_readRBI5_eq by assumption. reflexivity. Qed.

Definition sym_stepBI5 (bc : bctx) (kx : kix) (qm : qmemo) (ls : lst) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts)
  : stepres * qmemo :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signedF imm) in
      let '(r, qm') := sym_readRBI5 segs ss bc kx qm ls scr a n sx' in
      (match r with
       | None => SStop
       | Some (v, scs, scr', nx', recs) =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (recs ++ s_know ss) nx' (s_resv ss)) scs scr'
       end, qm')
  | _ => sym_stepBI3 bc kx qm segs i ss scr
  end.
Lemma sym_stepBI5_eq : forall bc kx qm ls segs i ss scr,
  LOK (s_log ss) ls -> sym_stepBI5 bc kx qm ls segs i ss scr = sym_stepBI3 bc kx qm segs i ss scr.
Proof.
  intros bc kx qm ls segs i ss scr HL. unfold sym_stepBI5. destruct i; try reflexivity.
  unfold sym_stepBI3. cbv zeta. rewrite sym_readRBI5_eq by exact HL. reflexivity.
Qed.

(* [comment removed for export] *)
Definition log_delta (i : instr) : bool :=
  match i with
  | Store _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ | FStore _ _ _ _ => true
  | _ => false
  end.
Definition l_sync (ls : lst) (i : instr) (ss' : sym_state) : lst :=
  if log_delta i then match s_log ss' with e :: _ => l_push ls (se_base e) | [] => ls end else ls.
End AX2E.

Module AX2FE.
Import AX2 AX2B AX2F AX2FB AX2E.
Section WithSegs.
Variable segs : list Segment.

Lemma stepFBI_log : forall bc kx i ss scr ss' scs scr',
  sym_stepFBI segs bc kx i ss scr = SOk ss' scs scr' ->
  if log_delta i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss.
Proof.
  intros bc kx i ss scr ss' scs scr' H. unfold sym_stepFBI in H.
  destruct (is_fp_instr i) eqn:FP; cbn [negb] in H.
  - destruct (s_clean ss); cbn [negb] in H; [|discriminate H].
    destruct i; cbn [is_fp_instr] in FP; try discriminate FP; try discriminate H; cbn [log_delta];
    repeat (lazymatch type of H with
            | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
            | (match ?x with _ => _ end) = _ => destruct x
            | (let (_, _) := ?x in _) = _ => destruct x
            | (if ?x then _ else _) = _ => destruct x
            end); try discriminate H; cbn [s_log sset sjump sfresh]; first [reflexivity | eexists; reflexivity].
  - unfold sym_stepBI in H.
    destruct i; try discriminate H; cbn [log_delta];
    repeat (lazymatch type of H with
            | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
            | (match ?x with _ => _ end) = _ => destruct x
            | (let (_, _) := ?x in _) = _ => destruct x
            | (if ?x then _ else _) = _ => destruct x
            end); try discriminate H; cbn [s_log sset sjump]; first [reflexivity | eexists; reflexivity].
Qed.

Lemma cap_rd_log : forall K i ss, s_log (cap_rd K i ss) = s_log ss.
Proof.
  intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i); [|reflexivity].
  destruct (bv_eqb _ _); [reflexivity|]. destruct (esize_le _ _); reflexivity.
Qed.
Lemma l_sync_ok : forall bc kx qm K i ss scr ss' scs scr' ls,
  QM_OK kx qm -> fst (sym_stepXFBI3 segs bc kx qm K i ss scr) = SOk ss' scs scr' ->
  LOK (s_log ss) ls -> LOK (s_log ss') (l_sync ls i ss').
Proof.
  intros bc kx qm K i ss scr ss' scs scr' ls HQ H HL.
  rewrite (proj1 (sym_stepXFBI3_eq segs bc kx qm K i ss scr HQ)) in H. unfold sym_stepXFBI in H.
  destruct (sym_stepFBI segs bc kx i ss scr) as [s1 scs1 scr1|] eqn:ES; [|discriminate H].
  injection H as <- _ _. pose proof (stepFBI_log _ _ _ _ _ _ _ _ ES) as HD.
  unfold l_sync. rewrite cap_rd_log. destruct (log_delta i).
  - destruct HD as [e He]. rewrite He. apply l_push_ok. exact HL.
  - rewrite HD. exact HL.
Qed.

Definition sym_stepFBI5 (bc : bctx) (kx : kix) (qm : qmemo) (ls : lst) (i : instr) (ss : sym_state) (scr : scripts) : stepres * qmemo :=
  if negb (is_fp_instr i) then sym_stepBI5 bc kx qm ls segs i ss scr else sym_stepFBI3 segs bc kx qm i ss scr.
Lemma sym_stepFBI5_eq : forall bc kx qm ls i ss scr,
  LOK (s_log ss) ls -> sym_stepFBI5 bc kx qm ls i ss scr = sym_stepFBI3 segs bc kx qm i ss scr.
Proof.
  intros bc kx qm ls i ss scr HL. unfold sym_stepFBI5. destruct (is_fp_instr i) eqn:FP; cbn [negb]; [reflexivity|].
  rewrite sym_stepBI5_eq by exact HL. unfold sym_stepFBI3. rewrite FP. reflexivity.
Qed.
Definition sym_stepXFBI5 (bc : bctx) (kx : kix) (qm : qmemo) (ls : lst) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres * qmemo :=
  let '(r, qm') := sym_stepFBI5 bc kx qm ls i ss scr in
  (match r with
   | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
   | SStop => SStop
   end, qm').
Lemma sym_stepXFBI5_eq : forall bc kx qm ls K i ss scr,
  LOK (s_log ss) ls -> sym_stepXFBI5 bc kx qm ls K i ss scr = sym_stepXFBI3 segs bc kx qm K i ss scr.
Proof. intros. unfold sym_stepXFBI5, sym_stepXFBI3. rewrite sym_stepFBI5_eq by assumption. reflexivity. Qed.

Fixpoint sym_execTXFBI5_go (bc : bctx) (kx : kix) (qm : qmemo) (ls : lst) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
         (ss : sym_state) (ck : sym_state) : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXFBI5 bc kx qm ls K i ss scr_nil with
          | (SOk ss' [] _, qm') => sym_execTXFBI5_go bc kx qm' (l_sync ls i ss') t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Lemma sym_execTXFBI5_go_eq : forall bc kx t K fuel first stops ss ck qm ls,
  QM_OK kx qm -> LOK (s_log ss) ls ->
  sym_execTXFBI5_go bc kx qm ls t K fuel first stops ss ck = sym_execTXFBI3_go segs bc kx qm t K fuel first stops ss ck.
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck qm ls HQ HL; [reflexivity|].
  cbn [sym_execTXFBI5_go sym_execTXFBI3_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXFBI5_eq by exact HL.
  destruct (sym_stepXFBI3 segs bc kx qm K i ss scr_nil) as [r qm'] eqn:ES.
  destruct r as [ss' scs scr'|]; [|reflexivity]. destruct scs; [|reflexivity].
  apply IH.
  - pose proof (proj2 (sym_stepXFBI3_eq segs bc kx qm K i ss scr_nil HQ)) as X. rewrite ES in X. exact X.
  - eapply (l_sync_ok bc kx qm K i ss scr_nil ss' [] scr' ls HQ); [rewrite ES; reflexivity | exact HL].
Qed.
(* [comment removed for export] *)
Definition sym_execTXFBI5 (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXFBI5_go bc kx [] (l_init (s_log ss)) t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXFBI5_eq : forall bc kx t K fuel first stops ss,
  sym_execTXFBI5 bc kx t K fuel first stops ss = sym_execTXFBI segs bc kx t K fuel first stops ss.
Proof.
  intros. unfold sym_execTXFBI5, sym_execTXFBI. apply sym_execTXFBI5_go_eq; [apply QM_OK_nil|].
  replace (s_log (clr ss)) with (s_log ss) by (destruct ss; reflexivity). apply l_init_ok.
Qed.
End WithSegs.
End AX2FE.
