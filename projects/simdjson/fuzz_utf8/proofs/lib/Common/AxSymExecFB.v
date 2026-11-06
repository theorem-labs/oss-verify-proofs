(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExecF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2B. Import AX2F.
Open Scope Z_scope.

Module AX2FB.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition sym_stepFBI (bc : bctx) (kx : kix) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  if negb (is_fp_instr i) then sym_stepBI bc kx segs i ss scr else
  if negb (s_clean ss) then SStop else
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | FLoad fmt rd rs imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      if (match s_log ss with [] => true | _ => false end
          && fload_img_ok segs (s_know ss) (mkAlu ALU_ADD (g rs) (ELit (bv_signed imm))) n)%bool
      then SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) (s_next ss) (s_resv ss)) [] scr
      else
      match sym_readBI segs ss bc kx scr a n false with
      | None => SStop
      | Some (_, scs, scr', nx') => SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | FStore fmt rs1 rs2 imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      SOk (SSR (p + 4) (s_regs ss) (SE a n (EVar (s_next ss)) :: s_log ss) (s_know ss) (S (s_next ss)) (s_resv ss))
          (flat_scB bc a n ++ storeok_scB bc a n) scr
  | Fmv FMV_X_F _ rd _ => SOk (sfresh ss rd (p + 4)) [] scr
  | Fmv FMV_F_X _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fsgnj _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Fari _ _ _ _ _ rm => if rm_okb rm then SOk (sjump ss (p + 4)) [] scr else SStop
  | Fcvt dst src rd _ rm =>
      if negb (rm_okb rm) then SStop else
      if fcvt_is_fp dst then SOk (sjump ss (p + 4)) [] scr
      else if fcvt_is_fp src then SOk (sfresh ss rd (p + 4)) [] scr
      else SStop
  | Fcmp _ _ rd _ _ => SOk (sfresh ss rd (p + 4)) [] scr
  | Fclass _ rd _ => SOk (sfresh ss rd (p + 4)) [] scr
  | Csr CSR_RS rd rs1 csr =>
      if (bv_eqb rs1 0 && Z.eqb (bv_unsigned csr) 2)%bool then SOk (sset ss rd (ELit 0) (p + 4)) [] scr else SStop
  | CsrI CSR_RS rd uimm csr =>
      if (bv_eqb rd 0 && Z.eqb (bv_unsigned csr) 1)%bool then SOk (sjump ss (p + 4)) [] scr else SStop
  | _ => SStop
  end.

Lemma sym_stepFBI_eq : forall i ss scr,
  sym_stepFBI (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) i ss scr = sym_stepF segs i ss scr.
Proof.
  intros i ss scr. unfold sym_stepFBI, sym_stepF.
  destruct (is_fp_instr i); cbn [negb]; [|rewrite sym_stepBI_eq; apply sym_stepB_eq].
  rewrite sym_readBI_eqf. autorewrite with bceq. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sym_stepF_next_le : forall i ss scr ss' scs scr',
  sym_stepF segs i ss scr = SOk ss' scs scr' -> (s_next ss <= s_next ss')%nat.
Proof.
  intros i ss scr ss' scs scr' H. unfold sym_stepF in H.
  destruct (is_fp_instr i); cbn [negb] in H; [|exact (sym_step_next_le _ _ _ _ _ _ _ H)].
  destruct (s_clean ss); cbn [negb] in H; [|discriminate].
  unfold sym_read in H.
  destruct i; try discriminate;
  try (lazymatch type of H with
       | context [sym_readR ?sg ?s0 ?f ?sc ?a ?n ?sx] =>
           destruct (sym_readR sg s0 f sc a n sx) as [[[[[v scs0] scr0] nx0] recs]|] eqn:ER;
           [pose proof (sym_readR_next _ _ _ _ _ _ _ _ _ _ _ _ ER) as HN|]
       end);
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; cbn [s_next sset sjump sfresh]; try lia.
  all: destruct HN as [-> | ->]; lia.
Qed.
Definition sym_stepXFBI (bc : bctx) (kx : kix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepFBI bc kx i ss scr with
  | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'   (* [comment removed for export] *)
  | SStop => SStop
  end.

Lemma sym_stepXFBI_eq : forall K i ss scr,
  sym_stepXFBI (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) K i ss scr = sym_stepXF segs K i ss scr.
Proof.
  intros. unfold sym_stepXFBI, sym_stepXF. rewrite sym_stepFBI_eq.
  destruct (sym_stepF segs i ss scr) as [ss' scs scr'|] eqn:E; [|reflexivity].
  rewrite (proj2 (Nat.leb_le _ _) (sym_stepF_next_le _ _ _ _ _ _ E)). rewrite x_filterB_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sym_stepF_kext : forall i ss scr ss' scs scr',
  sym_stepF segs i ss scr = SOk ss' scs scr' -> kext (s_know ss') (s_know ss).
Proof.
  intros i ss scr ss' scs scr' H. unfold sym_stepF in H.
  destruct (is_fp_instr i); cbn [negb] in H; [|exact (sym_step_kext _ _ _ _ _ _ _ H)].
  destruct (s_clean ss); cbn [negb] in H; [|discriminate].
  destruct i; try discriminate;
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; try apply kext_refl.
Qed.

Lemma sym_stepXF_kext : forall K i ss scr ss' scs scr',
  sym_stepXF segs K i ss scr = SOk ss' scs scr' -> kext (s_know ss') (s_know ss).
Proof.
  intros K i ss scr ss' scs scr' H. unfold sym_stepXF in H.
  destruct (sym_stepF segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  rewrite cap_rd_know. exact (sym_stepF_kext _ _ _ _ _ _ E).
Qed.

Fixpoint sym_execTXFBI_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXFBI bc kx K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXFBI_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXFBI1 (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXFBI_go bc kx t K fuel first stops (clr ss) (clr ss).

Lemma sym_execTXFBI_go_eq : forall t K fuel first stops ss ck,
  sym_execTXFBI_go (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) t K fuel first stops ss ck = sym_execTXF_go segs t K fuel first stops ss ck.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
  cbn [sym_execTXFBI_go sym_execTXF_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXFBI_eq. destruct (sym_stepXF segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
  destruct scs; [|reflexivity].
  rewrite <- (kext_facts _ _ (sym_stepXF_kext _ _ _ _ _ _ _ E)), <- (kext_kix _ _ (sym_stepXF_kext _ _ _ _ _ _ _ E)). apply IH.
Qed.

Lemma sym_execTXFBI1_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXFBI1 (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss = sym_execTXF segs t K fuel first stops ss.
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXFBI1, sym_execTXF.
  replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
  apply sym_execTXFBI_go_eq.
Qed.

(* [comment removed for export] *)
Definition sym_stepFBI3 (bc : bctx) (kx : kix) (qm : qmemo) (i : instr) (ss : sym_state) (scr : scripts) : stepres * qmemo :=
  if negb (is_fp_instr i) then sym_stepBI3 bc kx qm segs i ss scr else
  if negb (s_clean ss) then (SStop, qm) else
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | FLoad fmt rd rs imm =>
      let n := fmt_bytes fmt in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      if (match s_log ss with [] => true | _ => false end
          && fload_img_ok segs (s_know ss) (mkAlu ALU_ADD (g rs) (ELit (bv_signed imm))) n)%bool
      then (SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) (s_next ss) (s_resv ss)) [] scr, qm)
      else
      let '(r, qm') := sym_readBI3 segs ss bc kx qm scr a n false in
      (match r with
       | None => SStop
       | Some (_, scs, scr', nx') => SOk (SSR (p + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
       end, qm')
  | _ => (sym_stepFBI bc kx i ss scr, qm)
  end.
Lemma sym_stepFBI3_eq : forall bc kx qm i ss scr,
  QM_OK kx qm ->
  fst (sym_stepFBI3 bc kx qm i ss scr) = sym_stepFBI bc kx i ss scr
  /\ QM_OK kx (snd (sym_stepFBI3 bc kx qm i ss scr)).
Proof.
  intros bc kx qm i ss scr HQ. unfold sym_stepFBI3, sym_stepFBI.
  destruct (is_fp_instr i) eqn:HF; cbn [negb]; [|apply sym_stepBI3_eq; exact HQ].
  destruct (s_clean ss) eqn:HC; cbn [negb]; [|split; [reflexivity|exact HQ]].
  destruct i; try (split; [reflexivity|exact HQ]).
  cbv zeta. match goal with |- context [if (?a && ?b)%bool then _ else _] => destruct (a && b)%bool end; [split; [reflexivity|exact HQ]|].
  match goal with |- context [sym_readBI3 ?sg ?s ?b ?k ?q ?sc ?a ?n ?sx] =>
    destruct (sym_readBI3_eq sg s b k q sc a n sx HQ) as [E HQ'];
    destruct (sym_readBI3 sg s b k q sc a n sx) as [r qm']; cbn [fst snd] in E, HQ' |- *; rewrite <- E end.
  split; [destruct r as [[[[? ?] ?] ?]|]; reflexivity | exact HQ'].
Qed.
Definition sym_stepXFBI3 (bc : bctx) (kx : kix) (qm : qmemo) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres * qmemo :=
  let '(r, qm') := sym_stepFBI3 bc kx qm i ss scr in
  (match r with
   | SOk ss' scs scr' => SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
   | SStop => SStop
   end, qm').
Lemma sym_stepXFBI3_eq : forall bc kx qm K i ss scr,
  QM_OK kx qm ->
  fst (sym_stepXFBI3 bc kx qm K i ss scr) = sym_stepXFBI bc kx K i ss scr
  /\ QM_OK kx (snd (sym_stepXFBI3 bc kx qm K i ss scr)).
Proof.
  intros bc kx qm K i ss scr HQ. unfold sym_stepXFBI3, sym_stepXFBI.
  destruct (sym_stepFBI3_eq bc kx qm i ss scr HQ) as [E HQ'].
  destruct (sym_stepFBI3 bc kx qm i ss scr) as [r qm']. cbn [fst snd] in E, HQ' |- *. subst r.
  split; [reflexivity|exact HQ'].
Qed.
Fixpoint sym_execTXFBI3_go (bc : bctx) (kx : kix) (qm : qmemo) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXFBI3 bc kx qm K i ss scr_nil with
          | (SOk ss' [] _, qm') => sym_execTXFBI3_go bc kx qm' t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Lemma sym_execTXFBI3_go_eq : forall bc kx t K fuel first stops ss ck qm,
  QM_OK kx qm ->
  sym_execTXFBI3_go bc kx qm t K fuel first stops ss ck = sym_execTXFBI_go bc kx t K fuel first stops ss ck.
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck qm HQ; [reflexivity|].
  cbn [sym_execTXFBI3_go sym_execTXFBI_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  destruct (sym_stepXFBI3_eq bc kx qm K i ss scr_nil HQ) as [E HQ'].
  destruct (sym_stepXFBI3 bc kx qm K i ss scr_nil) as [r qm']. cbn [fst snd] in E, HQ'. rewrite <- E.
  destruct r as [ss' scs scr'|]; [|reflexivity]. destruct scs; [|reflexivity]. apply IH. exact HQ'.
Qed.
Definition sym_execTXFBI (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXFBI3_go bc kx [] t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXFBI_eq1 : forall bc kx t K fuel first stops ss,
  sym_execTXFBI bc kx t K fuel first stops ss = sym_execTXFBI1 bc kx t K fuel first stops ss.
Proof. intros. unfold sym_execTXFBI, sym_execTXFBI1. apply sym_execTXFBI3_go_eq. apply QM_OK_nil. Qed.
Lemma sym_execTXFBI_eq : forall kn0 t K fuel first stops ss,
  s_know ss = kn0 ->
  sym_execTXFBI (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss = sym_execTXF segs t K fuel first stops ss.
Proof. intros. rewrite sym_execTXFBI_eq1. apply sym_execTXFBI1_eq. assumption. Qed.

(* [comment removed for export] *)
Lemma sym_execTXF_go_kext : forall t K fuel first stops ss ck kn0,
  kext (s_know ck) kn0 -> kext (s_know ss) kn0 ->
  kext (s_know (sym_execTXF_go segs t K fuel first stops ss ck)) kn0.
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck kn0 Hck Hss.
  - cbn. destruct (s_clean ss); [exact Hss|exact Hck].
  - cbn [sym_execTXF_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); [exact Hss|exact Hck]|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); [exact Hss|exact Hck]].
    destruct (sym_stepXF segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); [exact Hss|exact Hck]].
    destruct scs; [|destruct (s_clean ss); [exact Hss|exact Hck]].
    pose proof (kext_trans _ _ _ (sym_stepXF_kext _ _ _ _ _ _ _ E) Hss) as HK.
    apply IH; [|exact HK]. destruct (s_clean ss'); [exact HK|exact Hck].
Qed.

Lemma sym_execTXF_kext : forall t K fuel first stops ss,
  kext (s_know (sym_execTXF segs t K fuel first stops ss)) (s_know ss).
Proof.
  intros. unfold sym_execTXF. apply sym_execTXF_go_kext; (replace (s_know (clr ss)) with (s_know ss) by (destruct ss; reflexivity)); apply kext_refl.
Qed.
Lemma sym_execTXF_facts : forall t K fuel first stops ss,
  facts_of (s_know (sym_execTXF segs t K fuel first stops ss)) = facts_of (s_know ss).
Proof. intros. apply kext_facts. apply sym_execTXF_kext. Qed.

End WithSegs.
End AX2FB.
