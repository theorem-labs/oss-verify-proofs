(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore CxPlan CxfCarry CxfCarry2 CxfGc CxfRt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFE.
Import AX2. Import AX2B. Import APC.

(* [comment removed for export] *)
Definition grows (i : instr) : bool :=
  match i with Store _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition se_br (bc : bctx) (e : sentry) : option (Z * Z) := match e with SE a _ _ => base_rangeB bc (a_base a) end.
Definition ranges_apartQRb (bc : bctx) (r1 br2 : option (Z * Z)) (RQ RS : list positive)
           (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  if (match r1, br2 with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartR bc RQ RS then true
  else lin_apartB bc b1 k1 n1 b2 k2 n2.
Fixpoint log_lookupQLb (bc : bctx) (log : list sentry) (lrs : list (list positive)) (lbr : list (option (Z * Z))) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) (q : option (option (Z * Z) * list positive)) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      let lrs' := match lrs with _ :: t => t | [] => [] end in
      let lbr' := match lbr with _ :: t => t | [] => [] end in
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupQLb bc rest lrs' lbr' rb rk n sx hints acc q
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let q' := match q with Some x => x | None => (base_rangeB bc rb, regs bc rb rk (Z.of_nat n)) end in
          let rs := match lrs with r :: _ => r | [] => regs bc kb kk (Z.of_nat w) end in
          let br := match lbr with r :: _ => r | [] => base_rangeB bc kb end in
          if ranges_apartQRb bc (fst q') br (snd q') rs rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupQLb bc rest lrs' lbr' rb rk n sx hints acc (Some q')
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupQLb bc rest lrs' lbr' rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) (Some q')
          end
      end
  end.
Lemma log_lookupQLb_eq : forall bc log lrs lbr rb rk n sx hints acc q,
  lbr = map (se_br bc) log ->
  log_lookupQLb bc log lrs lbr rb rk n sx hints acc q = log_lookupQL bc log lrs rb rk n sx hints acc q.
Proof.
  intros bc log. induction log as [|[[kb kk] w v] rest IH]; intros lrs lbr rb rk n sx hints acc q ->; [reflexivity|].
  cbn [log_lookupQLb log_lookupQL map se_br a_base]. unfold ranges_apartQRb, ranges_apartQR.
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH. reflexivity.
  - match goal with |- (if ?c then _ else _) = _ => destruct c end; [apply IH; reflexivity|].
    destruct hints as [|[|] hs]; [| | reflexivity]; apply IH; reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Definition sym_readBIF (ss : sym_state) (bc : bctx) (kx : kix) (lrs : list (list positive)) (lbr : list (option (Z * Z))) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupQLb bc (s_log ss) lrs lbr (a_base a) (a_off a) n sx' (sc_hints scr) [] None with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.
Lemma sym_readBIF_eq : forall ss bc kx lrs lbr scr a n sx', lbr = map (se_br bc) (s_log ss) ->
  sym_readBIF ss bc kx lrs lbr scr a n sx' = sym_readBI segs ss bc kx lrs scr a n sx'.
Proof. intros. unfold sym_readBIF, sym_readBI. rewrite log_lookupQLb_eq by assumption. reflexivity. Qed.

Definition sym_stepBIF (bc : bctx) (kx : kix) (lrs : list (list positive)) (lbr : list (option (Z * Z))) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBIF ss bc kx lrs lbr scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIF ss bc kx lrs lbr scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBIF ss bc kx lrs lbr scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.

Lemma sym_stepBIF_eq : forall bc kx lrs lbr i ss scr, lbr = map (se_br bc) (s_log ss) ->
  sym_stepBIF bc kx lrs lbr i ss scr = sym_stepBI bc kx lrs segs i ss scr.
Proof.
  intros bc kx lrs lbr i ss scr L. unfold sym_stepBIF, sym_stepBI.
  destruct i; try reflexivity; rewrite ?(sym_readBIF_eq _ _ _ _ _ _ _ _ _ L); reflexivity.
Qed.
Definition sym_stepXBIF (bc : bctx) (kx : kix) (lrs : list (list positive)) (lbr : list (option (Z * Z))) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBIF bc kx lrs lbr i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Lemma sym_stepXBIF_eq : forall bc kx lrs lbr K i ss scr, lbr = map (se_br bc) (s_log ss) ->
  sym_stepXBIF bc kx lrs lbr K i ss scr = sym_stepXBI segs bc kx lrs K i ss scr.
Proof. intros. unfold sym_stepXBIF, sym_stepXBI. rewrite sym_stepBIF_eq by assumption. reflexivity. Qed.

Lemma sym_stepBI_logk : forall bc kx lrs i ss scr ss' scs scr',
  sym_stepBI bc kx lrs segs i ss scr = SOk ss' scs scr' ->
  if grows i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss.
Proof.
  intros bc kx lrs i ss scr ss' scs scr' H. unfold sym_stepBI, sset, sjump in H.
  destruct i; cbn [grows]; try discriminate;
  repeat (lazymatch type of H with
          | SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
          | (match ?x with _ => _ end) = _ => destruct x
          | (let (_, _) := ?x in _) = _ => destruct x
          | (if ?x then _ else _) = _ => destruct x
          end); try discriminate; cbn [s_log]; first [reflexivity | eexists; reflexivity].
Qed.
Lemma sym_stepXBI_logk : forall bc kx lrs K i ss scr ss' scs scr',
  sym_stepXBI segs bc kx lrs K i ss scr = SOk ss' scs scr' ->
  if grows i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss.
Proof.
  intros bc kx lrs K i ss scr ss' scs scr' H. unfold sym_stepXBI in H.
  destruct (sym_stepBI bc kx lrs segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
  rewrite cap_rd_log. exact (sym_stepBI_logk _ _ _ _ _ _ _ _ _ E).
Qed.

Definition lrs_stepF (bc : bctx) (i : instr) (ss' : sym_state) (lrs : list (list positive)) : list (list positive) :=
  if grows i then match s_log ss' with e :: _ => regsE bc e :: lrs | [] => lrs end else lrs.
Lemma lrs_stepF_eq : forall bc kx lrs K i ss scr ss' scs scr',
  sym_stepXBI segs bc kx lrs K i ss scr = SOk ss' scs scr' ->
  lrs_stepF bc i ss' lrs = lrs_step bc ss ss' lrs.
Proof.
  intros bc kx lrs K i ss scr ss' scs scr' H. pose proof (sym_stepXBI_logk _ _ _ _ _ _ _ _ _ _ H) as L.
  unfold lrs_stepF, lrs_step. destruct (grows i).
  - destruct L as [e L]. rewrite L. cbn [length].
    replace (Nat.eqb (S (length (s_log ss))) (length (s_log ss))) with false; [reflexivity|].
    symmetry. apply Nat.eqb_neq. lia.
  - rewrite L, Nat.eqb_refl. reflexivity.
Qed.
Lemma logk_disj : forall i (ss ss' : sym_state),
  (if grows i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss) ->
  s_log ss' = s_log ss \/ exists e, s_log ss' = e :: s_log ss.
Proof. intros i ss ss' H. destruct (grows i); [right|left]; exact H. Qed.

Definition lbr_stepF (bc : bctx) (i : instr) (ss' : sym_state) (lbr : list (option (Z * Z))) : list (option (Z * Z)) :=
  if grows i then match s_log ss' with e :: _ => se_br bc e :: lbr | [] => lbr end else lbr.
Lemma lbr_stepF_ok : forall bc i (ss ss' : sym_state) lbr,
  (if grows i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss) ->
  lbr = map (se_br bc) (s_log ss) -> lbr_stepF bc i ss' lbr = map (se_br bc) (s_log ss').
Proof.
  intros bc i ss ss' lbr H ->. unfold lbr_stepF. destruct (grows i).
  - destruct H as [e H]. rewrite H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Variable IT : itab.

Fixpoint goF (bc : bctx) (kx : kix) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
         (lrs lck : list (list positive)) (lbr : list (option (Z * Z))) : sym_state * list (list positive) :=
  match fuel with
  | O => if s_clean ss then (ss, lrs) else (ck, lck)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, lrs) else (ck, lck)) else
      match itab_lookup IT (s_pc ss) with
      | None => if s_clean ss then (ss, lrs) else (ck, lck)
      | Some i =>
          match sym_stepXBIF bc kx lrs lbr K i ss scr_nil with
          | SOk ss' [] _ =>
              let lrs' := lrs_stepF bc i ss' lrs in
              let lbr' := lbr_stepF bc i ss' lbr in
              if s_clean ss' then goF bc kx K f false stops ss' ss' lrs' lrs' lbr' else goF bc kx K f false stops ss' ck lrs' lck lbr'
          | _ => if s_clean ss then (ss, lrs) else (ck, lck)
          end
      end
  end.
Lemma goF_fst : forall bc kx K fuel first stops ss ck lrs lck lbr, lbr = map (se_br bc) (s_log ss) ->
  fst (goF bc kx K fuel first stops ss ck lrs lck lbr) = sym_execTXBI_go segs bc kx IT K fuel first stops ss ck lrs.
Proof.
  intros bc kx K fuel. induction fuel as [|f IH]; intros first stops ss ck lrs lck lbr LB.
  - cbn [goF sym_execTXBI_go]. destruct (s_clean ss); reflexivity.
  - cbn [goF sym_execTXBI_go]. destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); reflexivity|].
    destruct (itab_lookup IT (s_pc ss)) as [i|]; [|destruct (s_clean ss); reflexivity].
    rewrite (sym_stepXBIF_eq _ _ _ _ _ _ _ _ LB).
    destruct (sym_stepXBI segs bc kx lrs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); reflexivity].
    destruct scs; [|destruct (s_clean ss); reflexivity]. cbv zeta.
    rewrite (lrs_stepF_eq _ _ _ _ _ _ _ _ _ _ E).
    pose proof (lbr_stepF_ok bc i ss ss' lbr (sym_stepXBI_logk _ _ _ _ _ _ _ _ _ _ E) LB) as LB'.
    destruct (s_clean ss'); apply IH; exact LB'.
Qed.
Lemma goF_snd : forall bc kx K fuel first stops ss ck lrs lck lbr,
  lrs = map (regsE bc) (s_log ss) -> lck = map (regsE bc) (s_log ck) -> lbr = map (se_br bc) (s_log ss) ->
  snd (goF bc kx K fuel first stops ss ck lrs lck lbr) = map (regsE bc) (s_log (fst (goF bc kx K fuel first stops ss ck lrs lck lbr))).
Proof.
  intros bc kx K fuel. induction fuel as [|f IH]; intros first stops ss ck lrs lck lbr L1 L2 LB.
  - cbn [goF]. destruct (s_clean ss); assumption.
  - cbn [goF]. destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); assumption|].
    destruct (itab_lookup IT (s_pc ss)) as [i|]; [|destruct (s_clean ss); assumption].
    rewrite (sym_stepXBIF_eq _ _ _ _ _ _ _ _ LB).
    destruct (sym_stepXBI segs bc kx lrs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); assumption].
    destruct scs; [|destruct (s_clean ss); assumption]. cbv zeta.
    assert (L' : lrs_stepF bc i ss' lrs = map (regsE bc) (s_log ss')).
    { rewrite (lrs_stepF_eq _ _ _ _ _ _ _ _ _ _ E). apply lrs_step_ok; [|exact L1].
      exact (logk_disj _ _ _ (sym_stepXBI_logk _ _ _ _ _ _ _ _ _ _ E)). }
    pose proof (lbr_stepF_ok bc i ss ss' lbr (sym_stepXBI_logk _ _ _ _ _ _ _ _ _ _ E) LB) as LB'.
    destruct (s_clean ss'); apply IH; assumption.
Qed.

Variable nx0 : nat.

Definition run_block_f (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  if fresh_ok nx0 cs then
    let ss := a_ss cs in
    let bc := mkbc (facts_of (s_know ss)) in
    let kx := mk_kix (s_know ss) in
    let ss0 := clr (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    let '(ss', lrs) := goF bc kx K fuel true stops ss0 ss0 [] [] [] in
    match CXFC2.carryKFL2 bc (s_log ss') lrs (s_know ss') [] with
    | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
    | _ => None
    end
  else None.
Lemma run_block_f_eq : forall K fuel stops cs, run_block_f K fuel stops cs = run_block segs IT nx0 K fuel stops cs.
Proof.
  intros. unfold run_block_f, run_block. destruct (fresh_ok nx0 cs); [|reflexivity]. cbv zeta.
  set (bc := mkbc (facts_of (s_know (a_ss cs)))). set (kx := mk_kix (s_know (a_ss cs))).
  set (ss0 := clr (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))).
  pose proof (goF_fst bc kx K fuel true stops ss0 ss0 [] [] [] eq_refl) as E1.
  pose proof (goF_snd bc kx K fuel true stops ss0 ss0 [] [] [] eq_refl eq_refl eq_refl) as E2.
  destruct (goF bc kx K fuel true stops ss0 ss0 [] [] []) as [ss' lrs]. cbn [fst snd] in E1, E2.
  unfold sym_execTXBI. cbn [s_log map]. fold ss0. rewrite <- E1.
  pose proof (CXFC2.carryKFL2_eq (facts_of (s_know (a_ss cs))) (s_log ss') lrs (s_know ss') [] E2) as EK. fold bc in EK. rewrite EK. clear EK.
  rewrite (CXFC.carryKFL_eq bc (s_log ss') lrs (s_know ss') [] (mkbc_rt _) E2). rewrite CXFC.carryKF_eq by apply mkbc_rt. reflexivity.
Qed.

Definition run_block_gc_f (K : nat) (fuel : nat) (stops : list Z) (cs : acs) : option acs :=
  match run_block_f K fuel stops cs with Some cs' => Some (CXFG.cs_gcF nx0 cs') | None => None end.
Lemma run_block_gc_f_eq : forall K fuel stops cs, run_block_gc_f K fuel stops cs = run_block_gc segs IT nx0 K fuel stops cs.
Proof. intros. unfold run_block_gc_f, run_block_gc. rewrite run_block_f_eq. destruct (run_block segs IT nx0 K fuel stops cs); [rewrite CXFG.cs_gcF_eq|]; reflexivity. Qed.
(* [comment removed for export] *)
Definition run_block_c (K : nat) (fuel : nat) (stops : list Z) (c : CXFRT.rtc) (cs : acs) : option acs * CXFRT.rtc :=
  if fresh_ok nx0 cs then
    let ss := a_ss cs in
    let bcc := CXFRT.mkbc_c c (facts_of (s_know ss)) in
    let bc := fst bcc in
    let kx := mk_kix (s_know ss) in
    let ss0 := clr (SS (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss)) in
    let '(ss', lrs) := goF bc kx K fuel true stops ss0 ss0 [] [] [] in
    (match CXFC2.carryKFL2 bc (s_log ss') lrs (s_know ss') [] with
     | (kn', [], _) => Some (with_ss cs (mk_ss (s_pc ss') (s_regs ss') kn' (s_next ss')))
     | _ => None
     end, snd bcc)
  else (None, c).
Lemma run_block_c_spec : forall K fuel stops c cs, CXFRT.rtc_ok c ->
  fst (run_block_c K fuel stops c cs) = run_block_f K fuel stops cs /\ CXFRT.rtc_ok (snd (run_block_c K fuel stops c cs)).
Proof.
  intros K fuel stops c cs H. unfold run_block_c, run_block_f. destruct (fresh_ok nx0 cs); [|split; [reflexivity|exact H]].
  destruct (CXFRT.mkbc_c_spec c (facts_of (s_know (a_ss cs))) H) as [E1 E2]. cbv zeta. rewrite E1.
  destruct (goF (mkbc (facts_of (s_know (a_ss cs)))) (mk_kix (s_know (a_ss cs))) K fuel true stops
              (clr (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs))))
              (clr (SS (s_pc (a_ss cs)) (s_regs (a_ss cs)) [] (s_know (a_ss cs)) (s_next (a_ss cs)))) [] [] []) as [ss' lrs].
  cbn [fst snd]. split; [reflexivity|exact E2].
Qed.
Definition run_block_gc_c (K : nat) (fuel : nat) (stops : list Z) (c : CXFRT.rtc) (cs : acs) : option acs * CXFRT.rtc :=
  let r := run_block_c K fuel stops c cs in
  (match fst r with Some cs' => Some (CXFG.cs_gcF nx0 cs') | None => None end, snd r).
Lemma run_block_gc_c_spec : forall K fuel stops c cs, CXFRT.rtc_ok c ->
  fst (run_block_gc_c K fuel stops c cs) = run_block_gc_f K fuel stops cs /\ CXFRT.rtc_ok (snd (run_block_gc_c K fuel stops c cs)).
Proof.
  intros K fuel stops c cs H. unfold run_block_gc_c, run_block_gc_f. destruct (run_block_c_spec K fuel stops c cs H) as [E1 E2].
  cbn [fst snd]. rewrite E1. split; [reflexivity|exact E2].
Qed.
End WithSegs.

(* [comment removed for export] *)
Definition RB_c (segs : list Segment) (IT : itab) (GC : bool) (KC bfuel : nat) (c : CXFRT.rtc) (gb : nat) (stops : list Z) (cs : acs) : option acs * CXFRT.rtc :=
  if GC then run_block_gc_c segs IT gb KC bfuel stops c cs else run_block_c segs IT gb KC bfuel stops c cs.

(* [comment removed for export] *)
Definition RB_f (segs : list Segment) (IT : itab) (GC : bool) (KC bfuel : nat) (gb : nat) (stops : list Z) (cs : acs) : option acs :=
  if GC then run_block_gc_f segs IT gb KC bfuel stops cs else run_block_f segs IT gb KC bfuel stops cs.
Lemma RB_f_eq : forall segs IT GC KC bfuel gb stops cs,
  RB_f segs IT GC KC bfuel gb stops cs = CAP.run_block_gcx segs IT GC gb KC bfuel stops cs.
Proof. intros. unfold RB_f, CAP.run_block_gcx. rewrite run_block_gc_f_eq, run_block_f_eq. reflexivity. Qed.

Lemma RB_c_spec : forall segs IT GC KC bfuel c gb stops cs, CXFRT.rtc_ok c ->
  fst (RB_c segs IT GC KC bfuel c gb stops cs) = RB_f segs IT GC KC bfuel gb stops cs /\ CXFRT.rtc_ok (snd (RB_c segs IT GC KC bfuel c gb stops cs)).
Proof. intros. unfold RB_c, RB_f. destruct GC; [apply run_block_gc_c_spec | apply run_block_c_spec]; assumption. Qed.
End CXFE.
