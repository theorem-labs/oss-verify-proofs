(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymStepR.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosFxStep PIosFxSound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegSR SegLearn SegFPSteps SegDisch SegFP SegAcc SegSrl SegLin SegSlt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2B. Import AX2S. Import AX2F.

Module SX.
Import SDI.

Record sexit : Type := SXT { x_ss : sym_state; x_path : list sidecond }.

Definition is_readbase (sc : sidecond) : bool := match sc with SCReadBase _ _ _ _ => true | _ => false end.

Definition set_know (ss : sym_state) (kn : list kentry) : sym_state :=
  SSR (s_pc ss) (s_regs ss) (s_log ss) kn (s_next ss) (s_resv ss).

Definition is_nilb {A} (l : list A) : bool := match l with [] => true | _ => false end.

(* [comment removed for export] *)
Definition add_respell (kn : list kentry) (e : expr) : option expr :=
  match e with
  | EAlu ALU_ADD b (ELit z) =>
      match SSR.srange kn b with
      | Some (lo, hi) => if Z.ltb lo 0 then (if Z.leb 0 (lo + z) then Some (EAlu ALU_ADD (ELit z) b) else None) else None
      | None => None
      end
  | _ => None
  end.

Definition ar_state (ss : sym_state) (rd : reg) : sym_state :=
  if bv_eqb rd 0 then ss else
  match add_respell (facts_of (s_know ss)) (sr_get (s_regs ss) rd) with
  | Some e' => SSR (s_pc ss) (sr_upd (s_regs ss) (ridx rd) e') (s_log ss) (s_know ss) (s_next ss) (s_resv ss)
  | None => ss
  end.

Lemma ar_know : forall ss rd, s_know (ar_state ss rd) = s_know ss.
Proof. intros ss rd. unfold ar_state. destruct (bv_eqb rd 0); [reflexivity|]. destruct (add_respell _ _); reflexivity. Qed.
Lemma ar_next : forall ss rd, s_next (ar_state ss rd) = s_next ss.
Proof. intros ss rd. unfold ar_state. destruct (bv_eqb rd 0); [reflexivity|]. destruct (add_respell _ _); reflexivity. Qed.
Lemma ar_resv : forall ss rd, s_resv (ar_state ss rd) = s_resv ss.
Proof. intros ss rd. unfold ar_state. destruct (bv_eqb rd 0); [reflexivity|]. destruct (add_respell _ _); reflexivity. Qed.

Lemma add_respell_sound : forall kn e e', add_respell kn e = Some e' -> forall E, edenot E e' = edenot E e.
Proof.
  intros kn e e' H E. unfold add_respell in H.
  destruct e as [| |op b c| | | | |]; try discriminate. destruct op; try discriminate. destruct c as [z| | | | | | |]; try discriminate.
  destruct (SSR.srange kn b) as [[lo hi]|]; [|discriminate]. destruct (Z.ltb lo 0); [|discriminate].
  destruct (Z.leb 0 (lo + z)); [|discriminate]. injection H as <-.
  cbn [edenot alu64 alu]. apply bv_eq. rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(* [comment removed for export] *)
Fixpoint has_srl (ts : list (Z * expr)) : bool :=
  match ts with [] => false | (_, a) :: r => match a with EAlu ALU_SRL _ (ELit _) => true | _ => has_srl r end end.
(* [comment removed for export] *)
Definition cancels (rb kb : expr) : bool :=
  let kt := snd (lin_of kb) in
  match kt with
  | [] => false
  | _ => forallb (fun t => negb (existsb (fun u => expr_eqb (snd t) (snd u)) kt)) (snd (lin_of (mkAlu ALU_SUB rb kb)))
  end.
(* [comment removed for export] *)
Definition srange_in (fk : list kentry) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  match kb, len with
  | ELit z0, ELit l0 =>
      match SSR.srange fk rb with
      | Some (lo, hi) => if Z.leb 0 lo then
                           if Z.leb (z0 mod 2 ^ 64 + kk) (lo + rk) then Z.leb (hi + rk + Z.of_nat n) (z0 mod 2 ^ 64 + kk + l0 mod 2 ^ 64)
                           else false
                         else false
      | None => false
      end
  | _, _ => false
  end.
Definition zf_in (fk : list kentry) (srl : bool) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
  if xinside fk rb rk (elen n) kb kk len then true
  else if srl then (if SLin.xinside2 fk rb rk (elen n) kb kk len then true else srange_in fk rb rk n kb kk len)
  else if cancels rb kb then SLin.xinside2 fk rb rk (elen n) kb kk len else srange_in fk rb rk n kb kk len.
Fixpoint zf_read0 (fk : list kentry) (srl : bool) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) (sx : bool) : option Z :=
  match kn with
  | [] => None
  | K :: r =>
      match K with
      | KZero (SA kb kk) len => if zf_in fk srl rb rk n kb kk len then Some 0%Z else zf_read0 fk srl r rb rk n sx
      | KFill (SA kb kk) len c =>
          if Nat.eqb n 1 then
            (if zf_in fk srl rb rk n kb kk len then Some (extz sx 1 (c mod 256)%Z) else zf_read0 fk srl r rb rk n sx)
          else zf_read0 fk srl r rb rk n sx
      | _ => zf_read0 fk srl r rb rk n sx
      end
  end.
Definition zf_read (kn : list kentry) (a : saddr) (n : nat) (sx : bool) : option Z :=
  if Nat.leb 1 n then if Nat.leb n 8 then
    zf_read0 (facts_of kn) (has_srl (snd (lin_of (a_base a)))) kn (a_base a) (a_off a) n sx else None else None.

(* [comment removed for export] *)
Definition respell (ss : sym_state) (i0 : nat) (scs : list sidecond) (i : instr) : sym_state :=
  match i with
  | Load _ _ rd _ _ =>
    match find_readbase i0 scs with
    | Some (a, n, sx) =>
        if (bv_eqb rd 0 || negb (expr_eqb (sr_get (s_regs ss) rd) (EVar i0)))%bool then ss else
        match zf_read (s_know ss) a n sx with
        | Some v => SSR (s_pc ss) (sr_upd (s_regs ss) (ridx rd) (ELit v)) (s_log ss) (s_know ss) (s_next ss) (s_resv ss)
        | None =>
            if (sx || negb (Nat.ltb n 8))%bool then ss
            else SSR (s_pc ss) (sr_upd (s_regs ss) (ridx rd) (EExt false 0 n (EVar i0))) (s_log ss) (s_know ss) (s_next ss) (s_resv ss)
        end
    | None => ss
    end
  | Op ALU_ADD rd _ _ | OpImm ALU_ADD rd _ _ => ar_state ss rd
  | ShiftImm ALU_SRL rd _ _ =>     (* [comment removed for export] *)
    if bv_eqb rd 0 then ss else
    match sr_get (s_regs ss) rd with
    | EAlu ALU_SRL a (ELit sh) =>
        match SSRL.srl_split (facts_of (s_know ss)) a sh with
        | Some e' => SSR (s_pc ss) (sr_upd (s_regs ss) (ridx rd) e') (s_log ss) (s_know ss) (s_next ss) (s_resv ss)
        | None => ss
        end
    | _ => ss
    end
  | _ => ss
  end.

Lemma respell_know : forall ss i0 scs i, s_know (respell ss i0 scs i) = s_know ss.
Proof.
  intros ss i0 scs i. unfold respell. destruct i; try reflexivity.
  - destruct (find_readbase i0 scs) as [[[a n] sx]|]; try reflexivity. destruct (_ || _)%bool; [reflexivity|].
    destruct (zf_read _ _ _ _); [reflexivity|]. destruct (_ || _)%bool; reflexivity.
  - destruct op; try reflexivity. apply ar_know.
  - destruct op; try reflexivity. destruct (bv_eqb rd 0); [reflexivity|]. destruct (sr_get (s_regs ss) rd) as [| |op' a b| | | | |]; try reflexivity.
    destruct op'; try reflexivity. destruct b; try reflexivity. destruct (SSRL.srl_split _ _ _); reflexivity.
  - destruct op; try reflexivity. apply ar_know.
Qed.
Lemma respell_next : forall ss i0 scs i, s_next (respell ss i0 scs i) = s_next ss.
Proof.
  intros ss i0 scs i. unfold respell. destruct i; try reflexivity.
  - destruct (find_readbase i0 scs) as [[[a n] sx]|]; try reflexivity. destruct (_ || _)%bool; [reflexivity|].
    destruct (zf_read _ _ _ _); [reflexivity|]. destruct (_ || _)%bool; reflexivity.
  - destruct op; try reflexivity. apply ar_next.
  - destruct op; try reflexivity. destruct (bv_eqb rd 0); [reflexivity|]. destruct (sr_get (s_regs ss) rd) as [| |op' a b| | | | |]; try reflexivity.
    destruct op'; try reflexivity. destruct b; try reflexivity. destruct (SSRL.srl_split _ _ _); reflexivity.
  - destruct op; try reflexivity. apply ar_next.
Qed.
Lemma respell_resv : forall ss i0 scs i, s_resv (respell ss i0 scs i) = s_resv ss.
Proof.
  intros ss i0 scs i. unfold respell. destruct i; try reflexivity.
  - destruct (find_readbase i0 scs) as [[[a n] sx]|]; try reflexivity. destruct (_ || _)%bool; [reflexivity|].
    destruct (zf_read _ _ _ _); [reflexivity|]. destruct (_ || _)%bool; reflexivity.
  - destruct op; try reflexivity. apply ar_resv.
  - destruct op; try reflexivity. destruct (bv_eqb rd 0); [reflexivity|]. destruct (sr_get (s_regs ss) rd) as [| |op' a b| | | | |]; try reflexivity.
    destruct op'; try reflexivity. destruct b; try reflexivity. destruct (SSRL.srl_split _ _ _); reflexivity.
  - destruct op; try reflexivity. apply ar_resv.
Qed.

(* [comment removed for export] *)
Inductive split : Type :=
| SpCmpG (v : bool) (pc : Z) (c : branch_cond) (e1 e2 : expr)
| SpEnumG (v : bool) (pc : Z) (e : expr) (lo hi : Z)
| SpHav (pc : Z) (r : nat)
| SpSlt (pc : Z)
| SpW (pc : Z)
| SpAl (pc : Z)
| SpEnumS (pc : Z) (n : nat) (lo hi : Z)
| SpRdK (pc : Z).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SpCmp (pc : Z) (c : branch_cond) (e1 e2 : expr) : split := SpCmpG false pc c e1 e2.
Definition SpEnum (pc : Z) (e : expr) (lo hi : Z) : split := SpEnumG false pc e lo hi.
Definition SpCmpV (pc : Z) (c : branch_cond) (e1 e2 : expr) : split := SpCmpG true pc c e1 e2.
Definition SpEnumV (pc : Z) (e : expr) (lo hi : Z) : split := SpEnumG true pc e lo hi.

Definition sp_pc (sp : split) : Z :=
  match sp with SpCmpG _ pc _ _ _ | SpEnumG _ pc _ _ _ | SpHav pc _ | SpSlt pc | SpW pc | SpAl pc | SpEnumS pc _ _ _ | SpRdK pc => pc end.

Definition shav (ss : sym_state) (r : nat) : sym_state :=
  SSR (s_pc ss) (sr_upd (s_regs ss) (ridx (Z_to_bv 5 (Z.of_nat r))) (EVar (s_next ss))) (s_log ss) (s_know ss) (S (s_next ss))
      (s_resv ss).
Definition slt_lit (kn : list kentry) (e : expr) : expr :=
  match e with
  | EAlu ALU_SLT a b => match SSLT.slt_dec kn a b with Some t => ELit (if t then 1 else 0) | None => e end
  | _ => e
  end.
Definition sslt (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (map (slt_lit (facts_of (s_know ss))) (s_regs ss)) (s_log ss) (s_know ss) (s_next ss) (s_resv ss).
Definition in32o (r : option (Z * Z)) : bool :=
  match r with Some (l, h) => if Z.leb (- 2 ^ 31) l then Z.ltb h (2 ^ 31) else false | None => false end.
(* [comment removed for export] *)
Fixpoint ealignX (kn : list kentry) (e : expr) : Z :=
  match e with
  | EAlu ALU_XOR a b => Z.max (ealign kn e) (Z.min (ealignX kn a) (ealignX kn b))
  | _ => ealign kn e
  end.
(* [comment removed for export] *)
Definition and_zero_ok (kn : list kentry) (a : expr) (m : Z) : bool := Z.ltb (m mod 2 ^ 64) (2 ^ ealignX kn a).
(* [comment removed for export] *)
Definition and_id_ok (kn : list kentry) (a : expr) (m : Z) : bool :=
  let j := ealignX kn a in Z.ltb (2 ^ 64 - 1 - m mod 2 ^ 64) (2 ^ j).
(* [comment removed for export] *)
Definition or_add_ok (kn : list kentry) (a : expr) (c : Z) : bool :=
  let j := ealignX kn a in if Z.leb 1 j then Z.ltb (c mod 2 ^ 64) (2 ^ j) else false.
(* [comment removed for export] *)
Definition clrlow_k (m : Z) : option Z :=
  let low := (2 ^ 64 - m mod 2 ^ 64)%Z in
  if Z.ltb 0 low then (if Z.eqb low (2 ^ Z.log2 low) then Some (Z.log2 low) else None) else None.
Definition and_addc (kn : list kentry) (a : expr) (m : Z) : option expr :=
  match clrlow_k m with
  | Some k =>
      match a with
      | EAlu ALU_ADD x (ELit c) =>
          if Z.leb k (ealignX kn x) then Some (mkAlu ALU_ADD x (ELit (Z.land (c mod 2 ^ 64) (m mod 2 ^ 64)))) else None
      | _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition lo32_strip (e : expr) : expr :=
  match e with
  | EAlu ALU_SRL a (ELit s) =>
      if Z.eqb s 32 then
        match a with
        | EMd M_MUL (ELit k) x => if Z.eqb k 4294967296 then x else e
        | EAlu ALU_SLL x (ELit c) => if Z.eqb c 32 then x else e
        | _ => e
        end
      else e
  | EAlu ALU_AND x (ELit m) => if Z.eqb m 4294967295 then x else e
  | _ => e
  end.
(* [comment removed for export] *)
Definition mulh0 (kn : list kentry) (a b : expr) : bool :=
  match SL.urange kn a, SL.urange kn b with
  | Some (_, ha), Some (_, hb) => if Z.ltb ha (2 ^ 63) then (if Z.ltb hb (2 ^ 63) then Z.ltb (ha * hb) (2 ^ 64) else false) else false
  | _, _ => false
  end.
Definition is_mulh (op : mulop) : bool := match op with M_MULH | M_MULHU | M_MULHSU => true | _ => false end.
Fixpoint wnorm (kn : list kentry) (e : expr) : expr :=
  match e with
  | EAlu op a b => let a' := wnorm kn a in let b' := wnorm kn b in
                   match op, b' with
                   | ALU_AND, ELit m => if and_zero_ok kn a' m then ELit 0 else if and_id_ok kn a' m then a'
                                        else match and_addc kn a' m with
                                             | Some e' => e'
                                             | None => if expr_eqb a a' then (if expr_eqb b b' then e else mkAlu op a' b') else mkAlu op a' b'
                                             end
                   | ALU_OR, ELit c => if or_add_ok kn a' c then mkAlu ALU_ADD a' b'
                                       else if expr_eqb a a' then (if expr_eqb b b' then e else mkAlu op a' b') else mkAlu op a' b'
                   | _, _ => if expr_eqb a a' then (if expr_eqb b b' then e else mkAlu op a' b') else mkAlu op a' b'
                   end
  | EMd op a b => let a' := wnorm kn a in let b' := wnorm kn b in
                  if is_mulh op then (if mulh0 kn a' b' then ELit 0 else
                    if expr_eqb a a' then (if expr_eqb b b' then e else mkMd op a' b') else mkMd op a' b')
                  else if expr_eqb a a' then (if expr_eqb b b' then e else mkMd op a' b') else mkMd op a' b'
  | EAluw op a b => let a' := lo32_strip (wnorm kn a) in let b' := lo32_strip (wnorm kn b) in
      match op with
      | ALU_ADD | ALU_SUB => let f := mkAlu op a' b' in if in32o (SSR.srange kn f) then f else EAluw op a' b'
      | _ => EAluw op a' b'
      end
  | EMdw op a b => let a' := lo32_strip (wnorm kn a) in let b' := lo32_strip (wnorm kn b) in
      match op with
      | M_MUL => let f := mkMd M_MUL a' b' in if in32o (SSR.srange kn f) then f else EMdw op a' b'
      | _ => EMdw op a' b'
      end
  | EExt sx lo n a => EExt sx lo n (wnorm kn a)
  | _ => e
  end.
Definition sw (ss : sym_state) : sym_state :=
  let kn := facts_of (s_know ss) in
  SSR (s_pc ss) (map (fun e => slt_lit kn (wnorm kn e)) (s_regs ss)) (s_log ss) (s_know ss) (s_next ss) (s_resv ss).
Fixpoint find_split (pc : Z) (l : list split) : option split :=
  match l with [] => None | sp :: r => if Z.eqb (sp_pc sp) pc then Some sp else find_split pc r end.

Fixpoint vsub (sg : list expr) (e : expr) : expr :=
  match e with
  | ELit z => ELit z
  | EVar n => nth n sg (ELit 0)
  | EAlu op a b => EAlu op (vsub sg a) (vsub sg b)
  | EAluw op a b => EAluw op (vsub sg a) (vsub sg b)
  | EMd op a b => EMd op (vsub sg a) (vsub sg b)
  | EMdw op a b => EMdw op (vsub sg a) (vsub sg b)
  | EExt sx lo n a => EExt sx lo n (vsub sg a)
  | EBlob sx k i n => EBlob sx k i n
  end.
Definition rsub (ss : sym_state) (e : expr) : expr := vsub (ELit 0 :: tl (s_regs ss)) e.
Definition sp_sub (v : bool) (ss : sym_state) (e : expr) : expr := if v then e else rsub ss e.

(* [comment removed for export] *)

Fixpoint kids_gen (g : Z -> option (list sexit)) (v : Z) (k : nat) : option (list sexit) :=
  match k with
  | O => Some []
  | S k' => match g v, kids_gen g (v + 1) k' with Some l1, Some l2 => Some (l1 ++ l2) | _, _ => None end
  end.

Lemma kids_gen_in : forall g k v xs, kids_gen g v k = Some xs -> forall u, (v <= u < v + Z.of_nat k)%Z ->
  exists l, g u = Some l /\ (forall x, In x l -> In x xs).
Proof.
  intros g k. induction k as [|k IH]; intros v xs H u Hu; [lia|].
  cbn [kids_gen] in H. destruct (g v) as [l1|] eqn:G1; [|discriminate].
  destruct (kids_gen g (v + 1) k) as [l2|] eqn:G2; [|discriminate]. injection H as <-.
  destruct (Z.eq_dec u v) as [->|Hne].
  - exists l1. split; [exact G1|]. intros x Hx. apply in_or_app. left. exact Hx.
  - destruct (IH (v + 1)%Z l2 G2 u ltac:(lia)) as (l & Hg & Hin). exists l. split; [exact Hg|].
    intros x Hx. apply in_or_app. right. exact (Hin x Hx).
Qed.

(* [comment removed for export] *)
Definition awin : Type := (expr * Z * expr)%type.

Definition mem_acc (i : instr) (ss : sym_state) : option (saddr * nat) :=
  let fk := facts_of (s_know ss) in let g r := sr_get (s_regs ss) r in
  match i with
  | Load msz _ _ rs imm => Some (to_saddrK fk (g rs) (bv_signed imm), SAC.msz_nb msz)
  | Store msz rs _ imm => Some (to_saddrK fk (g rs) (bv_signed imm), SAC.msz_nb msz)
  | FLoad fmt _ rs imm => Some (to_saddrK fk (g rs) (bv_signed imm), SAC.fmt_nb fmt)
  | FStore fmt rs _ imm => Some (to_saddrK fk (g rs) (bv_signed imm), SAC.fmt_nb fmt)
  | _ => None
  end.

Definition acc_okb (kn : list kentry) (a : saddr) (n : nat) (W : list awin) : bool :=
  if SLin.ex2 (fun w => let '(b, off, len) := w in xinside kn (a_base a) (a_off a) (elen n) b off len)
              (fun w => let '(b, off, len) := w in SLin.xinside2 kn (a_base a) (a_off a) (elen n) b off len) W then true
  else existsb (fun w => let '(b, off, len) := w in srange_in kn (a_base a) (a_off a) n b off len) W.

Definition acc_check (aw : option (list awin)) (i : instr) (ss : sym_state) : bool :=
  match aw with
  | None => true
  | Some W => if SAC.is_atomic i then false
              else match mem_acc i ss with None => true | Some (a, n) => acc_okb (s_know ss) a n W end
  end.

Definition rd_know (kn : list kentry) (path : list sidecond) : list kentry :=
  match path with
  | SCReadBase (SA b k) n false (EVar v) :: _ =>
      (* [comment removed for export] *)
      if (Nat.leb 1 n && Nat.leb n 8 && SDI.flat_ok kn b k (elen n))%bool
      then [KWord (SA b k) n (if Nat.ltb n 8 then EExt false 0 n (EVar v) else EVar v)] else []
  | _ => []
  end.

Section Explore.
Variable segs : list Segment.
Variable IT : itab.
Variable stops : list Z.
Variable rr : bool.          (* [comment removed for export] *)
Variable sps : list split.   (* [comment removed for export] *)
Variable aw : option (list awin).   (* [comment removed for export] *)

Fixpoint explore (fuel : nat) (first nosp : bool) (bc : bctx) (kx : kix) (ss : sym_state) (path : list sidecond)
  : option (list sexit) :=
  match fuel with
  | O => None
  | S f =>
    if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then
      (if s_clean ss then Some [SXT ss path] else None)
    else
    match (if nosp then None else find_split (s_pc ss) sps) with
    | Some (SpCmpG v _ c e1 e2) =>
        let a := sp_sub v ss e1 in let b := sp_sub v ss e2 in
        if (AxSymRun3.expr_vars_lt (s_next ss) a && AxSymRun3.expr_vars_lt (s_next ss) b)%bool then
          let kn := s_know ss in
          let r1 := match SL.learn (facts_of kn) c true a b with
                    | None => Some []
                    | Some l => let kn1 := l ++ kn in
                                explore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) (SCBr true c a b :: path)
                    end in
          let r0 := match SL.learn (facts_of kn) c false a b with
                    | None => Some []
                    | Some l => let kn0 := l ++ kn in
                                explore f first true (mkbc (facts_of kn0)) (mk_kix kn0) (set_know ss kn0) (SCBr false c a b :: path)
                    end in
          match r1, r0 with Some l1, Some l0 => Some (l1 ++ l0) | _, _ => None end
        else None
    | Some (SpEnumG v _ e lo hi) =>
        let a := sp_sub v ss e in
        if (AxSymRun3.expr_vars_lt (s_next ss) a && Z.leb 0 lo && Z.ltb hi (2^64) &&
            match erange (facts_of (s_know ss)) a with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end)%bool then
          kids_gen (fun v => let kn1 := KRange a v v :: s_know ss in
                             explore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) (SCBr true BC_EQ a (ELit v) :: path))
                   lo (S (Z.to_nat (hi - lo)))
        else None
    | Some (SpEnumS _ n lo hi) =>
        let a := EVar n in
        if (AxSymRun3.expr_vars_lt (s_next ss) a && Z.leb 0 lo && Z.ltb hi (2^64) &&
            match erange (facts_of (s_know ss)) a with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end)%bool then
          kids_gen (fun v => match SL.sub_facts (facts_of (s_know ss)) n v with
                             | None => Some []
                             | Some D => let kn1 := D ++ KRange a v v :: s_know ss in
                                 explore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) (SCBr true BC_EQ a (ELit v) :: path)
                             end)
                   lo (S (Z.to_nat (hi - lo)))
        else None
    | Some (SpRdK _) =>
        let kn1 := rd_know (facts_of (s_know ss)) path ++ s_know ss in
        explore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) path
    | Some (SpHav _ r) => if (Nat.ltb 0 r && Nat.ltb r 32)%bool then explore f first true bc kx (shav ss r) path else None
    | Some (SpSlt _) => explore f first true bc kx (sslt ss) path
    | Some (SpW _) => explore f first true bc kx (sw ss) path
    | Some (SpAl _) =>
        let kn := s_know ss in
        match SL.al_tight (facts_of kn) (facts_of kn) with
        | None => Some []
        | Some l => let kn1 := l ++ kn in explore f first true (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss kn1) path
        end
    | None =>
    match itab_lookup IT (s_pc ss) with
    | None => None
    | Some i =>
      match i with
      | Branch c rs1 rs2 _ =>
        match sym_stepBI bc kx segs i ss (SCR [true] [] []) with
        | SOk ss1 [] _ => explore f false false bc kx ss1 path
        | SOk ss1 (_ :: _) _ =>
          match sym_stepBI bc kx segs i ss (SCR [false] [] []) with
          | SOk ss0 (_ :: _) _ =>
            let a := sr_get (s_regs ss) rs1 in
            let b := sr_get (s_regs ss) rs2 in
            let kn := s_know ss in
            let r1 := match SL.learn (facts_of kn) c true a b with
                      | None => Some []
                      | Some l => let kn1 := l ++ kn in
                                  explore f false false (mkbc (facts_of kn1)) (mk_kix kn1) (set_know ss1 kn1) (SCBr true c a b :: path)
                      end in
            let r0 := match SL.learn (facts_of kn) c false a b with
                      | None => Some []
                      | Some l => let kn0 := l ++ kn in
                                  explore f false false (mkbc (facts_of kn0)) (mk_kix kn0) (set_know ss0 kn0) (SCBr false c a b :: path)
                      end in
            match r1, r0 with Some l1, Some l0 => Some (l1 ++ l0) | _, _ => None end
          | _ => None
          end
        | SStop => None
        end
      | _ =>
        if acc_check aw i ss then
        match (if SFP.is_fp_instr i then SFP.fp_step segs i ss else sym_stepBI bc kx segs i ss scr_nil) with
        | SOk ss' scs _ =>
            if (Nat.leb (s_next ss) (s_next ss') && rest_ok segs bc ss ss' scs)%bool then
              explore f false false bc kx (respell ss' (s_next ss) scs i) (if rr then List.filter is_readbase scs ++ path else path)
            else None
        | SStop => None
        end
        else None
      end
    end
    end
  end.

End Explore.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable segs : list Segment.
Section FX.
Context {fx : FPState}.

Lemma itab_facts : forall t pc i, itab_sound segs t -> itab_lookup t pc = Some i ->
  exists w, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z).
Proof.
  intros t pc i Ht Hl. pose proof (Ht _ _ Hl) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz.
  injection Hen as ->. exists w. auto.
Qed.

(* [comment removed for export] *)
Definition path_okX (base : word -> option byte) (E : env) (n : nat) (path : list sidecond) : Prop :=
  forall E', eagree n E E' -> scs_denot segs base E' path.

Lemma path_okX_le : forall base E E1 n n1 path, path_okX base E n path -> eagree n E E1 -> (n <= n1)%nat ->
  path_okX base E1 n1 path.
Proof.
  intros base E E1 n n1 path H Ha Hle E' Ha'. apply H. eapply eagree_trans; [exact Ha | eapply eagree_le; [exact Ha' | exact Hle]].
Qed.

(* [comment removed for export] *)
Lemma st_okR_svc : forall E base rom ss ms, st_okR segs E base rom ss ms -> ms_svc_pending ms = None.
Proof. intros E base rom ss ms (regs & -> & _). reflexivity. Qed.

(* [comment removed for export] *)
Lemma stepX0_sound : forall E base rom ss ms i ss' scs scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_step segs i ss scr_nil = SOk ss' scs scr' ->
  (s_next ss <= s_next ss')%nat ->
  disch_all segs ss ss' scs ->
  st_okX segs E base rom ss ms ->
  exists E1 ms', eagree (s_next ss) E E1
    /\ RiscvSemantics.step segs ms = MachineOk ms'
    /\ st_okX segs E1 base rom ss' ms'
    /\ (forall E'', eagree (s_next ss') E1 E'' -> scs_denot segs base E'' scs).
Proof.
  intros E base rom ss ms i ss' scs scr2 w Hf He Hd Hst Hle Hdis HX.
  destruct (disch_val segs E base rom ss ms ss' scs Hle Hdis HX) as (E1 & Ha1 & Hscs).
  destruct (sym_step_soundR segs E1 base rom ss ms i ss' scs scr_nil scr2 w Hf He Hd Hst
              (Hscs E1 (eagree_refl _ _)) (HX E1 Ha1)) as (ms' & Hstep & HR1).
  exists E1, ms'. split; [exact Ha1|]. split; [exact Hstep|]. split; [|exact Hscs].
  intros E'' Ha''.
  assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha'' | exact Hle]]).
  destruct (sym_step_soundR segs E'' base rom ss ms i ss' scs scr_nil scr2 w Hf He Hd Hst (Hscs E'' Ha'') (HX E'' HaE))
    as (ms'' & Hstep'' & HR''). rewrite Hstep in Hstep''. injection Hstep'' as <-. exact HR''.
Qed.

(* [comment removed for export] *)
Lemma branch_scs : forall c rs1 rs2 imm ss scr ss' scs scr',
  sym_step segs (Branch c rs1 rs2 imm) ss scr = SOk ss' scs scr' ->
  s_next ss' = s_next ss /\ s_know ss' = s_know ss /\
  (scs = [] \/ exists dirs', sc_dirs scr = (match scs with SCBr t _ _ _ :: _ => t | _ => true end) :: dirs' /\
                          scs = [SCBr (match scs with SCBr t _ _ _ :: _ => t | _ => true end) c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)]).
Proof.
  intros c rs1 rs2 imm ss scr ss' scs scr' H. cbn [sym_step] in H.
  repeat match type of H with
  | (match ?x with _ => _ end) = _ => let E := fresh "E" in destruct x eqn:E
  end; try discriminate;
  injection H as <- <- <-; cbn [sjump s_next s_know]; (split; [reflexivity|]); (split; [reflexivity|]);
  first [ left; reflexivity | right; eexists; split; [reflexivity | reflexivity] ].
Qed.

(* [comment removed for export] *)
Lemma branch_undecided : forall c rs1 rs2 imm ss t ss' scs scr',
  sym_step segs (Branch c rs1 rs2 imm) ss (SCR [t] [] []) = SOk ss' scs scr' -> scs <> [] ->
  scs = [SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)].
Proof.
  intros c rs1 rs2 imm ss t ss' scs scr' H Hne.
  destruct (branch_scs c rs1 rs2 imm ss _ ss' scs scr' H) as (_ & _ & [Hn | (dirs' & Hd & Hs)]); [contradiction|].
  cbn [sc_dirs] in Hd. injection Hd as Ht _. rewrite Hs. rewrite <- Ht. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_repeat0 : forall n, bytes_le_to_Z (repeat (Z_to_bv 8 0) n) = 0%Z.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat bytes_le_to_Z]. rewrite IH. cbn. reflexivity.
Qed.

Lemma extz0 : forall sx n, extz sx n 0 = 0%Z.
Proof.
  intros [|] n; cbn [extz]; [|reflexivity]. unfold bv_swrap, bv_wrap, bv_half_modulus.
  set (m := bv_modulus (8 * N.of_nat n)).
  assert (Hm : (0 < m)%Z) by (unfold m, bv_modulus; apply Z.pow_pos_nonneg; lia).
  assert (H2 : (0 <= m / 2 < m)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt; lia]).
  rewrite Z.add_0_l, Z.mod_small by lia. lia.
Qed.

Lemma srange_in_sound : forall E M fk rb rk n kb kk len, know_ok segs E M fk -> srange_in fk rb rk n kb kk len = true ->
  (estart E (SA kb kk) <= estart E (SA rb rk))%Z /\ (estart E (SA rb rk) + elenZ E (elen n) <= estart E (SA kb kk) + elenZ E len)%Z.
Proof.
  intros E M fk rb rk n kb kk len HK H. unfold srange_in in H.
  destruct kb as [z0| | | | | | |]; try discriminate. destruct len as [l0| | | | | | |]; try discriminate.
  destruct (SSR.srange fk rb) as [[lo hi]|] eqn:Hs; [|discriminate].
  destruct (Z.leb 0 lo) eqn:H0; [|discriminate]. apply Z.leb_le in H0.
  destruct (Z.leb (z0 mod 2 ^ 64 + kk) (lo + rk)) eqn:H1; [|discriminate]. apply Z.leb_le in H1. apply Z.leb_le in H.
  pose proof (SSR.srange_sound_u segs E M fk rb lo hi HK Hs H0) as R.
  unfold estart, elenZ, elen. cbn [a_base a_off]. rewrite !edenot_lit, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  pose proof (Z.mod_le (Z.of_nat n) (2 ^ 64) ltac:(lia) ltac:(lia)) as Hn. lia.
Qed.

Lemma zf_in_sound : forall E M fk srl rb rk n kb kk len, know_ok segs E M fk -> zf_in fk srl rb rk n kb kk len = true ->
  (estart E (SA kb kk) <= estart E (SA rb rk))%Z /\ (estart E (SA rb rk) + elenZ E (elen n) <= estart E (SA kb kk) + elenZ E len)%Z.
Proof.
  intros E M fk srl rb rk n kb kk len HK H. unfold zf_in in H.
  destruct (xinside fk rb rk (elen n) kb kk len) eqn:X; [exact (xinside_sound segs E M fk _ _ _ _ _ _ HK X)|].
  destruct srl.
  { destruct (SLin.xinside2 fk rb rk (elen n) kb kk len) eqn:X2; [exact (SLin.xinside2_sound segs E M fk _ _ _ _ _ _ HK X2)|].
    exact (srange_in_sound E M fk rb rk n kb kk len HK H). }
  destruct (cancels rb kb); [exact (SLin.xinside2_sound segs E M fk _ _ _ _ _ _ HK H) |].
  exact (srange_in_sound E M fk rb rk n kb kk len HK H).
Qed.

(* [comment removed for export] *)
Lemma rdn_const_in : forall E base n rb rk kb kk len c bs,
  (1 <= n <= 8)%nat ->
  flat E (SA kb kk) (elenZ E len) ->
  (forall i, (0 <= i < elenZ E len)%Z -> base (Z_to_bv 64 (estart E (SA kb kk) + i)) = Some (Z_to_bv 8 c)) ->
  (estart E (SA kb kk) <= estart E (SA rb rk))%Z -> (estart E (SA rb rk) + Z.of_nat n <= estart E (SA kb kk) + elenZ E len)%Z ->
  rdn segs base (adenot E (SA rb rk)) n = Some bs -> bs = repeat (Z_to_bv 8 c) n.
Proof.
  intros E base n rb rk kb kk len c bs Hn Hfl Hz H1 H2 Hbs.
  destruct Hfl as (Hf1 & Hf2 & Hf3 & Hf4). unfold estart in *. cbn [a_base a_off] in *.
  assert (Ha : bv_unsigned (adenot E (SA rb rk)) = (bv_unsigned (edenot E rb) + rk)%Z).
  { unfold adenot. cbn [a_base a_off]. unfold v_addi. rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia. }
  assert (R : rdn segs base (adenot E (SA rb rk)) n = Some (repeat (Z_to_bv 8 c) n)).
  { apply rdn_pointwise; [apply repeat_length | rewrite Ha; lia |].
    intros j Hj. rewrite (nth_indep _ _ (Z_to_bv 8 c)) by (rewrite repeat_length; lia). rewrite nth_repeat. rewrite Ha.
    replace (bv_unsigned (edenot E rb) + rk + Z.of_nat j)%Z
      with (bv_unsigned (edenot E kb) + kk + (bv_unsigned (edenot E rb) + rk - (bv_unsigned (edenot E kb) + kk) + Z.of_nat j))%Z by lia.
    apply Hz. lia. }
  rewrite R in Hbs. injection Hbs as <-. reflexivity.
Qed.

Lemma zf_read0_sound : forall E base fk srl kn rb rk n sx v bs, know_ok segs E base fk -> know_ok segs E base kn ->
  (1 <= n <= 8)%nat -> zf_read0 fk srl kn rb rk n sx = Some v ->
  rdn segs base (adenot E (SA rb rk)) n = Some bs -> Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = Z_to_bv 64 v.
Proof.
  intros E base fk srl kn rb rk n sx v bs HF HK Hn. induction HK as [|K r HK1 _ IH]; intros H Hbs; [discriminate|].
  cbn [zf_read0] in H.
  destruct K as [ |[kb kk] len| | | | | | |[kb kk] len c| ]; try exact (IH H Hbs).
  - destruct (zf_in fk srl rb rk n kb kk len) eqn:Hin; [|exact (IH H Hbs)]. injection H as <-.
    destruct (zf_in_sound E base fk srl rb rk n kb kk len HF Hin) as [C1 C2]. rewrite elenZ_elen in C2 by lia.
    cbn [kentry_ok] in HK1. destruct HK1 as [Hfl Hz].
    rewrite (rdn_const_in E base n rb rk kb kk len 0 bs Hn Hfl Hz C1 C2 Hbs).
    rewrite bytes_le_repeat0, extz0. reflexivity.
  - destruct (Nat.eqb n 1) eqn:Hn1; [|exact (IH H Hbs)]. apply Nat.eqb_eq in Hn1. subst n.
    destruct (zf_in fk srl rb rk 1 kb kk len) eqn:Hin; [|exact (IH H Hbs)]. injection H as <-.
    destruct (zf_in_sound E base fk srl rb rk 1 kb kk len HF Hin) as [C1 C2]. rewrite elenZ_elen in C2 by lia.
    cbn [kentry_ok] in HK1. destruct HK1 as [Hfl Hz].
    rewrite (rdn_const_in E base 1 rb rk kb kk len c bs Hn Hfl Hz C1 C2 Hbs).
    cbn [repeat bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity.
Qed.

Lemma zf_read_sound : forall E base kn a n sx v bs, know_ok segs E base kn -> zf_read kn a n sx = Some v ->
  rdn segs base (adenot E a) n = Some bs -> Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)) = Z_to_bv 64 v.
Proof.
  intros E base kn [rb rk] n sx v bs HK H Hbs. unfold zf_read in H. cbn [a_base a_off] in H.
  destruct (Nat.leb 1 n) eqn:H1; [|discriminate]. destruct (Nat.leb n 8) eqn:H2; [|discriminate].
  apply Nat.leb_le in H1, H2.
  exact (zf_read0_sound E base _ _ kn rb rk n sx v bs (facts_of_ok segs E base kn HK) HK ltac:(lia) H Hbs).
Qed.

Lemma respell_ok : forall E1 base rom ss' ms' i0 scs i,
  (forall E'', eagree (s_next ss') E1 E'' -> scs_denot segs base E'' scs) ->
  st_okX segs E1 base rom ss' ms' -> st_okX segs E1 base rom (respell ss' i0 scs i) ms'.
Proof.
  intros E1 base rom ss' ms' i0 scs i Hscs HX. unfold respell. destruct i; try exact HX.
  2, 4: (* [comment removed for export] *)
    destruct op; try exact HX; unfold ar_state; destruct (bv_eqb rd 0); try exact HX;
    destruct (add_respell (facts_of (s_know ss')) (sr_get (s_regs ss') rd)) as [e'|] eqn:Har; try exact HX;
    intros E'' Ha; destruct (HX E'' Ha) as (regs & Hms & HR & Hlf & HK);
    exists regs; cbn [s_pc s_regs s_log s_know s_resv]; split; [exact Hms|]; split; [|split; [exact Hlf | exact HK]];
    apply regs_ok_pin; [exact HR|]; rewrite (HR rd); symmetry; exact (add_respell_sound _ _ _ Har E'').
  2: { (* [comment removed for export] *)
    destruct op; try exact HX. destruct (bv_eqb rd 0) eqn:Hrd; [exact HX|].
    destruct (sr_get (s_regs ss') rd) as [| |op' a b| | | | |] eqn:Hg; try exact HX.
    destruct op'; try exact HX. destruct b as [sh| | | | | | |]; try exact HX.
    destruct (SSRL.srl_split (facts_of (s_know ss')) a sh) as [e'|] eqn:Hsp; [|exact HX].
    intros E'' Ha. destruct (HX E'' Ha) as (regs & Hms & HR & Hlf & HK).
    exists regs. cbn [s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [|split; [exact Hlf | exact HK]].
    apply regs_ok_pin; [exact HR|]. rewrite (HR rd), Hg.
    rewrite (SSRL.srl_split_sound segs E'' base (facts_of (s_know ss')) a sh e' (facts_of_ok segs E'' base _ HK) Hsp).
    reflexivity. }
  destruct (find_readbase i0 scs) as [[[a n] sx]|] eqn:Hrb; try exact HX.
  destruct (bv_eqb rd 0 || negb (expr_eqb (sr_get (s_regs ss') rd) (EVar i0)))%bool eqn:Hc; [exact HX|].
  apply orb_false_iff in Hc as [Hrd Hev]. apply negb_false_iff in Hev. apply expr_eqb_eq in Hev.
  destruct (zf_read (s_know ss') a n sx) as [v|] eqn:Hzf.
  { (* [comment removed for export] *)
    intros E'' Ha. destruct (HX E'' Ha) as (regs & Hms & HR & Hlf & HK).
    exists regs. cbn [s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [|split; [exact Hlf | exact HK]].
    apply regs_ok_pin; [exact HR|]. rewrite (HR rd), Hev.
    pose proof (proj1 (Forall_forall _ _) (Hscs E'' Ha) _ (find_readbase_In _ _ _ _ _ Hrb)) as RB.
    cbn [sc_denot] in RB. destruct RB as (bs & Hbs & Hv).
    rewrite <- Hv. cbn [edenot]. exact (zf_read_sound E'' base _ a n sx v bs HK Hzf Hbs). }
  destruct (sx || negb (Nat.ltb n 8))%bool eqn:Hc2; [exact HX|].
  apply orb_false_iff in Hc2 as [Hsx Hn8]. subst sx. apply negb_false_iff in Hn8. apply Nat.ltb_lt in Hn8.
  intros E'' Ha. destruct (HX E'' Ha) as (regs & Hms & HR & Hlf & HK).
  exists regs. cbn [s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [|split; [exact Hlf | exact HK]].
  apply regs_ok_pin; [exact HR|]. rewrite (HR rd), Hev.
  pose proof (proj1 (Forall_forall _ _) (Hscs E'' Ha) _ (find_readbase_In _ _ _ _ _ Hrb)) as RB.
  cbn [sc_denot] in RB. destruct RB as (bs & Hbs & Hv).
  pose proof (rdn_length segs _ _ _ _ Hbs) as Hlen.
  cbn [edenot]. symmetry. apply AxSymRun3.ext_val_zx_id.
  cbn [edenot] in Hv. rewrite <- Hv. cbn [extz]. pose proof (bytes_le_to_Z_bound bs) as Bd. rewrite Hlen in Bd.
  rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. cbn.
  assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma Forall1 : forall (P : sidecond -> Prop) x, P x -> Forall P [x].
Proof. intros P x H. constructor; [exact H | constructor]. Qed.
Lemma Forall0 : forall (P : sidecond -> Prop), Forall P [].
Proof. intros P. constructor. Qed.

Lemma regs_val : forall E sr R (r : reg), regs_ok E sr R -> edenot E (sr_get sr r) = getr R r.
Proof. intros E sr R r H. symmetry. apply H. Qed.

Lemma know_ok_app : forall E base l1 l2, know_ok segs E base l1 -> know_ok segs E base l2 -> know_ok segs E base (l1 ++ l2).
Proof. intros E base l1 l2 H1 H2. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
Lemma fork_child : forall E base rom ss ms c rs1 rs2 imm t ss1 scr1 w l,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  sym_step segs (Branch c rs1 rs2 imm) ss (SCR [t] [] []) = SOk ss1 [SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)] scr1 ->
  branch_taken c (getr (ms_regs ms) rs1) (getr (ms_regs ms) rs2) = t ->
  SL.learn (facts_of (s_know ss)) c t (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) = Some l ->
  st_okX segs E base rom ss ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms'
    /\ st_okX segs E base rom (set_know ss1 (l ++ s_know ss)) ms'
    /\ s_next (set_know ss1 (l ++ s_know ss)) = s_next ss
    /\ (forall E', eagree (s_next ss) E E' -> sc_denot segs base E' (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2))).
Proof.
  intros E base rom ss ms c rs1 rs2 imm t ss1 scr1 w l Hf He Hd Hst Hbr Hl HX.
  destruct (branch_scs c rs1 rs2 imm ss _ ss1 _ scr1 Hst) as (Hn & Hk & _).
  assert (SC : forall E', eagree (s_next ss) E E' -> sc_denot segs base E' (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2))).
  { intros E' Ha. destruct (st_okR_parts segs E' base rom ss ms (HX E' Ha)) as (Hregs & _).
    cbn [sc_denot]. rewrite !(regs_val E' (s_regs ss) (ms_regs ms)) by exact Hregs. exact Hbr. }
  destruct (sym_step_soundR segs E base rom ss ms _ ss1 _ _ scr1 w Hf He Hd Hst
              (Forall1 _ _ (SC E (eagree_refl _ _))) (HX E (eagree_refl _ _))) as (ms' & Hstep & _).
  exists ms'. split; [exact Hstep|]. split; [| split; [cbn [set_know s_next]; exact Hn | exact SC]].
  intros E' Ha. cbn [set_know s_next] in Ha. rewrite Hn in Ha.
  destruct (sym_step_soundR segs E' base rom ss ms _ ss1 _ _ scr1 w Hf He Hd Hst
              (Forall1 _ _ (SC E' Ha)) (HX E' Ha)) as (ms'' & Hstep'' & HR'').
  rewrite Hstep in Hstep''. injection Hstep'' as <-.
  destruct HR'' as (regs & Hms & Hregs & Hlf & Hkn). exists regs. cbn [set_know s_pc s_regs s_log s_know s_resv].
  split; [exact Hms|]. split; [exact Hregs|]. split; [exact Hlf|].
  apply know_ok_app; [|rewrite <- Hk; exact Hkn].
  destruct (st_okR_parts segs E' base rom ss ms (HX E' Ha)) as (Hregs0 & _ & _ & Hkn0 & _).
  eapply (SL.learn_sound segs E' base (facts_of (s_know ss)) c t); [exact (facts_of_ok segs E' base _ Hkn0) | | exact Hl].
  rewrite !(regs_val E' (s_regs ss) (ms_regs ms)) by exact Hregs0. exact Hbr.
Qed.

(* [comment removed for export] *)
Lemma fork_none : forall E base rom ss ms c rs1 rs2 t,
  SL.learn (facts_of (s_know ss)) c t (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) = None ->
  st_okX segs E base rom ss ms ->
  branch_taken c (getr (ms_regs ms) rs1) (getr (ms_regs ms) rs2) <> t.
Proof.
  intros E base rom ss ms c rs1 rs2 t Hl HX.
  destruct (st_okR_parts segs E base rom ss ms (HX E (eagree_refl _ _))) as (Hregs & _ & _ & Hkn & _).
  pose proof (SL.learn_none segs E base _ c t _ _ (facts_of_ok segs E base _ Hkn) Hl) as H.
  rewrite !(regs_val E (s_regs ss) (ms_regs ms)) in H by exact Hregs. exact H.
Qed.

Lemma sym_stepBI_ok : forall bc kx i ss scr, bc = mkbc (facts_of (s_know ss)) -> kx = mk_kix (s_know ss) ->
  sym_stepBI bc kx segs i ss scr = sym_step segs i ss scr.
Proof. intros bc kx i ss scr -> ->. rewrite sym_stepBI_eq. apply sym_stepB_eq. Qed.

Lemma x_filterB_ok : forall bc ss ss' scs, bc = mkbc (facts_of (s_know ss)) ->
  x_filterB segs bc ss ss' scs = x_filter segs ss ss' scs.
Proof. intros bc ss ss' scs ->. apply x_filterB_eq. Qed.

Lemma is_nilb_nil : forall {A} (l : list A), is_nilb l = true -> l = [].
Proof. intros A [|x l] H; [reflexivity | discriminate]. Qed.

(* [comment removed for export] *)
Lemma split_cmp_child : forall E base rom ss ms c t a b l,
  AxSymRun3.expr_vars_lt (s_next ss) a = true -> AxSymRun3.expr_vars_lt (s_next ss) b = true ->
  branch_taken c (edenot E a) (edenot E b) = t ->
  SL.learn (facts_of (s_know ss)) c t a b = Some l ->
  st_okX segs E base rom ss ms ->
  st_okX segs E base rom (set_know ss (l ++ s_know ss)) ms
  /\ (forall E', eagree (s_next ss) E E' -> sc_denot segs base E' (SCBr t c a b)).
Proof.
  intros E base rom ss ms c t a b l Hca Hcb Hbr Hl HX.
  assert (SAME : forall E', eagree (s_next ss) E E' -> branch_taken c (edenot E' a) (edenot E' b) = t).
  { intros E' Ha. apply eagree_env_agree in Ha.
    rewrite <- (AxSymRun3.edenot_agree _ E E' a Ha Hca), <- (AxSymRun3.edenot_agree _ E E' b Ha Hcb). exact Hbr. }
  split; [|intros E' Ha; exact (SAME E' Ha)].
  intros E' Ha. cbn [set_know s_next] in Ha. destruct (HX E' Ha) as (regs & Hms & HR & Hlf & HK).
  exists regs. cbn [set_know s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [exact HR|]. split; [exact Hlf|].
  apply know_ok_app; [|exact HK].
  exact (SL.learn_sound segs E' base _ c t a b l (facts_of_ok segs E' base _ HK) (SAME E' Ha) Hl).
Qed.

Lemma split_al_child : forall E base rom ss ms l,
  SL.al_tight (facts_of (s_know ss)) (facts_of (s_know ss)) = Some l ->
  st_okX segs E base rom ss ms ->
  st_okX segs E base rom (set_know ss (l ++ s_know ss)) ms.
Proof.
  intros E base rom ss ms l Hl HX E' Ha. cbn [set_know s_next] in Ha. destruct (HX E' Ha) as (regs & Hms & HR & Hlf & HK).
  exists regs. cbn [set_know s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [exact HR|]. split; [exact Hlf|].
  apply know_ok_app; [|exact HK].
  pose proof (facts_of_ok segs E' base _ HK) as HF.
  exact (proj1 (SL.al_tight_ok segs E' base _ _ HF HF) l Hl).
Qed.

Lemma split_enum_child : forall E base rom ss ms a u,
  AxSymRun3.expr_vars_lt (s_next ss) a = true -> (0 <= u < 2^64)%Z -> bv_unsigned (edenot E a) = u -> u = u ->
  st_okX segs E base rom ss ms ->
  st_okX segs E base rom (set_know ss (KRange a u u :: s_know ss)) ms
  /\ (forall E', eagree (s_next ss) E E' -> sc_denot segs base E' (SCBr true BC_EQ a (ELit u))).
Proof.
  intros E base rom ss ms a u Hca Hu Hv _ HX.
  assert (SAME : forall E', eagree (s_next ss) E E' -> bv_unsigned (edenot E' a) = u).
  { intros E' Ha. apply eagree_env_agree in Ha. rewrite <- (AxSymRun3.edenot_agree _ E E' a Ha Hca). exact Hv. }
  split.
  - intros E' Ha. cbn [set_know s_next] in Ha. destruct (HX E' Ha) as (regs & Hms & HR & Hlf & HK).
    exists regs. cbn [set_know s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [exact HR|]. split; [exact Hlf|].
    constructor; [|exact HK]. cbn [kentry_ok]. rewrite (SAME E' Ha). lia.
  - intros E' Ha. cbn [sc_denot branch_taken]. unfold bv_eqb. rewrite (SAME E' Ha), edenot_lit, Z_to_bv_unsigned, bv_wrap_small.
    + apply Z.eqb_refl.
    + unfold bv_modulus. cbn. lia.
Qed.

Lemma split_sub_child : forall E base rom ss ms n u D,
  SL.sub_facts (facts_of (s_know ss)) n u = Some D ->
  st_okX segs E base rom (set_know ss (KRange (EVar n) u u :: s_know ss)) ms ->
  st_okX segs E base rom (set_know ss (D ++ KRange (EVar n) u u :: s_know ss)) ms.
Proof.
  intros E base rom ss ms n u D HD HX E' Ha. cbn [set_know s_next] in Ha. destruct (HX E' Ha) as (regs & Hms & HR & Hlf & HK).
  exists regs. cbn [set_know s_pc s_regs s_log s_know s_resv] in *. split; [exact Hms|]. split; [exact HR|]. split; [exact Hlf|].
  apply know_ok_app; [|exact HK].
  inversion HK as [|? ? HK0 HKr]. cbn [kentry_ok] in HK0.
  pose proof (facts_of_ok segs E' base _ HKr) as HF.
  pose proof (SL.sub_facts_ok segs E' base (facts_of (s_know ss)) n u HF ltac:(lia)) as Hs. rewrite HD in Hs. exact Hs.
Qed.

Lemma rdk_land_shl : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z -> Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.
Lemma rdk_lor_shl : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z -> Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb. rewrite <- Z.lxor_lor by (apply rdk_land_shl; lia).
  symmetry. apply Z.add_nocarry_lxor. apply rdk_land_shl; lia.
Qed.
Lemma rdk_le_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = (bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest)%Z).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite rdk_lor_shl by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8)%Z.
    change (2 ^ 8)%Z with 256%Z in *.
    rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8)%Z with 256%Z in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256)%Z with (bytes_le_to_Z rest).
    + exact IH.
    + symmetry. rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma rdk_word_bytes : forall n bs, length bs = n -> (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros n bs <- Hlen. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : (bytes_le_to_Z bs < 2 ^ 64)%Z).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). apply rdk_le_bytes.
Qed.

Lemma rd_know_ok : forall E base kn path, know_ok segs E base kn -> scs_denot segs base E path -> know_ok segs E base (rd_know kn path).
Proof.
  intros E base kn path HK HP. unfold rd_know.
  destruct path as [|sc rest]; [constructor|].
  destruct sc as [| | | | |[b k] n sx e|]; try constructor.
  destruct sx; [constructor|]. destruct e as [|v| | | | | |]; try constructor.
  destruct (Nat.leb 1 n && Nat.leb n 8 && SDI.flat_ok kn b k (elen n))%bool eqn:C; [|constructor].
  apply andb_prop in C as [C Hf]. apply andb_prop in C as [C1 C2]. apply Nat.leb_le in C1, C2.
  inversion HP as [|? ? Hsc _]. cbn [sc_denot] in Hsc. destruct Hsc as (bs & Hrd & Hv).
  constructor; [|constructor]. cbn [kentry_ok]. split; [exact C2|]. split.
  - pose proof (SDI.flat_ok_sound segs E base kn b k (elen n) HK Hf) as F. rewrite elenZ_elen in F by lia. exact F.
  - assert (EV : edenot E (if Nat.ltb n 8 then EExt false 0 n (EVar v) else EVar v) = edenot E (EVar v)).
    { destruct (Nat.ltb n 8) eqn:N8; [|reflexivity]. apply Nat.ltb_lt in N8. cbn [edenot]. apply AxSymRun3.ext_val_zx_id.
      cbn [edenot] in Hv. rewrite <- Hv. cbn [extz]. pose proof (rdn_length segs _ _ _ _ Hrd) as Hlen.
      pose proof (bytes_le_to_Z_bound bs) as Bd. rewrite Hlen in Bd.
      rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. cbn.
      assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z by (apply Z.pow_le_mono_r; lia). lia. }
    rewrite EV. rewrite Hrd. f_equal. rewrite <- Hv. cbn [extz]. symmetry. apply rdk_word_bytes; [exact (rdn_length _ _ _ _ _ Hrd) | exact C2].
Qed.

Lemma split_rdk_child : forall E base rom ss ms path,
  st_okX segs E base rom ss ms -> path_okX base E (s_next ss) path ->
  st_okX segs E base rom (set_know ss (rd_know (facts_of (s_know ss)) path ++ s_know ss)) ms.
Proof.
  intros E base rom ss ms path HX HP E' Ha. cbn [set_know s_next] in Ha. destruct (HX E' Ha) as (regs & Hms & HR & Hlf & HK).
  exists regs. cbn [set_know s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [exact HR|]. split; [exact Hlf|].
  apply know_ok_app; [|exact HK].
  exact (rd_know_ok E' base _ path (facts_of_ok segs E' base _ HK) (HP E' Ha)).
Qed.

Lemma split_hav_child : forall E base rom ss ms r,
  st_okX segs E base rom ss ms ->
  st_okX segs (eupd E (s_next ss) (getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)))) base rom (shav ss r) ms.
Proof.
  intros E base rom ss ms r HX E'' Ha. cbn [shav s_next] in Ha.
  assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [apply eagree_upd | eapply eagree_le; [exact Ha | lia]]).
  destruct (HX E'' HaE) as (regs & Hms & HR & Hlf & HK).
  exists regs. cbn [shav s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [|split; [exact Hlf | exact HK]].
  apply regs_ok_pin; [exact HR|]. cbn [edenot].
  destruct Ha as [Hv _]. rewrite <- (Hv (s_next ss)) by lia. rewrite eupd_at. rewrite Hms. reflexivity.
Qed.

Lemma slt_lit_den : forall E base kn e, know_ok segs E base kn -> edenot E (slt_lit kn e) = edenot E e.
Proof.
  intros E base kn e HK. unfold slt_lit.
  destruct e as [| |op a b| | | | |]; try reflexivity. destruct op; try reflexivity.
  destruct (SSLT.slt_dec kn a b) as [t|] eqn:H; [|reflexivity].
  symmetry. exact (SSLT.slt_value segs E base kn a b t HK H).
Qed.

Lemma regs_ok_map : forall E sr regs (f : expr -> expr), (forall e, edenot E (f e) = edenot E e) -> f (ELit 0) = ELit 0 ->
  regs_ok E sr regs -> regs_ok E (map f sr) regs.
Proof.
  intros E sr regs f Hf H0 HR r. rewrite (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  replace (nth (ridx r) (map f sr) (ELit 0)) with (f (nth (ridx r) sr (ELit 0))); [symmetry; apply Hf|].
  rewrite <- (map_nth f sr (ELit 0) (ridx r)). rewrite H0. reflexivity.
Qed.

Lemma split_slt_child : forall E base rom ss ms, st_okX segs E base rom ss ms -> st_okX segs E base rom (sslt ss) ms.
Proof.
  intros E base rom ss ms HX E'' Ha. cbn [sslt s_next] in Ha.
  destruct (HX E'' Ha) as (regs & Hms & HR & Hlf & HK).
  exists regs. cbn [sslt s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [|split; [exact Hlf | exact HK]].
  apply regs_ok_map; [| reflexivity | exact HR].
  intros e. exact (slt_lit_den E'' base _ e (facts_of_ok segs E'' base _ HK)).
Qed.

(* [comment removed for export] *)
Lemma w32_exact : forall (W : word) t, eqm t (bv_unsigned W) -> - 2 ^ 31 <= bv_signed W < 2 ^ 31 -> Z_to_bv 64 (bv_swrap 32 t) = W.
Proof.
  intros W t Ht Hs. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite (SSR.swrap32_eqm t (bv_signed W)).
  - rewrite SSR.swrap32_id by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    destruct (SSR.s_eqm W) as [q Hq]. pose proof (bv_unsigned_in_range _ W) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
    rewrite (Z.mod_unique (bv_signed W) (2 ^ 64) q (bv_unsigned W)); [reflexivity | left; lia | lia].
  - apply SSR.eqm_to32. eapply eqm_trans; [exact Ht|]. apply eqm_sym. apply SSR.s_eqm.
Qed.

Lemma in32o_ok : forall segs' E M kn f, know_ok segs' E M kn -> in32o (SSR.srange kn f) = true ->
  - 2 ^ 31 <= bv_signed (edenot E f) < 2 ^ 31.
Proof.
  intros segs' E M kn f HK H. unfold in32o in H. destruct (SSR.srange kn f) as [[l h]|] eqn:Hs; [|discriminate].
  destruct (Z.leb (- 2 ^ 31) l) eqn:C; [|discriminate]. apply Z.leb_le in C. apply Z.ltb_lt in H.
  pose proof (SSR.srange_sound segs' E M kn f l h HK Hs). lia.
Qed.

Lemma lor_aligned : forall a c j : Z, (0 <= j)%Z -> Z.divide (2 ^ j)%Z a -> (0 <= c < 2 ^ j)%Z -> Z.lor a c = (a + c)%Z.
Proof.
  intros a c j Hj [k Hk] Hc. subst a.
  assert (L : Z.land (k * 2 ^ j)%Z c = 0%Z).
  { apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
    destruct (Z.lt_ge_cases n 0) as [Hn0|Hn0]; [rewrite Z.testbit_neg_r by lia; reflexivity|].
    destruct (Z.lt_ge_cases n j) as [Hn|Hn].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec c 0) as [->|Hc0]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 c n); [apply andb_false_r | lia |].
      apply Z.log2_lt_pow2; [lia|]. assert (2 ^ j <= 2 ^ n)%Z by (apply Z.pow_le_mono_r; lia). lia. }
  rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma land_aligned_id : forall x m j : Z, (0 <= x < 2 ^ 64)%Z -> (0 <= j)%Z -> Z.divide (2 ^ j)%Z x -> (0 <= m < 2 ^ 64)%Z ->
  (2 ^ 64 - 1 - m < 2 ^ j)%Z -> Z.land x m = x.
Proof.
  intros x m j Hx Hj [k Hk] Hm Hc. apply Z.bits_inj. intros n. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n 0) as [Hn0|Hn0]; [rewrite !Z.testbit_neg_r by lia; reflexivity|].
  destruct (Z.lt_ge_cases n j) as [Lj|Gj].
  - subst x. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.lt_ge_cases n 64) as [L64|G64].
    + assert (Tm : Z.testbit m n = true).
      { assert (B : Z.b2z (Z.testbit m n) = 1%Z).
        { rewrite Z.testbit_spec' by lia.
          assert (P1 : (2 ^ j <= 2 ^ n)%Z) by (apply Z.pow_le_mono_r; lia).
          assert (Q : (m / 2 ^ n = 2 ^ (64 - n) - 1)%Z).
          { symmetry. apply Z.div_unique with ((2 ^ n - 1 - (2 ^ 64 - 1 - m))%Z); [left; lia|].
            replace (2 ^ 64)%Z with (2 ^ n * 2 ^ (64 - n))%Z at 1 by (rewrite <- Z.pow_add_r by lia; f_equal; lia). ring. }
          rewrite Q. assert (E2 : (2 ^ (64 - n) = 2 * 2 ^ (64 - n - 1))%Z) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
          rewrite E2. replace (2 * 2 ^ (64 - n - 1) - 1)%Z with (1 + (2 ^ (64 - n - 1) - 1) * 2)%Z by ring.
          rewrite Z.mod_add by lia. reflexivity. }
        destruct (Z.testbit m n); [reflexivity | discriminate]. }
      rewrite Tm, andb_true_r. reflexivity.
    + assert (Tx : Z.testbit x n = false).
      { destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
        apply Z.log2_lt_pow2; [lia|]. assert (2 ^ 64 <= 2 ^ n)%Z by (apply Z.pow_le_mono_r; lia). lia. }
      rewrite Tx. reflexivity.
Qed.

Lemma land_aligned_zero : forall x m j : Z, (0 <= j)%Z -> Z.divide (2 ^ j)%Z x -> (0 <= m < 2 ^ j)%Z -> Z.land x m = 0%Z.
Proof.
  intros x m j Hj [k Hk] Hm. subst x. apply Z.bits_inj_0. intros n. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases n 0) as [Hn0|Hn0]; [rewrite Z.testbit_neg_r by lia; reflexivity|].
  destruct (Z.lt_ge_cases n j) as [Lj|Gj].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec m 0) as [->|Hm0]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 m n); [apply andb_false_r | lia |].
    apply Z.log2_lt_pow2; [lia|]. assert (2 ^ j <= 2 ^ n)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma ealignX_sound : forall E base kn e, know_ok segs E base kn ->
  (0 <= ealignX kn e <= 64)%Z /\ (2 ^ ealignX kn e | bv_unsigned (edenot E e))%Z.
Proof.
  intros E base kn e HK. induction e as [z|v|op a IHa b IHb| | | | | ]; cbn [ealignX]; try exact (ealign_sound segs E base kn _ HK).
  destruct op; try exact (ealign_sound segs E base kn _ HK).
  destruct (ealign_sound segs E base kn (EAlu ALU_XOR a b) HK) as [H1 H2].
  destruct IHa as [A1 A2]. destruct IHb as [B1 B2].
  set (k := Z.min (ealignX kn a) (ealignX kn b)).
  assert (Hk : (2 ^ k | bv_unsigned (edenot E (EAlu ALU_XOR a b)))%Z).
  { cbn [edenot]. rewrite u_xor64.
    assert (Da : (2 ^ k | bv_unsigned (edenot E a))%Z).
    { eapply Z.divide_trans; [|exact A2]. exists (2 ^ (ealignX kn a - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Db : (2 ^ k | bv_unsigned (edenot E b))%Z).
    { eapply Z.divide_trans; [|exact B2]. exists (2 ^ (ealignX kn b - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct Da as [p Hp]. destruct Db as [q Hq]. rewrite Hp, Hq.
    assert (Hk0 : (0 <= k)%Z) by lia.
    rewrite <- !Z.shiftl_mul_pow2 by exact Hk0. rewrite <- Z.shiftl_lxor. rewrite Z.shiftl_mul_pow2 by exact Hk0.
    exists (Z.lxor p q). reflexivity. }
  destruct (Z.max_spec (ealign kn (EAlu ALU_XOR a b)) k) as [[_ ->]|[_ ->]]; split; try lia; assumption.
Qed.

Lemma and_zero_den : forall E base kn a m, know_ok segs E base kn -> and_zero_ok kn a m = true ->
  edenot E (ELit 0) = alu64 ALU_AND (edenot E a) (edenot E (ELit m)).
Proof.
  intros E base kn a m HK H. unfold and_zero_ok in H. apply Z.ltb_lt in H.
  destruct (ealignX_sound E base kn a HK) as [Hj Hd].
  rewrite alu_and. unfold v_and. rewrite !edenot_lit, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64)%Z.
  rewrite (land_aligned_zero _ _ (ealignX kn a)); [reflexivity | lia | exact Hd |].
  split; [apply Z.mod_pos_bound; lia | exact H].
Qed.

Lemma and_id_den : forall E base kn a m, know_ok segs E base kn -> and_id_ok kn a m = true ->
  edenot E a = alu64 ALU_AND (edenot E a) (edenot E (ELit m)).
Proof.
  intros E base kn a m HK H. unfold and_id_ok in H. apply Z.ltb_lt in H.
  destruct (ealignX_sound E base kn a HK) as [Hj Hd].
  rewrite alu_and. unfold v_and. rewrite edenot_lit, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64)%Z.
  rewrite (land_aligned_id _ _ (ealignX kn a)).
  - symmetry. apply Z_to_bv_bv_unsigned.
  - pose proof (bv_unsigned_in_range _ (edenot E a)) as R. unfold bv_modulus in R. exact R.
  - lia.
  - exact Hd.
  - apply Z.mod_pos_bound. lia.
  - exact H.
Qed.

Lemma or_add_den : forall E base kn a c, know_ok segs E base kn -> or_add_ok kn a c = true ->
  edenot E (mkAlu ALU_ADD a (ELit c)) = alu64 ALU_OR (edenot E a) (edenot E (ELit c)).
Proof.
  intros E base kn a c HK H. unfold or_add_ok in H.
  destruct (Z.leb 1 (ealignX kn a)) eqn:C1; [|discriminate]. apply Z.leb_le in C1. apply Z.ltb_lt in H.
  destruct (ealignX_sound E base kn a HK) as [Hj Hd].
  rewrite mkAlu_denot, alu_add, alu_or. unfold v_add, v_or. f_equal. rewrite edenot_lit, Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  symmetry. apply (lor_aligned _ _ (ealignX kn a)); [lia | exact Hd |]. split; [apply Z.mod_pos_bound; lia | exact H].
Qed.

Lemma land_clear_low : forall v k : Z, (0 <= k <= 64)%Z -> (0 <= v < 2 ^ 64)%Z -> Z.land v (2 ^ 64 - 2 ^ k) = (v - v mod 2 ^ k)%Z.
Proof.
  intros v k Hk Hv.
  assert (E1 : (2 ^ 64 - 2 ^ k = Z.shiftl (Z.ones (64 - k)) k)%Z).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. unfold Z.pred.
    replace (2 ^ 64)%Z with (2 ^ (64 - k) * 2 ^ k)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia). ring. }
  assert (E2 : (v - v mod 2 ^ k = Z.ldiff v (Z.ones k))%Z).
  { rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    pose proof (Z.div_mod v (2 ^ k) ltac:(lia)). lia. }
  rewrite E1, E2. apply Z.bits_inj. intros n. rewrite Z.land_spec, Z.ldiff_spec.
  destruct (Z.lt_ge_cases n 0) as [Hn0|Hn0]; [rewrite !Z.testbit_neg_r by lia; reflexivity|].
  destruct (Z.lt_ge_cases n k) as [Lk|Gk].
  - rewrite Z.shiftl_spec_low by lia. rewrite Z.testbit_ones_nonneg by lia.
    replace (n <? k)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. rewrite !andb_false_r. reflexivity.
  - rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_ones_nonneg k n) by lia.
    replace (n <? k)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. rewrite andb_true_r.
    rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.lt_ge_cases n 64) as [L64|G64].
    + replace (n - k <? 64 - k)%Z with true by (symmetry; apply Z.ltb_lt; lia). apply andb_true_r.
    + replace (n - k <? 64 - k)%Z with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r.
      symmetry. destruct (Z.eq_dec v 0) as [->|Hv0]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.log2_lt_pow2; [lia|]. assert (2 ^ 64 <= 2 ^ n)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma mod_pow2_sub : forall a k : Z, (0 <= k <= 64)%Z -> ((a mod 2 ^ 64) mod 2 ^ k = a mod 2 ^ k)%Z.
Proof.
  intros a k Hk. symmetry. apply Znumtheory.Zmod_div_mod; try lia.
  exists (2 ^ (64 - k))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma and_addc_eq : forall x c k : Z, (0 <= k <= 64)%Z -> (0 <= x < 2 ^ 64)%Z -> Z.divide (2 ^ k)%Z x -> (0 <= c < 2 ^ 64)%Z ->
  Z.land ((x + c) mod 2 ^ 64) (2 ^ 64 - 2 ^ k) = ((x + Z.land c (2 ^ 64 - 2 ^ k)) mod 2 ^ 64)%Z.
Proof.
  intros x c k Hk Hx [q Hq] Hc.
  assert (P : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
  set (w := ((x + c) mod 2 ^ 64)%Z).
  assert (Hw : (0 <= w < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
  rewrite (land_clear_low w k Hk Hw), (land_clear_low c k Hk Hc).
  assert (Wk : (w mod 2 ^ k = c mod 2 ^ k)%Z).
  { unfold w. rewrite mod_pow2_sub by exact Hk. rewrite Hq. rewrite Z.add_comm. rewrite Z.mod_add by lia. reflexivity. }
  rewrite Wk.
  assert (L : (c mod 2 ^ k <= w)%Z) by (rewrite <- Wk; apply Z.mod_le; lia).
  apply Z.mod_unique with ((x + c) / 2 ^ 64)%Z; [left; lia|].
  pose proof (Z.div_mod (x + c) (2 ^ 64) ltac:(lia)) as DM. fold w in DM. lia.
Qed.

Lemma clrlow_k_ok : forall m k, clrlow_k m = Some k -> (0 <= k <= 64)%Z /\ (m mod 2 ^ 64 = 2 ^ 64 - 2 ^ k)%Z.
Proof.
  intros m k H. unfold clrlow_k in H.
  destruct (Z.ltb 0 (2 ^ 64 - m mod 2 ^ 64)) eqn:C1; [|discriminate]. apply Z.ltb_lt in C1.
  destruct (Z.eqb (2 ^ 64 - m mod 2 ^ 64) (2 ^ Z.log2 (2 ^ 64 - m mod 2 ^ 64))) eqn:C2; [|discriminate]. apply Z.eqb_eq in C2.
  injection H as <-. pose proof (Z.mod_pos_bound m (2 ^ 64) ltac:(lia)) as B.
  split; [split; [apply Z.log2_nonneg|] | lia].
  assert (Z.log2 (2 ^ 64 - m mod 2 ^ 64) <= Z.log2 (2 ^ 64))%Z by (apply Z.log2_le_mono; lia).
  rewrite Z.log2_pow2 in H by lia. exact H.
Qed.

Lemma and_addc_den : forall E base kn a m e', know_ok segs E base kn -> and_addc kn a m = Some e' ->
  edenot E e' = alu64 ALU_AND (edenot E a) (edenot E (ELit m)).
Proof.
  intros E base kn a m e' HK H. unfold and_addc in H.
  destruct (clrlow_k m) as [k|] eqn:Ck; [|discriminate]. destruct (clrlow_k_ok m k Ck) as [Hk Hm].
  destruct a as [| |op x c0| | | | |]; try discriminate. destruct op; try discriminate.
  destruct c0 as [c| | | | | | |]; try discriminate.
  destruct (Z.leb k (ealignX kn x)) eqn:Ca; [|discriminate]. apply Z.leb_le in Ca. injection H as <-.
  destruct (ealignX_sound E base kn x HK) as [Hj Hd].
  assert (Dk : Z.divide (2 ^ k)%Z (bv_unsigned (edenot E x))).
  { eapply Z.divide_trans; [|exact Hd]. exists (2 ^ (ealignX kn x - k))%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite mkAlu_denot. cbn [edenot]. rewrite !alu_add, alu_and. unfold v_add, v_and. rewrite ?edenot_lit.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64)%Z.
  pose proof (bv_unsigned_in_range _ (edenot E x)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64)%Z in R.
  rewrite Hm.
  assert (Cm : (0 <= c mod 2 ^ 64 < 2 ^ 64)%Z) by (apply Z.mod_pos_bound; lia).
  assert (Lr : (0 <= Z.land (c mod 2 ^ 64) (2 ^ 64 - 2 ^ k) < 2 ^ 64)%Z).
  { rewrite land_clear_low by lia. assert (Pk : (0 < 2 ^ k)%Z) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mod_pos_bound (c mod 2 ^ 64) (2 ^ k) Pk). pose proof (Z.mod_le (c mod 2 ^ 64) (2 ^ k) ltac:(lia) Pk). lia. }
  rewrite (Z.mod_small (Z.land (c mod 2 ^ 64) (2 ^ 64 - 2 ^ k))) by exact Lr.
  rewrite ?alu_add. unfold v_add. rewrite ?Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64)%Z.
  rewrite (and_addc_eq _ _ k Hk R Dk Cm).
  assert (Lw : (0 <= (bv_unsigned (edenot E x) + Z.land (c mod 2 ^ 64) (2 ^ 64 - 2 ^ k)) mod 2 ^ 64 < 2 ^ 64)%Z)
    by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small _ (2 ^ 64) Lw). reflexivity.
Qed.

Lemma low32_eq_mod : forall x y : word, (bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32)%Z -> low32 x = low32 y.
Proof.
  intros x y H. apply bv_eq. unfold low32. rewrite !bv_extract_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite !Z.shiftr_0_r. exact H.
Qed.

Lemma shl32_shr32 : forall v : Z, (0 <= v)%Z -> ((v * 2 ^ 32) mod 2 ^ 64 / 2 ^ 32 = v mod 2 ^ 32)%Z.
Proof.
  intros v Hv. change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z. rewrite Z.mul_mod_distr_r by lia.
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma lo32_strip_low : forall E e, low32 (edenot E (lo32_strip e)) = low32 (edenot E e).
Proof.
  intros E e. apply low32_eq_mod. unfold lo32_strip.
  destruct e as [| |op a b| | | | |]; try reflexivity. destruct op; try reflexivity.
  - (* [comment removed for export] *)
    destruct b as [s32| | | | | | |]; try reflexivity.
    destruct (Z.eqb s32 32) eqn:Hs; [|reflexivity]. apply Z.eqb_eq in Hs. subst s32.
    destruct a as [| |op' x c| |op' c x| | |]; try reflexivity.
    + destruct op'; try reflexivity. destruct c as [c| | | | | | |]; try reflexivity.
      destruct (Z.eqb c 32) eqn:Hc; [|reflexivity]. apply Z.eqb_eq in Hc. subst c.
      cbn [edenot]. rewrite alu_srl, alu_sll. unfold v_srl, v_sll. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64)%Z. change (32 mod 2 ^ 64 mod 64)%Z with 32%Z.
      rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia.
      pose proof (bv_unsigned_in_range _ (edenot E x)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
      rewrite shl32_shr32 by lia.
      rewrite (Z.mod_small (bv_unsigned (edenot E x) mod 2 ^ 32) (2 ^ 64)) by (pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x)) (2 ^ 32)); lia).
      symmetry. apply Z.mod_mod. lia.
    + destruct op'; try reflexivity. destruct c as [k| | | | | | |]; try reflexivity.
      destruct (Z.eqb k 4294967296) eqn:Hk; [|reflexivity]. apply Z.eqb_eq in Hk. subst k.
      cbn [edenot]. rewrite alu_srl, m_mul. unfold v_srl, v_mul. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with (2 ^ 64)%Z. change (32 mod 2 ^ 64 mod 64)%Z with 32%Z. change (4294967296 mod 2 ^ 64) with (2 ^ 32).
      rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.mul_comm.
      pose proof (bv_unsigned_in_range _ (edenot E x)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
      rewrite shl32_shr32 by lia.
      rewrite (Z.mod_small (bv_unsigned (edenot E x) mod 2 ^ 32) (2 ^ 64)) by (pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x)) (2 ^ 32)); lia).
      symmetry. apply Z.mod_mod. lia.
  - (* [comment removed for export] *) destruct b as [m| | | | | | |]; try reflexivity. destruct (Z.eqb m 4294967295) eqn:Hm; [|reflexivity].
    apply Z.eqb_eq in Hm. subst m. cbn [edenot]. rewrite alu_and. unfold v_and. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (4294967295 mod 2 ^ 64)%Z with (Z.ones 32).
    rewrite Z.land_ones by lia. pose proof (bv_unsigned_in_range _ (edenot E a)) as R. unfold bv_modulus in R.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
    rewrite (Z.mod_small (bv_unsigned (edenot E a) mod 2 ^ 32) (2 ^ 64)) by (pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a)) (2 ^ 32)); lia).
    symmetry. apply Z.mod_mod. lia.
Qed.

Lemma aluw_low32 : forall E op a b a2 b2, low32 (edenot E a) = low32 (edenot E a2) -> low32 (edenot E b) = low32 (edenot E b2) ->
  edenot E (EAluw op a b) = edenot E (EAluw op a2 b2).
Proof. intros E op a b a2 b2 Ha Hb. cbn [edenot]. rewrite Ha, Hb. reflexivity. Qed.
Lemma mdw_low32 : forall E op a b a2 b2, low32 (edenot E a) = low32 (edenot E a2) -> low32 (edenot E b) = low32 (edenot E b2) ->
  edenot E (EMdw op a b) = edenot E (EMdw op a2 b2).
Proof. intros E op a b a2 b2 Ha Hb. cbn [edenot]. rewrite Ha, Hb. reflexivity. Qed.

Lemma mulh0_den : forall E base kn op a b, know_ok segs E base kn -> is_mulh op = true -> mulh0 kn a b = true ->
  mul_div op (edenot E a) (edenot E b) = edenot E (ELit 0).
Proof.
  intros E base kn op a b HK Hop H. unfold mulh0 in H.
  destruct (SL.urange kn a) as [[la ha]|] eqn:Ra; [|discriminate]. destruct (SL.urange kn b) as [[lb hb]|] eqn:Rb; [|discriminate].
  destruct (Z.ltb ha (2 ^ 63)) eqn:C1; [|discriminate]. destruct (Z.ltb hb (2 ^ 63)) eqn:C2; [|discriminate].
  apply Z.ltb_lt in C1, C2, H.
  pose proof (SL.urange_sound segs E base kn a la ha HK Ra) as Sa. pose proof (SL.urange_sound segs E base kn b lb hb HK Rb) as Sb.
  pose proof (bv_unsigned_in_range _ (edenot E a)) as Ua. pose proof (bv_unsigned_in_range _ (edenot E b)) as Ub.
  unfold bv_modulus in Ua, Ub. change (2 ^ Z.of_N 64) with (2 ^ 64)%Z in Ua, Ub.
  assert (SA : bv_signed (edenot E a) = bv_unsigned (edenot E a)).
  { unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63)%Z. lia. }
  assert (SB : bv_signed (edenot E b) = bv_unsigned (edenot E b)).
  { unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63)%Z. lia. }
  assert (P : (0 <= bv_unsigned (edenot E a) * bv_unsigned (edenot E b) < 2 ^ 64)%Z) by nia.
  assert (Z0 : Z.shiftr (bv_unsigned (edenot E a) * bv_unsigned (edenot E b)) 64 = 0%Z).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. exact P. }
  destruct op; try discriminate; cbn [edenot].
  - rewrite m_mulh. unfold v_mulh. rewrite SA, SB, Z0. reflexivity.
  - rewrite m_mulhsu. unfold v_mulhsu. rewrite SA, Z0. reflexivity.
  - rewrite m_mulhu. unfold v_mulhu. rewrite Z0. reflexivity.
Qed.

Lemma wnorm_den : forall E base kn, know_ok segs E base kn -> forall e, edenot E (wnorm kn e) = edenot E e.
Proof.
  intros E base kn HK. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    cbn [wnorm]; try reflexivity.
  - assert (REB : edenot E (if expr_eqb a (wnorm kn a) then (if expr_eqb b (wnorm kn b) then EAlu op a b else mkAlu op (wnorm kn a) (wnorm kn b))
                            else mkAlu op (wnorm kn a) (wnorm kn b)) = edenot E (EAlu op a b)).
    { destruct (expr_eqb a (wnorm kn a)); [destruct (expr_eqb b (wnorm kn b)); [reflexivity|]|];
        rewrite mkAlu_denot; cbn [edenot]; rewrite IHa, IHb; reflexivity. }
    destruct op; try exact REB; destruct (wnorm kn b) as [c| | | | | | |] eqn:Hb; try exact REB.
    + destruct (or_add_ok kn (wnorm kn a) c) eqn:Ho; [|exact REB].
      rewrite (or_add_den E base kn _ c HK Ho). cbn [edenot]. rewrite IHa, <- IHb. reflexivity.
    + destruct (and_zero_ok kn (wnorm kn a) c) eqn:Hz.
      { rewrite (and_zero_den E base kn _ c HK Hz). cbn [edenot]. rewrite IHa, <- IHb. reflexivity. }
      destruct (and_id_ok kn (wnorm kn a) c) eqn:Ho.
      { rewrite (and_id_den E base kn _ c HK Ho). cbn [edenot]. rewrite IHa, <- IHb. reflexivity. }
      destruct (and_addc kn (wnorm kn a) c) as [e'|] eqn:Hac; [|exact REB].
      rewrite (and_addc_den E base kn _ c e' HK Hac). cbn [edenot]. rewrite IHa, <- IHb. reflexivity.
  - set (a2 := lo32_strip (wnorm kn a)). set (b2 := lo32_strip (wnorm kn b)).
    assert (LA : low32 (edenot E a) = low32 (edenot E a2)) by (unfold a2; rewrite lo32_strip_low, IHa; reflexivity).
    assert (LB : low32 (edenot E b) = low32 (edenot E b2)) by (unfold b2; rewrite lo32_strip_low, IHb; reflexivity).
    rewrite (aluw_low32 E op a b a2 b2 LA LB).
    destruct op; try reflexivity.
    + destruct (in32o (SSR.srange kn (mkAlu ALU_ADD a2 b2))) eqn:H; [|reflexivity].
      pose proof (in32o_ok segs E base kn _ HK H) as R. rewrite mkAlu_denot in R |- *.
      cbn [edenot]. rewrite w_addw. unfold v_addw. symmetry. apply w32_exact; [|exact R].
      rewrite alu_add. unfold v_add. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      pose proof (Z.div_mod (bv_unsigned (edenot E a2) + bv_unsigned (edenot E b2)) (2 ^ 64) ltac:(lia)) as DM.
      exists ((bv_unsigned (edenot E a2) + bv_unsigned (edenot E b2)) / 2 ^ 64). lia.
    + destruct (in32o (SSR.srange kn (mkAlu ALU_SUB a2 b2))) eqn:H; [|reflexivity].
      pose proof (in32o_ok segs E base kn _ HK H) as R. rewrite mkAlu_denot in R |- *.
      cbn [edenot]. rewrite w_subw. unfold v_subw. symmetry. apply w32_exact; [|exact R].
      rewrite alu_sub. unfold v_sub. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      pose proof (Z.div_mod (bv_unsigned (edenot E a2) - bv_unsigned (edenot E b2)) (2 ^ 64) ltac:(lia)) as DM.
      exists ((bv_unsigned (edenot E a2) - bv_unsigned (edenot E b2)) / 2 ^ 64). lia.
  - assert (REB : edenot E (if expr_eqb a (wnorm kn a) then (if expr_eqb b (wnorm kn b) then EMd op a b else mkMd op (wnorm kn a) (wnorm kn b))
                            else mkMd op (wnorm kn a) (wnorm kn b)) = edenot E (EMd op a b)).
    { destruct (expr_eqb a (wnorm kn a)); [destruct (expr_eqb b (wnorm kn b)); [reflexivity|]|];
        rewrite mkMd_denot; cbn [edenot]; rewrite IHa, IHb; reflexivity. }
    destruct (is_mulh op) eqn:Hop; [|exact REB].
    destruct (mulh0 kn (wnorm kn a) (wnorm kn b)) eqn:Hm; [|exact REB].
    change (edenot E (EMd op a b)) with (mul_div op (edenot E a) (edenot E b)). rewrite <- IHa, <- IHb.
    symmetry. exact (mulh0_den E base kn op _ _ HK Hop Hm).
  - set (a2 := lo32_strip (wnorm kn a)). set (b2 := lo32_strip (wnorm kn b)).
    assert (LA : low32 (edenot E a) = low32 (edenot E a2)) by (unfold a2; rewrite lo32_strip_low, IHa; reflexivity).
    assert (LB : low32 (edenot E b) = low32 (edenot E b2)) by (unfold b2; rewrite lo32_strip_low, IHb; reflexivity).
    rewrite (mdw_low32 E op a b a2 b2 LA LB).
    destruct op; try reflexivity.
    destruct (in32o (SSR.srange kn (mkMd M_MUL a2 b2))) eqn:H; [|reflexivity].
    pose proof (in32o_ok segs E base kn _ HK H) as R. rewrite mkMd_denot in R |- *.
    cbn [edenot]. rewrite w_mulw. unfold v_mulw. symmetry. apply w32_exact; [|exact R].
    rewrite m_mul. unfold v_mul. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    pose proof (Z.div_mod (bv_unsigned (edenot E a2) * bv_unsigned (edenot E b2)) (2 ^ 64) ltac:(lia)) as DM.
    exists ((bv_unsigned (edenot E a2) * bv_unsigned (edenot E b2)) / 2 ^ 64). lia.
  - cbn [edenot]. rewrite IHa. reflexivity.
Qed.

Lemma split_w_child : forall E base rom ss ms, st_okX segs E base rom ss ms -> st_okX segs E base rom (sw ss) ms.
Proof.
  intros E base rom ss ms HX E'' Ha. cbn [sw s_next] in Ha.
  destruct (HX E'' Ha) as (regs & Hms & HR & Hlf & HK).
  exists regs. cbn [sw s_pc s_regs s_log s_know s_resv]. split; [exact Hms|]. split; [|split; [exact Hlf | exact HK]].
  apply regs_ok_map; [| reflexivity | exact HR].
  intros e. rewrite (slt_lit_den E'' base _ _ (facts_of_ok segs E'' base _ HK)).
  exact (wnorm_den E'' base _ (facts_of_ok segs E'' base _ HK) e).
Qed.

(* [comment removed for export] *)
Lemma stepF_nonmem : forall FP E base rom ss ms ms1 i w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  SAC.mem_kind i = false -> SAC.is_atomic i = false ->
  st_okX segs E base rom ss ms -> RiscvSemantics.step segs ms = MachineOk ms1 -> ExecF.mstepF segs FP ms ms1.
Proof.
  intros FP E base rom ss ms ms1 i w Hf He Hd Hm Ha HX Hs.
  destruct (st_okR_parts segs E base rom ss ms (st_okX_R _ _ _ _ _ _ HX)) as (_ & _ & _ & _ & Hms).
  split; [exact (st_okR_svc _ _ _ _ _ (st_okX_R _ _ _ _ _ _ HX))|].
  assert (Hpc : ms_pc ms = Z_to_bv 64 (s_pc ss)) by (rewrite Hms; reflexivity).
  rewrite <- Hpc in Hf.
  exists []. split; [|constructor].
  rewrite (SAC.step_accesses_simple segs ms ms1 w i 4 Hf He Hd Ha Hs). rewrite SAC.eff_accs_nonmem by assumption. reflexivity.
Qed.

End FX.

Definition awin_den (E : env) (w : awin) : Z * Z :=
  let '(b, off, n) := w in (bv_unsigned (edenot E b) + off, bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n))%Z.

(* [comment removed for export] *)
Definition fp_of (aw : option (list awin)) (E : env) : ExecF.footprint :=
  match aw with
  | None => fun _ _ => True
  | Some W => fun b j => exists w, In w W /\ (fst (awin_den E w) <= b /\ b + Z.of_nat j <= snd (awin_den E w))%Z
  end.

Definition aw_closed (n : nat) (aw : option (list awin)) : bool :=
  match aw with
  | None => true
  | Some W => forallb (fun w => let '(b, _, l) := w in (AxSymRun3.expr_vars_lt n b && AxSymRun3.expr_vars_lt n l)%bool) W
  end.

(* [comment removed for export] *)
Definition aw_genuine (E : env) (aw : option (list awin)) : Prop :=
  match aw with
  | None => True
  | Some W => forall w, In w W -> (0 <= fst (awin_den E w) /\ snd (awin_den E w) <= 2^64)%Z
  end.

Lemma awin_den_agree : forall n E E' w, eagree n E E' -> (let '(b, _, l) := w in (AxSymRun3.expr_vars_lt n b && AxSymRun3.expr_vars_lt n l)%bool) = true ->
  awin_den E w = awin_den E' w.
Proof.
  intros n E E' [[b off] l] Ha Hc. apply andb_prop in Hc as [Hb Hl]. apply eagree_env_agree in Ha.
  cbn [awin_den]. rewrite (AxSymRun3.edenot_agree n E E' b Ha Hb), (AxSymRun3.edenot_agree n E E' l Ha Hl). reflexivity.
Qed.

Lemma fp_of_agree : forall n E E' aw, eagree n E E' -> aw_closed n aw = true -> forall b j, fp_of aw E' b j -> fp_of aw E b j.
Proof.
  intros n E E' [W|] Ha Hc b j H; [|exact I]. destruct H as (w & Hw & H). exists w. split; [exact Hw|].
  rewrite (awin_den_agree n E E' w Ha (proj1 (forallb_forall _ _) Hc w Hw)). exact H.
Qed.

Lemma aw_genuine_agree : forall n E E' aw, eagree n E E' -> aw_closed n aw = true -> aw_genuine E aw -> aw_genuine E' aw.
Proof.
  intros n E E' [W|] Ha Hc H; [|exact I]. intros w Hw. rewrite <- (awin_den_agree n E E' w Ha (proj1 (forallb_forall _ _) Hc w Hw)).
  exact (H w Hw).
Qed.

Lemma vars_lt_mono : forall b b' e, AxSymRun3.expr_vars_lt b e = true -> (b <= b')%nat -> AxSymRun3.expr_vars_lt b' e = true.
Proof.
  intros b b' e H Hle. induction e; cbn [AxSymRun3.expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite IHe1, IHe2 by assumption; reflexivity); try (apply IHe; exact H).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

Lemma aw_closed_mono : forall n n' aw, aw_closed n aw = true -> (n <= n')%nat -> aw_closed n' aw = true.
Proof.
  intros n n' [W|] H Hle; [|reflexivity]. cbn [aw_closed] in *. apply forallb_forall. intros [[b off] l] Hw.
  pose proof (proj1 (forallb_forall _ _) H _ Hw) as X. cbv beta iota in X |- *. apply andb_prop in X as [X1 X2].
  rewrite (vars_lt_mono n n' b X1 Hle), (vars_lt_mono n n' l X2 Hle). reflexivity.
Qed.

Lemma mstepsF_agree : forall n E E' aw ms ms', eagree n E E' -> aw_closed n aw = true ->
  ExecF.mstepsF segs (fp_of aw E') ms ms' -> ExecF.mstepsF segs (fp_of aw E) ms ms'.
Proof. intros n E E' aw ms ms' Ha Hc H. eapply ExecF.mstepsF_weaken; [|exact H]. exact (fp_of_agree n E E' aw Ha Hc). Qed.

Section FXA.
Context {fx : FPState}.

Lemma stepF_mem : forall aw E base rom ss ms ms1 i w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  SAC.mem_kind i = true -> acc_check aw i ss = true -> aw_genuine E aw ->
  st_okX segs E base rom ss ms -> RiscvSemantics.step segs ms = MachineOk ms1 -> ExecF.mstepF segs (fp_of aw E) ms ms1.
Proof.
  intros aw E base rom ss ms ms1 i w Hf He Hd Hm Hac Hg HX Hs.
  destruct (st_okR_parts segs E base rom ss ms (st_okX_R _ _ _ _ _ _ HX)) as (HR & _ & _ & HK & Hms).
  assert (Ha : SAC.is_atomic i = false) by (destruct i; try discriminate Hm; reflexivity).
  split; [exact (st_okR_svc _ _ _ _ _ (st_okX_R _ _ _ _ _ _ HX))|].
  assert (Hpc : ms_pc ms = Z_to_bv 64 (s_pc ss)) by (rewrite Hms; reflexivity).
  rewrite <- Hpc in Hf.
  eexists. split; [exact (SAC.step_accesses_simple segs ms ms1 w i 4 Hf He Hd Ha Hs)|].
  destruct aw as [W|]; [|cbn [fp_of]; apply Forall_forall; intros; exact I].
  cbn [acc_check] in Hac. rewrite Ha in Hac.
  assert (ADDR : forall rs (imm : bv 12) nb, mem_acc i ss = Some (to_saddrK (facts_of (s_know ss)) (sr_get (s_regs ss) rs) (bv_signed imm), nb) ->
            acc_okb (s_know ss) (to_saddrK (facts_of (s_know ss)) (sr_get (s_regs ss) rs) (bv_signed imm)) nb W = true ->
            (1 <= nb <= 8)%nat ->
            Forall (ExecF.acc_in (fp_of (Some W) E)) [(rget {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms;
                                                              c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |} rs + sext 64 imm, nb)]).
  { intros rs imm nb _ Hok Hnb. constructor; [|constructor].
    set (a := to_saddrK (facts_of (s_know ss)) (sr_get (s_regs ss) rs) (bv_signed imm)) in *.
    unfold acc_okb in Hok. rewrite SLin.ex2_eq in Hok by (intros [[b0 o0] l0] Hx0; apply SLin.xinside_2; exact Hx0).
    assert (CONT : exists b off len, In (b, off, len) W /\ (estart E (SA b off) <= estart E (SA (a_base a) (a_off a)))%Z /\
                     (estart E (SA (a_base a) (a_off a)) + elenZ E (elen nb) <= estart E (SA b off) + elenZ E len)%Z).
    { match type of Hok with (if ?X then true else _) = true => destruct X eqn:X1 end.
      - apply existsb_exists in X1 as ([[b off] len] & Hw & Hx). cbv beta iota in Hx.
        destruct (SLin.xinside2_sound segs E base (s_know ss) (a_base a) (a_off a) (elen nb) b off len HK Hx) as [A B].
        exists b, off, len. split; [exact Hw|]. split; [exact A | exact B].
      - apply existsb_exists in Hok as ([[b off] len] & Hw & Hx). cbv beta iota in Hx.
        destruct (srange_in_sound E base (s_know ss) (a_base a) (a_off a) nb b off len HK Hx) as [A B].
        exists b, off, len. split; [exact Hw|]. split; [exact A | exact B]. }
    destruct CONT as (b & off & len & Hw & A & B).
    rewrite elenZ_elen in B by lia.
    pose proof (Hg _ Hw) as G. cbn [awin_den fst snd] in G.
    assert (Hadr : adenot E a = rget {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms;
                                         c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |} rs + sext 64 imm).
    { unfold a. rewrite (to_saddrK_denot segs E base (facts_of (s_know ss)) _ _ (facts_of_ok segs E base _ HK)).
      rewrite b_addsext. f_equal. rewrite <- (HR rs). reflexivity. }
    unfold ExecF.acc_in. cbn [fst snd]. rewrite <- Hadr.
    unfold estart, elenZ in A, B. cbn [a_base a_off] in A, B.
    assert (Hfl : flat E a (Z.of_nat nb)).
    { unfold flat. unfold estart. lia. }
    rewrite (flat_u E _ _ Hfl). exists (b, off, len). split; [exact Hw|]. cbn [awin_den fst snd].
    unfold estart. lia. }
  destruct i; try discriminate Hm; cbn [mem_acc] in Hac;
    first [rewrite SAC.eff_accs_load | rewrite SAC.eff_accs_store | rewrite SAC.eff_accs_fload | rewrite SAC.eff_accs_fstore];
    (apply (ADDR _ _ _ eq_refl Hac);
     match goal with |- (1 <= SAC.msz_nb ?x <= 8)%nat => destruct x | |- (1 <= SAC.fmt_nb ?x <= 8)%nat => destruct x end; cbn; lia).
Qed.

End FXA.

(* [comment removed for export] *)
Definition explore_ok (IT : itab) (stops : list Z) (rr : bool) (sps : list split) (aw : option (list awin)) (fuel : nat) : Prop :=
  forall first nosp bc kx ss path xs,
  bc = mkbc (facts_of (s_know ss)) -> kx = mk_kix (s_know ss) ->
  explore segs IT stops rr sps aw fuel first nosp bc kx ss path = Some xs ->
  forall E base rom ms, aw_closed (s_next ss) aw = true -> aw_genuine E aw ->
  SFP.st_okXF segs E base rom ss ms -> path_okX base E (s_next ss) path ->
  exists x E' ms', In x xs /\ eagree (s_next ss) E E' /\ (s_next ss <= s_next (x_ss x))%nat
    /\ ExecF.mstepsF segs (fp_of aw E) ms ms' /\ SFP.st_okXF segs E' base rom (x_ss x) ms'
    /\ path_okX base E' (s_next (x_ss x)) (x_path x) /\ s_resv (x_ss x) = None.

(* [comment removed for export] *)
Lemma stepF_nonmem0 : forall FP ms ms1 i w,
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  SAC.mem_kind i = false -> SAC.is_atomic i = false -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms1 -> ExecF.mstepF segs FP ms ms1.
Proof.
  intros FP ms ms1 i w Hf He Hd Hm Ha Hsvc Hs. split; [exact Hsvc|].
  exists []. split; [|constructor].
  rewrite (SAC.step_accesses_simple segs ms ms1 w i 4 Hf He Hd Ha Hs). rewrite SAC.eff_accs_nonmem by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stepF_true : forall ms ms1, ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms1 ->
  ExecF.mstepF segs (fun _ _ => True) ms ms1.
Proof.
  intros ms ms1 Hsvc Hs. split; [exact Hsvc|]. unfold RiscvSemantics.step in Hs.
  destruct (RiscvSemantics.step_accesses segs ms) as [[v accs]| |] eqn:E; cbn in Hs; try discriminate.
  injection Hs as <-. exists accs. split; [reflexivity|]. apply Forall_forall. intros; exact I.
Qed.

Lemma respell_fp : forall ss i0 scs i, SFP.is_fp_instr i = true -> respell ss i0 scs i = ss.
Proof. intros ss i0 scs i H. destruct i; try reflexivity; discriminate H. Qed.

Section FX2.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma nb_case : forall IT stops rr sps aw f, explore_ok IT stops rr sps aw f ->
  forall bc kx ss path xs i w,
  bc = mkbc (facts_of (s_know ss)) -> kx = mk_kix (s_know ss) ->
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  (if acc_check aw i ss then
   match (if SFP.is_fp_instr i then SFP.fp_step segs i ss else sym_stepBI bc kx segs i ss scr_nil) with
   | SOk ss' scs _ =>
       if (Nat.leb (s_next ss) (s_next ss') && rest_ok segs bc ss ss' scs)%bool then
         explore segs IT stops rr sps aw f false false bc kx (respell ss' (s_next ss) scs i) (if rr then List.filter is_readbase scs ++ path else path)
       else None
   | SStop => None
   end else None) = Some xs ->
  forall E base rom ms, aw_closed (s_next ss) aw = true -> aw_genuine E aw ->
  frm_zero (@fp_csr fx) -> st_okX segs E base rom ss ms -> path_okX base E (s_next ss) path ->
  exists x E' ms', In x xs /\ eagree (s_next ss) E E' /\ (s_next ss <= s_next (x_ss x))%nat
    /\ ExecF.mstepsF segs (fp_of aw E) ms ms' /\ SFP.st_okXF segs E' base rom (x_ss x) ms'
    /\ path_okX base E' (s_next (x_ss x)) (x_path x) /\ s_resv (x_ss x) = None.
Proof.
  intros IT stops rr sps aw f IH bc kx ss path xs i w Hbc Hkx Hf He Hd Hex E base rom ms Hac Hag Hz HX HP.
  destruct (acc_check aw i ss) eqn:Hacc; [|discriminate].
  (* [comment removed for export] *)
  assert (ONE : forall ss' scs scr',
            (if SFP.is_fp_instr i then SFP.fp_step segs i ss else sym_stepBI bc kx segs i ss scr_nil) = SOk ss' scs scr' ->
            (s_next ss <= s_next ss')%nat -> rest_ok segs bc ss ss' scs = true ->
            s_know ss' = s_know ss /\
            exists E1 ms1, eagree (s_next ss) E E1 /\ RiscvSemantics.step segs ms = MachineOk ms1
              /\ SFP.st_okXF segs E1 base rom (respell ss' (s_next ss) scs i) ms1
              /\ (forall E'', eagree (s_next ss') E1 E'' -> scs_denot segs base E'' scs)).
  { intros ss' scs scr' Hst Hle Hrest.
    pose proof (rest_ok_disch segs bc ss ss' scs Hbc Hrest) as Hdis.
    destruct (SFP.is_fp_instr i) eqn:Hfp.
    - split; [exact (SFP.fp_step_know _ _ _ _ _ _ Hst)|].
      destruct (SFP.fp_step_sound segs fx E base rom ss ms i ss' scs scr' w Hfp Hf He Hd Hst Hle Hdis Hz HX)
        as (E1 & ms1 & Ha1 & Hstep1 & HX1 & Hscs1).
      exists E1, ms1. rewrite (respell_fp ss' (s_next ss) scs i Hfp). auto.
    - rewrite (sym_stepBI_ok bc kx _ ss scr_nil Hbc Hkx) in Hst.
      split; [exact (sym_step_know _ _ _ _ _ _ _ Hst)|].
      destruct (stepX0_sound E base rom ss ms _ ss' scs scr' w Hf He Hd Hst Hle Hdis HX) as (E1 & ms1 & Ha1 & Hstep1 & HX1 & Hscs1).
      exists E1, ms1. split; [exact Ha1|]. split; [exact Hstep1|]. split; [|exact Hscs1].
      apply (SFP.st_okX_XF fx segs E1 base rom _ ms1 Hz). exact (respell_ok E1 base rom ss' ms1 (s_next ss) scs i Hscs1 HX1). }
  destruct (if SFP.is_fp_instr i then SFP.fp_step segs i ss else sym_stepBI bc kx segs i ss scr_nil) as [ss' scs scr'|] eqn:Hst;
    [|discriminate].
  destruct (Nat.leb (s_next ss) (s_next ss') && rest_ok segs bc ss ss' scs)%bool eqn:Hok; [|discriminate].
  apply andb_prop in Hok as [Hle Hrest]. apply Nat.leb_le in Hle.
  destruct (ONE ss' scs scr' eq_refl Hle Hrest) as (HK1 & E1 & ms1 & Ha1 & Hstep1 & HX1r & Hscs1).
  edestruct (IH false false bc kx (respell ss' (s_next ss) scs i) _ xs ltac:(rewrite respell_know, HK1; exact Hbc)
               ltac:(rewrite respell_know, HK1; exact Hkx) Hex E1 base rom ms1
               ltac:(rewrite respell_next; exact (aw_closed_mono _ _ aw Hac Hle)) (aw_genuine_agree _ E E1 aw Ha1 Hac Hag) HX1r)
    as (x & E' & ms' & Hin & Ha' & Hle' & Hms & HX' & HP' & Hres).
  { rewrite respell_next. intros E'' Ha''. destruct rr.
    - apply Forall_app. split.
      + apply Forall_forall. intros sc Hsc. apply filter_In in Hsc as [Hsc _].
        exact (proj1 (Forall_forall _ _) (Hscs1 E'' Ha'') sc Hsc).
      + exact (HP E'' ltac:(eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha'' | exact Hle]])).
    - exact (HP E'' ltac:(eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha'' | exact Hle]])). }
  rewrite respell_next in Ha', Hle'.
  assert (STEPF : ExecF.mstepF segs (fp_of aw E) ms ms1).
  { destruct aw as [W|].
    - cbn [acc_check] in Hacc. destruct (SAC.is_atomic i) eqn:Hat; [discriminate|].
      destruct (SAC.mem_kind i) eqn:Hmk.
      + exact (stepF_mem (Some W) E base rom ss ms ms1 i w Hf He Hd Hmk ltac:(cbn [acc_check]; rewrite Hat; exact Hacc) Hag HX Hstep1).
      + exact (stepF_nonmem _ E base rom ss ms ms1 i w Hf He Hd Hmk Hat HX Hstep1).
    - exact (stepF_true ms ms1 (st_okR_svc _ _ _ _ _ (st_okX_R _ _ _ _ _ _ HX)) Hstep1). }
  exists x, E', ms'. split; [exact Hin|]. split; [eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha' | exact Hle]]|].
  split; [lia|]. split; [eapply ExecF.mstepsF_cons; [exact STEPF | exact (mstepsF_agree _ E E1 aw ms1 ms' Ha1 Hac Hms)]|].
  split; [exact HX'|]. split; [exact HP' | exact Hres].
Qed.

End FX2.

Theorem explore_sound : forall IT stops rr sps aw fuel first nosp bc kx ss path xs,
  itab_sound segs IT ->
  bc = mkbc (facts_of (s_know ss)) -> kx = mk_kix (s_know ss) ->
  explore segs IT stops rr sps aw fuel first nosp bc kx ss path = Some xs ->
  forall E base rom ms, aw_closed (s_next ss) aw = true -> aw_genuine E aw ->
  SFP.st_okXF segs E base rom ss ms -> path_okX base E (s_next ss) path ->
  exists x E' ms', In x xs /\ eagree (s_next ss) E E' /\ (s_next ss <= s_next (x_ss x))%nat
    /\ ExecF.mstepsF segs (fp_of aw E) ms ms' /\ SFP.st_okXF segs E' base rom (x_ss x) ms'
    /\ path_okX base E' (s_next (x_ss x)) (x_path x) /\ s_resv (x_ss x) = None.
Proof.
  intros IT stops rr sps aw fuel first nosp bc kx ss path xs HIT. revert first nosp bc kx ss path xs.
  induction fuel as [|f IH]; intros first nosp bc kx ss path xs Hbc Hkx Hex E base rom ms Hac Hag HXF HP; [discriminate|].
  pose proof (proj1 HXF) as HZ. pose proof (proj2 HXF) as HX. cbv beta in HX.
  set (FX := SFP.fx_of ms) in HX, HZ.
  cbn [explore] in Hex.
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool.
  { (* [comment removed for export] *)
    destruct (s_clean ss) eqn:Hc; [|discriminate]. injection Hex as <-.
    exists (SXT ss path), E, ms. cbn [x_ss x_path]. split; [left; reflexivity|]. split; [apply eagree_refl|].
    split; [lia|]. split; [apply ExecF.mstepsF_refl|]. split; [exact HXF|]. split; [exact HP|]. apply s_clean_None. exact Hc. }
  destruct (if nosp then None else find_split (s_pc ss) sps) as [[v pc0 c e1 e2|v pc0 e lo hi|pc0 r|pc0|pc0|pc0|pc0 n lo hi|pc0]|] eqn:Hsp.
  { (* [comment removed for export] *)
    set (a := sp_sub v ss e1) in *. set (b := sp_sub v ss e2) in *.
    destruct (AxSymRun3.expr_vars_lt (s_next ss) a && AxSymRun3.expr_vars_lt (s_next ss) b)%bool eqn:Hcl; [|discriminate].
    apply andb_prop in Hcl as [Hca Hcb].
    assert (CH : forall t rT, branch_taken c (edenot E a) (edenot E b) = t ->
              (match SL.learn (facts_of (s_know ss)) c t a b with
               | None => Some []
               | Some l => explore segs IT stops rr sps aw f first true (mkbc (facts_of (l ++ s_know ss))) (mk_kix (l ++ s_know ss))
                             (set_know ss (l ++ s_know ss)) (SCBr t c a b :: path)
               end) = Some rT ->
              exists x E' ms', In x rT /\ eagree (s_next ss) E E' /\ (s_next ss <= s_next (x_ss x))%nat
                /\ ExecF.mstepsF segs (fp_of aw E) ms ms' /\ SFP.st_okXF segs E' base rom (x_ss x) ms'
                /\ path_okX base E' (s_next (x_ss x)) (x_path x) /\ s_resv (x_ss x) = None).
    { intros t rT Hbr Hr.
      destruct (SL.learn (facts_of (s_know ss)) c t a b) as [l|] eqn:Hl'.
      - destruct (split_cmp_child E base rom ss ms c t a b l Hca Hcb Hbr Hl' HX) as (HX1 & HSC).
        edestruct (IH first true _ _ (set_know ss (l ++ s_know ss)) (SCBr t c a b :: path) rT ltac:(reflexivity) ltac:(reflexivity)
                     Hr E base rom ms Hac Hag (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1)) as (x & E' & ms' & Hin & R).
        { cbn [set_know s_next]. intros E' Ha. constructor; [exact (HSC E' Ha) | exact (HP E' Ha)]. }
        exists x, E', ms'. split; [exact Hin | exact R].
      - exfalso. destruct (st_okR_parts segs E base rom ss ms (HX E (eagree_refl _ _))) as (_ & _ & _ & Hkn & _).
        exact (SL.learn_none segs E base _ c t a b (facts_of_ok segs E base _ Hkn) Hl' Hbr). }
    destruct (match SL.learn (facts_of (s_know ss)) c true a b with
              | None => Some []
              | Some l => explore segs IT stops rr sps aw f first true (mkbc (facts_of (l ++ s_know ss))) (mk_kix (l ++ s_know ss))
                            (set_know ss (l ++ s_know ss)) (SCBr true c a b :: path)
              end) as [r1|] eqn:Hr1; [|discriminate].
    destruct (match SL.learn (facts_of (s_know ss)) c false a b with
              | None => Some []
              | Some l => explore segs IT stops rr sps aw f first true (mkbc (facts_of (l ++ s_know ss))) (mk_kix (l ++ s_know ss))
                            (set_know ss (l ++ s_know ss)) (SCBr false c a b :: path)
              end) as [r0|] eqn:Hr0; [|discriminate].
    injection Hex as <-.
    destruct (branch_taken c (edenot E a) (edenot E b)) eqn:Hbr.
    - destruct (CH true r1 eq_refl Hr1) as (x & E' & ms' & Hin & R). exists x, E', ms'. split; [apply in_or_app; left; exact Hin | exact R].
    - destruct (CH false r0 eq_refl Hr0) as (x & E' & ms' & Hin & R). exists x, E', ms'. split; [apply in_or_app; right; exact Hin | exact R]. }
  { (* [comment removed for export] *)
    set (a := sp_sub v ss e) in *.
    destruct (AxSymRun3.expr_vars_lt (s_next ss) a && Z.leb 0 lo && Z.ltb hi (2^64) &&
              match erange (facts_of (s_know ss)) a with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end)%bool eqn:Hc;
      [|discriminate].
    apply andb_prop in Hc as [Hc Hrg]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hca Hlo].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    destruct (erange (facts_of (s_know ss)) a) as [[l h]|] eqn:Er; [|discriminate]. apply andb_prop in Hrg as [Hl Hh].
    apply Z.leb_le in Hl, Hh.
    destruct (st_okR_parts segs E base rom ss ms (HX E (eagree_refl _ _))) as (_ & _ & _ & Hkn & _).
    pose proof (erange_sound segs E base (facts_of (s_know ss)) a l h (facts_of_ok segs E base _ Hkn) Er) as Hu.
    set (u := bv_unsigned (edenot E a)) in *.
    destruct (kids_gen_in _ _ lo xs Hex u ltac:(rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia)) as (lr & Hg & Hinc).
    cbv beta in Hg.
    destruct (split_enum_child E base rom ss ms a u Hca ltac:(lia) ltac:(lia) eq_refl HX) as (HX1 & HSC).
    edestruct (IH first true _ _ (set_know ss (KRange a u u :: s_know ss)) (SCBr true BC_EQ a (ELit u) :: path) lr
                 ltac:(reflexivity) ltac:(reflexivity) Hg E base rom ms Hac Hag (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1)) as (x & E' & ms' & Hin & R).
    { cbn [set_know s_next]. intros E' Ha. constructor; [exact (HSC E' Ha) | exact (HP E' Ha)]. }
    exists x, E', ms'. split; [exact (Hinc x Hin) | exact R]. }
  { (* [comment removed for export] *)
    destruct (Nat.ltb 0 r && Nat.ltb r 32)%bool; [|discriminate].
    set (E1 := eupd E (s_next ss) (getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)))).
    assert (Ha1 : eagree (s_next ss) E E1) by apply eagree_upd.
    pose proof (split_hav_child E base rom ss ms r HX) as HX1.
    edestruct (IH first true bc kx (shav ss r) path xs Hbc Hkx Hex E1 base rom ms
                 ltac:(cbn [shav s_next]; exact (aw_closed_mono (s_next ss) (S (s_next ss)) aw Hac ltac:(lia))) (aw_genuine_agree _ E E1 aw Ha1 Hac Hag)
                 (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1)
                 ltac:(cbn [shav s_next]; exact (path_okX_le base E E1 (s_next ss) (S (s_next ss)) path HP Ha1 ltac:(lia))))
      as (x & E' & ms' & Hin & Ha' & Hle' & Hms & HX' & HP' & Hres).
    cbn [shav s_next] in Ha', Hle'.
    exists x, E', ms'. split; [exact Hin|]. split; [eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha' | lia]]|].
    split; [lia|]. split; [exact (mstepsF_agree _ E E1 aw ms ms' Ha1 Hac Hms)|].
    split; [exact HX'|]. split; [exact HP' | exact Hres]. }
  { (* [comment removed for export] *)
    pose proof (split_slt_child E base rom ss ms HX) as HX1.
    edestruct (IH first true bc kx (sslt ss) path xs Hbc Hkx Hex E base rom ms Hac Hag (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1) HP)
      as (x & E' & ms' & Hin & R).
    exists x, E', ms'. split; [exact Hin | exact R]. }
  { (* [comment removed for export] *)
    pose proof (split_w_child E base rom ss ms HX) as HX1.
    edestruct (IH first true bc kx (sw ss) path xs Hbc Hkx Hex E base rom ms Hac Hag (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1) HP)
      as (x & E' & ms' & Hin & R).
    exists x, E', ms'. split; [exact Hin | exact R]. }
  { (* [comment removed for export] *)
    destruct (SL.al_tight (facts_of (s_know ss)) (facts_of (s_know ss))) as [l|] eqn:Hl'.
    - pose proof (split_al_child E base rom ss ms l Hl' HX) as HX1.
      edestruct (IH first true _ _ (set_know ss (l ++ s_know ss)) path xs ltac:(reflexivity) ltac:(reflexivity)
                   Hex E base rom ms Hac Hag (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1) HP) as (x & E' & ms' & Hin & R).
      exists x, E', ms'. split; [exact Hin | exact R].
    - exfalso. destruct (st_okR_parts segs E base rom ss ms (HX E (eagree_refl _ _))) as (_ & _ & _ & Hkn & _).
      pose proof (facts_of_ok segs E base _ Hkn) as HF.
      exact (proj2 (SL.al_tight_ok segs E base _ _ HF HF) Hl'). }
  { (* [comment removed for export] *)
    set (a := EVar n) in *.
    destruct (AxSymRun3.expr_vars_lt (s_next ss) a && Z.leb 0 lo && Z.ltb hi (2^64) &&
              match erange (facts_of (s_know ss)) a with Some (l, h) => (Z.leb lo l && Z.leb h hi)%bool | None => false end)%bool eqn:Hc;
      [|discriminate].
    apply andb_prop in Hc as [Hc Hrg]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hca Hlo].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    destruct (erange (facts_of (s_know ss)) a) as [[l h]|] eqn:Er; [|discriminate]. apply andb_prop in Hrg as [Hl Hh].
    apply Z.leb_le in Hl, Hh.
    destruct (st_okR_parts segs E base rom ss ms (HX E (eagree_refl _ _))) as (_ & _ & _ & Hkn & _).
    pose proof (erange_sound segs E base (facts_of (s_know ss)) a l h (facts_of_ok segs E base _ Hkn) Er) as Hu.
    set (u := bv_unsigned (edenot E a)) in *.
    destruct (kids_gen_in _ _ lo xs Hex u ltac:(rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia)) as (lr & Hg & Hinc).
    cbv beta in Hg.
    destruct (SL.sub_facts (facts_of (s_know ss)) n u) as [D|] eqn:HD.
    2:{ exfalso. pose proof (SL.sub_facts_ok segs E base (facts_of (s_know ss)) n u (facts_of_ok segs E base _ Hkn) eq_refl) as H0.
        rewrite HD in H0. exact H0. }
    destruct (split_enum_child E base rom ss ms a u Hca ltac:(lia) ltac:(lia) eq_refl HX) as (HX1 & HSC).
    pose proof (split_sub_child E base rom ss ms n u D HD HX1) as HX2.
    edestruct (IH first true _ _ (set_know ss (D ++ KRange a u u :: s_know ss)) (SCBr true BC_EQ a (ELit u) :: path) lr
                 ltac:(reflexivity) ltac:(reflexivity) Hg E base rom ms Hac Hag (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX2)) as (x & E' & ms' & Hin & R).
    { cbn [set_know s_next]. intros E' Ha. constructor; [exact (HSC E' Ha) | exact (HP E' Ha)]. }
    exists x, E', ms'. split; [exact (Hinc x Hin) | exact R]. }
  { (* [comment removed for export] *)
    pose proof (split_rdk_child E base rom ss ms path HX HP) as HX1.
    edestruct (IH first true _ _ (set_know ss (rd_know (facts_of (s_know ss)) path ++ s_know ss)) path xs ltac:(reflexivity) ltac:(reflexivity)
                 Hex E base rom ms Hac Hag (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1) HP) as (x & E' & ms' & Hin & R).
    exists x, E', ms'. split; [exact Hin | exact R]. }
  destruct (itab_lookup IT (s_pc ss)) as [i|] eqn:Hl; [|discriminate].
  destruct (itab_facts IT (s_pc ss) i HIT Hl) as (w & Hf & He & Hd).
  destruct i;
    (* [comment removed for export] *)
    try (eapply (nb_case IT stops rr sps aw f IH); [exact Hbc | exact Hkx | exact Hf | exact He | exact Hd | exact Hex | exact Hac | exact Hag | exact HZ | exact HX | exact HP]).
  (* [comment removed for export] *)
  rewrite !(sym_stepBI_ok bc kx _ ss _ Hbc Hkx) in Hex.
  destruct (sym_step segs (Branch c rs1 rs2 imm) ss (SCR [true] [] [])) as [ss1 scs1 scr1|] eqn:Hs1; [|discriminate].
  destruct (branch_scs c rs1 rs2 imm ss _ ss1 scs1 scr1 Hs1) as (Hn1 & Hk1 & _).
  destruct scs1 as [|sc1 scs1'].
  { (* [comment removed for export] *)
    destruct (sym_step_soundR segs E base rom ss ms _ ss1 [] _ scr1 w Hf He Hd Hs1 (Forall0 _) (st_okX_R _ _ _ _ _ _ HX))
      as (ms1 & Hstep1 & _).
    assert (HX1 : @st_okX FX segs E base rom ss1 ms1).
    { intros E' Ha. rewrite Hn1 in Ha.
      destruct (sym_step_soundR segs E' base rom ss ms _ ss1 [] _ scr1 w Hf He Hd Hs1 (Forall0 _) (HX E' Ha))
        as (ms'' & Hstep'' & HR''). rewrite Hstep1 in Hstep''. injection Hstep'' as <-. exact HR''. }
    edestruct (IH false false bc kx ss1 path xs ltac:(rewrite Hk1; exact Hbc) ltac:(rewrite Hk1; exact Hkx) Hex E base rom ms1
                 ltac:(rewrite Hn1; exact Hac) Hag (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1) ltac:(rewrite Hn1; exact HP))
      as (x & E' & ms' & Hin & Ha' & Hle' & Hms & HX' & HP' & Hres).
    exists x, E', ms'. rewrite Hn1 in Ha', Hle'. split; [exact Hin|]. split; [exact Ha'|]. split; [exact Hle'|].
    split; [eapply ExecF.mstepsF_cons; [exact (stepF_nonmem _ E base rom ss ms ms1 _ w Hf He Hd eq_refl eq_refl HX Hstep1) | exact Hms]|].
    split; [exact HX'|]. split; [exact HP' | exact Hres]. }
  (* [comment removed for export] *)
  destruct (sym_step segs (Branch c rs1 rs2 imm) ss (SCR [false] [] [])) as [ss0 scs0 scr0|] eqn:Hs0; [|discriminate].
  destruct scs0 as [|sc0 scs0']; [discriminate|].
  pose proof (branch_undecided c rs1 rs2 imm ss true _ _ scr1 Hs1 ltac:(discriminate)) as Hsc1.
  pose proof (branch_undecided c rs1 rs2 imm ss false _ _ scr0 Hs0 ltac:(discriminate)) as Hsc0.
  rewrite Hsc1 in Hs1. rewrite Hsc0 in Hs0. clear Hsc1 Hsc0.
  destruct (branch_scs c rs1 rs2 imm ss _ ss0 _ scr0 Hs0) as (Hn0 & Hk0 & _).
  set (a := sr_get (s_regs ss) rs1) in *. set (b := sr_get (s_regs ss) rs2) in *.
  (* [comment removed for export] *)
  assert (CH : forall t ssT scrT rT, sym_step segs (Branch c rs1 rs2 imm) ss (SCR [t] [] []) = SOk ssT [SCBr t c a b] scrT ->
              branch_taken c (getr (ms_regs ms) rs1) (getr (ms_regs ms) rs2) = t ->
              (match SL.learn (facts_of (s_know ss)) c t a b with
               | None => Some []
               | Some l => explore segs IT stops rr sps aw f false false (mkbc (facts_of (l ++ s_know ss))) (mk_kix (l ++ s_know ss))
                             (set_know ssT (l ++ s_know ss)) (SCBr t c a b :: path)
               end) = Some rT ->
              exists x E' ms', In x rT /\ eagree (s_next ss) E E' /\ (s_next ss <= s_next (x_ss x))%nat
                /\ ExecF.mstepsF segs (fp_of aw E) ms ms' /\ SFP.st_okXF segs E' base rom (x_ss x) ms'
                /\ path_okX base E' (s_next (x_ss x)) (x_path x) /\ s_resv (x_ss x) = None).
  { intros t ssT scrT rT HsT Hbr Hr.
    destruct (SL.learn (facts_of (s_know ss)) c t a b) as [l|] eqn:Hl'.
    - destruct (fork_child E base rom ss ms c rs1 rs2 imm t ssT scrT w l Hf He Hd HsT Hbr Hl' HX)
        as (ms1 & Hstep1 & HX1 & Hn & HSC).
      edestruct (IH false false _ _ (set_know ssT (l ++ s_know ss)) (SCBr t c a b :: path) rT
                   ltac:(reflexivity) ltac:(reflexivity) Hr E base rom ms1 ltac:(rewrite Hn; exact Hac) Hag
                   (SFP.st_okX_XF FX segs _ _ _ _ _ HZ HX1))
        as (x & E' & ms' & Hin & Ha' & Hle' & Hms & HX' & HP' & Hres).
      { rewrite Hn. intros E' Ha. constructor; [exact (HSC E' Ha) | exact (HP E' Ha)]. }
      exists x, E', ms'. rewrite Hn in Ha', Hle'. split; [exact Hin|]. split; [exact Ha'|]. split; [exact Hle'|].
      split; [eapply ExecF.mstepsF_cons; [exact (stepF_nonmem _ E base rom ss ms ms1 _ w Hf He Hd eq_refl eq_refl HX Hstep1) | exact Hms]|].
      split; [exact HX'|]. split; [exact HP' | exact Hres].
    - exfalso. exact (fork_none E base rom ss ms c rs1 rs2 t Hl' HX Hbr). }
  destruct (match SL.learn (facts_of (s_know ss)) c true a b with
            | None => Some []
            | Some l => explore segs IT stops rr sps aw f false false (mkbc (facts_of (l ++ s_know ss))) (mk_kix (l ++ s_know ss))
                          (set_know ss1 (l ++ s_know ss)) (SCBr true c a b :: path)
            end) as [r1|] eqn:Hr1; [|discriminate].
  destruct (match SL.learn (facts_of (s_know ss)) c false a b with
            | None => Some []
            | Some l => explore segs IT stops rr sps aw f false false (mkbc (facts_of (l ++ s_know ss))) (mk_kix (l ++ s_know ss))
                          (set_know ss0 (l ++ s_know ss)) (SCBr false c a b :: path)
            end) as [r0|] eqn:Hr0; [|discriminate].
  injection Hex as <-.
  destruct (branch_taken c (getr (ms_regs ms) rs1) (getr (ms_regs ms) rs2)) eqn:Hbr.
  - destruct (CH true ss1 scr1 r1 Hs1 eq_refl Hr1) as (x & E' & ms' & Hin & R).
    exists x, E', ms'. split; [apply in_or_app; left; exact Hin | exact R].
  - destruct (CH false ss0 scr0 r0 Hs0 eq_refl Hr0) as (x & E' & ms' & Hin & R).
    exists x, E', ms'. split; [apply in_or_app; right; exact Hin | exact R].
Qed.

End Sound.
End SX.
