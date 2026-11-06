(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbn.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK0o YK15.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP00 YP0k YP06 YP03 YP0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Record shent := mkSHE { she_m : nat; she_lo : Z; she_hi : Z }.
Record shob := mkOB { ob_x : sv; ob_n : Z }.
Record shtok := mkTK { tk_reg : reg; tk_T : nat; tk_x : sv; tk_sg : bool }.
Record shst := mkSH { sh_ss : sstate; sh_j : nat; sh_toks : list shtok; sh_chk : bool; sh_obls : list shob }.
Inductive tres := TRun (st : shst) | TEcall (st : shst) | TStop (why : stop_reason).
Fixpoint extK (E : env) (K : nat) (ws : list word) : env :=
match ws with
| [] => E
| w :: ws' => extK (ewset E K w) (S K) ws'
end.
Fixpoint sv_atom_bound (v : sv) : nat :=
match v with
| SLit _ => 0
| SOff n _ => S n
| SAlu _ a b | SAluw _ a b | SMd _ a b | SMdw _ a b => Nat.max (sv_atom_bound a) (sv_atom_bound b)
| SExt _ _ a => sv_atom_bound a
| SData _ _ _ => 0
| SF1 _ a => sv_atom_bound a
| SF2 _ a b => Nat.max (sv_atom_bound a) (sv_atom_bound b)
| SF3 _ a b c => Nat.max (sv_atom_bound a) (Nat.max (sv_atom_bound b) (sv_atom_bound c))
end.
Definition list_max_map {A} (f : A -> nat) (l : list A) : nat := fold_right (fun x m => Nat.max (f x) m) 0%nat l.
Definition cval_atom_bound (cv : cval) : nat := match cv with CVal _ v => sv_atom_bound v | _ => 0%nat end.
Definition region_atom_bound (r : region) : nat :=
Nat.max (match r_base r with Some n => S n | None => 0%nat end)
(list_max_map (fun c => cval_atom_bound (c_val c)) (r_chunks r)).
Definition facts_atom_bound (G : facts) : nat :=
Nat.max (list_max_map (fun p => S (fst p)) (f_atoms G))
(Nat.max (list_max_map (fun c => Nat.max (sv_atom_bound (ac_a c)) (sv_atom_bound (ac_b c))) (f_conds G))
(list_max_map (fun p => Nat.max (sv_atom_bound (fst p)) (sv_atom_bound (snd p))) (f_alias G))).
Definition ss_atom_bound (ss : sstate) : nat :=
Nat.max (list_max_map sv_atom_bound (ss_regs ss))
(Nat.max (list_max_map region_atom_bound (ss_mem ss))
(Nat.max (facts_atom_bound (ss_facts ss))
(match ss_resv ss with Some a => sv_atom_bound a | None => 0%nat end))).
Definition sh_atom_bound (Bx : sv) (SH : list shent) : nat :=
Nat.max (sv_atom_bound Bx) (list_max_map (fun e => S (she_m e)) SH).
Definition run_K (floor : nat) (Bx : sv) (SH : list shent) (ss : sstate) : nat :=
Nat.max floor (Nat.max (ss_atom_bound ss) (sh_atom_bound Bx SH)).
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Definition srl3_any (v : sv) : option sv :=
match v with
| SAlu ALU_SRL x (SLit k) => if k =? 3 then Some x else None
| _ => None
end.
Definition match_x_core (v : sv) : option sv :=
match v with
| SAlu ALU_ADD u w =>
match srl3_any u with
| Some x => if sv_eqb w Bx then Some x else None
| None => match srl3_any w with
| Some x => if sv_eqb u Bx then Some x else None
| None => None
end
end
| _ => None
end.
Definition match_x (a : sv) : option sv :=
match match_x_core a with
| Some x => Some x
| None => match a with
| SAlu ALU_ADD v (SLit z) => if zcanon z =? 0 then match_x_core v else None
| _ => None
end
end.
Fixpoint find_shent (l : list shent) (i : nat) (m : nat) (c : Z) : option (nat * shent) :=
match l with
| [] => None
| e :: l' => if (Nat.eqb (she_m e) m) && (she_lo e <=? c) && (c <? she_hi e)
then Some (i, e) else find_shent l' (S i) m c
end.
Definition window_itv (G : facts) (r : region) : option itv :=
if r_whi r <=? r_wlo r then None else
Some (match r_base r with
| None => Some (r_wlo r, r_whi r - 1)
| Some n => match sv_urange G (SOff n 0) with
| Some (bl, bh) => Some (bl + r_wlo r, bh + r_whi r - 1)
| None => None
end
end).
Definition itv_disjoint (a b : itv) : bool :=
match a, b with
| Some (al, ah), Some (bl, bh) => (ah <? bl) || (bh <? al)
| _, _ => false
end.
Definition window_covered (r : region) : bool :=
match r_base r with
| Some n => existsb (fun e => Nat.eqb (she_m e) n && (Z.min (she_lo e) (she_hi e) <=? r_wlo r) && (r_whi r <=? Z.max (she_lo e) (she_hi e))) SH
| None => false
end.
Definition span_in_band (G : facts) : bool :=
match sv_urange G Bx with
| Some (Bl, Bh) => (Bl =? Bh) && (Bl <=? fst Bspan) && (snd Bspan <? Bl + 17592186044416)
| None => false
end.
Definition cells_safe_b (G : facts) (rs : smem) : bool :=
forallb (fun r => match window_itv G r with
| None => true
| Some w => itv_disjoint w (Some Bspan) || (window_covered r && span_in_band G)
end) rs.
Definition shent_in_span (G : facts) (e : shent) : bool :=
(she_hi e <=? she_lo e) ||
match sv_urange G Bx, sv_urange G (SOff (she_m e) 0) with
| Some (Bl, Bh), Some (ml, mh) =>
(Bl =? Bh) && (she_lo e <? she_hi e) && (0 <=? ml + she_lo e) && (mh + she_hi e <? M64)
&& (fst Bspan <=? Bl + (ml + she_lo e) / 8) && (Bh + (mh + she_hi e - 1) / 8 <=? snd Bspan)
| _, _ => false
end.
Definition sh_atoms_ltb (k : nat) : bool :=
sv_atoms_lt k Bx && forallb (fun e => Nat.ltb (she_m e) k) SH.
Definition sh_static_ok (G : facts) (rs : smem) : bool :=
cells_safe_b G rs && forallb (shent_in_span G) SH && (Nat.ltb 0 K) && ((0 <=? fst Bspan) && (snd Bspan <? M64))
&& sh_atoms_ltb K.
Definition covered (x : sv) (n : Z) : bool :=
match x with
| SOff m c => match find_shent SH 0 m c with
| Some (_, e) => c + n <=? she_hi e
| None => false
end
| _ => false
end.
Definition ob_in_span (G : facts) (x : sv) (n : Z) : bool :=
match sv_urange G Bx, sv_urange G x with
| Some (Bl, Bh), Some (xl, xh) =>
(0 <? n) && (fst Bspan <=? Bl + xl / 8) && (Bh + (xh + n - 1) / 8 <=? snd Bspan)
| _, _ => false
end.
Definition add_ob (x : sv) (n : Z) (l : list shob) : list shob :=
if existsb (fun o => sv_eqb (ob_x o) x && (n <=? ob_n o)) l then l
else mkOB x n :: List.filter (fun o => negb (sv_eqb (ob_x o) x && (ob_n o <=? n))) l.
Definition need (G : facts) (x : sv) (n : Z) (obls : list shob) : option (list shob) :=
if covered x n then Some obls
else if sv_atoms_lt K x && ob_in_span G x n then Some (add_ob x n obls) else None.
Definition gran (G : facts) (x : sv) : sv :=
match x with
| SOff m c =>
match atom_lookup (f_atoms G) m with
| Some f => if (3 <=? af_al2 f) && (af_al2 f <=? 64) && (0 <=? af_lo f) && (0 <=? c - c mod 8) && (af_hi f + c <? M64)
then SOff m (c - c mod 8) else x
| None => x
end
| _ => x
end.
Definition tok_live (ss : sstate) (tk : shtok) : bool :=
sv_eqb (sr_get (ss_regs ss) (tk_reg tk)) (SOff (tk_T tk) 0).
Definition prune (ss : sstate) (toks : list shtok) : list shtok := List.filter (tok_live ss) toks.
Definition advance (st : shst) (ss' : sstate) : shst :=
mkSH ss' (sh_j st) (prune ss' (sh_toks st)) (sh_chk st) (sh_obls st).
Fixpoint find_tok (toks : list shtok) (r : reg) (T : nat) : option shtok :=
match toks with
| [] => None
| tk :: l => if bv_eqb (tk_reg tk) r && Nat.eqb (tk_T tk) T then Some tk else find_tok l r T
end.
Definition tok_load (st : shst) (sg : bool) (rd : reg) (a : sv) : option shst :=
let ss := sh_ss st in
let G := ss_facts ss in
if bv_eqb rd 0 then None else
match match_x a with
| None => None
| Some x =>
if negb (sh_chk st) then None else
match ss_resv ss with Some _ => None | None =>
if covered x 8 then
let ss' := setreg ss rd (SLit 0) (ss_pc ss + 4) in
Some (mkSH ss' (sh_j st) (prune ss' (sh_toks st)) (sh_chk st) (sh_obls st))
else
let T := (K + sh_j st)%nat in
if negb (ss_atoms_lt T ss) || negb (sv_atoms_lt K x) then None else
match need G x 1 (sh_obls st) with
| None => None
| Some obls' =>
let ss' := setreg ss rd (SOff T 0) (ss_pc ss + 4) in
Some (mkSH ss' (S (sh_j st)) (mkTK rd T x sg :: prune ss' (sh_toks st)) (sh_chk st) obls')
end
end
end.
Definition as_andi (i : instr) : option (reg * reg * Z) :=
match i with OpImm ALU_AND u xr imm => Some (u, xr, bv_signed imm) | _ => None end.
Definition as_addi (i : instr) : option (reg * reg * Z) :=
match i with OpImm ALU_ADD u1 u2 imm => Some (u1, u2, bv_signed imm) | _ => None end.
Definition as_branch (i : instr) : option (branch_cond * reg * reg * Z) :=
match i with Branch c r1 r2 off => Some (c, r1, r2, bv_signed off) | _ => None end.
Definition as_j (i : instr) : option Z :=
match i with Jal rd off => if bv_eqb rd 0 then Some (bv_signed off) else None | _ => None end.
Definition dec (pc : Z) : option instr :=
match clookup tbl pc with
| Some wz => let w := Z_to_bv 32 wz in
if is_ecall w then None else
match decode_any w with Some (i, sz) => if sz =? 4 then Some i else None | None => None end
| None => None
end.
Definition decp {A} (f : instr -> option A) (pc : Z) : option A :=
match dec pc with Some i => f i | None => None end.
Definition slow_block (L Lz : Z) (t : reg) : option (reg * reg * Z) :=
match decp as_andi L with
| Some (u, xr, i7) =>
if negb (i7 =? 7) || bv_eqb u 0 || bv_eqb u t then None else
let '(k, L2) := match decp as_addi (L + 4) with
| Some (u1, u2, k) => if bv_eqb u1 u && bv_eqb u2 u then (k, L + 8) else (0, L + 4)
| None => (0, L + 4)
end in
if negb ((0 <=? k) && (k <=? 7)) then None else
match decp as_branch L2 with
| Some (BC_LT, r1, r2, off) =>
if bv_eqb r1 u && bv_eqb r2 t && (zcanon (L2 + off) =? zcanon Lz) then Some (u, xr, k) else None
| Some (BC_GE, r1, r2, off) =>
if bv_eqb r1 u && bv_eqb r2 t then
match decp as_j (L2 + 4) with
| Some offj => if zcanon (L2 + 4 + offj) =? zcanon Lz then Some (u, xr, k) else None
| None => None
end
else None
| _ => None
end
| None => None
end.
Definition tok_branch (st : shst) (cnd : branch_cond) (rs1 rs2 : reg) (imm : Z) : option shst :=
let ss := sh_ss st in
let G := ss_facts ss in
let R := sr_get (ss_regs ss) in
if negb (bv_eqb rs2 0) then None else
match ss_resv ss with Some _ => None | None =>
match R rs1 with
| SOff T z0 =>
if negb (z0 =? 0) then None else
match find_tok (sh_toks st) rs1 T with
| None => None
| Some tk =>
let x := tk_x tk in
let pc := ss_pc ss in
let '(Lnz, Lz) := match cnd with
| BC_NE => (zcanon (pc + imm), pc + 4)
| BC_EQ => (pc + 4, zcanon (pc + imm))
| _ => (0, 0) end in
match cnd with
| BC_NE | BC_EQ =>
match slow_block Lnz Lz rs1 with
| Some (u, xr, k) =>
if negb (sv_eqb (R xr) x) then None else
let U0 := (K + sh_j st)%nat in
if negb (ss_atoms_lt U0 ss) then None else
match need G x (k + 1) (sh_obls st) with
| None => None
| Some obls' =>
let ss' := setreg ss u (SOff U0 0) Lz in
Some (mkSH ss' (S (sh_j st)) (prune ss' (sh_toks st)) (sh_chk st) obls')
end
| None =>
match dec Lnz with
| None => None
| Some i =>
match as_andi i with
| Some _ => None
| None =>
match need G (gran G x) 8 (sh_obls st) with
| None => None
| Some obls' =>
let ss' := setreg ss rs1 (SLit 0) Lz in
Some (mkSH ss' (sh_j st) (prune ss' (sh_toks st)) (sh_chk st) obls')
end
end
end
end
| _ => None
end
end
| _ => None
end
end.
Definition sym_step_tok (st : shst) : tres :=
let ss := sh_ss st in
match sym_step_sh segs tbl ss with
| SRun ss' => TRun (advance st ss')
| SEcall ss' => TEcall (advance st ss')
| SStop why =>
match dec (ss_pc ss) with
| Some (Load SZ1 sg rd rs1 imm) =>
let a := s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm)) in
match tok_load st sg rd a with Some st' => TRun st' | None => TStop why end
| Some (Branch cnd rs1 rs2 imm) =>
match tok_branch st cnd rs1 rs2 (bv_signed imm) with Some st' => TRun st' | None => TStop why end
| _ => TStop why
end
end.
Inductive trun_status := TS_running | TS_ecall | TS_stopped (why : stop_reason).
Fixpoint sym_run_tok (fuel : nat) (st : shst) : shst * trun_status :=
match fuel with
| O => (st, TS_running)
| S f => match sym_step_tok st with
| TRun st' => sym_run_tok f st'
| TEcall st' => (st', TS_ecall)
| TStop why => (st, TS_stopped why)
end
end.
Fixpoint sym_run_to_tok (fuel : nat) (stop_pc : Z) (st : shst) : shst * trun_status :=
match fuel with
| O => (st, TS_running)
| S f => if ss_pc (sh_ss st) =? stop_pc then (st, TS_running) else
match sym_step_tok st with
| TRun st' => sym_run_to_tok f stop_pc st'
| TEcall st' => (st', TS_ecall)
| TStop why => (st, TS_stopped why)
end
end.
Definition start (ss : sstate) : shst := mkSH ss 0 [] (sh_static_ok (ss_facts ss) (ss_mem ss)) [].
Definition sym_runN_tok (n : N) (ss : sstate) := sym_run_tok (N.to_nat n) (start ss).
Definition sym_run_toN_tok (n : N) (stop : Z) (ss : sstate) := sym_run_to_tok (N.to_nat n) stop (start ss).
End d.
Lemma extK_snoc : forall E K ws w, extK E K (ws ++ [w]) = ewset (extK E K ws) (K + length ws) w.
Proof.
intros E K ws. revert E K. induction ws as [|w0 ws IH]; intros E K w; cbn.
- rewrite Nat.add_0_r. reflexivity.
- rewrite IH. f_equal. lia.
Qed.
Lemma env_agree_extK : forall E K ws, env_agree K E (extK E K ws).
Proof.
intros E K ws. revert E K. induction ws as [|w ws IH]; intros E K; cbn.
- apply env_agree_refl.
- eapply env_agree_trans; [apply env_agree_ewset|].
eapply env_agree_le; [|apply IH]. lia.
Qed.
Section g.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Variables (K : nat) (Bx : sv) (Bspan : Z * Z) (SH : list shent).
Hypothesis Htbl : table_ok segs tbl.
Local Notation sym_step_tok := (sym_step_tok segs tbl K Bx Bspan SH).
Local Notation tok_load := (tok_load K Bx Bspan SH).
Local Notation tok_branch := (tok_branch tbl K Bx Bspan SH).
Local Notation need := (need K Bx Bspan SH).
Local Notation covered := (covered SH).
Local Notation sh_atoms_lt := (sh_atoms_ltb Bx SH).
Definition rd_of (m : word -> option byte) : Z -> option Z :=
fun a => option_map (fun b : byte => bv_unsigned b) (mbyte segs m a).
Definition app_apart (E : env) (e : shent) : Prop :=
forall a, U E (SOff (she_m e) 0) + Z.min (she_lo e) (she_hi e) <= a < U E (SOff (she_m e) 0) + Z.max (she_lo e) (she_hi e) ->
~ (U E Bx <= a < U E Bx + 17592186044416).
Definition shent_ok (E : env) (m : word -> option byte) (e : shent) : Prop :=
range_addressable (rd_of m) (U E Bx) (U E (SOff (she_m e) 0) + she_lo e) (she_hi e - she_lo e)
/\ app_apart E e.
Definition sh_ok (E : env) (m : word -> option byte) : Prop := Forall (shent_ok E m) SH.
Definition ob_holds (E : env) (m : word -> option byte) (o : shob) : Prop :=
range_addressable (rd_of m) (U E Bx) (U E (ob_x o)) (ob_n o).
Definition cell_of (E : env) (e : shent) (c : Z) : Z := U E Bx + (U E (SOff (she_m e) 0) + c) / 8.
Definition cell_x (E : env) (x : sv) : Z := U E Bx + U E x / 8.
Definition tok_ok (E : env) (m : word -> option byte) (tk : shtok) : Prop :=
sv_atoms_lt K (tk_x tk) = true
/\ fst Bspan <= cell_x E (tk_x tk) <= snd Bspan
/\ exists b, mbyte segs m (cell_x E (tk_x tk)) = Some b
/\ ew E (tk_T tk) = (if tk_sg tk then v_lb b else Z_to_bv 64 (bv_unsigned b)).
Definition ob_span (E : env) (o : shob) : Prop :=
forall i, 0 <= i < ob_n o -> fst Bspan <= U E Bx + (U E (ob_x o) + i) / 8 <= snd Bspan.
Definition dom (final : list shob) (o : shob) : Prop :=
exists o', In o' final /\ ob_x o' = ob_x o /\ ob_n o <= ob_n o'.
Definition doml (l final : list shob) : Prop := forall o, In o l -> dom final o.
Definition OBL (final : list shob) (E : env) (m : word -> option byte) : Prop :=
forall o, dom final o -> sv_atoms_lt K (ob_x o) = true -> ob_span E o -> ob_holds E m o.
Definition static_sem (E : env) (rs : smem) : Prop :=
(forall x, in_wrange E rs x -> ~ (fst Bspan <= x <= snd Bspan))
/\ (forall e, In e SH -> she_lo e < she_hi e ->
she_lo e < she_hi e /\ 0 <= U E (SOff (she_m e) 0) + she_lo e /\ U E (SOff (she_m e) 0) + she_hi e < M64
/\ (forall c, she_lo e <= c < she_hi e -> fst Bspan <= cell_of E e c <= snd Bspan))
/\ (0 < K)%nat /\ (0 <= fst Bspan /\ snd Bspan < M64).
Lemma dom_le : forall final x n n', dom final (mkOB x n') -> n <= n' -> dom final (mkOB x n).
Proof. intros final x n n' (o' & Hin & Hx & Hn) Hle. exists o'. cbn in *. repeat split; auto. lia. Qed.
Lemma doml_refl : forall l, doml l l.
Proof. intros l o Hin. exists o. repeat split; auto. lia. Qed.
Lemma doml_trans : forall l1 l2 l3, doml l1 l2 -> doml l2 l3 -> doml l1 l3.
Proof.
intros l1 l2 l3 H12 H23 o Hin. destruct (H12 o Hin) as (o2 & Hin2 & Hx2 & Hn2).
destruct (H23 o2 Hin2) as (o3 & Hin3 & Hx3 & Hn3). exists o3. repeat split; auto; [congruence | lia].
Qed.
Lemma add_ob_doml : forall x n l, doml l (add_ob x n l).
Proof.
intros x n l o Hin. unfold add_ob.
destruct (existsb (fun o0 => sv_eqb (ob_x o0) x && (n <=? ob_n o0)) l); [exists o; repeat split; auto; lia|].
destruct (sv_eqb (ob_x o) x && (ob_n o <=? n)) eqn:Hb.
- apply andb_prop in Hb as [H1 H2]. apply sv_eqb_eq in H1. apply Z.leb_le in H2.
exists (mkOB x n). split; [left; reflexivity|]. cbn. auto.
- exists o. split; [|repeat split; auto; lia]. right. apply filter_In. split; [exact Hin|]. rewrite Hb. reflexivity.
Qed.
Lemma add_ob_new : forall x n l final, doml (add_ob x n l) final -> dom final (mkOB x n).
Proof.
intros x n l final H. unfold add_ob in H.
destruct (existsb (fun o0 => sv_eqb (ob_x o0) x && (n <=? ob_n o0)) l) eqn:Hex.
- apply existsb_exists in Hex as (o0 & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply sv_eqb_eq in H1. apply Z.leb_le in H2.
destruct (H o0 Hin) as (o' & Hin' & Hx' & Hn'). exists o'. cbn. repeat split; auto; [congruence | lia].
- apply H. left. reflexivity.
Qed.
Lemma need_doml : forall G x n obls obls', need G x n obls = Some obls' -> doml obls obls'.
Proof.
intros G x n obls obls' H. unfold YCbn.need in H.
destruct (covered x n); [injection H as <-; apply doml_refl|].
destruct (sv_atoms_lt K x && ob_in_span Bx Bspan G x n); [|discriminate].
injection H as <-. apply add_ob_doml.
Qed.
Lemma sv_urange_sound : forall E G v lo hi,
facts_ok E G -> sv_urange G v = Some (lo, hi) -> lo <= U E v <= hi.
Proof.
intros E G v lo hi HG H. pose proof (sv_ranges_sound E G v HG) as [Hu _].
unfold sv_urange in H. rewrite H in Hu. exact Hu.
Qed.
Lemma window_itv_sound : forall E G rs r x,
facts_ok E G -> In r rs -> regions_wf rs = true ->
base_val E (r_base r) + r_wlo r <= x < base_val E (r_base r) + r_whi r ->
exists i lo hi, window_itv G r = Some i /\ (i = Some (lo, hi) -> lo <= x <= hi) /\ (i = None -> True)
/\ (forall l h, i = Some (l, h) -> l <= x <= h).
Proof.
intros E G rs r x HG Hin Hwf Hx. unfold window_itv.
destruct (r_whi r <=? r_wlo r) eqn:He; [apply Z.leb_le in He; lia|].
destruct (r_base r) as [n|] eqn:Hb; cbn [base_val] in Hx.
- destruct (sv_urange G (SOff n 0)) as [[bl bh]|] eqn:Hr.
+ pose proof (sv_urange_sound E G _ _ _ HG Hr) as Hb2. rewrite U_SOff, Z.add_0_r in Hb2.
pose proof (bv_unsigned_in_range 64 (ew E n)) as Hrg. change (bv_modulus 64) with M64 in Hrg.
rewrite zcanon_id in Hb2 by lia.
eexists; exists (bl + r_wlo r), (bh + r_whi r - 1). split; [reflexivity|]. split; [intros _; lia|]. split; [auto|].
intros l h Hlh. injection Hlh as <- <-. lia.
+ eexists; exists 0, 0. split; [reflexivity|]. split; [discriminate|]. split; [auto|]. intros l h Hlh; discriminate.
- eexists; exists (r_wlo r), (r_whi r - 1). split; [reflexivity|]. split; [intros _; lia|]. split; [auto|].
intros l h Hlh. injection Hlh as <- <-. lia.
Qed.
Lemma cells_safe_sound : forall E G rs mem x,
facts_ok E G -> regions_wf rs = true -> cells_safe_b Bx Bspan SH G rs = true ->
sh_ok E mem ->
in_wrange E rs x -> ~ (fst Bspan <= x <= snd Bspan).
Proof.
intros E G rs mem x HG Hwf Hc Hsh (r & Hin & Hx) Hsp.
unfold cells_safe_b in Hc. rewrite forallb_forall in Hc. specialize (Hc r Hin).
destruct (window_itv_sound E G rs r x HG Hin Hwf Hx) as (i & lo & hi & Hw & _ & _ & Hi).
rewrite Hw in Hc. apply orb_prop in Hc as [Hc|Hcov].
- destruct i as [[l h]|]; [|discriminate].
specialize (Hi l h eq_refl). unfold itv_disjoint in Hc. destruct Bspan as [Bl Bh]. cbn [fst snd] in *.
apply orb_prop in Hc as [Hc|Hc]; apply Z.ltb_lt in Hc; lia.
-
apply andb_prop in Hcov as [Hcov Hband].
unfold window_covered in Hcov. destruct (r_base r) as [n|] eqn:Hb; [|discriminate].
apply existsb_exists in Hcov as (e & Hein & Hce). apply andb_prop in Hce as [Hce H3]. apply andb_prop in Hce as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
unfold sh_ok in Hsh. rewrite Forall_forall in Hsh. destruct (Hsh e Hein) as [_ Happ].
unfold span_in_band in Hband. destruct (sv_urange G Bx) as [[Bl Bh]|] eqn:HB; [|discriminate].
pose proof (sv_urange_sound E G _ _ _ HG HB) as HB2.
apply andb_prop in Hband as [Hband Hb3]. apply andb_prop in Hband as [Hb1 Hb2].
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3.
cbn [base_val] in Hx.
apply (Happ x); [|lia]. rewrite H1, U_SOff, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E n)) as Hrg. change (bv_modulus 64) with M64 in Hrg.
rewrite zcanon_id by lia. clear - Hx H2 H3. lia.
Qed.
Lemma shent_in_span_sound : forall E G e,
facts_ok E G -> shent_in_span Bx Bspan G e = true -> she_lo e < she_hi e ->
she_lo e < she_hi e /\ 0 <= U E (SOff (she_m e) 0) + she_lo e /\ U E (SOff (she_m e) 0) + she_hi e < M64
/\ (forall c, she_lo e <= c < she_hi e -> fst Bspan <= cell_of E e c <= snd Bspan).
Proof.
intros E G e HG H Hlt. unfold shent_in_span in H.
apply orb_prop in H as [H|H]; [apply Z.leb_le in H; lia|].
destruct (sv_urange G Bx) as [[Bl Bh]|] eqn:HB; [|discriminate].
destruct (sv_urange G (SOff (she_m e) 0)) as [[ml mh]|] eqn:Hm; [|discriminate].
pose proof (sv_urange_sound E G _ _ _ HG HB) as HB2. pose proof (sv_urange_sound E G _ _ _ HG Hm) as Hm2.
apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
apply Z.leb_le in H5. apply Z.leb_le in H6.
split; [exact H2|]. split; [lia|]. split; [lia|].
intros c Hc. unfold cell_of. destruct Bspan as [Sl Sh]. cbn [fst snd] in *.
assert (Hlo : (ml + she_lo e) / 8 <= (U E (SOff (she_m e) 0) + c) / 8) by (apply Z.div_le_mono; lia).
assert (Hhi : (U E (SOff (she_m e) 0) + c) / 8 <= (mh + she_hi e - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma static_sound : forall E ss mem,
facts_ok E (ss_facts ss) -> regions_wf (ss_mem ss) = true ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sh_ok E mem ->
static_sem E (ss_mem ss).
Proof.
intros E ss mem HG Hwf H Hsh. unfold sh_static_ok in H. apply andb_prop in H as [H _].
apply andb_prop in H as [H Hsp]. apply andb_prop in H as [H HK]. apply andb_prop in H as [Hc He].
apply andb_prop in Hsp as [Hs1 Hs2]. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
split; [|split; [|split]].
- intros x Hin. exact (cells_safe_sound E _ _ mem x HG Hwf Hc Hsh Hin).
- intros e Hin Hlt. rewrite forallb_forall in He. exact (shent_in_span_sound E _ e HG (He e Hin) Hlt).
- apply Nat.ltb_lt in HK. exact HK.
- lia.
Qed.
Lemma sv_atoms_lt_mono : forall k k' v, (k <= k')%nat -> sv_atoms_lt k v = true -> sv_atoms_lt k' v = true.
Proof.
intros k k' v Hk. induction v; cbn; intros H; try reflexivity;
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end;
rewrite ?IHv, ?IHv1, ?IHv2, ?IHv3 by assumption; try reflexivity.
apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
Lemma sh_atoms_lt_mono : forall k k', (k <= k')%nat -> sh_atoms_lt k = true -> sh_atoms_lt k' = true.
Proof.
intros k k' Hk H. unfold sh_atoms_ltb in *. apply andb_prop in H as [HB He].
rewrite (sv_atoms_lt_mono k k' Bx Hk HB). cbn. rewrite forallb_forall in He |- *.
intros e Hin. specialize (He e Hin). apply Nat.ltb_lt in He. apply Nat.ltb_lt. lia.
Qed.
Lemma st_ok_setreg : forall E ss regs pc mem rd (e : sv) v pc',
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> ss_resv ss = None ->
sv_denot E e = v ->
st_ok segs E (setreg ss rd e pc')
(mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (Z_to_bv 64 pc') mem (seg_rom segs)).
Proof.
intros E ss regs pc mem rd e v pc' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hrv Hev.
unfold st_ok, setreg; cbn. rewrite Hrv. cbn. repeat (split; [reflexivity|]).
split; [apply regs_ok_set; assumption|]. split; assumption.
Qed.
Lemma v_lb_zero : forall b : byte, bv_unsigned b = 0 -> v_lb b = Z_to_bv 64 0.
Proof.
intros b Hb. unfold v_lb. f_equal. unfold bv_signed. rewrite Hb. reflexivity.
Qed.
Definition cellval (sg : bool) (b : byte) : word := if sg then v_lb b else Z_to_bv 64 (bv_unsigned b).
Lemma ob_in_span_sound : forall E G x n,
facts_ok E G -> ob_in_span Bx Bspan G x n = true -> 0 < n /\ ob_span E (mkOB x n).
Proof.
intros E G x n HG H. unfold ob_in_span in H.
destruct (sv_urange G Bx) as [[Bl Bh]|] eqn:HB; [|discriminate].
destruct (sv_urange G x) as [[xl xh]|] eqn:Hx; [|discriminate].
pose proof (sv_urange_sound E G _ _ _ HG HB) as HB2. pose proof (sv_urange_sound E G _ _ _ HG Hx) as Hx2.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
split; [exact H1|]. intros i Hi. cbn in Hi |- *. destruct Bspan as [Sl Sh]. cbn [fst snd] in *.
assert (Hlo : xl / 8 <= (U E x + i) / 8) by (apply Z.div_le_mono; lia).
assert (Hhi : (U E x + i) / 8 <= (xh + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma mbyte_frame_span : forall E rs m m' z,
static_sem E rs -> fst Bspan <= z <= snd Bspan ->
frame_of E rs m m' -> mbyte segs m' z = mbyte segs m z.
Proof.
intros E rs m m' z (Hw & _ & _ & Hsp) Hz HF. unfold mbyte.
rewrite (HF (Z_to_bv 64 z)); [reflexivity|].
intros Hwr. apply (Hw _ Hwr). rewrite unsigned_lit_small; [exact Hz | unfold M64 in Hsp; lia].
Qed.
Lemma mbyte_frame_cell : forall E rs m m' e c,
static_sem E rs -> In e SH -> she_lo e <= c < she_hi e ->
frame_of E rs m m' -> mbyte segs m' (cell_of E e c) = mbyte segs m (cell_of E e c).
Proof.
intros E rs m m' e c Hst Hin Hc HF. apply (mbyte_frame_span E rs m m' _ Hst); [|exact HF].
destruct Hst as (_ & He & _). destruct (He e Hin ltac:(lia)) as (_ & _ & _ & Hcell). exact (Hcell c Hc).
Qed.
Lemma shent_ok_frame : forall E rs m m' e,
static_sem E rs -> In e SH -> frame_of E rs m m' -> shent_ok E m e -> shent_ok E m' e.
Proof.
intros E rs m m' e Hst Hin HF [He Happ]. unfold shent_ok in *. split; [|exact Happ].
eapply range_addressable_agree; [|exact He]. intros x Hx.
unfold rd_of, shadow_of_addr.
replace (U E Bx + x / 8) with (cell_of E e (x - U E (SOff (she_m e) 0))).
2:{ unfold cell_of. f_equal. f_equal. lia. }
rewrite (mbyte_frame_cell E rs m m' e (x - U E (SOff (she_m e) 0)) Hst Hin ltac:(lia) HF). reflexivity.
Qed.
Lemma sh_ok_frame : forall E rs m m',
static_sem E rs -> frame_of E rs m m' -> sh_ok E m -> sh_ok E m'.
Proof.
intros E rs m m' Hst HF H. unfold sh_ok in *. rewrite Forall_forall in H |- *.
intros e Hin. exact (shent_ok_frame E rs m m' e Hst Hin HF (H e Hin)).
Qed.
Lemma tok_ok_frame : forall E rs m m' tk,
static_sem E rs -> frame_of E rs m m' -> tok_ok E m tk -> tok_ok E m' tk.
Proof.
intros E rs m m' tk Hst HF (Hat & Hsp & b & Hb & Hv). split; [exact Hat|]. split; [exact Hsp|].
exists b. split; [|exact Hv]. rewrite (mbyte_frame_span E rs m m' _ Hst Hsp HF). exact Hb.
Qed.
Lemma ob_holds_frame : forall E rs m m' o,
static_sem E rs -> frame_of E rs m m' -> ob_span E o -> ob_holds E m o -> ob_holds E m' o.
Proof.
intros E rs m m' o Hst HF Hsp H. unfold ob_holds in *.
eapply range_addressable_agree; [|exact H]. intros x Hx. unfold rd_of, shadow_of_addr.
rewrite (mbyte_frame_span E rs m m' _ Hst); [reflexivity| |exact HF].
specialize (Hsp (x - U E (ob_x o)) ltac:(lia)). replace (U E (ob_x o) + (x - U E (ob_x o))) with x in Hsp by lia.
exact Hsp.
Qed.
Lemma OBL_frame : forall final E rs m m',
static_sem E rs -> frame_of E rs m m' -> OBL final E m -> OBL final E m'.
Proof.
intros final E rs m m' Hst HF H o Hd Hat Hsp. exact (ob_holds_frame E rs m m' o Hst HF Hsp (H o Hd Hat Hsp)).
Qed.
Lemma U_agree : forall k E E' v, env_agree k E E' -> sv_atoms_lt k v = true -> U E' v = U E v.
Proof. intros k E E' v HA Hv. unfold U. rewrite (sv_denot_agree k E E' v HA Hv). reflexivity. Qed.
Lemma cell_of_agree : forall k E E' e c,
env_agree k E E' -> sh_atoms_lt k = true -> In e SH -> cell_of E' e c = cell_of E e c.
Proof.
intros k E E' e c HA Hk Hin. unfold sh_atoms_lt in Hk. apply andb_prop in Hk as [HB He].
rewrite forallb_forall in He. specialize (He e Hin). unfold cell_of.
rewrite (U_agree k E E' Bx HA HB). rewrite (U_agree k E E' (SOff (she_m e) 0) HA); [reflexivity|].
cbn. exact He.
Qed.
Lemma cell_x_agree : forall k E E' x,
env_agree k E E' -> sh_atoms_lt k = true -> sv_atoms_lt k x = true -> cell_x E' x = cell_x E x.
Proof.
intros k E E' x HA Hk Hx. unfold sh_atoms_lt in Hk. apply andb_prop in Hk as [HB _]. unfold cell_x.
rewrite (U_agree k E E' Bx HA HB), (U_agree k E E' x HA Hx). reflexivity.
Qed.
Lemma shent_ok_agree : forall k E E' m e,
env_agree k E E' -> sh_atoms_lt k = true -> In e SH -> shent_ok E m e -> shent_ok E' m e.
Proof.
intros k E E' m e HA Hk Hin H. unfold shent_ok, app_apart in *.
unfold sh_atoms_lt in Hk. apply andb_prop in Hk as [HB He]. rewrite forallb_forall in He.
rewrite (U_agree k E E' Bx HA HB). rewrite (U_agree k E E' (SOff (she_m e) 0) HA); [exact H|]. cbn. exact (He e Hin).
Qed.
Lemma sh_ok_agree : forall k E E' m,
env_agree k E E' -> sh_atoms_lt k = true -> sh_ok E m -> sh_ok E' m.
Proof.
intros k E E' m HA Hk H. unfold sh_ok in *. rewrite Forall_forall in H |- *.
intros e Hin. exact (shent_ok_agree k E E' m e HA Hk Hin (H e Hin)).
Qed.
Lemma static_sem_agree : forall k E E' rs,
env_agree k E E' -> sh_atoms_lt k = true -> mem_atoms_lt k rs = true ->
static_sem E rs -> static_sem E' rs.
Proof.
intros k E E' rs HA Hk Hrs (Hw & He & HK & Hsp). split; [|split; [|split; [exact HK|exact Hsp]]].
- intros x (r & Hin & Hr). apply (Hw x). exists r. split; [exact Hin|].
unfold mem_atoms_lt in Hrs. rewrite forallb_forall in Hrs. specialize (Hrs r Hin).
unfold region_atoms_lt in Hrs. apply andb_prop in Hrs as [Hb _].
rewrite <- (base_val_agree k E E' _ HA Hb). exact Hr.
- intros e Hin Hlt. destruct (He e Hin Hlt) as (H1 & H2 & H3 & H4).
unfold sh_atoms_lt in Hk. apply andb_prop in Hk as [HB Hes]. rewrite forallb_forall in Hes.
assert (Hm : U E' (SOff (she_m e) 0) = U E (SOff (she_m e) 0)).
{ apply (U_agree k); [exact HA|]. cbn. exact (Hes e Hin). }
rewrite Hm. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
intros c Hc. rewrite (cell_of_agree k E E' e c HA); [exact (H4 c Hc)| |exact Hin].
unfold sh_atoms_lt. rewrite HB. cbn. rewrite forallb_forall. exact Hes.
Qed.
Lemma tok_ok_agree : forall k E E' m tk,
env_agree k E E' -> (K <= k)%nat -> sh_atoms_lt k = true -> (tk_T tk < k)%nat -> tok_ok E m tk -> tok_ok E' m tk.
Proof.
intros k E E' m tk HA HK Hk HT (Hat & Hsp & b & Hb & Hv).
assert (Hxk : sv_atoms_lt k (tk_x tk) = true) by (apply (sv_atoms_lt_mono K); [exact HK | exact Hat]).
split; [exact Hat|]. rewrite (cell_x_agree k E E' _ HA Hk Hxk). split; [exact Hsp|].
exists b. split; [exact Hb|]. destruct HA as [HA _]. rewrite (HA _ HT). exact Hv.
Qed.
Lemma ob_span_agree : forall k E E' o,
env_agree k E E' -> (K <= k)%nat -> sh_atoms_lt k = true -> sv_atoms_lt K (ob_x o) = true ->
ob_span E' o <-> ob_span E o.
Proof.
intros k E E' o HA HK Hk Hat. unfold ob_span.
unfold sh_atoms_lt in Hk. apply andb_prop in Hk as [HB _].
rewrite (U_agree k E E' Bx HA HB), (U_agree k E E' (ob_x o) HA); [reflexivity|].
apply (sv_atoms_lt_mono K); [exact HK | exact Hat].
Qed.
Lemma ob_holds_agree : forall k E E' m o,
env_agree k E E' -> (K <= k)%nat -> sh_atoms_lt k = true -> sv_atoms_lt K (ob_x o) = true ->
ob_holds E m o -> ob_holds E' m o.
Proof.
intros k E E' m o HA HK Hk Hat H. unfold ob_holds in *.
unfold sh_atoms_lt in Hk. apply andb_prop in Hk as [HB _].
rewrite (U_agree k E E' Bx HA HB), (U_agree k E E' (ob_x o) HA); [exact H|].
apply (sv_atoms_lt_mono K); [exact HK | exact Hat].
Qed.
Lemma OBL_agree : forall final k E E' m,
env_agree k E E' -> (K <= k)%nat -> sh_atoms_lt k = true -> OBL final E m -> OBL final E' m.
Proof.
intros final k E E' m HA HK Hk H o Hd Hat Hsp.
apply (ob_holds_agree k E E' m o HA HK Hk Hat). apply (H o Hd Hat).
apply (proj1 (ob_span_agree k E E' o HA HK Hk Hat)). exact Hsp.
Qed.
Definition INV (final : list shob) (E : env) (st : shst) (ms : machine_state) : Prop :=
st_ok segs E (sh_ss st) ms
/\ Forall (fun tk => (tk_T tk < K + sh_j st)%nat) (sh_toks st)
/\ (sh_chk st = true ->
static_sem E (ss_mem (sh_ss st)) /\ sh_atoms_lt K = true
/\ sh_ok E (ms_mem ms) /\ Forall (tok_ok E (ms_mem ms)) (sh_toks st)
/\ OBL final E (ms_mem ms))
/\ (sh_chk st = false -> sh_toks st = []).
Lemma Forall_filter' : forall {A} (P : A -> Prop) f (l : list A), Forall P l -> Forall P (List.filter f l).
Proof. intros A P f l H. induction H; cbn; [constructor|]. destruct (f x); [constructor; assumption | assumption]. Qed.
Lemma static_sem_skeleton : forall E rs rs',
skeleton rs' = skeleton rs -> static_sem E rs -> static_sem E rs'.
Proof.
intros E rs rs' Hsk (Hw & He & HK & Hsp). split; [|split; [exact He | split; [exact HK | exact Hsp]]].
intros x Hin. apply Hw. exact (in_wrange_skeleton E rs' rs x Hsk Hin).
Qed.
Lemma advance_sound : forall final E st ss' ms ms',
INV final E st ms ->
st_ok segs E ss' ms' ->
skeleton (ss_mem ss') = skeleton (ss_mem (sh_ss st)) ->
frame_of E (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms') ->
INV final E (advance st ss') ms'.
Proof.
intros final E st ss' ms ms' (HS & HT & HC & HN) HS' Hsk HF. unfold advance, INV; cbn.
split; [exact HS'|]. split; [apply Forall_filter'; exact HT|]. split.
- intros Hchk. destruct (HC Hchk) as (Hst & Hat & Hsh & Htk & Hob).
split; [exact (static_sem_skeleton E _ _ Hsk Hst)|]. split; [exact Hat|]. split; [|split].
+ exact (sh_ok_frame E _ _ _ Hst HF Hsh).
+ apply Forall_filter'. rewrite Forall_forall in Htk |- *. intros tk Hin.
exact (tok_ok_frame E _ _ _ tk Hst HF (Htk tk Hin)).
+ exact (OBL_frame final E _ _ _ Hst HF Hob).
- intros Hchk. rewrite (HN Hchk). reflexivity.
Qed.
Lemma srl3_any_U : forall E v x, srl3_any v = Some x -> U E v = U E x / 8.
Proof.
intros E v x H. unfold srl3_any in H.
destruct v as [| | op u w | | | | | | | |]; try discriminate. destruct op; try discriminate.
destruct w as [k| | | | | | | | | |]; try discriminate.
destruct (k =? 3) eqn:Hk; [|discriminate]. apply Z.eqb_eq in Hk. injection H as <-. subst k. apply U_srl3.
Qed.
Lemma match_x_core_denot : forall E v x,
match_x_core Bx v = Some x -> Z_to_bv 64 (U E v) = Z_to_bv 64 (cell_x E x).
Proof.
intros E v x H. unfold match_x_core in H. unfold cell_x.
destruct v as [| | op u w | | | | | | | |]; try discriminate. destruct op; try discriminate.
destruct (srl3_any u) as [x'|] eqn:Hu.
- destruct (sv_eqb w Bx) eqn:Hw; [|discriminate]. injection H as ->. apply sv_eqb_eq in Hw. subst w.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (srl3_any_U E u x Hu), Z_to_bv64_canon. f_equal. lia.
- destruct (srl3_any w) as [x'|] eqn:Hw; [|discriminate].
destruct (sv_eqb u Bx) eqn:Hu2; [|discriminate]. injection H as ->. apply sv_eqb_eq in Hu2. subst u.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (srl3_any_U E w x Hw), Z_to_bv64_canon. reflexivity.
Qed.
Lemma match_x_denot : forall E a x,
match_x Bx a = Some x -> sv_denot E a = Z_to_bv 64 (cell_x E x).
Proof.
intros E a x H. rewrite denot_lit_U. unfold match_x in H.
destruct (match_x_core Bx a) as [x0|] eqn:Hc.
- injection H as ->. exact (match_x_core_denot E a x Hc).
- destruct a as [| | op v w | | | | | | | |]; try discriminate. destruct op; try discriminate.
destruct w as [z| | | | | | | | | |]; try discriminate.
destruct (zcanon z =? 0) eqn:Hz; [|discriminate]. apply Z.eqb_eq in Hz.
rewrite U_SAlu, U_SLit. cbn [zalu_raw]. rewrite Hz, Z.add_0_r, Z_to_bv64_canon.
exact (match_x_core_denot E v x H).
Qed.
Lemma find_shent_sound : forall l i m c j e,
find_shent l i m c = Some (j, e) ->
nth_error l (j - i) = Some e /\ (i <= j)%nat /\ she_m e = m /\ she_lo e <= c < she_hi e.
Proof.
induction l as [|e0 l IH]; intros i m c j e H; cbn in H; [discriminate|].
destruct ((she_m e0 =? m)%nat && (she_lo e0 <=? c) && (c <? she_hi e0)) eqn:Hb.
- injection H as <- <-. rewrite Nat.sub_diag. cbn.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Nat.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. repeat split; auto; lia.
- destruct (IH _ _ _ _ _ H) as (Hn & Hij & Hm & Hc).
replace (j - i)%nat with (S (j - S i))%nat by lia. cbn [nth_error].
split; [exact Hn|]. split; [lia|]. split; [exact Hm | exact Hc].
Qed.
Lemma covered_sound : forall x n, covered x n = true ->
exists m c e, x = SOff m c /\ In e SH /\ she_m e = m /\ she_lo e <= c < she_hi e /\ c + n <= she_hi e.
Proof.
intros x n H. unfold YCbn.covered in H. destruct x as [|m c| | | | | | | | |]; try discriminate.
destruct (find_shent SH 0 m c) as [[i e]|] eqn:Hf; [|discriminate]. apply Z.leb_le in H.
destruct (find_shent_sound _ _ _ _ _ _ Hf) as (Hnth & _ & Hm & Hc). rewrite Nat.sub_0_r in Hnth.
exists m, c, e. split; [reflexivity|]. split; [exact (nth_error_In _ _ Hnth)|]. auto.
Qed.
Lemma entry_sem : forall E rs mem m c e n,
static_sem E rs -> sh_ok E mem -> In e SH -> she_m e = m -> she_lo e <= c < she_hi e -> c + n <= she_hi e ->
U E (SOff m c) = U E (SOff m 0) + c
/\ range_addressable (rd_of mem) (U E Bx) (U E (SOff m c)) n
/\ (forall i, 0 <= i < n -> fst Bspan <= U E Bx + (U E (SOff m c) + i) / 8 <= snd Bspan).
Proof.
intros E rs mem m c e n (_ & Hents & _ & _) Hsh Hin Hm Hc Hn. subst m.
destruct (Hents e Hin ltac:(lia)) as (H1 & H2 & H3 & Hcell).
assert (HU : U E (SOff (she_m e) c) = U E (SOff (she_m e) 0) + c).
{ pose proof (bv_unsigned_in_range 64 (ew E (she_m e))) as Hr. change (bv_modulus 64) with M64 in Hr.
assert (H0 : U E (SOff (she_m e) 0) = bv_unsigned (ew E (she_m e))) by (rewrite U_SOff, Z.add_0_r; apply zcanon_id; lia).
rewrite H0 in H2, H3 |- *. rewrite U_SOff. apply zcanon_id. lia. }
rewrite HU. split; [reflexivity|]. split.
- unfold sh_ok in Hsh. rewrite Forall_forall in Hsh. specialize (Hsh e Hin). unfold shent_ok in Hsh. destruct Hsh as [Hsh _].
eapply range_addressable_sub; [exact Hsh | lia | lia].
- intros i Hi. specialize (Hcell (c + i) ltac:(lia)). unfold cell_of in Hcell.
replace (U E (SOff (she_m e) 0) + c + i) with (U E (SOff (she_m e) 0) + (c + i)) by lia. exact Hcell.
Qed.
Lemma need_sound : forall final E rs mem G x n obls obls',
static_sem E rs -> sh_ok E mem -> OBL final E mem -> facts_ok E G ->
need G x n obls = Some obls' -> doml obls' final -> 0 < n ->
range_addressable (rd_of mem) (U E Bx) (U E x) n
/\ (forall i, 0 <= i < n -> fst Bspan <= U E Bx + (U E x + i) / 8 <= snd Bspan).
Proof.
intros final E rs mem G x n obls obls' Hst Hsh Hob HG H Hdom Hn. unfold YCbn.need in H.
destruct (covered x n) eqn:Hcov.
- injection H as <-. destruct (covered_sound x n Hcov) as (m & c & e & -> & Hin & Hm & Hc & Hcn).
destruct (entry_sem E rs mem m c e n Hst Hsh Hin Hm Hc Hcn) as (_ & HRA & Hsp). auto.
- destruct (sv_atoms_lt K x && ob_in_span Bx Bspan G x n) eqn:Hb; [|discriminate]. injection H as <-.
apply andb_prop in Hb as [Hat Hspan].
destruct (ob_in_span_sound E G x n HG Hspan) as [_ Hsp].
split; [|exact Hsp]. apply (Hob (mkOB x n)); [exact (add_ob_new x n obls final Hdom) | exact Hat | exact Hsp].
Qed.
Lemma gran_val : forall E G x, facts_ok E G ->
U E (gran G x) = U E x \/ (U E (gran G x) = 8 * (U E x / 8) /\ U E (gran G x) <= U E x).
Proof.
intros E G x HG. unfold gran. destruct x as [|m c| | | | | | | | |]; try (left; reflexivity).
destruct (atom_lookup (f_atoms G) m) as [f|] eqn:Hl; [|left; reflexivity].
destruct ((3 <=? af_al2 f) && (af_al2 f <=? 64) && (0 <=? af_lo f) && (0 <=? c - c mod 8) && (af_hi f + c <? M64)) eqn:Hb; [|left; reflexivity].
right. repeat (apply andb_prop in Hb as [Hb ?]).
apply Z.leb_le in Hb. repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hl) as (Hlohi & Hal & Hal2).
set (v := bv_unsigned (ew E m)) in *.
assert (Hv8 : v mod 8 = 0).
{ destruct (proj1 (Z.mod_divide v (2 ^ af_al2 f) ltac:(apply Z.pow_nonzero; lia)) Hal) as [k Hk].
rewrite Hk. replace (2 ^ af_al2 f) with (2 ^ (af_al2 f - 3) * 8) by (change 8 with (2 ^ 3); rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hc8. pose proof (Z.div_mod c 8 ltac:(lia)) as Hcd.
pose proof (Z.div_mod v 8 ltac:(lia)) as Hvd.
rewrite !U_SOff. fold v. unfold M64 in *.
assert (E1 : zcanon (v + (c - c mod 8)) = v + (c - c mod 8)) by (apply zcanon_id; unfold M64; lia).
assert (E2 : zcanon (v + c) = v + c) by (apply zcanon_id; unfold M64; lia).
rewrite E1, E2.
assert (Hq : (v + c) / 8 = v / 8 + c / 8).
{ symmetry. apply (Z.div_unique_pos (v + c) 8 (v / 8 + c / 8) (c mod 8)); lia. }
rewrite Hq. lia.
Qed.
Lemma cell_byte : forall E mem x n,
range_addressable (rd_of mem) (U E Bx) (U E x) n -> 0 < n ->
exists b s, mbyte segs mem (cell_x E x) = Some b /\ bv_unsigned b = s
/\ rd_of mem (shadow_of_addr (U E Bx) (U E x)) = Some s.
Proof.
intros E mem x n HRA Hn.
destruct (range_addressable_present (rd_of mem) (U E Bx) (U E x) n (U E x) HRA ltac:(lia)) as (s & Hs).
pose proof Hs as Hs0. unfold rd_of, shadow_of_addr in Hs. unfold cell_x.
destruct (mbyte segs mem (U E Bx + U E x / 8)) as [b|]; [|discriminate]. cbn in Hs. injection Hs as Hs.
exists b, s. auto.
Qed.
Lemma tok_load_sound : forall final E st sg rd rs1 imm st' ms w,
INV final E st ms ->
fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 sg rd rs1 imm, 4) ->
tok_load st sg rd (s_alu2 (ss_facts (sh_ss st)) ALU_ADD (sr_get (ss_regs (sh_ss st)) rs1) (SLit (bv_signed imm))) = Some st' ->
doml (sh_obls st') final ->
exists ms' E',
RiscvSemantics.step segs ms = MachineOk ms' /\ INV final E' st' ms'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ ss_mem (sh_ss st') = ss_mem (sh_ss st) /\ ms_mem ms' = ms_mem ms /\ ss_facts (sh_ss st') = ss_facts (sh_ss st).
Proof.
intros final E st sg rd rs1 imm st' ms w HI Hf He Hd H Hdom.
destruct st as [ss j toks chk obls]. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
destruct HI as (HS & HT & HC & HN). cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
unfold tok_load in H. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in H.
destruct (bv_eqb rd 0) eqn:Hrd0; [discriminate|].
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (match_x Bx a) as [x|] eqn:Hmx; [|discriminate].
destruct chk; [|discriminate]. cbn [negb] in H.
destruct (ss_resv ss) as [rv|] eqn:Hrv; [discriminate|].
destruct (HC eq_refl) as (Hst & Hat & Hsh & Htk & Hob).
pose proof Hst as (Hwin & Hents & HK & Hspan).
pose proof HS as HS0. destruct HS as (_ & Hpc & _ & _ & _ & _ & Hregs & Hmem & HG).
pose proof (st_ok_mkst segs E ss ms HS0 Hrv) as Hshape.
assert (Haddr : v_addi (getr (ms_regs ms) rs1) (bv_signed imm) = Z_to_bv 64 (cell_x E x)).
{ unfold v_addi. transitivity (sv_denot E a).
- subst a. rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite (Hregs rs1).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (sr_get (ss_regs ss) rs1))) at 2.
rewrite zalu64_sound. apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
rewrite Z.mod_mod by lia. pose proof (bv_unsigned_in_range 64 (sv_denot E (sr_get (ss_regs ss) rs1))) as Hr.
change (bv_modulus 64) with (2 ^ 64) in Hr. rewrite (Z.mod_small (bv_unsigned _)) by lia.
rewrite Z.add_mod_idemp_r by lia. reflexivity.
- exact (match_x_denot E a x Hmx). }
assert (Hpc4 : v_addi (Z_to_bv 64 (ss_pc ss)) 4 = Z_to_bv 64 (ss_pc ss + 4)).
{ unfold v_addi. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity. }
rewrite Hshape in Hf. cbn [ms_pc_val mkst] in Hf.
assert (STEP : forall b, mbyte segs (ms_mem ms) (cell_x E x) = Some b ->
RiscvSemantics.step segs ms =
MachineOk (mkst (if bv_eqb rd 0 then ms_regs ms else regupd (ms_regs ms) rd (cellval sg b))
(Z_to_bv 64 (ss_pc ss + 4)) (ms_mem ms) (seg_rom segs))).
{ intros b Hb.
assert (Hrdn : rdn segs (ms_mem ms) (v_addi (getr (ms_regs ms) rs1) (bv_signed imm)) 1 = Some [b]).
{ rewrite Haddr. apply (proj2 (rdn_mbytes segs (ms_mem ms) 1 (cell_x E x) [b])).
split; [reflexivity|]. intros k Hk. destruct k; [|lia]. cbn. rewrite Z.add_0_r. exact Hb. }
rewrite Hshape at 1. rewrite <- Hpc4. unfold cellval.
destruct sg; [eapply step_lb | eapply step_lbu]; try exact Hf; try exact He; try exact Hd; exact Hrdn. }
destruct (covered x 8) eqn:Hcov8.
-
injection H as <-.
destruct (covered_sound x 8 Hcov8) as (m & c & e & -> & Hin & Hm & Hc & Hc8).
destruct (entry_sem E _ (ms_mem ms) m c e 8 Hst Hsh Hin Hm Hc Hc8) as (_ & HRA & _).
destruct (cell_byte E (ms_mem ms) (SOff m c) 8 HRA ltac:(lia)) as (b & s & Hb & Hbs & Hrds).
assert (Hs0 : s = 0).
{ apply (check_passes_whole (rd_of (ms_mem ms)) (U E Bx) (U E (SOff m c)) 8 (U E (SOff m c)) 8 s HRA);
[lia | lia | pose proof (Z.mul_div_le (U E (SOff m c)) 8 ltac:(lia)); lia | exact Hrds]. }
assert (Hval : cellval sg b = Z_to_bv 64 0).
{ rewrite Hs0 in Hbs. unfold cellval. destruct sg; [apply v_lb_zero; exact Hbs | rewrite Hbs; reflexivity]. }
specialize (STEP b Hb). rewrite Hval in STEP.
eexists. exists E. split; [exact STEP|]. split; [|split; [left; split; reflexivity | split; [reflexivity | split; reflexivity]]].
unfold INV; cbn [sh_ss sh_j sh_toks sh_chk sh_obls].
split; [|split; [apply Forall_filter'; exact HT|split; [|intros; discriminate]]].
+ rewrite Hshape in HS0. exact (st_ok_setreg E ss _ _ _ rd (SLit 0) (Z_to_bv 64 0) (ss_pc ss + 4) HS0 Hrv eq_refl).
+ intros _. split; [|split; [exact Hat| split; [exact Hsh | split; [apply Forall_filter'; exact Htk | exact Hob]]]].
exact Hst.
-
destruct (negb (ss_atoms_lt (K + j) ss) || negb (sv_atoms_lt K x)) eqn:Hal; [discriminate|].
apply orb_false_elim in Hal as [Hal Hxk]. apply negb_false_iff in Hal. apply negb_false_iff in Hxk.
destruct (need (ss_facts ss) x 1 obls) as [obls'|] eqn:Hneed; [|discriminate]. injection H as <-.
cbn [sh_obls] in Hdom.
destruct (need_sound final E _ (ms_mem ms) (ss_facts ss) x 1 obls obls' Hst Hsh Hob HG Hneed Hdom ltac:(lia)) as [HRA Hsp].
destruct (cell_byte E (ms_mem ms) x 1 HRA ltac:(lia)) as (b & s & Hb & Hbs & Hrds).
specialize (STEP b Hb).
set (T := (K + j)%nat) in *. set (v := cellval sg b) in *.
set (E' := ewset E T v).
assert (HA : env_agree T E E') by apply env_agree_ewset.
assert (HAK : env_agree K E E') by (eapply env_agree_le; [|exact HA]; lia).
assert (HTK : (K <= T)%nat) by lia.
eexists. exists E'. split; [exact STEP|].
split; [|split; [right; exists v; split; [reflexivity | split; [reflexivity | first [exact Hal | reflexivity]]] | split; [reflexivity | split; reflexivity]]].
unfold INV; cbn [sh_ss sh_j sh_toks sh_chk sh_obls].
assert (Hat' : sh_atoms_lt T = true) by (apply (sh_atoms_lt_mono K); [lia | exact Hat]).
split; [|split; [|split; [|intros; discriminate]]].
+ rewrite Hshape in HS0. pose proof (st_ok_agree segs T E E' ss _ HS0 HA Hal) as HS1.
apply (st_ok_setreg E' ss _ _ _ rd (SOff T 0) v (ss_pc ss + 4) HS1 Hrv).
cbn [sv_denot]. subst E'. rewrite ew_ewset_same, Z.add_0_r. apply Z_to_bv_bv_unsigned.
+ constructor; [cbn; lia|]. apply Forall_filter'. rewrite Forall_forall in HT |- *. intros tk Htk0. specialize (HT tk Htk0). lia.
+ intros _.
split; [|split; [exact Hat|split; [|split]]].
* eapply (static_sem_agree T E E'); [exact HA | exact Hat' | | exact Hst].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [_ Hm2]. exact Hm2.
* exact (sh_ok_agree T E E' _ HA Hat' Hsh).
* constructor.
-- split; [exact Hxk|]. cbn [tk_x tk_T tk_sg].
rewrite (cell_x_agree T E E' x HA Hat' (sv_atoms_lt_mono K T x HTK Hxk)).
split; [specialize (Hsp 0 ltac:(lia)); rewrite Z.add_0_r in Hsp; unfold cell_x; exact Hsp|].
exists b. split; [exact Hb|]. subst E'. rewrite ew_ewset_same. reflexivity.
-- apply Forall_filter'. rewrite Forall_forall in Htk, HT |- *. intros tk Htk0.
apply (tok_ok_agree T E E'); [exact HA | exact HTK | exact Hat' | exact (HT tk Htk0) | exact (Htk tk Htk0)].
* exact (OBL_agree final T E E' _ HA HTK Hat' Hob).
Qed.
Lemma dec_sound : forall pc i,
dec tbl pc = Some i ->
exists w, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4).
Proof.
intros pc i H. unfold dec in H.
destruct (clookup tbl pc) as [wz|] eqn:Hl; [|discriminate].
destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec; [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i' sz]|] eqn:Hd; [|discriminate].
destruct (sz =? 4) eqn:Hsz; [|discriminate]. injection H as <-. apply Z.eqb_eq in Hsz. subst sz.
exists (Z_to_bv 32 wz). split; [exact (Htbl pc wz Hl)|]. auto.
Qed.
Lemma decp_sound : forall {A} (f : instr -> option A) pc (x : A),
decp tbl f pc = Some x -> exists i, dec tbl pc = Some i /\ f i = Some x.
Proof.
intros A f pc x H. unfold decp in H. destruct (dec tbl pc) as [i|]; [|discriminate]. exists i. auto.
Qed.
Lemma as_andi_sound : forall i u xr z, as_andi i = Some (u, xr, z) -> exists imm, i = OpImm ALU_AND u xr imm /\ bv_signed imm = z.
Proof.
intros i u xr z H. destruct i; cbn in H; try discriminate.
match type of H with (match ?o with _ => _ end) = _ => destruct o; try discriminate end.
injection H as <- <- <-. eexists. split; reflexivity.
Qed.
Lemma as_addi_sound : forall i u1 u2 z, as_addi i = Some (u1, u2, z) -> exists imm, i = OpImm ALU_ADD u1 u2 imm /\ bv_signed imm = z.
Proof.
intros i u1 u2 z H. destruct i; cbn in H; try discriminate.
match type of H with (match ?o with _ => _ end) = _ => destruct o; try discriminate end.
injection H as <- <- <-. eexists. split; reflexivity.
Qed.
Lemma as_branch_sound : forall i c r1 r2 z, as_branch i = Some (c, r1, r2, z) -> exists off, i = Branch c r1 r2 off /\ bv_signed off = z.
Proof.
intros i c r1 r2 z H. destruct i; cbn in H; try discriminate.
injection H as <- <- <- <-. eexists. split; reflexivity.
Qed.
Lemma as_j_sound : forall i z, as_j i = Some z -> exists off, i = Jal 0 off /\ bv_signed off = z.
Proof.
intros i z H. destruct i; cbn in H; try discriminate.
match type of H with (if bv_eqb ?r 0 then _ else _) = _ => destruct (bv_eqb r 0) eqn:Hr; [|discriminate]; apply bv_eqb_eq in Hr; subst r end.
injection H as <-. eexists. split; reflexivity.
Qed.
Lemma v_addi_lit : forall pc k, v_addi (Z_to_bv 64 pc) k = Z_to_bv 64 (pc + k).
Proof.
intros pc k. unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_eq_mod.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.
Lemma btgt_lit : forall pc k, btgt (Z_to_bv 64 pc) k = Z_to_bv 64 (pc + k).
Proof. intros. unfold btgt. apply v_addi_lit. Qed.
Lemma zv_zcanon_eq : forall a b, zcanon a = zcanon b -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply Z_to_bv64_eq_mod. unfold zcanon, M64 in H. exact H. Qed.
Lemma alu_and7 : forall x, 0 <= x < M64 ->
alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 7) = Z_to_bv 64 (x mod 8).
Proof.
intros x Hx. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw]. rewrite Z_to_bv64_canon.
rewrite (zcanon_id x) by exact Hx. change (zcanon 7) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma alu_add_small : forall a k, 0 <= a -> 0 <= k -> a + k < M64 ->
alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a + k).
Proof.
intros a k Ha Hk Hs. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw]. rewrite Z_to_bv64_canon.
rewrite !zcanon_id by (unfold M64 in *; lia). reflexivity.
Qed.
Lemma bv_lts_small : forall a b, 0 <= a < 128 -> 0 <= b < 128 ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_id by (unfold M64; lia).
rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Lemma cellval_small : forall sg b s, bv_unsigned b = s -> 0 <= s < 128 -> cellval sg b = Z_to_bv 64 s.
Proof.
intros sg b s Hb Hs. unfold cellval, v_lb. destruct sg; [|rewrite Hb; reflexivity].
f_equal. unfold bv_signed. rewrite Hb. apply bv_swrap_small.
replace (bv_half_modulus 8) with 128 by reflexivity. lia.
Qed.
Lemma cellval_zero_iff : forall sg b, cellval sg b = Z_to_bv 64 0 <-> bv_unsigned b = 0.
Proof.
intros sg b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|intros H; rewrite (cellval_small sg b 0 H) by lia; reflexivity].
intros H. destruct sg; unfold cellval, v_lb in H; apply (f_equal bv_unsigned) in H;
rewrite !Z_to_bv_unsigned in H; unfold bv_wrap in H; change (bv_modulus 64) with (2 ^ 64) in H;
rewrite Z.mod_0_l in H by lia.
- unfold bv_signed, bv_swrap in H. replace (bv_half_modulus 8) with 128 in H by reflexivity.
unfold bv_wrap in H. change (bv_modulus 8) with 256 in H.
destruct (Z_lt_dec (bv_unsigned b) 128) as [Hl|Hl].
+ rewrite (Z.mod_small (bv_unsigned b + 128) 256) in H by lia. rewrite Z.mod_small in H; lia.
+ exfalso.
assert (H1 : (bv_unsigned b + 128) mod 256 = bv_unsigned b + 128 - 256).
{ rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
rewrite H1 in H.
assert (H2 : (bv_unsigned b + 128 - 256 - 128) mod 2 ^ 64 = bv_unsigned b - 256 + 2 ^ 64).
{ rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
rewrite H2 in H. lia.
- rewrite Z.mod_small in H; lia.
Qed.
Lemma andi_prefix_exec : forall L L2 (t u xr : reg) k regs mem x,
decp tbl as_andi L = Some (u, xr, 7) -> bv_eqb u 0 = false -> t <> u ->
((k = 0 /\ L2 = L + 4) \/ (decp tbl as_addi (L + 4) = Some (u, u, k) /\ L2 = L + 8)) ->
0 <= k <= 7 ->
getr regs xr = Z_to_bv 64 x -> 0 <= x < M64 ->
exists regs2, msteps segs (mkst regs (Z_to_bv 64 L) mem (seg_rom segs)) (mkst regs2 (Z_to_bv 64 L2) mem (seg_rom segs))
/\ getr regs2 u = Z_to_bv 64 (x mod 8 + k) /\ (forall r, r <> u -> getr regs2 r = getr regs r).
Proof.
intros L L2 t u xr k regs mem x HD0 Hu0 Hut Hk2 Hk Hxr Hx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hxm.
assert (Hune : u <> 0%bv) by (intros ->; rewrite bv_eqb_refl in Hu0; discriminate).
destruct (decp_sound as_andi L _ HD0) as (i0 & HD0' & Hi0).
destruct (as_andi_sound i0 u xr 7 Hi0) as (imm7 & -> & H7).
destruct (dec_sound L _ HD0') as (w0 & F0 & E0 & D0).
set (regs1 := regupd regs u (Z_to_bv 64 (x mod 8))).
assert (S0 : RiscvSemantics.step segs (mkst regs (Z_to_bv 64 L) mem (seg_rom segs))
= MachineOk (mkst regs1 (Z_to_bv 64 (L + 4)) mem (seg_rom segs))).
{ rewrite (step_opimm_gen segs regs _ mem _ w0 ALU_AND u xr imm7 F0 E0 D0), Hu0, Hxr, sext64_lit, H7, alu_and7 by exact Hx.
rewrite v_addi_lit. reflexivity. }
assert (R1u : getr regs1 u = Z_to_bv 64 (x mod 8)) by (subst regs1; apply getr_same; exact Hune).
assert (R1o : forall r, r <> u -> getr regs1 r = getr regs r) by (intros r Hr; subst regs1; apply getr_other; exact Hr).
destruct Hk2 as [[-> ->] | (HD1 & ->)].
- exists regs1. split; [apply msteps_one; [reflexivity | exact S0]|]. rewrite Z.add_0_r. auto.
- destruct (decp_sound as_addi _ _ HD1) as (i1 & HD1' & Hi1).
destruct (as_addi_sound i1 u u k Hi1) as (immk & -> & Hik).
destruct (dec_sound _ _ HD1') as (w1 & F1 & E1 & D1).
exists (regupd regs1 u (Z_to_bv 64 (x mod 8 + k))). split; [|split].
+ eapply mst_step; [reflexivity | exact S0 |]. apply msteps_one; [reflexivity|].
rewrite (step_opimm_gen segs regs1 _ mem _ w1 ALU_ADD u u immk F1 E1 D1), Hu0, R1u, sext64_lit, Hik.
rewrite alu_add_small by (unfold M64; lia). rewrite v_addi_lit. replace (L + 4 + 4) with (L + 8) by lia. reflexivity.
+ apply getr_same. exact Hune.
+ intros r Hr. rewrite getr_other by exact Hr. apply R1o. exact Hr.
Qed.
Lemma slow_block_facts : forall L Lz t u xr k,
slow_block tbl L Lz t = Some (u, xr, k) ->
exists L2,
decp tbl as_andi L = Some (u, xr, 7) /\ bv_eqb u 0 = false /\ bv_eqb u t = false
/\ ((k = 0 /\ L2 = L + 4) \/ (decp tbl as_addi (L + 4) = Some (u, u, k) /\ L2 = L + 8))
/\ 0 <= k <= 7
/\ ((exists off, decp tbl as_branch L2 = Some (BC_LT, u, t, off) /\ zcanon (L2 + off) = zcanon Lz)
\/ (exists off offj, decp tbl as_branch L2 = Some (BC_GE, u, t, off) /\ decp tbl as_j (L2 + 4) = Some offj
/\ zcanon (L2 + 4 + offj) = zcanon Lz)).
Proof.
intros L Lz t u xr k H. unfold slow_block in H.
destruct (decp tbl as_andi L) as [[[u0 xr0] i7]|] eqn:HD0; [|discriminate].
destruct (negb (i7 =? 7) || bv_eqb u0 0 || bv_eqb u0 t) eqn:Hg; [discriminate|].
apply orb_false_elim in Hg as [Hg Hut]. apply orb_false_elim in Hg as [H7 Hu0].
apply negb_false_iff in H7. apply Z.eqb_eq in H7. subst i7.
assert (TAIL : forall k0 L2,
((k0 = 0 /\ L2 = L + 4) \/ (decp tbl as_addi (L + 4) = Some (u0, u0, k0) /\ L2 = L + 8)) ->
(if negb ((0 <=? k0) && (k0 <=? 7)) then None else
match decp tbl as_branch L2 with
| Some (BC_LT, r1, r2, off) =>
if bv_eqb r1 u0 && bv_eqb r2 t && (zcanon (L2 + off) =? zcanon Lz) then Some (u0, xr0, k0) else None
| Some (BC_GE, r1, r2, off) =>
if bv_eqb r1 u0 && bv_eqb r2 t then
match decp tbl as_j (L2 + 4) with
| Some offj => if zcanon (L2 + 4 + offj) =? zcanon Lz then Some (u0, xr0, k0) else None
| None => None end
else None
| _ => None end) = Some (u, xr, k) ->
exists L2',
Some (u0, xr0, 7) = Some (u, xr, 7) /\ bv_eqb u 0 = false /\ bv_eqb u t = false
/\ ((k = 0 /\ L2' = L + 4) \/ (decp tbl as_addi (L + 4) = Some (u, u, k) /\ L2' = L + 8))
/\ 0 <= k <= 7
/\ ((exists off, decp tbl as_branch L2' = Some (BC_LT, u, t, off) /\ zcanon (L2' + off) = zcanon Lz)
\/ (exists off offj, decp tbl as_branch L2' = Some (BC_GE, u, t, off) /\ decp tbl as_j (L2' + 4) = Some offj
/\ zcanon (L2' + 4 + offj) = zcanon Lz))).
{ intros k0 L2 HkL HT.
destruct (negb ((0 <=? k0) && (k0 <=? 7))) eqn:Hk; [discriminate|].
apply negb_false_iff in Hk. apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
destruct (decp tbl as_branch L2) as [[[[c r1] r2] off]|] eqn:HD2; [|discriminate].
destruct c; try discriminate.
- destruct (bv_eqb r1 u0 && bv_eqb r2 t && (zcanon (L2 + off) =? zcanon Lz)) eqn:Hc; [|discriminate].
injection HT as -> -> ->.
apply andb_prop in Hc as [Hc Hz]. apply andb_prop in Hc as [Ha Hb].
apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hb. subst r1 r2. apply Z.eqb_eq in Hz.
exists L2. split; [reflexivity|]. split; [exact Hu0|]. split; [exact Hut|]. split; [exact HkL|]. split; [lia|].
left. exists off. auto.
- destruct (bv_eqb r1 u0 && bv_eqb r2 t) eqn:Hc; [|discriminate].
apply andb_prop in Hc as [Ha Hb]. apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hb. subst r1 r2.
destruct (decp tbl as_j (L2 + 4)) as [offj|] eqn:HD3; [|discriminate].
destruct (zcanon (L2 + 4 + offj) =? zcanon Lz) eqn:Hz; [|discriminate].
injection HT as -> -> ->. apply Z.eqb_eq in Hz.
exists L2. split; [reflexivity|]. split; [exact Hu0|]. split; [exact Hut|]. split; [exact HkL|]. split; [lia|].
right. exists off, offj. auto. }
destruct (decp tbl as_addi (L + 4)) as [[[u1 u2] k1]|] eqn:HD1.
- destruct (bv_eqb u1 u0 && bv_eqb u2 u0) eqn:Hrr.
+ apply andb_prop in Hrr as [Ha Hb]. apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hb. subst u1 u2.
destruct (TAIL k1 (L + 8) ltac:(right; auto) H) as (L2' & E1 & R). injection E1 as -> ->. exists L2'. split; [reflexivity | exact R].
+ destruct (TAIL 0 (L + 4) ltac:(left; auto) H) as (L2' & E1 & R). injection E1 as -> ->. exists L2'. split; [reflexivity | exact R].
- destruct (TAIL 0 (L + 4) ltac:(left; auto) H) as (L2' & E1 & R). injection E1 as -> ->. exists L2'. split; [reflexivity | exact R].
Qed.
Lemma slow_block_exec : forall L Lz (t u xr : reg) k regs mem x s,
slow_block tbl L Lz t = Some (u, xr, k) ->
getr regs xr = Z_to_bv 64 x -> 0 <= x < M64 ->
getr regs t = Z_to_bv 64 s -> 0 < s < 8 -> x mod 8 + k < s ->
exists regs', msteps segs (mkst regs (Z_to_bv 64 L) mem (seg_rom segs)) (mkst regs' (Z_to_bv 64 Lz) mem (seg_rom segs))
/\ (forall r, r <> u -> getr regs' r = getr regs r).
Proof.
intros L Lz t u xr k regs mem x s H Hxr Hx Ht Hs Hlt.
destruct (slow_block_facts L Lz t u xr k H) as (L2 & HD0 & Hu0 & Hut & HkL & Hk & Hcmp).
assert (Hut' : t <> u) by (intros ->; rewrite bv_eqb_refl in Hut; discriminate).
destruct (andi_prefix_exec L L2 t u xr k regs mem x HD0 Hu0 Hut' HkL Hk Hxr Hx) as (regs2 & M2 & R2u & R2o).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hxm.
assert (R2t : getr regs2 t = Z_to_bv 64 s) by (rewrite R2o by exact Hut'; exact Ht).
assert (Hlts : bv_lts (getr regs2 u) (getr regs2 t) = true).
{ rewrite R2u, R2t, bv_lts_small by lia. apply Z.ltb_lt. lia. }
exists regs2. split; [|exact R2o].
eapply msteps_trans; [exact M2|].
destruct Hcmp as [(off & HD2 & Hz) | (off & offj & HD2 & HD3 & Hz)].
- destruct (decp_sound as_branch _ _ HD2) as (i2 & HD2' & Hi2).
destruct (as_branch_sound i2 _ _ _ _ Hi2) as (offb & -> & Hoff).
destruct (dec_sound _ _ HD2') as (w2 & F2 & E2 & D2).
apply msteps_one; [reflexivity|].
rewrite (step_branch_tk_gen segs regs2 _ mem _ w2 BC_LT u t offb F2 E2 D2); [|cbn [branch_taken]; exact Hlts].
rewrite btgt_lit, Hoff, (zv_zcanon_eq _ _ Hz). reflexivity.
- destruct (decp_sound as_branch _ _ HD2) as (i2 & HD2' & Hi2).
destruct (as_branch_sound i2 _ _ _ _ Hi2) as (offb & -> & Hoff).
destruct (dec_sound _ _ HD2') as (w2 & F2 & E2 & D2).
destruct (decp_sound as_j _ _ HD3) as (i3 & HD3' & Hi3).
destruct (as_j_sound i3 _ Hi3) as (offc & -> & Hoffc).
destruct (dec_sound _ _ HD3') as (w3 & F3 & E3 & D3).
eapply mst_step; [reflexivity| |].
{ rewrite (step_branch_ft_gen segs regs2 _ mem _ w2 BC_GE u t offb F2 E2 D2); [reflexivity|].
cbn [branch_taken]. rewrite Hlts. reflexivity. }
rewrite v_addi_lit. apply msteps_one; [reflexivity|].
rewrite (step_jal_x0 segs regs2 _ mem _ w3 offc F3 E3 D3). rewrite btgt_lit, Hoffc, (zv_zcanon_eq _ _ Hz). reflexivity.
Qed.
Lemma regs_ok_rereg : forall E sr regs (r : reg) e,
regs_ok E sr regs -> bv_eqb r 0 = false -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 He r'. unfold sr_set. rewrite Hr0. specialize (Hr r').
unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact He.
Qed.
Lemma st_ok_rereg : forall E ss regs pc mem (r : reg) e pc',
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> ss_resv ss = None ->
bv_eqb r 0 = false -> getr regs r = sv_denot E e ->
st_ok segs E (setreg ss r e pc') (mkst regs (Z_to_bv 64 pc') mem (seg_rom segs)).
Proof.
intros E ss regs pc mem r e pc' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hrv Hr0 He.
unfold st_ok, setreg; cbn. rewrite Hrv. cbn. repeat (split; [reflexivity|]).
split; [apply regs_ok_rereg; assumption|]. split; assumption.
Qed.
Lemma find_tok_sound : forall toks rs1 T tk,
find_tok toks rs1 T = Some tk -> In tk toks /\ tk_reg tk = rs1 /\ tk_T tk = T.
Proof.
induction toks as [|t0 l IH]; intros rs1 T tk Htk; cbn in Htk; [discriminate|].
destruct (bv_eqb (tk_reg t0) rs1 && (tk_T t0 =? T)%nat) eqn:Hb.
- injection Htk as <-. apply andb_prop in Hb as [H1 H2]. apply bv_eqb_eq in H1. apply Nat.eqb_eq in H2.
split; [left; reflexivity | auto].
- destruct (IH _ _ _ Htk) as (Hin & Hr & HT0). split; [right; exact Hin | auto].
Qed.
Lemma tok_branch_sound : forall final E st cnd rs1 rs2 (imm : bv 13) st' ms w,
INV final E st ms ->
fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
decode_any w = Some (Branch cnd rs1 rs2 imm, 4) ->
tok_branch st cnd rs1 rs2 (bv_signed imm) = Some st' ->
doml (sh_obls st') final ->
exists ms' E',
msteps segs ms ms' /\ INV final E' st' ms'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ ss_mem (sh_ss st') = ss_mem (sh_ss st) /\ ms_mem ms' = ms_mem ms /\ ss_facts (sh_ss st') = ss_facts (sh_ss st).
Proof.
intros final E st cnd rs1 rs2 imm st' ms w HI Hf He Hd H Hdom.
destruct st as [ss j toks chk obls]. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
destruct HI as (HS & HT & HC & HN). cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in *.
unfold tok_branch in H. cbn [sh_ss sh_j sh_toks sh_chk sh_obls] in H.
destruct (bv_eqb rs2 0) eqn:Hrs2; [|discriminate]. cbn [negb] in H. apply bv_eqb_eq in Hrs2. subst rs2.
destruct (ss_resv ss) as [rv|] eqn:Hrv; [discriminate|].
destruct (sr_get (ss_regs ss) rs1) as [|T z0| | | | | | | | |] eqn:HR1; try discriminate.
destruct (z0 =? 0) eqn:Hz0; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hz0. subst z0.
destruct (find_tok toks rs1 T) as [tk|] eqn:Htk; [|discriminate].
destruct (find_tok_sound _ _ _ _ Htk) as (Htkin & Htkr & HtkT).
destruct chk; [|rewrite (HN eq_refl) in Htkin; destruct Htkin].
destruct (HC eq_refl) as (Hst & Hat & Hsh & Htoks & Hob).
pose proof Hst as (Hwin & Hents & HK & Hspan).
assert (Htok : tok_ok E (ms_mem ms) tk) by (rewrite Forall_forall in Htoks; exact (Htoks tk Htkin)).
destruct Htok as (Hxk & Hcsp & b & Hb & Hv).
set (x := tk_x tk) in *.
remember (match cnd with
| BC_NE => (zcanon (ss_pc ss + bv_signed imm), ss_pc ss + 4)
| BC_EQ => (ss_pc ss + 4, zcanon (ss_pc ss + bv_signed imm))
| _ => (0, 0) end) as LL eqn:HLL.
destruct LL as [Lnz Lz].
assert (Hcnd : (cnd = BC_NE /\ Lnz = zcanon (ss_pc ss + bv_signed imm) /\ Lz = ss_pc ss + 4)
\/ (cnd = BC_EQ /\ Lnz = ss_pc ss + 4 /\ Lz = zcanon (ss_pc ss + bv_signed imm))).
{ destruct cnd; try discriminate; injection HLL as -> ->; auto. }
assert (H' : match slow_block tbl Lnz Lz rs1 with
| Some (u, xr, k) =>
if negb (sv_eqb (sr_get (ss_regs ss) xr) x) then None else
if negb (ss_atoms_lt (K + j) ss) then None else
match need (ss_facts ss) x (k + 1) obls with
| None => None
| Some obls' => Some (mkSH (setreg ss u (SOff (K + j) 0) Lz) (S j) (prune (setreg ss u (SOff (K + j) 0) Lz) toks) true obls')
end
| None =>
match dec tbl Lnz with
| None => None
| Some i =>
match as_andi i with
| Some _ => None
| None =>
match need (ss_facts ss) (gran (ss_facts ss) x) 8 obls with
| None => None
| Some obls' => Some (mkSH (setreg ss rs1 (SLit 0) Lz) j (prune (setreg ss rs1 (SLit 0) Lz) toks) true obls')
end
end
end
end = Some st').
{ destruct cnd; try discriminate; exact H. }
clear H. rename H' into H.
pose proof HS as HS0. destruct HS as (_ & Hpc & _ & _ & _ & _ & Hregs & Hmem & HG).
pose proof (st_ok_mkst segs E ss ms HS0 Hrv) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
assert (Ht : getr regs rs1 = cellval (tk_sg tk) b).
{ rewrite (Hregs rs1), HR1. cbn [sv_denot]. rewrite <- HtkT, Hv, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (bv_unsigned_in_range 8 b) as Hbr. change (bv_modulus 8) with 256 in Hbr.
rewrite Hshape in Hf. cbn [ms_pc_val mkst] in Hf.
assert (Hrds : rd_of mem (shadow_of_addr (U E Bx) (U E x)) = Some (bv_unsigned b)).
{ unfold rd_of, shadow_of_addr. unfold cell_x in Hb. rewrite Hb. reflexivity. }
pose proof (U_range E x) as HUx.
assert (ZERO : bv_unsigned b = 0 ->
msteps segs (mkst regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs)) (mkst regs (Z_to_bv 64 Lz) mem (seg_rom segs))).
{ intros Hb0.
assert (Ht0 : getr regs rs1 = Z_to_bv 64 0) by (rewrite Ht; apply (proj2 (cellval_zero_iff _ _)); exact Hb0).
apply msteps_one; [reflexivity|].
destruct Hcnd as [(-> & _ & ->) | (-> & _ & ->)].
+ rewrite (step_branch_ft_gen segs regs _ mem _ w BC_NE rs1 0 imm Hf He Hd); [rewrite v_addi_lit; reflexivity|].
cbn [branch_taken]. rewrite Ht0, getr_zero, bv_eqb_refl. reflexivity.
+ rewrite (step_branch_tk_gen segs regs _ mem _ w BC_EQ rs1 0 imm Hf He Hd); [rewrite btgt_lit, Z_to_bv64_canon; reflexivity|].
cbn [branch_taken]. rewrite Ht0, getr_zero, bv_eqb_refl. reflexivity. }
destruct (slow_block tbl Lnz Lz rs1) as [[[u xr] k]|] eqn:Hsb.
-
destruct (sv_eqb (sr_get (ss_regs ss) xr) x) eqn:Hxr; [|discriminate]. cbn [negb] in H. apply sv_eqb_eq in Hxr.
destruct (ss_atoms_lt (K + j) ss) eqn:Hal; [|discriminate]. cbn [negb] in H.
destruct (need (ss_facts ss) x (k + 1) obls) as [obls'|] eqn:Hneed; [|discriminate]. injection H as <-.
cbn [sh_obls] in Hdom.
pose proof (slow_block_facts _ _ _ _ _ _ Hsb) as (L2 & _ & Hu0 & Hut & _ & Hk & _).
assert (Hune : u <> 0%bv) by (intros ->; rewrite bv_eqb_refl in Hu0; discriminate).
destruct (need_sound final E _ mem (ss_facts ss) x (k + 1) obls obls' Hst Hsh Hob HG Hneed Hdom ltac:(lia)) as [HRA _].
pose proof (check_passes_lb (rd_of mem) (U E Bx) (U E x) (k + 1) (U E x) (k + 1) (bv_unsigned b)
HRA ltac:(lia) ltac:(lia) ltac:(lia) Hrds) as Hpass.
assert (Hx : getr regs xr = Z_to_bv 64 (U E x)) by (rewrite (Hregs xr), Hxr, denot_lit_U; reflexivity).
assert (PATHS : exists regs', msteps segs (mkst regs (Z_to_bv 64 (ss_pc ss)) mem (seg_rom segs))
(mkst regs' (Z_to_bv 64 Lz) mem (seg_rom segs))
/\ (forall r, r <> u -> getr regs' r = getr regs r)).
{ destruct (Z.eq_dec (bv_unsigned b) 0) as [Hs0|Hs0].
- exists regs. split; [exact (ZERO Hs0) | intros; reflexivity].
- destruct Hpass as [Hz | [Hlt Hsr]]; [lia|].
assert (Hts : getr regs rs1 = Z_to_bv 64 (bv_unsigned b)) by (rewrite Ht; apply cellval_small; lia).
assert (Hne0 : bv_eqb (getr regs rs1) (getr regs 0) = false).
{ rewrite Hts, getr_zero. apply Bool.not_true_is_false. intros Hq. apply bv_eqb_eq in Hq.
apply (f_equal bv_unsigned) in Hq. rewrite !unsigned_lit_small in Hq by lia. lia. }
destruct (slow_block_exec Lnz Lz rs1 u xr k regs mem _ (bv_unsigned b) Hsb Hx ltac:(lia) Hts ltac:(lia) ltac:(lia))
as (regs' & Mslow & Hfr).
exists regs'. split; [|exact Hfr].
eapply mst_step; [reflexivity| |exact Mslow].
destruct Hcnd as [(-> & -> & _) | (-> & -> & _)].
+ rewrite (step_branch_tk_gen segs regs _ mem _ w BC_NE rs1 0 imm Hf He Hd); [rewrite btgt_lit, Z_to_bv64_canon; reflexivity|].
cbn [branch_taken]. rewrite Hne0. reflexivity.
+ rewrite (step_branch_ft_gen segs regs _ mem _ w BC_EQ rs1 0 imm Hf He Hd); [rewrite v_addi_lit; reflexivity|].
cbn [branch_taken]. exact Hne0. }
destruct PATHS as (regs' & Mp & Hfr).
set (U0 := (K + j)%nat) in *. set (v := getr regs' u). set (E' := ewset E U0 v).
assert (HA : env_agree U0 E E') by apply env_agree_ewset.
assert (HUK : (K <= U0)%nat) by lia.
exists (mkst regs' (Z_to_bv 64 Lz) mem (seg_rom segs)), E'.
split; [rewrite Hshape at 1; exact Mp|].
split; [|split; [right; exists v; split; [reflexivity | split; [reflexivity | first [exact Hal | reflexivity]]] | split; [reflexivity | split; reflexivity]]].
unfold INV; cbn [sh_ss sh_j sh_toks sh_chk sh_obls].
assert (Hat' : sh_atoms_lt U0 = true) by (apply (sh_atoms_lt_mono K); [lia | exact Hat]).
split; [|split; [|split; [|intros; discriminate]]].
+ rewrite Hshape in HS0.
change (setreg ss u (SOff U0 0) Lz) with (set_regs_pc ss [(u, SOff U0 0)] Lz).
apply (st_ok_set_regs segs U0 E E' ss regs regs' _ Lz mem [(u, SOff U0 0)] HS0 HA Hal Hrv).
* reflexivity.
* intros r Hr. cbn in Hr. apply orb_false_elim in Hr as [Hr _]. apply Hfr. intros ->. rewrite bv_eqb_refl in Hr. discriminate.
* constructor; [|constructor]. cbn [fst snd]. split; [exact Hu0|].
cbn [sv_denot]. subst E'. rewrite ew_ewset_same, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ apply Forall_filter'. rewrite Forall_forall in HT |- *. intros tk0 Hin0. specialize (HT tk0 Hin0). lia.
+ intros _.
split; [|split; [exact Hat|split; [|split]]].
* eapply (static_sem_agree U0 E E'); [exact HA | exact Hat' | | exact Hst].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal2 _]. apply andb_prop in Hal2 as [Hal2 _]. apply andb_prop in Hal2 as [_ Hm2]. exact Hm2.
* exact (sh_ok_agree U0 E E' _ HA Hat' Hsh).
* apply Forall_filter'. rewrite Forall_forall in Htoks, HT |- *. intros tk0 Hin0.
apply (tok_ok_agree U0 E E'); [exact HA | exact HUK | exact Hat' | exact (HT tk0 Hin0) | exact (Htoks tk0 Hin0)].
* exact (OBL_agree final U0 E E' _ HA HUK Hat' Hob).
-
destruct (dec tbl Lnz) as [i|]; [|discriminate].
destruct (as_andi i); [discriminate|].
destruct (need (ss_facts ss) (gran (ss_facts ss) x) 8 obls) as [obls'|] eqn:Hneed; [|discriminate]. injection H as <-.
cbn [sh_obls] in Hdom.
destruct (need_sound final E _ mem (ss_facts ss) (gran (ss_facts ss) x) 8 obls obls' Hst Hsh Hob HG Hneed Hdom ltac:(lia)) as [HRA _].
assert (Hb0 : bv_unsigned b = 0).
{ destruct (gran_val E (ss_facts ss) x HG) as [Hg | [Hg Hgle]].
- rewrite Hg in HRA.
apply (check_passes_whole (rd_of mem) (U E Bx) (U E x) 8 (U E x) 8 (bv_unsigned b) HRA);
[lia | lia | pose proof (Z.mul_div_le (U E x) 8 ltac:(lia)); lia | exact Hrds].
- rewrite Hg in HRA.
apply (check_passes_whole (rd_of mem) (U E Bx) (8 * (U E x / 8)) 8 (U E x) (8 * (U E x / 8) + 8 - U E x) (bv_unsigned b) HRA);
[pose proof (Z.mul_div_le (U E x) 8 ltac:(lia)); lia | lia | lia | exact Hrds]. }
assert (Hrs10 : bv_eqb rs1 0 = false).
{ apply Bool.not_true_is_false. intros Hq. apply bv_eqb_eq in Hq. rewrite Hq in HR1.
unfold sr_get in HR1. rewrite ?bv_eqb_refl in HR1. cbn in HR1. discriminate. }
exists (mkst regs (Z_to_bv 64 Lz) mem (seg_rom segs)), E.
split; [rewrite Hshape at 1; exact (ZERO Hb0)|].
split; [|split; [left; split; reflexivity | split; [reflexivity | split; reflexivity]]].
unfold INV; cbn [sh_ss sh_j sh_toks sh_chk sh_obls].
split; [|split; [apply Forall_filter'; exact HT|split; [|intros; discriminate]]].
+ rewrite Hshape in HS0. apply (st_ok_rereg E ss regs _ mem rs1 (SLit 0) Lz HS0 Hrv Hrs10).
rewrite Ht. cbn [sv_denot]. apply (proj2 (cellval_zero_iff _ _)). exact Hb0.
+ intros _. split; [exact Hst|]. split; [exact Hat|]. split; [exact Hsh|]. split; [apply Forall_filter'; exact Htoks | exact Hob].
Qed.
Lemma tok_load_doml : forall st sg rd a st',
tok_load st sg rd a = Some st' -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st sg rd a st'. unfold tok_load. destruct st as [ss j toks chk obls]; cbn.
repeat match goal with
|- context [match ?y with _ => _ end] =>
lazymatch y with
| YCbn.need _ _ _ _ ?G ?x ?n ?l => destruct y eqn:?
| _ => destruct y
end; try discriminate
end;
intros Hb; try discriminate; injection Hb as <-; cbn [sh_obls sh_chk];
(split; [first [apply doml_refl | eapply need_doml; eassumption] | reflexivity]).
Qed.
Lemma tok_branch_doml : forall st cnd rs1 rs2 imm st',
tok_branch st cnd rs1 rs2 imm = Some st' -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st cnd rs1 rs2 imm st'. unfold tok_branch. destruct st as [ss j toks chk obls]; cbn.
repeat match goal with
|- context [match ?y with _ => _ end] =>
lazymatch y with
| YCbn.need _ _ _ _ ?G ?x ?n ?l => destruct y eqn:?
| _ => destruct y
end; try discriminate
end;
intros Hb; try discriminate; injection Hb as <-; cbn [sh_obls sh_chk];
(split; [first [apply doml_refl | eapply need_doml; eassumption] | reflexivity]).
Qed.
Lemma sym_step_tok_doml : forall st st',
(sym_step_tok st = TRun st' \/ sym_step_tok st = TEcall st') ->
doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
intros st st' H. unfold sym_step_tok in H.
destruct (sym_step_sh segs tbl (sh_ss st)) as [ss1|ss1|why].
- destruct H as [H|H]; [injection H as <- | discriminate]. cbn. split; [apply doml_refl | reflexivity].
- destruct H as [H|H]; [discriminate | injection H as <-]. cbn. split; [apply doml_refl | reflexivity].
- destruct (dec tbl (ss_pc (sh_ss st))) as [i|]; [|destruct H; discriminate].
destruct i; try (destruct H; discriminate).
+ destruct (tok_branch st c rs1 rs2 (bv_signed imm)) as [st2|] eqn:Hb; [|destruct H; discriminate].
destruct H as [H|H]; [injection H as <- | discriminate]. exact (tok_branch_doml _ _ _ _ _ _ Hb).
+ destruct sz; try (destruct H; discriminate).
destruct (tok_load st signed rd _) as [st2|] eqn:Hl; [|destruct H; discriminate].
destruct H as [H|H]; [injection H as <- | discriminate]. exact (tok_load_doml _ _ _ _ _ Hl).
Qed.
Lemma sym_run_tok_doml : forall fuel st st' r,
sym_run_tok segs tbl K Bx Bspan SH fuel st = (st', r) -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros st st' r H; cbn [sym_run_tok] in H.
- injection H as <- <-. split; [apply doml_refl | reflexivity].
- destruct (sym_step_tok st) as [st1|st1|why] eqn:Hs.
+ destruct (sym_step_tok_doml st st1 (or_introl Hs)) as [D1 C1]. destruct (IH _ _ _ H) as [D2 C2].
split; [exact (doml_trans _ _ _ D1 D2) | congruence].
+ injection H as <- <-. exact (sym_step_tok_doml st st1 (or_intror Hs)).
+ injection H as <- <-. split; [apply doml_refl | reflexivity].
Qed.
Lemma sym_run_to_tok_doml : forall fuel stop st st' r,
sym_run_to_tok segs tbl K Bx Bspan SH fuel stop st = (st', r) -> doml (sh_obls st) (sh_obls st') /\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros stop st st' r H; cbn [sym_run_to_tok] in H.
- injection H as <- <-. split; [apply doml_refl | reflexivity].
- destruct (ss_pc (sh_ss st) =? stop); [injection H as <- <-; split; [apply doml_refl | reflexivity]|].
destruct (sym_step_tok st) as [st1|st1|why] eqn:Hs.
+ destruct (sym_step_tok_doml st st1 (or_introl Hs)) as [D1 C1]. destruct (IH _ _ _ _ H) as [D2 C2].
split; [exact (doml_trans _ _ _ D1 D2) | congruence].
+ injection H as <- <-. exact (sym_step_tok_doml st st1 (or_intror Hs)).
+ injection H as <- <-. split; [apply doml_refl | reflexivity].
Qed.
Theorem sym_step_tok_sound : forall final E st st' ms,
INV final E st ms -> sym_step_tok st = TRun st' -> doml (sh_obls st') final ->
exists ms' E',
msteps segs ms ms' /\ INV final E' st' ms'
/\ ((sh_j st' = sh_j st /\ E' = E)
\/ (exists v, sh_j st' = S (sh_j st) /\ E' = ewset E (K + sh_j st) v /\ ss_atoms_lt (K + sh_j st) (sh_ss st) = true))
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of E (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
intros final E st st' ms HI H Hdom.
pose proof (proj2 (sym_step_tok_doml st st' (or_introl H))) as Hchk.
unfold sym_step_tok in H.
pose proof HI as (HS & _).
destruct (sym_step_sh segs tbl (sh_ss st)) as [ss1|ss1|why] eqn:Hs.
- injection H as <-.
destruct (sym_step_sh_soundP segs tbl Htbl P1_pin P5_pin E (sh_ss st) ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr).
pose proof (sym_step_sh_skeleton segs tbl (sh_ss st) ss1 Hs) as Hsk.
exists ms1, E. split.
{ apply msteps_one; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hstep]. }
split; [exact (advance_sound final E st ss1 ms ms1 HI HS1 Hsk Hfr)|].
split; [left; split; reflexivity|]. split; [exact Hsk|]. split; [exact Hfr | reflexivity].
- discriminate.
- destruct (dec tbl (ss_pc (sh_ss st))) as [i|] eqn:HD; [|discriminate].
destruct (dec_sound _ _ HD) as (w & Hf & He & Hdi).
assert (Hf' : fetch_word segs (ms_pc_val ms) = Some w).
{ destruct HS as (_ & Hpc & _). rewrite Hpc. exact Hf. }
destruct i; try discriminate.
+
destruct (tok_branch st c rs1 rs2 (bv_signed imm)) as [st2|] eqn:Hb; [|discriminate]. injection H as <-.
destruct (tok_branch_sound final E st c rs1 rs2 imm st2 ms w HI Hf' He Hdi Hb Hdom) as (ms' & E' & Hms & HI' & Hj & Hm1 & Hm2 & _).
exists ms', E'. split; [exact Hms|]. split; [exact HI'|]. split; [exact Hj|].
rewrite Hm1, Hm2. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
+
destruct sz; try discriminate.
destruct (tok_load st signed rd _) as [st2|] eqn:Hl; [|discriminate]. injection H as <-.
destruct (tok_load_sound final E st signed rd rs1 imm st2 ms w HI Hf' He Hdi Hl Hdom) as (ms' & E' & Hstep & HI' & Hj & Hm1 & Hm2 & _).
exists ms', E'. split.
{ apply msteps_one; [destruct HS as (_ & _ & Hp & _); exact Hp | exact Hstep]. }
split; [exact HI'|]. split; [exact Hj|]. rewrite Hm1, Hm2. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
Qed.
Theorem sym_step_tok_ecall : forall final E st st' ms,
INV final E st ms -> sym_step_tok st = TEcall st' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok_ecall segs E (sh_ss st') ms'
/\ ms_mem ms' = ms_mem ms /\ sh_ss st' = sh_ss st /\ sh_j st' = sh_j st /\ sh_chk st' = sh_chk st
/\ sh_obls st' = sh_obls st.
Proof.
intros final E st st' ms (HS & _) H. unfold sym_step_tok in H.
destruct (sym_step_sh segs tbl (sh_ss st)) as [ss1|ss1|why] eqn:Hs; try discriminate.
- injection H as <-.
destruct (sym_step_sh_ecallP segs tbl Htbl P1_pin P5_pin E (sh_ss st) ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hm & ->).
exists ms1. cbn. auto 7.
- destruct (dec tbl (ss_pc (sh_ss st))) as [i|]; [|discriminate].
destruct i; try discriminate.
+ destruct (tok_branch st c rs1 rs2 (bv_signed imm)); discriminate.
+ destruct sz; try discriminate. destruct (tok_load st signed rd _); discriminate.
Qed.
Lemma in_wrange_agree : forall k E E' rs x,
env_agree k E E' -> mem_atoms_lt k rs = true -> in_wrange E' rs x -> in_wrange E rs x.
Proof.
intros k E E' rs x HA Hm (r & Hin & Hr). exists r. split; [exact Hin|].
unfold mem_atoms_lt in Hm. rewrite forallb_forall in Hm. specialize (Hm r Hin).
unfold region_atoms_lt in Hm. apply andb_prop in Hm as [Hb _].
rewrite (base_val_agree k E E' _ HA Hb) in Hr. exact Hr.
Qed.
Lemma frame_of_agree_skel : forall k E E' rs rs1 m m',
env_agree k E E' -> mem_atoms_lt k rs = true -> skeleton rs1 = skeleton rs ->
frame_of E' rs1 m m' -> frame_of E rs1 m m'.
Proof.
intros k E E' rs rs1 m m' HA Hm Hsk HF x Hx. apply HF. intros Hin. apply Hx.
apply (in_wrange_skeleton E rs rs1 _ (eq_sym Hsk)).
apply (in_wrange_agree k E E' rs _ HA Hm).
exact (in_wrange_skeleton E' rs1 rs _ Hsk Hin).
Qed.
Theorem sym_run_tok_sound_gen : forall final fuel E0 ws st ms st' r,
INV final (extK E0 K ws) st ms -> length ws = sh_j st ->
sym_run_tok segs tbl K Bx Bspan SH fuel st = (st', r) ->
doml (sh_obls st') final ->
exists ws2 ms',
length (ws ++ ws2) = sh_j st' /\ msteps segs ms ms'
/\ match r with
| TS_ecall => st_ok_ecall segs (extK E0 K (ws ++ ws2)) (sh_ss st') ms'
/\ (sh_chk st' = true -> sh_ok (extK E0 K (ws ++ ws2)) (ms_mem ms'))
| _ => INV final (extK E0 K (ws ++ ws2)) st' ms'
end
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of (extK E0 K ws) (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros E0 ws st ms st' r HI Hlen H Hdom; cbn [sym_run_tok] in H.
- injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
- destruct (sym_step_tok st) as [st1|st1|why] eqn:Hs.
+ assert (Hdom1 : doml (sh_obls st1) final).
{ eapply doml_trans; [exact (proj1 (sym_run_tok_doml fuel st1 st' r H)) | exact Hdom]. }
destruct (sym_step_tok_sound final _ st st1 ms HI Hs Hdom1) as (ms1 & E1 & Hms1 & HI1 & Hj & Hsk1 & Hfr1 & Hchk1).
assert (Hws1 : exists ws1, E1 = extK E0 K (ws ++ ws1) /\ length (ws ++ ws1) = sh_j st1).
{ destruct Hj as [[Hj ->] | (v & Hj & -> & _)].
- exists []. rewrite app_nil_r. split; [reflexivity | lia].
- exists [v]. rewrite extK_snoc, Hlen. split; [reflexivity|]. rewrite length_app. cbn. lia. }
destruct Hws1 as (ws1 & -> & Hlen1).
destruct (IH E0 (ws ++ ws1) st1 ms1 st' r HI1 Hlen1 H Hdom) as (ws2 & ms' & Hlen' & Hms & HR & Hsk & Hfr & Hchk).
exists (ws1 ++ ws2), ms'. rewrite app_assoc.
split; [exact Hlen'|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HR|].
split; [congruence|]. split; [|congruence].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 |].
destruct Hj as [[Hj HE] | (v & Hj & HE & Hal)].
* destruct ws1 as [|v1 ws1']; [rewrite app_nil_r in Hfr; exact Hfr|].
exfalso. rewrite length_app in Hlen1. cbn in Hlen1. lia.
* assert (Hws1 : ws1 = [v]).
{ destruct ws1 as [|v1 [|v2 l]]; rewrite length_app in Hlen1; cbn in Hlen1; try lia.
rewrite <- Hlen in HE. apply (f_equal (fun E => ew E (K + length ws)%nat)) in HE. cbn beta in HE.
rewrite extK_snoc, !ew_ewset_same in HE. rewrite HE. reflexivity. }
subst ws1. rewrite extK_snoc, Hlen in Hfr.
eapply (frame_of_agree_skel (K + sh_j st) _ _ (ss_mem (sh_ss st))); [apply env_agree_ewset | | exact Hsk1 | exact Hfr].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [_ Hm]. exact Hm.
+ injection H as <- <-.
destruct (sym_step_tok_ecall final _ st st1 ms HI Hs) as (ms1 & Hstep & HS1 & Hm & Hss & Hj & Hchk & _).
exists [], ms1. rewrite app_nil_r.
split; [rewrite Hj; exact Hlen|]. split.
{ apply msteps_one; [destruct HI as ((_ & _ & Hp & _) & _); exact Hp | exact Hstep]. }
split.
{ split; [exact HS1|]. intros Hc. rewrite Hm. rewrite Hchk in Hc.
destruct HI as (_ & _ & HC & _). destruct (HC Hc) as (_ & _ & Hsh & _). exact Hsh. }
rewrite Hss, Hm. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
+ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
Qed.
Theorem sym_run_to_tok_sound_gen : forall final fuel stop E0 ws st ms st' r,
INV final (extK E0 K ws) st ms -> length ws = sh_j st ->
sym_run_to_tok segs tbl K Bx Bspan SH fuel stop st = (st', r) ->
doml (sh_obls st') final ->
exists ws2 ms',
length (ws ++ ws2) = sh_j st' /\ msteps segs ms ms'
/\ match r with
| TS_ecall => st_ok_ecall segs (extK E0 K (ws ++ ws2)) (sh_ss st') ms'
/\ (sh_chk st' = true -> sh_ok (extK E0 K (ws ++ ws2)) (ms_mem ms'))
| _ => INV final (extK E0 K (ws ++ ws2)) st' ms'
end
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem (sh_ss st))
/\ frame_of (extK E0 K ws) (ss_mem (sh_ss st)) (ms_mem ms) (ms_mem ms')
/\ sh_chk st' = sh_chk st.
Proof.
induction fuel as [|fuel IH]; intros stop E0 ws st ms st' r HI Hlen H Hdom; cbn [sym_run_to_tok] in H.
- injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
- destruct (ss_pc (sh_ss st) =? stop).
{ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity]. }
destruct (sym_step_tok st) as [st1|st1|why] eqn:Hs.
+ assert (Hdom1 : doml (sh_obls st1) final).
{ eapply doml_trans; [exact (proj1 (sym_run_to_tok_doml fuel stop st1 st' r H)) | exact Hdom]. }
destruct (sym_step_tok_sound final _ st st1 ms HI Hs Hdom1) as (ms1 & E1 & Hms1 & HI1 & Hj & Hsk1 & Hfr1 & Hchk1).
assert (Hws1 : exists ws1, E1 = extK E0 K (ws ++ ws1) /\ length (ws ++ ws1) = sh_j st1).
{ destruct Hj as [[Hj ->] | (v & Hj & -> & _)].
- exists []. rewrite app_nil_r. split; [reflexivity | lia].
- exists [v]. rewrite extK_snoc, Hlen. split; [reflexivity|]. rewrite length_app. cbn. lia. }
destruct Hws1 as (ws1 & -> & Hlen1).
destruct (IH stop E0 (ws ++ ws1) st1 ms1 st' r HI1 Hlen1 H Hdom) as (ws2 & ms' & Hlen' & Hms & HR & Hsk & Hfr & Hchk).
exists (ws1 ++ ws2), ms'. rewrite app_assoc.
split; [exact Hlen'|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms]|]. split; [exact HR|].
split; [congruence|]. split; [|congruence].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 |].
destruct Hj as [[Hj HE] | (v & Hj & HE & Hal)].
* destruct ws1 as [|v1 ws1']; [rewrite app_nil_r in Hfr; exact Hfr|].
exfalso. rewrite length_app in Hlen1. cbn in Hlen1. lia.
* assert (Hws1 : ws1 = [v]).
{ destruct ws1 as [|v1 [|v2 l]]; rewrite length_app in Hlen1; cbn in Hlen1; try lia.
rewrite <- Hlen in HE. apply (f_equal (fun E => ew E (K + length ws)%nat)) in HE. cbn beta in HE.
rewrite extK_snoc, !ew_ewset_same in HE. rewrite HE. reflexivity. }
subst ws1. rewrite extK_snoc, Hlen in Hfr.
eapply (frame_of_agree_skel (K + sh_j st) _ _ (ss_mem (sh_ss st))); [apply env_agree_ewset | | exact Hsk1 | exact Hfr].
unfold ss_atoms_lt in Hal. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [Hal _]. apply andb_prop in Hal as [_ Hm]. exact Hm.
+ injection H as <- <-.
destruct (sym_step_tok_ecall final _ st st1 ms HI Hs) as (ms1 & Hstep & HS1 & Hm & Hss & Hj & Hchk & _).
exists [], ms1. rewrite app_nil_r.
split; [rewrite Hj; exact Hlen|]. split.
{ apply msteps_one; [destruct HI as ((_ & _ & Hp & _) & _); exact Hp | exact Hstep]. }
split.
{ split; [exact HS1|]. intros Hc. rewrite Hm. rewrite Hchk in Hc.
destruct HI as (_ & _ & HC & _). destruct (HC Hc) as (_ & _ & Hsh & _). exact Hsh. }
rewrite Hss, Hm. split; [reflexivity|]. split; [apply frame_of_refl | exact Hchk].
+ injection H as <- <-. exists [], ms. rewrite app_nil_r.
split; [exact Hlen|]. split; [apply mst_refl|]. split; [exact HI|]. split; [reflexivity|]. split; [apply frame_of_refl | reflexivity].
Qed.
Lemma OBL_of_final : forall final E m, Forall (ob_holds E m) final -> OBL final E m.
Proof.
intros final E m H o (o' & Hin & Hx & Hn) _ _. rewrite Forall_forall in H. specialize (H o' Hin).
unfold ob_holds in *. rewrite Hx in H. eapply range_addressable_sub; [exact H | lia | lia].
Qed.
Lemma start_INV : forall final E ss ms,
st_ok segs E ss ms -> sh_ok E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
Forall (ob_holds E (ms_mem ms)) final ->
INV final E (start K Bx Bspan SH ss) ms.
Proof.
intros final E ss ms HS Hsh Hchk Hfin. unfold start, INV; cbn. rewrite Hchk.
split; [exact HS|]. split; [constructor|]. split; [|intros; discriminate].
intros _. destruct HS as (_ & _ & _ & _ & _ & _ & _ & (Hwf & _) & HG).
split; [exact (static_sound E ss _ HG Hwf Hchk Hsh)|]. split; [|split; [exact Hsh | split; [constructor | exact (OBL_of_final _ _ _ Hfin)]]].
unfold sh_static_ok in Hchk. apply andb_prop in Hchk as [_ Hat]. exact Hat.
Qed.
Theorem sym_run_tok_sound : forall n E ss ms st' r,
st_ok segs E ss ms -> sh_ok E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
Forall (ob_holds E (ms_mem ms)) (sh_obls st') ->
exists ws ms',
length ws = sh_j st' /\ msteps segs ms ms'
/\ match r with
| TS_ecall => st_ok_ecall segs (extK E K ws) (sh_ss st') ms'
| _ => st_ok segs (extK E K ws) (sh_ss st') ms'
end
/\ sh_ok (extK E K ws) (ms_mem ms')
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem ss)
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n E ss ms st' r HS Hsh Hchk H Hfin. unfold sym_runN_tok in H.
destruct (sym_run_tok_sound_gen (sh_obls st') (N.to_nat n) E [] (start K Bx Bspan SH ss) ms st' r
(start_INV _ E ss ms HS Hsh Hchk Hfin) eq_refl H (doml_refl _)) as (ws & ms' & Hlen & Hms & HR & Hsk & Hfr & Hc).
cbn [app extK length start sh_ss sh_chk] in *. rewrite Hchk in Hc.
exists ws, ms'. split; [exact Hlen|]. split; [exact Hms|].
destruct r.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
- destruct HR as [HS' Hsh']. split; [exact HS'|]. split; [exact (Hsh' Hc)|]. auto.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
Qed.
Theorem sym_run_to_tok_sound : forall n stop E ss ms st' r,
st_ok segs E ss ms -> sh_ok E (ms_mem ms) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
Forall (ob_holds E (ms_mem ms)) (sh_obls st') ->
exists ws ms',
length ws = sh_j st' /\ msteps segs ms ms'
/\ match r with
| TS_ecall => st_ok_ecall segs (extK E K ws) (sh_ss st') ms'
| _ => st_ok segs (extK E K ws) (sh_ss st') ms'
end
/\ sh_ok (extK E K ws) (ms_mem ms')
/\ skeleton (ss_mem (sh_ss st')) = skeleton (ss_mem ss)
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n stop E ss ms st' r HS Hsh Hchk H Hfin. unfold sym_run_toN_tok in H.
destruct (sym_run_to_tok_sound_gen (sh_obls st') (N.to_nat n) stop E [] (start K Bx Bspan SH ss) ms st' r
(start_INV _ E ss ms HS Hsh Hchk Hfin) eq_refl H (doml_refl _)) as (ws & ms' & Hlen & Hms & HR & Hsk & Hfr & Hc).
cbn [app extK length start sh_ss sh_chk] in *. rewrite Hchk in Hc.
exists ws, ms'. split; [exact Hlen|]. split; [exact Hms|].
destruct r.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
- destruct HR as [HS' Hsh']. split; [exact HS'|]. split; [exact (Hsh' Hc)|]. auto.
- destruct HR as (HS' & _ & HC & _). split; [exact HS'|]. split; [exact (proj1 (proj2 (proj2 (HC Hc))))|]. auto.
Qed.
End g.
Ltac sym_why_tok segs tbl K Bx Bspan SH st :=
let r := eval vm_compute in (sym_step_tok segs tbl K Bx Bspan SH st) in
lazymatch r with
| TStop ?why => why
| _ => fail "sym_why_tok: state is not stuck"
end.
