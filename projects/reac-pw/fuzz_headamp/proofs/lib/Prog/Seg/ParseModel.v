(** The parts of the cuts of reac_headamp_prop_parse_result's walk that are the same in both builds: the call record,
    the saved-register cells, the FP condition, the params Struct and its children, the key slot, and the model read
    one pair at a time. Prog/Seg/ParseCut.v (plain) and U/Prog/Seg/ParseCut.v (UBSan) export this file and add the
    build's frame layout, memory predicate and cut statements. Statement text and model steps only; no function of a
    binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Accessors Spa SpaBool Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
Import ListNotations.
Open Scope Z_scope.

(** ** The call *)
(** The caller's ra, sp, gp, tp and s0 .. s11, the memory at the call, and the contract's lo, P (the pod), O (out),
    cap, R (res), bs, ev, can. *)
Record pctx := PCtx {
  c_ra : word; c_sp : word; c_gp : word; c_tp : word;
  c_s0 : word; c_s1 : word; c_s2 : word; c_s3 : word; c_s4 : word; c_s5 : word;
  c_s6 : word; c_s7 : word; c_s8 : word; c_s9 : word; c_s10 : word; c_s11 : word;
  c_m : word -> option byte;
  c_lo : Z; c_P : Z; c_O : Z; c_cap : Z; c_R : Z; c_bs : list byte; c_ev : word; c_can : word }.

(** Read the fields of a destructed call record. *)
Ltac pc_simpl :=
  cbn [c_ra c_sp c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_m c_lo c_P c_O c_cap
       c_R c_bs c_ev c_can] in *.

(** The answer of a non-NULL call. *)
Definition RESM (c : pctx) : answer := parse_model (c_bs c) (c_cap c).

(** The saved registers s11 .. s0, ra, in this order at the top of the frame (plain spf + 0x38 .. spf + 0xa0, UBSan
    spf + 0x28 .. spf + 0x90). *)
Definition saves (c : pctx) : list Cells.cell :=
  [C8 (c_s11 c); C8 (c_s10 c); C8 (c_s9 c); C8 (c_s8 c); C8 (c_s7 c); C8 (c_s6 c); C8 (c_s5 c); C8 (c_s4 c);
   C8 (c_s3 c); C8 (c_s2 c); C8 (c_s1 c); C8 (c_s0 c); C8 (c_ra c)].

(** The FP state inside the walk: fs0 = +0.0 (`fmv.d.x fs0,zero` in the walk setup; strtol, strncmp and strcmp keep
    F) and rounding mode 0. *)
Definition fp_ok (F : bvmap 5 word) (fc : bv 32) : Prop :=
  Sem.reg_get F (Z_to_bv 5 8) = Z_to_bv 64 0 /\ frm0 fc.

(** ** The params Struct and its children *)
(** The params prop at offset r of the pod (found by the find loop: 16 <= r, r mod 8 = 0), its value a Struct of
    vs = u32_at bs (r + 8) < 2^20 bytes (spa_pod_is_struct) inside the pod; its body at r + 16. *)
Definition st_ok (c : pctx) (r : Z) : Prop :=
  16 <= r /\ r mod 8 = 0 /\ u32_at (c_bs c) (r + 8) < 2^20 /\
  r + 16 + u32_at (c_bs c) (r + 8) <= Z.of_nat (length (c_bs c)).

(** The child at offset cc lies inside the Struct body (spa_pod_is_inside, iter.h:31-37, passed). *)
Definition child_in (c : pctx) (r cc : Z) : Prop :=
  cc + 8 + u32_at (c_bs c) cc <= r + 16 + u32_at (c_bs c) (r + 8).

(** The pairs from the child at offset cc on, n passes of fuel, the key slot km (Pod/Headamp.v's parse_model on
    VPods: pairs_by spa_get_string over the Struct's children). *)
Definition walk_pairs (bs : list byte) (r cc : Z) (n : nat) (km : option (list byte)) : list (list byte * ent) :=
  pairs_by spa_get_string (map (child_at bs) (struct_children bs (r + 16) (u32_at bs (r + 8)) cc n)) km.

(** The key slot s6: 0 (open), or the address of the key string at offset kk of the pod. *)
Definition key_reg (c : pctx) (k : option Z) : word :=
  match k with None => Z_to_bv 64 0 | Some kk => Z_to_bv 64 (c_P c + kk) end.

(** The key slot's string: the C string sx at offset kk of the pod, its NUL inside the pod (spa_pod_get_string's
    last-byte test, body.h:234). *)
Definition key_ok (c : pctx) (k : option Z) (km : option (list byte)) : Prop :=
  match k, km with
  | None, None => True
  | Some kk, Some sx => 0 <= kk /\ kk + Z.of_nat (length sx) + 1 <= Z.of_nat (length (c_bs c)) /\ ~ In NUL sx /\
                        firstn (S (length sx)) (skipn (Z.to_nat kk) (c_bs c)) = sx ++ [NUL]
  | _, _ => False
  end.

(** ** The model, one pair at a time *)
(** value_pod_to_byte and value_in_range of a key whose verdict is the cell address (ch, p): parse_cell's KCell arm. *)
Definition vcell (ch p : Z) (v : ent) : Z + Headamp.cell :=
  match parse_value v with
  | Some b => if value_in_range p b then inr (ch, p, b) else inl REFUSE_OUT_OF_RANGE
  | None => inl REFUSE_OUT_OF_RANGE
  end.

(** ha_fold's step on a pair whose key has the prefix, from the pair's verdict x on. *)
Definition fold_after (cap : Z) (x : Z + Headamp.cell) (rest : list (list byte * ent)) (cl : list Headamp.cell)
    (keys rf : Z) : list Headamp.cell * Z * Z :=
  match x with
  | inl bad => ha_fold parse_cell cap rest cl (keys + 1) (if rf =? REFUSE_NONE then bad else rf)
  | inr cv => if cap <=? Z.of_nat (length cl) then (cl, keys + 1, rf)
              else ha_fold parse_cell cap rest (cl ++ [cv]) (keys + 1) rf
  end.

Lemma ha_fold_cons : forall cap k v rest cl keys rf,
  ha_fold parse_cell cap ((k, v) :: rest) cl keys rf =
  if ha_prefix k then fold_after cap (parse_cell k v) rest cl keys rf else ha_fold parse_cell cap rest cl keys rf.
Proof. intros. cbn [ha_fold]. destruct (ha_prefix k); reflexivity. Qed.

Lemma parse_cell_vcell : forall k v ch p,
  parse_key (skipn (length HA_PREFIX) k) = KCell ch p -> parse_cell k v = vcell ch p v.
Proof. intros k v ch p H. unfold parse_cell. rewrite H. reflexivity. Qed.

Lemma walk_pairs_step : forall bs r cc n km,
  walk_pairs bs r cc (S n) km =
  if pod_is_inside bs (r + 16) (u32_at bs (r + 8)) cc then
    match km with
    | None => walk_pairs bs r (cc + round_up8 (8 + u32_at bs cc)) n (spa_get_string (child_at bs cc))
    | Some k => (k, child_at bs cc) :: walk_pairs bs r (cc + round_up8 (8 + u32_at bs cc)) n None
    end
  else [].
Proof. intros. unfold walk_pairs. cbn [struct_children]. destruct (pod_is_inside _ _ _ _); reflexivity. Qed.
