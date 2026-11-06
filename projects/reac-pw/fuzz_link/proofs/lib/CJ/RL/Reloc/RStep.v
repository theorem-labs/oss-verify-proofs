(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable option.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import PropExec MState Mem Cells Exec Step Image SysStep.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fetch_dec (segs : list Segment) (pc : word) : option (instr * Z) :=
  match fetch_word segs pc with
  | Some w => if is_ecall w then Some (Ecall, 4%Z)
              else match decode_any w with Some (Ecall, _) => None | d => d end
  | None => None
  end.

Lemma fetch_dec_inv : forall segs pc i sz, fetch_dec segs pc = Some (i, sz) -> i <> Ecall ->
  exists w, fetch_word segs pc = Some w /\ is_ecall w = false /\ decode_any w = Some (i, sz).
Proof.
  intros segs pc i sz H NE. unfold fetch_dec in H.
  destruct (fetch_word segs pc) as [w|]; [|discriminate].
  destruct (is_ecall w) eqn:E.
  - inversion H; subst. congruence.
  - exists w. split; [reflexivity|]. split; [exact E|].
    destruct (decode_any w) as [[j k]|] eqn:D; [|discriminate].
    destruct j; cbv beta iota in H; first [exact H | discriminate].
Qed.

Lemma fetch_dec_ecall : forall segs pc, fetch_dec segs pc = Some (Ecall, 4%Z) ->
  exists w, fetch_word segs pc = Some w /\ is_ecall w = true.
Proof.
  intros segs pc H. unfold fetch_dec in H.
  destruct (fetch_word segs pc) as [w|]; [|discriminate].
  destruct (is_ecall w) eqn:E; [exists w; auto|].
  destruct (decode_any w) as [[j k]|]; [|discriminate]. destruct j; cbv beta iota in H; discriminate.
Qed.

Definition prog := list (Z * (instr * Z)).

Fixpoint find_off (off : Z) (p : prog) : option (instr * Z) :=
  match p with
  | [] => None
  | (o, x) :: p' => if Z.eqb o off then Some x else find_off off p'
  end.

(* [comment removed for export] *)
Definition code_at (segs : list Segment) (B : Z) (p : prog) : Prop :=
  forall off x, find_off off p = Some x -> fetch_dec segs (Z_to_bv 64 (B + off)) = Some x.

Lemma code_at_fetch : forall segs B p off x,
  code_at segs B p -> find_off off p = Some x -> fetch_dec segs (Z_to_bv 64 (B + off)) = Some x.
Proof. intros segs B p off x H F. exact (H off x F). Qed.

Lemma code_at_fetch0 : forall segs B p x,
  code_at segs B p -> find_off 0 p = Some x -> fetch_dec segs (Z_to_bv 64 B) = Some x.
Proof. intros segs B p x H F. rewrite <- (Z.add_0_r B). exact (H 0%Z x F). Qed.

(* [comment removed for export] *)
Definition code_checkb (segs : list Segment) (B : Z) (p : prog) : bool :=
  forallb (fun ox => bool_decide (fetch_dec segs (Z_to_bv 64 (B + fst ox)) = Some (snd ox))) p.

Lemma find_off_In : forall off p x, find_off off p = Some x -> In (off, x) p.
Proof.
  intros off p x. induction p as [|[o y] p IH]; cbn; [discriminate|].
  destruct (Z.eqb_spec o off) as [->|_]; intros H.
  - inversion H; subst. left. reflexivity.
  - right. apply IH, H.
Qed.

Lemma code_checkb_ok : forall segs B p, code_checkb segs B p = true -> code_at segs B p.
Proof.
  intros segs B p H off x F. apply find_off_In in F. unfold code_checkb in H.
  rewrite forallb_forall in H. specialize (H (off, x) F). cbn [fst snd] in H.
  apply bool_decide_eq_true in H. exact H.
Qed.

(* [comment removed for export] *)
Inductive ptree : Type := PLeaf (p : prog) | PNode (s : Z) (l r : ptree).

Fixpoint find_t (off : Z) (t : ptree) : option (instr * Z) :=
  match t with
  | PLeaf p => find_off off p
  | PNode s l r => if Z.ltb off s then find_t off l else find_t off r
  end.

Fixpoint flat_t (t : ptree) : prog :=
  match t with PLeaf p => p | PNode _ l r => flat_t l ++ flat_t r end.

Definition code_at_t (segs : list Segment) (B : Z) (t : ptree) : Prop :=
  forall off x, find_t off t = Some x -> fetch_dec segs (Z_to_bv 64 (B + off)) = Some x.

Lemma find_t_In : forall t off x, find_t off t = Some x -> In (off, x) (flat_t t).
Proof.
  induction t as [p|s l IHl r IHr]; intros off x H; cbn in *.
  - apply find_off_In. exact H.
  - apply in_or_app. destruct (Z.ltb off s); [left; apply IHl | right; apply IHr]; exact H.
Qed.

Lemma code_checkb_t_ok : forall segs B t, code_checkb segs B (flat_t t) = true -> code_at_t segs B t.
Proof.
  intros segs B t H off x F. apply find_t_In in F. unfold code_checkb in H.
  rewrite forallb_forall in H. specialize (H (off, x) F). cbn [fst snd] in H.
  apply bool_decide_eq_true in H. exact H.
Qed.

Lemma code_at_t_fetch : forall segs B t off x,
  code_at_t segs B t -> find_t off t = Some x -> fetch_dec segs (Z_to_bv 64 (B + off)) = Some x.
Proof. intros segs B t off x H F. exact (H off x F). Qed.

Lemma code_at_t_fetch0 : forall segs B t x,
  code_at_t segs B t -> find_t 0 t = Some x -> fetch_dec segs (Z_to_bv 64 B) = Some x.
Proof. intros segs B t x H F. rewrite <- (Z.add_0_r B). exact (H 0%Z x F). Qed.

(* [comment removed for export] *)
Lemma code_at_app_l : forall segs B p1 p2, code_at segs B (p1 ++ p2) ->
  (forall off x, find_off off p1 = Some x -> find_off off (p1 ++ p2) = Some x) -> code_at segs B p1.
Proof. intros segs B p1 p2 H K off x F. apply H, K, F. Qed.

(* [comment removed for export] *)
Class RImg := { img_segs : list Segment; sym : Z -> Z }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hi_q (d : Z) : Z := ((d + 2048) / 4096)%Z.
Definition hi20 (d : Z) : bv 20 := Z_to_bv 20 (hi_q d).
Definition lo12 (d : Z) : bv 12 := Z_to_bv 12 (d - hi_q d * 4096).
(* [comment removed for export] *)
Definition jimm21 (d : Z) : bv 21 := Z_to_bv 21 d.
Definition bimm13 (d : Z) : bv 13 := Z_to_bv 13 d.

Lemma lo12_signed : forall d, bv_signed (lo12 d) = (d - hi_q d * 4096)%Z.
Proof.
  intros d. unfold lo12. rewrite Z_to_bv_signed. apply bv_swrap_small.
  change (bv_half_modulus 12) with 2048%Z. unfold hi_q. Z.div_mod_to_equations. lia.
Qed.

Lemma hi20_signed : forall d, (- 2^31 <= d + 2048 < 2^31)%Z -> bv_signed (hi20 d) = hi_q d.
Proof.
  intros d Hd. unfold hi20. rewrite Z_to_bv_signed. apply bv_swrap_small.
  change (bv_half_modulus 20) with (2^19)%Z. unfold hi_q. Z.div_mod_to_equations. lia.
Qed.

Lemma jimm21_signed : forall d, (- 2^20 <= d < 2^20)%Z -> bv_signed (jimm21 d) = d.
Proof.
  intros d Hd. unfold jimm21. rewrite Z_to_bv_signed. apply bv_swrap_small.
  change (bv_half_modulus 21) with (2^20)%Z. lia.
Qed.

Lemma bimm13_signed : forall d, (- 2^12 <= d < 2^12)%Z -> bv_signed (bimm13 d) = d.
Proof.
  intros d Hd. unfold bimm13. rewrite Z_to_bv_signed. apply bv_swrap_small.
  change (bv_half_modulus 13) with (2^12)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma pcrel_pair : forall d P, (- 2^31 <= d + 2048 < 2^31)%Z ->
  (Z.shiftl (bv_signed (hi20 d)) 12 + P + bv_signed (lo12 d) = P + d)%Z.
Proof.
  intros d P Hd. rewrite hi20_signed by exact Hd. rewrite lo12_signed.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 12)%Z with 4096%Z. lia.
Qed.

Lemma add_sub_cancel : forall x y, (x + (y - x) = y)%Z.
Proof. intros. lia. Qed.

(* [comment removed for export] *)
Definition rel_code (B L : Z) : Prop := (0 <= B /\ B + L <= 2^30 /\ B mod 2 = 0)%Z.
Definition rel_sym (K : Z) : Prop := (0 <= K < 2^30)%Z.
(* [comment removed for export] *)
Definition rel_near (B C : Z) : Prop := (0 <= C < 2^30 /\ - 2^19 <= C - B < 2^19)%Z.

(* [comment removed for export] *)
Lemma ro_cells_image_cells : forall segs m G cs,
  mem_inv segs m -> ro_bytes_b segs G (cells_bytes cs) = true -> cells_wf cs ->
  (0 <= G)%Z -> (G + Z.of_nat (length (cells_bytes cs)) <= 2^64)%Z ->
  ro_cells segs m G cs.
Proof.
  intros segs m G cs MI RO WF H0 H1. split; [exact WF|].
  apply ro_bytes_at; try assumption. apply ro_bytes_b_sound. exact RO.
Qed.

(* [comment removed for export] *)
Lemma sx32_small : forall e, (- 2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. f_equal. rewrite Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2^64)%Z. change (bv_half_modulus 32) with (2^31)%Z.
  change (bv_modulus 32) with (2^32)%Z.
  destruct (Z_le_gt_dec 0 e) as [H0|H0].
  - rewrite (Z.mod_small e (2^64)) by lia. rewrite Z.mod_small by lia. lia.
  - assert (E1 : (e mod 2^64 = e + 2^64)%Z).
    { rewrite <- (Z_mod_plus_full e 1). rewrite Z.mod_small by lia. lia. }
    rewrite E1.
    assert (E2 : ((e + 2^64 + 2^31) mod 2^32 = e + 2^31)%Z).
    { replace (e + 2^64 + 2^31)%Z with ((e + 2^31) + 2^32 * 2^32)%Z by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
    rewrite E2. lia.
Qed.

Lemma sub_add_cancel : forall x y, (x - y + y = x)%Z.
Proof. intros. lia. Qed.

(* [comment removed for export] *)
Class CodeAt (segs : list Segment) (B : Z) (p : prog) : Prop := code_at_pf : code_at segs B p.
Class CodeAtT (segs : list Segment) (B : Z) (t : ptree) : Prop := code_at_t_pf : code_at_t segs B t.
Class RoB (segs : list Segment) (G : Z) (bs : list byte) : Prop := ro_b_pf : ro_bytes_b segs G bs = true.
Class RelCode (B L : Z) : Prop := rel_code_pf : rel_code B L.
Class RelSym (K : Z) : Prop := rel_sym_pf : rel_sym K.
Class RelNear (B C : Z) : Prop := rel_near_pf : rel_near B C.
Class ZFact (P : Prop) : Prop := zfact_pf : P.

(* [comment removed for export] *)
Lemma ret_pc_sym : forall z, (0 <= z < 2^64)%Z -> (z mod 2 = 0)%Z -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. exact ret_pc_even. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section L.
  Variable segs : list Segment.

  Lemma step_gen_dec : forall R F pc fc rv m ro i sz,
    fetch_dec segs pc = Some (i, sz) -> i <> Ecall ->
    RiscvSemantics.step segs (MS R F pc fc rv m ro) =
    lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m).
  Proof.
    intros R F pc fc rv m ro i sz FD NE. destruct (fetch_dec_inv _ _ _ _ FD NE) as (w & Hf & He & Hd).
    exact (step_gen segs R F pc fc rv m ro w i sz Hf He Hd).
  Qed.

  Ltac fd_ev L := intros; lazymatch goal with FD : fetch_dec _ _ = Some _ |- _ =>
    destruct (fetch_dec_inv _ _ _ _ FD ltac:(discriminate)) as (w & Hf & He & Hd); eapply L; eassumption end.

  Lemma aevt_OpImm : forall Q R F pc fc rv m ro op rd rs (imm : bv 12) v pc',
    fetch_dec segs pc = Some (OpImm op rd rs imm, 4%Z) ->
    is_x0 rd = false ->
    alu64 op (if is_x0 rs then w0 else reg_get R rs) (sext 64 imm) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_OpImm segs). Qed.

  Lemma aevt_ShiftImm : forall Q R F pc fc rv m ro op rd rs (sh : bv 6) v pc',
    fetch_dec segs pc = Some (ShiftImm op rd rs sh, 4%Z) ->
    is_x0 rd = false ->
    alu64 op (if is_x0 rs then w0 else reg_get R rs) (zext 64 sh) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_ShiftImm segs). Qed.

  Lemma aevt_Op : forall Q R F pc fc rv m ro op rd rs1 rs2 v pc',
    fetch_dec segs pc = Some (Op op rd rs1 rs2, 4%Z) ->
    is_x0 rd = false ->
    alu64 op (if is_x0 rs1 then w0 else reg_get R rs1) (if is_x0 rs2 then w0 else reg_get R rs2) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Op segs). Qed.

  Lemma aevt_OpImm32 : forall Q R F pc fc rv m ro rd rs (imm : bv 12) v pc',
    fetch_dec segs pc = Some (OpImm32 rd rs imm, 4%Z) ->
    is_x0 rd = false ->
    sext 64 (alu32 ALU_ADD (low32 (if is_x0 rs then w0 else reg_get R rs)) (sext 32 imm)) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_OpImm32 segs). Qed.

  Lemma aevt_ShiftImm32 : forall Q R F pc fc rv m ro op rd rs (sh : bv 5) v pc',
    fetch_dec segs pc = Some (ShiftImm32 op rd rs sh, 4%Z) ->
    is_x0 rd = false ->
    sext 64 (alu32 op (low32 (if is_x0 rs then w0 else reg_get R rs)) (zext 32 sh)) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_ShiftImm32 segs). Qed.

  Lemma aevt_Op32 : forall Q R F pc fc rv m ro op rd rs1 rs2 v pc',
    fetch_dec segs pc = Some (Op32 op rd rs1 rs2, 4%Z) ->
    is_x0 rd = false ->
    sext 64 (alu32 op (low32 (if is_x0 rs1 then w0 else reg_get R rs1)) (low32 (if is_x0 rs2 then w0 else reg_get R rs2))) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Op32 segs). Qed.

  Lemma aevt_Mul : forall Q R F pc fc rv m ro op rd rs1 rs2 v pc',
    fetch_dec segs pc = Some (Mul op rd rs1 rs2, 4%Z) ->
    is_x0 rd = false ->
    mul_div op (if is_x0 rs1 then w0 else reg_get R rs1) (if is_x0 rs2 then w0 else reg_get R rs2) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Mul segs). Qed.

  Lemma aevt_Mul32 : forall Q R F pc fc rv m ro op rd rs1 rs2 v pc',
    fetch_dec segs pc = Some (Mul32 op rd rs1 rs2, 4%Z) ->
    is_x0 rd = false ->
    sext 64 (mul_div op (low32 (if is_x0 rs1 then w0 else reg_get R rs1)) (low32 (if is_x0 rs2 then w0 else reg_get R rs2))) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Mul32 segs). Qed.

  Lemma aevt_Lui : forall Q R F pc fc rv m ro rd (imm : bv 20) v pc',
    fetch_dec segs pc = Some (Lui rd imm, 4%Z) ->
    is_x0 rd = false ->
    sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Lui segs). Qed.

  Lemma aevt_Auipc : forall Q R F pc fc rv m ro rd (imm : bv 20) v pc',
    fetch_dec segs pc = Some (Auipc rd imm, 4%Z) ->
    is_x0 rd = false ->
    pc + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Auipc segs). Qed.

  Lemma aevt_Load : forall Q R F pc fc rv m ro msz sgn rd rs (imm : bv 12) a v pc',
    fetch_dec segs pc = Some (Load msz sgn rd rs imm, 4%Z) ->
    is_x0 rd = false ->
    (if is_x0 rs then w0 else reg_get R rs) + sext 64 imm = a ->
    match msz with
    | SZ1 => match ov_read_bytes segs m a (width_bytes 8) with Some bs => Some (if sgn then sext 64 (bv_extract 0 8 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))) | None => None end
    | SZ2 => match ov_read_bytes segs m a (width_bytes 16) with Some bs => Some (if sgn then sext 64 (bv_extract 0 16 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))) | None => None end
    | SZ4 => match ov_read_bytes segs m a (width_bytes 32) with Some bs => Some (if sgn then sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))) | None => None end
    | SZ8 => match ov_read_bytes segs m a (width_bytes 64) with Some bs => Some (bv_extract 0 64 (le_bytes_to_word bs)) | None => None end
    end = Some v ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS (bvmap_set rd v R) F pc' fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Load segs). Qed.

  Lemma aevt_Store : forall Q R F pc fc rv m ro msz rs1 rs2 (imm : bv 12) a a' bs rv' pc',
    fetch_dec segs pc = Some (Store msz rs1 rs2 imm, 4%Z) ->
    (if is_x0 rs1 then w0 else reg_get R rs1) + sext 64 imm = a ->
    match msz with
    | SZ1 => Z_to_le_bytes (width_bytes 8) (bv_unsigned (bv_extract 0 8 (if is_x0 rs2 then w0 else reg_get R rs2)))
    | SZ2 => Z_to_le_bytes (width_bytes 16) (bv_unsigned (bv_extract 0 16 (if is_x0 rs2 then w0 else reg_get R rs2)))
    | SZ4 => Z_to_le_bytes (width_bytes 32) (bv_unsigned (low32 (if is_x0 rs2 then w0 else reg_get R rs2)))
    | SZ8 => Z_to_le_bytes (width_bytes 64) (bv_unsigned (if is_x0 rs2 then w0 else reg_get R rs2))
    end = bs ->
    (store_ok segs m a (match msz with SZ1 => width_bytes 8 | SZ2 => width_bytes 16 | SZ4 => width_bytes 32 | SZ8 => width_bytes 64 end) = true /\ a = a') ->
    match rv with Some r => if (bv_unsigned r =? bv_unsigned a)%Z then None else Some r | None => None end = rv' ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS R F pc' fc rv' (write_to_mem m a' bs) ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Store segs). Qed.

  Lemma aevt_Branch : forall Q R F pc fc rv m ro bc rs1 rs2 (imm : bv 13) (cnd : bool) tgt pc',
    fetch_dec segs pc = Some (Branch bc rs1 rs2 imm, 4%Z) ->
    branch_taken bc (if is_x0 rs1 then w0 else reg_get R rs1) (if is_x0 rs2 then w0 else reg_get R rs2) = cnd ->
    pc + sext 64 imm = tgt ->
    pc + Z_to_bv 64 4 = pc' ->
    evt segs Q (MS R F (if cnd then tgt else pc') fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Branch segs). Qed.

  Lemma aevt_Jal : forall Q R F pc fc rv m ro rd (imm : bv 21) sz npc tgt,
    fetch_dec segs pc = Some (Jal rd imm, sz) ->
    is_x0 rd = false ->
    pc + Z_to_bv 64 sz = npc ->
    pc + sext 64 imm = tgt ->
    evt segs Q (MS (bvmap_set rd npc R) F tgt fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Jal segs). Qed.

  Lemma aevt_Jal_x0 : forall Q R F pc fc rv m ro rd (imm : bv 21) sz tgt,
    fetch_dec segs pc = Some (Jal rd imm, sz) ->
    is_x0 rd = true ->
    pc + sext 64 imm = tgt ->
    evt segs Q (MS R F tgt fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Jal_x0 segs). Qed.

  Lemma aevt_Jalr : forall Q R F pc fc rv m ro rd rs (imm : bv 12) sz npc tgt,
    fetch_dec segs pc = Some (Jalr rd rs imm, sz) ->
    is_x0 rd = false ->
    pc + Z_to_bv 64 sz = npc ->
    bv_and ((if is_x0 rs then w0 else reg_get R rs) + sext 64 imm) (bv_not w1) = tgt ->
    evt segs Q (MS (bvmap_set rd npc R) F tgt fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Jalr segs). Qed.

  Lemma aevt_Jalr_x0 : forall Q R F pc fc rv m ro rd rs (imm : bv 12) sz tgt,
    fetch_dec segs pc = Some (Jalr rd rs imm, sz) ->
    is_x0 rd = true ->
    bv_and ((if is_x0 rs then w0 else reg_get R rs) + sext 64 imm) (bv_not w1) = tgt ->
    evt segs Q (MS R F tgt fc rv m ro) -> evt segs Q (MS R F pc fc rv m ro).
  Proof. fd_ev (evt_Jalr_x0 segs). Qed.
  Lemma aevt_ecall : forall (Q : machine_state -> Prop) R F pc fc rv m ro,
    fetch_dec segs pc = Some (Ecall, 4%Z) ->
    Q (MSsvc R F pc (reg_get R 17) fc rv m ro) ->
    evt segs Q (MS R F pc fc rv m ro).
  Proof.
    intros Q R F pc fc rv m ro FD HQ. destruct (fetch_dec_ecall _ _ FD) as (w & Hf & He).
    eapply evt_step; [|apply evt_done; exact HQ].
    split; [reflexivity|]. rewrite (step_ecall_gen segs R F pc fc rv m ro w Hf He). reflexivity.
  Qed.
End L.
