(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_m7de.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lit_offset_ok k :=
  let ok := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 8192))%bool in
  lazymatch ok with true => idtac end.

Ltac solve_load_guarded :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        lit_offset_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        lit_offset_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store_guarded :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        lit_offset_ok k;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Ltac solve_load ::= first [solve_load_guarded | solve_load_image].
Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac eval_lit_tests :=
  repeat match goal with
  | |- context [negb (Z.eqb (Z.modulo ?a ?b) 0%Z)] =>
      let a' := zlit a in let v := eval vm_compute in (negb (Z.eqb (Z.modulo a b) 0%Z)) in
      change (negb (Z.eqb (Z.modulo a b) 0%Z)) with v
  end;
  repeat match goal with
  | |- context [Z.eqb ?a ?b] =>
      let a' := zlit a in let b' := zlit b in let v := eval vm_compute in (Z.eqb a b) in change (Z.eqb a b) with v
  end;
  repeat match goal with
  | |- context [negb true] => change (negb true) with false
  | |- context [negb false] => change (negb false) with true
  end;
  cbv beta iota.

(* [comment removed for export] *)
Ltac fold_xlit t :=
  let z' := eval vm_compute in (bv_unsigned t) in
  rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity).
Ltac fold_xlits :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z; fold_xlit constr:(sx32 (Z_to_bv 64 z))
  | |- context [zx32 (Z_to_bv 64 ?z)] => is_Zlit z; fold_xlit constr:(zx32 (Z_to_bv 64 z))
  | |- context [sx16 (Z_to_bv 64 ?z)] => is_Zlit z; fold_xlit constr:(sx16 (Z_to_bv 64 z))
  | |- context [zx16 (Z_to_bv 64 ?z)] => is_Zlit z; fold_xlit constr:(zx16 (Z_to_bv 64 z))
  | |- context [sx8 (Z_to_bv 64 ?z)] => is_Zlit z; fold_xlit constr:(sx8 (Z_to_bv 64 z))
  | |- context [zx8 (Z_to_bv 64 ?z)] => is_Zlit z; fold_xlit constr:(zx8 (Z_to_bv 64 z))
  | |- context [sxb (Z_to_bv 8 ?z)] => is_Zlit z; fold_xlit constr:(sxb (Z_to_bv 8 z))
  | |- context [zxb (Z_to_bv 8 ?z)] => is_Zlit z; fold_xlit constr:(zxb (Z_to_bv 8 z))
  | |- context [Z.b2z (Z.ltb ?a ?b)] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (Z.ltb a b)) in change (Z.b2z (Z.ltb a b)) with v
  | |- context [Z.b2z (Z.leb ?a ?b)] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (Z.leb a b)) in change (Z.b2z (Z.leb a b)) with v
  | |- context [Z.b2z (Z.eqb ?a ?b)] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.b2z (Z.eqb a b)) in change (Z.b2z (Z.eqb a b)) with v
  | |- context [Z.modulo ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.shiftr ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  end.

(* [comment removed for export] *)
Lemma le1_single : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.
Ltac fix_le1_lit :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      is_Zlit z; rewrite (le1_single (Z_to_bv 64 z)); fold_lit_ux
  | _ => idtac
  end.

Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; cbv beta iota zeta delta [amo_aligned amo_bytes]; simp_is_x0; simp_regs; fold_lit_ux; fold_xlits;
          eval_lit_tests; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; try fix_lit_store; fix_le1_lit; mem_after_store_opt; post_step i; fold_xlits ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.
Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
Ltac azstep := astep; zsimp.

(* [comment removed for export] *)
Ltac brstep := first [zstep | if_false | if_true].
Ltac bstep := first [azstep | if_false | if_true].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstep end).
Ltac at_pc pc :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ ?pc' _ _ _ _) => fail "not at pc" pc "but" pc'
  end.
(* [comment removed for export] *)
Ltac br_taken := let K := fresh "K" in if_cases K; zify_cond K; [ clear K | exfalso; lia ].
Ltac br_not_taken := let K := fresh "K" in if_cases K; zify_cond K; [ exfalso; lia | clear K ].

(* [comment removed for export] *)
Ltac lit_addrs :=
  repeat match goal with
  | H : context [Z.add ?a ?b] |- _ => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H
  end.

(* [comment removed for export] *)
Lemma land7_of_mod8 : forall x, 0 <= x -> x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x Hx Hm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact Hm. Qed.
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. rewrite Z.mod_small by lia. lia.
Qed.
Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hz. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac post_call_z segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  rewrite ?unsigned_lit in MUc by lia;
  try rewrite ?unsigned_lit in PO by lia;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "callz" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call_z segs m ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r%Z)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac show_regs :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ ?pc _ ?rv _ _) =>
      let v10 := reg_val 10%Z in let v11 := reg_val 11%Z in let v12 := reg_val 12%Z in let v13 := reg_val 13%Z in
      idtac "pc=" pc "a0=" v10 "a1=" v11 "a2=" v12 "a3=" v13 "rv=" rv
  | |- ?g => idtac "GOAL:" g
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memset_post_z (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D c n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 (c mod 256)) (Z.to_nat n))].

Lemma memset_spec_z : forall ra sp gp tp t0 t1 t2 s0 s1 (D c n : Z) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m D [CB (Z.to_nat n) junk] ->
  0 <= n -> 0 <= c < 2^64 -> D + n < 2^64 ->
  mem_inv rsegs m ->
  evt rsegs (memset_post_z ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D c n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 c) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa25c8) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST N0 C DHI MI.
  pose proof (rw_cells_bound _ _ _ _ DST) as B2. cbn [cells_size csize Nat.add] in B2.
  rewrite Nat.add_0_r, Z2Nat.id in B2 by lia.
  assert (U0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (U1 : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (memset_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk);
      rewrite ?U0, ?U2; [exact DST | exact MI]. }
  intros ms' PO. unfold memset_post in PO. unfold memset_post_z.
  (first [ dex15 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m'; dand5 PO as E MU WM MI' RW | dand20 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m' E MU WM MI' RW | destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & RW) ]).
  rewrite ?U0, ?U1, ?U2 in *.
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. exact RW.
Qed.
