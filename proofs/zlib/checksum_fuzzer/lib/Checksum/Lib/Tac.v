(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Export ExN.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac is_concrete_map R ::=
  lazymatch R with
  | TNode _ _ _ => idtac
  | TEmpty => idtac
  | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.
Ltac map_cbv_get ::= cbv beta iota delta [tget mkR].
Ltac map_cbv_set ::= cbv beta iota delta [tset mkR].

(* [comment removed for export] *)
Ltac solve_load_image :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
      let E := addr_expr a in
      let Ez := zlit E in
      lazymatch goal with
      | HI : mem_inv segs m |- _ =>
          let obs := eval vm_compute in (image_bytes segs Ez n) in
          lazymatch obs with
          | Some ?bs =>
              let RO := fresh "ROimg" in
              assert (RO : ro_cells segs m Ez [CB n bs])
                by (apply (ro_cells_image segs m Ez bs HI); [vm_compute; reflexivity | lia | cbn; lia]);
              rewrite (ro_cells_read_at segs m Ez [CB n bs] 0%nat (CB n bs) n a RO)
                by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
              clear RO; load_post
          | None => fail "no readable image bytes at" Ez
          end
      end
  end.
Ltac solve_load ::= first [ solve_load_base | solve_load_image ].

(* [comment removed for export] *)
Ltac simpl_arr_sizes := rewrite ?u32s_length, ?u64s_length, ?upd_length in *.
Ltac transport_chunks segs m a bs ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

(* [comment removed for export] *)
Ltac footprint_after_store segs m a bs :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Lemma le8_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 8 z = le8 (Z_to_bv 64 z).
Proof. intros z Hz. rewrite <- store_bytes_8'. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le4_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 4 z = le4 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le4. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le2_lit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 2 z = le2 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le2. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma le1_zlit : forall z, (0 <= z < 2^64)%Z -> Z_to_le_bytes 1 z = le1 (Z_to_bv 64 z).
Proof. intros z Hz. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.
Ltac fix_lit_store :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac mem_after_store_opt ::=
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac   (* [comment removed for export] *)
      end
  | _ => idtac
  end.

Ltac fstep := step.

Ltac fsteps n :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; fsteps n'
      | _ => idtac
      end
  end.

(* [comment removed for export] *)
Ltac destruct_exs PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let x := fresh "x" in destruct PO as [x PO]; destruct_exs PO
  | _ => idtac
  end.

Ltac destruct_ands PO :=
  lazymatch type of PO with
  | _ /\ _ => let H := fresh "PC" in destruct PO as [H PO]; destruct_ands PO
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac footprint_starts_at W A :=
  lazymatch W with context [(A, _)] => idtac end.
Ltac transport_after_call segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : rw_cells segs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  | H : u8arr segs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  | H : bytes_at segs m ?A2 _ |- _ => footprint_starts_at W A2; clear H
  end;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
Ltac post_call segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  (* [comment removed for export] *)
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Tactic Notation "call" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call segs m ]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac carve_frame n ST :=
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi =>
      let junk := fresh "junk" in let FR := fresh "FR" in let ST' := fresh "ST" in
      destruct (stk_carve segs m lo hi n ST ltac:(lia)) as [ST' [junk FR]];
      clear ST; rename ST' into ST;
      let z := eval vm_compute in (Z.of_nat n) in
      change (Z.of_nat n) with z in ST, FR;
      (* [comment removed for export] *)
      repeat match type of FR with
      | context [Z.sub (Z.add ?b ?c) ?d] => is_Zlit c; is_Zlit d; let v := eval vm_compute in (c - d)%Z in
           replace (Z.sub (Z.add b c) d) with (Z.add b v) in * by lia
      | context [Z.sub ?b ?d] => is_Zlit d; let v := eval vm_compute in (- d)%Z in
           replace (Z.sub b d) with (Z.add b v) in * by lia
      end
  end.

(* [comment removed for export] *)
Fixpoint mk_CB_cells (sizes : list nat) (bs : list byte) : list cell :=
  match sizes with
  | [] => []
  | s :: sizes' => CB s (firstn s bs) :: mk_CB_cells sizes' (skipn s bs)
  end.

Fixpoint sum_nat (l : list nat) : nat := match l with [] => 0 | x :: l' => x + sum_nat l' end.

Lemma mk_CB_cells_wf : forall sizes bs, length bs = sum_nat sizes -> cells_wf (mk_CB_cells sizes bs).
Proof.
  induction sizes as [|s sizes IH]; intros bs H; cbn; [exact I|].
  cbn in H. split.
  - rewrite firstn_length. lia.
  - apply IH. rewrite skipn_length. lia.
Qed.

Lemma mk_CB_cells_bytes : forall sizes bs, length bs = sum_nat sizes -> cells_bytes (mk_CB_cells sizes bs) = bs.
Proof.
  induction sizes as [|s sizes IH]; intros bs H; cbn in *.
  - destruct bs; [reflexivity| cbn in H; lia].
  - rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed.

Lemma mk_CB_cells_size : forall sizes bs, cells_size (mk_CB_cells sizes bs) = sum_nat sizes.
Proof. induction sizes; intros; cbn; [reflexivity|]. rewrite IHsizes. reflexivity. Qed.

Lemma rw_cells_split_CB : forall segs m A pre n junk post sizes,
  rw_cells segs m A (pre ++ CB n junk :: post) -> sum_nat sizes = n ->
  rw_cells segs m A (pre ++ mk_CB_cells sizes junk ++ post).
Proof.
  intros segs m A pre n junk post sizes [[Hwf Hb] Hw] Hs.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  assert (L : length junk = sum_nat sizes) by lia.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [apply mk_CB_cells_wf; exact L| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite mk_CB_cells_bytes by exact L. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite mk_CB_cells_size, Hs. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_merge : forall segs m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post).
Proof.
  intros segs m A pre mid post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 H23]. apply cells_wf_app in H23. destruct H23 as [H2 H3].
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. cbn. split; [apply cells_bytes_length; exact H2| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes]. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize]. exact Hw.
Qed.

Lemma rw_cells_forget : forall segs m A cs,
  rw_cells segs m A cs -> exists junk, rw_cells segs m A [CB (cells_size cs) junk].
Proof.
  intros segs m A cs H. exists (cells_bytes cs).
  pose proof (rw_cells_merge segs m A [] cs [] ) as M. rewrite app_nil_r in M. cbn [app] in M. apply M. exact H.
Qed.

(* [comment removed for export] *)
Ltac finish :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P end;
  hnf;
  hot_eexists_all;   (* [comment removed for export] *)
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.AndN.and_splits;   (* [comment removed for export] *)
  try assumption.

(* [comment removed for export] *)
Ltac release_frame FR ST hi :=
  eapply stk_release in FR; [ | exact ST | lia ];
  clear ST; rename FR into ST;
  cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia
  end.

(* [comment removed for export] *)
Ltac store_done :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    (lazymatch a with
     | wa _ => idtac
     | Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
     | _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
     end);
    (* [comment removed for export] *)
    try (lazymatch goal with
    | HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI;
        [ | first [ exact HS
                  | replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
                    first [ exact HS | simpl_sizes; exact HS ] ] ]
    end);
    (* [comment removed for export] *)
    let HBa := fresh "HBarr" in
    try (let X := lazymatch E with Z.add (Z.add ?X _) _ => X | Z.add ?X _ => X | _ => E end in
         first [ lazymatch goal with
                 | H : u32arr segs m X ?xs |- _ => pose proof (u32arr_bound segs m X xs H) as HBa
                 | H : u8arr segs m X ?xs |- _ => pose proof (u8arr_bound segs m X xs H) as HBa
                 | H : u64arr segs m X ?xs |- _ => pose proof (u64arr_bound segs m X xs H) as HBa
                 end
               | lazymatch E with Z.add (Z.add ?X2 _) _ =>
                   lazymatch goal with
                   | H : u32arr segs m X2 ?xs |- _ => pose proof (u32arr_bound segs m X2 xs H) as HBa
                   | H : u8arr segs m X2 ?xs |- _ => pose proof (u8arr_bound segs m X2 xs H) as HBa
                   | H : u64arr segs m X2 ?xs |- _ => pose proof (u64arr_bound segs m X2 xs H) as HBa
                   end
                 end ]);
    transport_chunks segs m E bs;
    footprint_after_store segs m E bs;
    try clear HBa;
    let m' := fresh "m" in
    remember (write_to_mem m (wa E) bs) as m' eqn:Heqm;
    clear Heqm;
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    try clear m
  end.
