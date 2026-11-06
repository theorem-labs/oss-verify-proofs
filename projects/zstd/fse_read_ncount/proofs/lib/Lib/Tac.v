(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Export ExElim.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac is_concrete_map R ::=
  lazymatch R with
  | TNode _ _ _ => idtac
  | TEmpty => idtac
  | mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
  end.
(* [comment removed for export] *)
Ltac map_cbv_get ::= lazymatch goal with |- ?G => let G' := eval cbv beta iota delta [tget mkR] in G in change_no_check G' end.
Ltac map_cbv_set ::= lazymatch goal with |- ?G => let G' := eval cbv beta iota delta [tset mkR] in G in change_no_check G' end.

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

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    let kz := eval vm_compute in (Z.of_nat kn) in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB; lit_of_nat_in HB;
          change (write_to_mem m (wa (A + Z.of_nat kn)) bs) with (write_to_mem m (wa (A + kz)) bs);   (* [comment removed for export] *)
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + kz)) c') in HI;
              [ | exact I
                | change (wa (A + kz)) with (wa (A + Z.of_nat kn));
                  apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          change (wa (A + Z.of_nat kn)) with (wa (A + kz)) in H';
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + kz)%Z (cbytes c');
          footprint_after_store segs m (A + kz)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + kz)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)
Ltac norm_lit_store_bytes :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           is_Zlit z; change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           is_Zlit z; change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]
       end).

Ltac mem_after_store_opt ::=
  norm_lit_store_bytes;
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
(* [comment removed for export] *)
Ltac destruct_exs_loop PO :=
  let T := type of PO in let T' := eval hnf in T in
  lazymatch T' with
  | ex _ => let x := fresh "x" in destruct PO as [x PO]; destruct_exs_loop PO
  | _ => idtac
  end.
Ltac destruct_exs PO :=
  diet_run ltac:(idtac; destruct_exs_loop PO) ltac:(idtac; ex_elim_hyp PO; destruct_exs_loop PO).

Ltac destruct_ands PO :=
  lazymatch type of PO with
  | _ /\ _ => let H := fresh "PC" in destruct PO as [H PO]; destruct_ands PO
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac transport_after_call segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
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
  - rewrite firstn_length. Local Ltac2 Set LiaHints.tbl := fun () => "0020=43991116490.562887682162.5000003006S1HS1H".
lia.
  - apply IH. rewrite skipn_length. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma mk_CB_cells_bytes : forall sizes bs, length bs = sum_nat sizes -> cells_bytes (mk_CB_cells sizes bs) = bs.
Proof.
  induction sizes as [|s sizes IH]; intros bs H; cbn in *.
  - Local Ltac2 Set LiaHints.tbl := fun () => "0020=62887682162.563919532770.3000003006S1HS1H".
destruct bs; [reflexivity| cbn in H; lia].
  - rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma mk_CB_cells_size : forall sizes bs, cells_size (mk_CB_cells sizes bs) = sum_nat sizes.
Proof. induction sizes; intros; cbn; [reflexivity|]. rewrite IHsizes. reflexivity. Qed.

Lemma rw_cells_split_CB : forall segs m A pre n junk post sizes,
  rw_cells segs m A (pre ++ CB n junk :: post) -> sum_nat sizes = n ->
  rw_cells segs m A (pre ++ mk_CB_cells sizes junk ++ post).
Proof.
  intros segs m A pre n junk post sizes [[Hwf Hb] Hw] Hs.
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>15675007370.14000007S2H22Hs".
assert (L : length junk = sum_nat sizes) by lia.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [apply mk_CB_cells_wf; exact L| exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite mk_CB_cells_bytes by exact L. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite mk_CB_cells_size, Hs. exact Hw.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

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
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
(* [comment removed for export] *)
Ltac2 Type u5lin := { l_atoms : (constr * int) list; l_const : int }.
Ltac2 rec u5_pos (xI : constr) (xO : constr) (c : constr) (depth : int) : int option :=
  if Int.lt 40 depth then None else
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f a =>
      if Int.equal (Array.length a) 1 then
        (match u5_pos xI xO (Array.get a 0) (Int.add depth 1) with
         | None => None
         | Some v => if Constr.equal f xI then Some (Int.add (Int.mul 2 v) 1)
                     else if Constr.equal f xO then Some (Int.mul 2 v) else None
         end)
      else None
  | Constr.Unsafe.Constructor _ _ => Some 1     (* [comment removed for export] *)
  | _ => None
  end.
Ltac2 Type u5heads := { h_add : constr; h_sub : constr; h_opp : constr; h_mul : constr; h_zpos : constr; h_zneg : constr;
                        h_z0 : constr; h_xI : constr; h_xO : constr; h_ofnat : constr; h_S : constr; h_O : constr }.
Ltac2 u5_heads () : u5heads :=
  { h_add := Env.instantiate reference:(Z.add); h_sub := Env.instantiate reference:(Z.sub); h_opp := Env.instantiate reference:(Z.opp);
    h_mul := Env.instantiate reference:(Z.mul); h_zpos := Env.instantiate reference:(Zpos); h_zneg := Env.instantiate reference:(Zneg);
    h_z0 := Env.instantiate reference:(Z0); h_xI := Env.instantiate reference:(xI); h_xO := Env.instantiate reference:(xO);
    h_ofnat := Env.instantiate reference:(Z.of_nat); h_S := Env.instantiate reference:(S); h_O := Env.instantiate reference:(O) }.
(* [comment removed for export] *)
Ltac2 rec u5_natlit (h : u5heads) (c : constr) (acc : int) : int option :=
  if Int.lt 100000 acc then None else
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f a => if Bool.and (Constr.equal f (h.(h_S))) (Int.equal (Array.length a) 1) then u5_natlit h (Array.get a 0) (Int.add acc 1) else None
  | _ => if Constr.equal c (h.(h_O)) then Some acc else None
  end.
Ltac2 u5_lit (h : u5heads) (c : constr) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f a =>
      if Int.equal (Array.length a) 1 then
        (if Constr.equal f (h.(h_zpos)) then u5_pos (h.(h_xI)) (h.(h_xO)) (Array.get a 0) 0
         else if Constr.equal f (h.(h_zneg)) then
           (match u5_pos (h.(h_xI)) (h.(h_xO)) (Array.get a 0) 0 with Some v => Some (Int.sub 0 v) | None => None end)
         else if Constr.equal f (h.(h_ofnat)) then u5_natlit h (Array.get a 0) 0
         else None)
      else None
  | _ => if Constr.equal c (h.(h_z0)) then Some 0 else None
  end.
Ltac2 rec u5_add_atom (a : constr) (k : int) (l : (constr * int) list) : (constr * int) list :=
  match l with
  | [] => [(a, k)]
  | p :: r => let (b, j) := p in if Constr.equal a b then (b, Int.add j k) :: r else p :: u5_add_atom a k r
  end.
Ltac2 rec u5_merge (l1 : (constr * int) list) (l2 : (constr * int) list) : (constr * int) list :=
  match l1 with [] => l2 | p :: r => let (a, k) := p in u5_merge r (u5_add_atom a k l2) end.
Ltac2 u5_scale (k : int) (x : u5lin) : u5lin :=
  { l_atoms := List.map (fun p => let (a, j) := p in (a, Int.mul k j)) (x.(l_atoms)); l_const := Int.mul k (x.(l_const)) }.
Ltac2 u5_plus (x : u5lin) (y : u5lin) : u5lin :=
  { l_atoms := u5_merge (x.(l_atoms)) (y.(l_atoms)); l_const := Int.add (x.(l_const)) (y.(l_const)) }.
Ltac2 rec u5_linz (h : u5heads) (c : constr) (depth : int) : u5lin :=
  let atom () := { l_atoms := [(c, 1)]; l_const := 0 } in
  if Int.lt 30 depth then atom () else
  match u5_lit h c with
  | Some v => { l_atoms := []; l_const := v }
  | None =>
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f a =>
        let n := Array.length a in
        if Bool.and (Int.equal n 2) (Constr.equal f (h.(h_add))) then
          u5_plus (u5_linz h (Array.get a 0) (Int.add depth 1)) (u5_linz h (Array.get a 1) (Int.add depth 1))
        else if Bool.and (Int.equal n 2) (Constr.equal f (h.(h_sub))) then
          u5_plus (u5_linz h (Array.get a 0) (Int.add depth 1)) (u5_scale (Int.sub 0 1) (u5_linz h (Array.get a 1) (Int.add depth 1)))
        else if Bool.and (Int.equal n 1) (Constr.equal f (h.(h_opp))) then
          u5_scale (Int.sub 0 1) (u5_linz h (Array.get a 0) (Int.add depth 1))
        else if Bool.and (Int.equal n 2) (Constr.equal f (h.(h_mul))) then
          (match u5_lit h (Array.get a 0) with
           | Some k => u5_scale k (u5_linz h (Array.get a 1) (Int.add depth 1))
           | None => match u5_lit h (Array.get a 1) with
                     | Some k => u5_scale k (u5_linz h (Array.get a 0) (Int.add depth 1))
                     | None => atom () end
           end)
        else atom ()
    | _ => atom ()
    end
  end.
Ltac2 rec u5_coeff (a : constr) (l : (constr * int) list) : int :=
  match l with [] => 0 | p :: r => let (b, j) := p in if Constr.equal a b then j else u5_coeff a r end.
Ltac2 u5_same_atoms (l1 : (constr * int) list) (l2 : (constr * int) list) : bool :=
  Bool.and (List.for_all (fun p => let (a, k) := p in Int.equal k (u5_coeff a l2)) l1)
           (List.for_all (fun p => let (a, k) := p in Int.equal k (u5_coeff a l1)) l2).
(* [comment removed for export] *)
Ltac2 u5_lin_neq (e : constr) (e' : constr) : bool :=
  let h := u5_heads () in
  let x := u5_linz h e 0 in
  let y := u5_linz h e' 0 in
  if u5_same_atoms (x.(l_atoms)) (y.(l_atoms)) then
    (let d := Int.sub (x.(l_const)) (y.(l_const)) in
     Bool.and (Bool.neg (Int.equal d 0)) (Bool.and (Int.lt d 1000000000000) (Int.lt (Int.sub 0 1000000000000) d)))
  else false.
Ltac u5_lin_compat E E' :=
  let f := ltac2:(e e' |- if u5_lin_neq (Option.get (Ltac1.to_constr e)) (Option.get (Ltac1.to_constr e')) then Control.zero (Tactic_failure None) else ()) in
  f E E'.
(* [comment removed for export] *)
Ltac u5_addr_compat E a' :=
  let E' := addr_expr a' in
  tryif (let k := addr_diff E E' in
         let z := eval vm_compute in (Z.eqb (Z.modulo k 18446744073709551616) 0) in
         lazymatch z with false => idtac | true => fail end)
  then fail else u5_lin_compat E E'.

Ltac solve_load_base_u5 :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let inr := eval vm_compute in (Z.leb 0 k && Z.ltb k (Z.of_nat (cells_size cs0)))%bool in
        lazymatch inr with true => idtac | false => fail end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let inr := eval vm_compute in (Z.leb 0 k && Z.ltb k (Z.of_nat (cells_size cs0)))%bool in
        lazymatch inr with true => idtac | false => fail end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        u5_addr_compat E a';                                   (* [comment removed for export] *)
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.
Ltac solve_load_u5 := first [ solve_load_base_u5 | solve_load_image ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zify_new_dm_u5 x y :=
  lazymatch goal with
  | _ : zify_done x y |- _ => fail
  | _ =>
      lazymatch y with
      | Zpos _ =>
          pose proof (Z.div_mod x y ltac:(discriminate));
          pose proof (Z.mod_pos_bound x y (@eq_refl comparison Lt));
          pose proof (I : zify_done x y)
      | Zneg _ =>
          pose proof (Z.div_mod x y ltac:(discriminate));
          pose proof (Z.mod_neg_bound x y (@eq_refl comparison Lt));
          pose proof (I : zify_done x y)
      | _ =>
          pose proof (Z.div_mod x y); pose proof (Z.mod_pos_bound x y); pose proof (Z.mod_neg_bound x y);
          pose proof (Z.div_0_r_ext x y); pose proof (Z.mod_0_r_ext x y);
          pose proof (I : zify_done x y)
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac flia_u5 :=
  first [ sassumption
        | lazymatch goal with
          | x := _ : Z |- _ => first [ slim; lia | lia ]
          | |- _ => lia
          end
        | assumption ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 u5_zify_heads () : constr list :=
  [Env.instantiate reference:(Z.add); Env.instantiate reference:(Z.sub); Env.instantiate reference:(Z.mul); Env.instantiate reference:(Z.opp);
   Env.instantiate reference:(Z.div); Env.instantiate reference:(Z.modulo); Env.instantiate reference:(Z.pow); Env.instantiate reference:(Z.of_nat);
   Env.instantiate reference:(Z.to_nat); Env.instantiate reference:(Z.max); Env.instantiate reference:(Z.min); Env.instantiate reference:(Z.abs);
   Env.instantiate reference:(Z.succ); Env.instantiate reference:(Z.pred); Env.instantiate reference:(Z.quot); Env.instantiate reference:(Z.rem);
   Env.instantiate reference:(Z.of_N); Env.instantiate reference:(Z.sgn); Env.instantiate reference:(Zpos); Env.instantiate reference:(Zneg);
   Env.instantiate reference:(Z.shiftl); Env.instantiate reference:(Z.shiftr); Env.instantiate reference:(Z.land); Env.instantiate reference:(Z.lor);
   Env.instantiate reference:(Z.lxor); Env.instantiate reference:(Z.b2z); Env.instantiate reference:(bv_unsigned); Env.instantiate reference:(bv_signed);
   Env.instantiate reference:(bv_wrap); Env.instantiate reference:(bv_swrap); Env.instantiate reference:(Z.lnot)].
Ltac2 rec u5_cmem (c : constr) (l : constr list) : bool :=
  match l with [] => false | x :: r => if Constr.equal c x then true else u5_cmem c r end.
(* [comment removed for export] *)
Ltac2 rec u5_occurs (e : constr) (t : constr) (fuel : int array) : bool :=
  if Int.lt (Array.get fuel 0) 0 then true else      (* [comment removed for export] *)
  (Array.set fuel 0 (Int.sub (Array.get fuel 0) 1);
   if Constr.equal e t then true else
   match Constr.Unsafe.kind t with
   | Constr.Unsafe.App f a => if u5_occurs e f fuel then true else Array.exist (fun x => u5_occurs e x fuel) a
   | Constr.Unsafe.Prod b c => if u5_occurs e (Constr.Binder.type b) fuel then true else u5_occurs e c fuel
   | Constr.Unsafe.Lambda b c => if u5_occurs e (Constr.Binder.type b) fuel then true else u5_occurs e c fuel
   | Constr.Unsafe.LetIn b v c => if u5_occurs e (Constr.Binder.type b) fuel then true else if u5_occurs e v fuel then true else u5_occurs e c fuel
   | Constr.Unsafe.Cast c _ _ => u5_occurs e c fuel
   | _ => false
   end).
Ltac2 u5_unbounded_atom (e : constr) : bool :=
  match Constr.Unsafe.kind e with
  | Constr.Unsafe.App f _ =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant _ _ =>
           if u5_cmem f (u5_zify_heads ()) then false
           else (let fuel := Array.make 1 200000 in
                 Bool.neg (List.exist (fun h => let (_, body, ty) := h in
                     if u5_occurs e ty fuel then true else match body with Some b => u5_occurs e b fuel | None => false end)
                   (Control.hyps ())))
       | _ => false
       end)
  | _ => false
  end.
(* [comment removed for export] *)
Ltac u5_boundable e :=
  let f := ltac2:(e |- if u5_unbounded_atom (Option.get (Ltac1.to_constr e)) then Control.zero (Tactic_failure None) else ()) in f e.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 u5_arith_heads () : constr list :=
  [Env.instantiate reference:(Logic.eq); Env.instantiate reference:(Z.le); Env.instantiate reference:(Z.lt); Env.instantiate reference:(Z.ge);
   Env.instantiate reference:(Z.gt); Env.instantiate reference:(and); Env.instantiate reference:(or); Env.instantiate reference:(not);
   Env.instantiate reference:(iff); Env.instantiate reference:(Peano.le); Env.instantiate reference:(Peano.lt); Env.instantiate reference:(N.le);
   Env.instantiate reference:(N.lt); Env.instantiate reference:(Z.divide); Env.instantiate reference:(Peano.ge); Env.instantiate reference:(Peano.gt)].
Ltac2 u5_num_types () : constr list := [constr:(Z); constr:(nat); constr:(N)].
Ltac2 u5_head_of (t : constr) : constr := match Constr.Unsafe.kind t with Constr.Unsafe.App f _ => f | _ => t end.
Ltac2 u5_unbounded_atom2 (e : constr) : bool :=
  match Constr.Unsafe.kind e with
  | Constr.Unsafe.App f _ =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant _ _ =>
           if u5_cmem f (u5_zify_heads ()) then false
           else (let fuel := Array.make 1 200000 in
                 let ah := u5_arith_heads () in let nt := u5_num_types () in
                 Bool.neg (List.exist (fun h => let (_, body, ty) := h in
                     match body with
                     | Some b => if u5_cmem ty nt then u5_occurs e b fuel else false
                     | None => if u5_cmem (u5_head_of ty) ah then u5_occurs e ty fuel else false
                     end)
                   (Control.hyps ())))
       | _ => false
       end)
  | _ => false
  end.
Ltac u5_boundable2 e :=
  let f := ltac2:(e |- if u5_unbounded_atom2 (Option.get (Ltac1.to_constr e)) then Control.zero (Tactic_failure None) else ()) in f e.

Ltac zrange_u5 :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange_u5 | zrange_nonneg_u5] | apply zr_land_r; [zrange_nonneg_u5 | zrange_u5] ]
      | Z.lor _ _ => apply zr_lor; [zrange_u5 | zrange_u5]
      | Z.lxor _ _ => apply zr_lxor; [zrange_u5 | zrange_u5]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange_u5 | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange_u5 | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange_u5 | zrange_u5]
      | _ => first [ apply zr_lit; tryif u5_boundable2 e then flia else first [ sassumption | assumption ]   (* [comment removed for export] *)
                   | is_var e; progress (unfold e); zrange_u5 ]
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange_u5
  end
with zrange_nonneg_u5 :=
  lazymatch goal with
  | |- (0 <= ?e)%Z =>
      first [ apply (proj1 (A:=(0 <= e)%Z) (B:=(e < 2^64)%Z)); change (inr64 e); zrange_u5
            | apply Z.land_nonneg; left; zrange_nonneg_u5
            | apply Z.lor_nonneg; split; zrange_nonneg_u5
            | apply Z.lxor_nonneg; split; zrange_nonneg_u5
            | apply Z.shiftr_nonneg; zrange_nonneg_u5
            | apply Z.shiftl_nonneg; zrange_nonneg_u5
            | flia
            | is_var e; progress (unfold e); zrange_nonneg_u5 ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 u5_arith_hyps () : ident list :=
  let st := rv4_new () in
  List.map_filter (fun h => let (id, body, ty) := h in
     match body with
     | Some _ => None
     | None =>
         let (pl, pr) := rv4_class st ty in
         if (if Int.equal pr 2 then rv4_is_prop st ty else Int.equal pr 1) then
           (if pl then Some id
            else match Constr.Unsafe.kind ty with
                 | Constr.Unsafe.App _ _ => (* [comment removed for export] *) Some id
                 | Constr.Unsafe.Prod _ _ => None
                 | _ => None
                 end)
         else None
     end) (Control.hyps ()).
(* [comment removed for export] *)
Ltac2 u5_on_length_hyps (len : constr) (tac : Ltac1.t) : unit :=
  let fuel () := Array.make 1 20000 in
  List.iter (fun id =>
     let ty := Constr.type (Control.hyp id) in
     if u5_occurs len ty (fuel ()) then
       Ltac1.apply tac [Ltac1.of_ident id] Ltac1.run
     else ()) (u5_arith_hyps ()).
Ltac u5_arr_in_hyps tacH :=
  let f := ltac2:(t |- u5_on_length_hyps (Env.instantiate reference:(Datatypes.length)) t) in f tacH.
(* [comment removed for export] *)
Ltac simpl_arr_sizes_u5 :=
  rewrite ?u32s_length, ?u64s_length, ?upd_length;
  u5_arr_in_hyps ltac:(fun H => rewrite ?u32s_length, ?u64s_length, ?upd_length in H).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 u5_closed_false () : bool :=
  let h := u5_heads () in
  let g := Control.goal () in
  let test (a : constr) (b : constr) (rel : int -> bool) :=
    let x := u5_linz h a 0 in let y := u5_linz h b 0 in
    if u5_same_atoms (x.(l_atoms)) (y.(l_atoms)) then Bool.neg (rel (Int.sub (x.(l_const)) (y.(l_const)))) else false in
  lazy_match! g with
  | @eq Z ?a ?b => test a b (fun d => Int.equal d 0)
  | Z.le ?a ?b => test a b (fun d => Int.le d 0)
  | Z.lt ?a ?b => test a b (fun d => Int.lt d 0)
  | Z.ge ?a ?b => test a b (fun d => Int.ge d 0)
  | Z.gt ?a ?b => test a b (fun d => Int.gt d 0)
  | _ => false
  end.
Ltac u5_guard_cf := ltac2:(Control.enter (fun () => if u5_closed_false () then Control.zero (Tactic_failure None) else ())).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac flia_k12 := first [ sassumption | slim; lia | lia | assumption ].
Ltac slia_k12 := first [ exact I | lia | split; [lia|exact I] ].
Ltac solve_load_k12 := first [ solve_load_base | solve_load_image ].
Ltac simpl_arr_sizes_k12 := rewrite ?u32s_length, ?u64s_length, ?upd_length in *.
Ltac zrange_k12 :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange_k12 | zrange_nonneg_k12] | apply zr_land_r; [zrange_nonneg_k12 | zrange_k12] ]
      | Z.lor _ _ => apply zr_lor; [zrange_k12 | zrange_k12]
      | Z.lxor _ _ => apply zr_lxor; [zrange_k12 | zrange_k12]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange_k12 | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange_k12 | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange_k12 | zrange_k12]
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange_k12 ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange_k12
  end
with zrange_nonneg_k12 :=
  lazymatch goal with
  | |- (0 <= ?e)%Z =>
      first [ apply (proj1 (A:=(0 <= e)%Z) (B:=(e < 2^64)%Z)); change (inr64 e); zrange_k12
            | apply Z.land_nonneg; left; zrange_nonneg_k12
            | apply Z.lor_nonneg; split; zrange_nonneg_k12
            | apply Z.lxor_nonneg; split; zrange_nonneg_k12   (* [comment removed for export] *)
            | apply Z.shiftr_nonneg; zrange_nonneg_k12
            | apply Z.shiftl_nonneg; zrange_nonneg_k12
            | flia
            | is_var e; progress (unfold e); zrange_nonneg_k12 ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac word_eq_tac_k12 :=
  first [ exact eq_refl
        | f_equal; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
Ltac word_eq_tac_u5 :=
  first [ exact eq_refl
        | f_equal; first [ u5_t0 | u5_p1 ]
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].

Ltac slia ::= slia_u5.
Ltac flia ::= flia_u5.
Ltac zrange ::= zrange_u5.
Ltac zrange_nonneg ::= zrange_nonneg_u5.
Ltac solve_load ::= solve_load_u5.
Ltac zify_new_dm ::= zify_new_dm_u5.
Ltac simpl_arr_sizes ::= simpl_arr_sizes_u5.
Ltac word_eq_tac ::= word_eq_tac_u5.   (* [comment removed for export] *)
Close Scope Z_scope.
