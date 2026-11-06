(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export PropExec MState Mem Cells Exec Step Frame Arr Image Diet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.   (* [comment removed for export] *)
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

Ltac mem_after_store_tac0 :=
  norm_lit_store_bytes;
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
          rmx_set (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) m';
          clear HB; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store ::= mem_after_store_tac0.

Ltac mem_after_store_opt ::=
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
Ltac destruct_exs PO := nd_destruct_exs PO.

Ltac destruct_ands PO := nd_destruct_ands PO.

(* [comment removed for export] *)
Ltac transport_after_call_tac0 segs m m' MU WM :=
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
Ltac transport_after_call segs m m' MU WM := transport_after_call_tac0 segs m m' MU WM.

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
    rmx_set (write_to_mem m (wa E) bs) m';
    repeat match goal with
    | H : store_ok segs m _ _ = true |- _ => clear H
    | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
    end;
    try clear m
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.

(* [comment removed for export] *)
Ltac simpl_sizes_step0 :=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].
Ltac simpl_arr_sizes_tac0 := rewrite ?u32s_length, ?u64s_length, ?upd_length in *.

Definition sl_hide (P : Prop) : Prop := P.

Section WithSegs.
Variable segs : list Segment.
#[using="Type"] Lemma sl_bytes_at_write_other : forall m a bs c cs (n : Z),
  sl_hide (Z.of_nat (length bs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  bytes_at segs m c cs -> (c + Z.of_nat (length cs) <= a \/ a + n <= c)%Z -> bytes_at segs (write_to_mem m (wa a) bs) c cs.
Proof. unfold sl_hide. intros m a bs c cs n <- Ha Hl H Hd. apply bytes_at_write_other; assumption. Qed.
#[using="Type"] Lemma sl_rw_cells_frame : forall m A cs (a : Z) bs (n : Z),
  sl_hide (Z.of_nat (length bs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. unfold sl_hide. intros m A cs a bs n <- Ha Hl H Hd. apply rw_cells_frame; assumption. Qed.
#[using="Type"] Lemma sl_ro_cells_frame : forall m A cs (a : Z) bs (n : Z),
  sl_hide (Z.of_nat (length bs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs (write_to_mem m (wa a) bs) A cs.
Proof. unfold sl_hide. intros m A cs a bs n <- Ha Hl H Hd. apply ro_cells_frame; assumption. Qed.
#[using="Type"] Lemma sl_u8arr_frame : forall m A bs a xs (n : Z),
  sl_hide (Z.of_nat (length xs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length xs) <= 2^64)%Z ->
  u8arr segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> u8arr segs (write_to_mem m (wa a) xs) A bs.
Proof. unfold sl_hide. intros m A bs a xs n <- Ha Hl H Hd. apply u8arr_frame; assumption. Qed.
#[using="Type"] Lemma sl_u32arr_frame : forall m A ws a xs (n : Z),
  sl_hide (Z.of_nat (length xs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length xs) <= 2^64)%Z ->
  u32arr segs m A ws -> (A + 4 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z -> u32arr segs (write_to_mem m (wa a) xs) A ws.
Proof. unfold sl_hide. intros m A ws a xs n <- Ha Hl H Hd. apply u32arr_frame; assumption. Qed.
#[using="Type"] Lemma sl_u64arr_frame : forall m A ws a xs (n : Z),
  sl_hide (Z.of_nat (length xs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length xs) <= 2^64)%Z ->
  u64arr segs m A ws -> (A + 8 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z -> u64arr segs (write_to_mem m (wa a) xs) A ws.
Proof. unfold sl_hide. intros m A ws a xs n <- Ha Hl H Hd. apply u64arr_frame; assumption. Qed.
#[using="Type"] Lemma sl_u8ro_frame : forall m A bs a xs (n : Z),
  sl_hide (Z.of_nat (length xs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length xs) <= 2^64)%Z ->
  u8ro segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> u8ro segs (write_to_mem m (wa a) xs) A bs.
Proof. unfold sl_hide. intros m A bs a xs n <- Ha Hl H Hd. apply u8ro_frame; assumption. Qed.
#[using="Type"] Lemma sl_stk_write : forall m lo hi a bs,
  sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  stk segs m lo hi -> stk segs (write_to_mem m (wa a) bs) lo hi.
Proof. unfold sl_hide. intros m lo hi a bs Ha Hl H. apply stk_write; assumption. Qed.
End WithSegs.
Lemma sl_munch_write : forall W m0 m a bs (n : Z),
  sl_hide (Z.of_nat (length bs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  munch W m0 m -> inside W a n -> munch W m0 (write_to_mem m (wa a) bs).
Proof. unfold sl_hide. intros W m0 m a bs n <- Ha Hl H Hin. apply munch_write; assumption. Qed.

(* [comment removed for export] *)
Section WithSegsNamed.
Variable segs : list Segment.
#[using="Type"] Lemma slm_bytes_at_write_other : forall m m' a bs c cs (n : Z),
  sl_hide (m' = write_to_mem m (wa a) bs) ->
  sl_hide (Z.of_nat (length bs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  bytes_at segs m c cs -> (c + Z.of_nat (length cs) <= a \/ a + n <= c)%Z -> bytes_at segs m' c cs.
Proof. unfold sl_hide. intros m m' a bs c cs n -> Hn Ha Hl H Hd. eapply sl_bytes_at_write_other; eassumption. Qed.
#[using="Type"] Lemma slm_wr_at_write : forall m m' a n c bs,
  sl_hide (m' = write_to_mem m c bs) -> wr_at segs m a n -> wr_at segs m' a n.
Proof. unfold sl_hide. intros m m' a n c bs ->. apply wr_at_write. Qed.
#[using="Type"] Lemma slm_rw_cells_frame : forall m m' A cs (a : Z) bs (n : Z),
  sl_hide (m' = write_to_mem m (wa a) bs) ->
  sl_hide (Z.of_nat (length bs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof. unfold sl_hide. intros m m' A cs a bs n -> Hn Ha Hl H Hd. eapply sl_rw_cells_frame; eassumption. Qed.
#[using="Type"] Lemma slm_ro_cells_frame : forall m m' A cs (a : Z) bs (n : Z),
  sl_hide (m' = write_to_mem m (wa a) bs) ->
  sl_hide (Z.of_nat (length bs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof. unfold sl_hide. intros m m' A cs a bs n -> Hn Ha Hl H Hd. eapply sl_ro_cells_frame; eassumption. Qed.
#[using="Type"] Lemma slm_u8arr_frame : forall m m' A bs a xs (n : Z),
  sl_hide (m' = write_to_mem m (wa a) xs) ->
  sl_hide (Z.of_nat (length xs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length xs) <= 2^64)%Z ->
  u8arr segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> u8arr segs m' A bs.
Proof. unfold sl_hide. intros m m' A bs a xs n -> Hn Ha Hl H Hd. eapply sl_u8arr_frame; eassumption. Qed.
#[using="Type"] Lemma slm_u32arr_frame : forall m m' A ws a xs (n : Z),
  sl_hide (m' = write_to_mem m (wa a) xs) ->
  sl_hide (Z.of_nat (length xs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length xs) <= 2^64)%Z ->
  u32arr segs m A ws -> (A + 4 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z -> u32arr segs m' A ws.
Proof. unfold sl_hide. intros m m' A ws a xs n -> Hn Ha Hl H Hd. eapply sl_u32arr_frame; eassumption. Qed.
#[using="Type"] Lemma slm_u64arr_frame : forall m m' A ws a xs (n : Z),
  sl_hide (m' = write_to_mem m (wa a) xs) ->
  sl_hide (Z.of_nat (length xs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length xs) <= 2^64)%Z ->
  u64arr segs m A ws -> (A + 8 * Z.of_nat (length ws) <= a \/ a + n <= A)%Z -> u64arr segs m' A ws.
Proof. unfold sl_hide. intros m m' A ws a xs n -> Hn Ha Hl H Hd. eapply sl_u64arr_frame; eassumption. Qed.
#[using="Type"] Lemma slm_u8ro_frame : forall m m' A bs a xs (n : Z),
  sl_hide (m' = write_to_mem m (wa a) xs) ->
  sl_hide (Z.of_nat (length xs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length xs) <= 2^64)%Z ->
  u8ro segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> u8ro segs m' A bs.
Proof. unfold sl_hide. intros m m' A bs a xs n -> Hn Ha Hl H Hd. eapply sl_u8ro_frame; eassumption. Qed.
#[using="Type"] Lemma slm_stk_write : forall m m' lo hi a bs,
  sl_hide (m' = write_to_mem m (wa a) bs) ->
  sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  stk segs m lo hi -> stk segs m' lo hi.
Proof. unfold sl_hide. intros m m' lo hi a bs -> Ha Hl H. apply stk_write; assumption. Qed.
#[using="Type"] Lemma slm_wmono_write : forall m0 m m' a bs,
  sl_hide (m' = write_to_mem m a bs) -> wmono segs m0 m -> wmono segs m0 m'.
Proof. unfold sl_hide. intros m0 m m' a bs ->. apply wmono_write. Qed.
#[using="Type"] Lemma slm_mem_inv_store_cbytes : forall m m' a c',
  sl_hide (m' = write_to_mem m a (cbytes c')) ->
  mem_inv segs m -> cell_wf c' -> store_ok segs m a (csize c') = true -> mem_inv segs m'.
Proof. unfold sl_hide. intros m m' a c' ->. apply mem_inv_store_cbytes. Qed.
#[using="Type"] Lemma slm_rw_cells_write : forall m m' A cs k c c',
  sl_hide (m' = write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) ->
  rw_cells segs m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
  rw_cells segs m' A (cell_upd cs k c').
Proof. unfold sl_hide. intros m m' A cs k c c' ->. apply rw_cells_write. Qed.
End WithSegsNamed.
Lemma slm_munch_write : forall W m0 m m' a bs (n : Z),
  sl_hide (m' = write_to_mem m (wa a) bs) ->
  sl_hide (Z.of_nat (length bs) = n) -> sl_hide (0 <= a)%Z -> sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z ->
  munch W m0 m -> inside W a n -> munch W m0 m'.
Proof. unfold sl_hide. intros W m0 m m' a bs n -> Hn Ha Hl H Hin. eapply sl_munch_write; eassumption. Qed.


(* [comment removed for export] *)
Module SLit.
  Import Ltac2.
  Ltac2 rec is_numeral (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if Constr.equal f constr:(S) then is_numeral (Array.get args 0) else false)
        else false
    | Constr.Unsafe.Constructor _ _ => Constr.equal c constr:(O)
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 rec arith_visible (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h _ =>
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant _ _ =>
            if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(Z.le) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(Z.lt) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(Z.ge) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(Z.gt) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(lt) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(ge) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(gt) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(N.le) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(N.lt) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(N.ge) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(N.gt) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(Pos.le) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(Pos.lt) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(Z.divide) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(not) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(iff) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(is_true) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(Is_true) then true
            else false
        | Constr.Unsafe.Ind _ _ =>
            if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(and) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(or) then true
            else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(eq) then true else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.lt_is_ref h reference:(le) then true
            else false
        | _ => false
        end
    | Constr.Unsafe.Prod _ _ => true
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 on_arith_hyps (tac : Ltac1.t) : unit :=
    List.iter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => ()
                 | None => if arith_visible ty then Ltac1.apply tac [Ltac1.of_constr (Control.hyp id)] Ltac1.run else ()
                 end) (Control.hyps ()).
  Ltac2 check_numeral (n : Ltac1.t) : unit :=
    match Ltac1.to_constr n with
    | Some c => if is_numeral c then () else Control.zero (Tactic_failure None)
    | None => Control.zero (Tactic_failure None)
    end.
End SLit.
Ltac sl_is_natlit n := let f := ltac2:(n |- SLit.check_numeral n) in f n.
Ltac sl_spine_closed cs :=
  lazymatch cs with
  | nil => idtac
  | cons ?c ?tl =>
      lazymatch c with C8 _ => idtac | C4 _ => idtac | C2 _ => idtac | C1 _ => idtac | CB ?n _ => sl_is_natlit n end;
      sl_spine_closed tl
  end.
Ltac sl_lit_sizes :=
  repeat match goal with
  | |- context [cells_size ?cs] =>
      sl_spine_closed cs;
      let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
      change (cells_size cs) with n
  end.
Ltac sl_lit_sizes_in H :=
  repeat match type of H with
  | context [cells_size ?cs] =>
      sl_spine_closed cs;
      let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
      change (cells_size cs) with n in H
  end.
(* [comment removed for export] *)
Ltac release_frame FR ST hi ::=
  eapply stk_release in FR; [ | exact ST | lia ];
  clear ST; rename FR into ST;
  sl_lit_sizes_in ST;
  cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia
  end.

Ltac simpl_sizes ::=
  lazymatch goal with |- context [@length _ _] => rewrite ?app_length | _ => idtac end;
  sl_lit_sizes;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  lazymatch goal with
  | |- context [@length _ _] => rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length]
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sl_arr_rw_in H := rewrite ?u32s_length, ?u64s_length, ?upd_length in H.
Ltac simpl_arr_sizes ::=
  (let f := ltac2:(t |- SLit.on_arith_hyps t) in f sl_arr_rw_in);
  rewrite ?u32s_length, ?u64s_length, ?upd_length.

(* [comment removed for export] *)
Ltac sl_is_poslit p := lazymatch p with xH => idtac | xO ?q => sl_is_poslit q | xI ?q => sl_is_poslit q end.
(* [comment removed for export] *)
Ltac sl_len_lit bs :=
  let n0 := constr:(Z.of_nat (length bs)) in
  let n1 := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
                      Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in n0 in
  lazymatch n1 with
  | Z0 => n1
  | Zpos ?p => let ok := constr:(ltac:(first [ sl_is_poslit p; exact true | exact false ])) in
               lazymatch ok with true => n1 | false => n0 end
  | _ => n0
  end.

(* [comment removed for export] *)
Ltac sl_transport_chunks_old segs m a bs :=
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
Ltac sl_footprint_old segs m a bs :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Ltac sl_transport_chunks_with segs m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (sl_bytes_at_write_other segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (sl_rw_cells_frame segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (sl_ro_cells_frame segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u8arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u32arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u64arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u8ro_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.
Ltac sl_footprint_with segs m a bs n Hn Ha Hl :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (sl_munch_write Wq mq m a bs n Hn Ha Hl) in MU; [ | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (sl_stk_write segs m loq hiq a bs Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac sl_with_facts a bs kf ko :=
  let Hn := fresh "Hn_sl" in let Ha := fresh "Ha_sl" in let Hl := fresh "Hl_sl" in
  let n := sl_len_lit bs in
  tryif (assert (Ha : sl_hide (0 <= a)%Z) by (unfold sl_hide; lia);
         assert (Hl : sl_hide (a + Z.of_nat (length bs) <= 2^64)%Z) by (unfold sl_hide; simpl_sizes; slia);
         assert (Hn : sl_hide (Z.of_nat (length bs) = n)) by (unfold sl_hide; exact eq_refl))
  then (kf n Hn Ha Hl; clear Hn Ha Hl)
  else ko tt.

Ltac transport_chunks segs m a bs ::=
  sl_with_facts a bs ltac:(fun n Hn Ha Hl => sl_transport_chunks_with segs m a bs n Hn Ha Hl)
                     ltac:(fun _ => sl_transport_chunks_old segs m a bs).
Ltac footprint_after_store segs m a bs ::=
  sl_with_facts a bs ltac:(fun n Hn Ha Hl => sl_footprint_with segs m a bs n Hn Ha Hl)
                     ltac:(fun _ => sl_footprint_old segs m a bs).

Ltac slm_transport_chunks_with segs m m' Heq a bs n Hn Ha Hl :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (slm_bytes_at_write_other segs m m' a bs A2 bs2 n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (slm_wr_at_write segs m m' A2 n2 (wa a) bs Heq) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u32arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u64arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8ro_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.
Ltac slm_footprint_with segs m m' Heq a bs n Hn Ha Hl :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (slm_munch_write Wq mq m m' a bs n Heq Hn Ha Hl) in MU; [ | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (slm_wmono_write segs mq m m' (wa a) bs Heq) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (slm_stk_write segs m m' loq hiq a bs Heq Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac sl_mas_old_tail segs m A kn bs c' cs c0 H HB :=
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
  sl_transport_chunks_old segs m (A + Z.of_nat kn)%Z (cbytes c');
  sl_footprint_old segs m (A + Z.of_nat kn)%Z (cbytes c');
  let m' := fresh "m" in
  remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
  clear Heqm; clear HB; try clear m; try rename H' into H.

(* [comment removed for export] *)
Ltac sl_store_extra m m' a bs n Hn Ha Hl CH := idtac.
Ltac sl_mas_new_tail segs m A kn bs c' cs c0 H HB n' Hn Ha Hl :=
  (* [comment removed for export] *)
  change bs with (cbytes c');
  let m' := fresh "m" in
  set (m' := write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c'));
  let Heq := fresh "Heq_sl" in
  assert (Heq : sl_hide (m' = write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c'))) by exact (eq_refl m');
  try lazymatch goal with
  | HI : mem_inv segs m |- _ =>
      apply (slm_mem_inv_store_cbytes segs m m' (wa (A + Z.of_nat kn)) c' Heq) in HI;
      [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
  end;
  let H' := fresh "CH" in
  pose proof (slm_rw_cells_write segs m m' A cs kn c0 c' Heq H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
  clear H;
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
  slm_transport_chunks_with segs m m' Heq (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
  sl_store_extra m m' (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl H';
  slm_footprint_with segs m m' Heq (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
  clear Heq Hn Ha Hl; clearbody m';
  clear HB; try clear m; try rename H' into H.

Ltac mem_after_store ::=
  norm_lit_store_bytes;
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
          pose proof (rw_cells_bound segs m A cs H) as HB; sl_lit_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
          let Hn := fresh "Hn_sl" in let Ha := fresh "Ha_sl" in let Hl := fresh "Hl_sl" in
          let a := constr:((A + Z.of_nat kn)%Z) in
          let n' := sl_len_lit (cbytes c') in
          tryif (assert (Ha : sl_hide (0 <= a)%Z) by (unfold sl_hide; lia);
                 assert (Hl : sl_hide (a + Z.of_nat (length (cbytes c')) <= 2^64)%Z) by (unfold sl_hide; simpl_sizes; slia);
                 assert (Hn : sl_hide (Z.of_nat (length (cbytes c')) = n')) by (unfold sl_hide; exact eq_refl))
          then sl_mas_new_tail segs m A kn bs c' cs c0 H HB n' Hn Ha Hl
          else sl_mas_old_tail segs m A kn bs c' cs c0 H HB
        end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module FF.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 rec is_pos (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if Bool.or (Constr.equal f constr:(xO)) (Constr.equal f constr:(xI)) then is_pos (Array.get args 0) else false)
        else false
    | Constr.Unsafe.Constructor _ _ => Constr.equal c constr:(xH)
    | _ => false
    end.
  Ltac2 is_zlit (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if Bool.or (Constr.equal f constr:(Zpos)) (Constr.equal f constr:(Zneg)) then is_pos (Array.get args 0) else false)
        else false
    | Constr.Unsafe.Constructor _ _ => Constr.equal c constr:(Z0)
    | _ => false
    end.
  Ltac2 rec is_natlit (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if Constr.equal f constr:(S) then is_natlit (Array.get args 0) else false)
        else false
    | Constr.Unsafe.Constructor _ _ => Constr.equal c constr:(O)
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 rec lin (sg : bool) (c : constr) (acc : (constr * bool) list * (constr * bool) list)
    : (constr * bool) list * (constr * bool) list :=
    let (ats, cs) := acc in
    if is_zlit c then (ats, (c, sg) :: cs) else
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 2 then
          (if Constr.equal f constr:(Z.add) then lin sg (Array.get args 1) (lin sg (Array.get args 0) acc)
           else if Constr.equal f constr:(Z.sub) then lin (Bool.neg sg) (Array.get args 1) (lin sg (Array.get args 0) acc)
           else ((c, sg) :: ats, cs))
        else if Int.equal (Array.length args) 1 then
          (if Constr.equal f constr:(Z.opp) then lin (Bool.neg sg) (Array.get args 0) acc
           else if Bool.and (Constr.equal f constr:(Z.of_nat)) (is_natlit (Array.get args 0)) then (ats, (c, sg) :: cs)
           else ((c, sg) :: ats, cs))
        else ((c, sg) :: ats, cs)
    | _ => ((c, sg) :: ats, cs)
    end.
  (* [comment removed for export] *)
  Ltac2 rec remove1 (a : constr) (sg : bool) (l : (constr * bool) list) : ((constr * bool) list) option :=
    match l with
    | [] => None
    | x :: tl => let (b, sb) := x in
        if Bool.and (Bool.equal sb sg) (Constr.equal a b) then Some tl
        else match remove1 a sg tl with Some r => Some (x :: r) | None => None end
    end.
  (* [comment removed for export] *)
  Ltac2 rec cancel (l : (constr * bool) list) (r : (constr * bool) list) : bool :=
    match l with
    | [] => (match r with [] => true | _ :: _ => false end)
    | x :: tl => let (a, sg) := x in
        match remove1 a sg r with
        | Some r' => cancel tl r'
        | None => false
        end
    end.
  Ltac2 sum_consts (cs : (constr * bool) list) : constr :=
    List.fold_left (fun acc x => let (c, sg) := x in
                      if sg then constr:(Z.add $acc $c) else constr:(Z.sub $acc $c)) constr:(0%Z) cs.
  (* [comment removed for export] *)
  Ltac2 decide_cmp (strict : bool) (l : constr) (r : constr) : bool option :=
    let (la, lc) := lin true l ([], []) in
    let (ra, rc) := lin true r ([], []) in
    if cancel la ra then
      let cl := sum_consts lc in let cr := sum_consts rc in
      let t := if strict then constr:(Z.ltb $cl $cr) else constr:(Z.leb $cl $cr) in
      let v := Std.eval_vm None t in
      (if Constr.equal v constr:(true) then Some true else if Constr.equal v constr:(false) then Some false else None)
    else None.
  (* [comment removed for export] *)
  Ltac2 rec decided_false (p : constr) : bool :=
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 2 then
          (if Constr.equal f constr:(Z.le) then
             (match decide_cmp false (Array.get args 0) (Array.get args 1) with Some b => Bool.neg b | None => false end)
           else if Constr.equal f constr:(Z.lt) then
             (match decide_cmp true (Array.get args 0) (Array.get args 1) with Some b => Bool.neg b | None => false end)
           else if Constr.equal f constr:(or) then
             (if decided_false (Array.get args 0) then decided_false (Array.get args 1) else false)
           else if Constr.equal f constr:(and) then
             (if decided_false (Array.get args 0) then true else decided_false (Array.get args 1))
           else false)
        else false
    | _ => false
    end.
  Ltac2 syn_refuted () : unit :=
    if decided_false (Control.goal ()) then () else Control.zero (Tactic_failure None).
End FF.
(* [comment removed for export] *)
Ltac sl_syn_refuted := ltac2:(Control.enter FF.syn_refuted).

(* [comment removed for export] *)
Ltac sl_call_slia := tryif sl_syn_refuted then fail else slia.



Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; sl_call_slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac d_is_natlit n := sl_is_natlit n.   (* [comment removed for export] *)
Ltac d_spine_closed cs :=
  lazymatch cs with
  | nil => idtac
  | cons ?c ?tl =>
      lazymatch c with C8 _ => idtac | C4 _ => idtac | C2 _ => idtac | C1 _ => idtac | CB ?n _ => d_is_natlit n end;
      d_spine_closed tl
  end.
(* [comment removed for export] *)
Ltac d_zsize t := eval cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in t.
Ltac d_is_Zlit a := lazymatch a with Z0 => idtac | Zpos ?p => sl_is_poslit p | Zneg ?p => sl_is_poslit p end.
(* [comment removed for export] *)
Ltac d_true b := let v := eval vm_compute in b in lazymatch v with true => idtac end.
(* [comment removed for export] *)
Ltac d_lit_size S := lazymatch S with Z.of_nat ?N => d_is_natlit N | _ => d_is_Zlit S end.
(* [comment removed for export] *)
Ltac d_split A k :=
  lazymatch A with
  | (?X + ?c)%Z => first [ d_is_Zlit c; k X c constr:(@eq_refl Z A) | k A 0%Z constr:(eq_sym (Z.add_0_r A)) ]
  | (?X - ?c)%Z => first [ d_is_Zlit c; let nc := eval vm_compute in (Z.opp c) in k X nc constr:(@eq_refl Z A)
                         | k A 0%Z constr:(eq_sym (Z.add_0_r A)) ]
  | _ => k A 0%Z constr:(eq_sym (Z.add_0_r A))
  end.
(* [comment removed for export] *)
Ltac d_target segs mnew a k :=
  lazymatch a with
  | (?A + Z.of_nat ?kn)%Z =>
      lazymatch goal with
      | CH : rw_cells segs mnew A ?cs |- _ =>
          d_spine_closed cs;
          let SZ := d_zsize constr:(Z.of_nat (cells_size cs)) in
          d_is_Zlit SZ; k A SZ constr:(Z.of_nat kn)
      end
  end.
(* [comment removed for export] *)
Ltac d_disj segs mnew a n A2 sz2 prover kyes kno :=
  d_target segs mnew a ltac:(fun A SZ kz =>
    let s2 := d_zsize sz2 in
    d_is_Zlit s2; d_is_Zlit n;
    lazymatch kz with Z.of_nat ?kn => d_is_natlit kn end;
    d_true constr:(dchk kz n SZ);
    first
    [ d_split A2 ltac:(fun X2 c2 E2 => d_split A ltac:(fun X c E =>
        constr_eq X2 X; d_true constr:(dchk_sb c2 s2 c SZ);
        kyes constr:(d_apart_sb A2 sz2 s2 A SZ X c2 c kz n E2 E (@eq_refl Z s2) (@eq_refl bool true) (@eq_refl bool true))))
    | lazymatch goal with
      | AP : dfact (A2 + s2 <= A \/ A + SZ <= A2)%Z |- _ =>
          kyes constr:(d_apart_use A2 sz2 s2 A SZ kz n AP (@eq_refl Z s2) (@eq_refl bool true))
      | NO : dno (A2 + s2 <= A \/ A + SZ <= A2)%Z |- _ => kno tt
      | _ => let AP := fresh "dAP" in
             tryif assert (AP : dfact (A2 + s2 <= A \/ A + SZ <= A2)%Z) by (apply dfact_in; prover)
             then kyes constr:(d_apart_use A2 sz2 s2 A SZ kz n AP (@eq_refl Z s2) (@eq_refl bool true))
             else (let NO := fresh "dNO" in assert (NO : dno (A2 + s2 <= A \/ A + SZ <= A2)%Z) by apply dno_in; kno tt)
      end ]).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac d_same_base3 lo hi A k :=
  d_split lo ltac:(fun Xl l El => d_split hi ltac:(fun Xh h Eh => d_split A ltac:(fun X c E =>
     constr_eq Xl X; constr_eq Xh X; k X c l h E El Eh))).
Ltac d_ins_has_sb W A := lazymatch W with cons (?lo, ?hi) ?W' => first [ d_same_base3 lo hi A ltac:(fun X c l h E El Eh => idtac) | d_ins_has_sb W' A ] end.
Ltac d_ins_sb_ok W A SZ := lazymatch W with cons (?lo, ?hi) ?W' =>
  first [ d_same_base3 lo hi A ltac:(fun X c l h E El Eh => d_true constr:(dchk_in l h c SZ)) | d_ins_sb_ok W' A SZ ] end.
Ltac d_ins_hopeless W A SZ := d_ins_has_sb W A; tryif d_ins_sb_ok W A SZ then fail else idtac.
Ltac d_inside segs mnew a n W prover kyes kno :=
  d_target segs mnew a ltac:(fun A SZ kz =>
    d_is_Zlit n; lazymatch kz with Z.of_nat ?kn => d_is_natlit kn end;
    d_true constr:(dchk kz n SZ);
    lazymatch goal with
    | IN : dfact (inside W A SZ) |- _ => kyes constr:(d_inside_sub W A SZ kz n IN (@eq_refl bool true))
    | NO : dno (inside W A SZ) |- _ => kno tt
    | _ => let IN := fresh "dIN" in
           tryif d_ins_hopeless W A SZ
           then (let NO := fresh "dNO" in assert (NO : dno (inside W A SZ)) by apply dno_in; kno tt)
           else tryif assert (IN : dfact (inside W A SZ)) by (apply dfact_in; cbn [inside]; prover)
                then kyes constr:(d_inside_sub W A SZ kz n IN (@eq_refl bool true))
                else (let NO := fresh "dNO" in assert (NO : dno (inside W A SZ)) by apply dno_in; kno tt)
    end).

(* [comment removed for export] *)
Ltac d_fact P prover kyes kno :=
  lazymatch goal with
  | AP : dfact P |- _ => kyes AP
  | NO : dno P |- _ => kno tt
  | _ => let AP := fresh "dAP" in
         tryif assert (AP : dfact P) by (apply dfact_in; prover)
         then kyes AP
         else (let NO := fresh "dNO" in assert (NO : dno P) by apply dno_in; kno tt)
  end.

Ltac slm_transport_chunks_with_d0 segs m m' Heq a bs n Hn Ha Hl :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (slm_bytes_at_write_other segs m m' a bs A2 bs2 n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (slm_wr_at_write segs m m' A2 n2 (wa a) bs Heq) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u32arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u64arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8ro_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.
Ltac slm_footprint_with_d0 segs m m' Heq a bs n Hn Ha Hl :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (slm_munch_write Wq mq m m' a bs n Heq Hn Ha Hl) in MU; [ | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (slm_wmono_write segs mq m m' (wa a) bs Heq) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (slm_stk_write segs m m' loq hiq a bs Heq Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Ltac slm_transport_chunks_with segs m m' Heq a bs n Hn Ha Hl ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (slm_bytes_at_write_other segs m m' a bs A2 bs2 n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (slm_wr_at_write segs m m' A2 n2 (wa a) bs Heq) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disj segs m' a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia)
                ltac:(fun t => apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disj segs m' a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia)
                ltac:(fun t => apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u32arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u64arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8ro_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.
Ltac slm_footprint_with segs m m' Heq a bs n Hn Ha Hl ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ d_inside segs m' a n Wq ltac:(slia)
                ltac:(fun t => apply (slm_munch_write Wq mq m m' a bs n Heq Hn Ha Hl) in MU; [ | exact t ])
                ltac:(fun _ => apply (slm_munch_write Wq mq m m' a bs n Heq Hn Ha Hl) in MU; [ | cbn [inside]; simpl_sizes; slia ])
            | apply (slm_munch_write Wq mq m m' a bs n Heq Hn Ha Hl) in MU; [ | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (slm_wmono_write segs mq m m' (wa a) bs Heq) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (slm_stk_write segs m m' loq hiq a bs Heq Ha Hl) in STq
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Ltac sl_facts_then_d0 a A kn len n' kf ko :=
  let Hn := fresh "Hn_sl" in let Ha := fresh "Ha_sl" in let Hl := fresh "Hl_sl" in
  tryif (assert (Ha : sl_hide (0 <= a)%Z) by (unfold sl_hide; lia);
         assert (Hl : sl_hide (a + len <= 2^64)%Z) by (unfold sl_hide; simpl_sizes; slia);
         assert (Hn : sl_hide (len = n')) by (unfold sl_hide; exact eq_refl))
  then kf n' Hn Ha Hl
  else ko tt.
Ltac sl_facts_then a A kn len n' kf ko :=
  let Hn := fresh "Hn_sl" in let Ha := fresh "Ha_sl" in let Hl := fresh "Hl_sl" in
  tryif (first
         [ lazymatch goal with
           | HB : (0 <= A /\ A + ?S <= 2 ^ 64)%Z |- _ =>
               d_lit_size S; d_is_natlit kn; d_is_Zlit n';
               d_true constr:(dchk (Z.of_nat kn) n' S);
               assert (Ha : sl_hide (0 <= a)%Z) by exact (d_lb A S (Z.of_nat kn) n' HB (@eq_refl bool true));
               assert (Hl : sl_hide (a + len <= 2^64)%Z) by exact (d_ub A S (Z.of_nat kn) n' len HB (@eq_refl Z n') (@eq_refl bool true))
           end
         | assert (Ha : sl_hide (0 <= a)%Z) by (unfold sl_hide; lia);
           assert (Hl : sl_hide (a + len <= 2^64)%Z) by (unfold sl_hide; simpl_sizes; slia) ];
         assert (Hn : sl_hide (len = n')) by (unfold sl_hide; exact eq_refl))
  then kf n' Hn Ha Hl
  else ko tt.

Ltac mem_after_store_d0 :=
  norm_lit_store_bytes;
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
          pose proof (rw_cells_bound segs m A cs H) as HB; sl_lit_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
          let Hn := fresh "Hn_sl" in let Ha := fresh "Ha_sl" in let Hl := fresh "Hl_sl" in
          let a := constr:((A + Z.of_nat kn)%Z) in
          let n' := sl_len_lit (cbytes c') in
          tryif (assert (Ha : sl_hide (0 <= a)%Z) by (unfold sl_hide; lia);
                 assert (Hl : sl_hide (a + Z.of_nat (length (cbytes c')) <= 2^64)%Z) by (unfold sl_hide; simpl_sizes; slia);
                 assert (Hn : sl_hide (Z.of_nat (length (cbytes c')) = n')) by (unfold sl_hide; exact eq_refl))
          then sl_mas_new_tail segs m A kn bs c' cs c0 H HB n' Hn Ha Hl
          else sl_mas_old_tail segs m A kn bs c' cs c0 H HB
        end
    end
  end.
Ltac mem_after_store ::=
  norm_lit_store_bytes;
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
          pose proof (rw_cells_bound segs m A cs H) as HB; sl_lit_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
          let a := constr:((A + Z.of_nat kn)%Z) in
          let n' := sl_len_lit (cbytes c') in
          sl_facts_then a A kn constr:(Z.of_nat (length (cbytes c'))) n'
            ltac:(fun n'' Hn Ha Hl => sl_mas_new_tail segs m A kn bs c' cs c0 H HB n'' Hn Ha Hl)
            ltac:(fun _ => sl_mas_old_tail segs m A kn bs c' cs c0 H HB)
        end
    end
  end.

(* [comment removed for export] *)
Ltac d_ivl A2 sz2 s2 lo hi prover kyes kno :=
  first
  [ d_split A2 ltac:(fun X2 c2 E2 => d_split lo ltac:(fun Xl l El => d_split hi ltac:(fun Xh h Eh =>
      constr_eq X2 Xl; constr_eq X2 Xh; d_true constr:(dchk_ivl c2 s2 l h);
      kyes constr:(d_ivl_sb A2 sz2 s2 lo hi X2 c2 l h E2 El Eh (@eq_refl Z s2) (@eq_refl bool true)))))
  | lazymatch goal with
    | AP : dfact (A2 + s2 <= lo \/ hi <= A2)%Z |- _ => kyes constr:(d_ivl_use A2 sz2 s2 lo hi AP (@eq_refl Z s2))
    | NO : dno (A2 + s2 <= lo \/ hi <= A2)%Z |- _ => kno tt
    | _ => let AP := fresh "dAP" in
           tryif assert (AP : dfact (A2 + s2 <= lo \/ hi <= A2)%Z) by (apply dfact_in; tryif sl_syn_refuted then fail else prover)
           then kyes constr:(d_ivl_use A2 sz2 s2 lo hi AP (@eq_refl Z s2))
           else (let NO := fresh "dNO" in assert (NO : dno (A2 + s2 <= lo \/ hi <= A2)%Z) by apply dno_in; kno tt)
    end ].
Ltac d_call_list W A2 sz2 s2 prover kyes kno :=
  lazymatch W with
  | nil => kyes constr:(I)
  | cons (?lo, ?hi) ?W' =>
      d_ivl A2 sz2 s2 lo hi prover
        ltac:(fun t1 => d_call_list W' A2 sz2 s2 prover ltac:(fun t2 => kyes constr:(conj t1 t2)) kno)
        kno
  end.
(* [comment removed for export] *)
Ltac d_call_disj W A2 sz2 prover kyes kno :=
  let s2 := d_zsize sz2 in
  d_is_Zlit s2;
  d_call_list W A2 sz2 s2 prover kyes kno.

(* [comment removed for export] *)
Ltac transport_call_munch_tac := unfold sub_fp; cbn [outside]; intros; slia.
Ltac transport_after_call_d0 segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; sl_call_slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disj W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia)
                ltac:(fun t => apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disj W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia)
                ltac:(fun t => apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; sl_call_slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ transport_call_munch_tac | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dhull (X lo hi : Z) (P : Prop) : Prop := dfact P.
Definition dhno (X lo hi : Z) : Prop := dno True.
Lemma dhull_in : forall (X lo hi : Z) (P : Prop), P -> dhull X lo hi P.
Proof. exact (fun (X lo hi : Z) (P : Prop) (H : P) => dfact_in P H). Qed.
Lemma dhno_in : forall X lo hi : Z, dhno X lo hi.
Proof. exact (fun X lo hi : Z => dno_in True). Qed.
Lemma d_hull_apart : forall X lo hi hmin hmax a s : Z,
  dhull X lo hi (hmax <= lo \/ hi <= hmin)%Z -> (hmin <= a)%Z -> (a + s <= hmax)%Z -> (a + s <= lo \/ hi <= a)%Z.
Proof.
  exact (fun X lo hi hmin hmax a s H H1 H2 =>
    match dfact_out _ H with
    | or_introl h => or_introl (Z.le_trans _ _ _ H2 h)
    | or_intror h => or_intror (Z.le_trans _ _ _ h H1)
    end).
Qed.
(* [comment removed for export] *)
Lemma d_hull_apart_off : forall X lo hi cmin cmax c s : Z,
  dhull X lo hi (X + cmax <= lo \/ hi <= X + cmin)%Z -> Z.leb cmin c = true -> Z.leb (c + s)%Z cmax = true ->
  (X + c + s <= lo \/ hi <= X + c)%Z.
Proof.
  exact (fun X lo hi cmin cmax c s H B1 B2 =>
    d_hull_apart X lo hi (X + cmin)%Z (X + cmax)%Z (X + c)%Z s H
      (proj1 (Z.add_le_mono_l cmin c X) (proj1 (Z.leb_le cmin c) B1))
      (eq_ind (X + (c + s))%Z (fun t => (t <= X + cmax)%Z)
         (proj1 (Z.add_le_mono_l (c + s)%Z cmax X) (proj1 (Z.leb_le (c + s)%Z cmax) B2)) (X + c + s)%Z (Z.add_assoc X c s))).
Qed.
(* [comment removed for export] *)
Lemma d_hull_apart_x : forall X lo hi cmin cmax s : Z,
  dhull X lo hi (X + cmax <= lo \/ hi <= X + cmin)%Z -> Z.leb cmin 0%Z = true -> Z.leb s cmax = true ->
  (X + s <= lo \/ hi <= X)%Z.
Proof.
  exact (fun X lo hi cmin cmax s H B1 B2 =>
    d_hull_apart X lo hi (X + cmin)%Z (X + cmax)%Z X s H
      (eq_ind (X + 0)%Z (fun t => (X + cmin <= t)%Z) (proj1 (Z.add_le_mono_l cmin 0%Z X) (proj1 (Z.leb_le cmin 0%Z) B1)) X (Z.add_0_r X))
      (proj1 (Z.add_le_mono_l s cmax X) (proj1 (Z.leb_le s cmax) B2))).
Qed.
Lemma d_hull_apart_lit : forall lo hi cmin cmax c s : Z,
  dhull 0%Z lo hi (cmax <= lo \/ hi <= cmin)%Z -> Z.leb cmin c = true -> Z.leb (c + s)%Z cmax = true ->
  (c + s <= lo \/ hi <= c)%Z.
Proof.
  exact (fun lo hi cmin cmax c s H B1 B2 =>
    d_hull_apart 0%Z lo hi cmin cmax c s H (proj1 (Z.leb_le cmin c) B1) (proj1 (Z.leb_le (c + s)%Z cmax) B2)).
Qed.
(* [comment removed for export] *)
Lemma d_lit_apart : forall a s lo hi : Z, orb (Z.leb (a + s)%Z lo) (Z.leb hi a) = true -> (a + s <= lo \/ hi <= a)%Z.
Proof.
  exact (fun a s lo hi B =>
    match Bool.orb_prop _ _ B with
    | or_introl b => or_introl (proj1 (Z.leb_le _ _) b)
    | or_intror b => or_intror (proj1 (Z.leb_le _ _) b)
    end).
Qed.
Module DH.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 is_ref (t : constr) (r : Std.reference) : bool :=
    match r with
    | Std.ConstRef c => (match Constr.Unsafe.kind t with Constr.Unsafe.Constant c' _ => Constant.equal c c' | _ => false end)
    | Std.IndRef i => (match Constr.Unsafe.kind t with Constr.Unsafe.Ind i' _ => Ind.equal i i' | _ => false end)
    | Std.ConstructRef k => (match Constr.Unsafe.kind t with Constr.Unsafe.Constructor k' _ => Constructor.equal k k' | _ => false end)
    | _ => false
    end.
  Ltac2 rec nat_int (c : constr) (acc : int) : int option :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if is_ref f reference:(S) then nat_int (Array.get args 0) (Int.add acc 1) else None)
        else None
    | Constr.Unsafe.Constructor _ _ => if is_ref c reference:(O) then Some acc else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 rec pos_int (c : constr) (depth : int) : int option :=
    if Int.gt depth 60 then None else
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Constructor _ _ => if is_ref c reference:(xH) then Some 1 else None
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if is_ref f reference:(xO) then (match pos_int (Array.get args 0) (Int.add depth 1) with Some v => Some (Int.mul 2 v) | None => None end)
           else if is_ref f reference:(xI) then (match pos_int (Array.get args 0) (Int.add depth 1) with Some v => Some (Int.add (Int.mul 2 v) 1) | None => None end)
           else None)
        else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 z_int (c : constr) : int option :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Constructor _ _ => if is_ref c reference:(Z0) then Some 0 else None
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if is_ref f reference:(Zpos) then pos_int (Array.get args 0) 0
           else if is_ref f reference:(Zneg) then (match pos_int (Array.get args 0) 0 with Some v => Some (Int.neg v) | None => None end)
           else if is_ref f reference:(Z.of_nat) then nat_int (Array.get args 0) 0
           else None)
        else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 rec lin (sg : bool) (c : constr) (acc : ((constr * bool) list * int) option) : ((constr * bool) list * int) option :=
    match acc with
    | None => None
    | Some p =>
        let (ats, k) := p in
        match z_int c with
        | Some v => Some (ats, (if sg then Int.add k v else Int.sub k v))
        | None =>
            match Constr.Unsafe.kind c with
            | Constr.Unsafe.App f args =>
                if Int.equal (Array.length args) 2 then
                  (if is_ref f reference:(Z.add) then lin sg (Array.get args 1) (lin sg (Array.get args 0) acc)
                   else if is_ref f reference:(Z.sub) then lin (Bool.neg sg) (Array.get args 1) (lin sg (Array.get args 0) acc)
                   else Some ((c, sg) :: ats, k))
                else if Int.equal (Array.length args) 1 then
                  (if is_ref f reference:(Z.opp) then lin (Bool.neg sg) (Array.get args 0) acc else Some ((c, sg) :: ats, k))
                else Some ((c, sg) :: ats, k)
            | _ => Some ((c, sg) :: ats, k)
            end
        end
    end.
  Ltac2 lin0 (c : constr) : ((constr * bool) list * int) option := lin true c (Some ([], 0)).
  (* [comment removed for export] *)
  Ltac2 le_dec (l : constr) (d : int) (r : constr) : bool option :=
    match lin0 l with
    | None => None
    | Some lp =>
        match lin0 r with
        | None => None
        | Some rp =>
            let (la, lc) := lp in let (ra, rc) := rp in
            if FF.cancel la ra then Some (Int.le (Int.add lc d) rc) else None
        end
    end.
  Ltac2 is_true_opt (o : bool option) : bool := match o with Some b => b | None => false end.
  Ltac2 is_some (o : 'a option) : bool := match o with Some _ => true | None => false end.
  Ltac2 rec pos_of_int (n : int) : constr :=
    if Int.le n 1 then constr:(xH)
    else (let p := pos_of_int (Int.div n 2) in
          if Int.equal (Int.mod n 2) 0 then constr:(xO $p) else constr:(xI $p)).
  Ltac2 z_of_int (n : int) : constr :=
    if Int.equal n 0 then constr:(Z0)
    else if Int.lt n 0 then (let p := pos_of_int (Int.neg n) in constr:(Zneg $p))
    else (let p := pos_of_int n in constr:(Zpos $p)).
  (* [comment removed for export] *)
  Ltac2 base_off (c : constr) : (constr option * int) option :=
    match lin0 c with
    | None => None
    | Some p =>
        let (ats, off) := p in
        match ats with
        | [] => Some (None, off)
        | x :: rest =>
            (match rest with
             | [] => (let (a, sg) := x in if sg then Some (Some a, off) else None)
             | _ :: _ => None
             end)
        end
    end.
  Ltac2 opt_eq (a : constr option) (b : constr option) : bool :=
    match a with
    | None => (match b with None => true | Some _ => false end)
    | Some x => (match b with None => false | Some y => Constr.equal x y end)
    end.
  (* [comment removed for export] *)
  Ltac2 rec cells_int (cs : constr) (acc : int) : int option :=
    match Constr.Unsafe.kind cs with
    | Constr.Unsafe.App f args =>
        if is_ref f reference:(nil) then Some acc
        else if is_ref f reference:(cons) then
          (if Int.equal (Array.length args) 3 then
             (let sz := match Constr.Unsafe.kind (Array.get args 1) with
                        | Constr.Unsafe.App g gargs =>
                            if is_ref g reference:(C8) then Some 8
                            else if is_ref g reference:(C4) then Some 4
                            else if is_ref g reference:(C2) then Some 2
                            else if is_ref g reference:(C1) then Some 1
                            else if is_ref g reference:(CB) then
                              (if Int.equal (Array.length gargs) 2 then nat_int (Array.get gargs 0) 0 else None)
                            else None
                        | _ => None
                        end in
              match sz with
              | Some n => cells_int (Array.get args 2) (Int.add acc n)
              | None => None
              end)
           else None)
        else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 hull (m : constr) (b : constr option) : (int * int * int) option :=
    List.fold_left (fun acc h =>
      let (_, body, ty) := h in
      match body with
      | Some _ => acc
      | None =>
          match Constr.Unsafe.kind ty with
          | Constr.Unsafe.App f args =>
              if Int.equal (Array.length args) 4 then
                (if (if is_ref f reference:(rw_cells) then true else is_ref f reference:(ro_cells)) then
                   (if Constr.equal (Array.get args 1) m then
                      (match base_off (Array.get args 2) with
                       | Some bo =>
                           (let (b', off) := bo in
                            if opt_eq b b' then
                              (match cells_int (Array.get args 3) 0 with
                               | Some n =>
                                   (match acc with
                                    | None => Some (1, off, Int.add off n)
                                    | Some t => (let (c, mn, mx) := t in
                                                 Some (Int.add c 1, (if Int.lt off mn then off else mn),
                                                       (if Int.gt (Int.add off n) mx then Int.add off n else mx)))
                                    end)
                               | None => acc
                               end)
                            else acc)
                       | None => acc
                       end)
                    else acc)
                 else acc)
              else acc
          | _ => acc
          end
      end) None (Control.hyps ()).
  (* [comment removed for export] *)
  Ltac2 rec find_in (x : constr) (lo : constr) (hi : constr) (hs : (ident * constr option * constr) list) : (ident * constr) option option :=
    match hs with
    | [] => None
    | h :: rest =>
        let (id, body, ty) := h in
        let r := match body with
                 | Some _ => None
                 | None =>
                     match Constr.Unsafe.kind ty with
                     | Constr.Unsafe.App f args =>
                         if is_ref f reference:(dhull) then
                           (if Int.equal (Array.length args) 4 then
                              (if (if Constr.equal (Array.get args 0) x then (if Constr.equal (Array.get args 1) lo then Constr.equal (Array.get args 2) hi else false) else false)
                               then Some (Some (id, Array.get args 3)) else None)
                            else None)
                         else if is_ref f reference:(dhno) then
                           (if Int.equal (Array.length args) 3 then
                              (if (if Constr.equal (Array.get args 0) x then (if Constr.equal (Array.get args 1) lo then Constr.equal (Array.get args 2) hi else false) else false)
                               then Some None else None)
                            else None)
                         else None
                     | _ => None
                     end
                 end in
        match r with Some _ => r | None => find_in x lo hi rest end
    end.
  Ltac2 find_hull (x : constr) (lo : constr) (hi : constr) : (ident * constr) option option :=
    find_in x lo hi (List.rev (Control.hyps ())).
  Ltac2 run1 (kk : Ltac1.t) (args : constr list) : unit := Ltac1.apply kk (List.map Ltac1.of_constr args) Ltac1.run.
  (* [comment removed for export] *)
  Ltac2 g_decided (a2 : constr) (sv : int) (lo : constr) (hi : constr) : bool :=
    let d1 := le_dec a2 sv lo in
    let d2 := le_dec hi 0 a2 in
    if is_true_opt d1 then true else if is_true_opt d2 then true
    else (if is_some d1 then is_some d2 else false).
  (* [comment removed for export] *)
  Ltac2 rec is_poslit (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Constructor _ _ => is_ref c reference:(xH)
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if (if is_ref f reference:(xO) then true else is_ref f reference:(xI)) then is_poslit (Array.get args 0) else false)
        else false
    | _ => false
    end.
  Ltac2 is_zlit (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Constructor _ _ => is_ref c reference:(Z0)
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 1 then
          (if (if is_ref f reference:(Zpos) then true else is_ref f reference:(Zneg)) then is_poslit (Array.get args 0) else false)
        else false
    | _ => false
    end.
  Ltac2 split_cands (a : constr) : constr list :=
    match Constr.Unsafe.kind a with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 2 then
          (if (if is_ref f reference:(Z.add) then true else is_ref f reference:(Z.sub)) then
             (if is_zlit (Array.get args 1) then [Array.get args 0; a] else [a])
           else [a])
        else [a]
    | _ => [a]
    end.
  Ltac2 mem_c (x : constr) (l : constr list) : bool := List.exist (fun y => Constr.equal x y) l.
  Ltac2 sb3 (a2 : constr) (lo : constr) (hi : constr) : unit :=
    let cl := split_cands lo in let ch := split_cands hi in
    if List.exist (fun b => if mem_c b cl then mem_c b ch else false) (split_cands a2) then () else Control.zero (Tactic_failure None).
  Ltac2 sb2 (a2 : constr) (a : constr) : unit :=
    let ca := split_cands a in
    if List.exist (fun b => mem_c b ca) (split_cands a2) then () else Control.zero (Tactic_failure None).
  Ltac2 x_of (b : constr option) : constr := match b with Some x => x | None => constr:(Z0) end.
  (* [comment removed for export] *)
  Ltac2 prep_base (a2 : constr) (s2 : constr) (lo : constr) (hi : constr) (k : Ltac1.t) : unit :=
    match z_int s2 with
    | None => ()
    | Some sv =>
        if g_decided a2 sv lo hi then () else
        match base_off a2 with
        | None => ()
        | Some bo => let (b, _) := bo in run1 k [x_of b]
        end
    end.
  (* [comment removed for export] *)
  Ltac2 mk_hull (m : constr) (x : constr) (lo : constr) (hi : constr) (kyes : Ltac1.t) (kno : Ltac1.t) : unit :=
    let b := if is_ref x reference:(Z0) then None else Some x in
    match hull m b with
    | None => run1 kno [x]
    | Some t =>
        let (cnt, mn, mx) := t in
        if Int.lt cnt 3 then run1 kno [x] else
        (let cmin := z_of_int mn in
         let cmax := z_of_int mx in
         let hmin := match b with Some y => constr:(Z.add $y $cmin) | None => cmin end in
         let hmax := match b with Some y => constr:(Z.add $y $cmax) | None => cmax end in
         run1 kyes [constr:(Z.le $hmax $lo \/ Z.le $hi $hmin)])
    end.
  (* [comment removed for export] *)
  Ltac2 m1 (a2 : constr) (s2 : constr) (lo : constr) (hi : constr) (ktiny : Ltac1.t) : unit :=
    match z_int s2 with
    | None => Control.zero (Tactic_failure None)
    | Some sv =>
        let d1 := le_dec a2 sv lo in
        let d2 := le_dec hi 0 a2 in
        if (if is_true_opt d1 then true else is_true_opt d2) then
          (let lits := if is_some (z_int a2) then (if is_some (z_int lo) then is_some (z_int hi) else false) else false in
           if lits then Control.refine (fun () => constr:(d_lit_apart $a2 $s2 $lo $hi (@eq_refl bool true)))
           else Ltac1.run ktiny)
        else Control.zero (Tactic_failure None)
    end.
  (* [comment removed for export] *)
  Ltac2 close_base (a2 : constr) (k : Ltac1.t) : unit :=
    match base_off a2 with
    | None => Control.zero (Tactic_failure None)
    | Some bo => let (b, _) := bo in run1 k [x_of b]
    end.
  (* [comment removed for export] *)
  Ltac2 bounds (based : bool) (p : constr) : (constr * constr) option :=
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.App _ oargs =>
        (match Constr.Unsafe.kind (Array.get oargs 0) with
         | Constr.Unsafe.App _ l1a =>
             (match Constr.Unsafe.kind (Array.get oargs 1) with
              | Constr.Unsafe.App _ l2a =>
                  (let hmax := Array.get l1a 0 in let hmin := Array.get l2a 1 in
                   if based then
                     (match Constr.Unsafe.kind hmin with
                      | Constr.Unsafe.App _ xa => (match Constr.Unsafe.kind hmax with
                                                  | Constr.Unsafe.App _ ya => Some (Array.get xa 1, Array.get ya 1)
                                                  | _ => None end)
                      | _ => None end)
                   else Some (hmin, hmax))
              | _ => None end)
         | _ => None end)
    | _ => None end.
  (* [comment removed for export] *)
  Ltac2 close_with (a2 : constr) (s2 : constr) (lo : constr) (hi : constr) (h : constr) (p : constr) : unit :=
    match z_int s2 with
    | None => Control.zero (Tactic_failure None)
    | Some sv =>
    match base_off a2 with
    | None => Control.zero (Tactic_failure None)
    | Some bo =>
        let (b, c2) := bo in
        match bounds (is_some b) p with
        | None => Control.zero (Tactic_failure None)
        | Some bb =>
            let (cmin, cmax) := bb in
            match z_int cmin with
            | None => Control.zero (Tactic_failure None)
            | Some vmin =>
                match z_int cmax with
                | None => Control.zero (Tactic_failure None)
                | Some vmax =>
                    if (if Int.le vmin c2 then Int.le (Int.add c2 sv) vmax else false) then
                      (match b with
                       | None => Control.refine (fun () => constr:(d_hull_apart_lit $lo $hi $cmin $cmax $a2 $s2 $h (@eq_refl bool true) (@eq_refl bool true)))
                       | Some y =>
                           if Constr.equal a2 y then
                             Control.refine (fun () => constr:(d_hull_apart_x $y $lo $hi $cmin $cmax $s2 $h (@eq_refl bool true) (@eq_refl bool true)))
                           else
                             (match Constr.Unsafe.kind a2 with
                              | Constr.Unsafe.App f2 a2a =>
                                  if (if is_ref f2 reference:(Z.add) then (if Int.equal (Array.length a2a) 2 then Constr.equal (Array.get a2a 0) y else false) else false) then
                                    (let c := Array.get a2a 1 in
                                     Control.refine (fun () => constr:(d_hull_apart_off $y $lo $hi $cmin $cmax $c $s2 $h (@eq_refl bool true) (@eq_refl bool true))))
                                  else Control.zero (Tactic_failure None)
                              | _ => Control.zero (Tactic_failure None)
                              end)
                       end)
                    else Control.zero (Tactic_failure None)
                end
            end
        end
    end
    end.
  (* [comment removed for export] *)
  Ltac2 c1 (x : Ltac1.t) : constr :=
    match Ltac1.to_constr x with
    | Some c => c
    | None =>
        match Ltac1.to_ident x with
        | Some id => if List.exist (fun h => let (i, _, _) := h in Ident.equal i id) (Control.hyps ()) then Control.hyp id
                     else Control.zero (Tactic_failure None)
        | None => Control.zero (Tactic_failure None)
        end
    end.
  (* [comment removed for export] *)
  Ltac2 clear_all () : unit :=
    let ids := List.map_filter (fun h =>
      let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match Constr.Unsafe.kind ty with
          | Constr.Unsafe.App f _ => if (if is_ref f reference:(dhull) then true else is_ref f reference:(dhno)) then Some id else None
          | _ => None
          end
      end) (Control.hyps ()) in
    match ids with [] => () | _ :: _ => Std.clear ids end.
End DH.
(* [comment removed for export] *)
Ltac d_tiny := clear; first [ xlia zchecker | Zify.zify; xlia zchecker ].
Ltac d_hull_clear := ltac2:(Control.enter DH.clear_all).
(* [comment removed for export] *)
Module DHP.
  Import Ltac2.
  Ltac2 prune_all () : unit :=
    let cs := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zt_plain_consts () in
    let mm := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zt_memo_new () in
    let ids := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zt_plain_arith_s cs ty then None
                           else if OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zt_is_prop_m mm ty then Some id else None
                 end) (Control.hyps ()) in
    match ids with
    | [] => ()
    | _ :: _ =>
        Control.once (fun () => Control.plus (fun () => Std.clear ids)
          (fun _ => List.iter (fun id => Control.once (fun () => Control.plus (fun () => Std.clear [id]) (fun _ => ()))) ids))
    end.
End DHP.
Ltac d_prune_all := ltac2:(Control.enter DHP.prune_all).
Ltac d_hull_cheap := d_prune_all; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac d_hull_prep_core m A2 s2 lo hi hp :=
  let f := ltac2:(a2 s2 lo hi k |- DH.prep_base (DH.c1 a2) (DH.c1 s2) (DH.c1 lo) (DH.c1 hi) k) in
  f A2 s2 lo hi ltac:(fun X =>
    lazymatch goal with
    | _ : dhull X lo hi _ |- _ => idtac
    | _ : dhno X lo hi |- _ => idtac
    | _ =>
        let g := ltac2:(m x lo hi ky kn |- DH.mk_hull (DH.c1 m) (DH.c1 x) (DH.c1 lo) (DH.c1 hi) ky kn) in
        g m X lo hi
          ltac:(fun P => let HL := fresh "dHL" in
                  tryif assert (HL : dhull X lo hi P) by (apply dhull_in; tryif sl_syn_refuted then fail else hp)
                  then idtac
                  else (let HN := fresh "dHN" in assert (HN : dhno X lo hi) by apply dhno_in))
          ltac:(fun X' => let HN := fresh "dHN" in assert (HN : dhno X lo hi) by apply dhno_in)
    end).
Ltac d_hull_prep m A2 s2 lo hi hp := try (d_hull_prep_core m A2 s2 lo hi hp).
(* [comment removed for export] *)
Ltac d_cheap_close A2 s2 lo hi :=
  first [ let f := ltac2:(a2 s2 lo hi k |- DH.m1 (DH.c1 a2) (DH.c1 s2) (DH.c1 lo) (DH.c1 hi) k) in f A2 s2 lo hi ltac:(idtac; d_tiny)
        | let f := ltac2:(a2 k |- DH.close_base (DH.c1 a2) k) in
          f A2 ltac:(fun X =>
            lazymatch goal with
            | HL : dhull X lo hi ?P |- _ =>
                let g := ltac2:(a2 s2 lo hi h p |- DH.close_with (DH.c1 a2) (DH.c1 s2) (DH.c1 lo) (DH.c1 hi) (DH.c1 h) (DH.c1 p)) in
                g A2 s2 lo hi HL P
            end) ].
(* [comment removed for export] *)
Ltac d_sb3 A2 lo hi := let f := ltac2:(a2 lo hi |- DH.sb3 (DH.c1 a2) (DH.c1 lo) (DH.c1 hi)) in f A2 lo hi.
Ltac d_sb2 A2 A := let f := ltac2:(a2 a |- DH.sb2 (DH.c1 a2) (DH.c1 a)) in f A2 A.

(* [comment removed for export] *)
Ltac sl_kz kn :=
  let b := constr:(ltac:(first [ sl_is_natlit kn; exact true | exact false ])) in
  lazymatch b with
  | true => let z := eval vm_compute in (Z.of_nat kn) in z
  | false => constr:(Z.of_nat kn)
  end.
(* [comment removed for export] *)
Ltac d_lit_kz k := lazymatch k with Z.of_nat ?N => d_is_natlit N | _ => d_is_Zlit k end.
Ltac d_target_e1 segs mnew a k :=
  lazymatch a with
  | (?A + Z.of_nat ?kn)%Z =>
      lazymatch goal with
      | CH : rw_cells segs mnew A ?cs |- _ =>
          d_spine_closed cs;
          let SZ := d_zsize constr:(Z.of_nat (cells_size cs)) in
          d_is_Zlit SZ; k A SZ constr:(Z.of_nat kn)
      end
  end.
Ltac d_target segs mnew a k ::=
  lazymatch a with
  | (?A + Z.of_nat ?kn)%Z =>
      lazymatch goal with
      | CH : rw_cells segs mnew A ?cs |- _ =>
          d_spine_closed cs;
          let SZ := d_zsize constr:(Z.of_nat (cells_size cs)) in
          d_is_Zlit SZ; k A SZ constr:(Z.of_nat kn)
      end
  | (?A + ?z)%Z =>
      d_is_Zlit z;
      lazymatch goal with
      | CH : rw_cells segs mnew A ?cs |- _ =>
          d_spine_closed cs;
          let SZ := d_zsize constr:(Z.of_nat (cells_size cs)) in
          d_is_Zlit SZ; k A SZ z
      end
  end.
Ltac d_disj segs mnew a n A2 sz2 prover kyes kno ::=
  d_target segs mnew a ltac:(fun A SZ kz =>
    let s2 := d_zsize sz2 in
    d_is_Zlit s2; d_is_Zlit n;
    d_lit_kz kz;
    d_true constr:(dchk kz n SZ);
    first
    [ d_split A2 ltac:(fun X2 c2 E2 => d_split A ltac:(fun X c E =>
        constr_eq X2 X; d_true constr:(dchk_sb c2 s2 c SZ);
        kyes constr:(d_apart_sb A2 sz2 s2 A SZ X c2 c kz n E2 E (@eq_refl Z s2) (@eq_refl bool true) (@eq_refl bool true))))
    | lazymatch goal with
      | AP : dfact (A2 + s2 <= A \/ A + SZ <= A2)%Z |- _ =>
          kyes constr:(d_apart_use A2 sz2 s2 A SZ kz n AP (@eq_refl Z s2) (@eq_refl bool true))
      | NO : dno (A2 + s2 <= A \/ A + SZ <= A2)%Z |- _ => kno tt
      | _ => let AP := fresh "dAP" in
             tryif assert (AP : dfact (A2 + s2 <= A \/ A + SZ <= A2)%Z) by (apply dfact_in; prover)
             then kyes constr:(d_apart_use A2 sz2 s2 A SZ kz n AP (@eq_refl Z s2) (@eq_refl bool true))
             else (let NO := fresh "dNO" in assert (NO : dno (A2 + s2 <= A \/ A + SZ <= A2)%Z) by apply dno_in; kno tt)
      end ]).
Ltac d_inside segs mnew a n W prover kyes kno ::=
  d_target segs mnew a ltac:(fun A SZ kz =>
    d_is_Zlit n; d_lit_kz kz;
    d_true constr:(dchk kz n SZ);
    lazymatch goal with
    | IN : dfact (inside W A SZ) |- _ => kyes constr:(d_inside_sub W A SZ kz n IN (@eq_refl bool true))
    | NO : dno (inside W A SZ) |- _ => kno tt
    | _ => let IN := fresh "dIN" in
           tryif d_ins_hopeless W A SZ
           then (let NO := fresh "dNO" in assert (NO : dno (inside W A SZ)) by apply dno_in; kno tt)
           else tryif assert (IN : dfact (inside W A SZ)) by (apply dfact_in; cbn [inside]; prover)
                then kyes constr:(d_inside_sub W A SZ kz n IN (@eq_refl bool true))
                else (let NO := fresh "dNO" in assert (NO : dno (inside W A SZ)) by apply dno_in; kno tt)
    end).
Ltac sl_facts_then_e1 a A kn len n' kf ko :=
  let Hn := fresh "Hn_sl" in let Ha := fresh "Ha_sl" in let Hl := fresh "Hl_sl" in
  tryif (first
         [ lazymatch goal with
           | HB : (0 <= A /\ A + ?S <= 2 ^ 64)%Z |- _ =>
               d_lit_size S; d_is_natlit kn; d_is_Zlit n';
               d_true constr:(dchk (Z.of_nat kn) n' S);
               assert (Ha : sl_hide (0 <= a)%Z) by exact (d_lb A S (Z.of_nat kn) n' HB (@eq_refl bool true));
               assert (Hl : sl_hide (a + len <= 2^64)%Z) by exact (d_ub A S (Z.of_nat kn) n' len HB (@eq_refl Z n') (@eq_refl bool true))
           end
         | assert (Ha : sl_hide (0 <= a)%Z) by (unfold sl_hide; lia);
           assert (Hl : sl_hide (a + len <= 2^64)%Z) by (unfold sl_hide; simpl_sizes; slia) ];
         assert (Hn : sl_hide (len = n')) by (unfold sl_hide; exact eq_refl))
  then kf n' Hn Ha Hl
  else ko tt.
(* [comment removed for export] *)
Ltac sl_facts_then a A kn len n' kf ko ::=
  let kz := sl_kz kn in
  let a := constr:((A + kz)%Z) in
  let Hn := fresh "Hn_sl" in let Ha := fresh "Ha_sl" in let Hl := fresh "Hl_sl" in
  tryif (first
         [ lazymatch goal with
           | HB : (0 <= A /\ A + ?S <= 2 ^ 64)%Z |- _ =>
               d_lit_size S; d_lit_kz kz; d_is_Zlit n';
               (* [comment removed for export] *)
               let Sz := lazymatch S with Z.of_nat ?N => let z := eval vm_compute in (Z.of_nat N) in z | _ => S end in
               change S with Sz in HB;
               d_true constr:(dchk kz n' Sz);
               assert (Ha : sl_hide (0 <= a)%Z) by exact (d_lb A Sz kz n' HB (@eq_refl bool true));
               assert (Hl : sl_hide (a + len <= 2^64)%Z) by exact (d_ub A Sz kz n' len HB (@eq_refl Z n') (@eq_refl bool true))
           end
         | assert (Ha : sl_hide (0 <= a)%Z) by (unfold sl_hide; lia);
           assert (Hl : sl_hide (a + len <= 2^64)%Z) by (unfold sl_hide; simpl_sizes; slia) ];
         assert (Hn : sl_hide (len = n')) by (unfold sl_hide; exact eq_refl))
  then kf n' Hn Ha Hl
  else ko tt.
Ltac sl_mas_new_tail_e1 segs m A kn bs c' cs c0 H HB n' Hn Ha Hl :=
  change bs with (cbytes c');
  let m' := fresh "m" in
  set (m' := write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c'));
  let Heq := fresh "Heq_sl" in
  assert (Heq : sl_hide (m' = write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c'))) by exact (eq_refl m');
  try lazymatch goal with
  | HI : mem_inv segs m |- _ =>
      apply (slm_mem_inv_store_cbytes segs m m' (wa (A + Z.of_nat kn)) c' Heq) in HI;
      [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
  end;
  let H' := fresh "CH" in
  pose proof (slm_rw_cells_write segs m m' A cs kn c0 c' Heq H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
  clear H;
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
  slm_transport_chunks_with segs m m' Heq (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
  sl_store_extra m m' (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl H';
  slm_footprint_with segs m m' Heq (A + Z.of_nat kn)%Z (cbytes c') n' Hn Ha Hl;
  clear Heq Hn Ha Hl; clearbody m';
  clear HB; try clear m; try rename H' into H.
(* [comment removed for export] *)
Ltac sl_mas_new_tail segs m A kn bs c' cs c0 H HB n' Hn Ha Hl ::=
  change bs with (cbytes c');
  let a := lazymatch type of Ha with sl_hide (Z.le 0 ?a) => a end in
  let m' := fresh "m" in
  set (m' := write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c'));
  let Heq0 := fresh "Heq_sl" in
  assert (Heq0 : sl_hide (m' = write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c'))) by exact (eq_refl m');
  let Heq := fresh "Heq_sl" in
  first [ constr_eq a (A + Z.of_nat kn)%Z; pose proof Heq0 as Heq
        | assert (Heq : sl_hide (m' = write_to_mem m (wa a) (cbytes c'))) by exact (eq_refl m') ];
  try lazymatch goal with
  | HI : mem_inv segs m |- _ =>
      apply (slm_mem_inv_store_cbytes segs m m' (wa (A + Z.of_nat kn)) c' Heq0) in HI;
      [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
  end;
  let H' := fresh "CH" in
  pose proof (slm_rw_cells_write segs m m' A cs kn c0 c' Heq0 H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
  clear H;
  cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
  slm_transport_chunks_with segs m m' Heq a (cbytes c') n' Hn Ha Hl;
  sl_store_extra m m' a (cbytes c') n' Hn Ha Hl H';
  slm_footprint_with segs m m' Heq a (cbytes c') n' Hn Ha Hl;
  clear Heq Heq0 Hn Ha Hl; clearbody m';
  clear HB; try clear m; try rename H' into H.

(* [comment removed for export] *)
Ltac d_ivlm m A2 sz2 s2 lo hi prover hp kyes kno :=
  first
  [ d_sb3 A2 lo hi;
    d_split A2 ltac:(fun X2 c2 E2 => d_split lo ltac:(fun Xl l El => d_split hi ltac:(fun Xh h Eh =>
      constr_eq X2 Xl; constr_eq X2 Xh; d_true constr:(dchk_ivl c2 s2 l h);
      kyes constr:(d_ivl_sb A2 sz2 s2 lo hi X2 c2 l h E2 El Eh (@eq_refl Z s2) (@eq_refl bool true)))))
  | lazymatch goal with
    | AP : dfact (A2 + s2 <= lo \/ hi <= A2)%Z |- _ => kyes constr:(d_ivl_use A2 sz2 s2 lo hi AP (@eq_refl Z s2))
    | NO : dno (A2 + s2 <= lo \/ hi <= A2)%Z |- _ => kno tt
    | _ => d_hull_prep m A2 s2 lo hi hp;
           let AP := fresh "dAP" in
           tryif assert (AP : dfact (A2 + s2 <= lo \/ hi <= A2)%Z)
                   by (apply dfact_in; tryif sl_syn_refuted then fail else first [ d_cheap_close A2 s2 lo hi | prover ])
           then kyes constr:(d_ivl_use A2 sz2 s2 lo hi AP (@eq_refl Z s2))
           else (let NO := fresh "dNO" in assert (NO : dno (A2 + s2 <= lo \/ hi <= A2)%Z) by apply dno_in; kno tt)
    end ].
Ltac d_call_listm m W A2 sz2 s2 prover hp kyes kno :=
  lazymatch W with
  | nil => kyes constr:(I)
  | cons (?lo, ?hi) ?W' =>
      d_ivlm m A2 sz2 s2 lo hi prover hp
        ltac:(fun t1 => d_call_listm m W' A2 sz2 s2 prover hp ltac:(fun t2 => kyes constr:(conj t1 t2)) kno)
        kno
  end.
Ltac d_call_disjm m W A2 sz2 prover hp kyes kno :=
  let s2 := d_zsize sz2 in
  d_is_Zlit s2;
  d_call_listm m W A2 sz2 s2 prover hp kyes kno.
Ltac d_disjm segs m mnew a n A2 sz2 prover hp kyes kno :=
  d_target segs mnew a ltac:(fun A SZ kz =>
    let s2 := d_zsize sz2 in
    d_is_Zlit s2; d_is_Zlit n;
    d_lit_kz kz;
    d_true constr:(dchk kz n SZ);
    first
    [ d_sb2 A2 A;
      d_split A2 ltac:(fun X2 c2 E2 => d_split A ltac:(fun X c E =>
        constr_eq X2 X; d_true constr:(dchk_sb c2 s2 c SZ);
        kyes constr:(d_apart_sb A2 sz2 s2 A SZ X c2 c kz n E2 E (@eq_refl Z s2) (@eq_refl bool true) (@eq_refl bool true))))
    | lazymatch goal with
      | AP : dfact (A2 + s2 <= A \/ A + SZ <= A2)%Z |- _ =>
          kyes constr:(d_apart_use A2 sz2 s2 A SZ kz n AP (@eq_refl Z s2) (@eq_refl bool true))
      | NO : dno (A2 + s2 <= A \/ A + SZ <= A2)%Z |- _ => kno tt
      | _ => d_hull_prep m A2 s2 A constr:((A + SZ)%Z) hp;
             let AP := fresh "dAP" in
             tryif assert (AP : dfact (A2 + s2 <= A \/ A + SZ <= A2)%Z)
                     by (apply dfact_in; first [ d_cheap_close A2 s2 A constr:((A + SZ)%Z) | prover ])
             then kyes constr:(d_apart_use A2 sz2 s2 A SZ kz n AP (@eq_refl Z s2) (@eq_refl bool true))
             else (let NO := fresh "dNO" in assert (NO : dno (A2 + s2 <= A \/ A + SZ <= A2)%Z) by apply dno_in; kno tt)
      end ]).

(* [comment removed for export] *)
Ltac sl_call_slia_e1 := tryif sl_syn_refuted then fail else slia.
Module LEAF.
  Import Ltac2.
  Ltac2 Type exn ::= [ LeafProved | LeafRefuted ].
  Ltac2 is_or (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args => if DH.is_ref f reference:(or) then Int.equal (Array.length args) 2 else false
    | _ => false
    end.
  (* [comment removed for export] *)
  Ltac2 rec leftmost (t : constr) : constr :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args => if is_or t then leftmost (Array.get args 0) else t
    | _ => t
    end.
  (* [comment removed for export] *)
  Ltac2 ors () : (ident * constr) list :=
    List.map_filter (fun h =>
      let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if is_or ty then (if SLit.arith_visible ty then Some (id, ty) else None) else None
      end) (Control.hyps ()).
  (* [comment removed for export] *)
  Ltac2 refuted () : unit :=
    let cs := ors () in
    match cs with
    | [] => Control.zero (Tactic_failure None)
    | _ :: _ =>
        let ids := List.map (fun p => let (id, _) := p in id) cs in
        let imp := List.fold_right (fun p acc => let (_, ty) := p in let l := leftmost ty in constr:($l -> $acc)) cs (Control.goal ()) in
        match Control.case (fun () =>
                ltac1:(t |- assert t) (Ltac1.of_constr imp);
                Control.focus 1 1 (fun () =>
                  match Control.case (fun () => Std.clear ids) with
                  | Val _ =>
                      (match Control.case (fun () => ltac1:(Zify.zify; xlia zchecker)) with
                       | Val _ => Control.zero LeafProved
                       | Err _ => Control.zero LeafRefuted
                       end)
                  | Err _ => Control.zero LeafProved
                  end)) with
        | Val _ => Control.zero (Tactic_failure None)
        | Err e => match e with
                   | LeafRefuted => ()
                   | _ => Control.zero (Tactic_failure None)
                   end
        end
    end.
End LEAF.
Ltac sl_leaf_refuted := ltac2:(Control.enter LEAF.refuted).
Ltac sl_call_slia ::=
  tryif sl_syn_refuted then fail
  else first [ exact I
             | d_hull_cheap
             | tryif sl_leaf_refuted then fail
               else lazymatch goal with
                    | |- _ /\ (_ /\ _) => first [ exact I | lia ]
                    | |- _ => slia
                    end ].

(* [comment removed for export] *)
Module ARR.
  Import Ltac2.
  Ltac2 arr_head (t : constr) : bool :=
    if DH.is_ref t reference:(u32s) then true else if DH.is_ref t reference:(u64s) then true else DH.is_ref t reference:(upd).
  Ltac2 rec mentions (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args => if mentions f then true else Array.exist mentions args
    | Constr.Unsafe.Constant _ _ => arr_head t
    | Constr.Unsafe.Prod b body => if mentions (Constr.Binder.type b) then true else mentions body
    | Constr.Unsafe.Lambda b body => if mentions (Constr.Binder.type b) then true else mentions body
    | Constr.Unsafe.LetIn b v body => if mentions (Constr.Binder.type b) then true else (if mentions v then true else mentions body)
    | Constr.Unsafe.Cast c _ t' => if mentions c then true else mentions t'
    | Constr.Unsafe.Rel _ => false
    | Constr.Unsafe.Var _ => false
    | Constr.Unsafe.Sort _ => false
    | Constr.Unsafe.Ind _ _ => false
    | Constr.Unsafe.Constructor _ _ => false
    | _ => true
    end.
  Ltac2 on_arr_hyps (tac : Ltac1.t) : unit :=
    List.iter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => ()
                 | None => if SLit.arith_visible ty then (if mentions ty then Ltac1.apply tac [Ltac1.of_constr (Control.hyp id)] Ltac1.run else ()) else ()
                 end) (Control.hyps ()).
End ARR.
Ltac simpl_arr_sizes ::=
  (let f := ltac2:(t |- ARR.on_arr_hyps t) in f sl_arr_rw_in);
  rewrite ?u32s_length, ?u64s_length, ?upd_length.

(* [comment removed for export] *)
Ltac d_chunk_prep m A2 cs2 a n :=
  try (d_spine_closed cs2;
       let s2 := d_zsize constr:(Z.of_nat (cells_size cs2)) in
       d_is_Zlit s2;
       d_hull_prep m A2 s2 a constr:((a + n)%Z) ltac:(d_hull_cheap)).
Ltac d_chunk_close A2 cs2 a n :=
  d_spine_closed cs2;
  let s2 := d_zsize constr:(Z.of_nat (cells_size cs2)) in
  d_is_Zlit s2;
  change (Z.of_nat (cells_size cs2)) with s2;
  d_cheap_close A2 s2 a constr:((a + n)%Z).

(* [comment removed for export] *)

Ltac transport_after_call_e1 segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disj W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia)
                ltac:(fun t => apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disj W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia)
                ltac:(fun t => apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; sl_call_slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ transport_call_munch_tac | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disjm m W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia) ltac:(d_hull_cheap)
                ltac:(fun t => apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | exact t ])
                ltac:(fun _ => first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_call_disjm m W A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia) ltac:(d_hull_cheap)
                ltac:(fun t => apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact t ])
                ltac:(fun _ => first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ])
            | apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; sl_call_slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; sl_call_slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ transport_call_munch_tac | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end);
  d_hull_clear.

Ltac slm_transport_chunks_with_e1 segs m m' Heq a bs n Hn Ha Hl :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (slm_bytes_at_write_other segs m m' a bs A2 bs2 n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (slm_wr_at_write segs m m' A2 n2 (wa a) bs Heq) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disj segs m' a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia)
                ltac:(fun t => apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disj segs m' a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia)
                ltac:(fun t => apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u32arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u64arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8ro_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac slm_transport_chunks_with segs m m' Heq a bs n Hn Ha Hl ::=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (slm_bytes_at_write_other segs m m' a bs A2 bs2 n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (slm_wr_at_write segs m m' A2 n2 (wa a) bs Heq) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disjm segs m m' a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia) ltac:(d_hull_cheap)
                ltac:(fun t => apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (slm_rw_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_spine_closed cs2;
              d_disjm segs m m' a n A2 constr:(Z.of_nat (cells_size cs2)) ltac:(slia) ltac:(d_hull_cheap)
                ltac:(fun t => apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | exact t ])
                ltac:(fun _ => first [ apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
                                     | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ])
            | apply (slm_ro_cells_frame segs m m' A2 cs2 a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u32arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u64arr_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (slm_u8ro_frame segs m m' A2 xs a bs n Heq Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end);
  d_hull_clear.

Ltac sl_transport_chunks_with_e1 segs m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (sl_bytes_at_write_other segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (sl_rw_cells_frame segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (sl_ro_cells_frame segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u8arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u32arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u64arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u8ro_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac sl_transport_chunks_with segs m a bs n Hn Ha Hl ::=
  (repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (sl_bytes_at_write_other segs m a bs A2 bs2 n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_chunk_prep m A2 cs2 a n;
              apply (sl_rw_cells_frame segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | first [ d_chunk_close A2 cs2 a n | simpl_sizes; slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ d_chunk_prep m A2 cs2 a n;
              apply (sl_ro_cells_frame segs m A2 cs2 a bs n Hn Ha Hl) in H; [ | first [ d_chunk_close A2 cs2 a n | simpl_sizes; slia ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u8arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u32arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u64arr_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (sl_u8ro_frame segs m A2 xs a bs n Hn Ha Hl) in H; [ | simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end);
  d_hull_clear.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export StepFast.
