(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Export X1c5 X1by X1bz X1bm X1bo X1c9 X1br X1bj X1bu.
Import ListNotations.
Open Scope bv_scope.

Ltac is_concrete_map R ::=
lazymatch R with
| TNode _ _ _ => idtac
| TEmpty => idtac
| mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
| mkF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac
end.
Ltac map_cbv_get ::= cbv beta iota delta [tget mkR mkF].
Ltac map_cbv_set ::= cbv beta iota delta [tset mkR mkF].

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

Ltac mem_after_store_opt ::=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
match goal with
| H : rw_cells segs m A _ |- _ => mem_after_store
| _ => idtac
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

try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).

Tactic Notation "call" uconstr(SPEC) :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_call segs m ]
end.

Ltac carve_frame n ST :=
lazymatch type of ST with
| stk ?segs ?m ?lo ?hi =>
let junk := fresh "junk" in let FR := fresh "FR" in let ST' := fresh "ST" in
destruct (stk_carve segs m lo hi n ST ltac:(lia)) as [ST' [junk FR]];
clear ST; rename ST' into ST;
let z := eval vm_compute in (Z.of_nat n) in
change (Z.of_nat n) with z in ST, FR;

repeat match type of FR with
| context [Z.sub (Z.add ?b ?c) ?d] => is_Zlit c; is_Zlit d; let v := eval vm_compute in (c - d)%Z in
replace (Z.sub (Z.add b c) d) with (Z.add b v) in * by lia
| context [Z.sub ?b ?d] => is_Zlit d; let v := eval vm_compute in (- d)%Z in
replace (Z.sub b d) with (Z.add b v) in * by lia
end
end.

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

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hn & H). repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hn & HA) & (Hb & Hm & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app, Nat2Z.inj_add.
split.
- intros ([[W1 W2] [B1 B2]] & WR). rewrite (cells_bytes_length cs1 W1) in B2.
apply wr_at_app in WR as [WR1 WR2]; [|lia|lia].
exact (conj (conj (conj W1 B1) WR1) (conj (conj W2 B2) WR2)).
- intros ([[W1 B1] WR1] & [[W2 B2] WR2]). rewrite (cells_bytes_length cs1 W1).
refine (conj (conj (conj W1 W2) (conj B1 B2)) _). apply wr_at_app; [lia|lia|]. split; assumption.
Qed.

Lemma rw_cells_uncons : forall segs m A c cs,
rw_cells segs m A (c :: cs) -> rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) cs.
Proof.
intros segs m A c cs H. change (c :: cs) with ([c] ++ cs) in H. apply rw_cells_app in H.
cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma rw_cells_snoc : forall segs m A cs c,
rw_cells segs m A cs -> rw_cells segs m (A + Z.of_nat (cells_size cs)) [c] -> rw_cells segs m A (cs ++ [c]).
Proof. intros segs m A cs c H1 H2. apply rw_cells_app. split; assumption. Qed.

Lemma rw_cells_join : forall segs m A cs1 cs2,
rw_cells segs m A cs1 -> rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof. intros segs m A cs1 cs2 H1 H2. apply rw_cells_app. split; assumption. Qed.

Lemma rw_cells_nil : forall segs m A, (0 <= A <= 2^64)%Z -> rw_cells segs m A [].
Proof.
intros segs m A HA. split; [split; [exact I| apply bytes_at_nil; exact HA]|].
cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Ltac is_pos_lit p := lazymatch p with xH => idtac | xO ?q => is_pos_lit q | xI ?q => is_pos_lit q end.
Ltac is_Z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => is_pos_lit p | Zneg ?p => is_pos_lit p end.
Ltac fold_of_nat_lits_in H :=
repeat match type of H with
| context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in is_Z_lit v; change (Z.of_nat n) with v in H
end.
Ltac fold_of_nat_lits :=
repeat match goal with
| |- context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in is_Z_lit v; change (Z.of_nat n) with v
end.

Tactic Notation "chunk_uncons" hyp(H) "as" ident(H1) :=
apply rw_cells_uncons in H; destruct H as [H1 H]; cbn [csize] in H; fold_of_nat_lits_in H.

Lemma rw_cells_f32_split : forall segs m A l n,
rw_cells segs m A (f32 l) ->
rw_cells segs m A (f32 (firstn n l)) /\ rw_cells segs m (A + Z.of_nat (4 * length (firstn n l)))%Z (f32 (skipn n l)).
Proof.
intros segs m A l n H. rewrite <- (firstn_skipn n l) in H at 1. rewrite f32_app in H.
apply rw_cells_app in H. rewrite cells_size_f32 in H. exact H.
Qed.
Tactic Notation "chunk_split_f32" hyp(H) "at" constr(n) "as" ident(H1) :=
apply (rw_cells_f32_split _ _ _ _ n) in H; destruct H as [H1 H];
cbn [firstn skipn app length Nat.mul Nat.add] in H1, H; fold_of_nat_lits_in H.

Ltac chunk_snoc HD H1 :=
lazymatch type of HD with
| rw_cells ?segs ?m ?A ?cs =>
lazymatch type of H1 with
| rw_cells _ _ ?A1 [?c] =>
let E := fresh in
assert (E : A1 = (A + Z.of_nat (cells_size cs))%Z)
by (rewrite ?cells_size_app, ?cells_size_f32, ?length_app, ?length_f32; autorewrite with chunk_sizes; cbn [cells_size csize length]; lia);
rewrite E in H1; pose proof (rw_cells_snoc segs m A cs c HD H1) as HD';
clear HD H1 E; rename HD' into HD
end
end.

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

Ltac fix_lit_store :=
try (lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
end).

Ltac lstep := step; fix_lit_store.

Ltac release_frame FR ST hi :=
eapply stk_release in FR; [ | exact ST | lia ];
clear ST; rename FR into ST;
cbn [cells_size csize Nat.add] in ST;
lazymatch type of ST with
| stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia
end.

Ltac store_done :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
let E := addr_expr a in
(lazymatch a with
| wa _ => idtac
| Z_to_bv 64 _ => change (write_to_mem m a bs) with (write_to_mem m (wa E) bs)
| _ => replace (write_to_mem m a bs) with (write_to_mem m (wa E) bs) by (f_equal; addr_eq_tac)
end);

try (lazymatch goal with
| HI : mem_inv segs m, HS : store_ok segs m ?a' ?n = true |- _ =>
apply (mem_inv_store segs m (wa E) bs) in HI;
[ | first [ exact HS
| replace (wa E) with a' by (first [reflexivity | addr_eq_tac | symmetry; addr_eq_tac]);
first [ exact HS | simpl_sizes; exact HS ] ] ]
end);

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

Definition lit_disj (c2 : Z) (n2 : nat) (ca : Z) (na : nat) : bool :=
((c2 + Z.of_nat n2 <=? ca) || (ca + Z.of_nat na <=? c2))%Z.
Lemma frame_disj_lit : forall (A2 a X c2 ca : Z) (n2 na : nat),
A2 = (X + c2)%Z -> a = (X + ca)%Z -> lit_disj c2 n2 ca na = true ->
(A2 + Z.of_nat n2 <= a \/ a + Z.of_nat na <= A2)%Z.
Proof.
intros A2 a X c2 ca n2 na -> -> H. unfold lit_disj in H. apply orb_true_iff in H.
destruct H as [H|H]; apply Z.leb_le in H; [left|right]; lia.
Qed.
Ltac fast_disj :=
lazymatch goal with
| |- (?A2 + Z.of_nat ?n2 <= ?a \/ ?a + Z.of_nat ?na <= ?A2)%Z =>
eapply (frame_disj_lit A2 a _ _ _ n2 na);
[ first [ reflexivity | exact (eq_sym (Z.add_0_r _)) ]
| first [ reflexivity | exact (eq_sym (Z.add_assoc _ _ _)) | exact (eq_sym (Z.add_0_r _)) ]
| vm_compute; reflexivity ]
end.
Ltac tdisj := first [ fast_disj | simpl_sizes; slia ].
Ltac tdisj_arr := first [ fast_disj | simpl_sizes; simpl_arr_sizes; slia ].

Ltac transport_chunks_with segs m a bs HB0 HB1 :=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H; [ | exact HB0 | exact HB1 | tdisj_arr ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ | exact HB0 | exact HB1 | tdisj ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ | exact HB0 | exact HB1 | tdisj ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs m A2 xs a bs) in H; [ | exact HB0 | exact HB1 | tdisj_arr ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_frame segs m A2 xs a bs) in H; [ | exact HB0 | exact HB1 | tdisj_arr ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_frame segs m A2 xs a bs) in H; [ | exact HB0 | exact HB1 | tdisj_arr ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs m A2 xs a bs) in H; [ | exact HB0 | exact HB1 | tdisj_arr ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end.
Ltac transport_chunks_stock segs m a bs :=
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

Ltac same_base_hyps3 segs m a :=
let chk X :=
match goal with
| H1 : rw_cells segs m (X + _)%Z _, H2 : rw_cells segs m (X + _)%Z _, H3 : rw_cells segs m (X + _)%Z _ |- _ =>
tryif constr_eq H1 H2 then fail else tryif constr_eq H2 H3 then fail else tryif constr_eq H1 H3 then fail else idtac
end in
lazymatch a with
| (?X + ?c + Z.of_nat ?k)%Z => chk X
| (?X + Z.of_nat ?k)%Z => chk X
end.
Ltac transport_chunks segs m a bs ::=
let HB0 := fresh "HBta" in let HB1 := fresh "HBtb" in
first [ same_base_hyps3 segs m a;
assert (HB0 : (0 <= a)%Z) by lia;
assert (HB1 : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; slia);
transport_chunks_with segs m a bs HB0 HB1; clear HB0 HB1
| transport_chunks_stock segs m a bs ].

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Export X1ca.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Export X1bv.

Ltac post_call_stock segs m :=
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
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).

Ltac lx_name_rest PO :=
lazymatch goal with
| |- _ -> _ -> _ => let H := fresh "PC" in intros H; lx_name_rest PO
| |- _ -> _ => intros PO
end.
Ltac post_call_lean segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
sf_exs_then_all PO; clear PO;
intros E MUc WMc;
lazymatch goal with
| |- _ -> _ -> _ => intros MIc
| |- _ -> _ => intros MIc
end;
subst ms';
lazymatch type of MUc with
| munch _ m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try lx_name_rest PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).
Ltac post_call segs m ::= first [ post_call_lean segs m | post_call_stock segs m ].

Ltac finish_stock :=
apply evt_done;
lazymatch goal with |- ?P ?ms => try unfold P end;
hnf;
repeat (lazymatch goal with |- ex _ => eexists end);
lazymatch goal with
| |- _ = _ /\ _ => split; [ reflexivity | ]
| |- _ = _ => reflexivity
end;
repeat match goal with |- _ /\ _ => split end; try assumption.
Ltac finish ::=
apply evt_done;
lazymatch goal with |- ?P ?ms => try unfold P end;
hnf;
first [ sf_eexists_all | idtac ];
repeat (lazymatch goal with |- ex _ => eexists end);
lazymatch goal with
| |- _ = _ /\ _ => split; [ reflexivity | ]
| |- _ = _ => reflexivity
end;
repeat match goal with |- _ /\ _ => split end; try assumption.

Definition sf_dj (A sz A2 n2 : Z) : Prop := (A2 + n2 <= A \/ A + sz <= A2)%Z.
Definition sf_dj_no (A A2 : Z) : Prop := True.
Lemma sf_dj_use : forall (A sz A2 n2 a n k : Z),
sf_dj A sz A2 n2 -> a = (A + k)%Z -> ((0 <=? k) && (k + n <=? sz))%Z%bool = true ->
(A2 + n2 <= a \/ a + n <= A2)%Z.
Proof.
intros A sz A2 n2 a n k DJ -> H. apply andb_true_iff in H. destruct H as [H0 H1].
apply Z.leb_le in H0. apply Z.leb_le in H1. unfold sf_dj in DJ. lia.
Qed.

From Ltac2 Require Ltac2.
Module SfDjL2.
Import Ltac2.
Ltac2 rec nat_depth (n : constr) (acc : int) : int :=
if Int.gt acc 5000 then Control.zero (Tactic_failure None) else
lazy_match! n with
| S ?k => nat_depth k (Int.add acc 1)
| O => acc
| _ => Control.zero (Tactic_failure None)
end.
Ltac2 rec cells_total (cs : constr) (acc : int) : int :=
if Int.gt acc 20000 then Control.zero (Tactic_failure None) else
lazy_match! cs with
| nil => acc
| cons (C8 _) ?r => cells_total r (Int.add acc 8)
| cons (C4 _) ?r => cells_total r (Int.add acc 4)
| cons (C2 _) ?r => cells_total r (Int.add acc 2)
| cons (C1 _) ?r => cells_total r (Int.add acc 1)
| cons (CB ?n _) ?r => cells_total r (Int.add acc (nat_depth n 0))
| _ => Control.zero (Tactic_failure None)
end.
Ltac2 rec pos_of_int (i : int) : constr :=
if Int.le i 1 then constr:(xH) else
let h := pos_of_int (Int.div i 2) in
if Int.equal (Int.mod i 2) 0 then constr:(xO $h) else constr:(xI $h).
Ltac2 z_of_int (i : int) : constr := if Int.equal i 0 then constr:(Z0) else let p := pos_of_int i in constr:(Zpos $p).
Ltac2 exact_size (cs : constr) : unit :=
let t := cells_total cs 0 in
(if Int.gt t 20000 then Control.zero (Tactic_failure None) else ());
let z := z_of_int t in exact $z.
Ltac2 exact_size1 (c : Ltac1.t) : unit :=
match Ltac1.to_constr c with Some cs => Control.enter (fun () => exact_size cs) | None => Control.zero (Tactic_failure None) end.
End SfDjL2.
Ltac sf_sizeZ_exact cs := let f := ltac2:(c |- SfDjL2.exact_size1 c) in f cs.

Ltac sf_sizeZ cs k := let z0 := constr:(ltac:(sf_sizeZ_exact cs) : Z) in let z := eval vm_compute in z0 in k z.

Ltac sf_base e := lazymatch e with Z.add ?x _ => sf_base x | Z.sub ?x _ => sf_base x | _ => e end.
Ltac sf_dj_ensure A sz A2 n2 prep full :=
lazymatch goal with
| DJ : sf_dj A sz A2 n2 |- _ => idtac
| NO : sf_dj_no A A2 |- _ => idtac
| _ => let bA := sf_base A in let bA2 := sf_base A2 in
tryif constr_eq bA bA2 then idtac
else (let DJ := fresh "sfDJ_" in
first [ assert (DJ : sf_dj A sz A2 n2) by (unfold sf_dj; full)
| pose proof (I : sf_dj_no A A2) as DJ ])
end.
Ltac sf_dj_close A sz A2 n2 a n kn :=
lazymatch goal with DJ : sf_dj A sz A2 n2 |- _ => exact (sf_dj_use A sz A2 n2 a n (Z.of_nat kn) DJ eq_refl eq_refl) end.

Ltac sf_store_chunk segs m a k :=
lazymatch a with
| (?A + Z.of_nat ?kn)%Z =>
lazymatch goal with
| CH : rw_cells segs (write_to_mem m _ _) A ?cs |- _ =>
sf_sizeZ cs ltac:(fun sz => lazymatch sz with Zpos _ => k A kn sz end)
end
end.

Ltac sf_dj_pre segs m a A2 n2 prep full :=
first [ sf_store_chunk segs m a ltac:(fun A kn sz =>
lazymatch n2 with
| Z.of_nat (cells_size ?cs2) => sf_sizeZ cs2 ltac:(fun n2' => sf_dj_ensure A sz A2 n2' prep full)
| _ => sf_dj_ensure A sz A2 n2 prep full
end)
| idtac ].
Ltac sf_dj_side a bs :=
lazymatch goal with
| |- (?A2 + _ <= _ \/ _)%Z =>
lazymatch a with
| (?A + Z.of_nat ?kn)%Z =>
lazymatch goal with
| DJ : sf_dj A ?sz A2 ?n2 |- _ =>
let n := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in (Z.of_nat (@length byte bs)) in
exact (sf_dj_use A sz A2 n2 a n (Z.of_nat kn) DJ eq_refl eq_refl)
end
end
end.
Ltac transport_chunks_dj segs m a bs A kn sz HB0 HB1 :=
let n := eval cbv [length app cbytes cells_bytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes
Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in (Z.of_nat (@length byte bs)) in
repeat match goal with
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ tryif sf_sizeZ cs2 ltac:(fun _ => idtac)
then first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ | exact HB0 | exact HB1 | fast_disj ]
| sf_sizeZ cs2 ltac:(fun n2 =>
sf_dj_ensure A sz A2 n2 ltac:(simpl_sizes) ltac:(simpl_sizes; slia);
apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ | exact HB0 | exact HB1 | first [ sf_dj_close A sz A2 n2 a n kn | simpl_sizes; slia ] ]) ]
else (apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ | exact HB0 | exact HB1 | simpl_sizes; slia ])
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ tryif sf_sizeZ cs2 ltac:(fun _ => idtac)
then first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ | exact HB0 | exact HB1 | fast_disj ]
| sf_sizeZ cs2 ltac:(fun n2 =>
sf_dj_ensure A sz A2 n2 ltac:(simpl_sizes) ltac:(simpl_sizes; slia);
apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ | exact HB0 | exact HB1 | first [ sf_dj_close A sz A2 n2 a n kn | simpl_sizes; slia ] ]) ]
else (apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ | exact HB0 | exact HB1 | simpl_sizes; slia ])
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ sf_dj_ensure A sz A2 (Z.of_nat (length bs2)) ltac:(simpl_sizes; simpl_arr_sizes) ltac:(simpl_sizes; simpl_arr_sizes; slia);
apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | exact HB0 | exact HB1 | first [ sf_dj_close A sz A2 (Z.of_nat (length bs2)) a n kn | simpl_sizes; simpl_arr_sizes; slia ] ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ sf_dj_ensure A sz A2 (Z.of_nat (length xs)) ltac:(simpl_sizes; simpl_arr_sizes) ltac:(simpl_sizes; simpl_arr_sizes; slia);
apply (u8arr_frame segs m A2 xs a bs) in H;
[ | exact HB0 | exact HB1 | first [ sf_dj_close A sz A2 (Z.of_nat (length xs)) a n kn | simpl_sizes; simpl_arr_sizes; slia ] ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ sf_dj_ensure A sz A2 (4 * Z.of_nat (length xs))%Z ltac:(simpl_sizes; simpl_arr_sizes) ltac:(simpl_sizes; simpl_arr_sizes; slia);
apply (u32arr_frame segs m A2 xs a bs) in H;
[ | exact HB0 | exact HB1 | first [ sf_dj_close A sz A2 (4 * Z.of_nat (length xs))%Z a n kn | simpl_sizes; simpl_arr_sizes; slia ] ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ sf_dj_ensure A sz A2 (8 * Z.of_nat (length xs))%Z ltac:(simpl_sizes; simpl_arr_sizes) ltac:(simpl_sizes; simpl_arr_sizes; slia);
apply (u64arr_frame segs m A2 xs a bs) in H;
[ | exact HB0 | exact HB1 | first [ sf_dj_close A sz A2 (8 * Z.of_nat (length xs))%Z a n kn | simpl_sizes; simpl_arr_sizes; slia ] ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ sf_dj_ensure A sz A2 (Z.of_nat (length xs)) ltac:(simpl_sizes; simpl_arr_sizes) ltac:(simpl_sizes; simpl_arr_sizes; slia);
apply (u8ro_frame segs m A2 xs a bs) in H;
[ | exact HB0 | exact HB1 | first [ sf_dj_close A sz A2 (Z.of_nat (length xs)) a n kn | simpl_sizes; simpl_arr_sizes; slia ] ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end.
Ltac transport_chunks_lean segs m a bs :=
let HB0 := fresh "HBta" in let HB1 := fresh "HBtb" in
first [ same_base_hyps3 segs m a;
assert (HB0 : (0 <= a)%Z) by lia;
assert (HB1 : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; slia);
transport_chunks_with segs m a bs HB0 HB1; clear HB0 HB1
| transport_chunks_stock segs m a bs ].
Ltac transport_chunks segs m a bs ::=
let HB0 := fresh "HBta" in let HB1 := fresh "HBtb" in
first [ sf_store_chunk segs m a ltac:(fun A kn sz =>
assert (HB0 : (0 <= a)%Z) by lia;
assert (HB1 : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; slia);
transport_chunks_dj segs m a bs A kn sz HB0 HB1; clear HB0 HB1)
| transport_chunks_lean segs m a bs ].
