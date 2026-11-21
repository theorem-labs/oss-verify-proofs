(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition hid (P : Prop) : Prop := P.
Ltac hide_or H := lazymatch type of H with hid _ => idtac | ?T => change T with (hid T) in H end.

Ltac sh_lia :=
  idtac;
  rewrite ?shad_div; unfold ASHOFF;
  rewrite ?Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
  Z.div_mod_to_equations; lia.

Lemma shr3_off : forall X k, X mod 8 = 0 -> Z.shiftr (X + k) 3 = Z.shiftr X 3 + k / 8.
Proof.
  intros X k H. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (Z.div_mod X 8) at 1 by lia. rewrite H, Z.add_0_r.
  rewrite (Z.mul_comm 8), Z.div_add_l by lia. reflexivity.
Qed.
Lemma sh_in_range_off : forall X k N,
  X mod 8 = 0 -> ((0 <=? k / 8) && (k / 8 <? N))%bool = true ->
  Z.shiftr X 3 + 2147450880 <= Z.shiftr (X + k) 3 + 2147450880 < Z.shiftr X 3 + 2147450880 + N.
Proof.
  intros X k N H B. rewrite (shr3_off X k H). apply andb_prop in B. destruct B as [B1 B2].
  apply Z.leb_le in B1. apply Z.ltb_lt in B2. lia.
Qed.
Lemma sh_in_range_0 : forall X N, (0 <? N) = true ->
  Z.shiftr X 3 + 2147450880 <= Z.shiftr X 3 + 2147450880 < Z.shiftr X 3 + 2147450880 + N.
Proof. intros X N B. apply Z.ltb_lt in B. lia. Qed.
Lemma sh_acc_off : forall X k N,
  X mod 8 = 0 -> ((0 <=? k / 8) && (k / 8 <? N))%bool = true ->
  Z.shiftr X 3 + 2147450880 <= Z.shiftr (X + k) 3 + 2147450880 /\ Z.shiftr (X + k) 3 + 2147450880 + 1 <= Z.shiftr X 3 + 2147450880 + N.
Proof. intros X k N H B. pose proof (sh_in_range_off X k N H B). lia. Qed.
Lemma sh_acc_0 : forall X N, (0 <? N) = true ->
  Z.shiftr X 3 + 2147450880 <= Z.shiftr X 3 + 2147450880 /\ Z.shiftr X 3 + 2147450880 + 1 <= Z.shiftr X 3 + 2147450880 + N.
Proof. intros X N B. apply Z.ltb_lt in B. lia. Qed.

Ltac sh_range_fast :=
  idtac;
  lazymatch goal with
  | |- Z.shiftr ?X 3 + 2147450880 <= Z.shiftr (?X + ?k) 3 + 2147450880 < Z.shiftr ?X 3 + 2147450880 + ?N =>
      apply (sh_in_range_off X k N); [assumption | vm_compute; reflexivity]
  | |- Z.shiftr ?X 3 + 2147450880 <= Z.shiftr ?X 3 + 2147450880 < Z.shiftr ?X 3 + 2147450880 + ?N =>
      apply (sh_in_range_0 X N); vm_compute; reflexivity
  end.
Ltac sh_acc_fast :=
  idtac;
  lazymatch goal with
  | |- Z.shiftr ?X 3 + 2147450880 <= Z.shiftr (?X + ?k) 3 + 2147450880 /\ _ <= Z.shiftr ?X 3 + 2147450880 + ?N =>
      apply (sh_acc_off X k N); [assumption | vm_compute; reflexivity]
  | |- Z.shiftr ?X 3 + 2147450880 <= Z.shiftr ?X 3 + 2147450880 /\ _ <= Z.shiftr ?X 3 + 2147450880 + ?N =>
      apply (sh_acc_0 X N); vm_compute; reflexivity
  end.
Ltac sh_range :=
  first [ lazymatch goal with
          | |- Z.shiftr ?X 3 + 2147450880 <= Z.shiftr (?X + ?k) 3 + 2147450880 < Z.shiftr ?X 3 + 2147450880 + ?N =>
              apply (sh_in_range_off X k N); [assumption | vm_compute; reflexivity]
          | |- Z.shiftr ?X 3 + 2147450880 <= Z.shiftr ?X 3 + 2147450880 < Z.shiftr ?X 3 + 2147450880 + ?N =>
              apply (sh_in_range_0 X N); vm_compute; reflexivity
          end
        | sh_lia ].
Ltac sh_acc :=
  first [ lazymatch goal with
          | |- Z.shiftr ?X 3 + 2147450880 <= Z.shiftr (?X + ?k) 3 + 2147450880 /\ _ <= Z.shiftr ?X 3 + 2147450880 + ?N =>
              apply (sh_acc_off X k N); [assumption | vm_compute; reflexivity]
          | |- Z.shiftr ?X 3 + 2147450880 <= Z.shiftr ?X 3 + 2147450880 /\ _ <= Z.shiftr ?X 3 + 2147450880 + ?N =>
              apply (sh_acc_0 X N); vm_compute; reflexivity
          end
        | sh_lia ].

Section WithSegs.
Variable segs : list Segment.

Lemma ov_read1_sh0 : forall m s1 s2 a,
  shadow_bytes m s1 s2 (fun _ => 0) ->
  s1 <= Z.shiftr a 3 + 2147450880 < s2 ->
  ov_read_bytes segs m (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m s1 s2 a SB H.
  exact (ov_read1_of_shadow_bytes segs m s1 s2 (fun _ => 0) (Z.shiftr a 3 + 2147450880) SB H).
Qed.

Lemma ov_read1_shv : forall m s v a,
  m (wa s) = Some (Z_to_bv 8 v) -> 0 <= s -> s + 1 <= 2^64 ->
  s = Z.shiftr a 3 + 2147450880 ->
  ov_read_bytes segs m (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [Z_to_bv 8 v].
Proof.
  intros m s v a H A B E. subst s. exact (ov_read1_of_byte segs m _ _ A B H).
Qed.

Lemma ov_read1_shc : forall m s1 s2 v s,
  shadow_bytes m s1 s2 (fun _ => v) -> s1 <= s < s2 ->
  ov_read_bytes segs m (Z_to_bv 64 s) 1 = Some [Z_to_bv 8 v].
Proof. intros m s1 s2 v s SB H. exact (ov_read1_of_shadow_bytes segs m s1 s2 (fun _ => v) s SB H). Qed.
Lemma shc_mu : forall W m m' s1 s2 v,
  shadow_bytes m s1 s2 (fun _ => v) -> munch W m m' -> disjoint_from W s1 (s2 - s1) ->
  shadow_bytes m' s1 s2 (fun _ => v).
Proof. intros W m m' s1 s2 v SB MU D. exact (shadow_bytes_munch W m m' s1 s2 _ SB MU D). Qed.

Lemma sh0_mu : forall W m m' s1 s2,
  shadow_bytes m s1 s2 (fun _ => 0) -> munch W m m' -> disjoint_from W s1 (s2 - s1) ->
  shadow_bytes m' s1 s2 (fun _ => 0).
Proof. intros W m m' s1 s2 SB MU D. exact (shadow_bytes_munch W m m' s1 s2 _ SB MU D). Qed.

Lemma unp_of_sh0 : forall m X N lo hi,
  shadow_bytes m (Z.shiftr X 3 + 2147450880) (Z.shiftr X 3 + 2147450880 + N) (fun _ => 0) ->
  X mod 8 = 0 -> 0 <= X -> X <= lo -> lo <= hi -> hi <= X + 8 * N -> hi <= 2^64 ->
  unpoisoned m lo hi.
Proof.
  intros m X N lo hi SB X8 X0 L1 L2 L3 L4.
  destruct (Z.eq_dec lo hi) as [->|NE].
  { destruct SB as (A & B & _). split; [lia|]. split; [lia|]. intros; lia. }
  eapply (unpoisoned_of_zero m _ _ (fun _ => 0) lo hi SB); [reflexivity| | | lia| exact L4].
  - rewrite shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
  - rewrite shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma unp_check_mu : forall W m m' lo hi a N,
  unpoisoned m lo hi -> munch W m m' -> disjoint_from W (shad lo) (shad (hi - 1) + 1 - shad lo) ->
  lo <= a -> a + N <= hi -> 1 <= N -> a mod 8 + N <= 8 ->
  exists b, ov_read_bytes segs m' (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)).
Proof.
  intros W m m' lo hi a N U MU DJ H1 H2 H3 H4.
  pose proof (unpoisoned_munch W m m' lo hi U MU DJ) as U'.
  destruct (unpoisoned_check_rd segs m' lo hi a N U' H1 H2 H3 H4) as (b & RD & CK).
  exists b. split; [| exact CK]. unfold wa, shad, ASHOFF in RD. rewrite Z.add_comm in RD. exact RD.
Qed.

Definition c1z : cell := C1 (Z_to_bv 8 0).
Lemma shadow8_c1s : forall m s, rw_cells segs m s [C8 (Z_to_bv 64 0)] ->
  rw_cells segs m s [c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.
Lemma shadow16_c1s : forall m s, rw_cells segs m s [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells segs m s [c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.
Lemma shadow32_c1s : forall m s, rw_cells segs m s [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells segs m s [c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z;
                     c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z; c1z].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

Lemma pay_read : forall m A (bs : list Z) (i : Z),
  bytes_at segs m A (map (Z_to_bv 8) bs) -> 0 <= i < Z.of_nat (length bs) ->
  ov_read_bytes segs m (Z_to_bv 64 (A + i)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat i) bs 0)].
Proof.
  intros m A bs i HB Hi.
  apply (u8ro_read segs m A (map (Z_to_bv 8) bs) i); [exact HB| | lia | reflexivity].
  rewrite nth_error_map. rewrite (nth_error_nth' bs 0) by lia. reflexivity.
Qed.

End WithSegs.

Definition bz (bs : list Z) (i : Z) : Z := nth (Z.to_nat i) bs 0.
Lemma bz_range : forall bs i, Forall (fun b => 0 <= b < 256) bs -> 0 <= bz bs i < 256.
Proof.
  intros bs i F. unfold bz.
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length bs)) as [L|L].
  - apply (proj1 (Forall_forall _ _) F). apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.
Lemma bz_val : forall bs i, Forall (fun b => 0 <= b < 256) bs -> bv_unsigned (Z_to_bv 8 (bz bs i)) = bz bs i.
Proof.
  intros bs i F. pose proof (bz_range bs i F) as R.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia.
Qed.

Ltac solve_load_sh0_with tac :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880)) 1] =>
      match goal with
      | SB : shadow_bytes m ?s1 ?s2 (fun _ => 0) |- _ =>
          rewrite (ov_read1_sh0 segs m s1 s2 a SB) by tac
      | MU : munch ?W ?m0 m, SB : shadow_bytes ?m0 ?s1 ?s2 (fun _ => 0), DJ : disjoint_from ?W ?s1 (?s2 - ?s1) |- _ =>
          rewrite (ov_read1_sh0 segs m s1 s2 a (sh0_mu W m0 m s1 s2 SB MU DJ)) by tac
      end
  end.
Ltac solve_load_sh0 :=
  first [ solve_load_sh0_with sh_range_fast | solve_load_sh0_with sh_lia ];
  load_post.

Ltac solve_load_shlit :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 ?s) 1] =>
      is_Zlit s;
      match goal with
      | SB : shadow_bytes m ?s1 ?s2 (fun _ => ?v) |- _ =>
          is_Zlit s1; is_Zlit s2;
          rewrite (ov_read1_shc segs m s1 s2 v s SB) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity)
      | MU : munch ?W ?m0 m, SB : shadow_bytes ?m0 ?s1 ?s2 (fun _ => ?v), DJ : disjoint_from ?W ?s1 (?s2 - ?s1) |- _ =>
          is_Zlit s1; is_Zlit s2;
          rewrite (ov_read1_shc segs m s1 s2 v s (shc_mu W m0 m s1 s2 v SB MU DJ))
            by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity)
      end
  end;
  load_post.

Ltac acc_hint_sh_with tac :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG (Z.shiftr ?X 3 + 2147450880) ?len |- _ =>
          apply (rng_acc_litZ RNG (Z.shiftr X 3 + 2147450880) len (Z.shiftr a 3 + 2147450880) n nz H (@eq_refl Z nz)); [first [exact (Z.le_refl 1) | lia]| tac]
      | H : rng RNG (shad ?X) ?len |- _ =>
          apply (rng_acc_litZ RNG (shad X) len (Z.shiftr a 3 + 2147450880) n nz H (@eq_refl Z nz)); [first [exact (Z.le_refl 1) | lia]| tac]
      | H : rng RNG ?lo ?len |- _ =>
          is_closed_lits lo;
          apply (rng_acc_litZ RNG lo len (Z.shiftr a 3 + 2147450880) n nz H (@eq_refl Z nz)); [first [exact (Z.le_refl 1) | lia]| tac]
      end
  end.
Ltac acc_hint_sh := first [ acc_hint_sh_with sh_acc_fast | acc_hint_sh_with sh_lia ].

Lemma mod8_room1 : forall a, a mod 8 + 1 <= 8.
Proof. intros a. pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.
Lemma mod16_mod8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof. intros a H. apply Z.mod_divide in H; [| lia]. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [| exact H]. exists 2. reflexivity. Qed.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Std Env List Array Ident.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import LiaTuning.
Set Default Proof Mode "Classic".

Fixpoint conjs (l : list Prop) : Prop :=
  match l with
  | nil => True
  | A :: l' => match l' with nil => A | _ => A /\ conjs l' end
  end.
Fixpoint arrows (l : list Prop) (G : Prop) : Prop := match l with nil => G | A :: l' => A -> arrows l' G end.
Lemma conjs_elim : forall l G, conjs l -> arrows l G -> G.
Proof.
  induction l as [|A l IH]; intros G H K; [exact K|].
  destruct l as [|B l']; [exact (K H)|].
  destruct H as [a r]. exact (IH G r (K a)).
Qed.

Module AndElim.
  Ltac2 rec spine (k : int) (t : constr) : constr list :=
    if Int.le k 1 then [t] else
    let t := lazy_match! t with
             | _ /\ _ => t
             | _ => Std.eval_hnf t
             end in
    lazy_match! t with
    | ?a /\ ?b => a :: spine (Int.sub k 1) b
    | _ => Control.zero (Tactic_failure (Some (Message.of_string "and_elim: fewer conjuncts than asked for")))
    end.
  Ltac2 rec mk_list (l : constr list) : constr :=
    match l with
    | [] => constr:(@nil Prop)
    | a :: r => let r' := mk_list r in constr:(@cons Prop $a $r')
    end.
  Ltac2 rec mk_arrows (l : constr list) (g : constr) : constr :=
    match l with
    | [] => g
    | a :: r => let r' := mk_arrows r g in constr:($a -> $r')
    end.
  Ltac2 and_elim (h : ident) (k : int) : unit :=
    let hc := Control.hyp h in
    let l := spine k (Constr.type hc) in
    let g := Control.goal () in
    let ll := mk_list l in
    let ar := mk_arrows l g in
    Control.refine (fun () => open_constr:(conjs_elim $ll $g $hc _));
    Std.change None (fun _ => ar) { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences };
    (match Control.case (fun () => Std.clear [h]) with Val _ => () | Err _ => () end).
End AndElim.
Ltac2 and_elim_l1 (h : Ltac1.t) (k : Ltac1.t) : unit :=
  let id := match Ltac1.to_ident h with
            | Some id => id
            | None => (match Ltac1.to_constr h with
                       | Some c => (match Constr.Unsafe.kind c with
                                    | Constr.Unsafe.Var id => id
                                    | _ => Control.zero (Tactic_failure (Some (Message.of_string "and_elim: not a hypothesis")))
                                    end)
                       | None => Control.zero (Tactic_failure (Some (Message.of_string "and_elim: not a hypothesis")))
                       end)
            end in
  let rec n (c : constr) : int := lazy_match! c with O => 0 | S ?p => Int.add 1 (n p) end in
  match Ltac1.to_constr k with
  | Some kc => AndElim.and_elim id (n kc)
  | None => Control.zero (Tactic_failure (Some (Message.of_string "and_elim: arity")))
  end.
Ltac and_elim_tac H k := let f := ltac2:(h k |- and_elim_l1 h k) in f H k.
Tactic Notation "and_elim" hyp(H) constr(k) := and_elim_tac H k.

Module LWLia.
  Ltac2 rec arith_logic (t : constr) : bool :=
    lazy_match! t with
    | ?a /\ ?b => if arith_logic a then arith_logic b else false
    | ?a \/ ?b => if arith_logic a then arith_logic b else false
    | ?a <-> ?b => if arith_logic a then arith_logic b else false
    | not ?a => arith_logic a
    | ?a -> ?b => if arith_logic a then arith_logic b else false
    | _ => zt_plain_arith t
    end.
  Ltac2 rec vars_of (fuel : int array) (acc : ident list) (c : constr) : ident list :=
    if Int.le (Array.get fuel 0) 0 then acc else
    (Array.set fuel 0 (Int.sub (Array.get fuel 0) 1);
     match Constr.Unsafe.kind c with
     | Constr.Unsafe.Var id => if List.exist (Ident.equal id) acc then acc else id :: acc
     | Constr.Unsafe.App f args => Array.fold_left (vars_of fuel) (vars_of fuel acc f) args
     | Constr.Unsafe.Prod b body => vars_of fuel (vars_of fuel acc (Constr.Binder.type b)) body
     | Constr.Unsafe.Cast c' _ _ => vars_of fuel acc c'
     | _ => acc
     end).
  Ltac2 rec meets (xs : ident list) (ys : ident list) : bool :=
    match xs with
    | [] => false
    | x :: xs' => if List.exist (Ident.equal x) ys then true else meets xs' ys
    end.
  Ltac2 rec newest_plain (hs : (ident * constr option * constr) list) : constr option :=
    match hs with
    | [] => None
    | (id, body, ty) :: r =>
        match newest_plain r with
        | Some t => Some t
        | None => match body with Some _ => None | None => if zt_is_local id then (if arith_logic ty then Some ty else None) else None end
        end
    end.
  Ltac2 prune_rel () : unit :=
    let hs := Control.hyps () in
    let g := Control.goal () in
    let gv := vars_of (Array.make 1 4000) [] g in
    let gv := match gv with
              | [] => match newest_plain hs with Some t => vars_of (Array.make 1 2000) [] t | None => [] end
              | _ => gv
              end in
    let ids := List.map_filter (fun (id, body, ty) =>
                  match body with
                  | Some _ => None
                  | None =>
                      if Bool.neg (zt_is_local id) then None
                      else if zt_plain_arith ty then None
                      else if arith_logic ty then (if meets (vars_of (Array.make 1 2000) [] ty) gv then None else Some id)
                      else None
                  end) hs in
    match ids with [] => () | _ :: _ => Std.clear ids end.
End LWLia.
Ltac lw_prune_rel := ltac2:(Control.enter LWLia.prune_rel).

Ltac lia1 := zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | lw_prune_rel; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
