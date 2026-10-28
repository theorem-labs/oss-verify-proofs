(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BMem BArr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Fixpoint lbyte (log : list sentry) (b : expr) (x : Z) : option (option Z) :=
  match log with
  | [] => None
  | SE a w v :: rest =>
      if (expr_eqb (a_base a) b && (a_off a <=? x) && (x <? a_off a + Z.of_nat w))%bool then
        match v with
        | ELit z => Some (Some (Z.land (Z.shiftr z (8 * (x - a_off a))) 255))
        | _ => Some None
        end
      else lbyte rest b x
  end.

Fixpoint lbytes (log : list sentry) (b : expr) (x0 : Z) (base : list Z) : option (list Z) :=
  match base with
  | [] => Some []
  | v :: rest =>
      match lbyte log b x0, lbytes log b (x0 + 1) rest with
      | Some (Some v'), Some vs => Some (v' :: vs)
      | None, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Lemma Z_to_bv8_land : forall z, Z_to_bv 8 (Z.land z 255) = Z_to_bv 8 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. apply Z.mod_mod. lia.
Qed.

Lemma shiftr_mod64_byte : forall z j, 0 <= j -> j + 8 <= 64 ->
  Z_to_bv 8 (Z.shiftr (z mod 2 ^ 64) j) = Z_to_bv 8 (Z.shiftr z j).
Proof.
  intros z j Hj Hj8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
  apply Z.bits_inj'. intros n Hn.
  destruct (Z.lt_ge_cases n 8) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_nth : forall (w : nat) (u : Z) (j : nat), (j < w)%nat ->
  nth_error (Z_to_le_bytes w u) j = Some (Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat j))).
Proof.
  induction w as [|w IH]; intros u j Hj; [lia|].
  destruct j as [|j].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Z_to_le_bytes nth_error]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia.
    replace (8 * Z.of_nat (S j)) with (8 + 8 * Z.of_nat j) by lia. reflexivity.
Qed.

Lemma le_byte_nth : forall (w : nat) (z : Z) (j : nat), (j < w)%nat -> (w <= 8)%nat ->
  nth_error (word_to_le_bytes w (Z_to_bv 64 z)) j = Some (Z_to_bv 8 (Z.land (Z.shiftr z (8 * Z.of_nat j)) 255)).
Proof.
  intros w z j Hj Hw. unfold word_to_le_bytes. rewrite Z_to_le_bytes_nth by exact Hj.
  rewrite Z_to_bv8_land. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply shiftr_mod64_byte; lia.
Qed.

Lemma wbytes_hit_byte : forall bs m (addr : word) (y : Z) b,
  bv_unsigned addr <= y < bv_unsigned addr + Z.of_nat (length bs) -> bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64 ->
  nth_error bs (Z.to_nat (y - bv_unsigned addr)) = Some b ->
  wbytes m addr bs (Z_to_bv 64 y) = Some b.
Proof.
  induction bs as [|b0 rest IH]; intros m addr y b Hy Hnw Hn; cbn [length] in *; [lia|].
  cbn [wbytes].
  destruct (Z.eq_dec y (bv_unsigned addr)) as [E|NE].
  - subst y. rewrite Z.sub_diag in Hn. cbn in Hn. injection Hn as <-.
    destruct rest as [|r rest'].
    + cbn [wbytes]. cbv beta. rewrite Z_to_bv_bv_unsigned. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in *. rewrite wbytes_below.
      * cbv beta. rewrite Z_to_bv_bv_unsigned. rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. rewrite Z_to_bv_bv_unsigned. lia.
  - apply IH.
    + rewrite u_add1 by lia. lia.
    + rewrite u_add1 by lia. lia.
    + rewrite u_add1 by lia. replace (Z.to_nat (y - (bv_unsigned addr + 1))) with (Z.to_nat (y - bv_unsigned addr) - 1)%nat by lia.
      destruct (Z.to_nat (y - bv_unsigned addr)) as [|k] eqn:Ek; [lia|]. cbn in Hn. cbn. rewrite Nat.sub_0_r. exact Hn.
Qed.

Lemma wbytes_miss_byte : forall bs m (addr : word) (y : Z),
  0 <= y < 2 ^ 64 -> bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64 ->
  (y < bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= y) ->
  wbytes m addr bs (Z_to_bv 64 y) = m (Z_to_bv 64 y).
Proof.
  intros bs m addr y Hy Hnw [H|H].
  - apply wbytes_below; [exact Hnw | rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small; lia].
  - apply wbytes_above. rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small; lia.
Qed.

Definition lmiss (E : env) (b : expr) (y : Z) (e : sentry) : Prop :=
  expr_eqb (a_base (e_addr e)) b = true
  \/ estart E (e_addr e) + Z.of_nat (e_width e) <= y \/ y + 1 <= estart E (e_addr e).

Lemma mem_denot_lbyte : forall E M log b x,
  log_flat E log ->
  Forall (lmiss E b (bv_unsigned (edenot E b) + x)) log ->
  0 <= bv_unsigned (edenot E b) + x < 2 ^ 64 ->
  match lbyte log b x with
  | Some (Some v) => mem_denot E M log (Z_to_bv 64 (bv_unsigned (edenot E b) + x)) = Some (Z_to_bv 8 v)
  | Some None => True
  | None => mem_denot E M log (Z_to_bv 64 (bv_unsigned (edenot E b) + x)) = M (Z_to_bv 64 (bv_unsigned (edenot E b) + x))
  end.
Proof.
  intros E M log b x. induction log as [|[a w v] rest IH]; intros Hf HM Hy; [reflexivity|].
  cbn [log_flat] in Hf. destruct Hf as (Hw & Hfa & Hf).
  inversion HM as [|? ? HM0 HM1]; subst. specialize (IH Hf HM1 Hy).
  pose proof (flat_u E a (Z.of_nat w) Hfa) as Hu. pose proof Hfa as (F1 & F2 & F3 & F4).
  cbn [lbyte mem_denot].
  remember (bv_unsigned (edenot E b) + x) as y eqn:Ey.
  destruct (expr_eqb (a_base a) b) eqn:Eb; cbn [andb].
  - pose proof (expr_eqb_true _ _ Eb) as Eab.
    assert (Hst : estart E a = bv_unsigned (edenot E b) + a_off a) by (unfold estart; rewrite Eab; reflexivity).
    destruct ((a_off a <=? x) && (x <? a_off a + Z.of_nat w))%bool eqn:Ein.
    + apply andb_true_iff in Ein. destruct Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      destruct v as [z| | | | | | |]; try exact I.
      cbn [edenot]. apply wbytes_hit_byte.
      * rewrite CatExec.length_N_to_le_bytes, Hu. lia.
      * rewrite CatExec.length_N_to_le_bytes, Hu. lia.
      * rewrite Hu. rewrite le_byte_nth by lia.
        replace (8 * Z.of_nat (Z.to_nat (y - estart E a))) with (8 * (x - a_off a)) by lia. reflexivity.
    + rewrite wbytes_miss_byte.
      * exact IH.
      * lia.
      * rewrite CatExec.length_N_to_le_bytes, Hu. lia.
      * rewrite CatExec.length_N_to_le_bytes, Hu. apply andb_false_iff in Ein.
        destruct Ein as [E1|E2]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E2]; lia.
  - destruct HM0 as [HM0|HM0]; [cbn [e_addr] in HM0; rewrite Eb in HM0; discriminate|].
    cbn [e_addr e_width] in HM0.
    rewrite wbytes_miss_byte.
    + exact IH.
    + lia.
    + rewrite CatExec.length_N_to_le_bytes, Hu. lia.
    + rewrite CatExec.length_N_to_le_bytes, Hu. lia.
Qed.

Lemma lbytes_length : forall log b x0 base vs, lbytes log b x0 base = Some vs -> length vs = length base.
Proof.
  intros log b x0 base. revert x0. induction base as [|v rest IH]; intros x0 vs H; cbn [lbytes] in H.
  - injection H as <-. reflexivity.
  - destruct (lbyte log b x0) as [[v'|]|]; destruct (lbytes log b (x0 + 1) rest) as [vs'|] eqn:Er; try discriminate;
      injection H as <-; cbn; f_equal; exact (IH _ _ Er).
Qed.

Lemma lbytes_nth : forall log b base x0 vs i,
  lbytes log b x0 base = Some vs -> (i < length base)%nat ->
  (lbyte log b (x0 + Z.of_nat i) = Some (Some (nth i vs 0)))
  \/ (lbyte log b (x0 + Z.of_nat i) = None /\ nth i vs 0 = nth i base 0).
Proof.
  intros log b base. induction base as [|v rest IH]; intros x0 vs i H Hi; cbn [length] in Hi; [lia|].
  cbn [lbytes] in H.
  destruct (lbyte log b x0) as [[v'|]|] eqn:E0; destruct (lbytes log b (x0 + 1) rest) as [vs'|] eqn:Er; try discriminate;
    injection H as <-.
  - destruct i as [|i]; [left; rewrite Z.add_0_r; exact E0|].
    destruct (IH (x0 + 1) vs' i Er ltac:(lia)) as [K|K]; [left | right]; replace (x0 + Z.of_nat (S i)) with (x0 + 1 + Z.of_nat i) by lia; exact K.
  - destruct i as [|i]; [right; rewrite Z.add_0_r; split; [exact E0 | reflexivity]|].
    destruct (IH (x0 + 1) vs' i Er ltac:(lia)) as [K|K]; [left | right]; replace (x0 + Z.of_nat (S i)) with (x0 + 1 + Z.of_nat i) by lia; exact K.
Qed.

Lemma bytes_at_mem_denot : forall segs E M log b x0 base vs,
  log_flat E log ->
  (forall i, 0 <= i < Z.of_nat (length base) -> Forall (lmiss E b (bv_unsigned (edenot E b) + x0 + i)) log) ->
  0 <= bv_unsigned (edenot E b) + x0 -> bv_unsigned (edenot E b) + x0 + Z.of_nat (length base) <= 2 ^ 64 ->
  BMem.bytes_at segs M (bv_unsigned (edenot E b) + x0) (map (Z_to_bv 8) base) ->
  lbytes log b x0 base = Some vs ->
  BMem.bytes_at segs (mem_denot E M log) (bv_unsigned (edenot E b) + x0) (map (Z_to_bv 8) vs).
Proof.
  intros segs E M log b x0 base vs Hf HM H0 H1 (B0 & B1 & BB) Hl.
  pose proof (lbytes_length _ _ _ _ _ Hl) as Hlen.
  rewrite length_map in B1.
  split; [exact H0|]. split; [rewrite length_map; lia|].
  intros i Hi. rewrite length_map in Hi.
  pose proof (mem_denot_lbyte E M log b (x0 + Z.of_nat i) Hf) as K.
  assert (HMi : Forall (lmiss E b (bv_unsigned (edenot E b) + (x0 + Z.of_nat i))) log).
  { replace (bv_unsigned (edenot E b) + (x0 + Z.of_nat i)) with (bv_unsigned (edenot E b) + x0 + Z.of_nat i) by lia.
    apply HM. lia. }
  specialize (K HMi ltac:(lia)).
  unfold BMem.mrd, BMem.wa. replace (bv_unsigned (edenot E b) + x0 + Z.of_nat i) with (bv_unsigned (edenot E b) + (x0 + Z.of_nat i)) by lia.
  rewrite nth_error_map.
  destruct (lbytes_nth log b base x0 vs i Hl ltac:(lia)) as [L|(L & Lv)]; rewrite L in K.
  - rewrite K. rewrite (nth_error_nth' vs 0) by lia. reflexivity.
  - rewrite K. specialize (BB i ltac:(rewrite length_map; lia)). unfold BMem.mrd, BMem.wa in BB.
    replace (bv_unsigned (edenot E b) + x0 + Z.of_nat i) with (bv_unsigned (edenot E b) + (x0 + Z.of_nat i)) in BB by lia.
    rewrite BB. rewrite nth_error_map. rewrite (nth_error_nth' base 0) by lia. rewrite (nth_error_nth' vs 0) by lia.
    cbn. rewrite Lv. reflexivity.
Qed.

Lemma u8arr_mem_denot : forall E M log b x0 base vs,
  log_flat E log ->
  (forall i, 0 <= i < Z.of_nat (length base) -> Forall (lmiss E b (bv_unsigned (edenot E b) + x0 + i)) log) ->
  0 <= bv_unsigned (edenot E b) + x0 -> bv_unsigned (edenot E b) + x0 + Z.of_nat (length base) <= 2 ^ 64 ->
  BArr.u8arr ASEGS M (bv_unsigned (edenot E b) + x0) (map (Z_to_bv 8) base) ->
  lbytes log b x0 base = Some vs ->
  BArr.u8arr ASEGS (mem_denot E M log) (bv_unsigned (edenot E b) + x0) (map (Z_to_bv 8) vs).
Proof.
  intros E M log b x0 base vs Hf HM H0 H1 [HB HW] Hl. split.
  - eapply bytes_at_mem_denot; eassumption.
  - pose proof (lbytes_length _ _ _ _ _ Hl) as Hlen. rewrite length_map in *. rewrite Hlen.
    destruct HW as (W0 & W1 & W). split; [exact W0|]. split; [exact W1|].
    intros i Hi. exact (LbB_Conv.wmono_mem_denot E M log _ (W i Hi)).
Qed.

Definition gran_of (sz : Z) (inscope : bool) : list Z :=
  if inscope then repeat 0 (Z.to_nat (sz / 8)) ++ (if sz mod 8 =? 0 then [] else [sz mod 8])
  else repeat 248 (Z.to_nat ((sz + 7) / 8)).

Fixpoint fsh_objs (objs : list (Z * Z)) (i : nat) (ins : list nat) (pos : Z) : list Z :=
  match objs with
  | [] => []
  | (off, sz) :: rest =>
      repeat 242 (Z.to_nat (off / 8 - pos)) ++ gran_of sz (existsb (Nat.eqb i) ins)
      ++ fsh_objs rest (Datatypes.S i) ins ((off + sz + 7) / 8)
  end.

Definition fsh_pat (objs : list (Z * Z)) (nsh : Z) (ins : list nat) : list Z :=
  let body := fsh_objs objs 0 ins 4 in
  repeat 241 4 ++ body ++ repeat 243 (Z.to_nat (nsh - 4 - Z.of_nat (length body))).

Definition fix_of (FB : expr) (FSHN : Z) (s : sidecond) : option kentry :=
  match s with
  | SCReadBase a 1 _ _ => if is_shadow_addr a then Some (KWord a 1 (ELit 0)) else None
  | SCDisj a1 n1 a2 n2 =>
      if (is_shadow_addr a1 && expr_eqb (a_base a2) FB)%bool then Some (KDisj a1 (ELit 1) (SA FB SHBASE) (ELit FSHN))
      else if (is_shadow_addr a2 && expr_eqb (a_base a1) FB)%bool then Some (KDisj a2 (ELit 1) (SA FB SHBASE) (ELit FSHN))
      else None
  | _ => None
  end.

Definition kentry_eqb (x y : kentry) : bool :=
  match x, y with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
  | KDisj a1 n1 a2 n2, KDisj a1' n1' a2' n2' =>
      saddr_eqb a1 a1' && expr_eqb n1 n1' && saddr_eqb a2 a2' && expr_eqb n2 n2'
  | _, _ => false
  end.

Fixpoint add_fixes (FB : expr) (FSHN : Z) (scs : list sidecond) (acc : list kentry) : list kentry :=
  match scs with
  | [] => acc
  | s :: t =>
      match fix_of FB FSHN s with
      | Some K => if existsb (kentry_eqb K) acc then add_fixes FB FSHN t acc else add_fixes FB FSHN t (acc ++ [K])
      | None => add_fixes FB FSHN t acc
      end
  end.

Fixpoint kn_fix2 (fuel : nat) (xfuel : nat) (FB : expr) (FSHN : Z) (stops : list Z) (scr : scripts) (pc : Z) (sr : list expr)
         (kn : list kentry) (nx : N) : list kentry :=
  match fuel with
  | O => kn
  | Datatypes.S f =>
      let '(_, scs, _) := sym_exec ASEGS xfuel true stops scr (SS pc sr [] kn nx) [] in
      let kn' := add_fixes FB FSHN scs kn in
      if Nat.eqb (length kn') (length kn) then kn else kn_fix2 f xfuel FB FSHN stops scr pc sr kn' nx
  end.

Definition sym_in1 (b : expr) (lo hi : Z) (se : sentry) : bool :=
  (expr_eqb (a_base (e_addr se)) b && (lo <=? a_off (e_addr se)) && (a_off (e_addr se) + Z.of_nat (e_width se) <=? hi))%bool.
Fixpoint sym_inside (wins : list (expr * Z * Z)) (se : sentry) : bool :=
  match wins with
  | [] => false
  | (b, lo, hi) :: t => (sym_in1 b lo hi se || sym_inside t se)%bool
  end.
Definition num_wins (E : env) (wins : list (expr * Z * Z)) : list (Z * Z) :=
  map (fun '(b, lo, hi) => (bv_unsigned (edenot E b) + lo, bv_unsigned (edenot E b) + hi)) wins.

Lemma sym_inside_sound : forall E wins se,
  sym_inside wins se = true -> BLFrame.inside (num_wins E wins) (estart E (e_addr se)) (Z.of_nat (e_width se)).
Proof.
  intros E wins se. induction wins as [|[[b lo] hi] t IH]; intros Hs; cbn in *; [discriminate|].
  apply orb_true_iff in Hs as [Hs|Hs].
  - left. unfold sym_in1 in Hs. apply andb_true_iff in Hs as [Hs H2]. apply andb_true_iff in Hs as [Hb H1].
    apply expr_eqb_true in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold estart. rewrite Hb. lia.
  - right. exact (IH Hs).
Qed.

Lemma munch_sym : forall E M log wins,
  log_flat E log -> forallb (sym_inside wins) log = true ->
  BLFrame.munch (num_wins E wins) M (mem_denot E M log).
Proof.
  intros E M log wins Hf Hb. apply LbB_Conv.munch_mem_denot; [exact Hf|].
  apply Forall_forall. intros se Hse. apply sym_inside_sound. exact (proj1 (forallb_forall _ _) Hb se Hse).
Qed.

Definition others (b : expr) (log : list sentry) : list sentry :=
  List.filter (fun se => negb (expr_eqb (a_base (e_addr se)) b)) log.

Lemma lmiss_of_others : forall E b log y0 n,
  Forall (fun se => estart E (e_addr se) + Z.of_nat (e_width se) <= y0 \/ y0 + n <= estart E (e_addr se)) (others b log) ->
  forall i, 0 <= i < n -> Forall (lmiss E b (y0 + i)) log.
Proof.
  intros E b log y0 n HO i Hi. apply Forall_forall. intros se Hse. unfold lmiss.
  destruct (expr_eqb (a_base (e_addr se)) b) eqn:Eb; [left; reflexivity|]. right.
  assert (Hin : In se (others b log)) by (unfold others; apply (proj2 (filter_In _ _ _)); split; [exact Hse | rewrite Eb; reflexivity]).
  destruct (proj1 (Forall_forall _ _) HO se Hin); [left | right]; lia.
Qed.

Ltac xrun_big fxg segs R pc M rom HR HK fuel stops scr nx :=
  lazymatch type of HR with
  | SymExec3Sound.SX2S.regs_ok ?E ?sr R =>
    lazymatch type of HK with
    | SymExec3Sound.SX2S.know_ok segs _ M ?kn =>
        let r := eval vm_compute in (SymExec3.SX2.sym_exec segs fuel true stops scr (SymExec3.SX2.SS pc sr [] kn nx) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
            let SS := fresh "SSbig" in
            pose (SS := ss');
            let Hsc := fresh "Hsc" in
            assert (Hsc : SymExec3Sound.SX2S.scs_denot segs M E scs);
            [ | let R' := fresh "R'" in let HR' := fresh "HR'" in
                let Hlf := fresh "Hlf" in let Hms := fresh "Hms" in
                destruct (@SymRun3.run_sound fxg segs fuel stops scr pc sr kn nx SS scs scr' E M rom R
                           ltac:(vm_cast_no_check (@eq_refl _ (SS, scs, scr'))) HR HK Hsc)
                  as (R' & HR' & Hlf & Hms);
                clear Hsc ]
        end
    end
  end.
