(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxEntryRel AxAcct.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record aent : Type := AE { ae_base : lin; ae_size : Z; ae_na : bool }.

Definition ent_val (ρ : valuation) (e : aent) : bv 64 * bv 64 :=
  (Z_to_bv 64 (leval ρ (ae_base e)), Z_to_bv 64 (ae_size e)).

Definition lin_eqb (f g : lin) : bool := (fst f =? fst g) && teqb (snd f) (snd g).

Lemma lin_eqb_eq (f g : lin) : lin_eqb f g = true -> f = g.
Proof.
  destruct f as [c1 t1], g as [c2 t2]. unfold lin_eqb. cbn [fst snd]. intros H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply teqb_eq in H2. subst. reflexivity.
Qed.

Lemma lin_eqb_refl (f : lin) : lin_eqb f f = true.
Proof.
  destruct f as [c t]. unfold lin_eqb. cbn [fst snd]. rewrite Z.eqb_refl. cbn [andb].
  induction t as [|[x k] r IH]; [reflexivity|]. cbn [teqb]. rewrite Uint63.eqb_refl, Z.eqb_refl. exact IH.
Qed.

Definition aent_eqb (a b : aent) : bool :=
  lin_eqb (ae_base a) (ae_base b) && (ae_size a =? ae_size b) && Bool.eqb (ae_na a) (ae_na b).

Lemma aent_eqb_eq (a b : aent) : aent_eqb a b = true -> a = b.
Proof.
  destruct a as [f1 n1 b1], b as [f2 n2 b2]. unfold aent_eqb. cbn [ae_base ae_size ae_na]. intros H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply lin_eqb_eq in H1. apply Z.eqb_eq in H2. apply Bool.eqb_prop in H3. subst. reflexivity.
Qed.

Lemma aent_eqb_refl (a : aent) : aent_eqb a a = true.
Proof. destruct a as [f n b]. unfold aent_eqb. cbn [ae_base ae_size ae_na]. rewrite lin_eqb_refl, Z.eqb_refl, Bool.eqb_reflx. reflexivity. Qed.

Lemma aent_eq_dec (a b : aent) : {a = b} + {a <> b}.
Proof.
  destruct (aent_eqb a b) eqn:E; [left; exact (aent_eqb_eq a b E)|].
  right. intros ->. rewrite aent_eqb_refl in E. discriminate E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive afd : Type := FDStd | FDDir | FDFile (off : lin) (vl vb0 vb1 : int) | FDDone (vl vb0 vb1 : int).

Definition afd_occ (v : int) (f : afd) : bool :=
  entry_var v || match f with FDFile off vl vb0 vb1 => existsb (fun p => (fst p =? v)%uint63) (snd off) || (v =? vl)%uint63 || (v =? vb0)%uint63 || (v =? vb1)%uint63
                 | FDDone vl vb0 vb1 => (v =? vl)%uint63 || (v =? vb0)%uint63 || (v =? vb1)%uint63 | _ => false end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive piece : Type :=
| PB (b : xb)        (* [comment removed for export] *)
| PS (k : Z).        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dec_str (k : Z) (ρ : valuation) : list byte :=
  if (0 <=? k) && (k <? 1048576) then
    map (fun j => Z_to_bv 8 (ρ (strvar k (Z.of_nat j)))) (seq 0 (Z.to_nat (ρ (lenvar k) mod 131072)))
  else [].

(* [comment removed for export] *)
Lemma strvar_entry (k j : Z) : 0 <= k < 1048576 -> 0 <= j < 131072 -> entry_var (strvar k j) = true.
Proof.
  intros Hk Hj. unfold entry_var, strvar. apply orb_true_iff. right. apply Uint63.leb_spec.
  rewrite of_Z_spec. change wB with (2 ^ 63). rewrite Z.mod_small by lia. change (to_Z 1099511627776) with (2 ^ 40). lia.
Qed.

Lemma lenvar_entry (k : Z) : 0 <= k < 1048576 -> entry_var (lenvar k) = true.
Proof.
  intros Hk. unfold entry_var, lenvar. apply orb_true_iff. right. apply Uint63.leb_spec.
  rewrite of_Z_spec. change wB with (2 ^ 63). rewrite Z.mod_small by lia. change (to_Z 1099511627776) with (2 ^ 40). lia.
Qed.

Lemma dec_str_agree_entry (ρ ρ' : valuation) (k : Z) :
  (forall x, entry_var x = true -> ρ' x = ρ x) -> dec_str k ρ' = dec_str k ρ.
Proof.
  intros H. unfold dec_str. destruct ((0 <=? k) && (k <? 1048576)) eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (H (lenvar k) (lenvar_entry k ltac:(lia))).
  apply map_ext_in. intros j Hj. apply in_seq in Hj.
  pose proof (Z.mod_pos_bound (ρ (lenvar k)) 131072 ltac:(lia)) as Hb.
  rewrite (H (strvar k (Z.of_nat j))); [reflexivity|]. apply strvar_entry; lia.
Qed.

Fixpoint pieces_val (ρ : valuation) (l : list piece) (o : list byte) : Prop :=
  match l with
  | [] => o = []
  | PB b :: r => exists (y : byte) (o' : list byte), o = y :: o' /\ xb_z ρ b (bv_unsigned y) /\ pieces_val ρ r o'
  | PS k :: r => exists o' : list byte, o = dec_str k ρ ++ o' /\ pieces_val ρ r o'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record amodel : Type := AM {
  am_maps : list aent;             (* [comment removed for export] *)
  am_brk0 : lin;                   (* [comment removed for export] *)
  am_brk : lin;                    (* [comment removed for export] *)
  am_tid : option xv;              (* [comment removed for export] *)
  am_shadow : bool;                (* [comment removed for export] *)
  am_next : int;                   (* [comment removed for export] *)
  am_atop : lin;                   (* [comment removed for export] *)
  am_out : list piece;             (* [comment removed for export] *)
  am_exp : list (aent * lin * Z);  (* [comment removed for export] *)
  am_fd : afd                      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sh_lo : Z := 2147446784.          (* [comment removed for export] *)
Definition sh_hi : Z := 17594333495296.      (* [comment removed for export] *)
Definition ls_ent : aent := AE (2147446784, []) 268435456 false.
Definition gap_ent : aent := AE (2415882240, []) 2199023255552 true.
Definition hs_ent : aent := AE (2201439137792, []) 15392894357504 false.

(* [comment removed for export] *)
Definition var_ent (e : aent) : bool := match snd (ae_base e) with [] => false | _ => true end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_grant (am : amodel) (e : aent) (nx : int) : amodel :=
  AM (e :: am_maps am) (am_brk0 am) (am_brk am) (am_tid am) (am_shadow am) nx (am_atop am) (am_out am) (am_exp am) (am_fd am).

(* [comment removed for export] *)
Definition am_shadow_on (am : amodel) : amodel :=
  AM (am_maps am) (am_brk0 am) (am_brk am) (am_tid am) true (am_next am) (am_atop am) (am_out am) (am_exp am) (am_fd am).

(* [comment removed for export] *)
Definition am_brk_grow (am : amodel) (e : aent) (b : lin) (nx : int) : amodel :=
  AM (e :: am_maps am) (am_brk0 am) b (am_tid am) (am_shadow am) nx (am_atop am) (am_out am) (am_exp am) (am_fd am).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gform (g : int) : lin := lvar g 4096.

Definition hole_ents (g : int) (nZ : Z) (ents : list aent) (s : store) : store :=
  fold_left (fun t e => shole t (lsub (gform g) (ae_base e)) (- nZ) (ae_size e)) ents s.

Definition hole_res (g : int) (nZ : Z) (res : list (Z * Z)) (s : store) : store :=
  fold_left (fun t q => shole t (gform g) (fst q - nZ) (fst q + snd q)) res s.

Definition hole_span (g : int) (nZ : Z) (on : bool) (s : store) : store :=
  if on then shole s (gform g) (sh_lo - nZ) sh_hi else s.

(* [comment removed for export] *)
Definition grant_rng (g : int) (nZ : Z) (atop : lin) (ghi : Z) (s : store) : store :=
  sadd (sadd s (lvar g 1) 1 ghi) (lsub (gform g) atop) (- 18446744073709551616) (- nZ).

(* [comment removed for export] *)
Fixpoint res_top (top : Z) (res : list (Z * Z)) : option Z :=
  match res with
  | [] => Some top
  | q :: r => if (fst q =? top) &&& (0 <? snd q) then res_top (fst q + snd q) r else None
  end.

Definition res_span (res : list (Z * Z)) : option (Z * Z) :=
  match res with
  | [] => None
  | q :: r => if 0 <? snd q then match res_top (fst q + snd q) r with Some t => Some (fst q, t) | None => None end else None
  end.

Definition hole_img (g : int) (nZ : Z) (res : list (Z * Z)) (s : store) : store :=
  match res_span res with Some (lo, hi) => shole s (gform g) (lo - nZ) hi | None => hole_res g nZ res s end.

(* [comment removed for export] *)
Definition grant_facts (g : int) (nZ : Z) (atop : lin) (ghi : Z) (on : bool) (ents : list aent) (res : list (Z * Z)) (s : store) : store :=
  hole_img g nZ res (hole_span g nZ on (hole_ents g nZ (List.filter var_ent ents) (grant_rng g nZ atop ghi s))).

(* [comment removed for export] *)
Definition res_lits (res : list (word * word)) : list (Z * Z) := map (fun q => (bas q, bsz q)) res.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AST : Type := astate amodel.

(* [comment removed for export] *)
Definition out_val (ρ : valuation) (A : AST) (o : list byte) : Prop := pieces_val ρ (am_out (a_model A)) o.

(* [comment removed for export] *)
Definition with_model (A : AST) (pc : w64) (regs : aregs) (mem : list region) (s : store) (am : amodel) (budget : Z) : AST :=
  AS pc regs (a_resv A) mem s am budget (a_steps A + 1).

(* [comment removed for export] *)
Definition xlit (v : xv) : option Z := match v with XL x => Some (wZ x) | _ => None end.

Lemma reg_lit (ρ : valuation) (regs : aregs) (ms : machine_state) (r : reg) (k : int) (z : Z) :
  RRegs ρ regs ms -> ri r = k -> xlit (aget regs k) = Some z -> bv_unsigned (rg ms r) = z.
Proof.
  intros H Hk E. specialize (H r). rewrite Hk in H. unfold xlit in E. destruct (aget regs k) as [x| | | | |]; try discriminate E.
  injection E as <-. exact H.
Qed.

Lemma reg_form (ρ : valuation) (regs : aregs) (ms : machine_state) (r : reg) (ts : terms) (o : w64) :
  RRegs ρ regs ms -> aget regs (ri r) = XS ts o -> bv_unsigned (rg ms r) = smod ρ ts o.
Proof. intros H E. specialize (H r). rewrite E in H. exact H. Qed.

Lemma rg_of_lit (w : word) (z : Z) : bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros H. apply bv_eq. rewrite Z_to_bv_unsigned, <- H. symmetry. apply bv_wrap_bv_unsigned. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition eb_above (s : store) (atop : lin) (A : list region) : bool :=
  match lrange s atop with
  | Some (tlo, thi) =>
      (0 <=? tlo) &&& (thi <=? 140737488355328) &&&
      lforall (fun R => if is_entry R then
                          match lrange s (lsub (wS (rg_bo R), rg_ts R) atop) with
                          | Some (lo, hi) => (0 <=? lo) &&& (hi <=? 4611686018427387904)
                          | None => false
                          end
                        else true) A
  | None => false
  end.

Lemma eb_above_sound (ρ : valuation) (s : store) (atop : lin) (A : list region) :
  sat ρ s -> eb_above s atop A = true ->
  0 <= leval ρ atop <= 140737488355328 /\ forall R, In R A -> is_entry R = true -> leval ρ atop <= rbase ρ R.
Proof.
  intros Hs H. unfold eb_above in H. destruct (lrange s atop) as [[tlo thi]|] eqn:Et; [|discriminate H].
  pose proof (lrange_sound ρ s atop Hs _ Et) as Ht. cbn [fst snd] in Ht.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [lia|]. intros R HIn He. pose proof (lforall_forall _ _ H3 R HIn) as H4. clear H3. rename H4 into H3. cbv beta in H3. rewrite He in H3.
  destruct (lrange s (lsub (wS (rg_bo R), rg_ts R) atop)) as [[lo hi]|] eqn:El; [|discriminate H3].
  pose proof (lrange_sound ρ s _ Hs _ El) as Hl. cbn [fst snd] in Hl. rewrite leval_lsub in Hl.
  apply andb_prop in H3 as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
  assert (E : leval ρ (wS (rg_bo R), rg_ts R) = wS (rg_bo R) + teval ρ (rg_ts R)) by reflexivity. rewrite E in Hl.
  unfold rbase, smod. rewrite <- (wS_mod (rg_bo R)), Zplus_mod_idemp_r. rewrite Z.mod_small; [lia|]. unfold two64. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint depth_aux (fuel d : nat) (n : Z) : nat :=
  match fuel with
  | O => d
  | S f => if n <=? 8 * 2 ^ Z.of_nat d then d else depth_aux f (S d) n
  end.

Definition depth_for (n : Z) : nat := depth_aux 44 0 n.

Lemma depth_aux_spec (n : Z) : forall fuel d, (d + fuel = 44)%nat -> n <= 8 * 2 ^ 44 ->
  (depth_aux fuel d n <= 44)%nat /\ n <= 8 * 2 ^ Z.of_nat (depth_aux fuel d n).
Proof.
  induction fuel as [|f IH]; intros d Hd Hn; cbn [depth_aux].
  - replace d with 44%nat by lia. split; [lia | exact Hn].
  - destruct (n <=? 8 * 2 ^ Z.of_nat d) eqn:E; [apply Z.leb_le in E; split; [lia | exact E]|]. apply IH; [lia | exact Hn].
Qed.

Lemma depth_for_spec (n : Z) : n < 2 ^ 47 -> (depth_for n <= 44)%nat /\ n <= 8 * 2 ^ Z.of_nat (depth_for n).
Proof. intros H. apply depth_aux_spec; [reflexivity | lia]. Qed.

(* [comment removed for export] *)
Definition zero_rg (ts : terms) (o : w64) (n : Z) : region := Rg ts o (of_Z n) KZero (depth_for n) IEmpty.

(* [comment removed for export] *)
Definition tdiv8 (ts : terms) : terms := map (fun p => (fst p, snd p / 8)) ts.
Definition comp_rg (ts : terms) (o : w64) (n : Z) : region :=
  Rg (tdiv8 ts) (wofZ (wS o / 8 + sh_off)) (of_Z (n / 8)) KShadow (depth_for (n / 8)) IEmpty.

Lemma wS_small (o : w64) : wZ o < 9223372036854775808 -> wS o = wZ o.
Proof.
  unfold wS, wZ. destruct (wh o); [|reflexivity]. pose proof (to_Z_bounded (wl o)). unfold two63. lia.
Qed.

Lemma wS_wofZ_small (c : Z) : 0 <= c < 9223372036854775808 -> wS (wofZ c) = c.
Proof. intros H. rewrite wS_small; rewrite wZ_wofZ, Z.mod_small by (unfold two64; lia); [reflexivity | lia]. Qed.

Definition tdiv8_ok (ts : terms) : bool := lforall (fun p => snd p mod 8 =? 0) ts.

Lemma teval_tdiv8 (ρ : valuation) (ts : terms) : tdiv8_ok ts = true -> teval ρ ts = 8 * teval ρ (tdiv8 ts).
Proof.
  unfold tdiv8_ok. intros H0. pose proof (lforall_forall _ _ H0) as H. clear H0. cbv beta in H.
  induction ts as [|[x k] r IH]; [reflexivity|]. cbn [tdiv8 map teval fst snd].
  fold (tdiv8 r). rewrite (IH (fun p Hp => H p (or_intror Hp))). pose proof (H (x, k) (or_introl eq_refl)) as Hk. cbn [snd] in Hk.
  apply Z.eqb_eq in Hk. pose proof (Z.div_mod k 8 ltac:(lia)) as D. rewrite Hk in D. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition part_wit (s : store) (lo hi : Z) (R : region) : bool :=
  is_shadow R &&& (0 <? to_Z (rg_n R)) &&&
  match lrange s (wS (rg_bo R), rg_ts R) with
  | Some (l, h) => (lo <=? l) &&& (h + to_Z (rg_n R) <=? hi)
  | None => false
  end.

Definition has_wit (s : store) (lo hi : Z) (A : list region) : bool := lexists (part_wit s lo hi) A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PIDMAX : Z := 4194304.

(* [comment removed for export] *)
Definition sys_set_tid (A : AST) : option (list AST) :=
  let am := a_model A in
  match am_tid am with
  | Some _ => None
  | None =>
      let t := am_next am in
      let v := XS [(t, 1)] w_zero in
      Some [with_model A (npc A) (aset (a_regs A) reg_a0 v) (a_mem A) (sadd (a_facts A) (lvar t 1) 1 (PIDMAX - 1))
              (AM (am_maps am) (am_brk0 am) (am_brk am) (Some v) (am_shadow am) (t + 1)%uint63 (am_atop am) (am_out am) (am_exp am) (am_fd am))
              (a_budget A)]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition null_shape (A : AST) : option (Z * bool * bool) :=
  let r := a_regs A in
  match xlit (aget r 11%uint63), xlit (aget r 12%uint63), xlit (aget r 13%uint63), xlit (aget r 15%uint63) with
  | Some len, Some prot, Some flags, Some off =>
      if (0 <? len) &&& (len <? 70368744177664) &&& (off =? 0) &&& ((flags =? 34) ||| (flags =? 16418)) &&& ((prot =? 3) ||| (prot =? 0))
      then Some (page_round_up_Z len, prot =? 0, flags =? 16418) else None
  | _, _, _, _ => None
  end.

(* [comment removed for export] *)
Definition ents_total (l : list aent) : Z := fold_right (fun e z => ae_size e + z) 0 l.

Definition pack_ok (am : amodel) (nZ tlo : Z) : bool :=
  4096 + (live_bytes (segments_reserved segs) + ents_total (am_maps am))
  + Z.of_nat (length (segments_reserved segs) + length (am_maps am)) * (nZ + 4096) + nZ <=? tlo.

Definition sys_mmap_null (LIM : Z) (A : AST) : option (list AST) :=
  let am := a_model A in
  let s := a_facts A in
  match null_shape A, lrange s (am_atop am) with
  | Some (nZ, na, lz), Some (tlo, thi) =>
      if am_shadow am &&& eb_above s (am_atop am) (a_mem A) &&& pack_ok am nZ tlo
         &&& (na ||| lz ||| (a_budget A + nZ <=? LIM))
         &&& lforall (fun R => (0 <? to_Z (rg_n R))) (a_mem A)
         &&& (na ||| (has_wit s ls_beg ls_end (a_mem A) &&& has_wit s hs_beg hs_hi (a_mem A)))
         &&& (negb lz ||| (65536 <=? nZ))      (* [comment removed for export] *)
      then
        let g := am_next am in
        let ts := [(g, 4096)] in
        let e := AE (gform g) nZ na in
        let s' := grant_facts g nZ (am_atop am) ((thi - nZ) / 4096) true (am_maps am) (res_lits (segments_reserved segs)) s in
        let mem' := if na then a_mem A else zero_rg ts w_zero nZ :: comp_rg ts w_zero nZ :: a_mem A in
        let b' := if na ||| lz then a_budget A else a_budget A + nZ in
        Some [with_model A (npc A) (aset (a_regs A) reg_a0 (XS ts w_zero)) mem' s' (am_grant am e (g + 1)%uint63) b']
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition norep_flags : Z := 1064994.

(* [comment removed for export] *)
Definition ent_misses (s : store) (lo hi : Z) (e : aent) : bool :=
  match lrange s (ae_base e) with
  | Some (l, h) => (h + ae_size e <=? lo) ||| (hi <=? l)
  | None => false
  end.

Definition res_misses (lo hi : Z) : bool :=
  lforall (fun q => (bas q + bsz q <=? lo) ||| (hi <=? bas q)) (segments_reserved segs).

(* [comment removed for export] *)
Definition comp_sel (s : store) (lo hi : Z) (R : region) : bool :=
  negb (is_entry R) &&& negb (is_shadow R) &&& tdiv8_ok (rg_ts R) &&& (wS (rg_bo R) mod 8 =? 0)
  &&& (to_Z (rg_n R) mod 8 =? 0) &&& (0 <? to_Z (rg_n R)) &&&
  match lrange s (wS (rg_bo R), rg_ts R) with
  | Some (l, h) => (lo <=? l) &&& (h + to_Z (rg_n R) <=? hi)
  | None => false
  end.

Definition norep_comps (s : store) (lo hi : Z) (A : list region) : list region :=
  flat_map (fun R => if comp_sel s lo hi R then [comp_rg (rg_ts R) (rg_bo R) (to_Z (rg_n R))] else []) A.

Definition has_ent (e : aent) (l : list aent) : bool := lexists (aent_eqb e) l.

Definition sys_mmap_noreplace (A : AST) : option (list AST) :=
  let r := a_regs A in
  let am := a_model A in
  let s := a_facts A in
  match xlit (aget r 10%uint63), xlit (aget r 11%uint63), xlit (aget r 12%uint63), xlit (aget r 13%uint63), xlit (aget r 15%uint63),
        lrange s (am_atop am) with
  | Some addr, Some len, Some prot, Some flags, Some off, Some (tlo, _) =>
      let e := AE (addr, []) len (prot =? 0) in
      let is_ls := aent_eqb e ls_ent in
      let is_hs := aent_eqb e hs_ent in
      if (off =? 0) &&& (flags =? norep_flags) &&& ((prot =? 3) ||| (prot =? 0)) &&& (is_ls ||| aent_eqb e gap_ent ||| is_hs)
         &&& negb (am_shadow am) &&& (sh_hi <=? tlo) &&& eb_above s (am_atop am) (a_mem A)
         &&& lforall (ent_misses s addr (addr + len)) (am_maps am) &&& res_misses addr (addr + len)
         &&& lforall (fun R => (0 <? to_Z (rg_n R))) (a_mem A)
         &&& (negb is_hs ||| (has_ent ls_ent (am_maps am) &&& has_ent gap_ent (am_maps am) &&& lforall (fun e0 => negb (var_ent e0)) (am_maps am)))
      then
        let comps := if is_ls then norep_comps s 0 sh_lo (a_mem A)
                     else if is_hs then norep_comps s sh_hi 140737488355328 (a_mem A) else [] in
        let am1 := am_grant am e (am_next am) in
        let am' := if is_hs then am_shadow_on am1 else am1 in
        Some [with_model A (npc A) (aset r reg_a0 (XL (wofZ addr))) (comps ++ a_mem A) s am' (a_budget A)]
      else None
  | _, _, _, _, _, _ => None
  end.

End WithSegs.
