(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope uint63_scope.

(* [comment removed for export] *)
Record pdesc : Type := PD { pd_pn : int; pd_wr : bool; pd_kind : pkind; pd_cells : list (int * cell) }.
Record rdesc : Type := RD { rd_tag : int; rd_lo : int; rd_len : int; rd_align : int;
                            rd_dflt : option pkind; rd_pages : list pdesc }.
Record sdesc : Type := SD { sd_pc : int; sd_regs : list (int * fval); sd_mem : list rdesc }.

Definition page_of (p : pdesc) : page := PG (pd_wr p) (pd_kind p) (iof_list (pd_cells p)).
Definition region_of (r : rdesc) : region :=
  RG (rd_lo r) (rd_len r) (rd_align r) (rd_dflt r)
     (iof_list (map (fun p => (pd_pn p, page_of p)) (rd_pages r))) clo_dflt chi_dflt.   (* [comment removed for export] *)
Definition state_of (d : sdesc) : fstate :=
  FS (sd_pc d) (iof_list (sd_regs d))
     (iof_list (map (fun r => (rd_tag r, region_of r)) (sd_mem d))) None.

(* [comment removed for export] *)
Inductive hfact : Type :=
| HCell (t off n : int) (w : w64)        (* [comment removed for export] *)
| HVal (t off : int) (v : fval)          (* [comment removed for export] *)
| HBytes (t off n : int) (v : fval)      (* [comment removed for export] *)
| HZero (t off len : int)                (* [comment removed for export] *)
| HClear (lo hi : int)                   (* [comment removed for export] *)
| HWr (t off len : int)                  (* [comment removed for export] *)
| HReg (r : int) (v : fval)              (* [comment removed for export] *)
| HRegion (t lo len al : int)            (* [comment removed for export] *)
| HDisj (t1 lo1 len1 t2 lo2 len2 : int). (* [comment removed for export] *)

Section Holds.
Variable segs : list Segment.
Variable rho : int -> word.
Variable ms : machine_state.

Definition hholds (f : hfact) : Prop :=
  match f with
  | HCell t off n w =>
      forall j, (j < Z.to_nat (to_Z n))%nat ->
        rview segs (ms_mem ms) (adr rho t (to_Z off + Z.of_nat j)) = nth_error (w_bytes w) j
  | HVal t off v =>
      forall j, (j < 8)%nat ->
        rview segs (ms_mem ms) (adr rho t (to_Z off + Z.of_nat j)) = nth_error (wbytes8 (dv rho v)) j
  | HBytes t off n v =>
      forall j, (j < Z.to_nat (to_Z n))%nat ->
        rview segs (ms_mem ms) (adr rho t (to_Z off + Z.of_nat j)) = nth_error (wbytes8 (dv rho v)) j
  | HZero t off len =>
      forall j, (0 <= j < to_Z len)%Z ->
        rview segs (ms_mem ms) (adr rho t (to_Z off + j)) = Some (Z_to_bv 8 0)
  | HClear lo hi =>
      forall a, (to_Z lo <= a < to_Z hi)%Z -> ms_mem ms (Z_to_bv 64 a) = None
  | HWr t off len =>
      forall j, (0 <= j < to_Z len)%Z ->
        wview segs (ms_mem ms) (adr rho t (to_Z off + j)) <> None
  | HReg r v =>
      forall rr : reg, ireg rr = r -> Sem.rget (core_of ms) rr = dv rho v
  | HRegion t lo len al => region_ok rho t (RG lo len al None iempty clo_dflt chi_dflt)
  | HDisj t1 lo1 len1 t2 lo2 len2 =>
      (bv_unsigned (rho t1) + to_Z len1 <= bv_unsigned (rho t2) + to_Z lo2
       \/ bv_unsigned (rho t2) + to_Z len2 <= bv_unsigned (rho t1) + to_Z lo1)%Z
  end.
End Holds.

(* [comment removed for export] *)
Definition b62 : int := 4611686018427387904.    (* [comment removed for export] *)
Definition b50 : int := 1125899906842624.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_iv (o l a n : int) : bool :=
  (o <? b62) && (l <=? b62) && (a <? b62) && (n <=? b62) && (o <=? a) && (a + n <=? o + l).

Definition fval_eqb (a b : fval) : bool :=
  (vtag a =? vtag b) && (wtop (vw a) =? wtop (vw b)) && (wlo (vw a) =? wlo (vw b)).

Definition iseq (n : nat) : list int := map (fun k => of_Z (Z.of_nat k)) (seq 0 n).

Section Check.
Variable IM : fimage.
Variable facts : list hfact.

Definition image_byte (a : int) : option int :=
  match find_seg IM a with
  | Some sg => hex_byte (sg_hex sg) (a - sg_base sg)
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint byte_known_in (fs : list hfact) (t a : int) : option int :=
  match fs with
  | [] => None
  | f :: r =>
      match f with
      | HCell t' o n w =>
          if (t' =? t) && (n <=? 8) && in_iv o n a 1 then Some (w_byte (a - o) w) else byte_known_in r t a
      | HVal t' o v =>
          if (t' =? t) && (vtag v =? 0) && in_iv o 8 a 1 then Some (w_byte (a - o) (vw v)) else byte_known_in r t a
      | HZero t' o l =>
          if (t' =? t) && in_iv o l a 1 then Some 0 else byte_known_in r t a
      | HClear lo hi =>
          if (t =? 0) && (lo <=? a) && (a <? hi) && (hi <=? b62) then
            match image_byte a with Some b => Some b | None => byte_known_in r t a end
          else byte_known_in r t a
      | _ => byte_known_in r t a
      end
  end.
Definition byte_known := byte_known_in facts.

Definition zero_cov (t a n : int) : bool :=
  existsb (fun f => match f with HZero t' o l => (t' =? t) && in_iv o l a n | _ => false end) facts.
Definition wr_cov (t a n : int) : bool :=
  existsb (fun f => match f with HWr t' o l => (t' =? t) && in_iv o l a n | _ => false end) facts.
Definition clear_cov (a n : int) : bool :=
  existsb (fun f => match f with
                    | HClear lo hi => (lo <=? a) && (a <? b62) && (n <=? b62) && (a + n <=? hi) && (hi <=? b62)
                    | _ => false end) facts.

(* [comment removed for export] *)
Definition cell_ok (t off : int) (v : fval) : bool :=
  if vtag v =? 0 then
    forallb (fun j => match byte_known t (off + j) with
                      | Some b => b =? w_byte j (vw v)
                      | None => false end) (iseq 8)
  else
    existsb (fun f => match f with
                      | HVal t' o v' => (t' =? t) && (o =? off) && fval_eqb v' v
                      | _ => false end) facts.

(* [comment removed for export] *)
Definition sv_cov (t a : int) (v : fval) (j : int) : bool :=
  existsb (fun f => match f with
                    | HBytes t' o n v' =>
                        (t' =? t) && fval_eqb v' v && (j <? n) && (j <? 8) && (o <? b62) && (o + j =? a)
                    | HVal t' o v' =>
                        (t' =? t) && fval_eqb v' v && (j <? 8) && (o <? b62) && (o + j =? a)
                    | _ => false end) facts.

Definition slot_ok_b (t a : int) (s : slot) : bool :=
  match s with
  | SK b => match byte_known t a with Some b' => b' =? b | None => false end
  | SV v j => sv_cov t a v j
  | SU => true
  end.

Definition seg_wr_page (pn : int) : bool :=
  match find_seg IM (pn << 12) with Some sg => sg_wr sg | None => false end.

(* [comment removed for export] *)
Definition page_ok_b (r : rdesc) (p : pdesc) : bool :=
  let t := rd_tag r in
  let pn := pd_pn p in
  let pg := page_of p in
  (pn <? b50) && (rd_lo r <=? (pn << 12)) && ((pn << 12) + 4096 <=? rd_len r) && (rd_len r <=? b62)
  && (if pd_wr p then (if t =? 0 then seg_wr_page pn else wr_cov t (pn << 12) 4096) else true)
  && (match pd_kind p with PKImage => t =? 0 | _ => true end)
  && forallb (fun ci =>
        let off := (pn << 12) + (ci << 3) in
        match iget ci (pg_cells pg) with
        | Some (CV v) => cell_ok t off v
        | Some CU => true
        | Some (CB sl) => forallb (fun j => slot_ok_b t (off + j) (sget j sl)) (iseq 8)
        | None => match pd_kind p with
                  | PKZero => zero_cov t off 8
                  | PKUnk => true
                  | PKImage => clear_cov off 8
                  end
        end) (iseq 512).

(* [comment removed for export] *)
Fixpoint pages_from (n : nat) (pn : int) (f : int -> bool) : bool :=
  match n with
  | O => true
  | S n' => f pn && pages_from n' (pn + 1) f
  end.

Definition explicit_b (r : rdesc) (pn : int) : bool :=
  existsb (fun p => pd_pn p =? pn) (rd_pages r).

Definition image_pages_ok (r : rdesc) : bool :=
  forallb (fun sg =>
     (sg_base sg <? b62) && (sg_size sg <=? b62) &&
     pages_from (Z.to_nat (to_Z (sg_size sg >> 12))) (sg_base sg >> 12)
       (fun pn => explicit_b r pn
                  || ((rd_lo r <=? (pn << 12)) && ((pn << 12) + 4096 <=? rd_len r)
                      && clear_cov (pn << 12) 4096))) IM.

Definition region_fact_b (r : rdesc) : bool :=
  if rd_tag r =? 0 then rd_len r <=? b62
  else existsb (fun f => match f with
                         | HRegion t lo len al =>
                             (t =? rd_tag r) && (lo =? rd_lo r) && (len =? rd_len r) && (al =? rd_align r)
                         | _ => false end) facts.

Definition disj_fact_b (r r' : rdesc) : bool :=
  existsb (fun f => match f with
                    | HDisj t1 lo1 len1 t2 lo2 len2 =>
                        ((t1 =? rd_tag r) && (lo1 =? rd_lo r) && (len1 =? rd_len r)
                         && (t2 =? rd_tag r') && (lo2 =? rd_lo r') && (len2 =? rd_len r'))
                        || ((t1 =? rd_tag r') && (lo1 =? rd_lo r') && (len1 =? rd_len r')
                            && (t2 =? rd_tag r) && (lo2 =? rd_lo r) && (len2 =? rd_len r))
                    | _ => false end) facts.

Definition region_ok_b (d : sdesc) (r : rdesc) : bool :=
  region_fact_b r
  && forallb (fun r' => (rd_tag r' =? rd_tag r) || disj_fact_b r r') (sd_mem d)
  && forallb (page_ok_b r) (rd_pages r)
  && (if rd_tag r =? 0 then
        image_pages_ok r && (match rd_dflt r with None => true | Some _ => false end)
      else
        match rd_dflt r with
        | None => true
        | Some PKUnk => (rd_lo r <=? rd_len r) && wr_cov (rd_tag r) (rd_lo r) (rd_len r - rd_lo r)
        | Some PKZero => (rd_lo r <=? rd_len r) && wr_cov (rd_tag r) (rd_lo r) (rd_len r - rd_lo r)
                         && zero_cov (rd_tag r) (rd_lo r) (rd_len r - rd_lo r) && ((rd_len r land 7) =? 0)
        | Some PKImage => false
        end).

Definition regs_ok_b (d : sdesc) : bool :=
  forallb (fun r =>
     (r =? 0) ||
     let v := rget (state_of d) r in
     existsb (fun f => match f with HReg r' v' => (r' =? r) && fval_eqb v' v | _ => false end) facts)
    (iseq 32).

(* [comment removed for export] *)
Definition ho_check (d : sdesc) : bool :=
  regs_ok_b d && forallb (region_ok_b d) (sd_mem d).
End Check.

(* [comment removed for export] *)
Definition fact_tags_lt (n : int) (f : hfact) : bool :=
  match f with
  | HCell t _ _ _ | HZero t _ _ | HWr t _ _ | HRegion t _ _ _ => t <? n
  | HVal t _ v | HBytes t _ _ v => (t <? n) && (vtag v <? n)
  | HClear _ _ => true
  | HReg _ v => vtag v <? n
  | HDisj t1 _ _ t2 _ _ => (t1 <? n) && (t2 <? n)
  end.

Section Sound.
Variable segs : list Segment.
Variable IM : fimage.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.

(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma ho_b62 : to_Z b62 = 2 ^ 62. Proof. reflexivity. Qed.
Lemma ho_b50 : to_Z b50 = 2 ^ 50. Proof. reflexivity. Qed.

Lemma ho_eqb_eq : forall a b : int, (a =? b)%uint63 = true -> a = b.
Proof. intros a b H. apply Uint63.eqb_spec. exact H. Qed.

Lemma in_iv_spec : forall o l a n, in_iv o l a n = true ->
  to_Z o < 2 ^ 62 /\ to_Z l <= 2 ^ 62 /\ to_Z a < 2 ^ 62 /\ to_Z n <= 2 ^ 62
  /\ to_Z o <= to_Z a /\ to_Z a + to_Z n <= to_Z o + to_Z l.
Proof.
  intros o l a n H. unfold in_iv in H. rewrite !andb_true_iff in H.
  destruct H as [[[[[H1 H2] H3] H4] H5] H6].
  apply i_ltb_lt in H1, H3. apply i_leb_le in H2, H4, H5, H6. rewrite ho_b62 in *.
  pose proof (i63_range o). pose proof (i63_range l). pose proof (i63_range a). pose proof (i63_range n).
  rewrite !toZ_add_small in H6 by lia. repeat split; assumption.
Qed.

Lemma in_iseq : forall n (ci : int), 0 <= to_Z ci < Z.of_nat n -> In ci (iseq n).
Proof.
  intros n ci H. unfold iseq. apply in_map_iff. exists (Z.to_nat (to_Z ci)). split.
  - rewrite Z2Nat.id by lia. apply of_to_Z.
  - apply in_seq. lia.
Qed.

Lemma fval_eqb_eq : forall a b, fval_eqb a b = true -> a = b.
Proof.
  intros [ta [tpa la]] [tb [tpb lb]] H. unfold fval_eqb in H. cbn [vtag vw wtop wlo] in H.
  rewrite !andb_true_iff in H. destruct H as [[H1 H2] H3].
  apply ho_eqb_eq in H1, H2, H3. subst. reflexivity.
Qed.

Lemma iget_iof_list_map_In {X A} (key : X -> int) (val : X -> A) : forall (l : list X) k v,
  iget k (iof_list (map (fun x => (key x, val x)) l)) = Some v ->
  exists x, In x l /\ key x = k /\ v = val x.
Proof.
  intros l k v H. rewrite iget_iof_list in H.
  destruct (List.find (fun kv => (k =? fst kv)%uint63) (rev (map (fun x => (key x, val x)) l)))
    as [kv |] eqn:E; [| discriminate H].
  inversion H; subst v. apply List.find_some in E as [Hin Hk].
  apply in_rev in Hin. apply in_map_iff in Hin as (x & <- & Hx). cbn [fst snd] in *.
  exists x. split; [exact Hx |]. split; [symmetry; apply ho_eqb_eq; exact Hk | reflexivity].
Qed.

Lemma iget_iof_list_map_None {X A} (key : X -> int) (val : X -> A) : forall (l : list X) k,
  iget k (iof_list (map (fun x => (key x, val x)) l)) = None ->
  forall x, In x l -> key x <> k.
Proof.
  intros l k H x Hx Hk. rewrite iget_iof_list in H.
  destruct (List.find (fun kv => (k =? fst kv)%uint63) (rev (map (fun x => (key x, val x)) l)))
    as [kv |] eqn:E; [discriminate H |].
  pose proof (List.find_none _ _ E (key x, val x)) as Hn. cbn [fst] in Hn.
  rewrite <- Hk, Uint63.eqb_refl in Hn. discriminate Hn.
  apply -> in_rev. apply in_map_iff. exists x. split; [reflexivity | exact Hx].
Qed.

Lemma ho_toZ_lsl12 : forall pn : int, to_Z pn < 2 ^ 50 -> to_Z (pn << 12)%uint63 = to_Z pn * 4096.
Proof.
  intros pn H. pose proof (i63_range pn).
  rewrite (toZ_lsl_small pn 12 12%uint63); [reflexivity | reflexivity | lia | change (2 ^ 12) with 4096; lia].
Qed.

Lemma ho_toZ_lsl3 : forall ci : int, to_Z ci < 512 -> to_Z (ci << 3)%uint63 = to_Z ci * 8.
Proof.
  intros ci H. pose proof (i63_range ci).
  rewrite (toZ_lsl_small ci 3 3%uint63); [reflexivity | reflexivity | lia | change (2 ^ 3) with 8; lia].
Qed.

Section Facts.
Variable facts : list hfact.
Variable rho : int -> word.
Variable ms : machine_state.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis Hfacts : Forall (hholds segs rho ms) facts.

Lemma ho_adr0 : forall z, adr rho 0%uint63 z = Z_to_bv 64 z.
Proof. intros z. unfold adr. rewrite Hrho0. apply bv_add_0_Z_to_bv. Qed.

Lemma ho_dv_tag0 : forall v, (vtag v =? 0)%uint63 = true -> dv rho v = wbv (vw v).
Proof. intros v H. apply (dv_tag0' rho Hrho0). exact H. Qed.

(* [comment removed for export] *)
Lemma byte_known_in_sound : forall fs t a b,
  Forall (hholds segs rho ms) fs ->
  byte_known_in IM fs t a = Some b ->
  rview segs (ms_mem ms) (adr rho t (to_Z a)) = Some (Z_to_bv 8 (to_Z b)).
Proof.
  induction fs as [| f fs IH]; intros t a b HF H; [discriminate H |].
  inversion HF as [| ? ? Hf HFs]; subst. cbn [byte_known_in] in H.
  destruct f as [t' o n w | t' o v | | t' o l | lo hi | | | |]; try (apply IH; assumption).
  - (* [comment removed for export] *)
    destruct ((t' =? t)%uint63 && (n <=? 8)%uint63 && in_iv o n a 1) eqn:E; [| apply IH; assumption].
    rewrite !andb_true_iff in E. destruct E as [[Et En] Eiv].
    apply ho_eqb_eq in Et. subst t'. apply i_leb_le in En. change (to_Z 8) with 8 in En.
    apply in_iv_spec in Eiv as (_ & _ & _ & _ & H5 & H6). change (to_Z 1) with 1 in H6.
    inversion H; subst b. clear H.
    pose proof (i63_range o). pose proof (i63_range a). pose proof (i63_range n).
    assert (Eao : to_Z (a - o)%uint63 = to_Z a - to_Z o) by (apply toZ_sub_small; lia).
    cbn [hholds] in Hf.
    specialize (Hf (Z.to_nat (to_Z (a - o)%uint63)) ltac:(rewrite Eao; lia)).
    rewrite Z2Nat.id in Hf by (rewrite Eao; lia). rewrite Eao in Hf.
    replace (to_Z o + (to_Z a - to_Z o)) with (to_Z a) in Hf by lia.
    rewrite Hf. rewrite <- Eao. apply w_bytes_nth_byte. rewrite Eao. lia.
  - (* [comment removed for export] *)
    destruct ((t' =? t)%uint63 && (vtag v =? 0)%uint63 && in_iv o 8 a 1) eqn:E; [| apply IH; assumption].
    rewrite !andb_true_iff in E. destruct E as [[Et Ev] Eiv].
    apply ho_eqb_eq in Et. subst t'.
    apply in_iv_spec in Eiv as (_ & _ & _ & _ & H5 & H6). change (to_Z 1) with 1 in H6.
    change (to_Z 8) with 8 in H6.
    inversion H; subst b. clear H.
    pose proof (i63_range o). pose proof (i63_range a).
    assert (Eao : to_Z (a - o)%uint63 = to_Z a - to_Z o) by (apply toZ_sub_small; lia).
    cbn [hholds] in Hf.
    specialize (Hf (Z.to_nat (to_Z (a - o)%uint63)) ltac:(rewrite Eao; lia)).
    rewrite Z2Nat.id in Hf by (rewrite Eao; lia). rewrite Eao in Hf.
    replace (to_Z o + (to_Z a - to_Z o)) with (to_Z a) in Hf by lia.
    rewrite Hf, (ho_dv_tag0 v Ev), wbytes8_wbv. rewrite <- Eao. apply w_bytes_nth_byte. rewrite Eao. lia.
  - (* [comment removed for export] *)
    destruct ((t' =? t)%uint63 && in_iv o l a 1) eqn:E; [| apply IH; assumption].
    rewrite !andb_true_iff in E. destruct E as [Et Eiv].
    apply ho_eqb_eq in Et. subst t'.
    apply in_iv_spec in Eiv as (_ & _ & _ & _ & H5 & H6). change (to_Z 1) with 1 in H6.
    inversion H; subst b. clear H. cbn [hholds] in Hf.
    specialize (Hf (to_Z a - to_Z o) ltac:(lia)).
    replace (to_Z o + (to_Z a - to_Z o)) with (to_Z a) in Hf by lia. exact Hf.
  - (* [comment removed for export] *)
    destruct ((t =? 0)%uint63 && (lo <=? a)%uint63 && (a <? hi)%uint63 && (hi <=? b62)%uint63) eqn:E;
      [| apply IH; assumption].
    destruct (image_byte IM a) as [b' |] eqn:Eb; [| apply IH; assumption].
    inversion H; subst b'. clear H.
    rewrite !andb_true_iff in E. destruct E as [[[Et E1] E2] E3].
    apply ho_eqb_eq in Et. subst t. apply i_leb_le in E1, E3. apply i_ltb_lt in E2. rewrite ho_b62 in E3.
    cbn [hholds] in Hf. unfold image_byte in Eb.
    destruct (find_seg IM a) as [sg |] eqn:Hfs; [| discriminate Eb].
    destruct (find_seg_spec _ _ _ Hfs) as (Hin & G1 & G2).
    pose proof (proj1 (Forall_forall _ _) HIM sg Hin) as Hsg.
    assert (Hnum : to_Z (sg_base sg) <= to_Z a < to_Z (sg_base sg) + to_Z (sg_size sg)).
    { destruct Hsg as (seg & _ & _ & _ & _ & _ & _ & _ & _ & Hle & _).
      apply i_leb_le in G1. apply i_ltb_lt in G2.
      pose proof (i63_range (sg_base sg)) as Hb0. pose proof (i63_range (sg_size sg)) as Hn0.
      rewrite toZ_add_small in G2 by (clear - Hle Hb0 Hn0; zlia). clear - G1 G2. zlia. }
    rewrite ho_adr0. unfold rview. rewrite (Hf (to_Z a) ltac:(lia)).
    rewrite (memory_read_hex segs sg (to_Z a) (a - sg_base sg)%uint63 b Hsg Hnum); [reflexivity | | exact Eb].
    apply toZ_sub_small. clear - Hnum. zlia.
Qed.

Lemma byte_known_sound : forall t a b,
  byte_known IM facts t a = Some b ->
  rview segs (ms_mem ms) (adr rho t (to_Z a)) = Some (Z_to_bv 8 (to_Z b)).
Proof. intros t a b H. exact (byte_known_in_sound facts t a b Hfacts H). Qed.

(* [comment removed for export] *)
Lemma zero_cov_sound : forall t a n, zero_cov facts t a n = true ->
  forall j, 0 <= j < to_Z n ->
    rview segs (ms_mem ms) (adr rho t (to_Z a + j)) = Some (Z_to_bv 8 0).
Proof.
  intros t a n H j Hj. unfold zero_cov in H. apply existsb_exists in H as (f & Hin & Hf).
  destruct f as [| | | t' o l | | | | |]; try discriminate Hf.
  apply andb_true_iff in Hf as [Et Eiv]. apply ho_eqb_eq in Et. subst t'.
  apply in_iv_spec in Eiv as (_ & _ & _ & _ & H5 & H6).
  pose proof (proj1 (Forall_forall _ _) Hfacts _ Hin) as Hh. cbn [hholds] in Hh.
  specialize (Hh (to_Z a - to_Z o + j) ltac:(lia)).
  replace (to_Z o + (to_Z a - to_Z o + j)) with (to_Z a + j) in Hh by lia. exact Hh.
Qed.

Lemma wr_cov_sound : forall t a n, wr_cov facts t a n = true ->
  forall j, 0 <= j < to_Z n ->
    wview segs (ms_mem ms) (adr rho t (to_Z a + j)) <> None.
Proof.
  intros t a n H j Hj. unfold wr_cov in H. apply existsb_exists in H as (f & Hin & Hf).
  destruct f as [| | | | | t' o l | | |]; try discriminate Hf.
  apply andb_true_iff in Hf as [Et Eiv]. apply ho_eqb_eq in Et. subst t'.
  apply in_iv_spec in Eiv as (_ & _ & _ & _ & H5 & H6).
  pose proof (proj1 (Forall_forall _ _) Hfacts _ Hin) as Hh. cbn [hholds] in Hh.
  specialize (Hh (to_Z a - to_Z o + j) ltac:(lia)).
  replace (to_Z o + (to_Z a - to_Z o + j)) with (to_Z a + j) in Hh by lia. exact Hh.
Qed.

Lemma clear_cov_sound : forall a n, clear_cov facts a n = true ->
  forall x, to_Z a <= x < to_Z a + to_Z n -> ms_mem ms (Z_to_bv 64 x) = None.
Proof.
  intros a n H x Hx. unfold clear_cov in H. apply existsb_exists in H as (f & Hin & Hf).
  destruct f as [| | | | lo hi | | | |]; try discriminate Hf.
  rewrite !andb_true_iff in Hf. destruct Hf as [[[[E1 E2] E3] E4] E5].
  apply i_leb_le in E1, E3, E4, E5. apply i_ltb_lt in E2. rewrite ho_b62 in *.
  pose proof (i63_range a). pose proof (i63_range n).
  rewrite toZ_add_small in E4 by lia.
  pose proof (proj1 (Forall_forall _ _) Hfacts _ Hin) as Hh. cbn [hholds] in Hh.
  apply Hh. lia.
Qed.

(* [comment removed for export] *)
Lemma cell_ok_sound : forall t off v,
  to_Z off < 2 ^ 62 ->
  cell_ok IM facts t off v = true ->
  forall j, (j < 8)%nat ->
    rview segs (ms_mem ms) (adr rho t (to_Z off + Z.of_nat j)) = nth_error (wbytes8 (dv rho v)) j.
Proof.
  intros t off v Hoff H j Hj. unfold cell_ok in H.
  destruct (vtag v =? 0)%uint63 eqn:Ev.
  - rewrite forallb_forall in H.
    set (ji := of_Z (Z.of_nat j)).
    assert (Eji : to_Z ji = Z.of_nat j) by (unfold ji; apply toZ_of_Z_small; lia).
    specialize (H ji (in_iseq 8 ji ltac:(rewrite Eji; lia))).
    destruct (byte_known IM facts t (off + ji)%uint63) as [b |] eqn:Eb; [| discriminate H].
    apply ho_eqb_eq in H. subst b.
    pose proof (byte_known_sound t _ _ Eb) as Hrv.
    pose proof (i63_range off).
    rewrite toZ_add_small, Eji in Hrv by (rewrite Eji; lia).
    rewrite Hrv, (ho_dv_tag0 v Ev), wbytes8_wbv.
    rewrite <- (Nat2Z.id j), <- Eji. symmetry. apply w_bytes_nth_byte. rewrite Eji. lia.
  - apply existsb_exists in H as (f & Hin & Hf).
    destruct f as [| t' o v' | | | | | | |]; try discriminate Hf.
    rewrite !andb_true_iff in Hf. destruct Hf as [[Et Eo] Efv].
    apply ho_eqb_eq in Et, Eo. apply fval_eqb_eq in Efv. subst t' o v'.
    pose proof (proj1 (Forall_forall _ _) Hfacts _ Hin) as Hh. cbn [hholds] in Hh.
    exact (Hh j Hj).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wview_image_wr : forall pn sg j,
  to_Z pn < 2 ^ 50 ->
  find_seg IM (pn << 12)%uint63 = Some sg -> sg_wr sg = true ->
  0 <= j < 4096 ->
  wview segs (ms_mem ms) (Z_to_bv 64 (to_Z pn * 4096 + j)) <> None.
Proof.
  intros pn sg j Hpn Hf Hw Hj.
  destruct (find_seg_spec _ _ _ Hf) as (Hin & H1 & H2).
  pose proof (proj1 (Forall_forall _ _) HIM sg Hin) as Hsg.
  pose proof (proj1 (Forall_forall _ _) HWR sg Hin) as Hwr.
  pose proof (i63_range pn) as Hpn0.
  pose proof (ho_toZ_lsl12 pn Hpn) as Epn.
  assert (Hnum : to_Z (sg_base sg) <= to_Z pn * 4096
                 /\ to_Z pn * 4096 + 4096 <= to_Z (sg_base sg) + to_Z (sg_size sg)
                 /\ to_Z (sg_base sg) + to_Z (sg_size sg) <= 2 ^ 62).
  { destruct Hsg as (seg & _ & _ & _ & _ & _ & _ & Mb & Mn & Hle & _).
    apply i_leb_le in H1. apply i_ltb_lt in H2. rewrite Epn in H1, H2.
    pose proof (i63_range (sg_base sg)) as Hb0. pose proof (i63_range (sg_size sg)) as Hn0.
    rewrite toZ_add_small in H2 by (clear - Hle Hb0 Hn0; zlia).
    pose proof (Z.div_mod (to_Z (sg_base sg)) 4096 ltac:(discriminate)) as Db. rewrite Mb in Db.
    pose proof (Z.div_mod (to_Z (sg_size sg)) 4096 ltac:(discriminate)) as Dn. rewrite Mn in Dn.
    clear - H1 H2 Hle Db Dn Hb0 Hn0.
    generalize dependent (to_Z (sg_base sg) / 4096).
    generalize dependent (to_Z (sg_size sg) / 4096). intros qn Dn qb Db. zlia. }
  destruct Hnum as (HB & HT & Hle).
  pose proof (i63_range (sg_base sg)) as Hb0.
  unfold wview. destruct (ms_mem ms (Z_to_bv 64 (to_Z pn * 4096 + j))) as [b0 |]; [discriminate |].
  assert (Hr : to_Z (sg_base sg) <= to_Z pn * 4096 + j < to_Z (sg_base sg) + to_Z (sg_size sg))
    by (clear - HB HT Hj; zlia).
  destruct Hsg as (seg & _ & Eb & En & Ebytes & Er & Ew & _ & _ & _ & Hfind).
  assert (EA : bv_unsigned (Z_to_bv 64 (to_Z pn * 4096 + j)) = to_Z pn * 4096 + j).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    clear - Hr Hle Hb0. zlia. }
  rewrite EA, (Hfind _ Hr), Ew, Hw, Ebytes.
  assert (Ho : 0 <= to_Z pn * 4096 + j - to_Z (sg_base sg) < to_Z (sg_size sg)) by (clear - Hr; zlia).
  specialize (Hwr Hw _ Ho).
  destruct (hex_byte (sg_hex sg) (of_Z (to_Z pn * 4096 + j - to_Z (sg_base sg)))) as [b |] eqn:Hb; [| congruence].
  destruct (seg_byte_hex _ _ _ Hb) as [Hs _].
  rewrite toZ_of_Z_small in Hs by (clear - Ho Hle Hb0 Hr; zlia).
  rewrite Eb, Hs. discriminate.
Qed.

(* [comment removed for export] *)
Lemma image_cell_rview : forall pn ci v,
  to_Z pn < 2 ^ 50 -> 0 <= to_Z ci < 512 ->
  image_cell IM ((pn << 12) + (ci << 3))%uint63 = Some v ->
  (forall x, to_Z pn * 4096 + to_Z ci * 8 <= x < to_Z pn * 4096 + to_Z ci * 8 + 8 ->
             ms_mem ms (Z_to_bv 64 x) = None) ->
  forall j, (j < 8)%nat ->
    rview segs (ms_mem ms) (adr rho 0%uint63 (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j))
    = nth_error (wbytes8 (dv rho v)) j.
Proof.
  intros pn ci v Hpn Hci Hcell Hclr j Hj.
  destruct (image_cell_tag _ _ _ Hcell) as [w ->].
  pose proof (i63_range pn) as Hpn0.
  pose proof (ho_toZ_lsl12 pn Hpn) as Epn. pose proof (ho_toZ_lsl3 ci ltac:(lia)) as Eci.
  assert (Ea8 : to_Z ((pn << 12) + (ci << 3))%uint63 = to_Z pn * 4096 + to_Z ci * 8).
  { rewrite toZ_add_small; rewrite Epn, Eci; [reflexivity | lia]. }
  assert (Hal : to_Z ((pn << 12) + (ci << 3))%uint63 mod 8 = 0).
  { rewrite Ea8. replace (to_Z pn * 4096 + to_Z ci * 8) with ((to_Z pn * 512 + to_Z ci) * 8) by ring.
    apply Z.mod_mul. discriminate. }
  pose proof (image_cell_sound segs IM _ w HIM Hal Hcell j Hj) as Hrd. rewrite Ea8 in Hrd.
  rewrite ho_adr0. unfold rview.
  rewrite (Hclr (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j) ltac:(lia)), Hrd.
  rewrite (fk_dv_conc rho w Hrho0). unfold wbytes8. rewrite wbv_unsigned.
  destruct (nth_error (Z_to_le_bytes 8 (wZ w)) j); reflexivity.
Qed.

Lemma ho_dv_fv0_bytes : forall j, (j < 8)%nat ->
  nth_error (wbytes8 (dv rho fv0)) j = Some (Z_to_bv 8 0).
Proof.
  intros j Hj. unfold fv0. rewrite (fk_dv_conc rho w_zero Hrho0). unfold wbytes8. rewrite wbv_unsigned.
  rewrite wZ_w_zero. do 8 (destruct j as [|j]; [reflexivity |]). lia.
Qed.

(* [comment removed for export] *)
Lemma sv_cov_sound : forall t a v j,
  sv_cov facts t a v j = true ->
  rview segs (ms_mem ms) (adr rho t (to_Z a)) = nth_error (wbytes8 (dv rho v)) (Z.to_nat (to_Z j)).
Proof.
  intros t a v j H. unfold sv_cov in H. apply existsb_exists in H as (f & Hin & Hf).
  pose proof (proj1 (Forall_forall _ _) Hfacts _ Hin) as Hh.
  pose proof (i63_range j) as Hj0.
  destruct f as [| t' o v' | t' o n v' | | | | | |]; try discriminate Hf.
  - (* [comment removed for export] *)
    rewrite !andb_true_iff in Hf. destruct Hf as [[[[E1 Ev] Hj8] Ho] Ea].
    apply ho_eqb_eq in E1, Ea. apply fval_eqb_eq in Ev. subst t' v' a.
    apply i_ltb_lt in Hj8, Ho. change (to_Z 8) with 8 in Hj8. rewrite ho_b62 in Ho.
    pose proof (i63_range o) as Ho0.
    cbn [hholds] in Hh. specialize (Hh (Z.to_nat (to_Z j)) ltac:(lia)).
    rewrite Z2Nat.id in Hh by lia. rewrite toZ_add_small by lia. exact Hh.
  - (* [comment removed for export] *)
    rewrite !andb_true_iff in Hf. destruct Hf as [[[[[E1 Ev] Hjn] Hj8] Ho] Ea].
    apply ho_eqb_eq in E1, Ea. apply fval_eqb_eq in Ev. subst t' v' a.
    apply i_ltb_lt in Hjn, Hj8, Ho. change (to_Z 8) with 8 in Hj8. rewrite ho_b62 in Ho.
    pose proof (i63_range o) as Ho0.
    cbn [hholds] in Hh. specialize (Hh (Z.to_nat (to_Z j)) ltac:(lia)).
    rewrite Z2Nat.id in Hh by lia. rewrite toZ_add_small by lia. exact Hh.
Qed.

(* [comment removed for export] *)
Lemma page_ok_b_sound : forall r p,
  page_ok_b IM facts r p = true ->
  page_ok segs IM rho (ms_mem ms) (rd_tag r) (pd_pn p) 4096 (page_of p)
  /\ to_Z (rd_lo r) <= to_Z (pd_pn p) * 4096
  /\ to_Z (pd_pn p) * 4096 + 4096 <= to_Z (rd_len r).
Proof.
  intros r p H. unfold page_ok_b in H. cbv zeta in H.
  rewrite !andb_true_iff in H. destruct H as [[[[[[Hpn Hlo] Hup] Hlen] Hwr] Hkind] Hcells].
  apply i_ltb_lt in Hpn. rewrite ho_b50 in Hpn.
  apply i_leb_le in Hlo, Hup, Hlen. rewrite ho_b62 in Hlen.
  pose proof (i63_range (pd_pn p)) as Hpn0.
  pose proof (ho_toZ_lsl12 _ Hpn) as Epn. rewrite Epn in Hlo.
  rewrite toZ_add_small, Epn in Hup by (rewrite Epn; change (to_Z 4096) with 4096; lia).
  change (to_Z 4096) with 4096 in Hup.
  split; [| split; [exact Hlo | exact Hup]].
  apply page_ok_of_whole; [reflexivity | | |].
  - (* [comment removed for export] *)
    cbn [page_of pg_wr]. intros Hw j Hj. rewrite Hw in Hwr.
    destruct (rd_tag r =? 0)%uint63 eqn:Et.
    + apply ho_eqb_eq in Et. rewrite Et, ho_adr0.
      unfold seg_wr_page in Hwr.
      destruct (find_seg IM (pd_pn p << 12)%uint63) as [sg |] eqn:Hf; [| discriminate Hwr].
      exact (wview_image_wr _ sg j Hpn Hf Hwr Hj).
    + pose proof (wr_cov_sound _ _ _ Hwr j ltac:(change (to_Z 4096) with 4096; exact Hj)) as Hv.
      rewrite Epn in Hv. exact Hv.
  - (* [comment removed for export] *)
    intros ci v Hci Hcell j Hj. change (4096 / 8) with 512 in Hci.
    rewrite forallb_forall in Hcells.
    specialize (Hcells ci (in_iseq 512 ci ltac:(change (Z.of_nat 512) with 512; lia))).
    pose proof (ho_toZ_lsl3 ci ltac:(lia)) as Eci.
    assert (Eoff : to_Z ((pd_pn p << 12) + (ci << 3))%uint63 = to_Z (pd_pn p) * 4096 + to_Z ci * 8).
    { rewrite toZ_add_small; rewrite Epn, Eci; [reflexivity | lia]. }
    unfold cell_at in Hcell.
    destruct (iget ci (pg_cells (page_of p))) as [[v0 | | sl0] |] eqn:Eg.
    + inversion Hcell; subst v0.
      pose proof (cell_ok_sound _ _ _ ltac:(rewrite Eoff; lia) Hcells j Hj) as Hv.
      rewrite Eoff in Hv. exact Hv.
    + discriminate Hcell.
    + discriminate Hcell.
    + cbn [page_of pg_kind] in Hcell, Hcells.
      destruct (pd_kind p) eqn:Ek.
      * inversion Hcell; subst v.
        pose proof (zero_cov_sound _ _ _ Hcells (Z.of_nat j) ltac:(change (to_Z 8) with 8; lia)) as Hv.
        rewrite Eoff in Hv. rewrite Hv. symmetry. apply ho_dv_fv0_bytes. exact Hj.
      * apply ho_eqb_eq in Hkind. rewrite Hkind.
        apply (image_cell_rview _ ci v Hpn Hci Hcell); [| exact Hj].
        intros x Hx. apply (clear_cov_sound _ _ Hcells). rewrite Eoff. change (to_Z 8) with 8. lia.
      * discriminate Hcell.
  - (* [comment removed for export] *)
    intros ci sl Hci Hget j Hj. change (4096 / 8) with 512 in Hci.
    rewrite forallb_forall in Hcells.
    specialize (Hcells ci (in_iseq 512 ci ltac:(change (Z.of_nat 512) with 512; lia))).
    rewrite Hget in Hcells. rewrite forallb_forall in Hcells.
    specialize (Hcells j (in_iseq 8 j ltac:(change (Z.of_nat 8) with 8; lia))).
    pose proof (ho_toZ_lsl3 ci ltac:(lia)) as Eci.
    assert (Eoff : to_Z ((pd_pn p << 12) + (ci << 3))%uint63 = to_Z (pd_pn p) * 4096 + to_Z ci * 8).
    { rewrite toZ_add_small; rewrite Epn, Eci; [reflexivity | lia]. }
    assert (Ea : to_Z ((pd_pn p << 12) + (ci << 3) + j)%uint63
                 = to_Z (pd_pn p) * 4096 + to_Z ci * 8 + to_Z j).
    { rewrite toZ_add_small; rewrite Eoff; [reflexivity | lia]. }
    unfold slot_ok_b in Hcells. unfold slot_ok.
    destruct (sget j sl) as [b | v j0 |].
    + destruct (byte_known IM facts (rd_tag r) ((pd_pn p << 12) + (ci << 3) + j)%uint63) as [b' |] eqn:Hb;
        [| discriminate Hcells].
      apply ho_eqb_eq in Hcells. subst b'.
      pose proof (byte_known_sound _ _ _ Hb) as Hv. rewrite Ea in Hv. exact Hv.
    + pose proof (sv_cov_sound _ _ _ _ Hcells) as Hv. rewrite Ea in Hv. exact Hv.
    + exact I.
Qed.

(* [comment removed for export] *)
Lemma pages_from_spec : forall n pn0 f pn,
  to_Z pn0 + Z.of_nat n < 2 ^ 62 ->
  pages_from n pn0 f = true ->
  to_Z pn0 <= to_Z pn < to_Z pn0 + Z.of_nat n -> f pn = true.
Proof.
  induction n as [| n IH]; intros pn0 f pn Hb H Hr; [lia |].
  cbn [pages_from] in H. apply andb_true_iff in H as [H0 Hrest].
  pose proof (i63_range pn0).
  assert (Es : to_Z (pn0 + 1)%uint63 = to_Z pn0 + 1) by (apply toZ_add_small; change (to_Z 1) with 1; lia).
  destruct (Z.eq_dec (to_Z pn) (to_Z pn0)) as [E | E].
  - apply to_Z_inj in E. subst pn. exact H0.
  - apply (IH (pn0 + 1)%uint63 f pn); [rewrite Es; lia | exact Hrest | rewrite Es; lia].
Qed.

Lemma image_page_ok : forall pn sg,
  to_Z pn < 2 ^ 50 ->
  find_seg IM (pn << 12)%uint63 = Some sg ->
  (forall x, to_Z pn * 4096 <= x < to_Z pn * 4096 + 4096 -> ms_mem ms (Z_to_bv 64 x) = None) ->
  page_ok segs IM rho (ms_mem ms) 0%uint63 pn 4096 (PG (sg_wr sg) PKImage iempty).
Proof.
  intros pn sg Hpn Hf Hclr. apply page_ok_of_whole; [reflexivity | | |];
    [| | intros ci sl _ Hget; cbn [pg_cells] in Hget; rewrite iget_iempty in Hget; discriminate Hget].
  - cbn [pg_wr]. intros Hw j Hj. rewrite ho_adr0. exact (wview_image_wr pn sg j Hpn Hf Hw Hj).
  - intros ci v Hci Hcell j Hj. change (4096 / 8) with 512 in Hci. unfold cell_at in Hcell. cbn [pg_cells pg_kind] in Hcell.
    rewrite iget_iempty in Hcell.
    apply (image_cell_rview pn ci v Hpn Hci Hcell); [| exact Hj].
    intros x Hx. apply Hclr. lia.
Qed.

Lemma image_pages_ok_sound : forall r pn sg,
  image_pages_ok IM facts r = true ->
  to_Z pn < 2 ^ 50 ->
  find_seg IM (pn << 12)%uint63 = Some sg ->
  explicit_b r pn = false ->
  page_ok segs IM rho (ms_mem ms) 0%uint63 pn 4096 (PG (sg_wr sg) PKImage iempty)
  /\ to_Z (rd_lo r) <= to_Z pn * 4096 /\ to_Z pn * 4096 + 4096 <= to_Z (rd_len r).
Proof.
  intros r pn sg H Hpn Hf Hexp. unfold image_pages_ok in H. rewrite forallb_forall in H.
  destruct (find_seg_spec _ _ _ Hf) as (Hin & H1 & H2).
  specialize (H sg Hin). rewrite !andb_true_iff in H. destruct H as [[Hb Hs] Hpf].
  apply i_ltb_lt in Hb. apply i_leb_le in Hs. rewrite ho_b62 in Hb, Hs.
  pose proof (proj1 (Forall_forall _ _) HIM sg Hin) as Hsg.
  pose proof (i63_range pn) as Hpn0. pose proof (ho_toZ_lsl12 pn Hpn) as Epn.
  pose proof (i63_range (sg_base sg)) as Hb0. pose proof (i63_range (sg_size sg)) as Hn0.
  (* [comment removed for export] *)
  destruct Hsg as (seg & _ & _ & _ & _ & _ & _ & Mb & Mn & Hle & _).
  pose proof (Z.div_mod (to_Z (sg_base sg)) 4096 ltac:(discriminate)) as Db. rewrite Mb in Db.
  pose proof (Z.div_mod (to_Z (sg_size sg)) 4096 ltac:(discriminate)) as Dn. rewrite Mn in Dn.
  apply i_leb_le in H1. apply i_ltb_lt in H2. rewrite Epn in H1, H2.
  rewrite toZ_add_small in H2 by (clear - Hb Hs Hb0 Hn0; zlia).
  assert (Eqb : to_Z (sg_base sg >> 12)%uint63 = to_Z (sg_base sg) / 4096) by (rewrite lsr_spec; reflexivity).
  assert (Eqn : to_Z (sg_size sg >> 12)%uint63 = to_Z (sg_size sg) / 4096) by (rewrite lsr_spec; reflexivity).
  assert (Hrange : to_Z (sg_base sg >> 12)%uint63 <= to_Z pn
                   < to_Z (sg_base sg >> 12)%uint63 + Z.of_nat (Z.to_nat (to_Z (sg_size sg >> 12)%uint63))
                   /\ to_Z (sg_base sg >> 12)%uint63 + Z.of_nat (Z.to_nat (to_Z (sg_size sg >> 12)%uint63)) < 2 ^ 62).
  { rewrite Eqb, Eqn. clear - H1 H2 Hb Hs Db Dn Hb0 Hn0 Hpn0.
    generalize dependent (to_Z (sg_base sg) / 4096). generalize dependent (to_Z (sg_size sg) / 4096).
    intros qn Dn qb Db. rewrite Z2Nat.id by zlia. zlia. }
  destruct Hrange as [Hrange Hbnd].
  pose proof (pages_from_spec _ _ _ pn Hbnd Hpf Hrange) as Hfp. cbv beta in Hfp.
  rewrite Hexp in Hfp. cbn [orb] in Hfp.
  rewrite !andb_true_iff in Hfp. destruct Hfp as [[Hlo Hup] Hclr].
  apply i_leb_le in Hlo, Hup. rewrite Epn in Hlo.
  clear Db Dn Eqb Eqn Hrange Hbnd H1 H2.
  rewrite toZ_add_small, Epn in Hup
    by (rewrite Epn; change (to_Z 4096) with 4096; clear - Hpn Hpn0; lia).
  change (to_Z 4096) with 4096 in Hup.
  split; [| split; [exact Hlo | exact Hup]].
  apply (image_page_ok pn sg Hpn Hf).
  intros x Hx. apply (clear_cov_sound _ _ Hclr). rewrite Epn. change (to_Z 4096) with 4096. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_in_region_spec : forall rg pn, page_in_region rg pn = true ->
  to_Z pn < 2 ^ 50 /\ to_Z (rg_lo rg) <= to_Z pn * 4096
  /\ to_Z pn * 4096 < to_Z (rg_len rg)
  /\ to_Z (rg_len rg) <= 2 ^ 62.
Proof.
  intros rg pn H. unfold page_in_region in H. rewrite !andb_true_iff in H.
  destruct H as [[[Hpn Hlo] Hup] Hlen].
  apply i_ltb_lt in Hpn. change (to_Z 1125899906842624) with (2 ^ 50) in Hpn.
  apply i_leb_le in Hlo, Hlen. change (to_Z 4611686018427387904) with (2 ^ 62) in Hlen.
  pose proof (i63_range pn). pose proof (ho_toZ_lsl12 pn Hpn) as Epn. rewrite Epn in Hlo.
  split; [exact Hpn|]. split; [exact Hlo|].
  apply i_ltb_lt in Hup. rewrite Epn in Hup. split; [exact Hup | exact Hlen].
Qed.

Lemma len_mod8_b : forall len : int, ((len land 7) =? 0)%uint63 = true -> to_Z len mod 8 = 0.
Proof.
  intros len Hal. apply ho_eqb_eq in Hal. apply (f_equal to_Z) in Hal. pose proof (i63_range len).
  rewrite (i63_land_ones len 7%uint63 3 eq_refl ltac:(lia)) in Hal. change (2 ^ 3) with 8 in Hal.
  change (to_Z 0) with 0 in Hal. exact Hal.
Qed.

Lemma default_page_ok : forall t lo len pn k,
  (lo <=? len)%uint63 = true ->
  wr_cov facts t lo (len - lo)%uint63 = true ->
  (k = PKUnk \/ (k = PKZero /\ zero_cov facts t lo (len - lo)%uint63 = true /\ to_Z len mod 8 = 0)) ->
  to_Z pn < 2 ^ 50 -> to_Z lo <= to_Z pn * 4096 ->
  forall B, 0 <= B <= 4096 -> to_Z pn * 4096 + B <= to_Z len -> (B mod 8 = 0 \/ to_Z pn * 4096 + B = to_Z len) ->
  page_ok segs IM rho (ms_mem ms) t pn B (PG true k iempty).
Proof.
  intros t lo len pn k Hle Hwr Hk Hpn Hlo B HB Hup HB8.
  apply i_leb_le in Hle. pose proof (i63_range lo). pose proof (i63_range len). pose proof (i63_range pn).
  assert (Esub : to_Z (len - lo)%uint63 = to_Z len - to_Z lo) by (apply toZ_sub_small; exact Hle).
  split; [| split; [| split]];
    [| | intros ci sl _ _ Hget; cbn [pg_cells] in Hget; rewrite iget_iempty in Hget; discriminate Hget |].
  3:{ (* [comment removed for export] *)
      intros ci Hci Hcut. unfold cell_at. cbn [pg_cells pg_kind]. rewrite iget_iempty.
      destruct Hk as [-> | (-> & _ & Hl8)]; [reflexivity|]. exfalso. Z.div_mod_to_equations. lia. }
  - intros _ j Hj.
    pose proof (wr_cov_sound _ _ _ Hwr (to_Z pn * 4096 + j - to_Z lo) ltac:(rewrite Esub; lia)) as Hv.
    replace (to_Z lo + (to_Z pn * 4096 + j - to_Z lo)) with (to_Z pn * 4096 + j) in Hv by lia. exact Hv.
  - intros ci v Hci Hcell j Hj. unfold cell_at in Hcell. cbn [pg_cells pg_kind] in Hcell.
    rewrite iget_iempty in Hcell.
    destruct Hk as [-> | (-> & Hz & Hl8)]; [discriminate Hcell |].
    inversion Hcell; subst v.
    pose proof (zero_cov_sound _ _ _ Hz (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j - to_Z lo)
                  ltac:(rewrite Esub; Z.div_mod_to_equations; lia)) as Hv.
    replace (to_Z lo + (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j - to_Z lo))
      with (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j) in Hv by lia.
    rewrite Hv. symmetry. apply ho_dv_fv0_bytes. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma region_fact_b_sound : forall r,
  region_fact_b facts r = true -> region_ok rho (rd_tag r) (region_of r).
Proof.
  intros r H. unfold region_fact_b in H.
  destruct (rd_tag r =? 0)%uint63 eqn:Et.
  - apply ho_eqb_eq in Et. apply i_leb_le in H. rewrite ho_b62 in H.
    unfold region_ok, region_of. cbn [rg_len rg_lo rg_align rg_clo rg_chi]. rewrite Et, Hrho0.
    change (bv_unsigned (Z_to_bv 64 0)) with 0.
    pose proof (i63_range (rd_len r)). pose proof (i63_range (rd_align r)).
    split; [change (to_Z 0) with 0; lia |].
    split; [exact H |]. split; [lia |]. split; [intros Hc; contradiction Hc; reflexivity |].
    split; [apply Z.mod_0_l; apply Z.pow_nonzero; lia |].
    split; [change (to_Z clo_dflt) with 0; change (to_Z chi_dflt) with (2 ^ 63 - 1); lia | exact I].
  - apply existsb_exists in H as (f & Hin & Hf).
    destruct f as [| | | | | | | t lo len al |]; try discriminate Hf.
    rewrite !andb_true_iff in Hf. destruct Hf as [[[E1 E2] E3] E4].
    apply ho_eqb_eq in E1, E2, E3, E4. subst t lo len al.
    pose proof (proj1 (Forall_forall _ _) Hfacts _ Hin) as Hh. cbn [hholds] in Hh.
    unfold region_ok, region_of in *. cbn [rg_len rg_lo rg_align rg_clo rg_chi] in *. exact Hh.
Qed.

Lemma disj_fact_b_sound : forall r r',
  disj_fact_b facts r r' = true ->
  bv_unsigned (rho (rd_tag r)) + to_Z (rd_len r) <= bv_unsigned (rho (rd_tag r')) + to_Z (rd_lo r')
  \/ bv_unsigned (rho (rd_tag r')) + to_Z (rd_len r') <= bv_unsigned (rho (rd_tag r)) + to_Z (rd_lo r).
Proof.
  intros r r' H. unfold disj_fact_b in H. apply existsb_exists in H as (f & Hin & Hf).
  destruct f as [| | | | | | | | t1 lo1 len1 t2 lo2 len2]; try discriminate Hf.
  pose proof (proj1 (Forall_forall _ _) Hfacts _ Hin) as Hh. cbn [hholds] in Hh.
  apply orb_true_iff in Hf as [Hf | Hf]; rewrite !andb_true_iff in Hf;
    destruct Hf as [[[[[E1 E2] E3] E4] E5] E6];
    apply ho_eqb_eq in E1, E2, E3, E4, E5, E6; subst t1 lo1 len1 t2 lo2 len2.
  - exact Hh.
  - destruct Hh as [Hh | Hh]; [right | left]; exact Hh.
Qed.

(* [comment removed for export] *)
Lemma region_ok_b_sound : forall d r,
  region_ok_b IM facts d r = true ->
  region_ok rho (rd_tag r) (region_of r)
  /\ forall pn pg, to_Z pn < 2 ^ 50 -> page_at IM (region_of r) (rd_tag r) pn = Some pg ->
       page_ok segs IM rho (ms_mem ms) (rd_tag r) pn (blim (region_of r) pn) pg
       /\ to_Z (rg_lo (region_of r)) <= to_Z pn * 4096
       /\ to_Z pn * 4096 < to_Z (rg_len (region_of r)).
Proof.
  intros d r H. unfold region_ok_b in H. rewrite !andb_true_iff in H.
  destruct H as [[[Hfact _] Hpages] Hrest].
  split; [apply region_fact_b_sound; exact Hfact |].
  intros pn pg Hpn Hpa.
  assert (Hwhole : forall pg', page_ok segs IM rho (ms_mem ms) (rd_tag r) pn 4096 pg'
            /\ to_Z (rd_lo r) <= to_Z pn * 4096 /\ to_Z pn * 4096 + 4096 <= to_Z (rd_len r) ->
            page_ok segs IM rho (ms_mem ms) (rd_tag r) pn (blim (region_of r) pn) pg'
            /\ to_Z (rd_lo r) <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z (rd_len r)).
  { intros pg' (Hok & Hl & Hu).
    assert (Ec : blim (region_of r) pn = 4096).
    { unfold blim. cbn [region_of rg_len]. clear - Hu. lia. }
    rewrite Ec. split; [exact Hok|]. split; [exact Hl | lia]. }
  cbn [region_of rg_lo rg_len].
  unfold page_at in Hpa. cbn [region_of rg_pages rg_dflt] in Hpa.
  destruct (iget pn (iof_list (map (fun p => (pd_pn p, page_of p)) (rd_pages r)))) as [pg0 |] eqn:Eg.
  - (* [comment removed for export] *)
    inversion Hpa; subst pg0. clear Hpa.
    destruct (iget_iof_list_map_In pd_pn page_of _ _ _ Eg) as (p & Hp & Hk & ->). subst pn.
    rewrite forallb_forall in Hpages. exact (Hwhole _ (page_ok_b_sound r p (Hpages p Hp))).
  - assert (Hexp : explicit_b r pn = false).
    { unfold explicit_b. destruct (existsb (fun p => (pd_pn p =? pn)%uint63) (rd_pages r)) eqn:E; [| reflexivity].
      apply existsb_exists in E as (p & Hp & Hk). apply ho_eqb_eq in Hk.
      exfalso. exact (iget_iof_list_map_None pd_pn page_of _ _ Eg p Hp Hk). }
    destruct (rd_tag r =? 0)%uint63 eqn:Et.
    + apply ho_eqb_eq in Et. apply andb_true_iff in Hrest as [Himg Hdf].
      destruct (find_seg IM (pn << 12)%uint63) as [sg |] eqn:Hf.
      * inversion Hpa; subst pg. apply Hwhole. rewrite Et.
        exact (image_pages_ok_sound r pn sg Himg Hpn Hf Hexp).
      * destruct (rd_dflt r); [discriminate Hdf | discriminate Hpa].
    + destruct (rd_dflt r) as [k |] eqn:Ek; [| discriminate Hpa].
      destruct (page_in_region (region_of r) pn) eqn:Epr; [| discriminate Hpa].
      inversion Hpa; subst pg. clear Hpa.
      apply page_in_region_spec in Epr as (_ & Hlo & Hup & _). cbn [region_of rg_lo rg_len] in Hlo, Hup.
      split; [| split; [exact Hlo | exact Hup]].
      assert (HL : 0 <= blim (region_of r) pn <= 4096 /\ to_Z pn * 4096 + blim (region_of r) pn <= to_Z (rd_len r)
                   /\ (blim (region_of r) pn mod 8 = 0 \/ to_Z pn * 4096 + blim (region_of r) pn = to_Z (rd_len r))).
      { unfold blim. cbn [region_of rg_len]. clear - Hup.
        destruct (Z_le_gt_dec 4096 (to_Z (rd_len r) - to_Z pn * 4096)); [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; [split; [lia|]; split; [lia | left; reflexivity] | lia]. }
      destruct k.
      * rewrite !andb_true_iff in Hrest. destruct Hrest as [[[Hle Hwr] Hz] Hal].
        apply (default_page_ok _ (rd_lo r) (rd_len r) pn PKZero Hle Hwr); [right; split; [reflexivity | split; [exact Hz | exact (len_mod8_b _ Hal)]] | exact Hpn | exact Hlo | exact (proj1 HL) | exact (proj1 (proj2 HL)) | exact (proj2 (proj2 HL))].
      * discriminate Hrest.
      * rewrite !andb_true_iff in Hrest. destruct Hrest as [Hle Hwr].
        apply (default_page_ok _ (rd_lo r) (rd_len r) pn PKUnk Hle Hwr); [left; reflexivity | exact Hpn | exact Hlo | exact (proj1 HL) | exact (proj1 (proj2 HL)) | exact (proj2 (proj2 HL))].
Qed.

(* [comment removed for export] *)
Lemma regs_ok_b_sound : forall d (r : reg),
  regs_ok_b facts d = true ->
  Sem.rget (core_of ms) r = dv rho (FxState.rget (state_of d) (ireg r)).
Proof.
  intros d r H. unfold regs_ok_b in H. rewrite forallb_forall in H.
  assert (Hir : to_Z (ireg r) = bv_unsigned r).
  { unfold ireg. pose proof (bv_unsigned_in_range _ r) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 5) with 32 in Hr. apply toZ_of_Z_small. lia. }
  pose proof (bv_unsigned_in_range _ r) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 5) with 32 in Hr.
  specialize (H (ireg r) (in_iseq 32 _ ltac:(rewrite Hir; change (Z.of_nat 32) with 32; lia))).
  apply orb_true_iff in H as [H0 | Hex].
  - apply ho_eqb_eq in H0. unfold FxState.rget. rewrite H0, Uint63.eqb_refl.
    unfold Sem.rget. assert (Hx : is_x0 r = true).
    { unfold is_x0. apply Z.eqb_eq. rewrite <- Hir, H0. reflexivity. }
    rewrite Hx. unfold fv0. rewrite (fk_dv_conc rho w_zero Hrho0). symmetry. apply wbv_w_zero.
  - apply existsb_exists in Hex as (f & Hin & Hf).
    destruct f as [| | | | | | r' v' | |]; try discriminate Hf.
    apply andb_true_iff in Hf as [Er Ev]. apply ho_eqb_eq in Er. apply fval_eqb_eq in Ev. subst r' v'.
    pose proof (proj1 (Forall_forall _ _) Hfacts _ Hin) as Hh. cbn [hholds] in Hh.
    exact (Hh r eq_refl).
Qed.

End Facts.

Theorem handoff_R : forall facts d rho ms,
  ho_check IM facts d = true ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  Forall (hholds segs rho ms) facts ->
  ms_pc_val ms = Z_to_bv 64 (to_Z (sd_pc d)) ->
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  R segs IM rho (state_of d) ms.
Proof.
  intros facts d rho ms Hc Hrho0 Hfacts Hpc Hsvc Hresv.
  unfold ho_check in Hc. apply andb_true_iff in Hc as [Hregs Hmem].
  rewrite forallb_forall in Hmem.
  constructor.
  - exact Hpc.
  - intros r. exact (regs_ok_b_sound facts rho ms Hrho0 Hfacts d r Hregs).
  - exact Hsvc.
  - rewrite Hresv. reflexivity.
  - cbn [state_of f_mem]. split.
    + intros t rg Hget.
      destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hget) as (r & Hr & Ht & ->). subst t.
      exact (region_ok_b_sound facts rho ms Hrho0 Hfacts d r (Hmem r Hr)).
    + intros t t' rg rg' Hne Hget Hget'.
      destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hget) as (r & Hr & Ht & ->).
      destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hget') as (r' & Hr' & Ht' & ->).
      subst t t'. cbn [region_of rg_len rg_lo].
      pose proof (Hmem r Hr) as Hrb. unfold region_ok_b in Hrb. rewrite !andb_true_iff in Hrb.
      destruct Hrb as [[[_ Hdisj] _] _]. rewrite forallb_forall in Hdisj.
      specialize (Hdisj r' Hr'). apply orb_true_iff in Hdisj as [Heq | Hd].
      * apply ho_eqb_eq in Heq. congruence.
      * exact (disj_fact_b_sound facts rho ms Hfacts r r' Hd).
Qed.

Lemma hholds_agree : forall n rho rho' ms f,
  agree n rho rho' -> fact_tags_lt n f = true ->
  hholds segs rho ms f -> hholds segs rho' ms f.
Proof.
  intros n rho rho' ms f [_ Hag] Hlt Hh.
  assert (Hadr : forall t z, (t <? n)%uint63 = true -> adr rho' t z = adr rho t z).
  { intros t z Ht. unfold adr. rewrite (Hag t (i_ltb_lt _ _ Ht)). reflexivity. }
  assert (Hdv : forall v, (vtag v <? n)%uint63 = true -> dv rho' v = dv rho v).
  { (* [comment removed for export] *)
    intros v Hv. apply i_ltb_lt in Hv. unfold dv.
    destruct (fk_tag_decomp (vtag v)) as [E Hb0]. pose proof (fk_vkind_le5 (vtag v)) as Hk.
    rewrite (Hag (vbase (vtag v))) by nia. reflexivity. }
  destruct f as [t off k w | t off v | t off k v | t off len | lo hi | t off len | r v | t lo len al
                 | t1 lo1 len1 t2 lo2 len2]; cbn [fact_tags_lt hholds] in *.
  - intros j Hj. rewrite (Hadr t _ Hlt). exact (Hh j Hj).
  - apply andb_true_iff in Hlt as [Ht Hv]. intros j Hj. rewrite (Hadr t _ Ht), (Hdv v Hv). exact (Hh j Hj).
  - apply andb_true_iff in Hlt as [Ht Hv]. intros j Hj. rewrite (Hadr t _ Ht), (Hdv v Hv). exact (Hh j Hj).
  - intros j Hj. rewrite (Hadr t _ Hlt). exact (Hh j Hj).
  - exact Hh.
  - intros j Hj. rewrite (Hadr t _ Hlt). exact (Hh j Hj).
  - intros rr Hrr. rewrite (Hdv v Hlt). exact (Hh rr Hrr).
  - unfold region_ok in *. rewrite (Hag t (i_ltb_lt _ _ Hlt)). exact Hh.
  - apply andb_true_iff in Hlt as [H1 H2].
    rewrite (Hag t1 (i_ltb_lt _ _ H1)), (Hag t2 (i_ltb_lt _ _ H2)). exact Hh.
Qed.

Theorem handoff_Rn : forall facts d n rho ms,
  ho_check IM facts d = true ->
  forallb (fact_tags_lt n) facts = true ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  Forall (hholds segs rho ms) facts ->
  ms_pc_val ms = Z_to_bv 64 (to_Z (sd_pc d)) ->
  ms_svc_pending ms = None ->
  ms_resv ms = None ->
  Rn segs IM n rho (state_of d) ms.
Proof.
  intros facts d n rho ms Hc Hlt Hrho Hf Hpc Hsvc Hresv rho' Hag.
  apply (handoff_R facts d rho' ms Hc (proj1 Hag)); [|exact Hpc|exact Hsvc|exact Hresv].
  rewrite Forall_forall in *. intros f Hin.
  apply (hholds_agree n rho rho' ms f Hag); [|apply Hf; exact Hin].
  rewrite forallb_forall in Hlt. apply Hlt. exact Hin.
Qed.
End Sound.
