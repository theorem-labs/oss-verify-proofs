(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzLemmasMtf BzCLemmas1 BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pwd (d : dst) : dst := d_set_out_len (d_set_cbcrc d (crc_update (d_cbcrc d) (d_out_ch d))) (d_out_len d - 1).
Definition pws (d : dst) (s : dstrm) : dstrm := out_byte s (d_out_ch d).

(* [comment removed for export] *)
Definition pfl' (n : nat) (d : dst) (s : dstrm) : dst * dstrm * bool :=
  if d_out_len d =? 0 then (d, s, false) else flush_run n (pwd d) (pws d s).

Lemma flush_run_S : forall n d s,
  flush_run (S n) d s = if s_avail_out s =? 0 then (d, s, true) else pfl' n d s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition upG (f : nat) (d1 : dst) (s1 : dstrm) : Z * dst * dstrm :=
  let PP := sv_nblock (d_sv d1) + 1 in
  if d_nused d1 =? PP then (0, d1, s1)
  else if PP <? d_nused d1 then (1, d1, s1)
  else
    let d2 := d_set_out_ch (d_set_out_len d1 1) (d_k0 d1) in
    match get_sym d2 with
    | None => (1, d2, s1)
    | Some (k1, d3) =>
        let d3 := d_set_nused d3 (d_nused d3 + 1) in
        if d_nused d3 =? PP then unrle_plain f d3 s1
        else if negb (k1 =? d_k0 d3) then unrle_plain f (d_set_k0 d3 k1) s1
        else
          let d4 := d_set_out_len d3 2 in
          match get_sym d4 with
          | None => (1, d4, s1)
          | Some (k2, d5) =>
              let d5 := d_set_nused d5 (d_nused d5 + 1) in
              if d_nused d5 =? PP then unrle_plain f d5 s1
              else if negb (k2 =? d_k0 d5) then unrle_plain f (d_set_k0 d5 k2) s1
              else
                let d6 := d_set_out_len d5 3 in
                match get_sym d6 with
                | None => (1, d6, s1)
                | Some (k3, d7) =>
                    let d7 := d_set_nused d7 (d_nused d7 + 1) in
                    if d_nused d7 =? PP then unrle_plain f d7 s1
                    else if negb (k3 =? d_k0 d7) then unrle_plain f (d_set_k0 d7 k3) s1
                    else
                      match get_sym d7 with
                      | None => (1, d7, s1)
                      | Some (k4, d8) =>
                          let d8 := d_set_out_len (d_set_nused d8 (d_nused d8 + 1)) (k4 + 4) in
                          match get_sym d8 with
                          | None => (1, d8, s1)
                          | Some (k5, d9) => unrle_plain f (d_set_nused (d_set_k0 d9 k5) (d_nused d9 + 1)) s1
                          end
                      end
                end
          end
    end.

Definition pl_rest (f : nat) (r : dst * dstrm * bool) : Z * dst * dstrm :=
  let '(d1, s1, ret) := r in if ret then (0, d1, s1) else upG f d1 s1.

Lemma unrle_plain_S : forall f d s,
  unrle_plain (S f) d s = pl_rest f (flush_run (S (Z.to_nat (d_out_len d))) d s).
Proof.
  intros f d s. cbn [unrle_plain]. unfold pl_rest, upG.
  destruct (flush_run _ d s) as [[d1 s1] ret]. destruct ret; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_PM (f : nat) (d : dst) (s : dstrm) : Z * dst * dstrm := unrle_plain (S f) d s.
Definition K_PH (f : nat) (d : dst) (s : dstrm) : Z * dst * dstrm := pl_rest f (pfl' (Z.to_nat (d_out_len d)) d s).
Definition K_PG (f : nat) (d : dst) (s : dstrm) : Z * dst * dstrm := upG f d s.

(* [comment removed for export] *)

Lemma K_PM_eq : forall f d s, K_PM f d s = if s_avail_out s =? 0 then (0, d, s) else K_PH f d s.
Proof.
  intros f d s. unfold K_PM, K_PH. rewrite unrle_plain_S, flush_run_S.
  destruct (s_avail_out s =? 0); reflexivity.
Qed.
Lemma K_PM_ret : forall f d s, s_avail_out s = 0 -> K_PM f d s = (0, d, s).
Proof. intros f d s H. rewrite K_PM_eq, H. reflexivity. Qed.
Lemma K_PM_go : forall f d s, s_avail_out s <> 0 -> K_PM f d s = K_PH f d s.
Proof. intros f d s H. rewrite K_PM_eq. destruct (Z.eqb_spec (s_avail_out s) 0); [lia| reflexivity]. Qed.

Lemma K_PH_0 : forall f d s, d_out_len d = 0 -> K_PH f d s = K_PG f d s.
Proof. intros f d s H. unfold K_PH, pfl', K_PG. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_PH_step : forall f d s, 1 <= d_out_len d ->
  K_PH f d s = let d' := pwd d in let s' := pws d s in
               if s_avail_out s' =? 0 then (0, d', s') else K_PH f d' s'.
Proof.
  intros f d s H. unfold K_PH at 1. unfold pfl'.
  destruct (Z.eqb_spec (d_out_len d) 0); [lia|]. cbv zeta.
  assert (E : Z.to_nat (d_out_len d) = S (Z.to_nat (d_out_len (pwd d)))) by (unfold pwd; cbn [d_out_len d_set_out_len]; lia).
  rewrite E, flush_run_S. unfold K_PH, pl_rest. destruct (s_avail_out (pws d s) =? 0); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_sym_None : forall d, blk_cap d <= d_tPos d -> get_sym d = None.
Proof. intros d H. unfold get_sym. destruct (Z.leb_spec (blk_cap d) (d_tPos d)); [reflexivity| lia]. Qed.

(* [comment removed for export] *)
Definition gsF (d : dst) : Z * dst :=
  let w := zget (d_tt d) (d_tPos d) in
  let d2 := rand_upd (d_set_tPos d (w / 256)) in
  (Z.lxor (Z.land w 255) (rand_mask d2), d2).
Lemma get_sym_FR : forall d, d_tPos d < blk_cap d -> d_small d = 0 -> d_rand d <> 0 -> get_sym d = Some (gsF d).
Proof.
  intros d H1 H2 H3. unfold get_sym, smallb, gsF. destruct (Z.leb_spec (blk_cap d) (d_tPos d)); [lia|].
  rewrite H2. cbn [Z.eqb negb]. destruct (Z.eqb_spec (d_rand d) 0); [lia|]. rewrite shiftr8_div. reflexivity.
Qed.
(* [comment removed for export] *)
Definition gsSN (d : dst) : Z * dst :=
  (indexIntoF (d_tPos d) (d_cftab d), d_set_tPos d (get_ll d (d_tPos d))).
Lemma get_sym_SN : forall d, d_tPos d < blk_cap d -> d_small d <> 0 -> d_rand d = 0 -> get_sym d = Some (gsSN d).
Proof.
  intros d H1 H2 H3. unfold get_sym, smallb, gsSN. destruct (Z.leb_spec (blk_cap d) (d_tPos d)); [lia|].
  destruct (Z.eqb_spec (d_small d) 0); [lia|]. cbn [negb]. rewrite H3. reflexivity.
Qed.
(* [comment removed for export] *)
Definition gsSR (d : dst) : Z * dst :=
  let d2 := rand_upd (d_set_tPos d (get_ll d (d_tPos d))) in
  (Z.lxor (indexIntoF (d_tPos d) (d_cftab d)) (rand_mask d2), d2).
Lemma get_sym_SR : forall d, d_tPos d < blk_cap d -> d_small d <> 0 -> d_rand d <> 0 -> get_sym d = Some (gsSR d).
Proof.
  intros d H1 H2 H3. unfold get_sym, smallb, gsSR. destruct (Z.leb_spec (blk_cap d) (d_tPos d)); [lia|].
  destruct (Z.eqb_spec (d_small d) 0); [lia|]. cbn [negb]. destruct (Z.eqb_spec (d_rand d) 0); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rand_upd_nz : forall d, d_rNToGo d <> 0 -> rand_upd d = d_set_rNToGo d (d_rNToGo d - 1).
Proof. intros d H. unfold rand_upd. destruct (Z.eqb_spec (d_rNToGo d) 0); [lia| reflexivity]. Qed.
Lemma rand_upd_z : forall d, d_rNToGo d = 0 ->
  rand_upd d = d_set_rNToGo (d_set_rTPos (d_set_rNToGo d (rNums (d_rTPos d))) (if d_rTPos d + 1 =? 512 then 0 else d_rTPos d + 1))
                          (rNums (d_rTPos d) - 1).
Proof. intros d H. unfold rand_upd. rewrite H. reflexivity. Qed.

Lemma rNums_range : forall i, 0 <= i < 512 -> 50 <= rNums i <= 999.
Proof.
  intros i Hi. unfold rNums.
  assert (FA : forallb (fun v => (50 <=? v) && (v <=? 999)) rNums_list = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in FA.
  assert (L : length rNums_list = 512%nat) by reflexivity.
  assert (IN : In (nth (Z.to_nat i) rNums_list 0) rNums_list) by (apply nth_In; rewrite L; lia).
  specialize (FA _ IN). apply andb_prop in FA. destruct FA as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stages.
  (* [comment removed for export] *)
  Definition PG5 (f : nat) (d8 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    match get_sym d8 with
    | None => (1, d8, s1)
    | Some (k5, d9) => unrle_plain f (d_set_nused (d_set_k0 d9 k5) (d_nused d9 + 1)) s1
    end.
  Definition PG4 (f : nat) (d7 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    match get_sym d7 with
    | None => (1, d7, s1)
    | Some (k4, d8) => PG5 f (d_set_out_len (d_set_nused d8 (d_nused d8 + 1)) (k4 + 4)) s1
    end.
  Definition PG3 (f : nat) (PP : Z) (d6 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    match get_sym d6 with
    | None => (1, d6, s1)
    | Some (k3, d7) =>
        let d7 := d_set_nused d7 (d_nused d7 + 1) in
        if d_nused d7 =? PP then unrle_plain f d7 s1
        else if negb (k3 =? d_k0 d7) then unrle_plain f (d_set_k0 d7 k3) s1
        else PG4 f d7 s1
    end.
  Definition PG2 (f : nat) (PP : Z) (d4 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    match get_sym d4 with
    | None => (1, d4, s1)
    | Some (k2, d5) =>
        let d5 := d_set_nused d5 (d_nused d5 + 1) in
        if d_nused d5 =? PP then unrle_plain f d5 s1
        else if negb (k2 =? d_k0 d5) then unrle_plain f (d_set_k0 d5 k2) s1
        else PG3 f PP (d_set_out_len d5 3) s1
    end.
  Definition PG1 (f : nat) (PP : Z) (d2 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    match get_sym d2 with
    | None => (1, d2, s1)
    | Some (k1, d3) =>
        let d3 := d_set_nused d3 (d_nused d3 + 1) in
        if d_nused d3 =? PP then unrle_plain f d3 s1
        else if negb (k1 =? d_k0 d3) then unrle_plain f (d_set_k0 d3 k1) s1
        else PG2 f PP (d_set_out_len d3 2) s1
    end.

  (* [comment removed for export] *)
  Definition PG1b (f : nat) (PP : Z) (k1 : Z) (d3 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    let d3 := d_set_nused d3 (d_nused d3 + 1) in
    if d_nused d3 =? PP then unrle_plain f d3 s1
    else if negb (k1 =? d_k0 d3) then unrle_plain f (d_set_k0 d3 k1) s1
    else PG2 f PP (d_set_out_len d3 2) s1.
  Definition PG2b (f : nat) (PP : Z) (k2 : Z) (d5 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    let d5 := d_set_nused d5 (d_nused d5 + 1) in
    if d_nused d5 =? PP then unrle_plain f d5 s1
    else if negb (k2 =? d_k0 d5) then unrle_plain f (d_set_k0 d5 k2) s1
    else PG3 f PP (d_set_out_len d5 3) s1.
  Definition PG3b (f : nat) (PP : Z) (k3 : Z) (d7 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    let d7 := d_set_nused d7 (d_nused d7 + 1) in
    if d_nused d7 =? PP then unrle_plain f d7 s1
    else if negb (k3 =? d_k0 d7) then unrle_plain f (d_set_k0 d7 k3) s1
    else PG4 f d7 s1.
  Definition PG4b (f : nat) (k4 : Z) (d8 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    PG5 f (d_set_out_len (d_set_nused d8 (d_nused d8 + 1)) (k4 + 4)) s1.
  Definition PG5b (f : nat) (k5 : Z) (d9 : dst) (s1 : dstrm) : Z * dst * dstrm :=
    unrle_plain f (d_set_nused (d_set_k0 d9 k5) (d_nused d9 + 1)) s1.
  Lemma PG1_b : forall f PP d s k1 d3, get_sym d = Some (k1, d3) -> PG1 f PP d s = PG1b f PP k1 d3 s.
  Proof. intros f PP d s k1 d3 H. unfold PG1. rewrite H. reflexivity. Qed.
  Lemma PG2_b : forall f PP d s k2 d5, get_sym d = Some (k2, d5) -> PG2 f PP d s = PG2b f PP k2 d5 s.
  Proof. intros f PP d s k2 d5 H. unfold PG2. rewrite H. reflexivity. Qed.
  Lemma PG3_b : forall f PP d s k3 d7, get_sym d = Some (k3, d7) -> PG3 f PP d s = PG3b f PP k3 d7 s.
  Proof. intros f PP d s k3 d7 H. unfold PG3. rewrite H. reflexivity. Qed.
  Lemma PG4_b : forall f d s k4 d8, get_sym d = Some (k4, d8) -> PG4 f d s = PG4b f k4 d8 s.
  Proof. intros f d s k4 d8 H. unfold PG4. rewrite H. reflexivity. Qed.
  Lemma PG5_b : forall f d s k5 d9, get_sym d = Some (k5, d9) -> PG5 f d s = PG5b f k5 d9 s.
  Proof. intros f d s k5 d9 H. unfold PG5. rewrite H. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma PG1b_eq : forall f PP k1 d3 s, PG1b (S f) PP k1 d3 s =
    let d3' := d_set_nused d3 (d_nused d3 + 1) in
    if d_nused d3' =? PP then K_PM f d3' s
    else if negb (k1 =? d_k0 d3') then K_PM f (d_set_k0 d3' k1) s else PG2 (S f) PP (d_set_out_len d3' 2) s.
  Proof. reflexivity. Qed.
  Lemma PG2b_eq : forall f PP k2 d5 s, PG2b (S f) PP k2 d5 s =
    let d5' := d_set_nused d5 (d_nused d5 + 1) in
    if d_nused d5' =? PP then K_PM f d5' s
    else if negb (k2 =? d_k0 d5') then K_PM f (d_set_k0 d5' k2) s else PG3 (S f) PP (d_set_out_len d5' 3) s.
  Proof. reflexivity. Qed.
  Lemma PG3b_eq : forall f PP k3 d7 s, PG3b (S f) PP k3 d7 s =
    let d7' := d_set_nused d7 (d_nused d7 + 1) in
    if d_nused d7' =? PP then K_PM f d7' s
    else if negb (k3 =? d_k0 d7') then K_PM f (d_set_k0 d7' k3) s else PG4 (S f) d7' s.
  Proof. reflexivity. Qed.
  Lemma PG5b_eq : forall f k5 d9 s, PG5b (S f) k5 d9 s = K_PM f (d_set_nused (d_set_k0 d9 k5) (d_nused d9 + 1)) s.
  Proof. reflexivity. Qed.

  Lemma K_PG_over : forall f d s, sv_nblock (d_sv d) + 1 < d_nused d -> K_PG f d s = (1, d, s).
  Proof.
    intros f d s H. unfold K_PG, upG. destruct (Z.eqb_spec (d_nused d) (sv_nblock (d_sv d) + 1)); [lia|].
    destruct (Z.ltb_spec (sv_nblock (d_sv d) + 1) (d_nused d)); [reflexivity| lia].
  Qed.
  Lemma K_PG_done : forall f d s, d_nused d = sv_nblock (d_sv d) + 1 -> K_PG f d s = (0, d, s).
  Proof. intros f d s H. unfold K_PG, upG. rewrite H, Z.eqb_refl. reflexivity. Qed.
  Lemma K_PG_go : forall f d s, d_nused d < sv_nblock (d_sv d) + 1 ->
    K_PG f d s = PG1 f (sv_nblock (d_sv d) + 1) (d_set_out_ch (d_set_out_len d 1) (d_k0 d)) s.
  Proof.
    intros f d s H. unfold K_PG, upG. destruct (Z.eqb_spec (d_nused d) (sv_nblock (d_sv d) + 1)); [lia|].
    destruct (Z.ltb_spec (sv_nblock (d_sv d) + 1) (d_nused d)); [lia|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma PG1_None : forall f PP d s, get_sym d = None -> PG1 f PP d s = (1, d, s).
  Proof. intros f PP d s H. unfold PG1. rewrite H. reflexivity. Qed.
  Lemma PG1_Some : forall f PP d s k1 d3, get_sym d = Some (k1, d3) ->
    PG1 (S f) PP d s = let d3 := d_set_nused d3 (d_nused d3 + 1) in
                       if d_nused d3 =? PP then K_PM f d3 s
                       else if negb (k1 =? d_k0 d3) then K_PM f (d_set_k0 d3 k1) s
                       else PG2 (S f) PP (d_set_out_len d3 2) s.
  Proof. intros f PP d s k1 d3 H. unfold PG1. rewrite H. reflexivity. Qed.
  Lemma PG2_None : forall f PP d s, get_sym d = None -> PG2 f PP d s = (1, d, s).
  Proof. intros f PP d s H. unfold PG2. rewrite H. reflexivity. Qed.
  Lemma PG2_Some : forall f PP d s k2 d5, get_sym d = Some (k2, d5) ->
    PG2 (S f) PP d s = let d5 := d_set_nused d5 (d_nused d5 + 1) in
                       if d_nused d5 =? PP then K_PM f d5 s
                       else if negb (k2 =? d_k0 d5) then K_PM f (d_set_k0 d5 k2) s
                       else PG3 (S f) PP (d_set_out_len d5 3) s.
  Proof. intros f PP d s k2 d5 H. unfold PG2. rewrite H. reflexivity. Qed.
  Lemma PG3_None : forall f PP d s, get_sym d = None -> PG3 f PP d s = (1, d, s).
  Proof. intros f PP d s H. unfold PG3. rewrite H. reflexivity. Qed.
  Lemma PG3_Some : forall f PP d s k3 d7, get_sym d = Some (k3, d7) ->
    PG3 (S f) PP d s = let d7 := d_set_nused d7 (d_nused d7 + 1) in
                       if d_nused d7 =? PP then K_PM f d7 s
                       else if negb (k3 =? d_k0 d7) then K_PM f (d_set_k0 d7 k3) s
                       else PG4 (S f) d7 s.
  Proof. intros f PP d s k3 d7 H. unfold PG3. rewrite H. reflexivity. Qed.
  Lemma PG4_None : forall f d s, get_sym d = None -> PG4 f d s = (1, d, s).
  Proof. intros f d s H. unfold PG4. rewrite H. reflexivity. Qed.
  Lemma PG4_Some : forall f d s k4 d8, get_sym d = Some (k4, d8) ->
    PG4 f d s = PG5 f (d_set_out_len (d_set_nused d8 (d_nused d8 + 1)) (k4 + 4)) s.
  Proof. intros f d s k4 d8 H. unfold PG4. rewrite H. reflexivity. Qed.
  Lemma PG5_None : forall f d s, get_sym d = None -> PG5 f d s = (1, d, s).
  Proof. intros f d s H. unfold PG5. rewrite H. reflexivity. Qed.
  Lemma PG5_Some : forall f d s k5 d9, get_sym d = Some (k5, d9) ->
    PG5 (S f) d s = K_PM f (d_set_nused (d_set_k0 d9 k5) (d_nused d9 + 1)) s.
  Proof. intros f d s k5 d9 H. unfold PG5. rewrite H. reflexivity. Qed.
End Stages.

(* [comment removed for export] *)
Lemma unRLE_plain : forall d s f,
  smallb d || negb (d_rand d =? 0) = true ->
  Z.to_nat (sv_nblock (d_sv d) + 1 + 3 - d_nused d) = S f ->
  unRLE d s = K_PM f d s.
Proof. intros d s f H F. unfold unRLE. rewrite H, F. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dout_okW (d : dst) : Prop :=
  d_out_len d = 0 /\
  0 <= d_tPos d < 4294967296 /\
  ((d_nused d = 1 /\ 0 <= d_k0 d < 256) \/ (d_nused d = 0 /\ 100000 * d_bs100k d <= d_tPos d)) /\
  1 <= sv_nblock (d_sv d) /\
  d_cbcrc d = 4294967295 /\
  0 <= d_sbcrc d < 4294967296 /\
  (d_rand d = 0 \/ d_rand d = 1) /\
  (d_rand d = 1 -> 0 <= d_rNToGo d < 2147483648 /\ 0 <= d_rTPos d < 512) /\
  (d_small d <> 0 -> forall i, 0 <= i < 257 -> 0 <= zget (d_cftab d) i <= sv_nblock (d_sv d)) /\
  d_out_ch d = 0 /\
  1 <= d_bs100k d <= 9.
(* [comment removed for export] *)
Definition dpost14W (R : Z * dst * dstrm) : Prop :=
  let '(rv, d', s') := R in
  (d_state d' = BZ_X_OUTPUT -> dout_okW d') /\ (rv = BZ_STREAM_END -> 0 <= d_sccrc d' < 4294967296) /\ (-5 <= rv <= 4).
