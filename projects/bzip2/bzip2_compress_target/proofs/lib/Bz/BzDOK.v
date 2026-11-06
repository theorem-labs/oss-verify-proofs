(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzLemmasMtf BzCLemmas1 BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Creg.
  Variables (tt : zarr) (cap PP : Z).

  (* [comment removed for export] *)
  Definition ucG (f : nat) (c1 : cloc) : Z * cloc :=
      if PP <? c_nused c1 then (1, c1)
      else if c_nused c1 =? PP then (0, c_set_len c1 0)
      else
        let c2 := c_set_ch c1 (c_k0 c1) in
        match c_get tt cap c2 with
        | None => (1, c2)
        | Some (k1, c3) =>
            let c3 := c_inc c3 in
            if negb (k1 =? c_k0 c3) then unrle_creg f true tt cap PP (c_set_k0 c3 k1)
            else if c_nused c3 =? PP then unrle_creg f true tt cap PP c3
            else
              let c4 := c_set_len c3 2 in
              match c_get tt cap c4 with
              | None => (1, c4)
              | Some (k2, c5) =>
                  let c5 := c_inc c5 in
                  if c_nused c5 =? PP then unrle_creg f false tt cap PP c5
                  else if negb (k2 =? c_k0 c5) then unrle_creg f false tt cap PP (c_set_k0 c5 k2)
                  else
                    let c6 := c_set_len c5 3 in
                    match c_get tt cap c6 with
                    | None => (1, c6)
                    | Some (k3, c7) =>
                        let c7 := c_inc c7 in
                        if c_nused c7 =? PP then unrle_creg f false tt cap PP c7
                        else if negb (k3 =? c_k0 c7) then unrle_creg f false tt cap PP (c_set_k0 c7 k3)
                        else
                          match c_get tt cap c7 with
                          | None => (1, c7)
                          | Some (k4, c8) =>
                              let c8 := c_set_len (c_inc c8) (k4 + 4) in
                              match c_get tt cap c8 with
                              | None => (1, c8)
                              | Some (k5, c9) => unrle_creg f false tt cap PP (c_inc (c_set_k0 c9 k5))
                              end
                          end
                    end
              end
        end.

  Definition K_H1 (f : nat) (c : cloc) : Z * cloc := unrle_creg (S f) false tt cap PP c.
  Definition K_H2 (f : nat) (c : cloc) : Z * cloc := unrle_creg (S f) true tt cap PP c.

  (* [comment removed for export] *)
  Definition cfl' (n : nat) (c : cloc) : cloc * bool :=
    if c_len c =? 1 then (c, false) else c_flush n (c_set_len (c_write c) (c_len c - 1)).
  (* [comment removed for export] *)
  Definition ph1_rest (f : nat) (cr : cloc * bool) : Z * cloc :=
    let '(c', r) := cr in
    if r then (0, c') else if c_avail c' =? 0 then (0, c_set_len c' 1) else ucG f (c_write c').
  Definition K_DR (f : nat) (c : cloc) : Z * cloc := ph1_rest f (cfl' (Z.to_nat (c_len c)) c).

  Lemma c_flush_S : forall n c, c_flush (S n) c = if c_avail c =? 0 then (c, true) else cfl' n c.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma K_H2_eq : forall f c, K_H2 f c = if c_avail c =? 0 then (0, c_set_len c 1) else ucG f (c_write c).
  Proof. intros f c. unfold K_H2. cbn [unrle_creg]. destruct (c_avail c =? 0); reflexivity. Qed.

  Lemma K_H1_eq : forall f c,
    K_H1 f c = if 0 <? c_len c then (if c_avail c =? 0 then (0, c) else K_DR f c) else ucG f c.
  Proof.
    intros f c. unfold K_H1, K_DR, ph1_rest. cbn [unrle_creg]. rewrite c_flush_S.
    destruct (0 <? c_len c); [| reflexivity]. destruct (c_avail c =? 0); [reflexivity|].
    destruct (cfl' (Z.to_nat (c_len c)) c) as [c' r]. destruct r; [reflexivity|]. destruct (c_avail c' =? 0); reflexivity.
  Qed.

  Lemma K_H2_go : forall f c, c_avail c <> 0 -> K_H2 f c = ucG f (c_write c).
  Proof. intros f c H. rewrite K_H2_eq. destruct (Z.eqb_spec (c_avail c) 0); [lia| reflexivity]. Qed.
  (* [comment removed for export] *)
  Lemma K_DR_one : forall f c, c_len c = 1 -> c_avail c <> 0 -> K_DR f c = ucG f (c_write c).
  Proof.
    intros f c H1 H2. unfold K_DR, cfl', ph1_rest. rewrite H1. cbn [Z.eqb Pos.eqb].
    destruct (Z.eqb_spec (c_avail c) 0); [lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma K_DR_step : forall f c, 1 < c_len c ->
    K_DR f c = let c2 := c_set_len (c_write c) (c_len c - 1) in
               if c_avail c2 =? 0 then (0, c2) else K_DR f c2.
  Proof.
    intros f c H. unfold K_DR at 1. unfold cfl' at 1.
    destruct (Z.eqb_spec (c_len c) 1); [lia|]. cbv zeta.
    set (c2 := c_set_len (c_write c) (c_len c - 1)).
    assert (E : Z.to_nat (c_len c) = S (Z.to_nat (c_len c2))) by (subst c2; cbn [c_len c_set_len]; lia).
    rewrite E, c_flush_S. unfold K_DR, ph1_rest. destruct (c_avail c2 =? 0); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma c_get_None : forall c, cap <= c_tPos c -> c_get tt cap c = None.
  Proof. intros c H. unfold c_get. destruct (Z.leb_spec cap (c_tPos c)); [reflexivity| lia]. Qed.
  Lemma c_get_Some : forall c, c_tPos c < cap ->
    c_get tt cap c = Some (Z.land (zget tt (c_tPos c)) 255,
                           CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c) (c_k0 c) (Z.shiftr (zget tt (c_tPos c)) 8) (c_out c) (c_avail c)).
  Proof. intros c H. unfold c_get. destruct (Z.leb_spec cap (c_tPos c)); [lia| reflexivity]. Qed.
  (* [comment removed for export] *)
  Definition G5 (f : nat) (c8 : cloc) : Z * cloc :=
    match c_get tt cap c8 with
    | None => (1, c8)
    | Some (k5, c9) => unrle_creg f false tt cap PP (c_inc (c_set_k0 c9 k5))
    end.
  Definition G4 (f : nat) (c7 : cloc) : Z * cloc :=
    match c_get tt cap c7 with
    | None => (1, c7)
    | Some (k4, c8) => G5 f (c_set_len (c_inc c8) (k4 + 4))
    end.
  Definition G3 (f : nat) (c6 : cloc) : Z * cloc :=
    match c_get tt cap c6 with
    | None => (1, c6)
    | Some (k3, c7) =>
        let c7 := c_inc c7 in
        if c_nused c7 =? PP then unrle_creg f false tt cap PP c7
        else if negb (k3 =? c_k0 c7) then unrle_creg f false tt cap PP (c_set_k0 c7 k3)
        else G4 f c7
    end.
  Definition G2 (f : nat) (c4 : cloc) : Z * cloc :=
    match c_get tt cap c4 with
    | None => (1, c4)
    | Some (k2, c5) =>
        let c5 := c_inc c5 in
        if c_nused c5 =? PP then unrle_creg f false tt cap PP c5
        else if negb (k2 =? c_k0 c5) then unrle_creg f false tt cap PP (c_set_k0 c5 k2)
        else G3 f (c_set_len c5 3)
    end.
  Definition G1 (f : nat) (c2 : cloc) : Z * cloc :=
    match c_get tt cap c2 with
    | None => (1, c2)
    | Some (k1, c3) =>
        let c3 := c_inc c3 in
        if negb (k1 =? c_k0 c3) then unrle_creg f true tt cap PP (c_set_k0 c3 k1)
        else if c_nused c3 =? PP then unrle_creg f true tt cap PP c3
        else G2 f (c_set_len c3 2)
    end.

  Lemma ucG_over : forall f c1, PP < c_nused c1 -> ucG f c1 = (1, c1).
  Proof. intros f c1 H. unfold ucG. destruct (Z.ltb_spec PP (c_nused c1)); [reflexivity| lia]. Qed.
  Lemma ucG_done : forall f c1, c_nused c1 = PP -> ucG f c1 = (0, c_set_len c1 0).
  Proof. intros f c1 H. unfold ucG. destruct (Z.ltb_spec PP (c_nused c1)); [lia|]. rewrite H, Z.eqb_refl. reflexivity. Qed.
  Lemma ucG_go : forall f c1, c_nused c1 < PP -> ucG f c1 = G1 f (c_set_ch c1 (c_k0 c1)).
  Proof.
    intros f c1 H. unfold ucG. destruct (Z.ltb_spec PP (c_nused c1)); [lia|].
    destruct (Z.eqb_spec (c_nused c1) PP); [lia|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition ttw (c : cloc) : Z := zget tt (c_tPos c).
  Definition cget (c : cloc) : cloc :=
    CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c + 1) (c_k0 c) (ttw c / 256) (c_out c) (c_avail c).
  Lemma shiftr8_div : forall w, Z.shiftr w 8 = w / 256.
  Proof. intros w. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.


  Lemma G1_None : forall f c2, cap <= c_tPos c2 -> G1 f c2 = (1, c2).
  Proof. intros f c2 H. unfold G1. rewrite c_get_None by exact H. reflexivity. Qed.
  Lemma G1_Some : forall f c2, c_tPos c2 < cap ->
    G1 (S f) c2 = let k1 := Z.land (ttw c2) 255 in let c3 := cget c2 in
                  if negb (k1 =? c_k0 c3) then K_H2 f (c_set_k0 c3 k1)
                  else if c_nused c3 =? PP then K_H2 f c3 else G2 (S f) (c_set_len c3 2).
  Proof. intros f c2 H. unfold G1. rewrite c_get_Some by exact H. unfold cget, ttw. rewrite <- shiftr8_div. reflexivity. Qed.
  Lemma G2_None : forall f c4, cap <= c_tPos c4 -> G2 f c4 = (1, c4).
  Proof. intros f c4 H. unfold G2. rewrite c_get_None by exact H. reflexivity. Qed.
  Lemma G2_Some : forall f c4, c_tPos c4 < cap ->
    G2 (S f) c4 = let k2 := Z.land (ttw c4) 255 in let c5 := cget c4 in
                  if c_nused c5 =? PP then K_H1 f c5
                  else if negb (k2 =? c_k0 c5) then K_H1 f (c_set_k0 c5 k2) else G3 (S f) (c_set_len c5 3).
  Proof. intros f c4 H. unfold G2. rewrite c_get_Some by exact H. unfold cget, ttw. rewrite <- shiftr8_div. reflexivity. Qed.
  Lemma G3_None : forall f c6, cap <= c_tPos c6 -> G3 f c6 = (1, c6).
  Proof. intros f c6 H. unfold G3. rewrite c_get_None by exact H. reflexivity. Qed.
  Lemma G3_Some : forall f c6, c_tPos c6 < cap ->
    G3 (S f) c6 = let k3 := Z.land (ttw c6) 255 in let c7 := cget c6 in
                  if c_nused c7 =? PP then K_H1 f c7
                  else if negb (k3 =? c_k0 c7) then K_H1 f (c_set_k0 c7 k3) else G4 (S f) c7.
  Proof. intros f c6 H. unfold G3. rewrite c_get_Some by exact H. unfold cget, ttw. rewrite <- shiftr8_div. reflexivity. Qed.
  Lemma G4_None : forall f c7, cap <= c_tPos c7 -> G4 f c7 = (1, c7).
  Proof. intros f c7 H. unfold G4. rewrite c_get_None by exact H. reflexivity. Qed.
  Lemma G4_Some : forall f c7, c_tPos c7 < cap ->
    G4 f c7 = G5 f (c_set_len (cget c7) (Z.land (ttw c7) 255 + 4)).
  Proof. intros f c7 H. unfold G4. rewrite c_get_Some by exact H. unfold cget, ttw. rewrite <- shiftr8_div. reflexivity. Qed.
  Lemma G5_None : forall f c8, cap <= c_tPos c8 -> G5 f c8 = (1, c8).
  Proof. intros f c8 H. unfold G5. rewrite c_get_None by exact H. reflexivity. Qed.
  Lemma G5_Some : forall f c8, c_tPos c8 < cap ->
    G5 (S f) c8 = K_H1 f (c_set_k0 (cget c8) (Z.land (ttw c8) 255)).
  Proof. intros f c8 H. unfold G5. rewrite c_get_Some by exact H. unfold cget, ttw. rewrite <- shiftr8_div. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

End Creg.

(* [comment removed for export] *)
Definition c0_of (d : dst) (s : dstrm) : cloc :=
  CLOC (d_cbcrc d) (d_out_ch d) (d_out_len d) (d_nused d) (d_k0 d) (d_tPos d) [] (s_avail_out s).
Definition dcommit (d : dst) (c : cloc) : dst :=
  d_set_tPos (d_set_k0 (d_set_nused (d_set_out_len (d_set_out_ch (d_set_cbcrc d (c_crc c)) (c_ch c)) (c_len c))
            (c_nused c)) (c_k0 c)) (c_tPos c).
Definition scommit (s : dstrm) (c : cloc) : dstrm :=
  DSTRM (s_in s) (c_out c ++ s_out s) (c_avail c) (s_tin s) (s_tout s + (s_avail_out s - c_avail c)).
Definition ccommit (d : dst) (s : dstrm) (rc : Z * cloc) : Z * dst * dstrm :=
  let '(r, c) := rc in if r =? 0 then (0, dcommit d c, scommit s c) else (1, d, s).

Lemma unRLE_creg : forall d s f,
  smallb d = false -> d_rand d = 0 ->
  Z.to_nat (sv_nblock (d_sv d) + 1 + 3 - d_nused d) = S f ->
  unRLE d s = ccommit d s (K_H1 (d_tt d) (blk_cap d) (sv_nblock (d_sv d) + 1) f (c0_of d s)).
Proof.
  intros d s f SM RD F. unfold unRLE. rewrite SM, RD. cbn [orb negb Z.eqb]. rewrite F.
  unfold K_H1, c0_of, ccommit. destruct (unrle_creg _ _ _ _ _ _) as [r c]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cinv (PP av0 : Z) (c : cloc) : Prop :=
  0 <= c_crc c < 4294967296 /\ 0 <= c_ch c < 256 /\ 0 <= c_len c <= 260 /\
  0 <= c_nused c <= PP + 1 /\ 0 <= c_k0 c < 256 /\ 0 <= c_tPos c < 4294967296 /\
  0 <= c_avail c <= av0 /\ Z.of_nat (length (c_out c)) = av0 - c_avail c.

Lemma land255_byte : forall x, 0 <= Z.land x 255 < 256.
Proof. intros x. rewrite Z.land_comm. change 255 with (Z.ones 8). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_L (f : nat) (R : Z * dst * dstrm) : Z * dst * dstrm :=
  let '(r, d2, s2) := R in
  if r =? BZ_STREAM_END then (if d_cccrc d2 =? d_sccrc d2 then (r, d2, s2) else (BZ_DATA_ERROR, d2, s2))
  else if negb (d_state d2 =? BZ_X_OUTPUT) then (r, d2, s2)
  else bzd_loop f d2 s2.
(* [comment removed for export] *)
Definition K_call (f : nat) (d : dst) (s : dstrm) : Z * dst * dstrm :=
  K_L f (decompress d s).
(* [comment removed for export] *)
Definition K_J (f : nat) (d' : dst) (s' : dstrm) : Z * dst * dstrm :=
  if (d_nused d' =? sv_nblock (d_sv d') + 1) && (d_out_len d' =? 0) then
    let crc := crc_final (d_cbcrc d') in
    let d'' := d_set_cbcrc d' crc in
    if negb (crc =? d_sbcrc d'') then (BZ_DATA_ERROR, d'', s')
    else
      let cc := Z.lxor (Z.lor (Z.shiftl (d_cccrc d'') 1) (Z.shiftr (d_cccrc d'') 31) mod 4294967296) crc in
      K_call f (d_set_state (d_set_cccrc d'' cc) BZ_X_BLKHDR_1) s'
  else (BZ_OK, d', s').
(* [comment removed for export] *)
Definition K_U (f : nat) (R : Z * dst * dstrm) : Z * dst * dstrm :=
  let '(corrupt, d', s') := R in if corrupt =? 1 then (BZ_DATA_ERROR, d', s') else K_J f d' s'.

Lemma bzd_loop_S : forall f d s, bzd_loop (S f) d s =
  if d_state d =? BZ_X_IDLE then (BZ_SEQUENCE_ERROR, d, s)
  else
    let '(ret, d1, s1) :=
      if d_state d =? BZ_X_OUTPUT then
        let '(corrupt, d', s') := unRLE d s in
        if corrupt =? 1 then (Some BZ_DATA_ERROR, d', s')
        else if (d_nused d' =? sv_nblock (d_sv d') + 1) && (d_out_len d' =? 0) then
          let crc := crc_final (d_cbcrc d') in
          let d'' := d_set_cbcrc d' crc in
          if negb (crc =? d_sbcrc d'') then (Some BZ_DATA_ERROR, d'', s')
          else
            let cc := Z.lxor (Z.lor (Z.shiftl (d_cccrc d'') 1) (Z.shiftr (d_cccrc d'') 31) mod 4294967296) crc in
            (None, d_set_state (d_set_cccrc d'' cc) BZ_X_BLKHDR_1, s')
        else (Some BZ_OK, d', s')
      else (None, d, s) in
    match ret with
    | Some r => (r, d1, s1)
    | None => if BZ_X_MAGIC_1 <=? d_state d1 then K_L f (decompress d1 s1) else bzd_loop f d1 s1
    end.
Proof. intros f d s. unfold K_L. cbn [bzd_loop]. reflexivity. Qed.

Lemma bzd_loop_out : forall f d s, d_state d = BZ_X_OUTPUT -> bzd_loop (S f) d s = K_U f (unRLE d s).
Proof.
  intros f d s Hst. rewrite bzd_loop_S. rewrite !Hst.
  replace (BZ_X_OUTPUT =? BZ_X_IDLE) with false by reflexivity. replace (BZ_X_OUTPUT =? BZ_X_OUTPUT) with true by reflexivity.
  unfold K_U, K_J, K_call.
  destruct (unRLE d s) as [[c d'] s']. destruct (c =? 1); [reflexivity|].
  destruct ((d_nused d' =? sv_nblock (d_sv d') + 1) && (d_out_len d' =? 0)); [| reflexivity].
  cbv zeta. destruct (negb (crc_final (d_cbcrc d') =? d_sbcrc (d_set_cbcrc d' (crc_final (d_cbcrc d'))))); [reflexivity|].
  cbn [d_state d_set_state]. replace (BZ_X_MAGIC_1 <=? BZ_X_BLKHDR_1) with true by reflexivity. reflexivity.
Qed.

Lemma bzd_loop_10 : forall f d s, d_state d = BZ_X_MAGIC_1 -> bzd_loop (S f) d s = K_call f d s.
Proof.
  intros f d s Hst. rewrite bzd_loop_S. rewrite !Hst.
  replace (BZ_X_MAGIC_1 =? BZ_X_IDLE) with false by reflexivity. replace (BZ_X_MAGIC_1 =? BZ_X_OUTPUT) with false by reflexivity.
  cbv beta iota zeta. rewrite Hst. replace (BZ_X_MAGIC_1 <=? BZ_X_MAGIC_1) with true by reflexivity. reflexivity.
Qed.
(* [comment removed for export] *)

Lemma bzDecompress_eq : forall d s, bzDecompress d s = bzd_loop (S (S (length (s_in s)))) d s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_L_end : forall f d2 s2, K_L f (BZ_STREAM_END, d2, s2) =
  (if d_cccrc d2 =? d_sccrc d2 then (BZ_STREAM_END, d2, s2) else (BZ_DATA_ERROR, d2, s2)).
Proof. reflexivity. Qed.
Lemma K_L_ret : forall f r d2 s2, r <> BZ_STREAM_END -> d_state d2 <> BZ_X_OUTPUT -> K_L f (r, d2, s2) = (r, d2, s2).
Proof.
  intros f r d2 s2 H1 H2. unfold K_L. destruct (Z.eqb_spec r BZ_STREAM_END); [lia|].
  destruct (Z.eqb_spec (d_state d2) BZ_X_OUTPUT); [lia| reflexivity].
Qed.
Lemma K_L_go : forall f r d2 s2, r <> BZ_STREAM_END -> d_state d2 = BZ_X_OUTPUT -> K_L (S f) (r, d2, s2) = K_U f (unRLE d2 s2).
Proof.
  intros f r d2 s2 H1 H2. unfold K_L. destruct (Z.eqb_spec r BZ_STREAM_END); [lia|].
  rewrite H2. cbn [Z.eqb Pos.eqb BZ_X_OUTPUT negb]. apply bzd_loop_out. exact H2.
Qed.
