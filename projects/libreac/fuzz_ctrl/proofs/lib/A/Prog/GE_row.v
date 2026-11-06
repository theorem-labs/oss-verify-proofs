(* fuzz_ctrl image A, ctrl_emit_as (0x849d8): the row facts of the cgif-form glue of a Theorem Labs lane.

   The glue instantiates A/Prog/ctrl_emit_asF2.v `Section Emit` with row := CROW r (A/Prog/C_ctrl_emit_as.v), for
   the rows 3 <= r <= 9 that the statement's call cases take. CROW r is the 24 bytes cd ea r 0^17 c L G A, with the
   gate bytes c = EM_C r, L = EM_L r, G = EM_G r, A = EM_A r. This file proves every fact about the VALUE of `row`
   that the Section takes:
     - the length (Hrl) and the kind byte ly_k = r (Hk, NM);
     - ly_k <> 2, which makes every KB = 2 hypothesis vacuous (Dst, Htm, Atm, RTM, RTMS, FPtm);
     - the gate bytes row[18..23] and their bounds (Hc, HL, HG, HA), the vacuous Hc2 and HLA;
     - ly_ao = ly_al = 0 (Hao, and every `ly_al row <> 0 ->` hypothesis vacuous);
     - the two magic bytes row[0] = 0xcd and row[1] = 0xea that the run's result bytes name;
   and it rewrites the Section's derived values (EE, LEN, LB, BLK, NM) at row := CROW r, g := 0 to the forms the
   statement's post `tctrl_emit_as_post` names.

   The import block is A/Prog/GEbase.v's. Glue closure rule (two Theorem Labs lanes, 2026-10-28 23:38Z): ctrl's
   address-free model files are Required qualified, so their names are written with their module. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

(* The seven rows, one goal each. *)
Local Ltac row_cases r :=
  let E := fresh "E" in
  assert (E : r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9) by lia;
  destruct E as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].

(* ---- the shape, the kind byte and the fixed bytes ---------------------------------------------------- *)

(* [Hrl] *)
Lemma ge_row_len : forall r, length (CROW r) = 24%nat.
Proof. intros r. reflexivity. Qed.

(* The kind byte row[2] is r.  [Hk, NM] *)
Lemma ge_row_k : forall r, 3 <= r <= 9 -> RcLay.ly_k (CROW r) = r.
Proof. intros r Hr. row_cases r; reflexivity. Qed.

(* [Hk] *)
Lemma ge_row_k9 : forall r, 3 <= r <= 9 -> RcLay.ly_k (CROW r) <= 9.
Proof. intros r Hr. rewrite (ge_row_k r Hr). lia. Qed.

Lemma ge_row_k39 : forall r, 3 <= r <= 9 -> 3 <= RcLay.ly_k (CROW r) <= 9.
Proof. intros r Hr. rewrite (ge_row_k r Hr). exact Hr. Qed.

Lemma ge_row_k_ne2 : forall r, 3 <= r <= 9 -> RcLay.ly_k (CROW r) <> 2.
Proof. intros r Hr. rewrite (ge_row_k r Hr). lia. Qed.

(* Every KB = 2 hypothesis of the Section is vacuous at row := CROW r. *)
Lemma ge_row_kb2 : forall r (P : Prop), 3 <= r <= 9 -> RcLay.ly_k (CROW r) = 2 -> P.
Proof. intros r P Hr E. exfalso. exact (ge_row_k_ne2 r Hr E). Qed.

Lemma ge_row_bb : forall r, 3 <= r <= 9 -> RcLay.ly_bb (RcLay.ly_k (CROW r)) = RcLay.ly_bb r.
Proof. intros r Hr. rewrite (ge_row_k r Hr). reflexivity. Qed.

(* The two magic bytes the run's result bytes name, and the kind byte as a byte. *)
Lemma ge_row_nth0 : forall r, nth 0 (CROW r) (Z_to_bv 8 0) = Z_to_bv 8 0xcd.
Proof. intros r. reflexivity. Qed.

Lemma ge_row_nth1 : forall r, nth 1 (CROW r) (Z_to_bv 8 0) = Z_to_bv 8 0xea.
Proof. intros r. reflexivity. Qed.

Lemma ge_row_nth2 : forall r, nth 2 (CROW r) (Z_to_bv 8 0) = Z_to_bv 8 r.
Proof. intros r. reflexivity. Qed.

(* Bytes 8 .. 17 are zero: the table pointer, the overlay offset and the overlay length. *)
Lemma ge_row_tm : forall r, RcLay.ly_tm (CROW r) = 0.
Proof. intros r. reflexivity. Qed.

Lemma ge_row_ao : forall r, RcLay.ly_ao (CROW r) = 0.
Proof. intros r. reflexivity. Qed.

Lemma ge_row_al : forall r, RcLay.ly_al (CROW r) = 0.
Proof. intros r. reflexivity. Qed.

(* [Hao] *)
Lemma ge_row_Hao : forall r, RcLay.ly_ao (CROW r) + RcLay.ly_al (CROW r) <= 32.
Proof. intros r. rewrite ge_row_ao, ge_row_al. lia. Qed.

(* Every `ly_al row <> 0 ->` hypothesis of the Section is vacuous at row := CROW r. *)
Lemma ge_row_al0 : forall r (P : Prop), RcLay.ly_al (CROW r) <> 0 -> P.
Proof. intros r P H. exfalso. exact (H (ge_row_al r)). Qed.

(* ---- the gate bytes ----------------------------------------------------------------------------------- *)

Lemma ge_em_bnd : forall r, 0 <= EM_C r <= 1 /\ 0 <= EM_L r <= 1 /\ 0 <= EM_G r <= 1 /\ 0 <= EM_A r <= 1.
Proof.
  intros r. unfold EM_C, EM_L, EM_G, EM_A.
  repeat split; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia.
Qed.

Lemma ge_row_b18 : forall r, RcFin.ubat (CROW r) 18 = 0.
Proof. intros r. reflexivity. Qed.

Lemma ge_row_b19 : forall r, RcFin.ubat (CROW r) 19 = 0.
Proof. intros r. reflexivity. Qed.

Lemma ge_row_b20 : forall r, RcFin.ubat (CROW r) 20 = EM_C r.
Proof. intros r. unfold RcFin.ubat, CROW, EM_C. destruct ((r =? 3) || (r =? 5)); reflexivity. Qed.

Lemma ge_row_b21 : forall r, RcFin.ubat (CROW r) 21 = EM_L r.
Proof. intros r. unfold RcFin.ubat, CROW, EM_L. destruct ((r =? 3) || (r =? 4) || (r =? 9)); reflexivity. Qed.

Lemma ge_row_b22 : forall r, RcFin.ubat (CROW r) 22 = EM_G r.
Proof. intros r. unfold RcFin.ubat, CROW, EM_G. destruct ((r =? 4) || (r =? 9)); reflexivity. Qed.

Lemma ge_row_b23 : forall r, RcFin.ubat (CROW r) 23 = EM_A r.
Proof.
  intros r. unfold RcFin.ubat, CROW, EM_A.
  destruct ((r =? 5) || (r =? 6) || (r =? 7) || (r =? 8)); reflexivity.
Qed.

(* [Hc] *)
Lemma ge_row_Hc : forall r, RcFin.ubat (CROW r) 20 <= 2.
Proof. intros r. rewrite ge_row_b20. pose proof (ge_em_bnd r). lia. Qed.

(* [HL] *)
Lemma ge_row_HL : forall r, RcFin.ubat (CROW r) 21 <= 2.
Proof. intros r. rewrite ge_row_b21. pose proof (ge_em_bnd r). lia. Qed.

(* [HG] *)
Lemma ge_row_HG : forall r, RcFin.ubat (CROW r) 22 <= 1.
Proof. intros r. rewrite ge_row_b22. pose proof (ge_em_bnd r). lia. Qed.

(* [HA] *)
Lemma ge_row_HA : forall r, RcFin.ubat (CROW r) 23 <= 1.
Proof. intros r. rewrite ge_row_b23. pose proof (ge_em_bnd r). lia. Qed.

(* [Hc2]: c <= 1 on every row, so the c = 2 arm is never taken. *)
Lemma ge_row_Hc2 : forall r, RcFin.ubat (CROW r) 20 = 2 ->
  2 <= RcFin.ubat (CROW r) 19 /\ RcFin.ubat (CROW r) 18 + RcFin.ubat (CROW r) 19 <= 31.
Proof. intros r H. rewrite ge_row_b20 in H. pose proof (ge_em_bnd r). lia. Qed.

(* [HLA]: L <= 1 on every row, so the L = 2 arm is never taken. *)
Lemma ge_row_HLA : forall r, RcFin.ubat (CROW r) 21 = 2 -> RcFin.ubat (CROW r) 23 = 0.
Proof. intros r H. rewrite ge_row_b21 in H. pose proof (ge_em_bnd r). lia. Qed.

(* ---- the KB = 2 hypotheses of the Section, each vacuous, in the Section's own shape -------------------- *)

(* [Dst] *)
Lemma ge_row_Dst : forall r lo hi, 3 <= r <= 9 ->
  RcLay.ly_k (CROW r) = 2 -> RcLay.ly_dj lo hi (RcLay.ly_tm (CROW r)) (RcLay.ly_tm (CROW r) + 32).
Proof. intros r lo hi Hr. apply ge_row_kb2. exact Hr. Qed.

(* [Htm] *)
Lemma ge_row_Htm : forall r (tb : list byte), 3 <= r <= 9 ->
  RcLay.ly_k (CROW r) = 2 ->
  RcLay.ly_tm (CROW r) + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (RcLay.ly_tm (CROW r)) tb.
Proof. intros r tb Hr. apply ge_row_kb2. exact Hr. Qed.

(* [Atm] *)
Lemma ge_row_Atm : forall r (m : word -> option byte), 3 <= r <= 9 ->
  RcLay.ly_k (CROW r) = 2 -> addressable m (RcLay.ly_tm (CROW r)) 32.
Proof. intros r m Hr. apply ge_row_kb2. exact Hr. Qed.

(* [RTM] *)
Lemma ge_row_RTM : forall r (RNG : ExecF.footprint), 3 <= r <= 9 ->
  RcLay.ly_k (CROW r) = 2 -> ExecF.rng RNG (RcLay.ly_tm (CROW r)) 32.
Proof. intros r RNG Hr. apply ge_row_kb2. exact Hr. Qed.

(* [RTMS] *)
Lemma ge_row_RTMS : forall r (RNG : ExecF.footprint), 3 <= r <= 9 ->
  RcLay.ly_k (CROW r) = 2 -> forall p q, RcLay.ly_tm (CROW r) <= p -> q <= RcLay.ly_tm (CROW r) + 31 ->
    ExecF.rng RNG (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
Proof. intros r RNG Hr E. exact (ge_row_kb2 r _ Hr E). Qed.

(* [FPtm] *)
Lemma ge_row_FPtm : forall r FS, 3 <= r <= 9 ->
  RcLay.ly_k (CROW r) = 2 ->
  fp_dj [(RcLay.ly_tm (CROW r), RcLay.ly_tm (CROW r) + 32)] (fp_w [0%nat; 1%nat] FS).
Proof. intros r FS Hr. apply ge_row_kb2. exact Hr. Qed.

(* ---- the Section's derived values at row := CROW r, g := 0, in the statement's forms ----------------------- *)

(* NM, the name-bytes condition, is the statement's premise condition (C_ctrl_emit_as.v:162). *)
Lemma ge_row_NM : forall r (mb : list byte), 3 <= r <= 9 ->
  (((3 <= RcLay.ly_k (CROW r) <= 9 /\
     (RcLay.ly_bb (RcLay.ly_k (CROW r)) = 5 \/ RcLay.ly_bb (RcLay.ly_k (CROW r)) = 6)) /\
    RcSynth.has mb <> 0 /\ RcSynth.rname mb <> 0) <->
   ((RcLay.ly_bb r = 5 \/ RcLay.ly_bb r = 6) /\ RcSynth.has mb <> 0 /\ RcSynth.rname mb <> 0)).
Proof.
  intros r mb Hr. rewrite (ge_row_k r Hr). split.
  - intros ((_ & HB) & HH). exact (conj HB HH).
  - intros (HB & HH). exact (conj (conj Hr HB) HH).
Qed.

(* EE and LEN. *)
Lemma ge_row_E : forall r n (mb : list byte),
  RcEmit.em_E (RcFin.ubat (CROW r) 21) (RcFin.ubat (CROW r) 22) n (RcEmit.em_hid mb) =
  RcEmit.em_E (EM_L r) (EM_G r) n (RcEmit.em_hid mb).
Proof. intros r n mb. rewrite ge_row_b21, ge_row_b22. reflexivity. Qed.

Lemma ge_row_LEN : forall r n, RcEmit.em_len (RcFin.ubat (CROW r) 21) n = RcEmit.em_len (EM_L r) n.
Proof. intros r n. rewrite ge_row_b21. reflexivity. Qed.

(* LB at g := 0: ctrl's block is the catalogue block ly_Z (C_ctrl_emit_as.v:115-116). *)
Lemma ge_row_LB : forall r md (mb nb tb gb : list byte), 3 <= r <= 9 ->
  RcLay.ly_lay (RcLay.ly_k (CROW r)) tb (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
    (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) gb =
  RcLay.ly_Z md mb nb (RcLay.ly_bb r).
Proof. intros r md mb nb tb gb Hr. row_cases r; reflexivity. Qed.

(* BLK at g := 0: the statement's `blk` (C_ctrl_emit_as.v:116). *)
Lemma ge_row_BLK : forall r md (mb nb tb gb : list byte), 3 <= r <= 9 ->
  RcFin.fin (RcFin.ubat (CROW r) 20) (RcFin.ubat (CROW r) 18) (RcFin.ubat (CROW r) 19)
    (RcLay.ly_lay (RcLay.ly_k (CROW r)) tb (RcLay.ly_Z md mb nb (RcLay.ly_bb (RcLay.ly_k (CROW r)))) 0
       (RcLay.ly_ao (CROW r)) (RcLay.ly_al (CROW r)) gb) =
  RcFin.fin (EM_C r) 0 0 (RcLay.ly_Z md mb nb (RcLay.ly_bb r)).
Proof.
  intros r md mb nb tb gb Hr.
  rewrite (ge_row_LB r md mb nb tb gb Hr), ge_row_b20, ge_row_b18, ge_row_b19. reflexivity.
Qed.
