(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzArr BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRM (cx : cctx) (z : zstrm) (nin : Z) (p1 p2 bza bzfr : word) : list cell :=
  [C8 (Z_to_bv 64 nin); C4 (Z_to_bv 64 (z_avail_in z)); C4 (Z_to_bv 64 (z_tin_lo z)); C4 (Z_to_bv 64 (z_tin_hi z)); C4 p1;
   C8 (Z_to_bv 64 (c_bz cx + 8 + (BZ_MAX_UNUSED - z_avail_out z))); C4 (Z_to_bv 64 (z_avail_out z));
   C4 (Z_to_bv 64 (z_tout_lo z)); C4 (Z_to_bv 64 (z_tout_hi z)); C4 p2;
   C8 (Z_to_bv 64 (c_E cx)); C8 bza; C8 bzfr; C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition outb_def (outr : list Z) (OB : list byte) : list byte :=
  map (fun c => Z_to_bv 8 c) (rev outr) ++ skipn (length outr) OB.
Definition outb_sig : { f : list Z -> list byte -> list byte | f = outb_def }. Proof. exists outb_def; reflexivity. Qed.
Definition outb : list Z -> list byte -> list byte := proj1_sig outb_sig.
Lemma outb_eq : forall outr OB, outb outr OB = map (fun c => Z_to_bv 8 c) (rev outr) ++ skipn (length outr) OB.
Proof. intros. unfold outb. rewrite (proj2_sig outb_sig). reflexivity. Qed.
Lemma outb_nil : forall OB, outb [] OB = OB.
Proof. intros. rewrite outb_eq. reflexivity. Qed.
Lemma outb_length_nat : forall outr OB, (length outr <= length OB)%nat -> length (outb outr OB) = length OB.
Proof. intros outr OB H. rewrite outb_eq, length_app, length_map, length_rev, length_skipn. lia. Qed.
Lemma outb_length : forall outr OB n, Z.of_nat (length OB) = n -> Z.of_nat (length outr) <= n -> Z.of_nat (length (outb outr OB)) = n.
Proof. intros outr OB n H1 H2. rewrite outb_length_nat by lia. exact H1. Qed.
Lemma outb_cons : forall c outr OB, (length outr < length OB)%nat ->
  outb (c :: outr) OB = upd (outb outr OB) (length outr) (Z_to_bv 8 c).
Proof.
  intros c outr OB H. rewrite !outb_eq. cbn [rev]. rewrite map_app. cbn [map length].
  set (M := map (fun c0 : Z => Z_to_bv 8 c0) (rev outr)).
  assert (L : length M = length outr) by (subst M; rewrite length_map, length_rev; reflexivity).
  rewrite (upd_firstn_skipn (M ++ skipn (length outr) OB) (length outr)) by (rewrite length_app, L, length_skipn; lia).
  rewrite firstn_app, L, Nat.sub_diag, firstn_O, app_nil_r. rewrite (firstn_all2 M) by lia.
  rewrite skipn_app, L, (skipn_all2 M) by lia.
  assert (E1 : (S (length outr) - length outr = 1)%nat) by lia. rewrite E1.
  rewrite skipn_skipn, <- app_assoc. reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition co_step (e : est) (z : zstrm) : est * zstrm :=
  let c := zget (bw_zb (e_bw e)) (e_state_out_pos e) in
  let '(lo, hi) := inc64 (z_tout_lo z) (z_tout_hi z) in
  (est_set_outpos e (e_state_out_pos e + 1),
   ZS (z_in z) (z_avail_in z) (c :: z_outr z) (z_avail_out z - 1) (z_tin_lo z) (z_tin_hi z) lo hi).
(* [comment removed for export] *)
Definition m32 (x : Z) : Z := x mod 4294967296.
Lemma m32_eq : forall x, m32 x = x mod 4294967296. Proof. reflexivity. Qed.
Lemma co_step_eq : forall e z, co_step e z =
  (est_set_outpos e (e_state_out_pos e + 1),
   ZS (z_in z) (z_avail_in z) (zget (bw_zb (e_bw e)) (e_state_out_pos e) :: z_outr z) (z_avail_out z - 1)
      (z_tin_lo z) (z_tin_hi z) (m32 (z_tout_lo z + 1))
      (if m32 (z_tout_lo z + 1) =? 0 then z_tout_hi z + 1 else z_tout_hi z)).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition z_adv (z : zstrm) (rest : list Z) : zstrm :=
  ZS rest (z_avail_in z - 1) (z_outr z) (z_avail_out z) (m32 (z_tin_lo z + 1))
     (if m32 (z_tin_lo z + 1) =? 0 then z_tin_hi z + 1 else z_tin_hi z) (z_tout_lo z) (z_tout_hi z).
Lemma ci_step_eq : forall e z c rest, z_in z = c :: rest ->
  ci_step e z = (est_set_rl e (add_char_to_block (est_rl e) c), z_adv z rest).
Proof. intros e z c rest H. unfold ci_step. rewrite H. reflexivity. Qed.
Lemma copy_output_S : forall f e z p,
  copy_output (S f) e z p =
  if z_avail_out z =? 0 then (e, z, p)
  else if bw_numZ (e_bw e) <=? e_state_out_pos e then (e, z, p)
  else copy_output f (fst (co_step e z)) (snd (co_step e z)) true.
Proof.
  intros f e z p. cbn [copy_output]. unfold co_step.
  destruct (z_avail_out z =? 0); [reflexivity|]. destruct (bw_numZ (e_bw e) <=? e_state_out_pos e); [reflexivity|].
  destruct (inc64 (z_tout_lo z) (z_tout_hi z)) as [lo hi]. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acb_same : forall r ch, ch = rl_ch r -> rl_len r <> 255 ->
  add_char_to_block r ch = RL (rl_nblock r) (rl_block r) (rl_inUse r) (rl_crc r) (rl_ch r) (rl_len r + 1).
Proof.
  intros r ch -> NE. unfold add_char_to_block. rewrite Z.eqb_refl. cbn [negb andb orb].
  replace (rl_len r =? 255) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
Qed.
Lemma acb_same255 : forall r ch, ch = rl_ch r -> rl_len r = 255 -> rl_ch r < 256 ->
  add_char_to_block r ch =
  let r1 := add_pair_to_block r in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1.
Proof.
  intros r ch Ech E LT. unfold add_char_to_block. rewrite <- Ech, Z.eqb_refl, E. cbn [negb andb orb Z.eqb Pos.eqb].
  replace (ch <? 256) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma acb_fast : forall r ch, ch <> rl_ch r -> rl_len r = 1 ->
  add_char_to_block r ch =
  RL (rl_nblock r + 1) (zset (rl_block r) (rl_nblock r) (Z.land (rl_ch r) 255)) (zset (rl_inUse r) (rl_ch r) 1)
     (crc_update (rl_crc r) (Z.land (rl_ch r) 255)) ch 1.
Proof.
  intros r ch NE E. unfold add_char_to_block. replace (ch =? rl_ch r) with false by (symmetry; apply Z.eqb_neq; exact NE).
  rewrite E. cbn [negb andb orb Z.eqb Pos.eqb]. reflexivity.
Qed.
Lemma acb_gen : forall r ch, ch <> rl_ch r -> rl_len r <> 1 -> rl_ch r < 256 ->
  add_char_to_block r ch =
  let r1 := add_pair_to_block r in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1.
Proof.
  intros r ch NE N1 LT. unfold add_char_to_block. replace (ch =? rl_ch r) with false by (symmetry; apply Z.eqb_neq; exact NE).
  replace (rl_len r =? 1) with false by (symmetry; apply Z.eqb_neq; exact N1). cbn [negb andb orb].
  replace (rl_ch r <? 256) with true by (symmetry; apply Z.ltb_lt; exact LT). reflexivity.
Qed.
Lemma acb_gen256 : forall r ch, ch <> rl_ch r -> rl_len r <> 1 -> 256 <= rl_ch r ->
  add_char_to_block r ch = RL (rl_nblock r) (rl_block r) (rl_inUse r) (rl_crc r) ch 1.
Proof.
  intros r ch NE N1 GE. unfold add_char_to_block. replace (ch =? rl_ch r) with false by (symmetry; apply Z.eqb_neq; exact NE).
  replace (rl_len r =? 1) with false by (symmetry; apply Z.eqb_neq; exact N1). cbn [negb andb orb].
  replace (rl_ch r <? 256) with false by (symmetry; apply Z.ltb_ge; exact GE). reflexivity.
Qed.

(* [comment removed for export] *)
Definition hc_prep (e : est) : est :=
  let e := prepare_new_block e in est_set_modes e (e_mode e) BZ_S_INPUT (e_avail_in_expect e).
(* [comment removed for export] *)
Definition hc_flush (e : est) : est := est_set_rl e (flush_RL (est_rl e)).
Definition hc_cbF (e : est) : est :=
  let e := hc_flush e in
  let '(e, _) := compressBlock e (e_mode e =? BZ_M_FINISHING) znew in
  est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e).
(* [comment removed for export] *)
Definition hc_cbR (e : est) : est :=
  let '(e, _) := compressBlock e false znew in
  est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e).
(* [comment removed for export] *)
Definition z_reset (z : zstrm) : zstrm :=
  ZS (z_in z) (z_avail_in z) [] BZ_MAX_UNUSED (z_tin_lo z) (z_tin_hi z) (z_tout_lo z) (z_tout_hi z).
(* [comment removed for export] *)
Definition eg_set_aie (g : eg) : eg := EG true (g_sort g) (g_mtf g) (g_bs g) (g_zbits g).
Definition e_finish (e : est) (z : zstrm) : est := est_set_modes e BZ_M_FINISHING (e_state e) (z_avail_in z).

(* [comment removed for export] *)
Definition hc_out (e : est) (z : zstrm) (pout : bool) : est * zstrm * bool * bool :=
  let '(e, z, pout) := copy_output (Z.to_nat (z_avail_out z) + 1)%nat e z pout in
  if e_state_out_pos e <? bw_numZ (e_bw e) then (e, z, pout, true) else
  if (e_mode e =? BZ_M_FINISHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e then (e, z, pout, true) else
  let e := hc_prep e in
  if (e_mode e =? BZ_M_FLUSHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e then (e, z, pout, true)
  else (e, z, pout, false).
Definition hc_in (lj : zarr) (e : est) (z : zstrm) (pin pout : bool) : est * zstrm * bool * bool * bool :=
  let '(e, z, pin) := copy_input (Z.to_nat (z_avail_in z) + 1)%nat e z pin in
  if negb (e_mode e =? BZ_M_RUNNING) && (e_avail_in_expect e =? 0) then
    let e := est_set_rl e (flush_RL (est_rl e)) in
    let '(e, _) := compressBlock e (e_mode e =? BZ_M_FINISHING) lj in
    (est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e), z, pin, pout, false)
  else if NBLOCKMAX <=? e_nblock e then
    let '(e, _) := compressBlock e false lj in
    (est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e), z, pin, pout, false)
  else if z_avail_in z =? 0 then (e, z, pin, pout, true)
  else (e, z, pin, pout, false).
(* [comment removed for export] *)
Lemma hc_iter_input : forall lj e z pin pout, e_state e = BZ_S_INPUT -> hc_iter lj e z pin pout = hc_in lj e z pin pout.
Proof.
  intros lj e z pin pout ST. unfold hc_iter, hc_in. rewrite ST. cbn [Z.eqb BZ_S_INPUT BZ_S_OUTPUT Pos.eqb].
  rewrite ST. cbn [Z.eqb BZ_S_INPUT BZ_S_OUTPUT Pos.eqb]. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma hc_iter_output : forall lj e z pin pout, e_state e = BZ_S_OUTPUT ->
  hc_iter lj e z pin pout =
  let '(e1, z1, pout1, brk) := hc_out e z pout in
  if brk then (e1, z1, pin, pout1, true) else hc_in lj e1 z1 pin pout1.
Proof.
  intros lj e z pin pout ST. unfold hc_iter, hc_out, hc_in. rewrite ST. cbn [Z.eqb BZ_S_INPUT BZ_S_OUTPUT Pos.eqb].
  destruct (copy_output _ e z pout) as [[e1 z1] pout1] eqn:CO.
  destruct (e_state_out_pos e1 <? bw_numZ (e_bw e1)); [reflexivity|].
  destruct ((e_mode e1 =? BZ_M_FINISHING) && (e_avail_in_expect e1 =? 0) && isempty_RL_e e1); [reflexivity|].
  unfold hc_prep. cbn [e_mode e_state e_avail_in_expect est_set_modes].
  destruct ((e_mode (prepare_new_block e1) =? BZ_M_FLUSHING) && (e_avail_in_expect (prepare_new_block e1) =? 0) &&
            isempty_RL_e (est_set_modes (prepare_new_block e1) (e_mode (prepare_new_block e1)) BZ_S_INPUT (e_avail_in_expect (prepare_new_block e1))));
    [reflexivity|].
  cbn [Z.eqb BZ_S_INPUT Pos.eqb]. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint hc_breaks (fuel : nat) (lj : zarr) (e : est) (z : zstrm) (pin pout : bool) : Prop :=
  match fuel with
  | O => False
  | S f => let '(e1, z1, pin1, pout1, brk) := hc_iter lj e z pin pout in
           if brk then True else hc_breaks f lj e1 z1 pin1 pout1
  end.
Lemma hc_breaks_S : forall f lj e z pin pout,
  hc_breaks (S f) lj e z pin pout =
  let '(e1, z1, pin1, pout1, brk) := hc_iter lj e z pin pout in if brk then True else hc_breaks f lj e1 z1 pin1 pout1.
Proof. reflexivity. Qed.
Lemma hc_loop_S : forall f lj e z pin pout,
  hc_loop (S f) lj e z pin pout =
  let '(e1, z1, pin1, pout1, brk) := hc_iter lj e z pin pout in if brk then (e1, z1, pin1 || pout1) else hc_loop f lj e1 z1 pin1 pout1.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma inUse_clear_other : forall n a i k, (k < i \/ i + Z.of_nat n <= k) -> zget (inUse_clear a i n) k = zget a k.
Proof.
  induction n as [|n IH]; intros a i k Hk; cbn [inUse_clear]; [reflexivity|].
  rewrite IH by lia. apply zget_zset_other. lia.
Qed.
Lemma inUse_clear_zero : forall n a i k, i <= k < i + Z.of_nat n -> zget (inUse_clear a i n) k = 0.
Proof.
  induction n as [|n IH]; intros a i k Hk; cbn [inUse_clear]; [lia|].
  destruct (Z.eq_dec k i) as [->|NE].
  - rewrite inUse_clear_other by lia. apply zget_zset_same.
  - apply IH. lia.
Qed.
Lemma inUse_clear_zdef : forall n a i k, i <= k < i + Z.of_nat n -> zdef (inUse_clear a i n) k = true.
Proof.
  induction n as [|n IH]; intros a i k Hk; cbn [inUse_clear]; [lia|].
  destruct (Z_lt_le_dec k (i + 1)).
  - assert (k = i) by lia. subst k.
    assert (H : forall m b j, zdef b i = true -> zdef (inUse_clear b j m) i = true).
    { induction m as [|m IHm]; intros b j Hb; cbn [inUse_clear]; [exact Hb|]. apply IHm. apply zdef_zset_mono. exact Hb. }
    apply H. apply zdef_zset_same.
  - apply IH. lia.
Qed.
Lemma ovb_inUse_clear : forall a J, ovb (inUse_clear a 0 256) J 256 = repeat (Z_to_bv 8 0) 256.
Proof.
  intros a J. apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 256) as [Hk|Hk].
  - replace k with (Z.to_nat (Z.of_nat k)) by lia.
    rewrite (ovb_nth (inUse_clear a 0 256) J 256 (Z.of_nat k)) by (first [lia | apply inUse_clear_zdef; cbn; lia]).
    rewrite inUse_clear_zero by (cbn; lia). symmetry. apply nth_error_repeat. lia.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite ovb_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.
Lemma inUse_clear_zdefr : forall a, zdefr (inUse_clear a 0 256) 0 256.
Proof. intros a k Hk. apply inUse_clear_zdef. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HCI (cx : cctx) (g : eg) (e : est) (z : zstrm) : Prop :=
  est_ok e /\
  (* [comment removed for export] *)
  ((e_state_in_ch e = 256 /\ e_state_in_len e = 0) \/ (e_state_in_ch e < 256 /\ 1 <= e_state_in_len e)) /\
  zdefr (e_inUse e) 0 256 /\
  (* [comment removed for export] *)
  (e_mode e = BZ_M_RUNNING \/
   (e_mode e = BZ_M_FINISHING /\ g_aie g = true /\ e_avail_in_expect e = 0 /\ z_avail_in z = 0)) /\
  (* [comment removed for export] *)
  z_avail_in z = Z.of_nat (length (z_in z)) /\ z_avail_in z < 2147483648 /\
  0 <= z_avail_out z <= BZ_MAX_UNUSED /\ Z.of_nat (length (z_outr z)) = BZ_MAX_UNUSED - z_avail_out z /\
  (* [comment removed for export] *)
  (e_state e = BZ_S_OUTPUT ->
     g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) /\ e_nblock e + bw_numZ (e_bw e) <= ARR2_SIZE /\
     (forall k, 0 <= k < bw_numZ (e_bw e) -> zget (e_arr2 e) (e_nblock e + k) = zget (bw_zb (e_bw e)) k)) /\
  (* [comment removed for export] *)
  e_nblock e + bw_numZ (e_bw e) <= ARR2_SIZE.

(* [comment removed for export] *)
Section HCIacc.
  Variables (cx : cctx) (g : eg) (e : est) (z : zstrm).
  Hypothesis H : HCI cx g e z.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End HCIacc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record hc_laws (HCX : cctx -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop) : Prop := HL {
  (* [comment removed for export] *)
  hl_hci : forall cx g e z, HCX cx g e z -> HCI cx g e z;
  (* [comment removed for export] *)
  hl_co : forall cx g e z, HCX cx g e z -> e_state e = BZ_S_OUTPUT -> z_avail_out z <> 0 ->
            e_state_out_pos e < bw_numZ (e_bw e) -> HCX cx g (fst (co_step e z)) (snd (co_step e z));
  (* [comment removed for export] *)
  hl_ci : forall cx g e z, HCX cx g e z -> e_state e = BZ_S_INPUT -> e_mode e = BZ_M_RUNNING ->
            e_nblock e < NBLOCKMAX -> z_avail_in z <> 0 -> HCX cx g (fst (ci_step e z)) (snd (ci_step e z));
  (* [comment removed for export] *)
  hl_prep : forall cx g e z, HCX cx g e z -> e_state e = BZ_S_OUTPUT -> bw_numZ (e_bw e) <= e_state_out_pos e ->
            (e_mode e =? BZ_M_FINISHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e = false ->
            HCX cx g (hc_prep e) z;
  (* [comment removed for export] *)
  hl_cbR : forall cx g e z, HCX cx g e z -> e_state e = BZ_S_INPUT -> e_mode e = BZ_M_RUNNING -> NBLOCKMAX <= e_nblock e ->
            cb_pre g e /\ CBFACTS e /\ HCX cx (eg_after_cb cx g e) (hc_cbR e) z;
  (* [comment removed for export] *)
  hl_cbF : forall cx g e z, HCX cx g e z -> e_state e = BZ_S_INPUT -> e_mode e = BZ_M_FINISHING ->
            cb_pre g (hc_flush e) /\ CBFACTS (hc_flush e) /\ HCX cx (eg_after_cb cx g (hc_flush e)) (hc_cbF e) z;
  (* [comment removed for export] *)
  hl_term : forall cx g e z, HCX cx g e z -> z_outr z = [] -> z_avail_out z = BZ_MAX_UNUSED ->
            hc_breaks (hc_fuel z) znew e z false false;
  (* [comment removed for export] *)
  hl_reset : forall cx g e z, HCX cx g e z -> HCX cx g e (z_reset z);
  (* [comment removed for export] *)
  hl_finish : forall cx g e z, HCX cx g e z -> e_mode e = BZ_M_RUNNING -> z_avail_in z = 0 ->
            HCX cx (eg_set_aie g) (e_finish e z) z;
  (* [comment removed for export] *)
  hl_cb_mode : forall e b, e_mode (fst (compressBlock e b znew)) = e_mode e
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u8ro_keep : forall segs W m m' nin (pl : list byte),
  u8ro segs m nin pl -> munch W m m' -> (pl <> [] -> disjoint_from W nin (Z.of_nat (length pl))) -> u8ro segs m' nin pl.
Proof.
  intros segs W m m' nin pl H MU D. destruct pl as [|b pl'].
  - cps_destruct H as (H1 & H2 & _). split; [exact H1|]. split; [exact H2|]. cbn. intros i Hi. lia.
  - eapply u8ro_transport; [exact H | exact MU | apply D; discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HC_STACK : Z := 16496.   (* [comment removed for export] *)
Definition handle_compress_W (cx : cctx) (usp : Z) : list (Z * Z) :=
  [(c_E cx, c_E cx + ESTATE_SIZE); (c_A1 cx, c_A1 cx + ARR1_SIZE); (c_A2 cx, c_A2 cx + ARR2_SIZE); (c_FT cx, c_FT cx + 4 * FTAB_WORDS);
   (c_bz cx + 8, c_bz cx + 5008); (c_bz cx + BZF_STRM, c_bz cx + BZF_STRM + 80); (usp - HC_STACK, usp)].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hid_sig : { f : Prop -> Prop | f = fun P => P }. Proof. exists (fun P => P); reflexivity. Qed.
Definition hid : Prop -> Prop := proj1_sig hid_sig.
Lemma hid_eq : forall P, hid P = P. Proof. intros P. unfold hid. rewrite (proj2_sig hid_sig). reflexivity. Qed.
Lemma hid_i : forall P : Prop, P -> hid P. Proof. intros P H. rewrite hid_eq. exact H. Qed.
Lemma hid_e : forall P : Prop, hid P -> P. Proof. intros P H. rewrite hid_eq in H. exact H. Qed.

Section Rest.
  Variables (I : cimg) (cx : cctx).
  (* [comment removed for export] *)
  Definition erest (e : est) (sv : word) (m : word -> option byte) : Prop :=
    u8arr (ci_segs I) m (c_E cx + 384) (ovb (e_unseqToSeq e) (jseg (c_J cx) 384 256) 256) /\
    u32arr (ci_segs I) m (c_E cx + 672) (ovw (e_mtfFreq e) (jseg (c_J cx) 672 1032) 258) /\
    u8arr (ci_segs I) m (c_E cx + 1704) (ovb (e_selector e) (jseg (c_J cx) 1704 18002) 18002) /\
    u8arr (ci_segs I) m (c_E cx + 19706) (ovb (e_selectorMtf e) (jseg (c_J cx) 19706 18002) 18002) /\
    u8arr (ci_segs I) m (c_E cx + 37708) (ovb (e_len e) (jseg (c_J cx) 37708 1548) 1548) /\
    u32arr (ci_segs I) m (c_E cx + 39256) (ovw (e_code e) (jseg (c_J cx) 39256 6192) 1548) /\
    u32arr (ci_segs I) m (c_E cx + 45448) (ovw (e_rfreq e) (jseg (c_J cx) 45448 6192) 1548) /\
    u32arr (ci_segs I) m (c_E cx + 51640) (ovw (e_len_pack e) (jseg (c_J cx) 51640 4128) 1032) /\
    u8arr (ci_segs I) m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\ u32arr (ci_segs I) m (c_FT cx) (zw32 (e_ftab e) FTAB_WORDS) /\
    cimg_mem I m sv.
  (* [comment removed for export] *)
  Lemma erest_intro : forall e sv m,
    u8arr (ci_segs I) m (c_E cx + 384) (ovb (e_unseqToSeq e) (jseg (c_J cx) 384 256) 256) ->
    u32arr (ci_segs I) m (c_E cx + 672) (ovw (e_mtfFreq e) (jseg (c_J cx) 672 1032) 258) ->
    u8arr (ci_segs I) m (c_E cx + 1704) (ovb (e_selector e) (jseg (c_J cx) 1704 18002) 18002) ->
    u8arr (ci_segs I) m (c_E cx + 19706) (ovb (e_selectorMtf e) (jseg (c_J cx) 19706 18002) 18002) ->
    u8arr (ci_segs I) m (c_E cx + 37708) (ovb (e_len e) (jseg (c_J cx) 37708 1548) 1548) ->
    u32arr (ci_segs I) m (c_E cx + 39256) (ovw (e_code e) (jseg (c_J cx) 39256 6192) 1548) ->
    u32arr (ci_segs I) m (c_E cx + 45448) (ovw (e_rfreq e) (jseg (c_J cx) 45448 6192) 1548) ->
    u32arr (ci_segs I) m (c_E cx + 51640) (ovw (e_len_pack e) (jseg (c_J cx) 51640 4128) 1032) ->
    u8arr (ci_segs I) m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) -> u32arr (ci_segs I) m (c_FT cx) (zw32 (e_ftab e) FTAB_WORDS) ->
    cimg_mem I m sv -> hid (erest e sv m).
  Proof. intros. apply hid_i. unfold erest. tauto. Qed.
  (* [comment removed for export] *)
  Lemma erest_fields : forall e e' sv m,
    e_unseqToSeq e' = e_unseqToSeq e -> e_mtfFreq e' = e_mtfFreq e -> e_selector e' = e_selector e ->
    e_selectorMtf e' = e_selectorMtf e -> e_len e' = e_len e -> e_code e' = e_code e -> e_rfreq e' = e_rfreq e ->
    e_len_pack e' = e_len_pack e -> e_arr1 e' = e_arr1 e -> e_ftab e' = e_ftab e ->
    hid (erest e sv m) -> hid (erest e' sv m).
  Proof. intros e e' sv m E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 H. apply hid_e in H. apply hid_i. unfold erest in *.
         rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. exact H. Qed.
  (* [comment removed for export] *)
  Definition hc_Wloc (usp : Z) : list (Z * Z) :=
    [(c_E cx, c_E cx + 384); (c_E cx + 640, c_E cx + 672); (c_A2 cx, c_A2 cx + ARR2_SIZE);
     (c_bz cx + 8, c_bz cx + 5008); (c_bz cx + BZF_STRM, c_bz cx + BZF_STRM + 80); (usp - HC_STACK, usp)].
    (* [comment removed for export] *)
End Rest.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hsh_sig : { f : Prop -> Prop | f = fun P => P }. Proof. exists (fun P => P); reflexivity. Qed.
Definition hsh : Prop -> Prop := proj1_sig hsh_sig.
Lemma hsh_eq : forall P, hsh P = P. Proof. intros P. unfold hsh. rewrite (proj2_sig hsh_sig). reflexivity. Qed.
Lemma hsh_i : forall P : Prop, P -> hsh P. Proof. intros P H. rewrite hsh_eq. exact H. Qed.
Lemma hsh_e : forall P : Prop, hsh P -> P. Proof. intros P H. rewrite hsh_eq in H. exact H. Qed.
End ACeilS1.

Ltac shelve_mem H := apply hsh_i in H.
Ltac unshelve_mems := repeat match goal with H : hsh _ |- _ => apply hsh_e in H end.
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sep_use : forall b1 a2 b2 a1 e1 a e2 A : Z,
  id (b1 <= a2 \/ b2 <= a1) -> (a1 <= A /\ e1 <= b1 /\ a2 <= a /\ e2 <= b2 /\ A <= e1 /\ a <= e2) -> (e1 <= a \/ e2 <= A).
Proof. unfold id. intros. lia. Qed.
Lemma sep_use' : forall b1 a2 b2 a1 e1 a e2 A : Z,
  id (b1 <= a2 \/ b2 <= a1) -> (a2 <= A /\ e1 <= b2 /\ a1 <= a /\ e2 <= b1 /\ A <= e1 /\ a <= e2) -> (e1 <= a \/ e2 <= A).
Proof. unfold id. intros. lia. Qed.
End ACeilS2.

Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Ltac sep_base e := lazymatch e with Z.add ?x _ => sep_base x | Z.sub ?x _ => sep_base x | _ => e end.
Ltac sep_is_lit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Ltac sep_same x y := first [ constr_eq x y | sep_is_lit x; sep_is_lit y ].
Ltac sep_tac :=
  lazymatch goal with |- (?e1 <= ?a \/ ?e2 <= ?A) =>
    let bA := sep_base A in let ba := sep_base a in
    match goal with
    | H : id (?b1 <= ?a2 \/ ?b2 <= ?a1) |- _ =>
        let c1 := sep_base a1 in let c2 := sep_base a2 in
        first [ sep_same c1 bA; sep_same c2 ba; apply (sep_use b1 a2 b2 a1 e1 a e2 A H); lia
              | sep_same c2 bA; sep_same c1 ba; apply (sep_use' b1 a2 b2 a1 e1 a e2 A H); lia ]
    end
  end.
Ltac slia_sep := first [ exact I | lia | sep_tac | split; [ first [ lia | sep_tac ] | slia_sep ] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac post_callW segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  unfold add_pair_W, compressBlock_W, handle_compress_W, bsW8_W, bsPutUInt32_W, blockSort_W, fallbackSort_W, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CB_STACK, HC_STACK, BZF_STRM in MUc;
  cbn [e_nblock e_mode e_state est_set_rl est_set_modes rl_nblock c_E c_A1 c_A2 c_FT c_bz] in MUc;
  repeat (rewrite unsigned_lit in MUc by lia);
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
