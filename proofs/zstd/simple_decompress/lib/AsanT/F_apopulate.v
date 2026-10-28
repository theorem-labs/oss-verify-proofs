(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 ARep ARepKit ARepFrame ARefill_iface RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
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
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Local Ltac by_GC GC := rewrite ?GC; cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user].

Section CANSEC1. Context {rc : runConstT}.
Definition populate_entry := 0x38af4.
End CANSEC1.
Notation POPULATE_STACK := 512 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma size_of_class_pos : forall c, 1 <= c < K_NUM_CLASSES -> 32 <= size_of_class c <= 65536 /\ size_of_class c mod 32 = 0.
Proof.
  intros c Hc. unfold K_NUM_CLASSES in Hc.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
              \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  repeat (destruct E as [->|E]; [vm_compute; split; [split; discriminate| reflexivity] |]). subst. vm_compute. split; [split; discriminate| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma size_formula : forall c, 17 <= c <= 30 ->
  Z_to_bv 64 (Z.land ((Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 63))) 63) mod 18446744073709551616)
                     (Z.shiftr ((Z.shiftl 512 ((Z.shiftr (c + -16) 1) mod 64)) mod 18446744073709551616) 1)
              + Z.shiftl 512 ((Z.shiftr (c + -16) 1) mod 64)) = Z_to_bv 64 (size_of_class c).
Proof.
  intros c Hc.
  assert (E : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct E as [->|E]; [apply f_equal; vm_compute; reflexivity|]). subst. apply f_equal. vm_compute. reflexivity.
Qed.

Lemma m_divu_lit : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 ->
  mul_div M_DIVU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold mul_div. rewrite (unsigned_lit y) by lia.
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, !unsigned_lit; [reflexivity| |lia|lia].
  Z.div_mod_to_equations. nia.
Qed.

Lemma aclass_eta1 : forall r x y,
  cls_set_allocated_user x (cls_set_num_freed y r) = mkAClass (c_mapped_user r) x y (c_mapped_free_array r) (c_count r).
Proof. intros [] ? ?; reflexivity. Qed.
Lemma aclass_eta2 : forall r x y z,
  cls_set_allocated_user x (cls_set_num_freed y (cls_set_mapped_free_array z r)) = mkAClass (c_mapped_user r) x y z (c_count r).
Proof. intros [] ? ? ?; reflexivity. Qed.
Lemma aclass_eta3 : forall r v, cls_set_mapped_user v r = mkAClass v (c_allocated_user r) (c_num_freed r) (c_mapped_free_array r) (c_count r).
Proof. intros [] ?; reflexivity. Qed.

Lemma u32arr_nil : forall m A, 0 <= A -> A <= 2^64 -> u32arr bsegs m A [].
Proof.
  intros m A H0 H1. split.
  - split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exfalso. lia.
  - split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exfalso. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fvals (au S : Z) (n : nat) : list word :=
  rev (map (fun j => Z_to_bv 64 (Z.shiftr (au + Z.of_nat j * S) 4)) (seq 0 n)).

Lemma fvals_S : forall au S n, fvals au S (Datatypes.S n) = Z_to_bv 64 (Z.shiftr (au + Z.of_nat n * S) 4) :: fvals au S n.
Proof. intros. unfold fvals. rewrite seq_S, map_app, rev_app_distr. reflexivity. Qed.
Lemma fvals_length : forall au S n, length (fvals au S n) = n.
Proof. intros. unfold fvals. rewrite length_rev, length_map, length_seq. reflexivity. Qed.
Lemma fvals_nth : forall au S n j, (j < n)%nat ->
  nth_error (fvals au S n) j = Some (Z_to_bv 64 (Z.shiftr (au + Z.of_nat (n - 1 - j) * S) 4)).
Proof.
  intros au S n. induction n as [|n IH]; intros j Hj; [lia|].
  rewrite fvals_S. destruct j as [|j]; cbn [nth_error].
  - replace (Datatypes.S n - 1 - 0)%nat with n by lia. reflexivity.
  - rewrite IH by lia. replace (Datatypes.S n - 1 - Datatypes.S j)%nat with (n - 1 - j)%nat by lia. reflexivity.
Qed.

Lemma snoc_inv : forall {X} (l : list X) n, length l = Datatypes.S n -> exists l' x, l = l' ++ [x] /\ length l' = n.
Proof.
  intros X l n HL. destruct l as [|y l0]; [cbn in HL; lia|].
  exists (removelast (y :: l0)), (last (y :: l0) y). split; [apply app_removelast_last; discriminate|].
  rewrite length_removelast by discriminate. rewrite HL. lia.
Qed.

Lemma fill_loop_spec : forall RNG (d : nat) (i ncnt A au S : Z) (jk : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (ncnt - i) ->
  0 <= i < ncnt -> length jk = Z.to_nat (ncnt - i) ->
  u32arr bsegs m A (jk ++ fvals au S (Z.to_nat i)) ->
  mem_inv bsegs m ->
  0 <= au -> 0 < S -> au + ncnt * S < 2^47 -> 0 <= A -> A + 4 * ncnt < 2^47 ->
  (forall k, 0 <= k < ncnt -> rng RNG (A + 4 * k) 4) ->      (* [comment removed for export] *)
  evtF bsegs RNG (fun ms' => exists a4' a5' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ncnt) (Z_to_bv 64 (A + 4 * ncnt)) (Z_to_bv 64 (au + ncnt * S)) a3 a4' a5' a6 a7
                    s2 (Z_to_bv 64 ncnt) s4 (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x38cd0) fc None m' (seg_rom bsegs)
      /\ munch [(A, A + 4 * ncnt)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ u32arr bsegs m' A (fvals au S (Z.to_nat ncnt)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 (A + 4 * ncnt)) (Z_to_bv 64 (au + i * S)) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 ncnt) s4 (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x38cb0) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LJK AR MI AU SP AUB A0 AB RA; [lia|].
  destruct (snoc_inv jk (Z.to_nat (ncnt - i - 1)) ltac:(rewrite LJK; lia)) as (jk' & x & -> & LJK').
  pose proof (munch_refl [(A, A + 4 * ncnt)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (A + 4 * (ncnt - 1 - i)))
    ltac:(apply Z_to_bv_eqm; rewrite zb_lxor_ones by lia; rewrite Z.shiftl_mul_pow2 by lia; clear -I A0 AB; Z.div_mod_to_equations; lia).
  assert (LL : length ((jk' ++ [x]) ++ fvals au S (Z.to_nat i)) = Z.to_nat ncnt) by (rewrite !length_app, fvals_length, LJK'; cbn; lia).
  pose proof (u32arr_store_ok bsegs m A _ (ncnt - 1 - i) (wa (A + 4 * (ncnt - 1 - i))) AR ltac:(rewrite LL; lia) eq_refl) as SOK.
  pose proof (RA (ncnt - 1 - i) ltac:(lia)) as RA1.
  step. clear RA1.                                       (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u32arr_write bsegs m A _ (ncnt - 1 - i) v AR ltac:(rewrite LL; lia)) as AR2;
    replace (A + 4 * (ncnt - 1 - i))%Z with E in AR2 by lia
  end.
  replace (upd ((jk' ++ [x]) ++ fvals au S (Z.to_nat i)) (Z.to_nat (ncnt - 1 - i)) (Z_to_bv 64 (Z.shiftr (au + i * S) 4)))
     with (jk' ++ fvals au S (Z.to_nat (i + 1))) in AR2.
  2:{ rewrite <- app_assoc. rewrite upd_firstn_skipn by (rewrite app_assoc, LL; lia).
      replace (Z.to_nat (ncnt - 1 - i)) with (length jk') by lia.
      rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
      replace (Datatypes.S (length jk')) with (length (jk' ++ [x])) by (rewrite length_app; cbn; lia).
      rewrite app_assoc, skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app].
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. rewrite fvals_S.
      f_equal. f_equal. f_equal. f_equal. f_equal. lia. }
  clear AR. store_done. try clear SOK.
  zstep. setreg 12 (Z_to_bv 64 (au + (i + 1) * S)) ltac:(f_equal; lia).    (* [comment removed for export] *)
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    try rewrite Z.mod_small in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) ncnt A au S jk'); try eassumption; try lia. }
    cbv beta. intros ms' (a4' & a5' & m' & -> & MU2 & WM2 & MI2 & AR3).
    exists a4', a5', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2| exact AR3].
  - (* [comment removed for export] *)
    try rewrite Z.mod_small in K by lia. assert (EI : i + 1 = ncnt) by lia.
    apply evtF_done. rewrite EI in AR2 |- *. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    destruct jk' as [|y jk'']; [| exfalso; cbn in LJK'; lia]. cbn [app] in AR2. exact AR2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_after {R} (c : Z) (k : astate -> bool -> AM R) (st1 : astate) : AM R :=
  let size := size_of_class c in
  let r1 := get_cls st1 c in
  let new_cnt := (c_mapped_user r1 - c_allocated_user r1) / size in
  let total_freed := c_num_freed r1 + new_cnt in
  ensure_free_array st1 c total_freed (fun st2 ok =>
    if negb ok then k st2 false else
    let r2 := get_cls st2 c in
    k (put_cls c (cls_set_allocated_user (c_allocated_user r2 + new_cnt * size) (cls_set_num_freed total_freed r2)) st2) true).

Lemma populate_unfold : forall {R} st c req (k : astate -> bool -> AM R),
  populate_free_array st c req k =
   (let size := size_of_class c in let r := get_cls st c in
    let total_user := c_allocated_user r + req * size in
    if total_user <=? c_mapped_user r then pop_after c k st else
    let ums := rup (total_user - c_mapped_user r) K_USER_MAP in
    if K_FREEARR_OFF <? c_mapped_user r + ums then aundef_ (UCheck 705) (k st false)
    else let beg := region_beg st c + c_mapped_user r in
    ev (AMmap beg ums PROT_RW F_FIXED) (fun a =>
      if negb (fixed_answer_ok beg a) then aundef_ UBadAnswer (k st false)
      else if is_err a then k st false
      else pop_after c k (put_cls c (cls_set_mapped_user (c_mapped_user r + ums) r) st))).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition tail_ret (L : alayout) (RNG : footprint) (sp : word) (st st1 : astate) (c lo : Z) (m1 : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r1 := get_cls st1 c in let S := size_of_class c in
  let FA := afreearr L c in let RI := aregion_info L c in
  let mu1 := c_mapped_user r1 in let au := c_allocated_user r1 in let nf := c_num_freed r1 in let mfa := c_mapped_free_array r1 in
  let ncnt := (mu1 - au) / S in
  fp_le RNG RNG' /\
  exists mfa' sj',
     (   (4 * (nf + ncnt) <= mfa /\ mfa' = mfa /\ RNG' = RNG)
      \/ (mfa < 4 * (nf + ncnt) /\ mfa' = rup (4 * (nf + ncnt)) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * (nf + ncnt) <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ u32arr bsegs m' (FA + 4 * nf) (fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * (nf + ncnt)) (mfa' - 4 * (nf + ncnt))
  /\ st2 = put_cls c (mkAClass mu1 (au + ncnt * S) (nf + ncnt) mfa' (c_count r1)) st
  /\ munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp);
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2800, al_t L + 3168); (RI + 16, RI + 56); (RI + 68, RI + 69)]%Z m1 m'
  /\ wmono bsegs m1 m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf + ncnt)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (au + ncnt * S)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 mu1); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma pop_tail_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rax s1x s3x s6x a1x a2x a4x a5x : word)
    (F : bvmap 5 word) fc (m1 : amem) (L : alayout) (st st1 : astate) (c lo : Z) (sj : list word) (fj : list byte),
  let r1 := get_cls st1 c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu1 := c_mapped_user r1 in let au := c_allocated_user r1 in let nf := c_num_freed r1 in let mfa := c_mapped_free_array r1 in
  stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
  mem_inv bsegs m1 -> tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m1 ->
  rw_cells bsegs m1 (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu1); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m1 (RI + 68) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m1 (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m1 (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  azero m1 (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (forall r', put_cls c r' st1 = put_cls c r' st) -> a_space_beg st1 = al_space_beg L ->
  (* [comment removed for export] *)
  1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu1 -> mu1 <= K_FREEARR_OFF -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG (FA + 4 * nf) (mfa - 4 * nf) ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      tail_ret L RNG sp st st1 c lo m1 st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
  evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (pop_after c k st1)) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x (Z_to_bv 64 AINSTANCE) a1x a2x (Z_to_bv 64 au) a4x a5x a6 a7
             (Z_to_bv 64 RB) s3x (Z_to_bv 64 mu1) (Z_to_bv 64 S) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38c68) fc None m1 (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP FR MC REG EXH STATS LSJ FJ AZF PUTEQ SBE HC MU MUX AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP RIMG RSTK RCTX RT RRI RFJ CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  set (mu1 := c_mapped_user (get_cls st1 c)) in *. set (au := c_allocated_user (get_cls st1 c)) in *.
  set (nf := c_num_freed (get_cls st1 c)) in *. set (mfa := c_mapped_free_array (get_cls st1 c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  rewrite RIE in REG, EXH, RRI |- *. rewrite RBE. rewrite FAE in FJ, AZF, RFJ.
  set (ncnt := (mu1 - au) / S).
  assert (NC : 0 <= ncnt /\ ncnt * S <= mu1 - au /\ S * nf <= au /\ 4 * (nf + ncnt) <= 469762048).
  { subst ncnt. clear -MU MUX SZ NF NFA AUM. Z.div_mod_to_equations. nia. }
  destruct NC as (NC0 & NC1 & NC2 & NC3).
  pose proof (munch_refl [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp)]%Z m1) as MUN.
  pose proof (wmono_refl bsegs m1) as WM.
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  setreg 19 (Z_to_bv 64 ncnt) ltac:(subst ncnt; symmetry; apply m_divu_lit; clear -MU MUX SZ; lia).
  zstep. step. step. step.                                     (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done. unfold pop_after. cbv zeta. fold S. fold mu1 au nf. fold ncnt.
  name_sp sp (-64).
  eapply ensure_spec with (lo := lo) (L := L).
  all: try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => rewrite Hsp; eassumption
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => rewrite RIE; exact REG
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ _ _ => rewrite FAE; exact AZF
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => rewrite RIE; exact RRI
       | |- rng _ _ _ => first [assumption | solve_rng]
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ?RIE, ?RBE; reflexivity]
       | |- a_space_beg _ = _ => exact SBE
       | |- boxed _ => assumption
       | |- _ \/ _ => first [ub TCX; exact Y | ub SCX; exact Y | ub TSP; exact Y]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold mfa; lia).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
  unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP in ER. cbv zeta in ER. fold mfa nf au mu1 in ER. rewrite FAE, RIE in ER.
  destruct ER as (FPLE & new & sj' & DISJ & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI2 & ST2 & REG2 & STATS2 & LSJ2 & AZ2 & MC2).
  box DISJ. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFJ.
  assert (SHF : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as [SHF1 SHF2].
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SHF1 SHF2 SP1 SP2 HC MFA NF NEWB NEWM T0 T1; lia).
  xport EXH MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SHF1 SHF2 SP1 SP2 HC MFA NF NEWB NEWM T0 T1 Y; lia).
  xport FJ MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SHF1 SHF2 SP1 SP2 HC MFA NF NEWB NEWM T0 T1 Y; lia).
  clear ST MI STATS LSJ REG AZF.
  pose proof MC2 as MC0. destruct MC0 as (PC2 & RC2 & TI2 & TK2 & T882 & TSD2 & CT2 & ISB2 & IREL2 & ISE2 & IPRE2). unfold ATP88, ATSD in T882, TSD2.
  clear TI TK T88 TSD CT ISB IREL ISE IPRE PC RC.
  (* [comment removed for export] *)
  assert (FALL : junk_at m2 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (4 * ncnt + (new - 4 * nf - 4 * ncnt))).
  { replace (4 * ncnt + (new - 4 * nf - 4 * ncnt)) with (new - 4 * nf) by (clear; lia).
    with_box DISJ ltac:(destruct DX as [(LE & Enew & _ & _)|(LT & Enew & _ & ZNEW & _)];
      [ exists fj; rewrite Enew; exact FJ
      | eexists;
        replace (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
           with (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + Z.of_nat (Z.to_nat (mfa - 4 * nf))) in ZNEW by (clear -MFA NF; lia);
        pose proof (cb_app m2 _ _ _ _ _ FJ ZNEW) as CA;
        replace (Z.to_nat (mfa - 4 * nf) + Z.to_nat (new - mfa))%nat with (Z.to_nat (new - 4 * nf)) in CA by (clear -MFA NF NEWM; lia);
        exact CA ]). }
  destruct (junk_split m2 _ _ _ FALL ltac:(clear -NC0; lia) ltac:(clear -NEWB; lia)) as [[bsw FW] JR]. clear FALL.
  pose proof (u8arr_of_rw_cells bsegs m2 _ _ _ FW) as U8.
  assert (LBS : length bsw = (4 * Z.to_nat ncnt)%nat).
  { destruct FW as [[WF _] _]. cbn in WF. clear -WF NC0. lia. }
  destruct (u32arr_of_u8arr bsegs m2 _ bsw (Z.to_nat ncnt) U8 LBS) as (ws & LWS & _ & AR). clear U8 FW LBS bsw.
  cbn [negb]. 
  replace (ret_pc (Z_to_bv 64 232584)) with (Z_to_bv 64 232584 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (FIN : forall m3 (s1y a0y a1y a2y a4y a5y : word),
    munch [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt)]%Z m2 m3 ->
    wmono bsegs m2 m3 -> mem_inv bsegs m3 ->
    u32arr bsegs m3 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (fvals au S (Z.to_nat ncnt)) ->
    evtF bsegs RNG' P
      (MS (mkR (Z_to_bv 64 0x38c88) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0' t1' t2'
               (Z_to_bv 64 (al_space_beg L + 137438953472 + c * 128)) s1y a0y a1y a2y (Z_to_bv 64 au) a4y a5y a6' a7'
               (Z_to_bv 64 (al_space_beg L + c * 4294967296)) (Z_to_bv 64 ncnt) (Z_to_bv 64 (mu1 - au)) (Z_to_bv 64 S)
               s6x s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x38cd0) fc None m3 (seg_rom bsegs)))
  end.
  { intros m3 s1y a0y a1y a2y a4y a5y MU3x WM3 MI3 AR3.
    xport FR MU3x WM3 ltac:(clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia).
    xport EXH MU3x WM3 ltac:(clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia).
    xport REG2 MU3x WM3 ltac:(clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia).
    xport STATS2 MU3x WM3 ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0 T0 T1 Y; lia).
    pose proof (stk_transport_disjoint bsegs _ m2 m3 _ _ ST2 MU3x WM3 ltac:(cbn [disjoint_from]; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia)) as ST3.
    clear ST2.
    assert (MU3 : munch [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt);
                         (al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56);
                         (al_space_beg L + 137438953472 + c * 128 + 68, al_space_beg L + 137438953472 + c * 128 + 69)]%Z m2 m3).
    { eapply munch_weaken; [| exact MU3x]. unfold sub_fp; cbn [outside]; clear -NEWB NC0; intros x Hx; lia. }
    clear MU3x.
    step.                                                      (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    zstep. zstep.                                              (* [comment removed for export] *)
    snapshot [(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56);
              (al_space_beg L + 137438953472 + c * 128 + 68, al_space_beg L + 137438953472 + c * 128 + 69)]%Z MUf WMf.
    box STATS2. box AR3.
    step. step.                                                (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3. { exfalso. clear -K3 NC1 NC0 MU MUX SZ. rewrite ?unsigned_lit in K3 by lia. lia. }   (* [comment removed for export] *)
    step. step. step. if_lit.                                  (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    step. step.                                                (* [comment removed for export] *)
    do 10 step.                                                (* [comment removed for export] *)
    carry STATS2 MUf WMf ltac:(rewrite LSJ2; ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y; lia).
    carry AR3 MUf WMf ltac:(rewrite fvals_length; clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM NC0; lia).
    lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -64) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
    (* [comment removed for export] *)
    rename MU3 into MU24. clear MUf. rename WM3 into WM24. clear WMf.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m4 _) =>
    assert (MU14 : munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp);
            (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + new);
            (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa), shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa));
            (al_t L + 2800, al_t L + 3168);
            (al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56);
            (al_space_beg L + 137438953472 + c * 128 + 68, al_space_beg L + 137438953472 + c * 128 + 69)]%Z m1 m4);
    [ eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU24]]; unfold sub_fp; cbn [outside]; clear -NEWB NC0 MFA NF; intros x Hx; lia |]
    end.
    pose proof (wmono_trans _ _ _ _ WM2 WM24) as WM14.
    assert (W24OK : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
       [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt);
        (al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56);
        (al_space_beg L + 137438953472 + c * 128 + 68, al_space_beg L + 137438953472 + c * 128 + 69)]%Z).
    { ub SCX. unfold AIMG_HI, AIMG_LO. do 3 (apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX0 CX1 SP1 SP2 HC MFA NF NEWB NC0 Y; lia |]). apply Forall_nil. }
    (* [comment removed for export] *)
    assert (ST2EQ : put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + ncnt * S) (cls_set_num_freed (nf + ncnt) (get_cls st2 c))) st2
                    = put_cls c (mkAClass mu1 (au + ncnt * S) (nf + ncnt) new (c_count (get_cls st1 c))) st).
    { with_box DISJ ltac:(destruct DX as [(LE & Enew & Est2 & _)|(LT & Enew & Est2 & _)]; rewrite Est2;
        [ rewrite PUTEQ, aclass_eta1, Enew; reflexivity
        | rewrite get_cls_put_cls_eq, put_cls_put_cls, PUTEQ, aclass_eta2; reflexivity ]). }
    apply evtF_done. rewrite ST2EQ. eapply KONT.
    unfold tail_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold S mu1 au nf mfa. fold ncnt. rewrite FAE, RIE.
    split; [exact FPLE|]. exists new, sj'.
    split. { with_box DISJ ltac:(destruct DX as [(LE & Enew & _ & Erng)|(LT & Enew & _ & _ & FILL & GR1 & GR2 & BW)];
             [ left; split; [exact LE| split; [exact Enew| exact Erng]]
             | right; split; [exact LT|]; split; [exact Enew|]; split; [| split; [exact GR1| split; [exact GR2| exact BW]]];
               eapply fill_frame; [exact FILL | exact MU24 | exact WM24 |];
               intros _; cbn [disjoint_from]; clear -SHF1 SHF2 SP1 SP2 HC NF MFA; lia ]). }
    split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|].
    split; [exact AR3|].
    split. { replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * (nf + ncnt)) with (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt) by (clear; lia).
             replace (new - 4 * (nf + ncnt)) with (new - 4 * nf - 4 * ncnt) by (clear; lia).
             eapply junk_frame; [exact JR | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from]; clear -SP1 SP2 HC NF MFA NEWB NC0; lia. }
    split; [reflexivity|].
    split; [exact MU14|]. split; [exact WM14|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [assumption|]. split; [exact STATS2|]. split; [exact LSJ2|].
    split. { eapply azero_frame; [exact AZ2 | exact MU24 | exact WM24 |]. intros _; cbn [disjoint_from].
             assert (SHT : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + new)
                        /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + new) + shlen (536870912 - new) <= 0x10007fff8000).
             { rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
             clear -SHT SP1 SP2 HC NF MFA. lia. }
    eapply m3_cells_frame; [exact MC2 | exact MU24 | exact WM24 | exact W24OK]. }
  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2.                            (* [comment removed for export] *)
  { assert (NC00 : ncnt = 0) by (subst ncnt; rewrite ?unsigned_lit in K2 by (clear -MU MUX SZ; lia); apply Z.div_small; clear -K2 MU; lia).
    rewrite NC00 in FIN |- *.
    eapply FIN; [ | apply wmono_refl | exact MI2 |].
    - replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * 0) with (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) by (clear; lia). apply munch_refl.
    - apply u32arr_nil; clear -SP1 SP2 HC NF MFA; lia. }
  assert (NCP : 0 < ncnt) by (subst ncnt; rewrite ?unsigned_lit in K2 by (clear -MU MUX SZ; lia); apply Z.div_str_pos; clear -K2 SZ; lia).
  step. step. zstep. zstep. zstep. zstep. step.                (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * ncnt)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; clear -NC0 NF; Z.div_mod_to_equations; lia).
  setreg 12 (Z_to_bv 64 (au + 0 * S)) ltac:(f_equal; clear; lia).
  eapply evtF_cut.
  { eapply (fill_loop_spec RNG' _ 0 ncnt _ au S ws); try reflexivity.
    - clear -NCP; lia.
    - rewrite LWS; clear; lia.
    - cbn [Z.to_nat fvals seq map rev]. rewrite app_nil_r. exact AR.
    - exact MI2.
    - clear -MU; lia.
    - clear -SZ; lia.
    - clear -NC1 MU MUX SP1 SP2 HC; lia.
    - clear -SP1 NF HC; lia.
    - clear -SP1 SP2 HC NF NEWB NC0; lia.
    - intros kk Hkk. assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia). destruct M4 as [q Hq].
      with_box DISJ ltac:(destruct DX as [(LE & Enew & _ & _)|(LT & Enew & _ & _ & _ & GR1 & _)];
        [ eapply rng_sub'; [exact RFJ|]; clear -Hkk LE MFA NF NC0; lia
        | destruct (Z_lt_le_dec (4 * nf + 4 * kk + 3) mfa) as [LO4|HI4];
          [ eapply rng_sub'; [exact RFJ|]; clear -Hkk LO4 MFA NF NC0; lia
          | eapply rng_sub'; [exact GR1|]; clear -Hkk HI4 MFA NF NC0 NEWB Hq; lia ] ]). }
  cbv beta. intros ms' (a4y & a5y & m3 & -> & MU3 & WM3 & MI3 & AR3).
  replace (Z_to_bv 64 (au + 0 * S)) with (Z_to_bv 64 au : word) by (f_equal; clear; lia).
  eapply FIN; [exact MU3 | exact WM3 | exact MI3 | exact AR3].
Qed.

(* [comment removed for export] *)
Definition populate_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c req lo : Z) (sj : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' : word),
     (* [comment removed for export] *)
     (   (au + req * S <= mu /\ mu' = mu)
      \/ (mu < au + req * S /\ mu' = mu + rup (au + req * S - mu) K_USER_MAP
          /\ rw_cells bsegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ncnt = (mu' - au) / S /\ 0 <= ncnt
     (* [comment removed for export] *)
  /\ (   (4 * (nf + ncnt) <= mfa /\ mfa' = mfa)
      \/ (mfa < 4 * (nf + ncnt) /\ mfa' = rup (4 * (nf + ncnt)) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * (nf + ncnt) <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ u32arr bsegs m' (FA + 4 * nf) (fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * (nf + ncnt)) (mfa' - 4 * (nf + ncnt))
     (* [comment removed for export] *)
  /\ st2 = put_cls c (mkAClass mu' (au + ncnt * S) (nf + ncnt) mfa' (c_count r)) st
     (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI + 16, RI + 56); (RI + 68, RI + 69)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf + ncnt)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (au + ncnt * S)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' (al_t L + 2792) [C8 stm']
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pop_map_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rax a1x a2x a3x a4x a5x s6x : word)
    (F : bvmap 5 word) fc (m1 : amem) (L : alayout) (st : astate) (c req lo : Z) (sj : list word) (stm : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
  mem_inv bsegs m1 -> tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m1 ->
  rw_cells bsegs m1 (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m1 (RI + 68) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m1 (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m1 (al_t L + 2792) [C8 stm] ->
  rw_cells bsegs m1 (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  azero m1 (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m1 (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0 <= req < 2^31 -> mu < au + req * S ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG (FA + 4 * nf) (mfa - 4 * nf) ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      populate_ret L RNG sp st c req lo sj m1 st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
  evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (populate_free_array st c req k)) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RI) (Z_to_bv 64 (al_t L + 2768)) (Z_to_bv 64 AINSTANCE)
             a1x a2x a3x a4x a5x a6 a7
             (Z_to_bv 64 RB) (Z_to_bv 64 (au + req * S)) (Z_to_bv 64 mu) (Z_to_bv 64 S) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38b94) fc None m1 (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP FR MC REG EXH STATS LSJ STM FJ AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM REQ LT
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFJ CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  rewrite RIE in REG, EXH, RRI |- *. rewrite RBE in AZU |- *. rewrite FAE in FJ, AZF, RFJ.
  set (total := au + req * S) in *.
  assert (TOT : mu < total < 2^48) by (subst total; clear -LT MU MUX REQ SZ; nia).
  pose proof (rup18_facts (total - mu) ltac:(clear -TOT; lia)) as (RU1 & RU2 & RU3).
  set (ums := rup (total - mu) 262144) in *.
  pose proof (munch_refl [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp)]%Z m1) as MUN.
  pose proof (wmono_refl bsegs m1) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (JOIN : forall a1z : word,
    evtF bsegs RNG P
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (al_space_beg L + 137438953472 + c * 128))
               (Z_to_bv 64 (al_t L + 2768)) (Z_to_bv 64 837272) a1z a2x a3x a4x a5x a6 a7
               (Z_to_bv 64 (al_space_beg L + c * 4294967296)) (Z_to_bv 64 total) (Z_to_bv 64 mu) (Z_to_bv 64 S) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x38b98) fc None m1 (seg_rom bsegs)))
  end.
  2:{ step. if_cases KZ; zify_cond KZ.                        (* [comment removed for export] *)
      - step. step. if_lit.                                   (* [comment removed for export] *)
        step. step.                                           (* [comment removed for export] *)
        rewrite ?unsigned_lit in KZ by (clear -MU MUX; lia). rewrite <- KZ. apply JOIN.
      - apply JOIN. }
  intros a1z.
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 19 (Z_to_bv 64 ums)
    ltac:(f_equal; rewrite zb_lxor_ones by (clear -MU MUX; lia);
          pose proof (Z.mod_pos_bound (total + (18446744073709551615 - mu)) 18446744073709551616 ltac:(clear; lia)) as B;
          rewrite land_align2p18 by exact B; subst ums; unfold rup; clear -TOT MU B; Z.div_mod_to_equations; lia).
  step. zstep. zstep. zstep. zstep.                            (* [comment removed for export] *)
  step. if_cases KX; zify_cond KX.                             (* [comment removed for export] *)
  { (* [comment removed for export] *)
    apply evtF_done. rewrite populate_unfold. cbv zeta. unfold K_FREEARR_OFF, K_USER_MAP. fold S mu au. fold total. fold ums.
    replace (total <=? mu) with false by (symmetry; apply Z.leb_gt; clear -TOT; lia).
    replace (3758096384 <? mu + ums) with true by (symmetry; apply Z.ltb_lt; rewrite ?unsigned_lit in KX by (clear -MU MUX RU1 TOT; lia); clear -KX MU RU1 TOT; lia).
    cbv beta iota. rewrite aembed_aundef_. apply implF_ret_unr. }
  assert (KX' : mu + ums <= 3758096384) by (rewrite ?unsigned_lit in KX by (clear -MU MUX RU1 TOT; lia); clear -KX MU RU1 TOT; lia). clear KX.
  lstep.                                                       (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 20 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + mu)) ltac:(f_equal; clear; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. zstep. step. step. step.                               (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. rewrite populate_unfold. cbv zeta. unfold K_FREEARR_OFF, K_USER_MAP. fold S mu au. fold total. fold ums.
  replace (total <=? mu) with false by (symmetry; apply Z.leb_gt; clear -TOT; lia).
  replace (3758096384 <? mu + ums) with false by (symmetry; apply Z.ltb_ge; exact KX').
  cbv beta iota. unfold ev. rewrite aembed_vis. cbn [aev_tree]. unfold PROT_RW, F_FIXED.
  unfold region_beg, K_REGION. change (2^32) with 4294967296. rewrite SBE.
  set (BEG := al_space_beg L + c * 4294967296 + mu) in *.
  assert (BEGF : BEG mod 4096 = 0 /\ 0x10007fff8000 <= BEG /\ BEG + ums <= al_space_beg L + c * 4294967296 + 3758096384 /\ ums mod 4096 = 0 /\ 0 < ums /\ BEG mod 8 = 0).
  { subst BEG. clear -SP1 SP3 HC MU MUM KX' RU1 RU2 TOT. Z.div_mod_to_equations. lia. }
  destruct BEGF as (BG1 & BG2 & BG3 & BG4 & BG5 & BG8).
  name_sp sp (-64).
  eapply rmap_spec with (addr := BEG) (size := ums) (lo := lo).
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite Hsp; eassumption
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => exact RC
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => assumption
       | |- 0 < _ => exact BG5
       end.
  all: try (unfold AIMG_HI; clear -BG1 BG2 BG3 BG4 BG5 SP2 CEIL LO HC; rewrite ?unsigned_lit by lia; lia).
  { (* [comment removed for export] *)
    intros a RNG' ms' NE P1 P2. unfold fixed_answer_ok, is_err, TWO64.
    replace (2 ^ 64 - 4096 <? a) with false by (symmetry; apply Z.ltb_ge; clear -P2 BG5; atop_facts; lia).
    replace (a =? BEG) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [negb orb]. rewrite aembed_aundef_. apply implF_ret_unr. }
  (* [comment removed for export] *)
  intros RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RP.
  destruct RP as (FPLE & _ & MU2 & WM2 & MI2 & ST2 & ZNEW & GR1 & GR2 & BW1 & RC2). unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFJ.
  assert (SHB : 0x2008fff7000 <= shad BEG /\ shad BEG + shlen ums <= 0x10007fff8000 /\ 0 < shlen ums
                /\ shad BEG + shlen ums = shad (BEG + ums) /\ shad (BEG + ums) + shlen (3758096384 - (mu + ums)) <= 0x10007fff8000
                /\ shad BEG + shlen (3758096384 - mu) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. subst BEG. clear -BG1 BG2 BG3 BG4 BG5 SP1 SP2 HC MU KX'. Z.div_mod_to_equations. lia. }
  destruct SHB as (SHB1 & SHB2 & SHB3 & SHB4 & SHB5 & SHB6).
  (* [comment removed for export] *)
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO BG2 BG3 SP2 HC; lia).
  xport REG MU2 WM2 ltac:(clear -SPR CEIL LO BG2 BG3 SP2 HC; lia).
  xport EXH MU2 WM2 ltac:(clear -SPR CEIL LO BG2 BG3 SP2 HC; lia).
  xport STATS MU2 WM2 ltac:(rewrite LSJ; ub TSP; clear -SPR CEIL LO BG2 BG3 SP2 HC T0 T1 MU Y TIC TB; subst BEG; lia).
  xport STM MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO BG2 BG3 SP2 HC T0 T1 MU Y TIC TB; subst BEG; lia).
  xport FJ MU2 WM2 ltac:(clear -SPR CEIL LO BG2 BG3 SP2 HC MFA NF; subst BEG; lia).
  assert (AZU2 : azero m2 (shad BEG) (shlen (3758096384 - mu))).
  { eapply azero_frame; [exact AZU | exact MU2 | exact WM2 |]. intros _; cbn [disjoint_from].
    clear -SPR CEIL LO SHB6 BG2. lia. }
  assert (AZF2 : azero m2 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa))).
  { eapply azero_frame; [exact AZF | exact MU2 | exact WM2 |]. intros _; cbn [disjoint_from].
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MFA NF. subst BEG. Z.div_mod_to_equations. lia. }
  clear ST MI.
  (* [comment removed for export] *)
  assert (MUW : munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp); (BEG, BEG + ums); (shad BEG, shad BEG + shlen ums);
                       (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
                       (al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56)]%Z m1 m2).
  { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  clear MU2 MUN.
  assert (WOK : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
                [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp); (BEG, BEG + ums); (shad BEG, shad BEG + shlen ums);
                 (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
                 (al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56)]%Z).
  { ub SCX. ub TCX. unfold AIMG_HI, AIMG_LO.
    do 6 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC SP1 SP2 HC MU BG2 BG3 SHB1 SHB2 SHB3 Y Y0 CXI TB; with_band CX0 ltac:(lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  assert (MC2 : m3_cells L m2) by (eapply m3_cells_frame; [exact MC | exact MUW | exact WM2 | exact WOK]).
  clear TI TK T88 TSD CT ISB IREL ISE IPRE PC RC.
  pose proof MC2 as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE). unfold ATP88, ATSD in T88, TSD.
  (* [comment removed for export] *)
  unfold fixed_answer_ok, is_err, TWO64. rewrite Z.eqb_refl.
  replace (2 ^ 64 - 4096 <? BEG) with false by (symmetry; apply Z.ltb_ge; clear -BG3 BG5 SP2 HC; lia). cbn [negb orb].
  replace (ret_pc (Z_to_bv 64 232468)) with (Z_to_bv 64 232468 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 BG2 BG3 SP2 HC. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. clear -K2. lia. }                                                 (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  pose proof (azero_cb m2 _ _ (shlen ums) AZU2 ltac:(rewrite !shlen_div; clear -MU KX' RU1 TOT; Z.div_mod_to_equations; lia)) as SHCB.
  step. with_band CX0 ltac:(with_band T0 ltac:(call_sp (poison_shadow_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BEG ums 250 lo))).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => exact PC
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => exact SHCB
       | |- rng _ (shad _) _ => exact GR2
       | |- rng _ _ _ => solve_rng
       end.
  all: try (atop_facts; clear -BG1 BG2 BG3 BG4 BG5 BG8 SP2 CEIL LO HC; rewrite ?shlen_div; first [lia | Z.div_mod_to_equations; lia]).
  all: try (unfold ablk; right; unfold K_SPACE_SIZE in *; clear -BG2 BG3 SP1 SP2 SP3 HC; lia).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-POISON" G end.
  (* [comment removed for export] *)
  step. with_band T0 ltac:(call_sp (thread_stats_spec RNG' (al_ctx L) (al_t L) lo)).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ _ => assumption
       | |- rng _ _ _ => solve_rng
       end.
  all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 CXI TIC TB; lia).
  aload STATS 9 (al_t L + 2800 + 72). aload STATS 10 (al_t L + 2800 + 80).
  zstep. zstep.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
  box CT. box REG. box ZNEW. box POST. box FR. box EXH. box STM. box FJ.
  astore STATS 9. astore STATS 10.
  carry CT MUs WMs ltac:(ub TCX; clear -CX0 CX1 T0 T1 Y TIC CXI TB; lia).
  carry REG MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
  carry ZNEW MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 MU BG2 BG3 BG5 Y TIC TB; subst BEG; lia).
  carry POST MUs WMs ltac:(clear -SHB1 SHB2 SHB3 T0 T1 TIC TB; with_band T0 lia).   (* [comment removed for export] *)
  carry FR MUs WMs ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry EXH MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
  carry STM MUs WMs ltac:(clear; lia).
  carry FJ MUs WMs ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 MFA NF Y TIC TB; lia).
  clear MUs WMs.
  step. zstep.                                                 (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 (al_t L + 2792)) ltac:(f_equal; clear; lia).
  assert (AMO : amo_aligned AD (Z_to_bv 64 (al_t L + 2792)) = true) by (apply amo_alignedD_intro; [clear -T0 T1 TIC TB; lia| clear -TAL; Z.div_mod_to_equations; lia]).
  snapshot [(al_t L + 2792, al_t L + 2800)]%Z MUa WMa.
  box CT. box REG. box ZNEW. box POST. box FR. box EXH. box FJ. box STATS.
  amo_stepA AMO.                                               (* [comment removed for export] *)
  carry CT MUa WMa ltac:(ub TCX; clear -CX0 CX1 T0 T1 Y TIC CXI TB; lia).
  carry REG MUa WMa ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
  carry ZNEW MUa WMa ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 MU BG2 BG3 BG5 Y TIC TB; subst BEG; lia).
  carry POST MUa WMa ltac:(clear -SHB1 SHB2 SHB3 T0 T1 TIC TB; with_band T0 lia).   (* [comment removed for export] *)
  carry FR MUa WMa ltac:(clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry EXH MUa WMa ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
  carry FJ MUa WMa ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 MFA NF Y TIC TB; lia).
  carry STATS MUa WMa ltac:(rewrite ?upd_length, LSJ; clear; lia).
  clear MUa WMa.
  step. step. zstep.                                           (* [comment removed for export] *)
  snapshot [(al_space_beg L + 137438953472 + c * 128 + 16, al_space_beg L + 137438953472 + c * 128 + 56)]%Z MUr WMr.
  box CT. box ZNEW. box POST. box FR. box STM. box FJ. box STATS.
  step.                                                        (* [comment removed for export] *)
  carry CT MUr WMr ltac:(ub SCX; clear -HC CX0 CX1 SP1 SP2 Y CXI; lia).
  carry ZNEW MUr WMr ltac:(clear -HC SP1 SP2 MU BG2 BG3 BG5; subst BEG; lia).
  carry POST MUr WMr ltac:(clear -SHB1 SHB2 SHB3 SP1 SP2 HC; lia).
  carry FR MUr WMr ltac:(clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry STM MUr WMr ltac:(ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
  carry FJ MUr WMr ltac:(clear -HC SP1 SP2 MFA NF; lia).
  carry STATS MUr WMr ltac:(rewrite ?upd_length, LSJ; ub TSP; clear -HC T0 T1 SP1 SP2 Y TIC TB; lia).
  clear MUr WMr.
  (* [comment removed for export] *)
  set (st1 := put_cls c (cls_set_mapped_user (mu + ums) (get_cls st c)) st) in *.
  assert (GC : get_cls st1 c = cls_set_mapped_user (mu + ums) (get_cls st c)) by (apply get_cls_put_cls_eq).
  replace (Z_to_bv 64 (mu + ums)) with (Z_to_bv 64 (c_mapped_user (get_cls st1 c)) : word) by (rewrite GC; reflexivity).
  replace (Z_to_bv 64 au) with (Z_to_bv 64 (c_allocated_user (get_cls st1 c)) : word) by (rewrite GC; reflexivity).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (m3_cells_frame L m1 mm _ MC MUW WM2 WOK) as MC3 end.
  eapply pop_tail_spec with (lo := lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => eassumption
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC3
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => rewrite RIE; by_GC GC; exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => rewrite RIE; exact EXH
       | |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; by_GC GC; exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => rewrite ?upd_length; exact LSJ
       | |- azero _ _ _ => rewrite FAE; by_GC GC; unfold K_FREEARR_MAX; eapply azero_frame; [exact AZF | exact MUW | exact WM2 |];
                            intros _; cbn [disjoint_from]; rewrite !shad_div, !shlen_div in *; unfold ASHOFF in *;
                            clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MFA NF T0 TB MU TIC; subst BEG; Z.div_mod_to_equations; lia
       | |- (forall r', put_cls _ r' _ = put_cls _ r' _) => intros r'; apply put_cls_put_cls
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => rewrite RIE; exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; by_GC GC; exact RFJ
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (by_GC GC; unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold S mu au nf mfa; first [assumption | clear -MU MUX KX' RU1 TOT AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]).
  (* [comment removed for export] *)
  intros st2 RNG'' m'' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' TR.
  eapply KONT.
  unfold tail_ret in TR. rewrite GC in TR. cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count cls_set_mapped_user] in TR.
  fold mu au nf mfa in TR. fold S in TR. rewrite FAE, RIE in TR. unfold K_FREEARR_MAX, K_FREEARR_MAP in TR.
  destruct TR as (FPLE2 & mfa' & sj'' & FDISJ & NEWB & NEWM & NEWMOD & AR & JR & ST2EQ & MUT & WMT & MIT & STT & REGT & EXHT & STATST & LSJT & AZT & MCT).
  box FDISJ.
  unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold S mu au nf mfa. rewrite FAE, RIE, RBE. fold total. fold ums. fold BEG.
  split; [eapply fp_le_trans; [exact FPLE | exact FPLE2]|].
  lazymatch type of STM with rw_cells _ _ _ [C8 ?w] => exists (mu + ums), mfa', ((mu + ums - au) / S), sj'', w end.
  replace (mu + ums - mu) with ums by (clear; lia).
  replace (al_space_beg L + c * 4294967296 + (mu + ums)) with (BEG + ums) by (subst BEG; clear; lia).
  (* [comment removed for export] *)
  assert (DJU : forall lo' hi', (hi' <= BEG \/ BEG + ums <= lo') -> (hi' <= shad BEG \/ shad BEG + shlen ums <= lo') ->
                 (hi' <= al_t L + 2792 \/ al_t L + 2800 <= lo') -> True) by (intros; exact I).
  assert (BW2 : fp_bw RNG'').
  { with_box FDISJ ltac:(destruct DX as [(_ & _ & Erng)|(_ & _ & _ & _ & _ & BWx)]; [rewrite Erng; exact BW1| exact BWx]). }
  split. { right. split; [exact LT|]. split; [reflexivity|].
           split; [| split; [| split; [eapply rng_fp_le; [exact FPLE2| exact GR1] | split; [eapply rng_fp_le; [exact FPLE2| exact GR2]| exact BW2]]]].
           - eapply cells_frame; [exact ZNEW | exact MUT | exact WMT |].
             cbn [disjoint_from cells_size csize Nat.add]. rewrite ?Z2Nat.id by (clear -BG5; lia).
             ub TSP. clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MU MFA NF NEWB NEWM T0 T1 SHB1 SHB2 Y TIC TB. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. subst BEG.
             Z.div_mod_to_equations. lia.
           - eapply fill_frame; [exact POST | exact MUT | exact WMT |]. intros _. cbn [disjoint_from].
             ub TSP. clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MU MFA NF NEWB NEWM T0 T1 SHB1 SHB2 SHB3 Y TIC TB. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. subst BEG.
             Z.div_mod_to_equations. lia. }
  split; [clear -KX' BG5; lia|]. split; [clear -MUM RU2; Z.div_mod_to_equations; lia|].
  split; [reflexivity|]. split; [apply Z.div_pos; clear -MU BG5 SZ; lia|].
  split; [with_box FDISJ ltac:(destruct DX as [(LE & Emfa & _)|RR]; [left; split; [exact LE| exact Emfa] | right; exact RR])|]. split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|].
  split; [exact AR|]. split; [exact JR|]. split; [exact ST2EQ|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MUW] | eapply munch_weaken; [| exact MUT]]; unfold sub_fp; cbn [outside]; subst BEG;
           clear -NEWB NEWM MFA NF BG5; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM2 | exact WMT]|]. split; [exact MIT|]. split; [exact STT|].
  split; [exact REGT|]. split; [exact EXHT|]. split; [exact STATST|]. split; [exact LSJT|].
  split. { eapply cells_frame; [exact STM | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
           ub TSP. clear -SPR CEIL LO SP1 SP2 HC MFA NF NEWB NEWM T0 T1 Y TIC TB. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  split. { (* [comment removed for export] *)
           pose proof (azero_split m1 _ _ (shlen ums) AZU ltac:(rewrite !shlen_div; clear -KX' BG5 MU; Z.div_mod_to_equations; lia)) as AZT'.
           rewrite SHB4 in AZT'.
           replace (shlen (3758096384 - mu) - shlen ums) with (shlen (3758096384 - (mu + ums))) in AZT'
             by (rewrite !shlen_div; clear -MUM RU2 BG4; Z.div_mod_to_equations; lia).
           eapply azero_frame; [eapply azero_frame; [exact AZT' | exact MUW | exact WM2 |] | exact MUT | exact WMT |];
             intros _; cbn [disjoint_from]; ub TSP; clear -SPR CEIL LO BG2 BG3 BG5 SP1 SP2 HC MU MFA NF NEWB NEWM T0 T1 SHB1 SHB2 SHB3 SHB4 SHB5 KX' Y TIC TB;
             rewrite !shad_div, !shlen_div in *; unfold ASHOFF in *; subst BEG; Z.div_mod_to_equations; lia. }
  split; [exact AZT | exact MCT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma populate_ret_pre : forall L RNG sp st c req lo sj m m1 st2 RNG' m',
  munch [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp)]%Z m m1 -> wmono bsegs m m1 ->
  populate_ret L RNG sp st c req lo sj m1 st2 RNG' m' -> populate_ret L RNG sp st c req lo sj m st2 RNG' m'.
Proof.
  intros until m'. intros MU0 WM0 PR. unfold populate_ret in *. cbv zeta in PR. cbv zeta.
  destruct PR as (FP & mu' & mfa' & ncnt & sj' & stm' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & MU & WM & REST).
  split; [exact FP|]. exists mu', mfa', ncnt, sj', stm'.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU0] | exact MU]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM0 | exact WM]|]. exact REST.
Qed.

Lemma tail_to_populate : forall L RNG (sp : word) st c req lo sj m1 (stm : word) st2 RNG' m',
  let r := get_cls st c in let S := size_of_class c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  au + req * S <= mu -> 0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> 0 < S ->
  0 <= nf -> 4 * nf <= mfa -> 1 <= c < K_NUM_CLASSES ->
  ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rw_cells bsegs m1 (al_t L + 2792) [C8 stm] ->
  azero m1 (shad (aregion L c + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  tail_ret L RNG sp st st c lo m1 st2 RNG' m' -> populate_ret L RNG sp st c req lo sj m1 st2 RNG' m'.
Proof.
  intros until m'. cbv zeta. intros LE MU MUX MUM SZ NF MFA HC CEIL LO SP1 SP2 SP3 T0 T1 TSP STM AZU TIC TR. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  unfold K_NUM_CLASSES, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472 in *.
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  unfold tail_ret, K_FREEARR_MAX, K_FREEARR_MAP in TR. cbv zeta in TR. rewrite FAE, RIE in TR.
  destruct TR as (FP & mfa' & sj' & FDISJ & NEWB & NEWM & NEWMOD & AR & JR & ST2EQ & MUT & WMT & MIT & STT & REGT & EXHT & STATST & LSJT & AZT & MCT).
  unfold populate_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. rewrite FAE, RBE, RIE. rewrite RBE in AZU.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (S := size_of_class c) in *.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + mu) + shlen (3758096384 - mu) <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)
                /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000
                /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).   (* [comment removed for export] *)
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -MU MUX MUM NF MFA NEWB NEWM HC SP1 SP2 SP3. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  split; [exact FP|]. exists mu, mfa', ((mu - au) / S), sj', stm.
  split; [left; split; [exact LE| reflexivity]|].
  split; [clear -MU MUX; lia|]. split; [exact MUM|]. split; [reflexivity|]. split; [apply Z.div_pos; clear -MU SZ; lia|].
  split; [destruct FDISJ as [(LE2 & Emfa & _)|RR]; [left; split; [exact LE2| exact Emfa] | right; exact RR]|].
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|].
  split; [exact AR|]. split; [exact JR|]. split; [exact ST2EQ|].
  split. { eapply munch_weaken; [| exact MUT]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [exact WMT|]. split; [exact MIT|]. split; [exact STT|]. split; [exact REGT|]. split; [exact EXHT|]. split; [exact STATST|]. split; [exact LSJT|].
  split. { eapply cells_frame; [exact STM | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
           clear -CEIL LO SP1 SP2 HC NF MFA NEWB NEWM T0 T1 TSP SHF2 SHF4 TIC TB. pose proof (bv_unsigned_in_range 64 sp). lia. }
  split. { eapply azero_frame; [exact AZU | exact MUT | exact WMT |]. intros _. cbn [disjoint_from].
           assert (SLO : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + mu)) by (rewrite shad_div; unfold ASHOFF; clear -SP1 HC MU; Z.div_mod_to_equations; lia).
           clear -CEIL LO SP1 SP2 HC NF MFA NEWB NEWM T0 T1 TSP SHF1 SHF2 SHF3 SLO MU TIC TB. pose proof (bv_unsigned_in_range 64 sp). lia. }
  split; [exact AZT | exact MCT].
Qed.

Lemma populate_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c req lo : Z) (sj : list word) (stm : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 RI -> a4 = Z_to_bv 64 req ->
  m3_cells L m ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0 <= req < 2^31 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG (FA + 4 * nf) (mfa - 4 * nf) ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      populate_ret L RNG sp st c req lo sj m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (populate_free_array st c req k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 populate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> -> MC REG EXH STATS LSJ STM FJ AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM REQ
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFJ CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, populate_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - POPULATE_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl bsegs m) as WM.
  set (total := au + req * S).
  assert (TOTB : 0 <= total < 2^48) by (subst total; clear -MU MUX REQ SZ; nia).
  iprefix.
  carve_frame 64%nat ST.
  do 9 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  rewrite RIE in REG, EXH, RRI |- *. rewrite RBE in AZU. rewrite FAE in FJ, AZF, RFJ.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZU1 : azero m1 (shad (al_space_beg L + c * 4294967296 + mu)) (shlen (3758096384 - mu)));
    [ eapply azero_frame; [exact AZU | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia |];
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MUN | exact WM |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia |]
  end.
  clear AZU AZF.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P (MS _ _ _ _ _ ?m1 _) =>
  assert (MAPK : forall a1x a2x a3x a4x a5x a6x : word, mu < total ->
    evtF bsegs RNG P
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (al_space_beg L + 137438953472 + c * 128))
               (Z_to_bv 64 (al_t L + 2768)) (Z_to_bv 64 837272) a1x a2x a3x a4x a5x a6x a7
               (Z_to_bv 64 (al_space_beg L + c * 4294967296)) (Z_to_bv 64 total) (Z_to_bv 64 mu) (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x38b94) fc None m1 (seg_rom bsegs)));
  [ intros a1x a2x a3x a4x a5x a6x KM;
    eapply pop_map_spec with (lo := lo) (L := L) (st := st);
    try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => eassumption
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => eapply m3_cells_frame; [exact MC | exact MUN | exact WM | apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1 CXI; unfold AIMG_HI; lia | apply Forall_nil]]
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => rewrite RIE; exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => rewrite RIE; exact EXH
       | |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (aregion _ _ + _)) _ => rewrite RBE; exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => rewrite RIE; exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; exact RFJ
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => intros * PR; eapply KONT; eapply populate_ret_pre; [exact MUN | exact WM | exact PR]
       end;
    unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
    clear KONT; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM REQ KM LO HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]
  | ]
  end.
  lazymatch goal with |- evtF _ _ ?P (MS _ _ _ _ _ ?m1 _) =>
  assert (TAILK : forall s1x s3x a1x a2x a4x a5x a6x : word, total <= mu ->
    evtF bsegs RNG P
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 (al_space_beg L + 137438953472 + c * 128))
               s1x (Z_to_bv 64 837272) a1x a2x (Z_to_bv 64 au) a4x a5x a6x a7
               (Z_to_bv 64 (al_space_beg L + c * 4294967296)) s3x (Z_to_bv 64 mu) (Z_to_bv 64 S) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x38c68) fc None m1 (seg_rom bsegs)));
  [ intros s1x s3x a1x a2x a4x a5x a6x KM;
    eapply evtF_mono;
    [ eapply pop_tail_spec with (lo := lo) (L := L) (st := st) (st1 := st);
      try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => eassumption
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => eapply m3_cells_frame; [exact MC | exact MUN | exact WM | apply Forall_cons; [cbn [fst snd]; clear -CEIL LO CX1 CXI; unfold AIMG_HI; lia | apply Forall_nil]]
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => rewrite RIE; exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => rewrite RIE; exact EXH
       | |- rw_cells _ _ (afreearr _ _ + _) _ => rewrite FAE; exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- (forall r', put_cls _ r' _ = put_cls _ r' _) => intros r'; reflexivity
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => rewrite RIE; exact RRI
       | |- rng _ (afreearr _ _ + _) _ => rewrite FAE; exact RFJ
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => intros * TR; eapply KONT; eapply populate_ret_pre; [exact MUN | exact WM |];
                             eapply tail_to_populate; try eassumption; try (first [unboxed TSP | rewrite RBE; exact AZU1 | atop_facts; exact CEIL]);
                             unfold K_NUM_CLASSES, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
                             clear -MU MUX MUM NF MFA HC KM LO SZ SP1 SP2 SP3 T0 T1 TIC TB; lia
       end;
      unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
      clear KONT; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM REQ KM LO HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC CXI TB; lia]
    | cbv beta; intros ms' H; rewrite populate_unfold; cbv zeta; fold S mu au; fold total;
      replace (total <=? mu) with true by (symmetry; apply Z.leb_le; exact KM); exact H ]
  | ]
  end.
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases K31; zify_cond K31.                           (* [comment removed for export] *)
  1: step.                                                     (* [comment removed for export] *)
  1: setreg 21 (Z_to_bv 64 S) ltac:(subst S; rewrite K31; reflexivity).
  2: step; step; if_cases K16; zify_cond K16.                  (* [comment removed for export] *)
  2: do 9 zstep.                                               (* [comment removed for export] *)
  2: setreg 21 (Z_to_bv 64 S) ltac:(subst S; symmetry; apply size_formula; clear -K16 K31 HC; lia).
  3: zstep.                                                    (* [comment removed for export] *)
  3: setreg 21 (Z_to_bv 64 S) ltac:(subst S; unfold size_of_class; replace (c <=? 16) with true by (symmetry; apply Z.leb_le; clear -K16; lia);
                                   rewrite Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  all: step; step.                                             (* [comment removed for export] *)
  all: zstep; zstep; zstep.                                    (* [comment removed for export] *)
  all: setreg 19 (Z_to_bv 64 total) ltac:(subst total; apply Z_to_bv_eqm; clear -REQ SZ MU MUX; Z.div_mod_to_equations; nia).
  all: setreg 18 (Z_to_bv 64 (al_space_beg L + c * 4294967296)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  all: step; if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by (clear -MU MUX TOTB; lia).   (* [comment removed for export] *)
  - apply MAPK. exact KM.
  - step. apply TAILK. exact KM.                               (* [comment removed for export] *)
  - apply TAILK. exact KM.
  - apply MAPK. exact KM.
  - apply MAPK. exact KM.
  - step. apply TAILK. exact KM.                               (* [comment removed for export] *)
Qed.
End CANSEC2.
