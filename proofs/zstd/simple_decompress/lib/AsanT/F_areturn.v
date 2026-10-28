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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 AKitR ARep ARepKit ARepFrame RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_agetfrom F_amaybe.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
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
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
Definition rta_entry : Z := 0x36490.
End CANSEC1.
Notation RTA_STACK := 576 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma rta_copy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u32arr bsegs m SRC src -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  u32arr bsegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv bsegs m ->
  0 <= SRC -> SRC + 4 * n < 2^47 -> 0 <= DST -> DST + 4 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 4 * n <= DST \/ DST + 4 * Z.of_nat (length ws0) <= SRC) ->
  (forall k, 0 <= k < n -> rng RNG (SRC + 4 * k) 4) -> (forall k, 0 <= k < n -> rng RNG (DST + 4 * k) 4) ->
  evtF bsegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1' a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * n)) s7 s8 (Z_to_bv 64 (DST + 4 * n)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36620) fc None m' (seg_rom bsegs)
      /\ munch [(DST, DST + 4 * n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ u32arr bsegs m' SRC src /\ u32arr bsegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SRC + 4 * n)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 (SRC + 4 * i)) s7 s8 (Z_to_bv 64 (DST + 4 * i)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3660c) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA SM DSTA MI S0 S1 D0 D1 DJ RS RDS; [lia|].
  pose proof (munch_refl [(DST, DST + 4 * n)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  pose proof (proj1 (Forall_forall _ _) SM w (nth_error_In _ _ NTH)) as W31. cbv beta in W31.
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u32arr_read bsegs _ _ src i w (wa (SRC + 4 * i)) SRCA NTH ltac:(lia) eq_refl) as RD.
  pose proof (RS i ltac:(lia)) as RS1. pose proof (RDS i ltac:(lia)) as RD1.
  step. clear RD RS1.                                    (* [comment removed for export] *)
  rewrite (sx32_small w W31).
  zstep.                                                 (* [comment removed for export] *)
  setreg 22 (Z_to_bv 64 (SRC + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u32arr_store_ok bsegs m DST _ i (wa (DST + 4 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le4 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u32arr_write bsegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 4 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  clear DSTA. store_done. try clear SOK. clear RD1.
  zstep.                                                 (* [comment removed for export] *)
  setreg 25 (Z_to_bv 64 (DST + 4 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (a1' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists a1', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    split; [assumption|]. rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

Lemma junk_of_cells' : forall m A cs n, rw_cells bsegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof. intros m A cs n H <-. apply junk_of_cells. exact H. Qed.

Lemma set_mfa_eq : forall v r,
  cls_set_mapped_free_array v r = mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) v (c_count r).
Proof. intros v []; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rta_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c n SRC lo : Z) (src : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st c in let FA := afreearr L c in let RI := aregion_info L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let nf2 := nf + n in
  fp_le RNG RNG' /\
  exists mfa' sj',
     (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ get_cls st2 c = mkAClass (c_mapped_user r) (c_allocated_user r) nf mfa' (c_count r)
  /\ (st2 = st \/ st2 = put_cls c (get_cls st2 c) st)
  /\ munch [(bv_unsigned sp - RTA_STACK, bv_unsigned sp);
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 nf2); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)]
  /\ junk_at m' (RI + 72) 56
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ u32arr bsegs m' (FA + 4 * nf) src
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma rta_spec : forall RNG {R} (kb : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c n SRC lo : Z) (sj src : list word),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RTA_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c -> a4 = Z_to_bv 64 SRC -> a5 = Z_to_bv 64 n ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  u32arr bsegs m SRC src -> length src = Z.to_nat n -> Forall (fun w : word => bv_unsigned w < 2^31) src ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES -> 1 <= n <= 16 ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + n) <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  al_t L + 208 <= SRC -> SRC + 4 * n <= al_t L + 2768 ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      rta_ret L RNG sp st c n SRC lo src m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (kb st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (ensure_free_array st c (nf + n) kb)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rta_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until src. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG J72 STATS LSJ CH LCH CH31 FJ AZF SBE HC N NF MFA MFAM NFN
         SP1 SP2 SP3 CX0 CX1 T0 T1 TCX SCX TSP CHK0 CHK1 RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  box TCX. box SCX. box TSP.
  pose proof MC as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, rta_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  pose proof (munch_refl [(bv_unsigned sp - RTA_STACK, bv_unsigned sp)]%Z m) as MUN.
  pose proof (wmono_refl bsegs m) as WM.
  rewrite FAE in FJ, AZF, RFA.
  (* [comment removed for export] *)
  destruct (junk_split m (aregion_info L c + 72) 8 48 J72 ltac:(lia) ltac:(lia)) as [J72a J80].
  destruct (junk_split m (aregion_info L c + 72 + 8) 8 40 J80 ltac:(lia) ltac:(lia)) as [J80a J88].
  destruct (junk_split m (aregion_info L c + 72 + 8 + 8) 8 32 J88 ltac:(lia) ltac:(lia)) as [J88a J96].
  replace (aregion_info L c + 72 + 8) with (aregion_info L c + 80) in J80a by lia.
  replace (aregion_info L c + 72 + 8 + 8) with (aregion_info L c + 88) in J88a by lia.
  replace (aregion_info L c + 72 + 8 + 8 + 8) with (aregion_info L c + 96) in J96 by lia.
  destruct (c8_of_junk m _ J72a) as [stn STN]. destruct (c8_of_junk m _ J80a) as [w80 W80]. destruct (c8_of_junk m _ J88a) as [w88 W88].
  destruct J96 as [j96 J96].
  clear J72 J72a J80 J80a J88 J88a.
  iprefix.
  carve_frame 128%nat ST.
  snapshot [(bv_unsigned sp - 128, bv_unsigned sp)]%Z MUp WMp.
  box MTX. box REG. box STN. box W80. box W88. box J96. box STATS. box CH. box FJ. box AZF.
  box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
  do 14 step.                                                  (* [comment removed for export] *)
  carry MTX MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W80 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W88 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry J96 MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry CH MUp WMp ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 N TIC TB; lia).
  carry TI MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TK MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry T88 MUp WMp ltac:(clear -SPR CEIL LO; lia). carry TSD MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry CT MUp WMp ltac:(clear -SPR CEIL LO CX0 CX1 CXI; lia). carry ISB MUp WMp ltac:(clear -SPR CEIL LO; lia).
  carry IREL MUp WMp ltac:(clear -SPR CEIL LO; lia). carry ISE MUp WMp ltac:(clear -SPR CEIL LO; lia). carry IPRE MUp WMp ltac:(clear -SPR CEIL LO; lia).
  clear MUp WMp.
  do 7 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 9 zstep.                                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 25 (Z_to_bv 64 (al_space_beg L + c * 4294967296 + 3758096384)) ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  setreg 12 (Z_to_bv 64 (aregion L c)) ltac:(rewrite RBE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 4 zstep.                                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (aregion_info L c)) = true)
    by (apply amo_alignedD_intro; [rewrite RIE; clear -SP1 SP2 HC; lia| rewrite RIE; clear -SP3; Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  box MUN. snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUl WMl.
  box CT. box CH. box STATS.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry CT MUl WMl ltac:(ub SCX; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia).
  carry CH MUl WMl ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry STATS MUl WMl ltac:(rewrite LSJ; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  unbox MUN.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MU01 : munch [(bv_unsigned sp - RTA_STACK, bv_unsigned sp); (aregion_info L c, aregion_info L c + 8)]%Z m m1)
      by (eapply munch_trans; [eapply munch_weaken; [| exact MUN] | eapply munch_weaken; [| exact MUl]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia)
  end.
  rename WM into WM01. clear MUN MUl WMl.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (MC1 : m3_cells L m1);
    [ eapply m3_cells_frame; [exact MC | exact MU01 | exact WM01 |]; ub SCX; unfold AIMG_HI, AIMG_LO;
      do 2 (apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |]
  end.
  unbox FJ. eapply junk_frame in FJ; [| exact MU01 | exact WM01 | intros _; cbn [disjoint_from]; clear -SPR CEIL LO SP1 SP2 HC RIE NF MFA; lia].
  unbox AZF.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (AZF1 : azero m1 (shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)) (shlen (536870912 - mfa)));
    [ eapply azero_frame; [exact AZF | exact MU01 | exact WM01 |]; intros _; cbn [disjoint_from];
      rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC MFA NF RIE; Z.div_mod_to_equations; lia |]
  end.
  clear AZF.
  box MU01.
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done.
  name_sp sp (-128).
  eapply ensure_spec with (lo := lo) (L := L) (sj := sj);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => rewrite FAE; exact AZF1
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; solve_rng
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; fold mu au nf mfa; first [assumption | clear -NF MFA MFAM NFN N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
  unfold ensure_ret, K_FREEARR_MAX, K_FREEARR_MAP in ER. cbv zeta in ER. fold nf mfa in ER. rewrite FAE in ER.
  destruct ER as (FPLE & new & sj' & UD & NEWB & NEWGE & NEWM & MU2 & WM2 & MI2 & ST2 & REG2 & STATS2 & LSJ2 & AZF2 & MC2).
  box UD. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RRI. apply (rng_fp_le _ _ _ _ FPLE) in RFA.
  assert (SHF : shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa) + shlen (new - mfa) <= 0x10007fff8000).
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF NEWB NEWGE. Z.div_mod_to_equations. lia. }
  assert (SHFL : 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + mfa)).   (* [comment removed for export] *)
  { rewrite !shad_div. unfold ASHOFF. clear -SP1 SP2 HC MFA NF. Z.div_mod_to_equations. lia. }
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF TIC TB SHFL; lia).
  xport MTX MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport STN MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport W80 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport W88 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport J96 MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia).
  xport CH MU2 WM2 ltac:(rewrite LCH; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF CHK0 CHK1 N Y TIC TB SHFL; lia).
  eapply junk_frame in FJ; [| exact MU2 | exact WM2 | intros _; cbn [disjoint_from]; ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE T0 T1 NF MFA NEWB NEWGE SHF Y TIC TB SHFL; lia].
  clear ST MI REG STATS MC1 AZF1 CT TI TK T88 TSD ISB IREL ISE IPRE PC RC MC.
  (* [comment removed for export] *)
  assert (JD : junk_at m2 (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) (new - 4 * nf)).
  { ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & ZCB & _)].
    - rewrite E. exact FJ.
    - replace (new - 4 * nf) with ((mfa - 4 * nf) + (new - mfa)) by (clear; lia).
      apply junk_merge; [exact FJ | | clear -MFA; lia | clear -NEWGE; lia].
      replace (al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + (mfa - 4 * nf)) with (al_space_beg L + c * 4294967296 + 3758096384 + mfa) by (clear; lia).
      eapply junk_of_cb. exact ZCB. }
  clear FJ.
  destruct (junk_split m2 _ (4 * n) (new - 4 * nf - 4 * n) ltac:(eapply junk_at_eq; [exact JD| reflexivity | clear; lia]) ltac:(clear -N; lia) ltac:(clear -NEWB; lia)) as [JD4 JR].
  destruct (u32arr_of_junk m2 _ n JD4 ltac:(clear -N; lia)) as (ws0 & U0 & L0). clear JD JD4.
  set (DST := al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf) in *.
  replace (ret_pc (Z_to_bv 64 222708)) with (Z_to_bv 64 222708 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN. { exfalso. clear -KN N. rewrite ?unsigned_lit in KN by lia. lia. }   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 25 (Z_to_bv 64 (DST + 4 * 0)) ltac:(subst DST; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 10 (Z_to_bv 64 (SRC + 4 * n)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear; lia).
  setreg 22 (Z_to_bv 64 (SRC + 4 * 0)) ltac:(f_equal; clear; lia).
  eapply evtF_cut.
  { eapply (rta_copy_loop_spec RNG' _ 0 n SRC DST src ws0); try reflexivity.
    - clear -N; lia.
    - exact LCH.
    - rewrite L0. clear -N; lia.
    - exact CH.
    - exact CH31.
    - cbn [Z.to_nat firstn skipn app]. exact U0.
    - exact MI2.
    - clear -CHK0 T0 TIC TB; lia.
    - clear -CHK1 T1 N TIC TB; lia.
    - subst DST. clear -SP1 HC NF; lia.
    - subst DST. rewrite L0, Z2Nat.id by (clear -N; lia). clear -SP2 HC NF N NEWB MFA; lia.
    - subst DST. rewrite L0, Z2Nat.id by (clear -N; lia). ub TSP. clear -Y CHK0 CHK1 T0 T1 SP1 SP2 HC NF N NEWB MFA TIC TB. destruct Y as [Y|Y]; [left; lia| right; lia].
    - intros kk Hkk. eapply rng_sub'; [exact RT|]. clear -CHK0 CHK1 Hkk N; lia.
    - intros kk Hkk. subst DST. destruct (Z_lt_le_dec (4 * nf + 4 * kk) mfa) as [LT|GE].
      + eapply rng_sub'; [exact RFA|]. assert (M4 : exists q, mfa = 4 * q) by (exists (mfa / 4); clear -MFAM; Z.div_mod_to_equations; lia).
        destruct M4 as [q Hq]. clear -LT Hkk NF Hq. lia.
      + ub UD. destruct Y as [(_ & E & _ & _)|(_ & _ & _ & _ & _ & R1 & _)].
        * exfalso. clear -E GE Hkk NEWB. lia.
        * eapply rng_sub'; [exact R1|]. clear -GE Hkk NEWB. lia. }
  cbv beta. intros ms' (a1x & m3 & -> & MU3 & WM3 & MI3 & SR3 & DS3).
  xport FR MU3 WM3 ltac:(subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia).
  xport MTX MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport STN MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport W80 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport W88 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport J96 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport REG2 MU3 WM3 ltac:(subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  xport STATS2 MU3 WM3 ltac:(rewrite LSJ2; subst DST; ub TSP; clear -SP1 SP2 HC T0 T1 NF N NEWB Y TIC TB; lia).
  eapply junk_frame in JR; [| exact MU3 | exact WM3 | intros _; cbn [disjoint_from]; subst DST; clear -NF N; lia].
  pose proof (stk_transport_disjoint bsegs _ m2 m3 _ _ ST2 MU3 WM3 ltac:(cbn [disjoint_from]; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia)) as ST3.
  assert (AZF3 : azero m3 (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new))).
  { eapply azero_frame; [exact AZF2 | exact MU3 | exact WM3 |]. intros _; cbn [disjoint_from].
    rewrite shad_div, shlen_div; unfold ASHOFF; subst DST; clear -SP1 SP2 HC NF N NEWB; Z.div_mod_to_equations; lia. }
  assert (MC3 : m3_cells L m3).
  { eapply m3_cells_frame; [exact MC2 | exact MU3 | exact WM3 |]. ub SCX; unfold AIMG_HI, AIMG_LO.
    apply Forall_cons; [cbn [fst snd]; subst DST; clear -CX0 CX1 SP1 SP2 HC NF N NEWB Y CXI; lia |]. apply Forall_nil. }
  clear ST2 MI2 AZF2 MC2 U0. box MU3. box MU2.
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  snapshot [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88)]%Z MUs WMs.
  box SR3. box DS3. box STATS2. clear CH.
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  carry SR3 MUs WMs ltac:(rewrite LCH; ub TSP; clear -SP1 SP2 HC RIE T0 T1 CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUs WMs ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUs WMs ltac:(rewrite LSJ2; ub TSP; clear -SP1 SP2 HC RIE T0 T1 Y TIC TB; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (MC4 : m3_cells L mm) ; [eapply m3_cells_frame; [exact MC3 | exact MUs | exact WMs |]; ub SCX; unfold AIMG_HI, AIMG_LO;
    do 2 (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 SP1 SP2 HC RIE Y CXI; lia |]); apply Forall_nil |] end.
  eapply junk_frame in JR; [| exact MUs | exact WMs | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia].
  clear MC3. box MUs.
  (* [comment removed for export] *)
  step. step. step. step.                                      (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  box SR3. box DS3. box STATS2. box MTX. box STN. box W88. box J96. box REG2. box W80.
  snapshot [(bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)]%Z MUm WMm.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of REG2 with boxed (rw_cells _ _ _ [C8 _; C8 _; C8 (Z_to_bv 64 ?auv); C8 _; C8 (Z_to_bv 64 ?muv); C8 _]) =>
    lazymatch type of W80 with boxed (rw_cells _ _ _ [C8 ?w80v]) =>
      call_sp (maybe_release_spec RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm L c lo (nf + n) new auv muv w80v w88);
      [ exact ST3 | atop_facts; exact CEIL | clear -LO; lia | assumption | reflexivity | reflexivity | reflexivity
      | exact MC4 | unboxed REG2 | unboxed W80 | unboxed W88 | unfold K_NUM_CLASSES; exact HC | exact SP1 | unfold K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; exact SP2
      | ]
    end end end.
  rename POST into ST5.
  carry SR3 MUm WMm ltac:(rewrite LCH; clear -SPR CEIL LO T0 T1 CHK0 CHK1 N TIC TB; lia).
  carry DS3 MUm WMm ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia).
  carry STATS2 MUm WMm ltac:(rewrite LSJ2; clear -SPR CEIL LO T0 T1 TIC TB; lia).
  carry MTX MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry STN MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W80 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry W88 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry J96 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  carry REG2 MUm WMm ltac:(clear -SPR CEIL LO SP1 SP2 HC RIE; lia).
  eapply junk_frame in JR; [| exact MUm | exact WMm | intros _; cbn [disjoint_from]; subst DST; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB; lia].
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MC5 : m3_cells L mm); [eapply m3_cells_frame; [exact MC4 | exact MUm | exact WMm |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI; lia |]; apply Forall_nil |];
    assert (MU35 : munch [(aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88);
                          (bv_unsigned sp + -128 - 80, bv_unsigned sp + -128)]%Z m3 mm);
    [ eapply munch_trans; [eapply munch_weaken; [| unboxed MUs] | eapply munch_weaken; [| exact MUm]]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia |];
    pose proof WMs as WM35;
    assert (AZF5 : azero mm (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new)));
    [ eapply azero_frame; [exact AZF3 | exact MU35 | exact WM35 |];
      intros _; cbn [disjoint_from]; rewrite shad_div, shlen_div; unfold ASHOFF; clear -SPR CEIL LO SP1 SP2 HC NF N NEWB RIE; Z.div_mod_to_equations; lia |]
  end.
  clear MC4 AZF3.
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  do 7 zstep. step. do 5 zstep.                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  do 7 zstep. step. if_lit.                                    (* [comment removed for export] *)
  box SR3. box DS3. box STATS2. box MUm. box MU35.
  snapshot [(aregion_info L c, aregion_info L c + 8)]%Z MUu WMu.
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  lrsc_stepA AMO.                                              (* [comment removed for export] *)
  carry SR3 MUu WMu ltac:(rewrite LCH; ub TSP; clear -T0 T1 SP1 SP2 HC RIE CHK0 CHK1 N Y TIC TB; lia).
  carry DS3 MUu WMu ltac:(rewrite length_app, length_skipn, LCH, L0; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia).
  carry STATS2 MUu WMu ltac:(rewrite LSJ2; ub TSP; clear -T0 T1 SP1 SP2 HC RIE Y TIC TB; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  do 15 step.                                                  (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -128) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MUx4 : munch [(aregion_info L c, aregion_info L c + 8)]%Z x14 mm) by (eapply munch_weaken; [| exact MUu]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia);
    eapply junk_frame in JR; [| exact MUx4 | exact WMu | intros _; cbn [disjoint_from]; subst DST; clear -SP1 SP2 HC RIE NF N NEWB; lia];
    assert (AZF6 : azero mm (shad (al_space_beg L + c * 4294967296 + 3758096384 + new)) (shlen (536870912 - new)));
    [ eapply azero_frame; [exact AZF5 | exact MUx4 | exact WMu |];
      intros _; cbn [disjoint_from]; rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC NF N NEWB RIE; Z.div_mod_to_equations; lia |];
    assert (MC6 : m3_cells L mm); [eapply m3_cells_frame; [exact MC5 | exact MUx4 | exact WMu |]; unfold AIMG_HI, AIMG_LO; ub SCX;
      apply Forall_cons; [cbn [fst snd]; clear -SP1 SP2 HC RIE CX0 CX1 Y CXI; lia |]; apply Forall_nil |]
  end.
  clear MC5 AZF5 MUu.
  apply evtF_done. eapply KONT.
  unfold rta_ret, K_FREEARR_MAX, K_FREEARR_MAP. cbv zeta. fold mu au nf mfa. rewrite FAE.
  split; [exact FPLE|].
  exists new, sj'.
  (* [comment removed for export] *)
  lazymatch goal with |- context [munch ?W m ?mm] =>
    assert (MUT : munch W m mm);
    [ ub MU01; ub MU3; ub MU35; ub MU2; subst DST;
      eapply munch_trans; [eapply munch_weaken; [| exact Y] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y2] |]; [unfold sub_fp; cbn [outside]; clear -MFA NF N NEWB NEWGE; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y0] |]; [unfold sub_fp; cbn [outside]; clear -MFA NF N NEWB NEWGE; intros xq Hxq; lia|];
      eapply munch_trans; [eapply munch_weaken; [| exact Y1] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|];
      eapply munch_weaken; [| exact MUx4]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia |]
  end.
  assert (WMT : wmono bsegs m _) by (eapply wmono_trans; [exact WM01 | eapply wmono_trans; [exact WM2 | exact WM3]]).
  split.
  { ub UD. destruct Y as [(_ & E & _ & _)|(LT & E & _ & _ & FILL & R1 & R2 & BW)]; [left; exact E| right].
    split; [exact LT|]. split; [exact E|]. split; [| split; [exact R1| split; [exact R2| exact BW]]].
    ub MU3; ub MU35; subst DST.
    eapply (fill_frame [(al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf, al_space_beg L + c * 4294967296 + 3758096384 + 4 * nf + 4 * n);
                        (aregion_info L c + 16, aregion_info L c + 24); (aregion_info L c + 80, aregion_info L c + 88);
                        (bv_unsigned sp + -128 - 80, bv_unsigned sp + -128); (aregion_info L c, aregion_info L c + 8)]%Z);
      [exact FILL | | exact WM3 |].
    - eapply munch_trans; [eapply munch_weaken; [| exact Y] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact Y0] |]; [unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia|].
      eapply munch_weaken; [| exact MUx4]; unfold sub_fp; cbn [outside]; clear; intros xq Hxq; lia.
    - intros _. cbn [disjoint_from]. rewrite shad_div, shlen_div; unfold ASHOFF. clear -SPR CEIL LO SP1 SP2 HC NF N NEWB NEWGE MFA RIE. Z.div_mod_to_equations; lia. }
  split; [exact NEWB|]. split; [exact NEWGE|]. split; [exact NEWM|].
  assert (GC2 : get_cls st2 c = mkAClass mu au nf new (c_count (get_cls st c))).
  { ub UD. destruct Y as [(_ & E & -> & _)|(_ & _ & -> & _)].
    - rewrite E. subst mu au nf mfa. symmetry. apply aclass_eta0.
    - rewrite get_cls_put_cls_eq. subst mu au nf mfa. apply set_mfa_eq. }
  split; [exact GC2|].
  split. { ub UD. destruct Y as [(_ & _ & -> & _)|(_ & _ & E & _)]; [left; reflexivity| right]. rewrite GC2. rewrite E at 1. f_equal; subst mu au nf mfa; apply set_mfa_eq. }
  split; [exact MUT|]. split; [exact WMT|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX|]. split; [exact REG2|].
  split. { replace 56 with (8 + (8 + (8 + 32))) by reflexivity.
           apply junk_merge; [eapply junk_of_cells'; [exact STN| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 72 + 8) with (aregion_info L c + 80) by (clear; lia).
           apply junk_merge; [eapply junk_of_cells'; [exact W80| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 80 + 8) with (aregion_info L c + 88) by (clear; lia).
           apply junk_merge; [eapply junk_of_cells'; [exact W88| reflexivity] | | clear; lia | clear; lia].
           replace (aregion_info L c + 88 + 8) with (aregion_info L c + 96) by (clear; lia). exists j96. exact J96. }
  split; [exact STATS2|]. split; [exact LSJ2|].
  split; [exact (proj1 (u32arr_app_inv _ _ _ _ DS3))|].
  split; [eapply junk_at_eq; [exact JR | subst DST; clear; lia | clear; lia]|].
  split; [exact AZF6| exact MC6].
Qed.
End CANSEC2.
