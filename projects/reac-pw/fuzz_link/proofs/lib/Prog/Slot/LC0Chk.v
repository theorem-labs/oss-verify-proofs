(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 467 of its 509 lines of code are new or changed and 422 lines of the source are left out. *)
(* op_read (fuzz_link.c:677-700), plain image: segment S3b, the six checks.

   From the lane's split c0_mid (0x13ed4, the return of reac_link_alias_read) to the call of free
   (kind) at 0x13f64 (c0_cut_fk):

     0x13ed4  mv s8, a0                       s8 = rc
     0x13ed8  jal check_socket
     0x13edc  beqz s2 / lbu a0, 0(s2) / beqz a0 / index_of (name) / bnez a0     the refusal test
     0x13ef4  lw a1, 0x218(s1); mv a0, s9; jal check_refused
     0x13f00  beqz s3 / check_bounds (kind, kc);   0x13f10  s9 = 4
     0x13f14  beqz s4 / check_bounds (alias, ac);  a4 = alias ? alias : wa
     0x13f30  s5 = 46; s6 = [sp+0x30]; a2 = kind ? kind : wk; a3 = wk; a5 = wa; a0 = rc; a1 = want
     0x13f54  jal check_read
     0x13f58  mv a0, s0; jal check_requests
     0x13f60  mv a0, s3; jal free           -> c0_cut_fk

   Every check is a `leaf` call (LC0Call.v leaf_call). The walk is cut at its join points: c0ck_w0
   (0x13ed4), c0ck_wref (0x13ef4), c0ck_w1 (0x13f00), c0ck_w2 (0x13f14), c0ck_w3 (0x13f30),
   c0ck_w3b (0x13f44), c0ck_w4 (0x13f58). The memory facts the walk carries are c0ck_inv; every
   callee writes only its own frame, inside the stack window below the slot's frame, so the
   segment's footprint is that window (c0ck_keep). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  check_socket_c index_of_c check_refused_c check_bounds_c check_read_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC0Defs LC0Call LC0Lib LC0Kern.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Small facts
   ========================================================================== *)

Lemma c0ck_q_ext : forall X, q_ext (eqv_cl X).
Proof.
  intros X c a (d & Hd & Edc) Eca. exists d. split; [exact Hd|]. exact (c0_ms_eqv_trans d c a Edc Eca).
Qed.

Lemma c0ck_eq0 : forall z, z = 0 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = true.
Proof. intros z ->. reflexivity. Qed.

Lemma c0ck_ne0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Ltac c0ck_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(* the named registers of an mkR map, as the contracts read them *)
Section Get.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Let R := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Lemma c0ck_g10 : getr R 10 = a0. Proof. reflexivity. Qed.
Lemma c0ck_g11 : getr R 11 = a1. Proof. reflexivity. Qed.
End Get.

Ltac c0ck_regs := rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?c0ck_g10, ?c0ck_g11.

(* the byte compare of `beqz a0` after `lbu` *)
Lemma c0ck_zxb_eqb : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bv_unsigned b =? 0).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb, bv_eqb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

(* the name name_of hands the refusal test: NULL for the selector 255, else a C string in the image *)
Lemma c0ck_name : forall m sel, 0 <= sel < 256 -> sel <> 255 -> gnames_at m -> odd_at m ->
  exists s, sel_name sel = Some s /\ cstr_at m (sel_ptr sel) s /\
            4096 <= sel_ptr sel /\ sel_ptr sel + Z.of_nat (length s) + 1 <= 0x960e0.
Proof.
  intros m sel Hs Hn HG HO. pose proof (c0_sel_str m sel Hs HG HO) as HS.
  revert HS. destruct (sel_name sel) as [s|] eqn:E; intros HS.
  - destruct HS as [_ HC]. exists s. split; [reflexivity|]. split; [exact HC|].
    destruct (c0_sel_fixed sel s Hs E) as [_ (_ & [F|F])];
      unfold A_RO_LO, A_RO_END, A_G_NAMES, G_NAMES_SIZE in F; lia.
  - exfalso. unfold sel_name in E. destruct (Z.eqb_spec sel 255); [contradiction|].
    destruct (sel <? 64); discriminate.
Qed.

Lemma c0ck_first : forall m p b s, cstr_at m p (b :: s) ->
  ov_read_bytes rsegs m (wa p) 1 = Some [b] /\ bv_unsigned b <> 0.
Proof.
  intros m p b s (HB & HN). split.
  - pose proof (bytes_at_read rsegs m p _ 0 1 HB ltac:(lia) ltac:(cbn [length app]; lia)) as E.
    rewrite Z.add_0_r in E. exact E.
  - intros E0. apply HN. left. apply bv_eq. rewrite E0. reflexivity.
Qed.

Lemma c0ck_first0 : forall m p, cstr_at m p [] -> ov_read_bytes rsegs m (wa p) 1 = Some [zb 0].
Proof.
  intros m p (HB & _).
  pose proof (bytes_at_read rsegs m p _ 0 1 HB ltac:(lia) ltac:(cbn [length app]; lia)) as E.
  rewrite Z.add_0_r in E. exact E.
Qed.

Lemma c0ck_le_bytes_id : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as HR.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

(* `lw a1, 0x218(s1)` with s1 = g_nl + 0x40000: g_nl.opened *)
Lemma c0ck_opened_rd : forall m kbs, nlk_at m kbs ->
  ov_read_bytes rsegs m (wa (GNL40 + 536)) 4 = Some (le4 (Z_to_bv 64 (nk_opened kbs))) /\
  0 <= nk_opened kbs.
Proof.
  intros m kbs ((HB & _) & HL).
  assert (El : nk_opened kbs = bytes_le_to_Z (firstn 4 (skipn (Z.to_nat NK_OPENED) kbs))) by reflexivity.
  assert (Hl : length (firstn 4 (skipn (Z.to_nat NK_OPENED) kbs)) = 4%nat)
    by (rewrite length_firstn, length_skipn; unfold NK_OPENED, NK_SIZE in *; lia).
  pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn (Z.to_nat NK_OPENED) kbs))) as H0.
  pose proof (bytes_le_to_Z_bound (firstn 4 (skipn (Z.to_nat NK_OPENED) kbs))) as H1.
  rewrite Hl in H1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in H1.
  split; [|lia].
  replace (GNL40 + 536) with (A_G_NL + NK_OPENED) by reflexivity.
  rewrite (bytes_at_read rsegs m A_G_NL kbs NK_OPENED 4 HB) by (unfold NK_OPENED, NK_SIZE in *; lia).
  f_equal. rewrite El. unfold le4. rewrite unsigned_lit by lia.
  rewrite <- Hl at 2. symmetry. apply c0ck_le_bytes_id.
Qed.

Lemma c0ck_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma c0ck_index_range : forall tab nm,
  (forall i n ix, nth_error tab i = Some (n, ix) -> 0 <= ix < 2 ^ 31) -> 0 <= index_of tab nm < 2 ^ 31.
Proof.
  induction tab as [|[n ix] tab IH]; intros nm H; cbn [index_of]; [lia|].
  destruct (bl_eqb n nm).
  - exact (H O n ix eq_refl).
  - apply IH. intros i n2 ix2 E. exact (H (S i) n2 ix2 E).
Qed.

(* check_read's three clauses over rc: the word encoding is injective where they need it *)
Lemma c0ck_rc : forall rc, rc < 2 ^ 64 ->
  (Z_to_bv 64 (norm_rc rc) = Z_to_bv 64 RC_FAILS -> Z_to_bv 64 rc <> Z_to_bv 64 0) /\
  (Z_to_bv 64 (norm_rc rc) <> Z_to_bv 64 RC_FAILS -> Z_to_bv 64 rc = Z_to_bv 64 (norm_rc rc)).
Proof.
  intros rc Hrc. unfold norm_rc. destruct (Z.ltb_spec 0 rc) as [Hp|Hn].
  - split.
    + intros _ E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
    + intros H. exfalso. apply H. reflexivity.
  - split.
    + intros E E0. rewrite E0 in E. apply (f_equal bv_unsigned) in E.
      rewrite !unsigned_lit in E by (unfold RC_FAILS; lia). unfold RC_FAILS in E. lia.
    + intros _. reflexivity.
Qed.




(* ==========================================================================
   2. The memory the walk carries
   ========================================================================== *)

(* the slot's frame and memory facts (c0_frame, c0_base), the four texts check_read compares and the
   two buffers check_bounds checks, and the footprint so far against the segment's start memory m0 *)
Definition c0ck_inv (E : lenv) (P N kc ac K A : Z) (kbs mbs gbs rk ral : list byte)
    (m0 m : word -> option byte) : Prop :=
  (exists wa wk, c0_frame E P N wa wk m) /\ c0_base E P N kbs mbs gbs m /\
  (kc <> 0 -> cstr_at m K rk /\ exists bs, tbuf_at m K kc bs /\ In (zb 0) bs) /\
  (ac <> 0 -> cstr_at m A ral /\ exists bs, tbuf_at m A ac bs /\ In (zb 0) bs) /\
  cstr_at m (e_S E - SLOT_FRAME + FO_B256) (if kc <? 1 then [] else rk) /\
  cstr_at m (e_S E - SLOT_FRAME + FO_B40) (if ac <? 1 then [] else ral) /\
  munch [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME)] m0 m /\ wmono rsegs m0 m.


Lemma c0ck_keep : forall E P N kc ac K A kbs mbs gbs rk ral m0 m m' k,
  lenv_ok E -> 0 <= k <= 48 -> 0 <= kc < 40 -> 0 <= ac < 40 ->
  (kc <> 0 -> c0_blk E K (kc + 1)) -> (ac <> 0 -> c0_blk E A (ac + 1)) ->
  Z.of_nat (length rk) <= kc -> Z.of_nat (length ral) <= ac ->
  c0ck_inv E P N kc ac K A kbs mbs gbs rk ral m0 m ->
  munch [(e_S E - SLOT_FRAME - k, e_S E - SLOT_FRAME)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  c0ck_inv E P N kc ac K A kbs mbs gbs rk ral m0 m'.
Proof.
  intros E P N kc ac K A kbs mbs gbs rk ral m0 m m' k HE Hk Hkc Hac HKb HAb Hrk Hra
    ((wa & wk & j0 & j2 & FR) & B & HK & HA & HW1 & HW2 & MU0 & WM0) MU WM MI ST.
  pose proof HE as (HS1 & HS2 & _).
  assert (ESZ : SLOT_STACK_Z = 65536) by reflexivity. assert (EF : SLOT_FRAME = 480) by reflexivity.
  assert (E1 : FO_B256 = 120) by reflexivity. assert (E2 : FO_B40 = 80) by reflexivity.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - exists wa, wk, j0, j2. eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
    cbn [disjoint_from cells_size csize c0_cells]. split; [right; lia | exact I].
  - eapply c0_base_keep; [exact HE | exact B | exact MU | exact WM | exact MI | exact ST |].
    intros x Hx NO. cbn [outside] in NO. lia.
  - intros Hk0. destruct (HK Hk0) as ((HB & HN) & bs & TB & Hin).
    destruct (HKb Hk0) as ((Hb1 & Hb2 & _) & _).
    split; [split; [|exact HN] | exists bs; split; [|exact Hin]].
    + eapply bytes_at_transport; [exact HB | exact MU |]. cbn [disjoint_from].
      rewrite length_app. cbn [length]. split; [left; lia | exact I].
    + eapply rw_cells_transport; [exact TB | exact MU | exact WM |]. cbn [disjoint_from cells_size csize].
      split; [left; lia | exact I].
  - intros Ha0. destruct (HA Ha0) as ((HB & HN) & bs & TB & Hin).
    destruct (HAb Ha0) as ((Hb1 & Hb2 & _) & _).
    split; [split; [|exact HN] | exists bs; split; [|exact Hin]].
    + eapply bytes_at_transport; [exact HB | exact MU |]. cbn [disjoint_from].
      rewrite length_app. cbn [length]. split; [left; lia | exact I].
    + eapply rw_cells_transport; [exact TB | exact MU | exact WM |]. cbn [disjoint_from cells_size csize].
      split; [left; lia | exact I].
  - destruct HW1 as (HB & HN). split; [|exact HN].
    eapply bytes_at_transport; [exact HB | exact MU |]. cbn [disjoint_from]. split; [right; lia | exact I].
  - destruct HW2 as (HB & HN). split; [|exact HN].
    eapply bytes_at_transport; [exact HB | exact MU |]. cbn [disjoint_from]. split; [right; lia | exact I].
  - eapply munch_trans; [exact MU0 |]. eapply munch_weaken; [| exact MU].
    intros x Hx. cbn [outside] in *. lia.
  - eapply wmono_trans; [exact WM0 | exact WM].
Qed.

(* the common post of every piece: the cut at free (kind), and the footprint *)
Definition c0ck_Q (E : lenv) (i : Z) (gp : word) (P N sel kc ac K A : Z) (kbs mbs gbs : list byte)
    (m0 : word -> option byte) : machine_state -> Prop :=
  eqv_cl (fun ms' => c0_cut_fk E i gp P N sel kc ac K A kbs mbs gbs ms' /\
                     seg_fp (e_S E) (c0_hpKA E kc K ac A) m0 (ms_mem ms')).


(* ==========================================================================
   3. The walk
   ========================================================================== *)

Section C0Chk.
Hypothesis CSOCK : check_socket_contract.
Hypothesis IDXOF : index_of_contract_P.
Hypothesis CREF : check_refused_contract.
Hypothesis CBND : check_bounds_contract.
Hypothesis CREAD : check_read_contract.
Hypothesis CREQ : check_requests_contract.

Section Walk.
Variables (E : lenv) (i : Z) (gp : word) (P N sel kc ac K A op0 want rc : Z)
          (kbs mbs gbs rk ral : list byte) (m0 : word -> option byte) (F : bvmap 5 word) (fc : bv 32).
Hypothesis HE : lenv_ok E.
Hypothesis Hfc : frm0 fc.
Hypothesis Hi : 0 <= i <= 47.
Hypothesis Hkc : 0 <= kc < 40.
Hypothesis Hac : 0 <= ac < 40.
Hypothesis HN : 0 <= N.
Hypothesis HKr : 0 <= K < 2 ^ 64.
Hypothesis HAr : 0 <= A < 2 ^ 64.
Hypothesis Hop : nk_opened kbs <= 64 * i + 1.
Hypothesis Hoc : nk_opened kbs = nk_closed kbs.
Hypothesis HKA : kc <> 0 -> ac <> 0 -> apart K (kc + 1) A (ac + 1).
Hypothesis HK0 : kc = 0 -> K = 0.
Hypothesis HKb : kc <> 0 -> c0_blk E K (kc + 1).
Hypothesis HA0 : ac = 0 -> A = 0.
Hypothesis HAb : ac <> 0 -> c0_blk E A (ac + 1).
Hypothesis Hrk : Z.of_nat (length rk) <= kc.
Hypothesis Hral : Z.of_nat (length ral) <= ac.
Hypothesis Hreq : requests_are kbs mbs.
Hypothesis Hwant : want = norm_rc rc.
Hypothesis Hrc : rc < 2 ^ 64.

Local Abbreviation SP := (Z_to_bv 64 (e_S E - SLOT_FRAME)).
Local Abbreviation QQ := (c0ck_Q E i gp P N sel kc ac K A kbs mbs gbs m0).
Local Abbreviation JJ := (c0ck_inv E P N kc ac K A kbs mbs gbs rk ral m0).

Ltac c0ck_facts :=
  pose proof HE as (HS1 & HS2 & _ & (HMD1 & HMD2 & HMDF) & _);
  assert (ESZ : SLOT_STACK_Z = 65536) by reflexivity; assert (EF : SLOT_FRAME = 480) by reflexivity;
  assert (EB1 : FO_B256 = 120) by reflexivity; assert (EB2 : FO_B40 = 80) by reflexivity;
  assert (EMD : MD_SIZE = 8856) by reflexivity;
  assert (EGN : A_G_NL = 0x31b80) by reflexivity; assert (ENK : NK_SIZE = 271992) by reflexivity.

(* after a leaf call of frame k: the walk's memory facts hold of the callee's result memory *)
Ltac c0ck_keep_tac kk :=
  lazymatch goal with
  | MU : munch _ ?m ?m', ST : stk rsegs ?m' _ _ |- _ =>
      rewrite ?unsigned_lit in MU, ST by lia; cbn [writes_nothing app] in MU;
      eapply c0ck_keep with (k := kk); solve [ eassumption | lia ]
  end.

Lemma c0ck_w4 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 t3 t4 t5 t6 : word) m,
  JJ m ->
  evt rsegs QQ (MS (mkR ra SP gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E)) (Z_to_bv 64 GNL40)
                        a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K) (Z_to_bv 64 A) (Z_to_bv 64 46) (Z_to_bv 64 A_JT)
                        s7 s8 (Z_to_bv 64 4) (Z_to_bv 64 (e_md E + MD_N_REQ)) (Z_to_bv 64 i) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f58) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 t3 t4 t5 t6 m HJ. c0ck_facts.
  pose proof HJ as (_ & B & _).
  pose proof B as (_ & HNL & HNW & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMA & HMW & _ & _ & _ & _ & _ & _ & HMI & _ & HST).
  step. step.
  pose proof CREQ as HC. unfold check_requests_contract in HC.
  eapply (leaf_call _ _ _ _ _ HC c0_check_requests_post_ext _ (c0ck_q_ext _)) with (lo := e_S E - SLOT_STACK_Z).
  - cbv beta. exists kbs, mbs. unfold frame_apart_gnl, apart_frame, apart_gnl. c0ck_regs.
    rewrite !unsigned_lit by lia.
    split; [exact HNL|]. split; [right; lia|].
    split; [exact HMA|]. split; [exact HNW|]. split; [exact HMW|]. split; [exact Hreq|].
    split; [left; lia | exact (proj1 (c0_img_named _ _ HMDF ltac:(lia)))].
  - exact HMI.
  - rewrite unsigned_lit by lia. exact HST.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
  - intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI ST _.
    assert (HJ' : JJ m') by c0ck_keep_tac 48.
    c0ck_ret. step. step.
    apply evt_done. unfold c0ck_Q. apply c0_eqv_intro.
    destruct HJ' as ((wa & wk & FR) & B' & _ & _ & _ & _ & MU0 & WM0).
    split.
    + unfold c0_cut_fk. do 22 eexists. split; [reflexivity|].
      split; [exact Hfc|]. split; [exact Hi|]. split; [exact Hkc|]. split; [exact Hac|]. split; [exact HN|].
      split; [exact HKr|]. split; [exact HAr|]. split; [exact Hop|]. split; [exact Hoc|]. split; [exact HKA|].
      split; [exact HK0|].
      split; [intros H0; split; [destruct (HKb H0) as ((? & _) & _); lia | exact (HKb H0)]|].
      split; [exact HA0|].
      split; [intros H0; split; [destruct (HAb H0) as ((? & _) & _); lia | exact (HAb H0)]|].
      split; [exact FR | exact B'].
    + exists [(e_S E - SLOT_STACK_Z, e_S E - SLOT_FRAME)]. split; [exact MU0|]. split; [exact WM0|].
      intros x Hx NO. cbn [outside] in NO. left. lia.
Qed.

(* 0x13f44: a3 = wk, a5 = wa, a0 = rc, a1 = want, then check_read *)
Lemma c0ck_w3b : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m,
  JJ m ->
  bv_unsigned a2 = (if kc =? 0 then e_S E - SLOT_FRAME + FO_B256 else K) ->
  bv_unsigned a4 = (if ac =? 0 then e_S E - SLOT_FRAME + FO_B40 else A) ->
  evt rsegs QQ (MS (mkR ra SP gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E)) (Z_to_bv 64 GNL40)
                        a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K) (Z_to_bv 64 A) (Z_to_bv 64 46) (Z_to_bv 64 A_JT)
                        (Z_to_bv 64 want) (Z_to_bv 64 rc) (Z_to_bv 64 4) (Z_to_bv 64 (e_md E + MD_N_REQ))
                        (Z_to_bv 64 i) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f44) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m HJ Ha2 Ha4. c0ck_facts.
  pose proof HJ as (_ & B & HK & HA & HW1 & HW2 & _).
  pose proof B as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & HST).
  rewrite EB1 in Ha2, HW1. rewrite EB2 in Ha4, HW2.
  do 4 step. step.
  pose proof CREAD as HC. unfold check_read_contract in HC.
  eapply (leaf_call _ _ _ _ _ HC c0_check_read_post_ext _ (c0ck_q_ext _)) with (lo := e_S E - SLOT_STACK_Z).
  - cbv beta.
    exists (if kc <? 1 then [] else rk), (if kc <? 1 then [] else rk),
           (if ac <? 1 then [] else ral), (if ac <? 1 then [] else ral).
    unfold apart_frame. c0ck_regs. rewrite Ha2, Ha4. rewrite !unsigned_lit by lia.
    destruct (c0ck_rc rc Hrc) as [Hr1 Hr2]. rewrite <- Hwant in Hr1, Hr2. unfold wz.
    split.
    { destruct (Z.eqb_spec kc 0) as [Hk0|Hk0]; [exact HW1|].
      destruct (HK Hk0) as [HC1 _]. rewrite (proj2 (Z.ltb_ge kc 1)) by lia. exact HC1. }
    split; [exact HW1|].
    split.
    { destruct (Z.eqb_spec ac 0) as [Ha0|Ha0]; [exact HW2|].
      destruct (HA Ha0) as [HC1 _]. rewrite (proj2 (Z.ltb_ge ac 1)) by lia. exact HC1. }
    split; [exact HW2|].
    split.
    { destruct (Z.eqb_spec kc 0) as [Hk0|Hk0]; [right; lia|].
      left. destruct (HKb Hk0) as ((? & ? & _) & _). destruct (Z.ltb_spec kc 1); cbn [length]; lia. }
    split; [right; lia|].
    split.
    { destruct (Z.eqb_spec ac 0) as [Ha0|Ha0]; [right; lia|].
      left. destruct (HAb Ha0) as ((? & ? & _) & _). destruct (Z.ltb_spec ac 1); cbn [length]; lia. }
    split; [right; lia|].
    split; [exact Hr1|]. split; [exact Hr2|]. intros _. split; reflexivity.
  - exact HMI.
  - rewrite unsigned_lit by lia. exact HST.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
  - intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI ST _.
    assert (HJ' : JJ m') by c0ck_keep_tac 32.
    c0ck_ret. apply c0ck_w4. exact HJ'.
Qed.

(* 0x13f30: s5 = 46, s6 = [sp+0x30] (the jump table), a2 = kind ? kind : wk *)
Lemma c0ck_w3 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 : word) m,
  JJ m ->
  bv_unsigned a4 = (if ac =? 0 then e_S E - SLOT_FRAME + FO_B40 else A) ->
  evt rsegs QQ (MS (mkR ra SP gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E)) (Z_to_bv 64 GNL40)
                        a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K) (Z_to_bv 64 A) s5 s6
                        (Z_to_bv 64 want) (Z_to_bv 64 rc) (Z_to_bv 64 4) (Z_to_bv 64 (e_md E + MD_N_REQ))
                        (Z_to_bv 64 i) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f30) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 t3 t4 t5 t6 m HJ Ha4. c0ck_facts.
  pose proof HJ as ((wa & wk & j0 & j2 & FR) & _).
  unfold c0_cells in FR.
  step. step. step. step.
  destruct (Z.eqb_spec kc 0) as [Hk0|Hk0].
  - rewrite (c0ck_eq0 K (HK0 Hk0)). cbv iota.
    apply c0ck_w3b; [exact HJ | | exact Ha4].
    rewrite unsigned_lit by lia. rewrite (proj2 (Z.eqb_eq kc 0) Hk0). cbv beta iota. lia.
  - destruct (HKb Hk0) as ((Hb1 & Hb2 & _) & _).
    rewrite (c0ck_ne0 K) by lia. cbv iota.
    step.
    apply c0ck_w3b; [exact HJ | | exact Ha4].
    rewrite unsigned_lit by lia. rewrite (proj2 (Z.eqb_neq kc 0) Hk0). reflexivity.
Qed.

(* 0x13f14: check_bounds (alias, ac) when alias is not NULL; a4 = alias ? alias : wa *)
Lemma c0ck_w2 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m,
  JJ m ->
  evt rsegs QQ (MS (mkR ra SP gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E)) (Z_to_bv 64 GNL40)
                        a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K) (Z_to_bv 64 A) (Z_to_bv 64 ac) (Z_to_bv 64 kc)
                        (Z_to_bv 64 want) (Z_to_bv 64 rc) (Z_to_bv 64 4) (Z_to_bv 64 (e_md E + MD_N_REQ))
                        (Z_to_bv 64 i) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f14) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m HJ. c0ck_facts.
  pose proof HJ as (_ & B & _ & HA & _).
  pose proof B as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & HST).
  step.
  destruct (Z.eqb_spec ac 0) as [Ha0|Ha0].
  - rewrite (c0ck_eq0 A (HA0 Ha0)). cbv iota. step.
    apply c0ck_w3; [exact HJ|].
    rewrite unsigned_lit by lia. rewrite (proj2 (Z.eqb_eq ac 0) Ha0). cbv beta iota. lia.
  - destruct (HAb Ha0) as ((Hb1 & Hb2 & _) & _).
    destruct (HA Ha0) as (_ & bs & TB & Hin).
    rewrite (c0ck_ne0 A) by lia. cbv iota.
    step. step. step.
    pose proof CBND as HC. unfold check_bounds_contract in HC.
    eapply (leaf_call _ _ _ _ _ HC c0_check_bounds_post_ext _ (c0ck_q_ext _)) with (lo := e_S E - SLOT_STACK_Z).
    + cbv beta. exists bs. unfold apart_frame. c0ck_regs. rewrite !unsigned_lit by lia.
      split; [lia|]. split; [lia|]. split; [exact TB|]. split; [exact Hin|]. left; lia.
    + exact HMI.
    + rewrite unsigned_lit by lia. exact HST.
    + rewrite unsigned_lit by lia. lia.
    + rewrite unsigned_lit by lia. lia.
    + intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI ST _.
      assert (HJ' : JJ m') by c0ck_keep_tac 32.
      c0ck_ret. step. step.
      apply c0ck_w3; [exact HJ'|].
      rewrite unsigned_lit by lia. rewrite (proj2 (Z.eqb_neq ac 0) Ha0). reflexivity.
Qed.

(* 0x13f00: check_bounds (kind, kc) when kind is not NULL; 0x13f10 s9 = 4 *)
Lemma c0ck_w1 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s9 t3 t4 t5 t6 : word) m,
  JJ m ->
  evt rsegs QQ (MS (mkR ra SP gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E)) (Z_to_bv 64 GNL40)
                        a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K) (Z_to_bv 64 A) (Z_to_bv 64 ac) (Z_to_bv 64 kc)
                        (Z_to_bv 64 want) (Z_to_bv 64 rc) s9 (Z_to_bv 64 (e_md E + MD_N_REQ))
                        (Z_to_bv 64 i) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13f00) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s9 t3 t4 t5 t6 m HJ. c0ck_facts.
  pose proof HJ as (_ & B & HK & _).
  pose proof B as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & HST).
  step.
  destruct (Z.eqb_spec kc 0) as [Hk0|Hk0].
  - rewrite (c0ck_eq0 K (HK0 Hk0)). cbv iota. step. apply c0ck_w2. exact HJ.
  - destruct (HKb Hk0) as ((Hb1 & Hb2 & _) & _).
    destruct (HK Hk0) as (_ & bs & TB & Hin).
    rewrite (c0ck_ne0 K) by lia. cbv iota.
    step. step. step.
    pose proof CBND as HC. unfold check_bounds_contract in HC.
    eapply (leaf_call _ _ _ _ _ HC c0_check_bounds_post_ext _ (c0ck_q_ext _)) with (lo := e_S E - SLOT_STACK_Z).
    + cbv beta. exists bs. unfold apart_frame. c0ck_regs. rewrite !unsigned_lit by lia.
      split; [lia|]. split; [lia|]. split; [exact TB|]. split; [exact Hin|]. left; lia.
    + exact HMI.
    + rewrite unsigned_lit by lia. exact HST.
    + rewrite unsigned_lit by lia. lia.
    + rewrite unsigned_lit by lia. lia.
    + intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI ST _.
      assert (HJ' : JJ m') by c0ck_keep_tac 32.
      c0ck_ret. step. apply c0ck_w2. exact HJ'.
Qed.

(* 0x13ef4: a1 = g_nl.opened, a0 = s9 = opened before the readers, check_refused *)
Lemma c0ck_wref : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 : word) m,
  JJ m -> nk_opened kbs = op0 ->
  evt rsegs QQ (MS (mkR ra SP gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E)) (Z_to_bv 64 GNL40)
                        a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K) (Z_to_bv 64 A) (Z_to_bv 64 ac) (Z_to_bv 64 kc)
                        (Z_to_bv 64 want) (Z_to_bv 64 rc) (Z_to_bv 64 op0) (Z_to_bv 64 (e_md E + MD_N_REQ))
                        (Z_to_bv 64 i) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13ef4) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 m HJ Href. c0ck_facts.
  pose proof HJ as (_ & B & _).
  pose proof B as (_ & HNL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMI & _ & HST).
  destruct (c0ck_opened_rd m kbs HNL) as [HR Hn0].
  step. rewrite c0ck_sx32 by lia. step. step.
  pose proof CREF as HC. unfold check_refused_contract in HC.
  eapply (leaf_call _ _ _ _ _ HC c0_check_refused_post_ext _ (c0ck_q_ext _)) with (lo := e_S E - SLOT_STACK_Z).
  - cbv beta. c0ck_regs. rewrite Href. reflexivity.
  - exact HMI.
  - rewrite unsigned_lit by lia. exact HST.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
  - intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' _ _ _ _ PO.
    unfold unchanged in PO. subst m'.
    c0ck_ret. apply c0ck_w1. exact HJ.
Qed.

(* 0x13ed4: s8 = rc, check_socket, then the refusal test *)
Lemma c0ck_w0 : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) m,
  JJ m -> 0 <= sel < 256 ->
  ((sel_name sel = None \/ sel_name sel = Some [] \/
    (forall s, sel_name sel = Some s -> index_of link_tab s = 0)) -> nk_opened kbs = op0) ->
  evt rsegs QQ (MS (mkR ra SP gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (e_md E)) (Z_to_bv 64 GNL40)
                        (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (sel_ptr sel)) (Z_to_bv 64 K)
                        (Z_to_bv 64 A) (Z_to_bv 64 ac) (Z_to_bv 64 kc) (Z_to_bv 64 want) s8 (Z_to_bv 64 op0)
                        (Z_to_bv 64 (e_md E + MD_N_REQ)) (Z_to_bv 64 i) t3 t4 t5 t6)
                   F (Z_to_bv 64 C0_MID) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 m HJ Hsel Href. c0ck_facts.
  pose proof HJ as (_ & B & _).
  pose proof B as (_ & HNL & _ & HIF & HOP & HMS & HGN & HODD & _ & _ & _ & HIP & _ & _ & _ & _ & _ & _ & _ & _
                   & HMI & _ & HST).
  unfold C0_MID. step. step.
  pose proof CSOCK as HC. unfold check_socket_contract in HC.
  eapply (leaf_call _ _ _ _ _ HC c0_check_socket_post_ext _ (c0ck_q_ext _)) with (lo := e_S E - SLOT_STACK_Z).
  - cbv beta. exists kbs. split; [exact HNL|]. split; [exact HOP|]. split; [exact Hoc | exact HMS].
  - exact HMI.
  - rewrite unsigned_lit by lia. exact HST.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
  - intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' _ _ _ _ PO.
    unfold unchanged in PO. subst m'. c0ck_ret.
    step.
    destruct (Z.eqb_spec sel 255) as [H255|H255].
    + (* a NULL name *)
      rewrite (c0ck_eq0 (sel_ptr sel)) by (rewrite H255; reflexivity). cbv iota.
      apply c0ck_wref; [exact HJ|]. apply Href. left. rewrite H255. reflexivity.
    + destruct (c0ck_name m sel Hsel H255 HGN HODD) as (s & Hs & Hcs & Hp1 & Hp2).
      rewrite (c0ck_ne0 (sel_ptr sel)) by lia. cbv iota.
      destruct s as [|b s'].
      * (* an empty name *)
        pose proof (c0ck_first0 m (sel_ptr sel) Hcs) as HR1.
        step. step.
        rewrite c0ck_zxb_eqb. change (bv_unsigned (zb 0) =? 0) with true. cbv iota.
        apply c0ck_wref; [exact HJ|]. apply Href. right. left. exact Hs.
      * destruct (c0ck_first m (sel_ptr sel) b s' Hcs) as [HR1 Hb0].
        step. step.
        rewrite c0ck_zxb_eqb, (proj2 (Z.eqb_neq _ 0) Hb0). cbv iota.
        step. step.
        pose proof IDXOF as HC2. unfold index_of_contract_P, index_of_contract in HC2.
        eapply (leaf_call _ _ _ _ _ HC2 c0_index_of_post_ext _ (c0ck_q_ext _)) with (lo := e_S E - SLOT_STACK_Z).
        -- cbv beta. exists kbs, link_tab, (b :: s').
           unfold frame_apart_gnl, apart_gnl, apart_frame. c0ck_regs. rewrite !unsigned_lit by lia.
           split; [exact HNL|]. split; [right; lia|]. split; [exact HIF|]. split; [lia|]. split; [exact Hcs|].
           split; [left; lia|].
           intros j n2 ix p Ej Ep.
           pose proof (c0_ifname_ctx E (mkR w0 (Z_to_bv 64 (e_S E - SLOT_FRAME)) w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0
                                       w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0 w0) 48 m kbs HE
                         ltac:(rewrite mkR_sp; apply unsigned_lit; lia) ltac:(lia) HIF HIP link_tab j n2 ix p HIF Ej Ep)
             as AF.
           cbv zeta in AF. destruct AF as (_ & AF & _). unfold apart_frame in AF.
           rewrite mkR_sp, unsigned_lit in AF by lia. exact AF.
        -- exact HMI.
        -- rewrite unsigned_lit by lia. exact HST.
        -- rewrite unsigned_lit by lia. lia.
        -- rewrite unsigned_lit by lia. lia.
        -- intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 m2 MU WM MI ST PO.
           specialize (PO kbs link_tab (b :: s') HNL HIF). rewrite mkR_a0, unsigned_lit in PO by lia.
           specialize (PO Hcs). rewrite c0ck_g10 in PO. unfold wz in PO. subst a02.
           assert (HJ' : JJ m2) by c0ck_keep_tac 48.
           c0ck_ret. step.
           pose proof (c0ck_index_range link_tab (b :: s')
                         (fun j n ix E0 => proj1 (proj2 (proj2 HIF) j n ix E0))) as HIr.
           destruct (Z.eqb_spec (index_of link_tab (b :: s')) 0) as [Hi0|Hi0].
           ++ (* not in the table: the refusal *)
              rewrite (c0ck_eq0 _ Hi0). cbv beta iota delta [negb].
              apply c0ck_wref; [exact HJ'|]. apply Href. right. right.
              intros s0 Es0. rewrite Hs in Es0. injection Es0 as <-. exact Hi0.
           ++ rewrite (c0ck_ne0 _) by lia. cbv beta iota delta [negb].
              apply c0ck_w1. exact HJ'.
Qed.

End Walk.

Lemma c0_s3b : forall E i gp P N sel kc ac K A op0 want rc kbs mbs gbs ms,
    lenv_ok E -> c0_mid E i gp P N sel kc ac K A op0 want rc kbs mbs gbs ms ->
    evt rsegs (eqv_cl (fun ms' => c0_cut_fk E i gp P N sel kc ac K A kbs mbs gbs ms' /\
                                  seg_fp (e_S E) (c0_hpKA E kc K ac A) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp P N sel kc ac K A op0 want rc kbs mbs gbs ms HE HM.
  destruct HM as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & t3 & t4 & t5 & t6 & F & fc & m
                  & wa & wk & -> & Hfc & Hi & Hsel & Hkc & Hac & HN & HKr & HAr & _ & Hop & Hoc & HKA
                  & kbs0 & HM).
  cbv zeta in HM.
  destruct HM as (Hwf & Hrc & Hwant & Href & HK & HA & HW1 & HW2 & HKb & HAb & HK0 & HA0 & Hreq & FR & B).
  pose proof (c0_read_rc_wf link_tab (sel_name sel) kc ac [] kbs0 Hwf) as Hrc'. rewrite <- Hrc in Hrc'.
  assert (Hrc2 : rc < 2 ^ 64) by lia.
  pose proof (c0_rkind_len link_tab (sel_name sel) kc ac [] (nk_kstate kbs0) ltac:(lia)) as Hrk.
  pose proof (c0_ralias_len link_tab (sel_name sel) kc ac [] (nk_kstate kbs0) ltac:(lia)) as Hral.
  rewrite <- Hrc in Hwant.
  unfold wz.
  eapply c0ck_w0 with (m0 := m) (rk := r_kind (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs0)))
                      (ral := r_alias (read_core link_tab (sel_name sel) kc ac [] (nk_kstate kbs0)));
    first [ eassumption | lia | idtac ].
  split; [exists wa, wk; exact FR|]. split; [exact B|].
  split; [exact HK|]. split; [exact HA|]. split; [exact HW1|]. split; [exact HW2|].
  split; [apply munch_refl | apply wmono_refl].
Qed.

End C0Chk.
