(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 1038 of its 1165 lines of code are new or changed and 890 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c strncmp_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma cat8_len : forall ptrs : list Z,
  length (concat (map (fun p => le8 (Z_to_bv 64 p)) ptrs)) = (8 * length ptrs)%nat.
Proof.
  induction ptrs as [|q ptrs IH]; [reflexivity|].
  cbn [map length]. rewrite concat_cons, length_app, length_le8, IH. lia.
Qed.

Lemma cat8_nth : forall (ptrs : list Z) i p, nth_error ptrs i = Some p ->
  firstn 8 (skipn (8 * i) (concat (map (fun p => le8 (Z_to_bv 64 p)) ptrs))) = le8 (Z_to_bv 64 p).
Proof.
  induction ptrs as [|q ptrs IH]; intros [|i] p H; cbn [nth_error] in H; try discriminate.
  - injection H as <-. cbn [map]. rewrite concat_cons. replace (8 * 0)%nat with 0%nat by lia.
    change (skipn 0 ?l) with l.
    rewrite firstn_app, length_le8, Nat.sub_diag. change (firstn 0 ?l) with (@nil byte). rewrite app_nil_r.
    apply firstn_all2. rewrite length_le8. lia.
  - cbn [map]. rewrite concat_cons. replace (8 * S i)%nat with (8 * i + 8)%nat by lia.
    rewrite <- skipn_skipn, skipn_app, length_le8, Nat.sub_diag.
    rewrite (skipn_all2 (le8 (Z_to_bv 64 q))) by (rewrite length_le8; lia). change (skipn 0 ?l) with l.
    cbn [app]. exact (IH i p H).
Qed.

Lemma read_ptr : forall m tok (ptrs : list Z) i p,
  bytes_at rsegs m tok (concat (map (fun p => le8 (Z_to_bv 64 p)) ptrs)) -> nth_error ptrs i = Some p ->
  ov_read_bytes rsegs m (wa (tok + 8 * Z.of_nat i)%Z) 8 = Some (le8 (Z_to_bv 64 p)).
Proof.
  intros m tok ptrs i p H E.
  assert (Hi : (i < length ptrs)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite (bytes_at_read rsegs m tok _ (8 * Z.of_nat i) 8 H) by (rewrite ?cat8_len; lia).
  replace (Z.to_nat (8 * Z.of_nat i)) with (8 * i)%nat by lia. rewrite (cat8_nth ptrs i p E). reflexivity.
Qed.

Lemma read1 : forall m A bs k b, bytes_at rsegs m A bs -> (0 <= k)%Z -> nth_error bs (Z.to_nat k) = Some b ->
  ov_read_bytes rsegs m (wa (A + k)%Z) 1 = Some [b].
Proof.
  intros m A bs k b H Hk Hn.
  assert (L : (Z.to_nat k < length bs)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_read rsegs m A bs k 1 H Hk) by lia.
  destruct (skipn (Z.to_nat k) bs) as [|x r] eqn:E.
  - apply (f_equal (@length byte)) in E. rewrite length_skipn in E. cbn in E. lia.
  - cbn [firstn]. f_equal. f_equal. rewrite <- (firstn_skipn (Z.to_nat k) bs) in Hn.
    rewrite nth_error_app2 in Hn by (rewrite length_firstn; lia).
    rewrite length_firstn, E in Hn. replace (Z.to_nat k - Init.Nat.min (Z.to_nat k) (length bs))%nat with 0%nat in Hn by lia.
    cbn in Hn. congruence.
Qed.

Lemma eqb_byte_lit : forall (b : byte) c, (0 <= c < 256)%Z ->
  bv_eqb (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 c) = (bv_unsigned b =? c)%Z.
Proof.
  intros b c Hc. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8)%Z with 256%Z in R.
  unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma eqb_small : forall v, (-256 < v < 256)%Z -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0)%Z.
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2 ^ 64)%Z with 0%Z.
  destruct (Z.eqb_spec v 0) as [E|E]; [subst; reflexivity|].
  apply Z.eqb_neq. intros C. apply E. apply Z.mod_divide in C; [|lia]. destruct C as [k Hk]. nia.
Qed.

Lemma ntok_ltu : forall n, (1 <= n <= 64)%Z ->
  bv_ltu (Z_to_bv 64 (bv_swrap 32 (n + -6))) (Z_to_bv 64 (-2)) = negb ((n =? 4) || (n =? 5))%Z.
Proof.
  intros n Hn. assert (E : bv_swrap 32 (n + -6) = (n + -6)%Z).
  { change (bv_swrap 32 ?z) with (((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z). rewrite Z.mod_small by lia. lia. }
  rewrite E. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec n 4); destruct (Z.eqb_spec n 5); cbn [orb negb];
    first [ apply Z.ltb_ge; Z.div_mod_to_equations; lia | apply Z.ltb_lt; Z.div_mod_to_equations; lia ].
Qed.

Lemma len_ltu : forall n, (0 <= n < 2 ^ 64)%Z ->
  bv_ltu (Z_to_bv 64 4096) (Z_to_bv 64 n) = (Verbs.line_max <? n)%Z.
Proof. intros n Hn. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Ltac cond_by b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b;
      [ cbv iota
      | symmetry; unfold bv_eqb, bv_ltu, bv_leu; fold_lit_ux; rewrite ?unsigned_lit_wrap;
        change 7%Z with (Z.ones 3); rewrite ?Z.land_ones by lia;
        repeat match goal with
               | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
               | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
               end;
        cbn [negb]; first [reflexivity | exfalso; Z.div_mod_to_equations; lia] ]
  end.

Lemma sw_prefix : forall k (P w : list byte), length P = S k ->
  Forall (fun c => bv_unsigned c <> 0%Z) P -> Forall (fun c => bv_unsigned c <> 0%Z) w ->
  exists v, strncmp_walk (w ++ [Z_to_bv 8 0]) P k = Some v /\ (-256 < v < 256)%Z /\
            (v = 0%Z <-> Verbs.has_prefix P w = true).
Proof.
  induction k as [|k IH]; intros [|c P] w HL NP NW; try discriminate;
    apply Forall_cons_iff in NP; destruct NP as [Nc NP];
    pose proof (bv_unsigned_in_range 8 c) as Rc; change (bv_modulus 8) with 256%Z in Rc;
    (destruct w as [|a w];
     [ cbn [app strncmp_walk]; change (bv_unsigned (Z_to_bv 8 0)) with 0%Z; cbn [Z.eqb orb];
       exists (0 - bv_unsigned c)%Z; split; [reflexivity|]; split; [lia|];
       unfold Verbs.has_prefix; cbn [length Nat.leb andb]; split; [lia | discriminate] | ]);
    apply Forall_cons_iff in NW; destruct NW as [Na NW];
    pose proof (bv_unsigned_in_range 8 a) as Ra; change (bv_modulus 8) with 256%Z in Ra;
    cbn [app strncmp_walk]; rewrite (proj2 (Z.eqb_neq _ _) Na), (proj2 (Z.eqb_neq _ _) Nc); cbn [orb];
    unfold Verbs.has_prefix; cbn [length Nat.leb firstn Verbs.list_eqb].
  - cbn [length] in HL. destruct P; [|discriminate]. cbn [Nat.eqb orb].
    exists (bv_unsigned a - bv_unsigned c)%Z. split; [reflexivity|]. split; [lia|].
    cbn [firstn Verbs.list_eqb]. rewrite andb_true_r.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)); cbn [andb]; split;
      first [intros; reflexivity | intros; lia | intros; discriminate | intros; exfalso; lia].
  - cbn [Nat.eqb orb]. cbn [length] in HL.
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|E]; cbn [negb andb].
    + destruct (IH P w ltac:(lia) NP NW) as (v & Hv & Rv & Qv). exists v. split; [exact Hv|]. split; [exact Rv|].
      rewrite Qv. unfold Verbs.has_prefix. reflexivity.
    + exists (bv_unsigned a - bv_unsigned c)%Z. split; [reflexivity|]. split; [lia|].
      split; first [intros; reflexivity | intros; lia | intros; discriminate | intros; exfalso; lia].
Qed.

Lemma dash_cases : forall w : list byte, Forall (fun c => bv_unsigned c <> 0%Z) w ->
  exists c0, nth_error (w ++ [Z_to_bv 8 0]) 0 = Some c0 /\
    ((bv_unsigned c0 <> 45%Z /\ Verbs.list_eqb w Verbs.Lit.word_layout_unknown = false) \/
     (bv_unsigned c0 = 45%Z /\ exists c1, nth_error (w ++ [Z_to_bv 8 0]) 1 = Some c1 /\
        (bv_unsigned c1 = 0%Z <-> Verbs.list_eqb w Verbs.Lit.word_layout_unknown = true))).
Proof.
  intros [|a w] NW.
  - exists (Z_to_bv 8 0). split; [reflexivity|]. left. split; [intro C; vm_compute in C; discriminate C | reflexivity].
  - apply Forall_cons_iff in NW. destruct NW as [Na NW]. exists a. split; [reflexivity|].
    change Verbs.Lit.word_layout_unknown with [Z_to_bv 8 45]. cbn [Verbs.list_eqb].
    change (bv_unsigned (Z_to_bv 8 45)) with 45%Z.
    destruct (Z.eqb_spec (bv_unsigned a) 45) as [E|E]; cbn [andb]; [right | left; split; [exact E | reflexivity]].
    split; [exact E|]. destruct w as [|b w].
    + exists (Z_to_bv 8 0). split; [reflexivity|]. cbn. split; reflexivity.
    + apply Forall_cons_iff in NW. destruct NW as [Nb _]. exists b. split; [reflexivity|].
      cbn [Verbs.list_eqb]. split; [intros C; contradiction | discriminate].
Qed.

Lemma key_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x107cb Verbs.Lit.word_verdict.
Proof.
  intros m MI. split; [lia|]. split; [vm_compute; discriminate|]. intros i Hi.
  change (length Verbs.Lit.word_verdict) with 8%nat in Hi.
  unfold mrd. destruct (m (wa (0x107cb + Z.of_nat i)%Z)) as [b|] eqn:E.
  - apply MI in E. exfalso.
    assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat \/ i = 7%nat)
      by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute in E; discriminate E|]). subst i. vm_compute in E. discriminate E.
  - assert (C : i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/ i = 4%nat \/ i = 5%nat \/ i = 6%nat \/ i = 7%nat)
      by lia.
    repeat (destruct C as [C|C]; [subst i; vm_compute; reflexivity|]). subst i. vm_compute. reflexivity.
Qed.

Definition psw_ref (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-902)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'.

Definition psw_call (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p1 p2 p3 pv : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x8 x9 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x17f80) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 x8 x9
                  (Z_to_bv 64 p1) (Z_to_bv 64 p2) (Z_to_bv 64 p3) (Z_to_bv 64 pv) a4 a5 a6 a7
                  x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x170a8) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 48)%Z [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition acc_shape (ptrs : list Z) (tks : list (list byte)) (u f l : list byte) (v : option (list byte))
    (p1 p2 p3 pv : Z) : Prop :=
  nth_error ptrs 1 = Some p1 /\ nth_error ptrs 2 = Some p2 /\ nth_error ptrs 3 = Some p3 /\
  nth_error tks 1 = Some u /\ nth_error tks 2 = Some f /\ nth_error tks 3 = Some l /\
  match v with
  | None => pv = 0%Z
  | Some x => exists p4 w4, nth_error ptrs 4 = Some p4 /\ nth_error tks 4 = Some w4 /\ pv = (p4 + 8)%Z /\
      (8 <= length w4)%nat /\ x = skipn 8 w4
  end.

Definition psw_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (T : list byte) (ptrs : list Z) (tks : list (list byte)) : machine_state -> Prop :=
  fun ms' =>
    (Verbs.pin_set_words_m T (tl tks) = Verbs.reject /\
     psw_ref ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ms') \/
    (exists u f l v p1 p2 p3 pv, Verbs.pin_set_words_m T (tl tks) = Verbs.SPinSet u f l v /\
     acc_shape ptrs tks u f l v p1 p2 p3 pv /\
     psw_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p1 p2 p3 pv ms').

Lemma psw_run1 : strlen_contract -> strncmp_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (line tok ntok lo : Z) (T slackT : list byte)
    (ptrs : list Z) (tks : list (list byte)),
  bytes_at rsegs m line (T ++ Z_to_bv 8 0 :: slackT) ->
  ~ In (Z_to_bv 8 0) T ->
  ((- (line + Z.of_nat (length T) + 1)) mod 8 <= Z.of_nat (length slackT))%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z ->
  (line + Z.of_nat (length (T ++ Z_to_bv 8 0 :: slackT)) <= bv_unsigned sp - 48)%Z ->
  bytes_at rsegs m tok (concat (map (fun p => le8 (Z_to_bv 64 p)) ptrs)) -> (tok mod 8 = 0)%Z ->
  length ptrs = length tks -> ntok = Z.of_nat (length tks) -> (1 <= ntok <= 64)%Z ->
  (bv_unsigned sp <= tok)%Z ->
  (forall i p w, nth_error ptrs i = Some p -> nth_error tks i = Some w ->
     bytes_at rsegs m p (w ++ [Z_to_bv 8 0]) /\ Forall (fun c => bv_unsigned c <> 0%Z) w /\ (4096 <= p)%Z /\
     (p + Z.of_nat (length w) + 1 <= bv_unsigned sp - 48)%Z) ->
  mem_inv rsegs m ->
  evt rsegs (psw_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m T ptrs tks)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 line) (Z_to_bv 64 tok) (Z_to_bv 64 ntok) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17e94) fc None m (seg_rom rsegs)).
Proof.
  intros SLEN SNCMP ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m line tok ntok lo T slackT ptrs tks BL NZT PADT ST LO DL HT TM LPT NTK NT TK HW MI.
  pose proof (bytes_at_bound _ _ _ _ BL) as LB. rewrite length_app in LB, DL. cbn [length] in LB, DL.
  pose proof (bytes_at_bound _ _ _ _ HT) as LT. rewrite cat8_len in LT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UL : bv_unsigned (Z_to_bv 64 line) = line) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 ntok) = ntok) by (apply unsigned_lit; lia).
  destruct (Z.eq_dec ntok 4) as [N4|N4]; [|destruct (Z.eq_dec ntok 5) as [N5|N5]].
  3: { carve_frame 48%nat ST.
       apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
       cbn [mk_CB_cells app firstn skipn] in FR.
       do 12 step.
       rewrite UN, (ntok_ltu ntok NT), (proj2 (Z.eqb_neq _ _) N4), (proj2 (Z.eqb_neq _ _) N5). cbn [orb negb].
       cbv iota.
       do 8 step.
       apply evt_done. left. split.
       { subst ntok. destruct tks as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 tks']]]]]]; cbn [length] in *; try lia; reflexivity. }
       unfold psw_ref. do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM]. }
  - destruct tks as [|w0 [|w1 [|w2 [|w3 [|w4 tks']]]]]; cbn [length] in NTK; try lia.
    destruct ptrs as [|q0 [|q1 [|q2 [|q3 [|q4 ptrs']]]]]; cbn [length] in LPT; try lia.
    destruct (HW 3%nat q3 w3 eq_refl eq_refl) as (B3 & Z3 & P3a & P3b).
    clear HW.
    destruct (dash_cases w3 Z3) as (c0 & C0 & DC).
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app firstn skipn] in FR.
    do 12 step.
    rewrite UN, (ntok_ltu _ NT), (proj2 (Z.eqb_eq _ _) N4). cbn [orb negb]. cbv iota.
    step.
    call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T slackT).
    1-4: rewrite ?UL; first [eassumption | lia].
    cbv delta [mkR].
    do 2 step.
    rewrite len_ltu by lia.
    destruct (Verbs.line_max <? Z.of_nat (length T))%Z eqn:LM; cbv iota.
    + do 8 step. apply evt_done. left. split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM; reflexivity|].
      unfold psw_ref. do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
    + pose proof (read_ptr _ _ _ 3 q3 HT eq_refl) as R3. change (8 * Z.of_nat 3)%Z with 24%Z in R3.
      pose proof (read1 _ _ _ 0 c0 B3 ltac:(lia) C0) as RC0. rewrite Z.add_0_r in RC0.
      cbn [length] in LT.
      assert (UT : bv_unsigned (Z_to_bv 64 tok) = tok) by (apply unsigned_lit; lia).
      step. step. cond_by false.
      step. step. step. cond_by false.
      step. zstep. zstep. zstep.
      rewrite eqb_byte_lit by lia.
      pose proof (read_ptr _ _ _ 1 q1 HT eq_refl) as R1. change (8 * Z.of_nat 1)%Z with 8%Z in R1.
      pose proof (read_ptr _ _ _ 2 q2 HT eq_refl) as R2. change (8 * Z.of_nat 2)%Z with 16%Z in R2.
      clear NTK. subst ntok.
      destruct DC as [[D0 DL0]|[D0 (c1 & C1 & DC1)]].
      * rewrite (proj2 (Z.eqb_neq _ _) D0). cbn [negb]. cbv iota.
        step. step. if_true.
        step. step. step. cond_by false. step. step. step. cond_by false.
        step. step. cond_by false. step. step. step. cond_by false. do 4 step.
        apply evt_done. right. exists w1, w2, w3, None, q1, q2, q3, 0%Z.
        split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM, DL0; reflexivity|].
        split; [unfold acc_shape; repeat split|].
        unfold psw_call. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact FR].
      * rewrite (proj2 (Z.eqb_eq _ _) D0). cbn [negb]. cbv iota.
        pose proof (read1 _ _ _ 1 c1 B3 ltac:(lia) C1) as RC1.
        zstep. zstep. rewrite eqb_byte_lit by lia.
        destruct (Z.eqb_spec (bv_unsigned c1) 0) as [Z1|Z1]; cbv iota.
        -- do 8 step. apply evt_done. left.
           split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM, (proj1 DC1 Z1); reflexivity|].
           unfold psw_ref. do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
        -- assert (DL0 : Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown = false).
           { destruct (Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown); [|reflexivity]. exfalso. apply Z1, DC1. reflexivity. }
           step. step. if_true.
           step. step. step. cond_by false. step. step. step. cond_by false.
           step. step. cond_by false. step. step. step. cond_by false. do 4 step.
           apply evt_done. right. exists w1, w2, w3, None, q1, q2, q3, 0%Z.
           split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM, DL0; reflexivity|].
           split; [unfold acc_shape; repeat split|].
           unfold psw_call. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact FR].
  - destruct tks as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 tks']]]]]]; cbn [length] in NTK; try lia.
    destruct ptrs as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 ptrs']]]]]]; cbn [length] in LPT; try lia.
    destruct (HW 3%nat q3 w3 eq_refl eq_refl) as (B3 & Z3 & P3a & P3b).
    destruct (HW 4%nat q4 w4 eq_refl eq_refl) as (B4 & Z4 & P4a & P4b).
    clear HW.
    destruct (dash_cases w3 Z3) as (c0 & C0 & DC).
    assert (NZV : Forall (fun c => bv_unsigned c <> 0%Z) Verbs.Lit.word_verdict)
      by (repeat constructor; vm_compute; discriminate).
    destruct (sw_prefix 7 Verbs.Lit.word_verdict w4 eq_refl NZV Z4) as (v & SV & RV & QV).
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app firstn skipn] in FR.
    do 12 step.
    rewrite UN, (ntok_ltu _ NT), (proj2 (Z.eqb_neq _ _) N4), (proj2 (Z.eqb_eq _ _) N5). cbn [orb negb]. cbv iota.
    step.
    call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T slackT).
    1-4: rewrite ?UL; first [eassumption | lia].
    cbv delta [mkR].
    do 2 step.
    rewrite len_ltu by lia.
    destruct (Verbs.line_max <? Z.of_nat (length T))%Z eqn:LM; cbv iota.
    + do 8 step. apply evt_done. left. split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM; reflexivity|].
      unfold psw_ref. do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
    + pose proof (read_ptr _ _ _ 3 q3 HT eq_refl) as R3. change (8 * Z.of_nat 3)%Z with 24%Z in R3.
      pose proof (read1 _ _ _ 0 c0 B3 ltac:(lia) C0) as RC0. rewrite Z.add_0_r in RC0.
      cbn [length] in LT.
      step. step. cond_by false.
      step. step. step. cond_by false.
      step. zstep. zstep. zstep.
      rewrite eqb_byte_lit by lia.
      pose proof (read_ptr _ _ _ 4 q4 HT eq_refl) as R4. change (8 * Z.of_nat 4)%Z with 32%Z in R4.
      clear NTK. subst ntok.
      destruct DC as [[D0 DL0]|[D0 (c1 & C1 & DC1)]].
      * rewrite (proj2 (Z.eqb_neq _ _) D0). cbn [negb]. cbv iota.
        step. step. if_false.
        step. step. cond_by false. step. step. step. cond_by false. do 6 step.
        call (SNCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                (w4 ++ [Z_to_bv 8 0]) Verbs.Lit.word_verdict v).
        { rewrite unsigned_lit by lia. exact B4. }
        { rewrite unsigned_lit by lia. apply key_bytes. assumption. }
        { unfold strncmp_model. rewrite unsigned_lit by lia. exact SV. }
        { assumption. }
        step. rewrite eqb_small by lia.
        pose proof (read_ptr _ _ _ 1 q1 HT eq_refl) as R1. change (8 * Z.of_nat 1)%Z with 8%Z in R1.
        pose proof (read_ptr _ _ _ 2 q2 HT eq_refl) as R2. change (8 * Z.of_nat 2)%Z with 16%Z in R2.
        destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb]; cbv iota.
        -- step. step. step. cond_by true.
           step. step. cond_by false. step. step. step. cond_by false.
           step. step. cond_by false. step. step. step. cond_by false. do 4 step.
           apply evt_done. right. exists w1, w2, w3, (Some (skipn 8 w4)), q1, q2, q3, (q4 + 8)%Z.
           assert (HP : Verbs.has_prefix Verbs.Lit.word_verdict w4 = true) by (apply QV; exact V0).
           split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM, DL0; cbn [orb]; rewrite HP; reflexivity|].
           split.
           { unfold acc_shape. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
             split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
             exists q4, w4. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
             split; [|reflexivity]. unfold Verbs.has_prefix in HP. apply andb_prop in HP. destruct HP as [HP _].
             apply Nat.leb_le in HP. exact HP. }
           unfold psw_call. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact FR].
        -- do 8 step. apply evt_done. left.
           split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM, DL0; cbn [orb];
                   destruct (Verbs.has_prefix Verbs.Lit.word_verdict w4) eqn:HP; [exfalso; apply V0, QV; reflexivity | reflexivity]|].
           unfold psw_ref. do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
      * rewrite (proj2 (Z.eqb_eq _ _) D0). cbn [negb]. cbv iota.
        pose proof (read1 _ _ _ 1 c1 B3 ltac:(lia) C1) as RC1.
        zstep. zstep. rewrite eqb_byte_lit by lia.
        destruct (Z.eqb_spec (bv_unsigned c1) 0) as [Z1|Z1]; cbv iota.
        -- do 8 step. apply evt_done. left.
           split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM, (proj1 DC1 Z1); reflexivity|].
           unfold psw_ref. do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
        -- assert (DL0 : Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown = false).
           { destruct (Verbs.list_eqb w3 Verbs.Lit.word_layout_unknown); [|reflexivity]. exfalso. apply Z1, DC1. reflexivity. }
           step. step. if_false.
           step. step. cond_by false. step. step. step. cond_by false. do 6 step.
           call (SNCMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                   (w4 ++ [Z_to_bv 8 0]) Verbs.Lit.word_verdict v).
           { rewrite unsigned_lit by lia. exact B4. }
           { rewrite unsigned_lit by lia. apply key_bytes. assumption. }
           { unfold strncmp_model. rewrite unsigned_lit by lia. exact SV. }
           { assumption. }
           step. rewrite eqb_small by lia.
           pose proof (read_ptr _ _ _ 1 q1 HT eq_refl) as R1. change (8 * Z.of_nat 1)%Z with 8%Z in R1.
           pose proof (read_ptr _ _ _ 2 q2 HT eq_refl) as R2. change (8 * Z.of_nat 2)%Z with 16%Z in R2.
           destruct (Z.eqb_spec v 0) as [V0|V0]; cbn [negb]; cbv iota.
           ++ step. step. step. cond_by true.
              step. step. cond_by false. step. step. step. cond_by false.
              step. step. cond_by false. step. step. step. cond_by false. do 4 step.
              apply evt_done. right. exists w1, w2, w3, (Some (skipn 8 w4)), q1, q2, q3, (q4 + 8)%Z.
              assert (HP : Verbs.has_prefix Verbs.Lit.word_verdict w4 = true) by (apply QV; exact V0).
              split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM, DL0; cbn [orb]; rewrite HP; reflexivity|].
              split.
              { unfold acc_shape. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
                split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
                exists q4, w4. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
                split; [|reflexivity]. unfold Verbs.has_prefix in HP. apply andb_prop in HP. destruct HP as [HP _].
                apply Nat.leb_le in HP. exact HP. }
              unfold psw_call. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact FR].
           ++ do 8 step. apply evt_done. left.
              split; [cbn [tl Verbs.pin_set_words_m]; rewrite LM, DL0; cbn [orb];
                      destruct (Verbs.has_prefix Verbs.Lit.word_verdict w4) eqn:HP; [exfalso; apply V0, QV; reflexivity | reflexivity]|].
              unfold psw_ref. do 15 eexists. split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Lemma eqb_wide : forall v, (- 2 ^ 64 < v < 2 ^ 64)%Z -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0)%Z.
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2 ^ 64)%Z with 0%Z.
  destruct (Z.eqb_spec v 0) as [E|E]; [subst; reflexivity|].
  apply Z.eqb_neq. intros C. apply E. apply Z.mod_divide in C; [|lia]. destruct C as [k Hk]. nia.
Qed.

Lemma psw_mid_mem : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (T : list byte) (ptrs : list Z) (tks : list (list byte)) ms',
  psw_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m T ptrs tks ms' ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m (ms_mem ms') /\ wmono rsegs m (ms_mem ms').
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m T ptrs tks ms'
    [[_ (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM)]
    |(u & f & l & v & p1 & p2 & p3 & pv & _ & _ &
      (t0 & t1 & t2 & x8 & x9 & a4 & a5 & a6 & a7 & x18 & x19 & t3 & t4 & t5 & t6 & m' & junk & -> & MU & WM & _))];
    cbn [ms_mem]; split; assumption.
Qed.

Lemma psw_ret_nz :
  forall ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 : word) (junk : list byte) (r : Z),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 junk; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  (48 <= bv_unsigned sp0)%Z -> (- 2 ^ 63 < r < 2 ^ 63)%Z -> r <> 0%Z ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                              s02 s03 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17f80) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 junk r FR SPR RR NZ.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  step. step. rewrite eqb_wide by lia. rewrite (proj2 (Z.eqb_neq _ _) NZ). cbn [negb]. cbv iota.
  do 8 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma psw_to_lv2 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17f8c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x1731c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17f80) fc None m (seg_rom rsegs)).
Proof.
  intros. step. step. if_false. step. apply evt_done. reflexivity.
Qed.

Lemma psw_ret_z :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 : word) (junk : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 48) [CB 8 junk; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  (48 <= bv_unsigned sp0)%Z ->
  evt rsegs
    (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                              s02 s03 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17f8c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 junk FR SPR.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 9 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 48 + 48)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma psw_g8_found :
  forallb (fun i => match find_segment rsegs (0x33fe8 + Z.of_nat i) 1 with Some _ => true | None => false end)
    (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YN03 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecSeq RecStep RecTail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import pins_set_c lv2_refusals_forget_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
Local Open Scope Z_scope.

Lemma psw_le_at_bytes : forall (B : malloc_syms) m a bs, VerbsB.le_at B m a bs -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at (ms_segs B) m a bs.
Proof.
  unfold VerbsB.le_at, blk_data. intros B m a bs H Ha Hb. split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
  pose proof (H (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. exact E.
Qed.

Lemma psw_present_bytes : forall segs m a (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> present m (a + i)) -> exists bs, length bs = k /\ bytes_at segs m a bs.
Proof.
  intros segs m a k Ha Hk H. destruct (present_rw_cells segs m a k Ha Hk H) as [junk [[Hwf Hb] _]].
  exists junk. cbn in Hwf. split; [tauto|]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma psw_wr_static : forall m a, (0x22d40 <= a < 0x22d48 \/ 0x54730 <= a < 0x54738) -> writable_at rsegs m a.
Proof.
  intros m a Ha. unfold writable_at, wview. destruct (m (Z_to_bv 64 a)) as [b|]; [discriminate|].
  assert (C : a = 0x22d40 \/ a = 0x22d41 \/ a = 0x22d42 \/ a = 0x22d43 \/ a = 0x22d44 \/ a = 0x22d45 \/
              a = 0x22d46 \/ a = 0x22d47 \/ a = 0x54730 \/ a = 0x54731 \/ a = 0x54732 \/ a = 0x54733 \/
              a = 0x54734 \/ a = 0x54735 \/ a = 0x54736 \/ a = 0x54737) by lia.
  repeat (destruct C as [C|C]; [subst a; intro H; vm_compute in H; discriminate H|]).
  subst a; intro H; vm_compute in H; discriminate H.
Qed.

Lemma psw_f18_of_le : forall m (can : word),
  (forall i, 0 <= i < 8 -> mbyte rsegs m (0x22d40 + i) = nth_error (le8 (Z_to_bv 64 0x54730)) (Z.to_nat i)) ->
  (forall i, 0 <= i < 8 -> mbyte rsegs m (0x54730 + i) = nth_error (le8 can) (Z.to_nat i)) ->
  f18_words rsegs m.
Proof.
  intros m can H1 H2.
  unfold f18_words, OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.snprintf_c.GOT_GUARD,
    OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.snprintf_c.GUARD. split; [|exists can];
    (split; [split; [cbn; tauto|] | split; [lia|]; split; [cbn; lia|]; intros i Hi; apply psw_wr_static; cbn in Hi; lia]);
    cbn [cells_bytes cbytes]; rewrite app_nil_r; (split; [lia|]); rewrite length_le8; (split; [lia|]);
    intros i Hi; [pose proof (H1 (Z.of_nat i) ltac:(lia)) as E | pose proof (H2 (Z.of_nat i) ltac:(lia)) as E];
    rewrite Nat2Z.id in E; exact E.
Qed.

Lemma psw_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma psw_le_byte_bv : forall v k, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v k Hv. unfold le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Mem.Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

Lemma psw_word_le_at : forall (B : malloc_syms) m a v, word_mem (ms_segs B) m a v -> 0 <= v < 2 ^ 64 ->
  VerbsB.le_at B m a (le8 (Z_to_bv 64 v)).
Proof.
  unfold VerbsB.le_at, blk_data. intros B m a v Hw Hv i Hi. rewrite length_le8 in Hi.
  unfold le8, word_to_le_bytes. rewrite psw_nth_le_bytes by lia. rewrite unsigned_lit by lia.
  rewrite <- psw_le_byte_bv by exact Hv.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. exact (Hw (Z.to_nat i) ltac:(lia)).
Qed.

Lemma psw_O_blocks : forall segs L A mem R O pn, g_rec_rep segs L A mem R O -> In pn O ->
  In pn (blocks L A) /\ 0 < snd pn.
Proof.
  intros segs L A mem R O pn GR Hin. split; [|exact (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hin)].
  destruct GR as (Q & HR & HO). exact (rep_at_blocks segs _ _ _ _ _ _ _ HR (proj1 (HO pn) Hin)).
Qed.

Lemma sbm_fields : forall ns b, sb_live (sb_mallocs b ns) = sb_live b + Z.of_nat (length ns) /\
  sb_bytes (sb_mallocs b ns) = sb_bytes b + fold_right Z.add 0 ns /\ sb_cap (sb_mallocs b ns) = sb_cap b.
Proof.
  unfold sb_mallocs. induction ns as [|n ns IH]; intros b; cbn [fold_left fold_right length]; [repeat split; lia|].
  destruct (IH (sb_malloc b n)) as (H1 & H2 & H3). rewrite H1, H2, H3. unfold sb_malloc. cbn [sb_live sb_bytes sb_cap].
  repeat split; lia.
Qed.

Lemma sum_le : forall ns, Forall (fun n => n <= 8194) ns -> fold_right Z.add 0 ns <= 8194 * Z.of_nat (length ns).
Proof.
  induction ns as [|n ns IH]; intros H; cbn [fold_right length]; [lia|].
  apply Forall_cons_iff in H as [H1 H2]. specialize (IH H2). lia.
Qed.

Lemma sb_le_n : forall b ns k, Forall (fun n => n <= 8194) ns -> (length ns <= k)%nat ->
  sb_le (sb_mallocs b ns) (VerbsB.sb_n b k).
Proof.
  intros b ns k HF Hk. destruct (sbm_fields ns b) as (H1 & H2 & H3). pose proof (sum_le ns HF).
  unfold sb_le, VerbsB.sb_n, VerbsB.SB_REQ. cbn [sb_live sb_bytes sb_cap]. rewrite H1, H2, H3. repeat split; lia.
Qed.

Lemma room_n : forall b k ns n', room_slots (VerbsB.sb_n b k) 8194 -> Forall (fun n => n <= 8194) ns ->
  (length ns <= k)%nat -> 0 <= n' <= 8194 -> room_slots (sb_mallocs b ns) n'.
Proof. intros b k ns n' R HF Hk Hn. exact (room_slots_mono _ _ n' 8194 (sb_le_n b ns k HF Hk) Hn R). Qed.

Lemma res_n : forall s b ns k, Forall (fun n => n <= 8194) ns -> (length ns <= k)%nat ->
  sb_live b + Z.of_nat k <= sb_cap b -> res_ok_slots s (sb_mallocs b ns) -> res_ok_slots s (VerbsB.sb_n b k).
Proof.
  intros s b ns k HF Hk Hc H. apply (res_ok_slots_le s (sb_mallocs b ns)); [exact (sb_le_n b ns k HF Hk) | | exact H].
  unfold VerbsB.sb_n. cbn [sb_live sb_cap]. exact Hc.
Qed.

Lemma mallocs_app : forall b ns ms, sb_mallocs (sb_mallocs b ns) ms = sb_mallocs b (ns ++ ms).
Proof. intros b ns ms. unfold sb_mallocs. rewrite fold_left_app. reflexivity. Qed.

Lemma res_from : forall s b b0 ns, sb_le b0 (sb_mallocs b ns) -> res_ok_slots s b0 ->
  sb_live b + Z.of_nat (length ns) <= sb_cap b -> res_ok_slots s (sb_mallocs b ns).
Proof.
  intros s b b0 ns LE R0 Hc. apply (res_ok_slots_le s b0 _ LE); [|exact R0].
  destruct (sbm_fields ns b) as (F1 & _ & F3). rewrite F1, F3. exact Hc.
Qed.

Lemma pins_set_code : forall R u f l v, (r_refuse R <> 0 -> declared (r_code R) = true) ->
  snd (pins_set_m R u f l v) = 0 \/ - 2 ^ 31 <= snd (pins_set_m R u f l v) < 0.
Proof.
  intros R u f l v NR. unfold pins_set_m, rec_stub_code, rec_answer_code, rec_record, set_calls, set_spill.
  destruct (Nat.ltb _ _); cbn [r_refuse r_code];
    destruct (Z.eqb_spec (r_refuse R) 0) as [Z0|Z0]; cbn [snd];
    first [left; reflexivity | right; apply declared_range, NR, Z0].
Qed.

Definition psw_kept_rel (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
    getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Ltac psw_kept X :=
  intros rr Hrr Nrr2 Nrr8 Nrr9 Nrr18 Nrr19; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27)
    by lia;
  clear Hrr Nrr2 Nrr8 Nrr9 Nrr18 Nrr19;
  repeat (destruct CC as [CC|CC]; [subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
    simp_regs; first [reflexivity | unfold getr; reflexivity]|]);
  subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Ltac psw_saved X :=
  match goal with |- getr _ (Z_to_bv 5 ?n) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 n) X eq_refl); simp_regs; first [reflexivity | unfold getr; reflexivity] end.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GUARDV : ms_guard B = 0x54730.
Hypothesis GFRAME : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BSP : block_slack_present B API.
Hypothesis CTXO : ctx_owned B API.
Hypothesis SLEN : strlen_contract.
Hypothesis SNCMP : strncmp_contract.
Hypothesis PSET : pins_set_contract B API.
Hypothesis LV2 : forall fx' : YK11.FPState, @lv2_refusals_forget_contract fx' rc B API.

Lemma psw_excl : forall L A mem md R O a n, aa_MR API L A mem md -> g_rec_rep (ms_segs B) L A mem R O ->
  In (a, n) (blocks L A) -> 0 < n -> ~ In (a, n) O -> ~ In a (map fst O).
Proof.
  intros L A mem md R O a n HM GR Hb Hn NO Hin. apply in_map_iff in Hin as ([a' k] & Ea & Hk). cbn [fst] in Ea. subst a'.
  destruct (psw_O_blocks _ _ _ _ _ _ _ GR Hk) as [Hkb Hkp]. cbn [snd] in Hkp.
  pose proof (blocks_same_addr B _ (aa_laws API) L A mem md a n k HM Hb Hkb Hn Hkp) as E. subst k. exact (NO Hk).
Qed.

Lemma psw_img_low8 : forall a, 0x33fe8 <= a < 0x33ff0 -> in_img B a.
Proof using SEGS.
  intros a Ha. apply (in_img_found B SEGS); [lia|].
  pose proof (proj1 (forallb_forall _ _) psw_g8_found (Z.to_nat (a - 0x33fe8)) ltac:(apply in_seq; lia)) as H.
  cbv beta in H. rewrite Z2Nat.id in H by lia. replace (0x33fe8 + (a - 0x33fe8)) with a in H by ring.
  destruct (find_segment rsegs a 1); [discriminate | discriminate H].
Qed.

Lemma psw_not_rec : forall L A mem md q k a, aa_MR API L A mem md -> In (q, k) (blocks L A) -> 0 < k ->
  q <= a < 8 * ((q + k + 7) / 8) -> ~ rec_area a.
Proof using SEGS GFRAME AX.
  intros L A mem md q k a HM Hb Hk Ha HR.
  assert (HRr : 0x33ff0 <= a < 0x33ff0 + 1020) by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in HR; lia).
  destruct (proj1 (YI04.blocks_In L A q k) Hb) as (p & Ep & Hp).
  assert (IMG : forall c, 0x33fe8 <= c < 0x33ff0 + 1020 -> in_img B c).
  { intros c Hc. destruct (Z_lt_ge_dec c 0x33ff0) as [D|D]; [exact (psw_img_low8 c ltac:(lia))|].
    refine (proj1 (GFRAME c _)). exists 0x33ff0, 1020. split; [left; reflexivity | lia]. }
  pose proof (Z.div_mod (q + k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + k + 7) 8 ltac:(lia)).
  destruct (Z_lt_ge_dec a (q + k)) as [D|D].
  - apply (ax_blocks_img AX L A mem md p k (a - q) HM Hp ltac:(lia)). rewrite Ep.
    replace (q + (a - q)) with a by ring. apply IMG. lia.
  - apply (ax_blocks_img AX L A mem md p k (k - 1) HM Hp ltac:(lia)). rewrite Ep. apply IMG. lia.
Qed.

Lemma psw_slack : forall L A mem md p x q k, aa_MR API L A mem md -> In (q, k) (blocks L A) -> q <= p ->
  p + Z.of_nat (length x) + 1 <= q + k -> bytes_at rsegs mem p (x ++ [Z_to_bv 8 0]) ->
  exists slack, bytes_at rsegs mem p (x ++ Z_to_bv 8 0 :: slack) /\
    (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
    p + Z.of_nat (length x) + 1 + Z.of_nat (length slack) <= 8 * ((q + k + 7) / 8) /\
    8 * ((q + k + 7) / 8) <= q + k + 7.
Proof using BSP.
  intros L A mem md p x q k HM Hb Hqp Hpk HX.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof (block_facts B _ LAWS _ _ _ _ _ _ 0 HM Hb ltac:(lia)) as (_ & Q4 & QC & _).
  set (pad := (- (p + Z.of_nat (length x) + 1)) mod 8).
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADE : (p + Z.of_nat (length x) + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Z.add_mod, Z.mod_mod, <- Z.add_mod by lia.
    replace (p + Z.of_nat (length x) + 1 + - (p + Z.of_nat (length x) + 1)) with 0 by ring. reflexivity. }
  pose proof (Z.div_mod (q + k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + k + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (p + Z.of_nat (length x) + 1 + pad) 8 ltac:(lia)).
  assert (END : p + Z.of_nat (length x) + 1 + pad <= 8 * ((q + k + 7) / 8)) by lia.
  destruct (psw_present_bytes rsegs mem (p + Z.of_nat (length x) + 1) (Z.to_nat pad)) as (slack & SLL & SLB);
    [lia | lia | |].
  { intros i Hi. rewrite Z2Nat.id in Hi by lia.
    destruct (Z_lt_ge_dec (p + Z.of_nat (length x) + 1 + i) (q + k)) as [D|D].
    - destruct (block_facts B _ LAWS _ _ _ _ _ _ (p + Z.of_nat (length x) + 1 + i - q) HM Hb ltac:(lia)) as (P & _).
      replace (p + Z.of_nat (length x) + 1 + i) with (q + (p + Z.of_nat (length x) + 1 + i - q)) by ring. exact P.
    - apply (BSP L A mem md q k (p + Z.of_nat (length x) + 1 + i) HM Hb). lia. }
  exists slack. split.
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact HX|]. rewrite length_app. cbn [length].
    replace (p + Z.of_nat (length x + 1)) with (p + Z.of_nat (length x) + 1) by lia. exact SLB. }
  rewrite SLL, Z2Nat.id by lia. fold pad. lia.
Qed.

Lemma psw_tok_arg : forall L A mem md (O : list (Z * Z)) sp K p x q k, aa_MR API L A mem md ->
  In (q, k) (blocks L A) -> ~ In q (map fst O) -> q <= p -> p + Z.of_nat (length x) + 1 <= q + k ->
  bytes_at rsegs mem p (x ++ [Z_to_bv 8 0]) -> Forall (fun c => bv_unsigned c <> 0) x ->
  Z.of_nat (length x) <= LMAX -> q + k + 7 <= sp - K ->
  str_arg B L A O sp K mem p (Some x).
Proof using SEGS GFRAME AX BSP.
  intros L A mem md O sp K p x q k HM Hb NQ Hqp Hpk HX NZ HL HS.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof (block_facts B _ LAWS _ _ _ _ _ _ 0 HM Hb ltac:(lia)) as (_ & Q4 & QC & _).
  destruct (psw_slack L A mem md p x q k HM Hb Hqp Hpk HX) as (slack & BS & PAD & END & RND).
  unfold str_arg. cbv beta iota. rewrite SEGS.
  split; [lia|]. split.
  { intros Hin. rewrite Forall_forall in NZ. apply (NZ _ Hin). reflexivity. }
  split; [exact HL|].
  exists slack. split; [exact BS|]. split; [exact PAD|].
  split; [left; rewrite length_app; cbn [length]; lia|].
  split.
  { unfold buf_home. right. left. exists q, k. split; [exact Hb|]. split; [exact NQ|]. lia. }
  intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (psw_not_rec L A mem md q k a HM Hb ltac:(lia)). lia.
Qed.

Lemma psw_keep_blocks : forall K S E (O : list (Z * Z)) L A mem md L' A' mem' md',
  rjr B (aa_MR API) K S E (fun pn => In pn O) L A mem md L' A' mem' md' ->
  forall a n, In (a, n) (blocks L A) -> ~ In (a, n) O -> In (a, n) (blocks L' A').
Proof.
  intros K S E O L A mem md L' A' mem' md' RJ a n Hb Hn.
  destruct (proj1 (YI04.blocks_In L A a n) Hb) as (p & Ep & Hp). subst a.
  pose proof RJ as (_ & HWA & _ & _ & HL & _).
  apply (proj2 (YI04.blocks_In L' A' (ptr_addr L p) n)). exists p. split.
  - exact (ptr_addr_stable A L L' p n HWA Hp HL).
  - exact (rjr_in_cur B (aa_MR API) K S E _ L A mem md L' A' mem' md' p n RJ Hp Hn).
Qed.

Lemma psw_final : forall L A regs mem md (O : list (Z * Z)) line nl tok cb ncb ntok (T : list byte) ptrs tks
    L' A' regs' mem' md',
  call_pre_k B (aa_MR API) PSW_K L A regs mem md ->
  rjr B (aa_MR API) PSW_K (spZ regs) psw_writes (fun pn => In pn O) L A mem md L' A' mem' md' ->
  regs_preserved regs regs' ->
  In (line, nl) (blocks L A) -> ~ In (line, nl) O -> VerbsB.le_at B mem line (T ++ [Z_to_bv 8 0]) ->
  Z.of_nat (length T) + 1 <= nl ->
  In (cb, ncb) (blocks L A) -> ~ In (cb, ncb) O -> VerbsB.toks_at B mem tok ptrs tks cb ncb ->
  ntok = Z.of_nat (length tks) -> spZ regs <= tok -> tok + 8 * ntok < 2 ^ 63 ->
  VerbsB.outside B L A PSW_K regs tok (8 * ntok) ->
  call_post_rec B (aa_MR API) PSW_K L A regs mem md psw_writes (fun a => In a (map fst O)) L' A' regs' mem' md' /\
  VerbsB.le_at B mem' line (T ++ [Z_to_bv 8 0]) /\ VerbsB.toks_at B mem' tok ptrs tks cb ncb /\
  (forall pn, In pn (blocks L A) -> ~ In pn O -> In pn (blocks L' A')) /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  blocks_kept B L A mem mem' (fun a => exists j, In (a, j) O) /\
  (exists can', VerbsB.ssp_b B mem' can').
Proof using CTXO GOTG GUARDV AX.
  intros L A regs mem md O line nl tok cb ncb ntok T ptrs tks L' A' regs' mem' md' PRE RJ RP INL NOL HLT LTN
    INC NOC HTK NTK SPT T63 OUTS.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  assert (KV : PSW_K = 13360) by reflexivity.
  pose proof RJ as RJ0.
  destruct RJ as (HM' & HWA & HW' & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  assert (KEEP : forall a n, In (a, n) (blocks L A) -> ~ In (a, n) O -> forall i, 0 <= i < n ->
            mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)).
  { intros a n Hb Hn. destruct (proj1 (YI04.blocks_In L A a n) Hb) as (p & Ep & Hp). subst a.
    intros i Hi. exact (HKP p n i Hp Hn Hi). }
  split.
  { exact (rjr_final B (aa_MR API) CTXO PSW_K psw_writes (fun pn => In pn O) (fun a => In a (map fst O))
             L A regs mem md L' A' regs' mem' md' PRE RJ0 RP (fun a n G => in_map fst O (a, n) G)). }
  split.
  { unfold VerbsB.le_at, blk_data in *. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (KEEP line nl INL NOL i ltac:(lia)). apply HLT. rewrite length_app. cbn [length]. lia. }
  split.
  { destruct HTK as (TM & LP & HTA & HW). split; [exact TM|]. split; [exact LP|]. split.
    - unfold VerbsB.le_at, blk_data in *. intros i Hi. rewrite <- (HTA i Hi).
      rewrite cat8_len in Hi.
      destruct (OUTS i ltac:(lia)) as [_ NS].
      destruct (HF (tok + i)) as [E _].
      + left. lia.
      + lia.
      + intros He. apply NS. right. exact He.
      + unfold psw_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE. lia.
      + exact E.
    - intros i p w Hp Hw. destruct (HW i p w Hp Hw) as (LE & NZ & L8 & CBP & PCB & DIS).
      split; [|split; [exact NZ|]; split; [exact L8|]; split; [exact CBP|]; split; [exact PCB | exact DIS]].
      unfold VerbsB.le_at, blk_data in *. intros j Hj. rewrite <- (LE j Hj).
      rewrite length_app in Hj. cbn [length] in Hj.
      replace (p + j) with (cb + (p - cb + j)) by ring.
      rewrite (KEEP cb ncb INC NOC (p - cb + j) ltac:(lia)). reflexivity. }
  split; [intros [a n] Hb Hn; exact (psw_keep_blocks _ _ _ O L A mem md L' A' mem' md' RJ0 a n Hb Hn)|].
  split; [exact HLen|].
  split.
  { intros a k i Hb Hg Hi. assert (Hn : ~ In (a, k) O) by (intros H; apply Hg; exists k; exact H).
    exact (KEEP a k Hb Hn i Hi). }
  destruct (ax_statics AX L' A' mem' md' HM') as (WG & (g & Hg & WGD) & _).
  exists (Z_to_bv 64 g). unfold VerbsB.ssp_b, VerbsB.SSP_GOT_B, VerbsB.SSP_GUARD_B. split.
  - rewrite <- GOTG, <- GUARDV. apply psw_word_le_at; [exact WG | rewrite GUARDV; lia].
  - rewrite <- GUARDV. apply psw_word_le_at; [exact WGD | exact Hg].
Qed.

Theorem pin_set_words_holds : pin_set_words_contract B API.
Proof using SEGS ERRNO_LOW GOTG GUARDV GFRAME AX BSP CTXO SLEN SNCMP PSET LV2.
  unfold pin_set_words_contract, PIN_SET_WORDS, PSW_MALLOCS, PSW_REQ.
  intros L A regs mem md b R O line nl tok cb ncb ntok T ptrs tks can PRE RA FRM A0R A1R A2R INL NOL HLT NZT LTN
    INC NOC HTK NTK NTR V0 SPT T63 OUTS GR NREF SSP RES ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  assert (KV : PSW_K = 13360) by reflexivity.
  assert (LIVE : sb_live b + 8 <= sb_cap b).
  { destruct ROOM as (_ & R1 & _). unfold VerbsB.sb_n in R1. cbn [sb_live sb_cap] in R1. lia. }
  destruct PRE as (PRE0 & HTS).
  pose proof PRE0 as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (NOWN : forall L' A' mem' md' a, aa_MR API L' A' mem' md' -> alloc_ceiling <= a -> ~ owned B L' A' a).
  { intros L' A' mem' md' a HM Ha Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HM Ho). lia. }
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  change (bv_unsigned (getr regs 2)) with (bv_unsigned sp) in SPT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (RA0 : ret_pc (reg_get regs 1) = reg_get regs 1) by exact (ret_pc_of_ok _ HRA).
  pose proof (block_facts B _ LAWS _ _ _ _ _ _ 0 HMR INL ltac:(lia)) as (_ & L4 & LC & _).
  pose proof HTK as (TM & LPT & HTA & HW).
  assert (P0 : exists p0, nth_error ptrs 0 = Some p0).
  { destruct ptrs as [|p0 ptrs']; [|exists p0; reflexivity].
    destruct tks; [discriminate V0 | discriminate LPT]. }
  destruct P0 as (p0 & P0).
  destruct (HW 0%nat p0 _ P0 V0) as (_ & _ & _ & CB0 & PCB0 & _).
  pose proof (block_facts B _ LAWS _ _ _ _ _ _ 0 HMR INC ltac:(lia)) as (_ & C4 & CBC & _).
  assert (HLB : bytes_at rsegs mem line (T ++ [Z_to_bv 8 0])).
  { rewrite <- SEGS. apply psw_le_at_bytes; [exact HLT | lia | rewrite length_app; cbn [length]; lia]. }
  destruct (psw_slack L A mem md line T line nl HMR INL ltac:(lia) ltac:(lia) HLB) as (slack & BSL & PADL & ENDL & RNDL).
  assert (HTB : bytes_at rsegs mem tok (concat (map (fun p => le8 (Z_to_bv 64 p)) ptrs))).
  { rewrite <- SEGS. apply psw_le_at_bytes; [exact HTA | lia | rewrite cat8_len; lia]. }
  assert (NZ0 : ~ In (Z_to_bv 8 0) T).
  { intros Hin. rewrite Forall_forall in NZT. apply (NZT _ Hin). reflexivity. }
  rewrite SEGS in RA, HWS, HERR.
  assert (HW' : forall i p w, nth_error ptrs i = Some p -> nth_error tks i = Some w ->
     bytes_at rsegs (normalize rsegs mem) p (w ++ [Z_to_bv 8 0]) /\ Forall (fun c => bv_unsigned c <> 0) w /\
     4096 <= p /\ p + Z.of_nat (length w) + 1 <= bv_unsigned sp - 48).
  { intros i p w Hp Hw. destruct (HW i p w Hp Hw) as (LE & NZ & _ & CBP & PCB & _).
    split; [|split; [exact NZ | lia]].
    apply (bytes_at_normalize rsegs); [exact RA|]. rewrite <- SEGS.
    apply psw_le_at_bytes; [exact LE | lia | rewrite length_app; cbn [length]; lia]. }
  pose proof (bytes_at_normalize rsegs mem line _ RA BSL) as BSN.
  pose proof (bytes_at_normalize rsegs mem tok _ RA HTB) as HTBN.
  assert (ST : stk rsegs (normalize rsegs mem) (bv_unsigned sp - PSW_K) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E].
    assert (NE : normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
    unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  pose proof (rjr_init B (aa_MR API) PSW_K psw_writes (fun pn => In pn O) L A regs mem md PRE0 ltac:(lia)) as RJ0.
  change (spZ regs) with (bv_unsigned sp) in RJ0.
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 line) by exact A0R.
    assert (R11 : reg_get regs 11 = Z_to_bv 64 tok) by exact A1R.
    assert (R12 : reg_get regs 12 = Z_to_bv 64 ntok) by exact A2R.
    rewrite R10, R11, R12.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (psw_run1 SLEN SNCMP) with (lo := bv_unsigned sp - PSW_K) (slackT := slack) (ptrs := ptrs) (tks := tks);
      [exact BSN | exact NZ0 | exact PADL | exact ST | lia | rewrite length_app; cbn [length]; lia
      | exact HTBN | exact TM | exact LPT | exact NTK | exact NTR | exact SPT | exact HW' | apply mem_inv_normalize]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1').
  pose proof REL1 as (_ & _ & _ & _ & _ & _ & _ & MREL1).
  pose proof Q1 as Q1m. apply psw_mid_mem in Q1m. destruct Q1m as [MU1n WM1n].
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem RA) MREL1 RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem RA) MREL1 RO1 WM1n) as WM1.
  pose proof (ro_agree_same rsegs _ _ RA RO1) as RA1.
  remember (ms_mem can1) as m1 eqn:EM1.
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside [(bv_unsigned sp - 48, bv_unsigned sp)] a ->
            bv_unsigned sp - 48 <= a < bv_unsigned sp) by (intros a _ H; cbn in H; lia).
  assert (IN1 : forall a, ~ (bv_unsigned sp - 48 <= a < bv_unsigned sp) ->
            Frame.outside [(bv_unsigned sp - 48, bv_unsigned sp)] a) by (intros a H; cbn; split; [exact H | exact I]).
  assert (RJ1 : rjr B (aa_MR API) PSW_K (bv_unsigned sp) psw_writes (fun pn => In pn O) L A mem md L A m1 md).
  { apply (rjr_munch B (aa_MR API) SEGS LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ RJ0 MU1 ltac:(rewrite SEGS; exact WM1)).
    - intros a Ra Hn _. left. pose proof (OUT1 a Ra Hn). lia.
    - intros a Ra Hn. pose proof (OUT1 a Ra Hn). apply (NOWN _ _ _ _ a HMR). lia.
    - intros a Ha. apply IN1. lia.
    - intros p n i Hp _ Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hp Hi) as (_ & H4 & H5 & _).
      apply IN1. lia.
    - intros p n i Hp Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hp Hi) as (Hpr & H4 & H5 & _).
      apply (munch_present _ _ _ _ MU1); [lia | apply IN1; lia | exact Hpr]. }
  pose proof RJ1 as (MR1 & _).
  assert (GR1m : g_rec_rep (ms_segs B) L A m1 R O).
  { unfold g_rec_rep in *. apply (rec_rep_frame (ms_segs B) G_REC REC_SC L A mem R O L A m1 GR).
    - intros a Ha. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha.
      split; [apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply IN1; lia]|].
      intros W. apply (munch_writable _ _ _ _ a MU1 ltac:(lia) ltac:(apply IN1; lia)). exact W.
    - intros p n i Hin Hi. destruct (psw_O_blocks _ _ _ _ _ _ (p, n) GR Hin) as [Hb _].
      destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hb Hi) as (_ & Hp4 & Hpc & _).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply IN1; lia].
    - intros pn Hin. exact (proj1 (psw_O_blocks _ _ _ _ _ _ pn GR Hin)). }
  pose proof SSP as (S1 & S2). unfold VerbsB.le_at, blk_data, VerbsB.SSP_GOT_B, VerbsB.SSP_GUARD_B in S1, S2.
  rewrite SEGS in S1, S2.
  assert (F18m : f18_words rsegs m1).
  { apply (psw_f18_of_le m1 can).
    - intros i Hi. rewrite (munch_mbyte rsegs _ _ _ (0x22d40 + i) MU1 ltac:(lia) ltac:(apply IN1; lia)).
      apply S1. rewrite length_le8. lia.
    - intros i Hi. rewrite (munch_mbyte rsegs _ _ _ (0x54730 + i) MU1 ltac:(lia) ltac:(apply IN1; lia)).
      apply S2. rewrite length_le8. lia. }
  destruct Q1 as [[REJ (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _ & _)]
    | (u & f & l & vv & p1 & p2 & p3 & pv & PSM & ACC & (t0' & t1' & t2' & x8' & x9' & a4' & a5' & a6' & a7' & x18' & x19'
       & t3' & t4' & t5' & t6' & m' & junk & -> & _ & _ & FR1n))].
  - destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 _]. rewrite <- EM1 in EC1. clear EM1. subst can1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1' eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 (-902)) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (RP1 : regs_preserved regs R1).
    { intros rr Hrr. unfold callee_saved in Hrr.
      assert (C : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
                  rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
      repeat (destruct C as [C|C]; [subst rr; psw_saved X1|]). subst rr. psw_saved X1. }
    destruct (psw_final L A regs mem md O line nl tok cb ncb ntok T ptrs tks L A R1 m1 md PRE0 RJ1 RP1 INL NOL HLT LTN
      INC NOC HTK NTK SPT T63 OUTS) as (POST & HLT1 & HTK1 & KB1 & LEN1 & BK1 & SSP1).
    rewrite RA0. apply SR_ret.
    exists fx, L, A, R1, m1, md, O, 0%nat.
    split; [reflexivity|].
    split; [split; [exact FRM | intros; reflexivity]|].
    split; [exact POST|].
    split; [exact RA1|].
    split.
    { unfold VerbsRun.pin_set_run. rewrite REJ. unfold Verbs.reject. cbv beta iota zeta.
      split; [rewrite <- SEGS; exact GR1m | exact E1_10]. }
    split; [exact HLT1|]. split; [exact HTK1|]. split; [exact KB1|].
    split; [intros pn Hpn; destruct (in_dec pair_dec pn O) as [H|H]; [right; exact H | left; split; assumption]|].
    split; [intros pn _ H; exact H|].
    split; [exact LEN1|]. split; [exact BK1|]. split; [exact SSP1|].
    split; [lia|].
    exact (res_n A b [] 0 (Forall_nil _) ltac:(cbn; lia) ltac:(lia) RES).
  - destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 _]. rewrite <- EM1 in EC1. clear EM1. subst can1.
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1' eq_refl eq_refl) as (R1 & -> & X1).
    cbn [ms_mem] in MREL1.
    pose proof (rw_cells_rel rsegs _ _ _ _ MREL1 FR1n) as FR1.
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x17f80) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 p1) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 p2) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_12 : getr R1 12 = Z_to_bv 64 p3) by (rewrite (getr_of_eqv _ _ 12 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_13 : getr R1 13 = Z_to_bv 64 pv) by (rewrite (getr_of_eqv _ _ 13 X1 eq_refl); simp_regs; reflexivity).
    assert (K1 : psw_kept_rel regs R1) by psw_kept X1.
    assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    assert (RET1 : YK0s.ret_ok (getr R1 1)) by (rewrite E1_1; apply bv_eq; vm_compute; reflexivity).
    destruct ACC as (AP1 & AP2 & AP3 & AT1 & AT2 & AT3 & AV).
    assert (TOKM : forall i p w, nth_error ptrs i = Some p -> nth_error tks i = Some w ->
              bytes_at rsegs m1 p (w ++ [Z_to_bv 8 0]) /\ Forall (fun c => bv_unsigned c <> 0) w /\
              Z.of_nat (length w) <= 8192 /\ cb <= p /\ p + Z.of_nat (length w) + 1 <= cb + ncb).
    { intros i p w Hp Hw. destruct (HW i p w Hp Hw) as (LE & NZ & L8 & CBP & PCB & _).
      split; [|tauto].
      apply (bytes_at_transfer rsegs mem).
      - rewrite <- SEGS. apply psw_le_at_bytes; [exact LE | lia | rewrite length_app; cbn [length]; lia].
      - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
        apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply IN1; lia]. }
    assert (CBO : ~ In cb (map fst O)) by exact (psw_excl L A mem md R O cb ncb HMR GR INC ltac:(lia) NOC).
    assert (SAk : forall i p w, nth_error ptrs i = Some p -> nth_error tks i = Some w ->
              str_arg B L A O (spZ R1) PINS_SET_K m1 p (Some w)).
    { intros i p w Hp Hw. destruct (TOKM i p w Hp Hw) as (BT & NZ & L8 & CBP & PCB).
      apply (psw_tok_arg L A m1 md O _ _ p w cb ncb MR1 INC CBO CBP PCB BT NZ ltac:(unfold LMAX; lia)).
      rewrite SP1. unfold PINS_SET_K. lia. }
    assert (SA4 : str_arg B L A O (spZ R1) PINS_SET_K m1 pv vv).
    { destruct vv as [x|]; cbv beta iota in AV.
      - destruct AV as (p4 & w4 & AP4 & AT4 & EPV & L84 & EX). subst pv x.
        destruct (TOKM 4%nat p4 w4 AP4 AT4) as (BT & NZ & L8 & CBP & PCB).
        rewrite <- (firstn_skipn 8 w4) in BT, NZ.
        rewrite <- app_assoc in BT. apply bytes_at_app in BT. destruct BT as [_ BT].
        rewrite length_firstn, Nat.min_l in BT by exact L84.
        apply Forall_app in NZ. destruct NZ as [_ NZ].
        assert (LS : Z.of_nat (length (skipn 8 w4)) = Z.of_nat (length w4) - 8) by (rewrite length_skipn; lia).
        apply (psw_tok_arg L A m1 md O _ _ (p4 + 8) (skipn 8 w4) cb ncb MR1 INC CBO ltac:(lia) ltac:(lia) BT NZ
                 ltac:(unfold LMAX; lia)).
        rewrite SP1. unfold PINS_SET_K. lia.
      - exact AV. }
    assert (SZ : forall r', r' = 0 \/ - 2 ^ 31 <= r' < 0 ->
               Forall (fun n => n <= 8194) (pins_set_sizes (Some u) (Some f) (Some l) vv r')).
    { intros r' Hr'. pose proof (resp_length r' ltac:(lia)) as RL.
      destruct (TOKM 1%nat p1 u AP1 AT1) as (_ & _ & L1u & _).
      destruct (TOKM 2%nat p2 f AP2 AT2) as (_ & _ & L2f & _).
      destruct (TOKM 3%nat p3 l AP3 AT3) as (_ & _ & L3l & _).
      unfold pins_set_sizes, pins_set_args. cbn [map app sarg].
      destruct vv as [x|]; cbv beta iota in AV; cbn [darg].
      - destruct AV as (p4 & w4 & AP4 & AT4 & _ & _ & ->).
        destruct (TOKM 4%nat p4 w4 AP4 AT4) as (_ & _ & L4w & _).
        rewrite length_skipn. repeat constructor; lia.
      - repeat constructor; first [lia | apply Z.leb_le; vm_compute; reflexivity]. }
    pose proof (pins_set_code R (Some u) (Some f) (Some l) vv NREF) as RR0.
    rewrite <- SEGS.
    eapply SR_bind.
    { apply (PSET L A R1 m1 md p1 p2 p3 pv (Some u) (Some f) (Some l) vv R O b).
      - split; [|rewrite SP1; lia].
        apply (call_pre_k_of_rjr B (aa_MR API) PSW_K (bv_unsigned sp) psw_writes (fun pn => In pn O) L A mem md L A m1 md
                 PINS_SET_K R1 RJ1 RET1).
        + rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
          rewrite Z.mod_add by lia. exact HAL.
        + unfold PINS_SET_K. lia.
        + rewrite SP1. unfold PINS_SET_K. lia.
        + rewrite SP1. lia.
        + rewrite E1_4. exact HTP.
      - exact E1_10.
      - exact E1_11.
      - exact E1_12.
      - exact E1_13.
      - exact (SAk 1%nat p1 u AP1 AT1).
      - exact (SAk 2%nat p2 f AP2 AT2).
      - exact (SAk 3%nat p3 l AP3 AT3).
      - exact SA4.
      - exact GR1m.
      - rewrite SEGS. exact RA1.
      - exact FRM.
      - rewrite SEGS. exact F18m.
      - exact RES.
      - apply (room_n b 7 _ (LMAX + 1) ROOM (SZ _ RR0)); [|unfold LMAX; lia].
        unfold pins_set_sizes, pins_set_args. cbn [length map app]. lia. }
    intros c2 (fx1 & L1 & A1 & R2 & m2 & md1 & R1' & O1 & r & PSM' & -> & FPK & POST1 & ER2 & GR2 & OWN1 & OK1 & ACC1
      & RA2 & F182 & INIT1 & REG1 & LE1 & RS1).
    assert (RES1 : res_ok_slots A1 (sb_mallocs b (pins_set_sizes (Some u) (Some f) (Some l) vv r))).
    { apply (res_from A1 b _ _ LE1 RS1). unfold pins_set_sizes, pins_set_args. cbn [length map app]. lia. }
    pose proof POST1 as (HMR1 & HWF1 & HBD1 & HLE1 & HSTAB1 & HPRES1 & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
    destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & _).
    assert (RJ2 : rjr B (aa_MR API) PSW_K (bv_unsigned sp) psw_writes (fun pn => In pn O) L A mem md L1 A1 m2 md1).
    { eapply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW); [exact RJ1 | exact POST1 | | | | | | |].
      - rewrite SP1. unfold PINS_SET_K. lia.
      - rewrite SP1. lia.
      - intros a Ha _. unfold rec_area in Ha. split; [unfold psw_writes; tauto|].
        unfold REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha. lia.
      - intros p n Hp Hn Hpos. exact (psw_excl L A mem md R O (ptr_addr L p) n HMR GR (user_in_blocks L A p n Hp) Hpos Hn).
      - intros p n Hp _ Hn. destruct (in_dec pair_dec (ptr_addr L p, n) O) as [H|H]; [exact H|].
        exfalso. apply Hn. exact (proj1 (OK1 p n Hp H)).
      - exact REG1.
      - intros H. rewrite INIT1 in H. discriminate. }
    assert (RR : r = 0 \/ - 2 ^ 31 <= r < 0) by (rewrite PSM' in RR0; exact RR0).
    assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 48))
      by exact (eq_trans (HPRES1 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (E2_10 : reg_get R2 10 = Z_to_bv 64 r) by exact ER2.
    pose proof FR1 as FR2. apply (rw_cells_transfer rsegs m1 m2) in FR2.
    2: { intros i Hi. cbn in Hi. rewrite <- SEGS.
         assert (Ha : alloc_ceiling <= bv_unsigned sp - 48 + i < 2 ^ 64) by lia.
         destruct (HFRAME1 (bv_unsigned sp - 48 + i) (or_introl Ha) (NOWN _ _ _ _ _ MR1 (proj1 Ha))
                    (NOWN _ _ _ _ _ HMR1 (proj1 Ha))) as [E W].
         - unfold scratch_k. rewrite SP1. unfold PINS_SET_K. intros [H|H]; lia.
         - unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia.
         - split; [exact E | apply W]. }
    destruct (Z.eq_dec r 0) as [RZ|RNZ].
    + subst r.
      rewrite SEGS, E1_1.
      eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_10. apply psw_to_lv2. }
      intros ms3 (can3 & Q3 & EQ3). subst can3.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
      assert (E3_1 : getr R3 1 = Z_to_bv 64 0x17f8c) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
      assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 48))
        by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; exact E2_2).
      assert (E3_4 : getr R3 4 = reg_get regs 4).
      { rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs.
        exact (eq_trans (HPRES1 4 ltac:(unfold callee_saved; lia)) E1_4). }
      assert (E3_10 : getr R3 10 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
      assert (K3 : psw_kept_rel R2 R3) by psw_kept X3.
      assert (SP3 : spZ R3 = bv_unsigned sp - 48) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
      assert (RET3 : YK0s.ret_ok (getr R3 1)) by (rewrite E3_1; apply bv_eq; vm_compute; reflexivity).
      rewrite <- SEGS.
      eapply SR_bind.
      { apply (LV2 fx1 L1 A1 R3 m2 md1 0 None R1' O1 (sb_mallocs b (pins_set_sizes (Some u) (Some f) (Some l) vv 0))).
        - apply (call_pre_k_of_rjr B (aa_MR API) PSW_K (bv_unsigned sp) psw_writes (fun pn => In pn O) L A mem md
                   L1 A1 m2 md1 LV2_REFUSALS_FORGET_K R3 RJ2 RET3).
          + rewrite SP3. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring.
            rewrite Z.mod_add by lia. exact HAL.
          + unfold LV2_REFUSALS_FORGET_K. lia.
          + rewrite SP3. unfold LV2_REFUSALS_FORGET_K. lia.
          + rewrite SP3. lia.
          + rewrite E3_4. exact HTP.
        - exact E3_10.
        - reflexivity.
        - exact GR2.
        - exact RA2.
        - exact F182.
        - exact RES1.
        - rewrite mallocs_app. apply (room_n b 7 _ (LMAX + 1) ROOM).
          + apply Forall_app. split; [exact (SZ 0 (or_introl eq_refl))|].
            constructor; [apply Z.leb_le; vm_compute; reflexivity | constructor].
          + rewrite length_app. unfold pins_set_sizes, pins_set_args. cbn [length map app]. lia.
          + unfold LMAX. lia. }
      intros c4 (L2 & A2 & R4 & m4 & md2 & O2 & -> & POST2 & GR4 & OWN2 & OK2 & ACC2 & RA4 & F184 & INIT2 & REG2
        & LE2 & RS2).
      assert (RES2 : res_ok_slots A2 (sb_mallocs (sb_mallocs b (pins_set_sizes (Some u) (Some f) (Some l) vv 0))
                                       [lv2_refusals_forget_size None])).
      { apply (res_from A2 _ _ _ LE2 RS2).
        destruct (sbm_fields (pins_set_sizes (Some u) (Some f) (Some l) vv 0) b) as (F1 & _ & F3). rewrite F1, F3.
        unfold pins_set_sizes, pins_set_args. cbn [length map app]. lia. }
      pose proof POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HPRES2 & HVM2 & HFRAME2 & HBLKS2 & HSCR2).
      destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & _).
      pose proof RJ2 as (_ & HWA & _ & _ & HL2 & _).
      assert (NO1 : forall p n, In (p, n) (user_blocks A) -> ~ In (ptr_addr L p, n) O -> ~ In (ptr_addr L1 p, n) O1).
      { intros p n Hp Hn Ho. rewrite (ptr_addr_stable A L L1 p n HWA Hp HL2) in Ho.
        destruct (OWN1 _ Ho) as [H|H]; [exact (Hn H) | exact (H (user_in_blocks L A p n Hp))]. }
      assert (RJ3 : rjr B (aa_MR API) PSW_K (bv_unsigned sp) psw_writes (fun pn => In pn O) L A mem md L2 A2 m4 md2).
      { eapply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW); [exact RJ2 | exact POST2 | | | | | | |].
        - rewrite SP3. unfold LV2_REFUSALS_FORGET_K. lia.
        - rewrite SP3. lia.
        - intros a Ha _. unfold rec_area in Ha. split; [unfold psw_writes; tauto|].
          unfold REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha. lia.
        - intros p n Hp Hn Hpos. cbv beta.
          pose proof (rjr_in_cur B (aa_MR API) _ _ _ _ L A mem md L1 A1 m2 md1 p n RJ2 Hp Hn) as Hp1.
          rewrite <- (ptr_addr_stable A L L1 p n HWA Hp HL2).
          exact (psw_excl L1 A1 m2 md1 R1' O1 (ptr_addr L1 p) n HMR1 GR2 (user_in_blocks L1 A1 p n Hp1) Hpos
                   (NO1 p n Hp Hn)).
        - intros p n Hp Hp1 Hn2. cbv beta. destruct (in_dec pair_dec (ptr_addr L p, n) O) as [H|H]; [exact H|].
          exfalso. apply Hn2. exact (proj1 (OK2 p n Hp1 (NO1 p n Hp H))).
        - exact REG2.
        - intros H. rewrite INIT2 in H. discriminate. }
      pose proof FR2 as FR3. apply (rw_cells_transfer rsegs m2 m4) in FR3.
      2: { intros i Hi. cbn in Hi. rewrite <- SEGS.
           assert (Ha : alloc_ceiling <= bv_unsigned sp - 48 + i < 2 ^ 64) by lia.
           destruct (HFRAME2 (bv_unsigned sp - 48 + i) (or_introl Ha) (NOWN _ _ _ _ _ HMR1 (proj1 Ha))
                      (NOWN _ _ _ _ _ HMR2 (proj1 Ha))) as [E W].
           - unfold scratch_k. rewrite SP3. unfold LV2_REFUSALS_FORGET_K. intros [H|H]; lia.
           - unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia.
           - split; [exact E | apply W]. }
      assert (E4_2 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp - 48))
        by exact (eq_trans (HPRES2 2 ltac:(unfold callee_saved; lia)) E3_2).
      rewrite SEGS, E3_1.
      eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E4_2. eapply psw_ret_z; [exact FR3 | lia]. }
      intros ms5 (can5 & Q5 & EQ5). subst can5.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
      assert (K5 : psw_kept_rel R4 R5) by psw_kept X5.
      assert (RP5 : regs_preserved regs R5).
      { intros rr Hrr.
        destruct (Z.eq_dec rr 2) as [->|N2]; [psw_saved X5|].
        destruct (Z.eq_dec rr 8) as [->|N8]; [psw_saved X5|].
        destruct (Z.eq_dec rr 9) as [->|N9]; [psw_saved X5|].
        destruct (Z.eq_dec rr 18) as [->|N18]; [psw_saved X5|].
        destruct (Z.eq_dec rr 19) as [->|N19]; [psw_saved X5|].
        rewrite (K5 rr Hrr N2 N8 N9 N18 N19), (HPRES2 rr Hrr), (K3 rr Hrr N2 N8 N9 N18 N19), (HPRES1 rr Hrr).
        exact (K1 rr Hrr N2 N8 N9 N18 N19). }
      destruct (psw_final L A regs mem md O line nl tok cb ncb ntok T ptrs tks L2 A2 R5 m4 md2 PRE0 RJ3 RP5 INL NOL HLT
        LTN INC NOC HTK NTK SPT T63 OUTS) as (POST & HLT3 & HTK3 & KB3 & LEN3 & BK3 & SSP3).
      rewrite RA0. apply SR_ret.
      exists fx1, L2, A2, R5, m4, md2, O2, 7%nat.
      split; [reflexivity|].
      split; [exact FPK|].
      split; [exact POST|].
      split; [rewrite <- SEGS; exact RA4|].
      split.
      { unfold VerbsRun.pin_set_run. rewrite PSM. cbv beta iota zeta. rewrite PSM'. cbv beta iota zeta.
        unfold VerbsRun.pins_follow. cbn [fst Z.eqb].
        split; [rewrite <- SEGS; exact GR4 | rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; reflexivity]. }
      split; [exact HLT3|]. split; [exact HTK3|]. split; [exact KB3|].
      split.
      { intros pn Hpn. destruct (ACC2 pn Hpn) as [[H1 H2]|H]; [|right; exact H].
        destruct (ACC1 pn H1) as [H3|H3]; [left; exact H3 | contradiction]. }
      split.
      { intros [a n] Hb Hn Ho. destruct (OWN2 _ Ho) as [H|H].
        - destruct (OWN1 _ H) as [H'|H']; contradiction.
        - exact (H (psw_keep_blocks _ _ _ O L A mem md L1 A1 m2 md1 RJ2 a n Hb Hn)). }
      split; [exact LEN3|]. split; [exact BK3|]. split; [exact SSP3|].
      split; [lia|].
      rewrite mallocs_app in RES2.
      apply (res_n A2 b (pins_set_sizes (Some u) (Some f) (Some l) vv 0 ++ [lv2_refusals_forget_size None]) 7);
        [| | lia | exact RES2].
      * apply Forall_app. split; [exact (SZ 0 (or_introl eq_refl))|].
        constructor; [apply Z.leb_le; vm_compute; reflexivity | constructor].
      * rewrite length_app. unfold pins_set_sizes, pins_set_args. cbn [length map app]. lia.
    + rewrite SEGS, E1_1.
      eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite E2_2, E2_10.
        eapply psw_ret_nz; [exact FR2 | lia | lia | exact RNZ]. }
      intros ms3 (can3 & Q3 & EQ3). subst can3.
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
      assert (K3 : psw_kept_rel R2 R3) by psw_kept X3.
      assert (RP3 : regs_preserved regs R3).
      { intros rr Hrr.
        destruct (Z.eq_dec rr 2) as [->|N2]; [psw_saved X3|].
        destruct (Z.eq_dec rr 8) as [->|N8]; [psw_saved X3|].
        destruct (Z.eq_dec rr 9) as [->|N9]; [psw_saved X3|].
        destruct (Z.eq_dec rr 18) as [->|N18]; [psw_saved X3|].
        destruct (Z.eq_dec rr 19) as [->|N19]; [psw_saved X3|].
        rewrite (K3 rr Hrr N2 N8 N9 N18 N19), (HPRES1 rr Hrr). exact (K1 rr Hrr N2 N8 N9 N18 N19). }
      destruct (psw_final L A regs mem md O line nl tok cb ncb ntok T ptrs tks L1 A1 R3 m2 md1 PRE0 RJ2 RP3 INL NOL HLT
        LTN INC NOC HTK NTK SPT T63 OUTS) as (POST & HLT2 & HTK2 & KB2 & LEN2 & BK2 & SSP2).
      rewrite RA0. apply SR_ret.
      exists fx1, L1, A1, R3, m2, md1, O1, 6%nat.
      split; [reflexivity|].
      split; [exact FPK|].
      split; [exact POST|].
      split; [rewrite <- SEGS; exact RA2|].
      split.
      { unfold VerbsRun.pin_set_run. rewrite PSM. cbv beta iota zeta. rewrite PSM'. cbv beta iota zeta.
        unfold VerbsRun.pins_follow. rewrite (proj2 (Z.eqb_neq r 0) RNZ). cbn [fst].
        split; [rewrite <- SEGS; exact GR2 | rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity]. }
      split; [exact HLT2|]. split; [exact HTK2|]. split; [exact KB2|].
      split; [exact ACC1|].
      split; [intros pn Hb Hn Ho; destruct (OWN1 pn Ho) as [H|H]; contradiction|].
      split; [exact LEN2|]. split; [exact BK2|]. split; [exact SSP2|].
      split; [lia|].
      apply (res_n A1 b _ 6 (SZ r RR)); [| lia | exact RES1].
      unfold pins_set_sizes, pins_set_args. cbn [length map app]. lia.
Qed.

End P.
