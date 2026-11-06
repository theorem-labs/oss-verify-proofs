(* proves the UBSan contract of check_parse_fields (U/Prog/check_parse_fields_c.v) by a walk of fuzz_frame.ubsan. *)
(* Walk of check_parse_fields (fuzz/fuzz_frame.c:65-112 at 835f336c) in fuzz_frame.ubsan,
   0x1305c..0x131e4, the twin of the walk of Prog/check_parse_fields.v (fuzz_frame.plain).
   Each of the 22 tests that branch to abort at 0x131dc compares a value of the struct
   diginet_frame at f with the same value of the struct spec_frame at w, or with the answer of
   a callee, and the libdiginet model (DgnSpec, DgnLib) reads both from the frame bytes b:
   - the header fields, the EtherType, body, body_len, pad_len and body_sum: the same cell
     contents at f (parse_cells) and at w (spec_cells);
   - the two bcmp calls on the MACs answer 0 (cpf_memcmp_eq);
   - bcmp of w->src with SPEC_OUI (00 a0 7e at 0x1038f) answers 0 exactly when
     oui_of (fr_src b), the answer of diginet_mac_is_digidesign (oui_of_firstn);
   - sum_matches against (w->sum ^ body_sum) == 0 (cpf_summ);
   - diginet_frame_is_keepalive against the harness's test, on each of its three paths
     (body_len <> 1; cmd <> 0; body[0], the byte buf + 30 of b, tested).
   None of the three UBSan branches to the trap at 0x131e0 is taken:
   - 0x13080, (f | w) & 7: f mod 8 = 0 and w mod 8 = 0 (cpf_land7, cpf_land7_wrap);
   - 0x13148, buf >= 2^64 - 30: buf + length b < 2^64 and length b >= 30;
   - 0x131a8, w->body = buf + 30 is 0: 0 <= buf and buf + 30 < 2^64.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import CheckStackU diginet_frame_parse_c
  check_parse_fields_c bcmp_c diginet_mac_is_digidesign_c diginet_frame_is_keepalive_c.
Import ListNotations.
Open Scope Z_scope.

(** * Lists and bytes *)

(* memcmp_model answers 0 exactly when the first n bytes agree. *)
Lemma cpf_memcmp_eq : forall n l r, (n <= length l)%nat -> (n <= length r)%nat ->
  memcmp_model l r n = Some 0 <-> firstn n l = firstn n r.
Proof.
  induction n as [|n IH]; intros [|a l] [|c r] Hl Hr; cbn in *; try lia;
    try (split; intros; reflexivity).
  destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|E]; cbv iota beta.
  - rewrite IH by lia. split.
    + intros H. rewrite H. f_equal. apply bv_eq. exact E.
    + intros H. injection H as _ H. exact H.
  - split.
    + intros H. injection H as H. lia.
    + intros H. injection H as H _. subst c. contradiction.
Qed.

Lemma cpf_memcmp_range : forall n l r v, memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros [|a l] [|c r] v H; cbn in H; try discriminate;
    try (injection H as <-; lia).
  destruct (bv_unsigned a =? bv_unsigned c).
  - exact (IH l r v H).
  - injection H as <-. pose proof (bz_range a). pose proof (bz_range c). unfold bz in *. lia.
Qed.

Lemma cpf_bytes_skipn : forall m a l k, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k l).
Proof.
  intros m a l k H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by exact Hk. exact H.
Qed.

Lemma cpf_bytes_sub : forall m a l k n, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk. apply (cpf_bytes_skipn m a l k H) in Hk.
  rewrite <- (firstn_skipn n (skipn k l)) in Hk. apply bytes_at_app in Hk. exact (proj1 Hk).
Qed.

(* The bytes of one cell of a ro_cells block. *)
Lemma cpf_cell_bytes : forall m A cs k c, ro_cells rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [Hwf Hb] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hwpre. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma cpf_nth_skipn : forall {X} (l : list X) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] x N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma cpf_rd1 : forall m a l (i : nat) x, bytes_at rsegs m a l -> nth_error l i = Some x ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [x].
Proof.
  intros m a l i x BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m a l i 1 BL ltac:(lia)). rewrite (cpf_nth_skipn l i x N). reflexivity.
Qed.

(* The body bytes that diginet_frame_is_keepalive reads, at buf + 30. *)
Lemma cpf_body_at : forall m buf b, fr_code b = 0 -> bytes_at rsegs m buf b ->
  bytes_at rsegs m (buf + 30) (fr_body b).
Proof.
  intros m buf b C BB. destruct (fr_code_ok b C) as (L30 & _). unfold fr_body.
  pose proof (cpf_bytes_sub m buf b 30 (Z.to_nat (fr_body_len b)) BB L30) as S.
  change (Z.of_nat 30) with 30 in S. exact S.
Qed.

(* The low three bits of an 8-aligned value, and of its 64-bit wrap: the UBSan alignment
   check at 0x13080. *)
Lemma cpf_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma cpf_land7_wrap : forall x, Z.land x 7 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x H. rewrite unsigned_lit_wrap. transitivity (Z.land x 7); [|exact H].
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 64) as [L|L].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 7 i) by (cbn; lia). rewrite !andb_false_r. reflexivity.
Qed.

Lemma cpf_lor_al : forall f w, f mod 8 = 0 -> w mod 8 = 0 -> Z.land (Z.lor f w) 7 = 0.
Proof.
  intros f w Hf Hw. rewrite Z.land_lor_distr_l, (cpf_land7 f Hf), (cpf_land7 w Hw). reflexivity.
Qed.

Lemma cpf_at8_body : forall b x, fr_code b = 0 -> fr_body_len b = 1 -> nth_error b 30 = Some x ->
  at8 (fr_body b) 0 = bz x.
Proof.
  intros b x C L N. unfold fr_body, at8. rewrite L, (cpf_nth_skipn b 30 x N). reflexivity.
Qed.

(** * Register values *)

Lemma cpf_seqz_nz : forall v, -256 < v < 256 -> v <> 0 -> v_sltiu (Z_to_bv 64 v) 1 = Z_to_bv 64 0.
Proof.
  intros v Hv Hn. unfold v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  replace (v mod 2^64 <? 1) with false; [reflexivity|]. symmetry. apply Z.ltb_ge.
  change (2^64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Lemma cpf_seqz_byte : forall x : byte, v_sltiu (zxb x) 1 = Z_to_bv 64 (if bz x =? 0 then 1 else 0).
Proof.
  intros x. pose proof (bz_range x) as R. unfold v_sltiu, zxb. fold (bz x).
  rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec (bz x) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (bz x <? 1) with false; [reflexivity|]. symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma cpf_lxor16 : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 -> (Z.lxor x y <? 1) = (x =? y).
Proof.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [E|E].
  - subst y. rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. assert (Z.lxor x y <> 0) by (intros H; exact (E (proj1 (Z.lxor_eq_0_iff x y) H))).
    pose proof (proj2 (Z.lxor_nonneg x y) ltac:(split; lia)). lia.
Qed.

Lemma cpf_log2_16 : forall x, 0 <= x < 2^16 -> Z.log2 x < 16.
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|N]; [cbn; lia|].
  apply (proj1 (Z.log2_lt_pow2 x 16 ltac:(lia))). lia.
Qed.

Lemma cpf_lxor_lt : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 -> 0 <= Z.lxor x y < 2^16.
Proof.
  intros x y Hx Hy. pose proof (proj2 (Z.lxor_nonneg x y) ltac:(split; lia)) as P.
  split; [exact P|].
  destruct (Z.eq_dec (Z.lxor x y) 0) as [E|E]; [rewrite E; lia|].
  apply (proj2 (Z.log2_lt_pow2 (Z.lxor x y) 16 ltac:(lia))).
  pose proof (Z.log2_lxor x y ltac:(lia) ltac:(lia)) as L.
  pose proof (cpf_log2_16 x Hx). pose proof (cpf_log2_16 y Hy). lia.
Qed.

(* 0x1317c..0x13188: (w->sum ^ f->body_sum) == 0, against f->sum_matches. *)
Lemma cpf_summ : forall x y, 0 <= x < 2^16 -> 0 <= y < 2^16 ->
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (zx16 (Z_to_bv 64 x))) (bv_unsigned (zx16 (Z_to_bv 64 y))))) 1 =
  zxb (b8 (if x =? y then 1 else 0)).
Proof.
  intros x y Hx Hy. unfold zx16.
  rewrite (unsigned_lit x), (unsigned_lit y) by lia.
  rewrite (Z.mod_small x), (Z.mod_small y) by lia.
  rewrite (unsigned_lit x), (unsigned_lit y) by lia.
  pose proof (cpf_lxor_lt x y Hx Hy) as L.
  unfold v_sltiu. rewrite (unsigned_lit (Z.lxor x y)) by lia. change (bv_wrap 64 1) with 1.
  rewrite (cpf_lxor16 x y Hx Hy). destruct (x =? y); reflexivity.
Qed.

(** * The walk *)

Ltac cpf_uns := rewrite ?unsigned_lit by lia.
Ltac cpf_br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; cpf_uns; solve_cond_rec]
  end.
(* Decide a branch whose condition is a closed term. *)
Ltac cpf_brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.
Ltac cpf_curmem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => k mm end.

Theorem check_parse_fields_holds :
  bcmp_contract -> diginet_mac_is_digidesign_contract -> diginet_frame_is_keepalive_contract ->
  check_parse_fields_contract.
Proof.
  intros BCMP MAC KA. unfold check_parse_fields_contract, CHECK_PARSE_FIELDS, U_CPF_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf f w lo b fj
    C0 BLT FNZ FAL WAL BB PF SW ST LO DB DF DW MI.
  unfold parse_cells in PF. unfold spec_cells in SW.
  destruct (fr_code_ok b C0) as (L30 & ET & NB1 & NB2).
  destruct (fr_body_len_ok b C0) as (BL0 & PL0 & BLP).
  pose proof (u64_range sp) as Rsp.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBb.
  pose proof (ro_cells_bound _ _ _ _ PF) as PFb. cbn [cells_size csize Nat.add] in PFb.
  pose proof (ro_cells_bound _ _ _ _ SW) as SWb. cbn [cells_size csize Nat.add] in SWb.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  (* prologue; 0x13078 or, 0x1307c andi, 0x13080 bnez -> trap: (f | w) & 7 is 0 *)
  do 10 step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry]
  end.
  2: { unfold_cond; try change (bv_wrap 64 7) with 7;
       rewrite ?(unsigned_lit f), ?(unsigned_lit w) by lia;
       rewrite (cpf_land7_wrap _ (cpf_lor_al f w FAL WAL)); vm_compute; reflexivity. }
  (* the header fields numbytes, sum, send, ack, retry, cmd, ncmds *)
  do 5 step. cpf_br false.
  do 3 step. cpf_br false.
  do 3 step. cpf_br false.
  do 3 step. cpf_br false.
  do 3 step. cpf_br false.
  do 3 step. cpf_br false.
  do 3 step. cpf_br false.
  (* bcmp (f, w->dst = buf, 6) *)
  do 4 step.
  pose proof (cpf_cell_bytes _ _ _ 0 _ PF eq_refl) as D0. cbn [cbytes] in D0. rewrite Z.add_0_r in D0.
  cpf_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply BCMP with (ls := fr_dst b) (rs := b) (v := 0) | post_call rsegs mm ]).
  1: { cpf_uns. exact D0. }
  1: { cpf_uns. exact BB. }
  1: { cpf_uns. change (Z.to_nat 6) with 6%nat. apply cpf_memcmp_eq.
       - unfold fr_dst. rewrite length_firstn, Nat.min_l by lia. lia.
       - lia.
       - unfold fr_dst. rewrite firstn_firstn. reflexivity. }
  1: { eassumption. }
  step. cpf_br false.
  (* bcmp (f + 6, w->src = buf + 6, 6) *)
  do 5 step.
  pose proof (cpf_cell_bytes _ _ _ 6 _ PF eq_refl) as D6. cbn [cbytes] in D6. change (Z.of_nat 6) with 6 in D6.
  pose proof (cpf_bytes_skipn _ _ _ 6 BB ltac:(lia)) as B6. change (Z.of_nat 6) with 6 in B6.
  cpf_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply BCMP with (ls := fr_src b) (rs := skipn 6 b) (v := 0) | post_call rsegs mm ]).
  1: { cpf_uns. exact D6. }
  1: { cpf_uns. exact B6. }
  1: { cpf_uns. change (Z.to_nat 6) with 6%nat. apply cpf_memcmp_eq.
       - unfold fr_src. rewrite length_firstn, length_skipn, Nat.min_l by lia. lia.
       - rewrite length_skipn. lia.
       - unfold fr_src. rewrite firstn_firstn. reflexivity. }
  1: { eassumption. }
  step. cpf_br false.
  (* EtherType *)
  do 3 step. cpf_br false.
  (* diginet_mac_is_digidesign (f + 6) *)
  do 2 step.
  eapply evt_cut.
  { eapply MAC with (mac := f + 6) (l := fr_src b).
    - lia.
    - unfold fr_src. rewrite length_firstn, length_skipn, Nat.min_l by lia. reflexivity.
    - exact D6. }
  intros ms' (a1' & a2' & ->).
  replace (ret_pc (Z_to_bv 64 0x13120)) with (Z_to_bv 64 0x13120) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* bcmp (w->src, SPEC_OUI, 3); SPEC_OUI is 00 a0 7e at 0x1038f in .rodata *)
  do 7 step.
  assert (LS6 : (3 <= length (skipn 6 b))%nat) by (rewrite length_skipn; lia).
  assert (LO3 : (3 <= length [b8 0; b8 0xa0; b8 0x7e])%nat) by (cbn; lia).
  assert (LSRC : (3 <= length (fr_src b))%nat)
    by (unfold fr_src; rewrite length_firstn, length_skipn, Nat.min_l by lia; lia).
  cpf_curmem ltac:(fun mm => assert (BO : bytes_at rsegs mm 66447 [b8 0; b8 0xa0; b8 0x7e])
    by (apply ro_bytes_at; [eassumption | lia | cbn; lia | apply (ro_bytes_b_sound rsegs); vm_compute; reflexivity])).
  destruct (memcmp_model_total (skipn 6 b) [b8 0; b8 0xa0; b8 0x7e] 3 LS6 LO3) as [v HV].
  pose proof (cpf_memcmp_range _ _ _ _ HV) as VR.
  cpf_curmem ltac:(fun mm => eapply evt_cut;
    [ eapply BCMP with (ls := skipn 6 b) (rs := [b8 0; b8 0xa0; b8 0x7e]) (v := v) | post_call rsegs mm ]).
  1: { cpf_uns. exact B6. }
  1: { cpf_uns. exact BO. }
  1: { cpf_uns. exact HV. }
  1: { eassumption. }
  (* seqz, against the answer of diginet_mac_is_digidesign *)
  step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry]
  end.
  2: { destruct (oui_of (fr_src b)) eqn:OU.
       - assert (V0 : v = 0).
         { apply (proj1 (oui_of_firstn (fr_src b) LSRC)) in OU.
           assert (E3 : firstn 3 (skipn 6 b) = firstn 3 [b8 0; b8 0xa0; b8 0x7e]).
           { rewrite <- OU. unfold fr_src. rewrite !firstn_firstn. reflexivity. }
           pose proof (proj2 (cpf_memcmp_eq 3 _ _ LS6 LO3) E3) as E4. rewrite HV in E4.
           injection E4 as E4. exact E4. }
         subst v. vm_compute. reflexivity.
       - assert (VNZ : v <> 0).
         { intros ->. pose proof (proj1 (cpf_memcmp_eq 3 _ _ LS6 LO3) HV) as E3.
           assert (OT : oui_of (fr_src b) = true).
           { apply (proj2 (oui_of_firstn (fr_src b) LSRC)). unfold fr_src. rewrite firstn_firstn. exact E3. }
           congruence. }
         rewrite (cpf_seqz_nz v VR VNZ). vm_compute. reflexivity. }
  (* 0x13144 addi, 0x13148 bgeu buf, 2^64 - 30 -> trap: buf + 30 <= buf + length b < 2^64 *)
  do 2 step. cpf_br false.
  (* body == buf + 30, body_len, pad_len, body_sum *)
  do 3 step. cpf_br false.
  do 3 step. cpf_br false.
  do 3 step. cpf_br false.
  do 3 step. cpf_br false.
  (* sum_matches == (w->sum == w->body_sum) *)
  pose proof (be16_range b 16) as RS. change (be16 b 16) with (fr_sum b) in RS.
  pose proof (sum16_range (fr_body b)) as RB. change (sum16 (fr_body b)) with (fr_body_sum b) in RB.
  do 5 step.
  rewrite (cpf_summ (fr_sum b) (fr_body_sum b) RS RB).
  cpf_br false.
  (* the harness's keepalive test: body_len == 1, then cmd == 0, then body[0] == 0 *)
  assert (ZC : zxb (b8 (fr_cmd b)) = Z_to_bv 64 (fr_cmd b))
    by (unfold zxb; f_equal; apply bz_b8; unfold fr_cmd; apply at8_range).
  pose proof (at8_range b 28) as RC. change (at8 b 28) with (fr_cmd b) in RC.
  do 3 step.
  destruct (Z.eq_dec (fr_body_len b) 1) as [BL1|BL1]; [cpf_br false | cpf_br true].
  (* goals: body_len = 1; body_len <> 1 *)
  1: (step; step; rewrite ZC;
      destruct (Z.eq_dec (fr_cmd b) 0) as [CM0|CM0]; [cpf_br false | cpf_br true]).
  (* goals: body_len = 1 and cmd = 0; body_len = 1 and cmd <> 0; body_len <> 1 *)
  1: (assert (LB : (30 < length b)%nat) by lia;
      destruct (nth_error b 30) as [xb|] eqn:NX; [| apply nth_error_None in NX; lia];
      step;
      (* 0x131a8 beqz w->body -> trap: w->body = buf + 30 is not 0 *)
      step; cpf_br false;
      cpf_curmem ltac:(fun mm => pose proof (cpf_rd1 mm buf b 30 xb BB NX) as HR);
      step; clear HR; step; rewrite cpf_seqz_byte).
  (* diginet_frame_is_keepalive (f) *)
  all: do 2 step.
  all: eapply evt_cut;
    [ eapply KA with (f := f) (cmd := fr_cmd b) (body := buf + 30) (bb := fr_body b)
    | intros ms' (ka1 & ka2 & ->) ].
  all: first [ exact FNZ | exact FAL | exact RC | lazymatch goal with |- 0 < _ < _ => lia end
             | exact (cpf_cell_bytes _ _ _ 30 _ PF eq_refl)
             | exact (cpf_body_at _ buf b C0 BB)
             | (rewrite (length_fr_body b C0), Z2Nat.id by lia;
                apply (proj2 (bytes_at_app _ _ _ _ _)); split;
                [ exact (cpf_cell_bytes _ _ _ 32 _ PF eq_refl)
                | rewrite length_le8; replace (f + 32 + Z.of_nat 8) with (f + Z.of_nat 40) by lia;
                  exact (cpf_cell_bytes _ _ _ 40 _ PF eq_refl) ])
             | lazymatch goal with |- evt _ _ _ => idtac end ].
  all: replace (ret_pc (Z_to_bv 64 0x131bc)) with (Z_to_bv 64 0x131bc)
         by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  all: step.
  (* the answer of diginet_frame_is_keepalive against the harness's test *)
  1: (assert (KE : keepalive_of (fr_cmd b) (Z.of_nat (length (fr_body b))) (fr_body b) = (bz xb =? 0))
        by (rewrite (length_fr_body b C0), BL1; unfold keepalive_of;
            rewrite CM0, (cpf_at8_body b xb C0 BL1 NX); reflexivity);
      rewrite KE; cpf_br false).
  2: (assert (KE : keepalive_of (fr_cmd b) (Z.of_nat (length (fr_body b))) (fr_body b) = false)
        by (unfold keepalive_of; rewrite (proj2 (Z.eqb_neq _ _) CM0); reflexivity);
      rewrite KE; cpf_brc).
  3: (assert (KE : keepalive_of (fr_cmd b) (Z.of_nat (length (fr_body b))) (fr_body b) = false)
        by (unfold keepalive_of; rewrite (length_fr_body b C0), Z2Nat.id by lia;
            rewrite (proj2 (Z.eqb_neq _ _) BL1), andb_false_r; reflexivity);
      rewrite KE; cpf_brc).
  (* epilogue *)
  all: do 7 step.
  all: release_frame FR ST (bv_unsigned sp).
  all: apply evt_done; do 16 eexists; split; [reflexivity|].
  all: refine (conj _ (conj _ (conj _ _))); eassumption.
Qed.
