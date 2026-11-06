(* Segment crt_m2 of check_round_trip in fuzz_frame.plain, 0x13190 .. 0x13310: the three tests
   of the answer of diginet_frame_build (each branch to the abort at 0x13514 is not taken),
   s9 = sys | !fits, the first inlined spec_build_frame into want (memset, two memcpy of the MACs,
   the header bytes with the 64-bit sum of the body, memcpy of the body), and bcmp of out and want
   when the answer is the frame length. crt_m2_ok proves crt_m2_stmt (crt_defs.v).
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import check_parse_fields_c memset_c memcpy_c
  bcmp_c diginet_frame_build_c crt_defs crt_m2_bytes.
Import ListNotations.
Open Scope Z_scope.

(** * Lists and bytes *)

Lemma m2_firstn1_skipn : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn 1 (skipn i l) = [x].
Proof.
  intros X l; induction l as [|c l IH]; intros [|i] x N; cbn in *; try discriminate.
  - injection N as ->. reflexivity.
  - apply IH; exact N.
Qed.

Lemma m2_rd1 : forall m a l (i : nat) x, bytes_at rsegs m a l -> nth_error l i = Some x ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [x].
Proof.
  intros m a l i x BL N. pose proof (nth_error_Some l i) as NS. rewrite N in NS.
  assert (Hi : (i < length l)%nat) by (apply NS; discriminate).
  rewrite (bytes_at_ov_read rsegs m a l i 1 BL ltac:(lia)). f_equal. apply m2_firstn1_skipn. exact N.
Qed.

Lemma m2_sum_step : forall bb i x, nth_error bb i = Some x ->
  sum_bytes (firstn (S i) bb) = sum_bytes (firstn i bb) + bv_unsigned (zxb x).
Proof.
  intros bb i x N. assert (Hi : (i < length bb)%nat) by (apply nth_error_Some; congruence).
  rewrite sum_bytes_firstn_S by exact Hi. unfold at8. erewrite nth_error_nth by exact N.
  pose proof (bz_range x) as R. unfold zxb. unfold bz in *. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma m2_skipn_repeat : forall {X} (x : X) k n, skipn k (repeat x n) = repeat x (n - k).
Proof. intros X x k; induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.

Lemma m2_firstn_repeat : forall {X} (x : X) k n, firstn k (repeat x n) = repeat x (Nat.min k n).
Proof. intros X x k; induction k as [|k IH]; intros [|n]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

(* A block of N zero bytes as a block of a and a block of b zero bytes, N = a + b. *)
Lemma m2_cb_split_z : forall m A (N a b : nat), rw_cells rsegs m A [CB N (repeat (b8 0) N)] -> N = (a + b)%nat ->
  rw_cells rsegs m A [CB a (repeat (b8 0) a)] /\ rw_cells rsegs m (A + Z.of_nat a) [CB b (repeat (b8 0) b)].
Proof.
  intros m A N a b H ->. apply m2_cb_split in H. destruct H as [H1 H2].
  rewrite m2_firstn_repeat, Nat.min_l in H1 by lia. rewrite m2_skipn_repeat in H2.
  replace (a + b - a)%nat with b in H2 by lia. split; assumption.
Qed.

Lemma m2_swrap : forall z, 0 <= z < 2^31 -> bv_swrap 32 (z + 0) = z.
Proof. intros z Hz. rewrite Z.add_0_r. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma m2_le1_zxb : forall x : byte, le1 (zxb x) = [x].
Proof. intros x. rewrite m2_le1. f_equal. unfold zxb. rewrite m2_b8_w64. apply b8_bz. Qed.

(* A store at offset 0 of a register that holds a variable word leaves the address as the word
   itself; the equation of its write needs the direction without symmetry too. *)
Local Ltac addr_eq_tac ::=
  first [ symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
        | first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

(* A step; a byte store that the step leaves in the memory term is put in the cells. *)
Ltac m2_s := step; try (lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?v))) _) => rewrite (m2_le1_zxb v); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) => rewrite (m2_le1 v); mem_after_store
  end).

(** * The sum loop, 0x13260 .. 0x1327c *)

Section Sum.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (p : Z) (bb : list byte).
Hypothesis BB : bytes_at rsegs m p bb.
Hypothesis HP : p + Z.of_nat (length bb) < 2^64.
Hypothesis S6 : s6 = Z_to_bv 64 (Z.of_nat (length bb)).

Local Notation ST pc a0 a1 a2 a3 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 p) s8 s9 s10 s11
           t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma m2_sum_loop : forall k (i : nat) (a3 : word) (v0 v1 v2 : Z),
  (i + S k = length bb)%nat -> v0 = sum_bytes (firstn i bb) -> v1 = p + Z.of_nat (length bb) ->
  v2 = p + Z.of_nat i ->
  (forall a1' a2' a3', evt rsegs Q (ST 0x1327c (Z_to_bv 64 (sum_bytes bb)) a1' a2' a3')) ->
  evt rsegs Q (ST 0x1326c (Z_to_bv 64 v0) (Z_to_bv 64 v1) (Z_to_bv 64 v2) a3).
Proof.
  pose proof (bytes_at_bound _ _ _ _ BB) as HB.
  induction k as [|k IH]; intros i a3 v0 v1 v2 Hk -> -> -> K.
  all: destruct (nth_error bb i) as [x|] eqn:Nx; [| apply nth_error_None in Nx; lia].
  all: pose proof (m2_rd1 m p bb i x BB Nx) as R.
  all: step; step; step; step.
  - br false. rewrite <- (m2_sum_step bb i x Nx), (firstn_all2 (n := S i)) by lia. apply K.
  - br true. eapply (IH (S i)); [lia | symmetry; apply m2_sum_step; exact Nx | reflexivity | lia | exact K].
Qed.

Lemma m2_sum : forall (a1 a2 a3 : word) (v0 : Z), v0 = 0 ->
  (forall a1' a2' a3', evt rsegs Q (ST 0x1327c (Z_to_bv 64 (sum_bytes bb)) a1' a2' a3')) ->
  evt rsegs Q (ST 0x13260 (Z_to_bv 64 v0) a1 a2 a3).
Proof.
  intros a1 a2 a3 v0 -> K. pose proof (bytes_at_bound _ _ _ _ BB) as HB. rewrite S6.
  destruct (Nat.eq_dec (length bb) 0) as [L0|L0].
  - step. br true. rewrite <- S6.
    assert (E : sum_bytes bb = 0) by (destruct bb; [reflexivity | cbn in L0; lia]).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (sum_bytes bb)) by (rewrite E; reflexivity). apply K.
  - step. br false. step. step. rewrite <- S6.
    eapply (m2_sum_loop (length bb - 1) 0); [lia | reflexivity | first [reflexivity | lia] | first [reflexivity | lia] | exact K].
Qed.

End Sum.

(** * Register values and codes *)

Lemma m2_sltiu_t : forall z k, 0 <= z < k -> k < 2^64 -> v_sltiu (Z_to_bv 64 z) k = Z_to_bv 64 1.
Proof.
  intros z k Hz Hk. unfold v_sltiu. rewrite unsigned_lit by lia. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  replace (z <? k) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma m2_sltiu_f : forall z k, 0 <= k <= z -> z < 2^64 -> v_sltiu (Z_to_bv 64 z) k = Z_to_bv 64 0.
Proof.
  intros z k Hz Hk. unfold v_sltiu. rewrite unsigned_lit by lia. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia.
  replace (z <? k) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma m2_code_true : forall b, crt_ok b = true ->
  build_code (fr_body b) (frame_len (length (fr_body b))) = frame_len (length (fr_body b)).
Proof.
  intros b H. unfold crt_ok in H. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply negb_true_iff in H2. unfold build_code. rewrite H2.
  replace (1484 <? Z.of_nat (length (fr_body b))) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Z.ltb_irrefl. reflexivity.
Qed.

Lemma m2_code_false : forall b c, crt_ok b = false -> build_code (fr_body b) c = -4 \/ build_code (fr_body b) c = -10.
Proof.
  intros b c H. unfold crt_ok in H. unfold build_code.
  destruct (1484 <? Z.of_nat (length (fr_body b))) eqn:E1; [left; reflexivity|]. apply Z.ltb_ge in E1.
  destruct (system_at (fr_body b)) eqn:E2; [right; reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) E1) in H. discriminate.
Qed.

(** * Tactics of the walk *)

(* Decide a branch whose condition is a closed term. *)
Ltac brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

(* After a callee contract: its footprint with literal bounds, the transport of the facts, the
   return address. *)
Ltac m2_after mm MUc WMc MIc :=
  rewrite ?unsigned_lit in MUc by lia;
  lazymatch type of MUc with munch _ _ ?m' =>
    transport_after_call rsegs mm m' MUc WMc; clear MUc WMc;
    try match goal with H : mem_inv rsegs mm |- _ => clear H end;
    try clear mm end;
  rename MIc into m2MI;
  rewrite ?ret_pc_even by first [lia | reflexivity].

Ltac m2_modeq :=
  rewrite ?m2_w64_mod by lia;
  first [ apply m2_sx32_mod | apply m2_zx16_mod | f_equal; lia
        | rewrite spec_sum_eq; unfold sum16; rewrite Z.mod_mod by lia; reflexivity ].

(* One stored byte against its byte of build_frame. *)
Ltac m2_byte :=
  rewrite ?m2_b8_w64;
  first [ reflexivity
        | f_equal; lia
        | apply m2_b8_shr with (w := 16); [lia | lia | m2_modeq]
        | apply m2_b8_shr with (w := 32); [lia | lia | m2_modeq]
        | apply m2_b8_low with (w := 16); [lia | m2_modeq]
        | apply m2_b8_low with (w := 32); [lia | m2_modeq] ].

Ltac m2_lists := repeat match goal with
  | |- ?a ++ _ = ?a ++ _ => f_equal
  | |- _ :: _ = _ :: _ => f_equal
  end.

(** * 0x132f0 .. 0x13310: n to s10, out back to s6, bcmp (out, want, n) when the answer is n *)

Lemma m2_end : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s10 s11 t3 t4 t5 t6 x8 x16 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte)
         (w out want n : Z) (b j2 : list byte) (sv hdr : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) ->
    0 < out -> out + n <= bv_unsigned sp - 240 -> 0 < want -> want + n <= bv_unsigned sp - 240 ->
    cells_size sv = 104%nat ->
    rw_cells rsegs m (bv_unsigned sp) (C8 x8 :: C8 x16 :: C8 (Z_to_bv 64 out) :: CB 4 j2 :: CB 12 (crt_hb b) :: sv) ->
    rw_cells rsegs m out [CB (Z.to_nat n) (build_out (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                            (fr_cmd b) (fr_ncmds b) (fr_body b) 0 (repeat (b8 0xa5) (Z.to_nat n)))] ->
    rw_cells rsegs m want [CB 6 (fr_dst b)] ->
    rw_cells rsegs m (want + 6) [CB 6 (fr_src b)] ->
    rw_cells rsegs m (want + 12) hdr -> cells_size hdr = 18%nat ->
    cells_bytes hdr = m2_hdr (Z.of_nat (length (fr_body b))) (spec_sum (fr_body b)) (fr_send b) (fr_ack b)
                        (fr_retry b) (fr_cmd b) (fr_ncmds b) ->
    rw_cells rsegs m (want + 30) [CB (length (fr_body b)) (fr_body b)] ->
    rw_cells rsegs m (want + 30 + Z.of_nat (length (fr_body b)))
      [CB (30 - length (fr_body b)) (repeat (b8 0) (30 - length (fr_body b)))] ->
    munch [(bv_unsigned sp, bv_unsigned sp + 40); (want, want + n)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
    evt rsegs (crt_m2_post sp gp tp F fc w out want n b sv m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) (Z_to_bv 64 n)
               (Z_to_bv 64 (build_code (fr_body b) n)) (Z_to_bv 64 (want + 6)) s6 s7 s8
               (Z_to_bv 64 (if crt_ok b then 0 else 1)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x132f0) fc None m (seg_rom rsegs)).
Proof.
  intros HBC ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s10 s11 t3 t4 t5 t6 x8 x16 F fc m0 m
    w out want n b j2 sv hdr HC HLB Hn Hout0 Hout1 Hwant0 Hwant1 Hsv FR m2OUT W1 W2 W3 HS3 HB3 W4 W5 m2MU m2WM m2MI.
  pose proof (u64_range sp) as Rsp.
  destruct (fr_code_ok b HC) as (L30 & _ & _ & _).
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLP).
  pose proof (length_fr_body b HC) as LFB.
  assert (NL : n = Z.max 60 (30 + Z.of_nat (length (fr_body b)))) by (subst n; unfold frame_len; lia).
  assert (Ld : length (fr_dst b) = 6%nat) by (unfold fr_dst; rewrite length_firstn; lia).
  assert (Ls : length (fr_src b) = 6%nat) by (unfold fr_src; rewrite length_firstn, length_skipn; lia).
  (* want holds build_frame; it is writable stack *)
  pose proof (m2_rw_app_at _ _ (want + 30 + Z.of_nat (length (fr_body b))) _ _ W4
                ltac:(cbn [cells_size csize]; lia) W5) as W45.
  pose proof (m2_rw_app_at _ _ (want + 30) _ _ W3 ltac:(rewrite HS3; lia) W45) as W35.
  pose proof (m2_rw_app_at _ _ (want + 12) _ _ W2 ltac:(cbn [cells_size csize]; lia) W35) as W25.
  pose proof (m2_rw_app_at _ _ (want + 6) _ _ W1 ltac:(cbn [cells_size csize]; lia) W25) as WALL.
  clear W45 W35 W25 W1 W2 W3 W4 W5.
  assert (STW : stk rsegs m want (want + n)).
  { pose proof (stk_of_rw_cells rsegs m want _ WALL) as X.
    rewrite !cells_size_app, HS3 in X. cbn [cells_size csize] in X.
    replace (want + n) with (want + Z.of_nat (6 + 0 + (6 + 0 + (18 + (length (fr_body b) + 0 +
                                (30 - length (fr_body b) + 0)))))) by lia.
    exact X. }
  assert (WB : bytes_at rsegs m want (build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                                        (fr_cmd b) (fr_ncmds b) (fr_body b) false)).
  { pose proof (m2_rw_bytes _ _ _ WALL) as X. rewrite !cells_bytes_app, HB3 in X.
    cbn [cells_bytes cbytes] in X. rewrite !app_nil_r in X.
    rewrite m2_build_frame_split. exact X. }
  clear WALL.
  (* the frame; out *)
  pose proof (rw_cells_merge rsegs m (bv_unsigned sp) [] [C8 x8; C8 x16]
                (C8 (Z_to_bv 64 out) :: CB 4 j2 :: CB 12 (crt_hb b) :: sv) FR) as FR2.
  cbn [app cells_size csize Nat.add] in FR2. clear FR.
  pose proof (stk_of_rw_cells rsegs m out _ m2OUT) as SO. cbn [cells_size csize] in SO.
  replace (out + Z.of_nat (Z.to_nat n + 0)) with (out + n) in SO by lia.
  (* 0x132f0 sext.w s10, s3; 0x132f4 ld s6, 0x10(sp); 0x132f8 bne s4, s10 *)
  step. step. step.
  rewrite (unsigned_lit n) by lia. rewrite (m2_swrap n) by lia.
  assert (OKc : crt_ok b = true \/ crt_ok b = false) by (destruct (crt_ok b); auto).
  destruct OKc as [OK|OK].
  - (* the answer is n: bcmp (out, want, n) *)
    pose proof (m2_code_true b OK) as BCn. rewrite <- Hn in BCn. rewrite BCn.
    br false. do 4 step.
    rewrite m2_build_out_eq in m2OUT by (rewrite repeat_length, Z2Nat.id by lia; exact BCn).
    change (0 =? 1) with false in m2OUT.
    pose proof (m2_rw_bytes _ _ _ m2OUT) as OB. cbn [cells_bytes cbytes] in OB. rewrite app_nil_r in OB.
    pose proof (length_build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                  (fr_cmd b) (fr_ncmds b) (fr_body b) false Ld Ls) as LB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply HBC with (ls := build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                                 (fr_cmd b) (fr_ncmds b) (fr_body b) false)
                        (rs := build_frame (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                                 (fr_cmd b) (fr_ncmds b) (fr_body b) false) (v := 0);
        [ uns; exact OB | uns; exact WB | uns; apply m2_memcmp_self; lia | eassumption ]
      | intros ms5 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mE & -> &
                    MU5 & WM5 & MI5 & _ & _);
        m2_after mm MU5 WM5 MI5 ]
    end.
    (* 0x1330c bnez a0 *)
    step. br false.
    apply evt_done. unfold crt_m2_post. do 24 eexists. split; [reflexivity|].
    split; [exact m2MU|]. split; [exact m2WM|]. split; [exact m2MI|]. split; [exact FR2|].
    split; [exact SO | exact STW].
  - (* the answer is -4 or -10: no bcmp *)
    destruct (m2_code_false b n OK) as [BCx|BCx]; rewrite BCx; br true;
    apply evt_done; unfold crt_m2_post; do 24 eexists;
    (split; [reflexivity|]);
    (split; [exact m2MU|]); (split; [exact m2WM|]); (split; [exact m2MI|]); (split; [exact FR2|]);
    (split; [exact SO | exact STW]).
Qed.

(** * 0x131cc .. 0x13310 *)

Lemma m2_tail : memset_contract -> memcpy_contract -> bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (w buf out want n : Z) (b j : list byte) (sv : list cell),
    fr_code b = 0 -> Z.of_nat (length b) < 2 ^ 26 -> n = frame_len (length (fr_body b)) ->
    crt_lay (bv_unsigned sp) w buf out want n (Z.of_nat (length b)) ->
    ro_cells rsegs m w (spec_cells buf b) ->
    bytes_at rsegs m buf b ->
    rw_cells rsegs m out [CB (Z.to_nat n) (build_out (fr_dst b) (fr_src b) (fr_send b) (fr_ack b) (fr_retry b)
                            (fr_cmd b) (fr_ncmds b) (fr_body b) 0 (repeat (b8 0xa5) (Z.to_nat n)))] ->
    stk rsegs m want (want + n) ->
    cells_size sv = 104%nat ->
    rw_cells rsegs m (bv_unsigned sp) (CB 28 j :: CB 12 (crt_hb b) :: sv) ->
    mem_inv rsegs m ->
    s4 = Z_to_bv 64 (build_code (fr_body b) n) ->
    s9 = Z_to_bv 64 (if crt_ok b then 0 else 1) ->
    evt rsegs (crt_m2_post sp gp tp F fc w out want n b sv m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 want) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 w) (Z_to_bv 64 n) s4
               s5 (Z_to_bv 64 out) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x131cc) fc None m (seg_rom rsegs)).
Proof.
  intros HMS HMC HBC ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m w buf out want n b j sv HC HLB Hn LAY m2SW BB m2OUT STW Hsv m2FR m2MI E4 E9.
  subst s4 s9.
  destruct LAY as (Hbuf0 & Hbuf1 & Hout0 & Hout1 & Hwant0 & Hwant1 & Dow & Dob & Dwb & Hw0 & Hw1).
  destruct (fr_code_ok b HC) as (L30 & ET & NB1 & NB2).
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLP).
  pose proof (length_fr_body b HC) as LFB.
  assert (LZ : Z.of_nat (length (fr_body b)) = fr_body_len b) by lia.
  assert (NL : n = Z.max 60 (30 + fr_body_len b)) by (subst n; unfold frame_len; lia).
  pose proof (u64_range sp) as Rsp.
  assert (Ld : length (fr_dst b) = 6%nat) by (unfold fr_dst; rewrite length_firstn; lia).
  assert (Ls : length (fr_src b) = 6%nat) by (unfold fr_src; rewrite length_firstn, length_skipn; lia).
  assert (m2BD : bytes_at rsegs m buf (fr_dst b)).
  { pose proof (m2_bytes_sub m buf b 0 6 BB ltac:(lia)) as X. change (Z.of_nat 0) with 0 in X.
    rewrite Z.add_0_r in X. exact X. }
  pose proof (m2_bytes_sub m buf b 6 6 BB ltac:(lia)) as m2BS.
  change (Z.of_nat 6) with 6 in m2BS. change (firstn 6 (skipn 6 b)) with (fr_src b) in m2BS.
  pose proof (m2_bytes_sub m buf b 30 (Z.to_nat (fr_body_len b)) BB ltac:(lia)) as m2BY.
  change (Z.of_nat 30) with 30 in m2BY.
  change (firstn (Z.to_nat (fr_body_len b)) (skipn 30 b)) with (fr_body b) in m2BY.
  clear BB.
  unfold spec_cells in m2SW.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 40); (want, want + n)] m) as m2MU.
  pose proof (wmono_refl rsegs m) as m2WM.
  (* 0x131cc .. 0x131e4: out to sp + 0x10, body_len, dst, src; a2 = the frame length *)
  do 7 step.
  evar (G : Prop). assert (KK : G).
  2: {
    destruct (Z.ltb_spec 60 (fr_body_len b + 30)) as [C|C].
    - br true. generalize (Z_to_bv 64 60) as x0.
      replace (Z_to_bv 64 (fr_body_len b + 30)) with (Z_to_bv 64 n) by (f_equal; lia). exact KK.
    - br false. generalize (Z_to_bv 64 60) as x0. intros x0. step.
      replace (Z_to_bv 64 60) with (Z_to_bv 64 n) by (f_equal; lia). revert x0. exact KK. }
  subst G. intros x0.
  (* 0x131ec .. 0x13214: retry, send, ack; cmd to sp + 8, ncmds to sp; body; memset (want, 0, n) *)
  do 11 step.
  destruct (stk_carve rsegs _ want (want + n) (Z.to_nat n) STW ltac:(lia)) as [_ [jw WJ]].
  replace (want + n - Z.of_nat (Z.to_nat n)) with want in WJ by lia.
  clear STW.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HMS; [uns; exact WJ | eassumption]
    | intros ms1 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mA & -> &
                  MU1 & WM1 & MI1 & RW1);
      m2_after mm MU1 WM1 MI1 ]
  end.
  rewrite ?unsigned_lit in RW1 by lia.
  lazymatch type of RW1 with context [repeat ?z _] => replace z with (b8 0) in RW1 by (vm_compute; reflexivity) end.
  apply (m2_cb_split_z _ _ _ 6 (Z.to_nat n - 6)) in RW1; [| lia]. destruct RW1 as [m2W1 RW1].
  apply (m2_cb_split_z _ _ _ 6 (Z.to_nat n - 12)) in RW1; [| lia]. destruct RW1 as [m2W2 RW1].
  apply (m2_cb_split_z _ _ _ 18 (Z.to_nat n - 30)) in RW1; [| lia]. destruct RW1 as [m2W3 RW1].
  apply (m2_cb_split_z _ _ _ (length (fr_body b)) (30 - length (fr_body b))) in RW1; [| lia].
  destruct RW1 as [m2W4 m2W5].
  change (Z.of_nat 6) with 6 in m2W2, m2W3, m2W4, m2W5. change (Z.of_nat 18) with 18 in m2W4, m2W5.
  replace (want + 6 + 6) with (want + 12) in m2W3 by lia.
  replace (want + 6 + 6 + 18) with (want + 30) in m2W4 by lia.
  replace (want + 6 + 6 + 18) with (want + 30) in m2W5 by lia.
  (* 0x13218: memcpy (want, buf, 6) *)
  do 4 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HMC with (src := fr_dst b); [uns; exact m2BD | uns; exact Ld | uns; exact m2W1 | uns; lia | eassumption]
    | intros ms2 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mB & -> &
                  MU2 & WM2 & MI2 & RW2 & SRC2);
      clear SRC2; m2_after mm MU2 WM2 MI2 ]
  end.
  rewrite ?unsigned_lit in RW2 by lia. rename RW2 into m2W1.
  (* 0x13228: s5 = want + 6; memcpy (want + 6, buf + 6, 6) *)
  do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply HMC with (src := fr_src b); [uns; exact m2BS | uns; exact Ls | uns; exact m2W2 | uns; lia | eassumption]
    | intros ms3 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mC & -> &
                  MU3 & WM3 & MI3 & RW3 & SRC3);
      clear SRC3; m2_after mm MU3 WM3 MI3 ]
  end.
  rewrite ?unsigned_lit in RW3 by lia. rename RW3 into m2W2.
  (* 0x1323c .. 0x1325c: 0x88 0x5f and numbytes at want + 12 .. 15 *)
  do 9 m2_s.
  (* 0x13260 .. 0x13278: the sum of the body *)
  eapply m2_sum with (bb := fr_body b); [exact m2BY | lia | f_equal; lia | first [reflexivity | lia] | ].
  intros a1' a2' a3'.
  (* 0x1327c .. 0x132d8: the sum, send, ack, retry, cmd, ncmds at want + 16 .. 29 *)
  do 24 m2_s.
  lazymatch type of m2W3 with rw_cells _ _ _ ?cs =>
    assert (HS3 : cells_size cs = 18%nat) by reflexivity;
    assert (HB3 : cells_bytes cs = m2_hdr (Z.of_nat (length (fr_body b))) (spec_sum (fr_body b)) (fr_send b)
                                     (fr_ack b) (fr_retry b) (fr_cmd b) (fr_ncmds b))
      by (cbn [cells_bytes cbytes app]; unfold m2_hdr; m2_lists; m2_byte)
  end.
  (* 0x132dc: the body, when there is one *)
  step.
  destruct (Z.eq_dec (fr_body_len b) 0) as [L0|L0].
  - br true.
    assert (FB0 : fr_body b = []) by (apply length_zero_iff_nil; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (W4 : rw_cells rsegs mm (want + 30) [CB (length (fr_body b)) (fr_body b)])
        by (rewrite FB0; rewrite FB0 in m2W4; exact m2W4)
    end.
    eapply m2_end; eassumption.
  - br false. do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply HMC with (src := fr_body b);
        [uns; exact m2BY | uns; exact LFB | uns; rewrite <- LFB; exact m2W4 | uns; lia | eassumption]
      | intros ms4 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mD & -> &
                    MU4 & WM4 & MI4 & RW4 & SRC4);
        clear SRC4; m2_after mm MU4 WM4 MI4 ]
    end.
    rewrite ?unsigned_lit in RW4 by lia. rewrite <- LFB in RW4.
    eapply m2_end; eassumption.
Qed.

(** * 0x13190 .. 0x13310 *)

Lemma crt_m2_ok : crt_m2_stmt.
Proof.
  unfold crt_m2_stmt.
  intros HMS HMC HBC ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    w buf out want n b j sv HC HLB Hn LAY SW BB OUT STW Hsv FR MI.
  pose proof LAY as LAY'. destruct LAY' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hw0 & Hw1).
  pose proof (u64_range sp) as Rsp.
  destruct (fr_code_ok b HC) as (L30 & _ & _ & _).
  destruct (fr_body_len_ok b HC) as (BL0 & PL0 & BLP).
  pose proof (length_fr_body b HC) as LFB.
  assert (NL : n = Z.max 60 (30 + Z.of_nat (length (fr_body b)))) by (subst n; unfold frame_len; lia).
  unfold crt_sys.
  destruct (Z.le_gt_cases (Z.of_nat (length (fr_body b))) 1484) as [FIT|NFIT];
    destruct (system_at (fr_body b)) eqn:SYS; cbv iota.
  (* 0x13190 .. 0x131c8: the answer is -4 past 1484 body bytes, else -10 for a system
     message, else n; s9 = sys | !fits *)
  1: { (* fits, sys: -10 *)
    assert (BC : build_code (fr_body b) n = -10).
    { unfold build_code. rewrite SYS.
      replace (1484 <? Z.of_nat (length (fr_body b))) with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity. }
    assert (OK : crt_ok b = false) by (unfold crt_ok; rewrite SYS; cbn [negb]; apply andb_false_r).
    rewrite BC.
    step. step. step. br true.
    step. rewrite m2_sltiu_t by lia.
    step. step. brc.
    step. step. brc.
    step. step. step. brc.
    eapply m2_tail; try eassumption.
    - rewrite BC. first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity].
    - rewrite OK. first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
  1: { (* fits, no sys: n *)
    assert (OK : crt_ok b = true).
    { unfold crt_ok. rewrite SYS. apply andb_true_iff. split; [apply Z.leb_le; lia | reflexivity]. }
    pose proof (m2_code_true b OK) as BC. rewrite <- Hn in BC. rewrite BC.
    step. step. step. br true.
    step. rewrite m2_sltiu_t by lia.
    step. step. brc.
    step. step. step. brc.
    step. step.
    rewrite (unsigned_lit n) by lia. rewrite (m2_swrap n) by lia. br false.
    eapply m2_tail; try eassumption.
    - rewrite BC. first [reflexivity | f_equal; lia].
    - rewrite OK. first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
  (* past 1484 body bytes: -4 *)
  all: assert (BC : build_code (fr_body b) n = -4) by
         (unfold build_code;
          replace (1484 <? Z.of_nat (length (fr_body b))) with true by (symmetry; apply Z.ltb_lt; lia);
          reflexivity).
  all: assert (OK : crt_ok b = false) by
         (unfold crt_ok;
          replace (Z.of_nat (length (fr_body b)) <=? 1484) with false by (symmetry; apply Z.leb_gt; lia);
          reflexivity).
  all: rewrite BC.
  all: step; step; step; br false.
  all: step; step; brc.
  all: step; rewrite m2_sltiu_f by lia.
  all: step; step; brc.
  all: step; step; step; brc.
  all: eapply m2_tail; try eassumption.
  all: first [ rewrite BC; first [reflexivity | f_equal; lia | apply bv_eq; vm_compute; reflexivity]
             | rewrite OK; first [reflexivity | apply bv_eq; vm_compute; reflexivity] ].
Qed.
