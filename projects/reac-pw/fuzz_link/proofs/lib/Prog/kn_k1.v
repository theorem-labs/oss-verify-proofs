(* reac-pw/fuzz_link, PLAIN build: kernel (0x14190-0x14faf), part 1: the chunk loop and what it does with one
   chunk besides building messages: the queueing of a chunk into g_nl (+0xc94, and its copy at +0xda0 on the
   raw-input path), the empty-cursor path (+0xc78), the raw-input path (+0xcec), the message path's start
   (+0x200) and its end (+0xc64), the latch (+0xce0), the loop (+0x1d4), the prologue and the top of the walk.
   The message loop itself is kn_kmsg.v (k_msgloop). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0
  memcpy_c memcpy memset_c memset.
Local Open Scope Z_scope.

(* ==========================================================================
   1. g_nl as one array: reads, and writes that keep its bytes
   ========================================================================== *)

Lemma u8arr_rd : forall m A bs E n a,
  u8arr rsegs m A bs -> A <= E -> E + Z.of_nat n <= A + Z.of_nat (length bs) -> a = wa E ->
  ov_read_bytes rsegs m a n = Some (slice bs (E - A) (Z.of_nat n)).
Proof.
  intros m A bs E n a [HB _] H1 H2 ->.
  assert (EE : wa E = wa (A + (E - A))) by (f_equal; lia). rewrite EE.
  rewrite (bytes_at_read rsegs m A bs (E - A) n HB) by lia. unfold slice. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma u8arr_rd4 : forall m A bs E a,
  u8arr rsegs m A bs -> A <= E -> E + 4 <= A + Z.of_nat (length bs) -> a = wa E ->
  ov_read_bytes rsegs m a 4 = Some (le4 (wz (rdn bs (E - A) 4))).
Proof.
  intros m A bs E a H H1 H2 Ha. rewrite (u8arr_rd m A bs E 4 a H H1 ltac:(lia) Ha).
  f_equal. apply rdn_le4_slice; lia.
Qed.

Lemma u8arr_store_ok_z : forall m A bs E n,
  u8arr rsegs m A bs -> A <= E -> E + Z.of_nat n <= A + Z.of_nat (length bs) ->
  store_ok rsegs m (wa E) n = true.
Proof.
  intros m A bs E n [_ HW] H1 H2. replace E with (A + (E - A)) by lia.
  apply wr_at_store_ok with (n := Z.of_nat (length bs)); [exact HW | lia | lia].
Qed.

Lemma u8arr_write_z : forall m A bs E l,
  u8arr rsegs m A bs -> A <= E -> E + Z.of_nat (length l) <= A + Z.of_nat (length bs) ->
  u8arr rsegs (write_to_mem m (wa E) l) A (upd_bytes bs (Z.to_nat (E - A)) l).
Proof.
  intros m A bs E l [HB HW] H1 H2. pose proof (bytes_at_bound rsegs m A bs HB). split.
  - assert (EE : wa E = wa (A + (E - A))) by (f_equal; lia). rewrite EE.
    apply bytes_at_write_inside; [exact HB | lia | lia].
  - rewrite upd_bytes_length by lia. apply wr_at_write. exact HW.
Qed.

Lemma signed_lit : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. unfold bv_signed. rewrite unsigned_lit by lia. unfold bv_swrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_wrap 64 (z + 2 ^ 63)) with ((z + 2 ^ 63) mod 2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

(* chunk j of g_nl cut out for memcpy, and put back *)
Lemma gnl_cut_chunk : forall m kbs j wn,
  u8arr rsegs m 203648 kbs -> Z.of_nat (length kbs) = 271992 -> 0 <= j <= 63 -> 0 <= wn <= 4096 ->
  exists pre post,
    bytes_at rsegs m 203648 pre /\ Z.of_nat (length pre) = 4096 * j /\
    rw_cells rsegs m (203648 + 4096 * j) [CB (Z.to_nat wn) (slice kbs (4096 * j) wn)] /\
    bytes_at rsegs m (203648 + 4096 * j + wn) post /\ Z.of_nat (length post) = 271992 - 4096 * j - wn /\
    wr_at rsegs m 203648 271992 /\
    pre = firstn (Z.to_nat (4096 * j)) kbs /\ post = skipn (Z.to_nat (4096 * j) + Z.to_nat wn) kbs.
Proof.
  intros m kbs j wn NK GL J W.
  assert (NK' : nlk_at m kbs) by (split; [exact NK | exact GL]).
  destruct (nlk_split m kbs (4096 * j) [CB (Z.to_nat wn) (slice kbs (4096 * j) wn)] NK') as (B1 & C & B3 & WA).
  - lia.
  - cbn [cells_wf cell_wf]. split; [|exact I]. apply slice_length; lia.
  - cbn [cells_size csize]. unfold NK_SIZE. lia.
  - cbn [cells_bytes cbytes cells_size csize]. rewrite app_nil_r, Nat.add_0_r, Z2Nat.id by lia. reflexivity.
  - cbn [cells_size csize] in B3. rewrite Nat.add_0_r in B3.
    exists (firstn (Z.to_nat (4096 * j)) kbs), (skipn (Z.to_nat (4096 * j) + Z.to_nat wn) kbs).
    split; [exact B1|]. split; [rewrite length_firstn; lia|]. split; [exact C|].
    split; [eapply bytes_at_at; [exact B3 | unfold A_G_NL; lia]|]. split; [rewrite length_skipn; lia|].
    split; [exact WA|]. split; reflexivity.
Qed.

Lemma gnl_join_chunk : forall m kbs j wn src,
  Z.of_nat (length kbs) = 271992 -> 0 <= j <= 63 -> 0 <= wn <= 4096 -> Z.of_nat (length src) = wn ->
  bytes_at rsegs m 203648 (firstn (Z.to_nat (4096 * j)) kbs) ->
  rw_cells rsegs m (203648 + 4096 * j) [CB (Z.to_nat wn) src] ->
  bytes_at rsegs m (203648 + 4096 * j + wn) (skipn (Z.to_nat (4096 * j) + Z.to_nat wn) kbs) ->
  wr_at rsegs m 203648 271992 ->
  u8arr rsegs m 203648 (upd_bytes kbs (Z.to_nat (4096 * j)) src) /\
  Z.of_nat (length (upd_bytes kbs (Z.to_nat (4096 * j)) src)) = 271992.
Proof.
  intros m kbs j wn src GL J W LS B1 C B3 WA.
  destruct (nlk_join m kbs (4096 * j) [CB (Z.to_nat wn) src] GL ltac:(lia)) as [[NK _] LU].
  - cbn [cells_size csize]. unfold NK_SIZE. lia.
  - exact B1.
  - exact C.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. eapply bytes_at_at; [exact B3 | unfold A_G_NL; lia].
  - exact WA.
  - cbn [cells_bytes cbytes] in NK, LU. rewrite app_nil_r in NK, LU. split; [exact NK | rewrite LU; exact GL].
Qed.

(* the queue's three writes keep kgnl, one chunk longer *)
Lemma kgnl_queue : forall c kbs j wn src,
  kgnl c kbs j -> 0 <= j <= 2 -> 0 <= wn <= 4096 -> Z.of_nat (length src) = wn ->
  kgnl c (upd_bytes (upd_bytes (upd_bytes kbs (Z.to_nat (4096 * j)) src)
                               (Z.to_nat 262656) (le4 (Z_to_bv 64 (j + 1))))
                    (Z.to_nat (262144 + 8 * j)) (le8 (Z_to_bv 64 wn))) (j + 1).
Proof.
  intros c kbs j wn src (GL & GS & GJ & GN & GE & GSO & GSE & GC) J W LS. unfold NK_SIZE in GL.
  set (k1 := upd_bytes kbs (Z.to_nat (4096 * j)) src).
  assert (L1 : Z.of_nat (length k1) = 271992) by (unfold k1; rewrite upd_bytes_length by lia; exact GL).
  set (k2 := upd_bytes k1 (Z.to_nat 262656) (le4 (Z_to_bv 64 (j + 1)))).
  assert (L2 : Z.of_nat (length k2) = 271992)
    by (unfold k2; rewrite upd_bytes_length by (rewrite length_le4; lia); exact L1).
  set (k3 := upd_bytes k2 (Z.to_nat (262144 + 8 * j)) (le8 (Z_to_bv 64 wn))).
  assert (L3 : Z.of_nat (length k3) = 271992)
    by (unfold k3; rewrite upd_bytes_length by (rewrite length_le8; lia); exact L2).
  (* a field outside the three writes reads as in kbs *)
  assert (O : forall a n, 0 <= a -> 0 <= n -> a + n <= 271992 ->
     (a + n <= 4096 * j \/ 4096 * j + wn <= a) -> (a + n <= 262656 \/ 262660 <= a) ->
     (a + n <= 262144 + 8 * j \/ 262144 + 8 * j + 8 <= a) -> rdn k3 a n = rdn kbs a n).
  { intros a n Ha Hn H0 H1 H2 H3. unfold k3.
    rewrite rdn_upd_out by (rewrite ?length_le8; lia). unfold k2.
    rewrite rdn_upd_out by (rewrite ?length_le4; lia). unfold k1.
    apply rdn_upd_out; lia. }
  unfold kgnl. split; [unfold NK_SIZE; exact L3|].
  split.
  { assert (SK : forall bs k l, (k + length l <= Z.to_nat 262676)%nat -> (Z.to_nat 262676 <= length bs)%nat ->
              skipn (Z.to_nat 262676) (upd_bytes bs k l) = skipn (Z.to_nat 262676) bs).
    { intros bs k l H1 H2. apply list_eq_nth. intros i. rewrite !nth_error_skipn.
      destruct (Nat.lt_ge_cases (Z.to_nat 262676 + i) (length bs)) as [Hi|Hi].
      - rewrite upd_bytes_nth by lia.
        match goal with |- context [if ?b then _ else _] => destruct b eqn:E end; [|reflexivity].
        apply andb_prop in E as [E1 E2]. apply Nat.ltb_lt in E2. lia.
      - rewrite (proj2 (nth_error_None bs _)) by lia.
        apply nth_error_None. rewrite upd_bytes_length by lia. lia. }
    unfold k3. rewrite SK by (rewrite ?length_le8; lia).
    unfold k2. rewrite SK by (rewrite ?length_le4; lia).
    unfold k1. rewrite SK by lia. exact GS. }
  split.
  { unfold k3. rewrite rdn_upd_out by (rewrite ?length_le8; lia). unfold k2.
    rewrite rdn_upd_in by (rewrite ?length_le4; lia). replace (262656 - Z.of_nat (Z.to_nat 262656)) with 0 by lia.
    rewrite <- (app_nil_r (le4 (Z_to_bv 64 (j + 1)))). rewrite rdn_le4_head by reflexivity.
    rewrite unsigned_lit by lia. apply Z.mod_small. lia. }
  split; [rewrite O by lia; exact GN|].
  split; [rewrite O by lia; exact GE|].
  split; [rewrite O by lia; exact GSO|].
  split; [rewrite O by lia; exact GSE|].
  intros i Hi. destruct (Z.eq_dec i j) as [->|NE].
  - unfold k3. rewrite rdn_upd_in by (rewrite ?length_le8; lia).
    replace (262144 + 8 * j - Z.of_nat (Z.to_nat (262144 + 8 * j))) with 0 by lia.
    rewrite <- (app_nil_r (le8 (Z_to_bv 64 wn))). rewrite rdn_le8_head by reflexivity.
    rewrite unsigned_lit by lia. lia.
  - rewrite O by lia. apply GC. lia.
Qed.

(* the reply buffer as one run for memset(w, 0, 4112), and the zeros it leaves as the buffer's runs *)
Lemma kw_join16 : forall m A wbj wnc,
  rw_cells rsegs m A [CB (Z.to_nat 4096) wbj] -> rw_cells rsegs m (A + 4096) wnc -> cells_size wnc = 16%nat ->
  exists j, rw_cells rsegs m A [CB (Z.to_nat 4112) j].
Proof.
  intros m A wbj wnc C1 C2 S.
  assert (C : rw_cells rsegs m A ([CB (Z.to_nat 4096) wbj] ++ wnc)).
  { apply rw_cells_app. split; [exact C1|]. eapply rw_cells_at; [exact C2|]. cbn [cells_size csize]. lia. }
  exists (cells_bytes ([CB (Z.to_nat 4096) wbj] ++ wnc)).
  pose proof C as [[Hwf _] _].
  apply (rw_cells_same_bytes m A _ _ C).
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite cells_bytes_length by exact Hwf.
    rewrite cells_size_app. cbn [cells_size csize]. rewrite S. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
  - rewrite cells_size_app. cbn [cells_size csize]. rewrite S. lia.
Qed.

Lemma kw_zero : forall m A z,
  rw_cells rsegs m A [CB (Z.to_nat 4112) (repeat z (Z.to_nat 4112))] -> z = Z_to_bv 8 0 ->
  rw_cells rsegs m A [CB (Z.to_nat 4096) (repeat z (Z.to_nat 4096))] /\
  rw_cells rsegs m (A + 4096) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat z 4)].
Proof.
  intros m A z C ->.
  assert (C' : rw_cells rsegs m A
                 ([CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))] ++
                  [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4)])).
  { apply (rw_cells_same_bytes m A _ _ C).
    - cbn [app cells_wf cell_wf]. rewrite !repeat_length. repeat split.
    - cbn [app cells_bytes cbytes]. rewrite app_nil_r.
      replace (Z.to_nat 4112) with (Z.to_nat 4096 + 16)%nat by lia. rewrite repeat_app. f_equal; try reflexivity.
    - cbn [app cells_size csize]. lia. }
  apply rw_cells_app in C'. destruct C' as [C1 C2]. split; [exact C1|].
  eapply rw_cells_at; [exact C2|]. cbn [cells_size csize]. lia.
Qed.

(* a callee that wrote [A, A + n) and left readable bytes there keeps every stack fact *)
Lemma stk_after_region : forall m m' lo hi A n bs,
  stk rsegs m lo hi -> munch [(A, A + n)] m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' A bs -> Z.of_nat (length bs) = n -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi A n bs (H0 & H1 & H) MU WM HB LB. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Z.lt_ge_cases a A) as [L|L]; [|destruct (Z.lt_ge_cases a (A + n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia. lia.
  - destruct HB as (_ & _ & HB). specialize (HB (Z.to_nat (a - A)) ltac:(lia)).
    replace (A + Z.of_nat (Z.to_nat (a - A))) with a in HB by lia. rewrite HB.
    destruct (nth_error bs (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. cbn [outside]. rewrite wa_unsigned by lia. lia.
Qed.

(* a store into g_nl, which the walk keeps as one array: before the step pose its store_ok; after it, the array
   with the new bytes replaces the old one, and store_done carries the rest over *)
Ltac gnl_after_store NK NKL :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
    let E := addr_expr a in
    lazymatch type of NK with u8arr _ _ 203648 ?kb =>
      let NK2 := fresh "NK" in let NKL2 := fresh "NKL" in
      pose proof (u8arr_write_z mm 203648 kb E bs NK ltac:(lia) ltac:(rewrite ?length_le4, ?length_le8; lia)) as NK2;
      assert (NKL2 : Z.of_nat (length (upd_bytes kb (Z.to_nat (E - 203648)) bs)) = 271992)
        by (rewrite upd_bytes_length by (rewrite ?length_le4, ?length_le8; lia); exact NKL);
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      clear NK NKL; store_done; rename NK2 into NK; rename NKL2 into NKL
    end
  end.

(* ==========================================================================
   2. The loop's latch state, and the queueing of one chunk (+0xc94)
   ========================================================================== *)

Definition klatch (c : kfix) (m : word -> option byte) (adv : Z) (kbs : list byte) (j : Z) (la : list byte)
    (n ci : Z) : Prop :=
  (exists j0 mc kd atw, kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) mc kd atw) /\
  (exists wbj, rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj]) /\
  (exists wnc, rw_cells rsegs m (kSP c + -120) wnc /\ cells_size wnc = 16%nat) /\
  kcore c m adv kbs j la /\ 1 <= n <= 3 /\ 0 <= ci < n /\ 0 <= j <= ci + 1.

(* the latch at 0x14e70 (+0xce0): s1 holds the chunk index again *)
Definition k_latch_k (c : kfix) (n ci : Z) : Prop :=
  forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y23 y25 y27 y28 y29 y30 y31 : word)
         (m : word -> option byte) adv kbs j la,
    klatch c m adv kbs j la n ci ->
    evt rsegs (kf_Q c)
      (MS (mkR y1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) y5 y6 y7 (kf_a0 c) (Z_to_bv 64 ci) y10 y11 y12
               y13 y14 y15 y16 y17 y18 y19 y20 (Z_to_bv 64 203648) (Z_to_bv 64 n) y23 (Z_to_bv 64 (kSP c + -120))
               y25 (Z_to_bv 64 (-4093)) y27 y28 y29 y30 y31)
          (kf_F c) (Z_to_bv 64 0x14e70) (kf_fc c) None m (seg_rom rsegs)).

Lemma k_queue : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la n ci mc kd atw j0 wbj wfw pad wn,
  kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) mc kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) [C8 (Z_to_bv 64 wn); C4 wfw; CB 4 pad] ->
  kcore c m adv kbs j la -> 1 <= wn <= 4096 -> 1 <= n <= 3 -> 0 <= ci < n -> 0 <= j <= ci ->
  k_latch_k c n ci ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) x9 x10 x11 x12 x13 x14 x15
             x16 x17 (Z_to_bv 64 wn) x19 x20 (Z_to_bv 64 203648) (Z_to_bv 64 n) x23
             (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14e24) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la n
    ci mc kd atw j0 wbj wfw pad wn SPL WB WNC KC WNR NR CIR JR LK.
  kctx c HC.
  destruct KC as (FRS & ADV & CUR & IN & NK & GI & LA & MU & WM & MI & ST).
  unfold kspill in SPL; unfold kfrs in FRS; unfold kW in MU.
  pose proof GI as (GL & GS & GJ & GN & GE & GSO & GSE & GC). unfold NK_SIZE in GL.
  pose proof (rw_cells_bound rsegs _ _ _ WB) as WBB. cbn [cells_size csize] in WBB.
  zstep.
  pose proof (u8arr_rd4 m 203648 kbs 466304 (Z_to_bv 64 466304) NK ltac:(lia) ltac:(lia) eq_refl) as RD.
  replace (466304 - 203648) with 262656 in RD by reflexivity. rewrite GJ in RD.
  zstep. rewrite sx32_wz by lia. unfold wz.
  zstep. zstep. if_cases K; zify_cond K; rewrite ?signed_lit in K by lia; [exfalso; lia|].
  zstep. zstep. zstep. zstep.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 12) with 4096.
  (* the source: the first wn bytes of w.b; the destination: chunk j of g_nl *)
  assert (SRC : bytes_at rsegs m (kSP c + -4216) (firstn (Z.to_nat wn) wbj)).
  { destruct WB as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    rewrite <- (firstn_skipn (Z.to_nat wn) wbj) in HB. apply bytes_at_app in HB. exact (proj1 HB). }
  assert (LW : length wbj = Z.to_nat 4096) by (destruct WB as [[[HW _] _] _]; exact HW).
  destruct (gnl_cut_chunk m kbs j wn NK GL ltac:(lia) ltac:(lia)) as (pre & post & B1 & LP1 & DST & B3 & LP3 & WA & Epre & Epost).
  clear NK RD.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply memcpy_holds with (src := firstn (Z.to_nat wn) wbj) (junk := slice kbs (4096 * j) wn)
    | ]
  end.
  - rewrite unsigned_lit by lia. exact SRC.
  - rewrite length_firstn, unsigned_lit by lia. lia.
  - rewrite !unsigned_lit by lia. replace (203648 + j * 4096) with (203648 + 4096 * j) by lia. exact DST.
  - rewrite !unsigned_lit by lia. lia.
  - exact MI.
  - intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc
                    & WMc & MIc & DSTc & SRCc).
    repeat match goal with H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
      rewrite (unsigned_lit z) in H by lia end.
    replace (203648 + j * 4096) with (203648 + 4096 * j) in MUc, DSTc by lia.
    match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    assert (ST' : stk rsegs m' (kf_lo c) (kSP c + -4336)).
    { destruct DSTc as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
      eapply stk_after_region; [exact ST | exact MUc | exact WMc | exact HB | rewrite length_firstn; lia]. }
    transport_after_call rsegs m m' MUc WMc. clear MUc WMc MI. rename MIc into MI. rename ST' into ST.
    subst pre post.
    destruct (gnl_join_chunk m' kbs j wn (firstn (Z.to_nat wn) wbj) GL ltac:(lia) ltac:(lia)
                ltac:(rewrite length_firstn; lia) B1 DSTc B3 WA) as [NK LK1].
    set (kbs1 := upd_bytes kbs (Z.to_nat (4096 * j)) (firstn (Z.to_nat wn) wbj)) in NK, LK1.
    assert (G1 : rdn kbs1 262656 4 = j).
    { unfold kbs1. rewrite rdn_upd_out by (rewrite ?length_firstn; lia). exact GJ. }
    zstep.
    pose proof (u8arr_rd4 m' 203648 kbs1 466304 (Z_to_bv 64 466304) NK ltac:(lia) ltac:(lia) eq_refl) as RD.
    replace (466304 - 203648) with 262656 in RD by reflexivity. rewrite G1 in RD.
    zstep. rewrite sx32_wz by lia. unfold wz.
    zstep.
    pose proof (u8arr_store_ok_z m' 203648 kbs1 466304 4 NK ltac:(lia) ltac:(lia)) as HS.
    zstep. gnl_after_store NK LK1.
    zstep. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    zstep.
    match goal with H : u8arr _ ?mm 203648 ?kb |- _ =>
      pose proof (u8arr_store_ok_z mm 203648 kb (465792 + j * 8) 8 H ltac:(lia) ltac:(lia)) as HS2 end.
    zstep. gnl_after_store NK LK1.
    zstep.
    replace (465792 + j * 8 - 203648) with (262144 + 8 * j) in NK, LK1 by lia.
    eapply LK.
    refine (conj (ex_intro _ j0 (ex_intro _ mc (ex_intro _ kd (ex_intro _ atw SPL))))
              (conj (ex_intro _ wbj WB) (conj (ex_intro _ _ (conj WNC eq_refl)) (conj _ (conj NR (conj CIR _)))))).
    1: refine (conj FRS (conj ADV (conj CUR (conj IN (conj NK (conj _ (conj LA (conj MU (conj WM (conj MI ST)))))))))).
    1: (unfold kbs1; apply kgnl_queue; [exact GI | lia | lia | rewrite length_firstn; lia]).
    lia.
Qed.

(* kcore as named hypotheses, and back *)
Ltac kcore_unpack H :=
  destruct H as (FRS & ADV & CUR & IN & NK & GI & LA & MU & WM & MI & ST);
  unfold kfrs in FRS; unfold kW in MU;
  let GL := fresh "GL" in pose proof GI as [GL _]; unfold NK_SIZE in GL.

Ltac kcore_pack :=
  lazymatch goal with |- kcore _ ?m _ _ _ _ =>
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))));
    first [eassumption | lia | idtac]
  end.

(* +0xc88: an empty buffer gets the four zero bytes `nl_put32(&w, 0)`, then the queue *)
Lemma k_c88 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la n ci mc kd atw j0 wbj w0 wfw pad,
  kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) mc kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) [C8 w0; C4 wfw; CB 4 pad] ->
  kcore c m adv kbs j la -> 1 <= n <= 3 -> 0 <= ci < n -> 0 <= j <= ci ->
  k_latch_k c n ci ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) x9 x10 x11 x12 x13 x14 x15
             x16 x17 x18 x19 x20 (Z_to_bv 64 203648) (Z_to_bv 64 n) x23
             (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14e18) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la
    n ci mc kd atw j0 wbj w0 wfw pad SPL WB WNC KC NR CIR JR LK.
  kctx c HC. kcore_unpack KC. unfold kspill in SPL.
  zstep. zstep. zstep.
  eapply k_queue; [exact HC | exact SPL | exact WB | exact WNC | kcore_pack | lia | lia | lia | lia | exact LK].
Qed.

(* memset(w, 0, 4112) at a call site (pc = memset, a0 = w, a1 = 0, a2 = 4112): the buffer's two runs become
   zeros, every other hypothesis is carried over *)
Ltac memset_w c :=
  lazymatch goal with
  | WB : rw_cells _ ?mm (kSP c + -4216) [CB (Z.to_nat 4096) ?wbj],
    WNC : rw_cells _ ?mm (kSP c + -120) ?wnc, WNS : cells_size ?wnc = 16%nat, MI : mem_inv _ ?mm
    |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let jw := fresh "jw" in let WW := fresh "WW" in
    destruct (kw_join16 mm (kSP c + -4216) wbj wnc WB
                ltac:(eapply rw_cells_at; [exact WNC | lia]) WNS) as [jw WW];
    clear WB WNC WNS;
    eapply evt_cut;
    [ eapply memset_holds with (junk := jw); [ rewrite !unsigned_lit by lia; exact WW | exact MI ] | ];
    let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO; unfold memset_post in PO;
    let m' := fresh "m" in
    destruct PO as (?t0 & ?t1 & ?t2 & ?a1 & ?a2 & ?a3 & ?a4 & ?a5 & ?a6 & ?a7 & ?t3 & ?t4 & ?t5 & ?t6 & m' & -> &
                    ?MUc & ?WMc & ?MIc & ?WC);
    repeat match goal with H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
      rewrite (unsigned_lit z) in H by lia end;
    match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end;
    lazymatch goal with MUc : munch _ mm m', WMc : wmono _ mm m', MIc : mem_inv _ m', WC : rw_cells _ m' _ _ |- _ =>
      transport_after_call rsegs mm m' MUc WMc; clear MUc WMc MI; rename MIc into MI;
      let WB' := fresh "WB" in let WNC' := fresh "WNC" in
      destruct (kw_zero m' (kSP c + -4216) _ WC ltac:(reflexivity)) as [WB' WNC'];
      clear WC; replace (kSP c + -4216 + 4096) with (kSP c + -120) in WNC' by lia
    end
  end.

(* +0xc78: the cursor is empty: memset(w), then +0xc88 *)
Lemma k_c78 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la n ci mc kd atw j0 wbj wnc,
  kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) mc kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) wnc -> cells_size wnc = 16%nat ->
  kcore c m adv kbs j la -> 1 <= n <= 3 -> 0 <= ci < n -> 0 <= j <= ci ->
  k_latch_k c n ci ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) x9 x10 x11 x12 x13 x14 x15
             x16 x17 x18 x19 x20 (Z_to_bv 64 203648) (Z_to_bv 64 n) x23
             (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14e08) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la
    n ci mc kd atw j0 wbj wnc SPL WB WNC WNS KC NR CIR JR LK.
  kctx c HC. kcore_unpack KC. unfold kspill in SPL.
  zstep. zstep. zstep. zstep.
  memset_w c.
  eapply k_c88; [exact HC | exact SPL | exact WB | exact WNC | kcore_pack | lia | lia | lia | exact LK].
Qed.

(* the end of a message path, 0x14df4 (+0xc64): queue w, or put 4 zero bytes first when it is empty *)
Lemma k_c64 : forall c, kf_ok c ->
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y27 y28 y29 y30 y31 : word)
         (m : word -> option byte) adv kbs j la n ci mc wn wf,
  kmsg_st c m adv kbs j la n ci mc wn wf -> k_latch_k c n ci ->
  evt rsegs (kf_Q c)
    (MS (mkR y1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) y5 y6 y7 (kf_a0 c) y9 y10 y11 y12 y13 y14 y15
             y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 (kSP c + -120)) y25 (Z_to_bv 64 (-4093)) y27 y28 y29 y30 y31)
        (kf_F c) (Z_to_bv 64 0x14df4) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y27 y28 y29 y30 y31 m adv
    kbs j la n ci mc wn wf KM LK.
  kctx c HC. kmsg_unpack KM. pose proof GI as [GL _]. unfold NK_SIZE in GL.
  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - eapply k_c88; [exact HC | exact SPL | exact WB | exact WNC | kcore_pack | lia | lia | lia | exact LK].
  - zstep.
    eapply k_queue; [exact HC | exact SPL | exact WB | exact WNC | kcore_pack | lia | lia | lia | lia | exact LK].
Qed.

(* name the current memory m again after a store has cleared the old one *)
Tactic Notation "mem_as" ident(m) :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m end.

(* +0xd88 .. +0xdd8: the raw path's queueing: w.n := wn, then (when wn <> 0) the copy of k_queue's three writes *)
Lemma k_d88 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la n ci mc kd atw j0 wbj w0 wfw pad wn,
  kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) mc kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) [C8 w0; C4 wfw; CB 4 pad] ->
  kcore c m adv kbs j la -> 0 <= wn <= 4096 -> 1 <= n <= 3 -> 0 <= ci < n -> 0 <= j <= ci ->
  k_latch_k c n ci ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) (Z_to_bv 64 ci) x10 x11 x12
             x13 x14 x15 x16 x17 x18 (Z_to_bv 64 wn) (Z_to_bv 64 (kSP c + -120)) (Z_to_bv 64 203648)
             (Z_to_bv 64 n) x23 (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14f18) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la n ci mc kd
    atw j0 wbj w0 wfw pad wn SPL WB WNC KC WNR NR CIR JR LK.
  kctx c HC.
  destruct KC as (FRS & ADV & CUR & IN & NK & GI & LA & MU & WM & MI & ST).
  unfold kspill in SPL; unfold kfrs in FRS; unfold kW in MU.
  pose proof GI as (GL & GS & GJ & GN & GE & GSO & GSE & GC). unfold NK_SIZE in GL.
  pose proof (rw_cells_bound rsegs _ _ _ WB) as WBB. cbn [cells_size csize] in WBB.
  zstep.
  pose proof (u8arr_rd4 m 203648 kbs 466304 (Z_to_bv 64 466304) NK ltac:(lia) ltac:(lia) eq_refl) as RD.
  replace (466304 - 203648) with 262656 in RD by reflexivity. rewrite GJ in RD.
  zstep. rewrite sx32_wz by lia. unfold wz. clear RD.
  zstep. mem_as m. zstep. zstep. if_cases K; zify_cond K; rewrite ?signed_lit in K by lia; [exfalso; lia|].
  zstep. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia.
  { (* wn = 0: nothing queued *)
    eapply LK.
    refine (conj (ex_intro _ j0 (ex_intro _ mc (ex_intro _ kd (ex_intro _ atw SPL))))
              (conj (ex_intro _ wbj WB) (conj (ex_intro _ _ (conj WNC eq_refl)) (conj _ (conj NR (conj CIR _)))))).
    1: refine (conj FRS (conj ADV (conj CUR (conj IN (conj NK (conj GI (conj LA (conj MU (conj WM (conj MI ST)))))))))).
    lia. }
  zstep. zstep. zstep. zstep.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 12) with 4096.
  assert (SRC : bytes_at rsegs m (kSP c + -4216) (firstn (Z.to_nat wn) wbj)).
  { destruct WB as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    rewrite <- (firstn_skipn (Z.to_nat wn) wbj) in HB. apply bytes_at_app in HB. exact (proj1 HB). }
  assert (LW : length wbj = Z.to_nat 4096) by (destruct WB as [[[HW _] _] _]; exact HW).
  destruct (gnl_cut_chunk m kbs j wn NK GL ltac:(lia) ltac:(lia)) as (pre & post & B1 & LP1 & DST & B3 & LP3 & WA & Epre & Epost).
  clear NK.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply memcpy_holds with (src := firstn (Z.to_nat wn) wbj) (junk := slice kbs (4096 * j) wn)
    | ]
  end.
  - rewrite unsigned_lit by lia. exact SRC.
  - rewrite length_firstn, unsigned_lit by lia. lia.
  - rewrite !unsigned_lit by lia. replace (203648 + j * 4096) with (203648 + 4096 * j) by lia. exact DST.
  - rewrite !unsigned_lit by lia. lia.
  - exact MI.
  - intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc
                    & WMc & MIc & DSTc & SRCc).
    repeat match goal with H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
      rewrite (unsigned_lit z) in H by lia end.
    replace (203648 + j * 4096) with (203648 + 4096 * j) in MUc, DSTc by lia.
    match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    assert (ST' : stk rsegs m' (kf_lo c) (kSP c + -4336)).
    { destruct DSTc as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
      eapply stk_after_region; [exact ST | exact MUc | exact WMc | exact HB | rewrite length_firstn; lia]. }
    transport_after_call rsegs m m' MUc WMc. clear MUc WMc MI. rename MIc into MI. rename ST' into ST.
    subst pre post.
    destruct (gnl_join_chunk m' kbs j wn (firstn (Z.to_nat wn) wbj) GL ltac:(lia) ltac:(lia)
                ltac:(rewrite length_firstn; lia) B1 DSTc B3 WA) as [NK LK1].
    set (kbs1 := upd_bytes kbs (Z.to_nat (4096 * j)) (firstn (Z.to_nat wn) wbj)) in NK, LK1.
    assert (G1 : rdn kbs1 262656 4 = j).
    { unfold kbs1. rewrite rdn_upd_out by (rewrite ?length_firstn; lia). exact GJ. }
    zstep.
    pose proof (u8arr_rd4 m' 203648 kbs1 466304 (Z_to_bv 64 466304) NK ltac:(lia) ltac:(lia) eq_refl) as RD.
    replace (466304 - 203648) with 262656 in RD by reflexivity. rewrite G1 in RD.
    zstep. rewrite sx32_wz by lia. unfold wz.
    zstep.
    pose proof (u8arr_store_ok_z m' 203648 kbs1 466304 4 NK ltac:(lia) ltac:(lia)) as HS.
    zstep. gnl_after_store NK LK1.
    zstep. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    zstep.
    match goal with H : u8arr _ ?mm 203648 ?kb |- _ =>
      pose proof (u8arr_store_ok_z mm 203648 kb (465792 + j * 8) 8 H ltac:(lia) ltac:(lia)) as HS2 end.
    zstep. gnl_after_store NK LK1.
    zstep.
    replace (465792 + j * 8 - 203648) with (262144 + 8 * j) in NK, LK1 by lia.
    eapply LK.
    refine (conj (ex_intro _ j0 (ex_intro _ mc (ex_intro _ kd (ex_intro _ atw SPL))))
              (conj (ex_intro _ wbj WB) (conj (ex_intro _ _ (conj WNC eq_refl)) (conj _ (conj NR (conj CIR _)))))).
    1: refine (conj FRS (conj ADV (conj CUR (conj IN (conj NK (conj _ (conj LA (conj MU (conj WM (conj MI ST)))))))))).
    1: (unfold kbs1; apply kgnl_queue; [exact GI | lia | lia | rewrite length_firstn; lia]).
    lia.
Qed.

Lemma kbytes_slice : forall m a (d : list byte) off len, bytes_at rsegs m a d -> 0 <= off -> 0 <= len ->
  off + len <= Z.of_nat (length d) -> bytes_at rsegs m (a + off) (slice d off len).
Proof.
  intros m a d off len H H0 H1 H2. unfold slice.
  rewrite <- (firstn_skipn (Z.to_nat off) d) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (a + Z.of_nat (Nat.min (Z.to_nat off) (length d))) with (a + off) in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat off) d)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(* a run of N bytes cut at k, and glued back *)
Lemma kcb_split : forall m A N j k, rw_cells rsegs m A [CB N j] -> (k <= N)%nat ->
  rw_cells rsegs m A [CB k (firstn k j)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB (N - k) (skipn k j)].
Proof.
  intros m A N j k C Hk. pose proof C as [[[Hl _] _] _]. cbn [cell_wf] in Hl.
  assert (C' : rw_cells rsegs m A ([CB k (firstn k j)] ++ [CB (N - k) (skipn k j)])).
  { apply (rw_cells_same_bytes m A [CB N j]); [exact C | | |].
    - cbn [app cells_wf cell_wf]. rewrite length_firstn, length_skipn. repeat split; try exact I; lia.
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. apply firstn_skipn.
    - cbn [app cells_size csize]. lia. }
  apply rw_cells_app in C'. destruct C' as [C1 C2]. split; [exact C1|].
  eapply rw_cells_at; [exact C2|]. cbn [cells_size csize]. lia.
Qed.

Lemma kcb_join : forall m A k j1 N2 j2,
  rw_cells rsegs m A [CB k j1] -> rw_cells rsegs m (A + Z.of_nat k) [CB N2 j2] ->
  rw_cells rsegs m A [CB (k + N2) (j1 ++ j2)].
Proof.
  intros m A k j1 N2 j2 C1 C2. pose proof C1 as [[[L1 _] _] _]. pose proof C2 as [[[L2 _] _] _].
  cbn [cell_wf] in L1, L2.
  assert (C : rw_cells rsegs m A ([CB k j1] ++ [CB N2 j2])).
  { apply rw_cells_app. split; [exact C1|]. eapply rw_cells_at; [exact C2|]. cbn [cells_size csize]. lia. }
  apply (rw_cells_same_bytes m A _ _ C).
  - cbn [cells_wf cell_wf]. rewrite length_app. repeat split; try exact I; lia.
  - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn [app cells_size csize]. lia.
Qed.

(* +0xd5c: the raw chunk of len input bytes: the cursor passes them, memcpy copies them to w.b, then +0xd88 *)
Lemma k_d5c : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la n ci mc kd atw j0 wbj w0 wfw pad len,
  kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) mc kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) [C8 w0; C4 wfw; CB 4 pad] -> w0 = Z_to_bv 64 0 ->
  kcore c m adv kbs j la -> 0 <= len <= 4096 -> len <= kWN c - adv -> (kWN c - adv = 0 -> len = 0) ->
  1 <= n <= 3 -> 0 <= ci < n -> 0 <= j <= ci ->
  k_latch_k c n ci ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) (Z_to_bv 64 ci)
             (Z_to_bv 64 (kWN c - adv)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (kWP c + adv)) (Z_to_bv 64 len)
             (Z_to_bv 64 (kSP c + -120)) (Z_to_bv 64 203648)
             (Z_to_bv 64 n) x23 (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14eec) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la n ci mc kd atw j0
    wbj w0 wfw pad len SPL WB WNC -> KC LR LA0 LZ NR CIR JR LK.
  kctx c HC. kcore_unpack KC. unfold kspill in SPL.
  zstep. zstep. zstep. zstep.
  replace (kWP c + adv + len) with (kWP c + (adv + len)) in * by lia.
  replace (kWN c - adv - len) with (kWN c - (adv + len)) in * by lia.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* no bytes left: len = 0, nothing copied *)
    assert (L0 : len = 0) by lia. subst len.
    eapply k_d88 with (adv := adv + 0); [exact HC | exact SPL | exact WB | exact WNC | kcore_pack | lia | lia | lia | lia | exact LK].
  - zstep. zstep. zstep.
    pose proof (kbytes_slice m (kWP c) (kf_d c) adv len IN ltac:(lia) ltac:(lia) ltac:(lia)) as SRC.
    destruct (kcb_split m (kSP c + -4216) (Z.to_nat 4096) wbj (Z.to_nat len) WB ltac:(lia)) as [WB1 WB2].
    clear WB.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply memcpy_holds with (src := slice (kf_d c) adv len) (junk := firstn (Z.to_nat len) wbj)
      | ]
    end.
    + rewrite unsigned_lit by lia. exact SRC.
    + rewrite slice_length by lia. rewrite unsigned_lit by lia. reflexivity.
    + rewrite !unsigned_lit by lia. exact WB1.
    + rewrite !unsigned_lit by lia. lia.
    + exact MI.
    + intros ms' PO. unfold memcpy_post in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                      MUc & WMc & MIc & DSTc & SRCc).
      repeat match goal with H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
        rewrite (unsigned_lit z) in H by lia end.
      match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      transport_after_call rsegs m m' MUc WMc. clear MUc WMc MI. rename MIc into MI.
      pose proof (kcb_join m' (kSP c + -4216) (Z.to_nat len) _ _ _ DSTc WB2) as WB.
      replace (Z.to_nat len + (Z.to_nat 4096 - Z.to_nat len))%nat with (Z.to_nat 4096) in WB by lia.
      clear DSTc WB2.
      zstep. zstep. rewrite Z.add_0_l.
      eapply k_d88 with (adv := adv + len); [exact HC | exact SPL | exact WB | exact WNC | kcore_pack | lia | lia | lia | lia | exact LK].
Qed.

(* +0xd44: want = lo + hi + 1 (the u16 % 4096 + 1 of nl_queue_raw), len = min(want, bytes left) *)
Lemma k_d44 : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x19 x20 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la n ci mc kd atw j0 wbj w0 wfw pad lo hi rem,
  kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) mc kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) [C8 w0; C4 wfw; CB 4 pad] -> w0 = Z_to_bv 64 0 ->
  kcore c m adv kbs j la -> 0 <= lo < 256 -> 0 <= hi <= 3840 -> rem = kWN c - adv ->
  1 <= n <= 3 -> 0 <= ci < n -> 0 <= j <= ci ->
  k_latch_k c n ci ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) x9
             (Z_to_bv 64 rem) (Z_to_bv 64 lo) (Z_to_bv 64 hi) x13 x14 x15 x16 x17
             (Z_to_bv 64 (kWP c + adv)) x19 x20 (Z_to_bv 64 203648)
             (Z_to_bv 64 n) x23 (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14ed4) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x19 x20 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la n ci mc kd atw
    j0 wbj w0 wfw pad lo hi rem SPL WB WNC E0 KC LOR HIR -> NR CIR JR LK.
  kctx c HC. pose proof KC as (_ & ADV & _). unfold kspill in SPL.
  zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - eapply k_d5c with (len := lo + hi + 1); [exact HC | exact SPL | exact WB | exact WNC | exact E0 | exact KC
      | lia | lia | lia | lia | lia | lia | exact LK].
  - zstep.
    eapply k_d5c with (len := kWN c - adv); [exact HC | exact SPL | exact WB | exact WNC | exact E0 | exact KC
      | lia | lia | lia | lia | lia | lia | exact LK].
Qed.

(* +0xcec: a raw chunk: memset(w), then the u16 length from up to two more input bytes *)
Lemma k_raw : forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) adv kbs j la n ci mc kd atw j0 wbj wnc,
  kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) mc kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) wnc -> cells_size wnc = 16%nat ->
  kcore c m (adv + 1) kbs j la -> 0 <= adv ->
  1 <= n <= 3 -> 0 <= ci < n -> 0 <= j <= ci ->
  k_latch_k c n ci ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) (Z_to_bv 64 (kWP c + adv))
             x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (kWP c + adv + 1)) (Z_to_bv 64 (kWN c - adv)) (Z_to_bv 64 (kWN c - adv + -1))
             (Z_to_bv 64 203648)
             (Z_to_bv 64 n) x23 (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14e7c) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c HC x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x27 x28 x29 x30 x31 m adv kbs j la n ci mc kd atw
    j0 wbj wnc SPL WB WNC WNS KC A0 NR CIR JR LK.
  kctx c HC. kcore_unpack KC. unfold kspill in SPL.
  zstep. zstep. zstep. zstep.
  memset_w c.
  zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* no length bytes *)
    zstep. zstep. zstep.
    replace (kWP c + adv + 1) with (kWP c + (adv + 1)) by lia.
    eapply k_d44 with (adv := adv + 1) (lo := 0) (hi := 0) (rem := 0); [exact HC | exact SPL | exact WB | exact WNC
      | reflexivity | kcore_pack | lia | lia | lia | lia | lia | lia | exact LK].
  - zstep. zstep. zstep. zstep.
    match goal with H : bytes_at _ ?mm (kWP c) (kf_d c) |- _ =>
      pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + adv + 1) _ H ltac:(lia) ltac:(lia) eq_refl) as RD1 end.
    replace (kWP c + adv + 1 - kWP c) with (adv + 1) in RD1 by lia.
    zstep. pose proof (rdn1_range (kf_d c) (adv + 1) ltac:(lia) ltac:(lia)) as BR1. rewrite zx8_wz by lia. unfold wz.
    zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + zstep.
      replace (kWP c + adv + 2) with (kWP c + (adv + 2)) in * by lia.
      eapply k_d44 with (adv := adv + 2) (hi := 0) (rem := kWN c - adv + -2); [exact HC | exact SPL | exact WB
        | exact WNC | reflexivity | kcore_pack | lia | lia | lia | lia | lia | lia | exact LK].
      replace (kWN c - (adv + 2)) with (kWN c - adv + -2) by lia. exact CUR.
    + zstep. zstep. zstep. zstep.
      match goal with H : bytes_at _ ?mm (kWP c) (kf_d c) |- _ =>
        pose proof (bytes_at_rd1 mm (kWP c) (kf_d c) (kWP c + adv + 2) _ H ltac:(lia) ltac:(lia) eq_refl) as RD2 end.
      replace (kWP c + adv + 2 - kWP c) with (adv + 2) in RD2 by lia.
      zstep. pose proof (rdn1_range (kf_d c) (adv + 2) ltac:(lia) ltac:(lia)) as BR2. rewrite zx8_wz by lia. unfold wz.
      zstep. zstep.
      rewrite (by_enum256 (fun b => Z.shiftr (Z.shiftl b 60 mod 18446744073709551616) 52) (fun b => b mod 16 * 256)
                 ltac:(vm_compute; reflexivity) _ BR2).
      zstep.
      replace (kWP c + adv + 3) with (kWP c + (adv + 3)) in * by lia.
      eapply k_d44 with (adv := adv + 3) (rem := kWN c - adv + -3); [exact HC | exact SPL | exact WB
        | exact WNC | reflexivity | kcore_pack | lia | lia | lia | lia | lia | lia | exact LK].
      replace (kWN c - (adv + 3)) with (kWN c - adv + -3) by lia. exact CUR.
Qed.
