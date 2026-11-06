(* reac-pw/fuzz_link, PLAIN build: kernel (0x14190-0x14faf), part 0: the fixed context every block of the walk
   shares, and the epilogue.

   `kfix` holds the entry registers kernel saves, the entry memory, the cursor, the input bytes, the entry fake
   kernel and the goal Q; `kf_ok` holds what the walk uses of them. The blocks are lemmas over a `kfix`: each says
   that from its entry pc and the state it names, the machine reaches Q. Q itself enters only through the
   epilogue's continuation, so no block below the top theorem (lib/Prog/kernel.v) mentions kernel's Post.

   Frame: kernel's sp is SP - 4336 (SP = the entry sp). The frame is cut in four runs whose offsets the walk
   tactics read and write at literal offsets from their bases:
     [SP - 4336, SP - 4216)  the spill slots (0x00 .. 0x78 of kernel's sp)
     [SP - 4216, SP - 120)   w.b, the 4096 bytes of the reply buffer (written at computed offsets)
     [SP - 120,  SP - 104)   w.n, w.full and 4 bytes of padding
     [SP - 104,  SP)         the 13 saved registers (s11 .. s0, ra). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr.
Local Open Scope Z_scope.

Record kfix := KFix {
  kf_ra : word; kf_sp : word; kf_gp : word; kf_tp : word;
  kf_s0 : word; kf_s1 : word; kf_s2 : word; kf_s3 : word; kf_s4 : word; kf_s5 : word;
  kf_s6 : word; kf_s7 : word; kf_s8 : word; kf_s9 : word; kf_s10 : word; kf_s11 : word;
  kf_F : bvmap 5 word; kf_fc : bv 32; kf_m0 : word -> option byte; kf_lo : Z;
  kf_a0 : word;                   (* the cursor `in` *)
  kf_wp : word; kf_wn : word;     (* the cursor's two words at entry *)
  kf_d : list byte;               (* the wn input bytes at wp *)
  kf_kbs0 : list byte;            (* g_nl at entry *)
  kf_la0 : list byte;             (* long_alias's 300 bytes at entry *)
  kf_Q : machine_state -> Prop }.

Notation kSP c := (bv_unsigned (kf_sp c)).
Notation kCUR c := (bv_unsigned (kf_a0 c)).
Notation kWP c := (bv_unsigned (kf_wp c)).
Notation kWN c := (bv_unsigned (kf_wn c)).

(* the entry register map, up to its caller-saved registers *)
Definition kR0 (c : kfix) : bvmap 5 word :=
  let z := Z_to_bv 64 0 in
  mkR (kf_ra c) (kf_sp c) (kf_gp c) (kf_tp c) z z z (kf_s0 c) (kf_s1 c) z z z z z z z z
      (kf_s2 c) (kf_s3 c) (kf_s4 c) (kf_s5 c) (kf_s6 c) (kf_s7 c) (kf_s8 c) (kf_s9 c) (kf_s10 c) (kf_s11 c)
      z z z z.

(* the saved registers, as the prologue leaves them *)
Definition kfrs (c : kfix) : list cell :=
  [C8 (kf_s11 c); C8 (kf_s10 c); C8 (kf_s9 c); C8 (kf_s8 c); C8 (kf_s7 c); C8 (kf_s6 c); C8 (kf_s5 c);
   C8 (kf_s4 c); C8 (kf_s3 c); C8 (kf_s2 c); C8 (kf_s1 c); C8 (kf_s0 c); C8 (kf_ra c)].

(* kernel's writes: its frame and its callees' (K = 4416), g_nl up to `open`, long_alias, the cursor *)
Definition kW (c : kfix) : list ivl :=
  [(kSP c + -4416, kSP c); (203648, 466324); (476152, 476453); (kCUR c, kCUR c + 16)].

(* [a, a + n) is apart from every write of kernel (kernel_c.v `kernel_apart`) *)
Definition kapart (c : kfix) (a n : Z) : Prop :=
  (a + n <= kSP c + -4416 \/ kSP c <= a) /\ (a + n <= 203648 \/ 475640 <= a) /\
  (a + n <= 476152 \/ 476456 <= a) /\ (a + n <= kCUR c \/ kCUR c + 16 <= a).

(* g_nl while kernel runs: the bytes from `open` on are the entry's, the queue holds j chunks of at most 4096
   bytes, the cursor is 0 and the three errnos come from nl_errno's table *)
Definition kgnl (c : kfix) (kbs : list byte) (j : Z) : Prop :=
  Z.of_nat (length kbs) = NK_SIZE /\
  skipn (Z.to_nat 262676) kbs = skipn (Z.to_nat 262676) (kf_kbs0 c) /\
  rdn kbs 262656 4 = j /\ rdn kbs 262660 4 = 0 /\
  In (rdn kbs 262664 4) nl_errno_tab /\
  (rdn kbs 262668 4 = 0 \/ In (rdn kbs 262668 4) nl_errno_tab) /\
  (rdn kbs 262672 4 = 0 \/ In (rdn kbs 262672 4) nl_errno_tab) /\
  (forall i, 0 <= i < j -> 0 <= rdn kbs (262144 + 8 * i) 8 <= 4096).

(* what every block keeps: saved registers, the cursor after adv bytes, the input, g_nl, long_alias, and the
   frame below the spill slots *)
Definition kcore (c : kfix) (m : word -> option byte) (adv : Z) (kbs : list byte) (j : Z) (la : list byte) : Prop :=
  rw_cells rsegs m (kSP c + -104) (kfrs c) /\
  0 <= adv <= kWN c /\
  rw_cells rsegs m (kCUR c) [C8 (Z_to_bv 64 (kWP c + adv)); C8 (Z_to_bv 64 (kWN c - adv))] /\
  bytes_at rsegs m (kWP c) (kf_d c) /\
  u8arr rsegs m 203648 kbs /\ kgnl c kbs j /\
  rw_cells rsegs m 476152 [CB (Z.to_nat 300) la; C1 (zb 0)] /\
  munch (kW c) (kf_m0 c) m /\ wmono rsegs (kf_m0 c) m /\ mem_inv rsegs m /\
  stk rsegs m (kf_lo c) (kSP c + -4336).

(* the spill slots: sp+0x10 n, 0x18 g_nl, 0x20 &w.n, 0x28 sizeof w, 0x30 g_nl+0x40000, 0x38 the chunk index,
   0x40 the message count, 0x48 the message kind, 0x50 the message start, 0x58 the 4-byte mask, 0x60 the
   magic for /6, 0x68 -4097, 0x70 -4098 *)
Definition kspill (c : kfix) (m : word -> option byte) (j0 : list byte) (n ci mc kd atw : word) : Prop :=
  rw_cells rsegs m (kSP c + -4336)
    [CB 16 j0; C8 n; C8 (Z_to_bv 64 203648); C8 (Z_to_bv 64 (kSP c + -120)); C8 (Z_to_bv 64 4112);
     C8 (Z_to_bv 64 465792); C8 ci; C8 mc; C8 kd; C8 atw; C8 (Z_to_bv 64 4294967292);
     C8 (Z_to_bv 64 3074457345618258603); C8 (Z_to_bv 64 18446744073709547519);
     C8 (Z_to_bv 64 18446744073709547518)].

(* the reply buffer w = sp + 0x78: 4096 bytes b the walk forgets, then n, full and padding *)
Definition kwbuf (c : kfix) (m : word -> option byte) (wn wf : Z) : Prop :=
  (exists wbj, rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj]) /\
  (exists pad, rw_cells rsegs m (kSP c + -120) [C8 (Z_to_bv 64 wn); C4 (Z_to_bv 64 wf); CB 4 pad]) /\
  0 <= wn <= 4096 /\ 0 <= wf <= 1.

(* the state of one message loop of one chunk (msg path, 0x143e4 .. 0x14df4): n chunks asked, this is chunk ci,
   the operation asked mc messages; g_nl (kbs, j) is not touched while messages are built *)
Definition kmsg_st (c : kfix) (m : word -> option byte) (adv : Z) (kbs : list byte) (j : Z) (la : list byte)
    (n ci mc wn wf : Z) : Prop :=
  (exists j0 kd atw, kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) (Z_to_bv 64 mc) kd atw) /\
  kwbuf c m wn wf /\ kcore c m adv kbs j la /\
  1 <= n <= 3 /\ 0 <= ci < n /\ 0 <= j <= ci /\ 1 <= mc <= 5.

Lemma kmsg_intro : forall c m adv kbs j la n ci mc wn wf j0 kd atw wbj pad,
  kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) (Z_to_bv 64 mc) kd atw ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) [C8 (Z_to_bv 64 wn); C4 (Z_to_bv 64 wf); CB 4 pad] ->
  0 <= wn <= 4096 -> 0 <= wf <= 1 ->
  rw_cells rsegs m (kSP c + -104) (kfrs c) ->
  0 <= adv <= kWN c ->
  rw_cells rsegs m (kCUR c) [C8 (Z_to_bv 64 (kWP c + adv)); C8 (Z_to_bv 64 (kWN c - adv))] ->
  bytes_at rsegs m (kWP c) (kf_d c) ->
  u8arr rsegs m 203648 kbs -> kgnl c kbs j ->
  rw_cells rsegs m 476152 [CB (Z.to_nat 300) la; C1 (zb 0)] ->
  munch (kW c) (kf_m0 c) m -> wmono rsegs (kf_m0 c) m -> mem_inv rsegs m ->
  stk rsegs m (kf_lo c) (kSP c + -4336) ->
  1 <= n <= 3 -> 0 <= ci < n -> 0 <= j <= ci -> 1 <= mc <= 5 ->
  kmsg_st c m adv kbs j la n ci mc wn wf.
Proof.
  intros c m adv kbs j la n ci mc wn wf j0 kd atw wbj pad SPL WB WNC WNR WFR FRS ADV CUR IN NK GI LA MU WM MI ST
    NR CIR JR MCR.
  exact (conj (ex_intro _ j0 (ex_intro _ kd (ex_intro _ atw SPL)))
          (conj (conj (ex_intro _ wbj WB) (conj (ex_intro _ pad WNC) (conj WNR WFR)))
          (conj (conj FRS (conj ADV (conj CUR (conj IN (conj NK (conj GI (conj LA (conj MU (conj WM (conj MI ST))))))))))
          (conj NR (conj CIR (conj JR MCR)))))).
Qed.

(* kmsg_st as named hypotheses the step tactics read and write *)
Ltac kmsg_unpack H :=
  let j0 := fresh "j0" in let kd := fresh "kd" in let atw := fresh "atw" in let wbj := fresh "wbj" in
  let pad := fresh "pad" in
  destruct H as ((j0 & kd & atw & SPL) & ((wbj & WB) & (pad & WNC) & WNR & WFR) &
                 (FRS & ADV & CUR & IN & NK & GI & LA & MU & WM & MI & ST) & NR & CIR & JR & MCR);
  unfold kspill in SPL; unfold kfrs in FRS; unfold kW in MU.

(* ... and back: every piece by the hypothesis of the same shape, every range by lia *)
Ltac kmsg_pack :=
  eapply kmsg_intro; first [eassumption | lia | idtac].

(* what the walk takes from kernel's Pre, and what Q needs at the return *)
Record kf_ok (c : kfix) : Prop := KOk {
  ko_lo : 0 <= kf_lo c;
  ko_k : kf_lo c + 4416 <= kSP c;
  ko_sp : kSP c < 2 ^ 63;
  ko_fg : kSP c <= 203648 \/ 475640 <= kSP c + -4416;
  ko_fla : kSP c <= 476152 \/ 476456 <= kSP c + -4416;
  ko_cg : kCUR c + 16 <= 203648 \/ 475640 <= kCUR c;
  ko_cf : kCUR c + 16 <= kSP c + -4416 \/ kSP c <= kCUR c;
  ko_cla : kCUR c + 16 <= 476152 \/ 476456 <= kCUR c;
  ko_in : bytes_at rsegs (kf_m0 c) (kWP c) (kf_d c);
  ko_inl : Z.of_nat (length (kf_d c)) = kWN c;
  ko_ia : kapart c (kWP c) (kWN c);
  ko_nk : nlk_at (kf_m0 c) (kf_kbs0 c);
  ko_wf : nlk_wf (kf_kbs0 c);
  ko_cu : rw_cells rsegs (kf_m0 c) (kCUR c) [C8 (kf_wp c); C8 (kf_wn c)];
  ko_la : rw_cells rsegs (kf_m0 c) 476152 [CB (Z.to_nat 300) (kf_la0 c); C1 (zb 0)];
  ko_sl : exists sl, bytes_at rsegs (kf_m0 c) 476453 sl /\ length sl = 3%nat;
  ko_ta : kapart c 0x207f0 88;
  ko_tt : forall i, 0 <= i < 11 -> exists p s slack,
            u64_at (kf_m0 c) (0x207f0 + 8 * i) p /\ p <> 0
            /\ bytes_at rsegs (kf_m0 c) p (s ++ zb 0 :: slack) /\ ~ In (zb 0) s
            /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
            /\ Z.of_nat (length s) < 4096
            /\ kapart c p (Z.of_nat (length s) + 1 + Z.of_nat (length slack));
  ko_mi : mem_inv rsegs (kf_m0 c);
  ko_st : stk rsegs (kf_m0 c) (kf_lo c) (kSP c);
  ko_qext : q_ext (kf_Q c);
  ko_fin : forall R' m' kbs' j adv la,
    regs_preserved (kR0 c) R' -> munch (kW c) (kf_m0 c) m' -> wmono rsegs (kf_m0 c) m' -> mem_inv rsegs m' ->
    stk rsegs m' (kf_lo c) (kSP c) -> u8arr rsegs m' 203648 kbs' -> kgnl c kbs' j -> 0 <= j <= 3 ->
    0 <= adv <= kWN c ->
    rw_cells rsegs m' (kCUR c) [C8 (Z_to_bv 64 (kWP c + adv)); C8 (Z_to_bv 64 (kWN c - adv))] ->
    rw_cells rsegs m' 476152 [CB (Z.to_nat 300) la; C1 (zb 0)] ->
    kf_Q c (MS R' (kf_F c) (ret_pc (kf_ra c)) (kf_fc c) None m' (seg_rom rsegs)) }.

(* ==========================================================================
   The interfaces of the message blocks (proved in kn_k07.v and kn_kmsg.v)
   ========================================================================== *)

(* the state at 0x14de0 (+0xc50), after one message: the shape every message kind ends in *)
Definition k_after_msg (c : kfix) (k : Z) (adv : Z) (kbs : list byte) (j : Z) (n ci mc : Z) : Prop :=
  forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y23 y25 y27 y28 y29 y30 y31 : word)
         (m' : word -> option byte) (adv' : Z) (la' : list byte) (wn' wf' : Z),
    kmsg_st c m' adv' kbs j la' n ci mc wn' wf' -> adv <= adv' ->
    evt rsegs (kf_Q c)
      (MS (mkR y1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) y5 y6 y7 (kf_a0 c) y9 y10 y11 y12 y13 y14 y15 y16
               y17 y18 (Z_to_bv 64 1) (Z_to_bv 64 (kSP c + -4216)) y21 (Z_to_bv 64 k) y23
               (Z_to_bv 64 (kSP c + -120)) y25 (Z_to_bv 64 (-4093)) y27 y28 y29 y30 y31)
          (kf_F c) (Z_to_bv 64 0x14de0) (kf_fc c) None m' (seg_rom rsegs)).

(* kinds 0 and 7, from 0x1443c (+0x2ac): the cursor has given the kind byte (or was empty), s1 holds the bytes
   left, a4 the kind % 8 *)
Definition k_kind07_stmt : Prop :=
  forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (adv : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn kd : Z),
  kmsg_st c m adv kbs j la n ci mc wn 0 -> 0 <= k < mc -> (kd = 0 \/ kd = 7) ->
  k_after_msg c k adv kbs j n ci mc ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) (Z_to_bv 64 (kWN c - adv))
             x10 x11 x12 x13 (Z_to_bv 64 kd) x15 x16 x17 x18 (Z_to_bv 64 1) (Z_to_bv 64 (kSP c + -4216)) x21
             (Z_to_bv 64 k) x23 (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x1443c) (kf_fc c) None m (seg_rom rsegs)).

(* the message loop of one chunk, from its head 0x143e4 (+0x254) to 0x14df4 (+0xc64) *)
Definition k_msgloop_stmt : Prop :=
  forall c, kf_ok c ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (adv : Z) (kbs : list byte) (j : Z) (la : list byte) (n ci mc k wn : Z),
  kmsg_st c m adv kbs j la n ci mc wn 0 -> 0 <= k < mc ->
  (forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y27 y28 y29 y30 y31 : word)
          (m' : word -> option byte) (adv' : Z) (la' : list byte) (wn' wf' : Z),
     kmsg_st c m' adv' kbs j la' n ci mc wn' wf' -> adv <= adv' ->
     evt rsegs (kf_Q c)
       (MS (mkR y1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) y5 y6 y7 (kf_a0 c) y9 y10 y11 y12 y13 y14 y15
                y16 y17 y18 y19 y20 y21 y22 y23 (Z_to_bv 64 (kSP c + -120)) y25 (Z_to_bv 64 (-4093)) y27 y28 y29 y30 y31)
           (kf_F c) (Z_to_bv 64 0x14df4) (kf_fc c) None m' (seg_rom rsegs))) ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) x9 x10 x11 x12 x13 x14 x15
             x16 x17 x18 (Z_to_bv 64 1) (Z_to_bv 64 (kSP c + -4216)) x21 (Z_to_bv 64 k) x23
             (Z_to_bv 64 (kSP c + -120)) x25 (Z_to_bv 64 (-4093)) x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x143e4) (kf_fc c) None m (seg_rom rsegs)).

(* the facts of kf_ok the step tactics need in context, as numbers lia reads *)
Ltac kctx c HC :=
  pose proof (ko_lo c HC); pose proof (ko_k c HC); pose proof (ko_sp c HC);
  pose proof (ko_fg c HC); pose proof (ko_fla c HC); pose proof (ko_cg c HC); pose proof (ko_cf c HC);
  pose proof (ko_cla c HC); pose proof (ko_inl c HC); pose proof (ko_ia c HC) as KIA; unfold kapart in KIA;
  pose proof (zr_word (kf_sp c)); pose proof (zr_word (kf_a0 c)); pose proof (zr_word (kf_wp c));
  pose proof (zr_word (kf_wn c)); unfold inr64 in *;
  pose proof (bytes_at_bound rsegs _ _ _ (ko_in c HC)).

Lemma stk_release_z : forall m lo A cs B,
  stk rsegs m lo A -> rw_cells rsegs m A cs -> lo <= A -> A + Z.of_nat (cells_size cs) = B -> stk rsegs m lo B.
Proof. intros m lo A cs B ST C H E. subst B. apply stk_release; assumption. Qed.

(* The epilogue, 0x14f6c (+0xddc): from any state whose frame is the four runs above, kernel returns with every
   callee-saved register restored and the frame given back to `stk`; K says what Q needs of that. *)
Lemma k_exit : forall c,
  forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (m : word -> option byte) (spl : list cell) (wbj : list byte) (wnc : list cell),
  0 <= kf_lo c -> kf_lo c + 4416 <= kSP c -> kSP c < 2 ^ 63 ->
  stk rsegs m (kf_lo c) (kSP c + -4336) ->
  rw_cells rsegs m (kSP c + -4336) spl -> cells_size spl = 120%nat ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) wnc -> cells_size wnc = 16%nat ->
  rw_cells rsegs m (kSP c + -104) (kfrs c) ->
  (forall R', regs_preserved (kR0 c) R' -> stk rsegs m (kf_lo c) (kSP c) ->
     kf_Q c (MS R' (kf_F c) (ret_pc (kf_ra c)) (kf_fc c) None m (seg_rom rsegs))) ->
  evt rsegs (kf_Q c)
    (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        (kf_F c) (Z_to_bv 64 0x14f6c) (kf_fc c) None m (seg_rom rsegs)).
Proof.
  intros c x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m spl wbj wnc L0 L1 L2 ST SPL LS WB WNC LW FRS FIN.
  unfold kfrs in *.
  pose proof (zr_word (kf_sp c)) as Rsp. unfold inr64 in Rsp.
  do 17 zstep.
  assert (S1 : stk rsegs m (kf_lo c) (bv_unsigned (kf_sp c) + -4216))
    by (eapply stk_release_z; [exact ST | exact SPL | lia | rewrite LS; lia]).
  assert (S2 : stk rsegs m (kf_lo c) (bv_unsigned (kf_sp c) + -120))
    by (eapply stk_release_z; [exact S1 | exact WB | lia | cbn [cells_size csize]; lia]).
  assert (S3 : stk rsegs m (kf_lo c) (bv_unsigned (kf_sp c) + -104))
    by (eapply stk_release_z; [exact S2 | exact WNC | lia | rewrite LW; lia]).
  assert (S4 : stk rsegs m (kf_lo c) (bv_unsigned (kf_sp c)))
    by (eapply stk_release_z; [exact S3 | exact FRS | lia | cbn [cells_size csize]; lia]).
  apply evt_done. apply FIN; [unfold kR0; solve_rp | exact S4].
Qed.
