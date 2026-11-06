(* reac-pw/fuzz_link, PLAIN build: kernel (0x14190-0x14faf), kinds 0 and 7 of msg_build (fuzz_link.c:179-220),
   from 0x1443c (+0x2ac) to the message latch 0x14de0 (+0xc50): `k_kind07 : k_kind07_stmt` (lib/Prog/kn_k0.v),
   with attr_text's contract as a Section hypothesis (attr_text has no walk yet), so after the Section
   k_kind07 : attr_text_contract -> k_kind07_stmt. memset is called by its released walk (memset_holds).

   The walk is cut at the join blocks of the CFG (link/kn/kernel-cfg.txt); each block is a lemma from its entry pc
   to the next join, over a state `kst` (the frame runs, the reply buffer, and `kfar`, the rest of kernel's state
   folded so that the frame stores of a block do not transport it one by one). A block opens `kst`, walks with the
   frame chunks only, and at its end carries `kfar` over the block's frame writes in one step (`kfar_frame`).
   Blocks, by entry: +0x2ac nl_begin (k2ac, k2e8, k340), +0x3a0 the 16-byte ifinfomsg (k3a0), +0x3e0 nattr
   (k3e0), the attribute loop +0x65c (k65c, by induction on the attributes left: kloop) with its latch +0x794
   (k794) and its cases (k760, k738, k6d4 .. k580, k77c, k424 .. k61c, all through attr_text at k790 or k580),
   +0x7a0 nl_end (k7a0), +0x7d0 kind 7 (k7d0), +0x804 nl_pad (k804), ending in k_after_msg (kfin).
   The byte-wide divisions (/5, /6, /11 by multiplication) are checked over the 256 byte values (by_enum256); the
   texts index (a >> 3) % 11 stays symbolic and texts[i] is read through ko_tt i. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0
  memset_c memset attr_text_c.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Two step-tactic helpers that only make a failing match fail sooner: an access at a literal offset is tried
      against a run of cells only when its offset in that run is in [0, 512) and fits in a run of known size. Every
      literal-offset access of this walk is into a run of at most 120 bytes; the frame has four runs at bases up
      to 4216 bytes apart, and building the unary offset of a miss took seconds a step.
   ========================================================================== *)

#[local] Ltac addr_diff E A ::=
  let d :=
    lazymatch E with
    | Z.add ?X ?c1 =>
        lazymatch A with
        | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
        | X => zlit c1
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    | _ =>
        lazymatch A with
        | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
        | E => constr:(0%Z)
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    end in
  lazymatch eval vm_compute in (Z.leb 0 d && Z.ltb d 512)%bool with true => d end.

#[local] Ltac split_for_access H segs m A cs kn n ::=
  let fits := eval vm_compute in (Nat.leb (kn + n) (cells_size cs)) in
  lazymatch fits with
  | true =>
    let ok := eval_cb_split_ok cs kn n in
    lazymatch ok with
    | true =>
        let cs2 := eval_cb_split cs kn n in
        lazymatch cs2 with
        | cs => idtac
        | _ => first [ apply (rw_cells_cb_split segs m A cs cs2 kn n) in H
                     | apply (ro_cells_cb_split segs m A cs cs2 kn n) in H ];
               [ | exact_no_check (@eq_refl bool true) | exact_no_check (@eq_refl (list cell) cs2) ]
        end
    end
  end.

(* ==========================================================================
   2. Runs of bytes cut in three and glued back (a call that writes a part of the reply buffer)
   ========================================================================== *)

Lemma cb_split3 : forall m A (N : nat) jb E L,
  rw_cells rsegs m A [CB N jb] -> A <= E -> 0 <= L -> E + L <= A + Z.of_nat N ->
  (exists j1, rw_cells rsegs m A [CB (Z.to_nat (E - A)) j1]) /\
  (exists j2, rw_cells rsegs m E [CB (Z.to_nat L) j2]) /\
  (exists j3, rw_cells rsegs m (E + L) [CB (Z.to_nat (A + Z.of_nat N - E - L)) j3]).
Proof.
  intros m A N jb E L H H1 H2 H3.
  pose proof H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  assert (C : rw_cells rsegs m A
                ([CB (Z.to_nat (E - A)) (firstn (Z.to_nat (E - A)) jb)] ++
                 [CB (Z.to_nat L) (firstn (Z.to_nat L) (skipn (Z.to_nat (E - A)) jb))] ++
                 [CB (Z.to_nat (A + Z.of_nat N - E - L)) (skipn (Z.to_nat L) (skipn (Z.to_nat (E - A)) jb))])).
  { apply (rw_cells_same_bytes m A [CB N jb]); [exact H | | | ].
    - cbn [app cells_wf cell_wf]. rewrite !length_firstn, !length_skipn. repeat split; lia.
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. rewrite firstn_skipn, firstn_skipn. reflexivity.
    - cbn [app cells_size csize]. lia. }
  apply rw_cells_app in C. destruct C as [C1 C23]. apply rw_cells_app in C23. destruct C23 as [C2 C3].
  cbn [cells_size csize] in C2, C3.
  split; [eexists; exact C1|]. split; [eexists; eapply rw_cells_at; [exact C2 | lia]|].
  eexists; eapply rw_cells_at; [exact C3 | lia].
Qed.

Lemma cb_split3n : forall m A (N : nat) jb E L,
  rw_cells rsegs m A [CB N jb] -> A <= E -> 0 <= L -> E + L <= A + Z.of_nat N ->
  exists (n1 n3 : nat) j1 j2 j3, rw_cells rsegs m A [CB n1 j1] /\ rw_cells rsegs m E [CB (Z.to_nat L) j2] /\
    rw_cells rsegs m (E + L) [CB n3 j3] /\ Z.of_nat n1 = E - A /\ Z.of_nat n3 = A + Z.of_nat N - E - L.
Proof.
  intros m A N jb E L H H1 H2 H3.
  destruct (cb_split3 m A N jb E L H H1 H2 H3) as ((j1 & C1) & (j2 & C2) & (j3 & C3)).
  exists (Z.to_nat (E - A)), (Z.to_nat (A + Z.of_nat N - E - L)), j1, j2, j3.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; lia.
Qed.

Lemma cb_glue3n : forall m A (N n1 n2 n3 : nat) E E' j1 j2 j3,
  rw_cells rsegs m A [CB n1 j1] -> rw_cells rsegs m E [CB n2 j2] -> rw_cells rsegs m E' [CB n3 j3] ->
  A + Z.of_nat n1 = E -> E + Z.of_nat n2 = E' -> (n1 + n2 + n3)%nat = N ->
  exists jb, rw_cells rsegs m A [CB N jb].
Proof.
  intros m A N n1 n2 n3 E E' j1 j2 j3 C1 C2 C3 H1 H2 H3.
  exists (j1 ++ j2 ++ j3).
  assert (C : rw_cells rsegs m A ([CB n1 j1] ++ [CB n2 j2] ++ [CB n3 j3])).
  { apply rw_cells_app. split; [exact C1|]. apply rw_cells_app. cbn [cells_size csize].
    split; [eapply rw_cells_at; [exact C2 | lia] | eapply rw_cells_at; [exact C3 | lia]]. }
  pose proof C1 as [[W1 _] _]. pose proof C2 as [[W2 _] _]. pose proof C3 as [[W3 _] _].
  cbn [cells_wf cell_wf] in W1, W2, W3. destruct W1 as [W1 _], W2 as [W2 _], W3 as [W3 _].
  apply (rw_cells_same_bytes m A _ _ C).
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite !length_app. lia.
  - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn [app cells_size csize]. lia.
Qed.

Lemma land_align : forall x, 0 <= x < 4104 -> Z.land x 4294967292 = x - x mod 4.
Proof.
  intros x Hx.
  assert (E : forallb (fun v => Z.land v 4294967292 =? v - v mod 4) (map Z.of_nat (seq 0 4104)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in E. apply Z.eqb_eq. apply E.
  replace x with (Z.of_nat (Z.to_nat x)) by lia. apply in_map. apply in_seq. lia.
Qed.

Lemma rw_cells_cb_eq : forall m A A' L L' (jb : list byte),
  rw_cells rsegs m A [CB (Z.to_nat L) jb] -> A = A' -> L = L' -> rw_cells rsegs m A' [CB (Z.to_nat L') jb].
Proof. intros; subst; assumption. Qed.

Ltac unsigned_all :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac unsigned_all_in H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) in H by lia end.

Lemma attr_text_post_ext : post_ext (fun regs m regs' m' => forall bs, nlw_at m (arg regs 0) bs ->
       exists bs', nlw_at m' (arg regs 0) bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs').
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H bs H1. unfold arg in *.
  rewrite <- (E1 (Z_to_bv 5 (10 + 0))) in H1 |- *. exact (H bs H1).
Qed.

(* bytes of the read-only image are not in a stack that `stk` gives (they are not writable) *)
Lemma ro_apart : forall m lo hi a n, mem_inv rsegs m -> stk rsegs m lo hi -> lo < hi -> 0 <= a -> 0 < n ->
  forallb (fun i => ro_addr rsegs (wa (a + Z.of_nat i))) (seq 0 (Z.to_nat n)) = true ->
  a + n <= lo \/ hi <= a.
Proof.
  intros m lo hi a n MI (L0 & H0 & ST) LH Ha Hn RO.
  destruct (Z_le_gt_dec (a + n) lo) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec hi a) as [H'|H']; [right; exact H'|].
  exfalso.
  destruct (ST (Z.max a lo) ltac:(lia)) as [WV _].
  rewrite forallb_forall in RO.
  assert (R : ro_addr rsegs (wa (a + Z.of_nat (Z.to_nat (Z.max a lo - a)))) = true)
    by (apply RO; apply in_seq; lia).
  replace (a + Z.of_nat (Z.to_nat (Z.max a lo - a))) with (Z.max a lo) in R by lia.
  destruct (m (wa (Z.max a lo))) as [b|] eqn:Em.
  - rewrite (MI _ b Em) in R. discriminate.
  - rewrite (wview_not_ro rsegs m _ WV Em) in R. discriminate.
Qed.

(* a stack range stays a stack range across a call that writes a run of it: the run is readable afterwards *)
Lemma stk_after_write : forall m m' lo hi A (n : nat) bs,
  stk rsegs m lo hi -> munch [(A, A + Z.of_nat n)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' A [CB n bs] -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi A n bs (H1 & H2 & H) MU WM [[Hwf B] _].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  destruct B as (B0 & B1 & B).
  split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  destruct (Z_lt_le_dec a A) as [L|L]; [|destruct (Z_lt_le_dec a (A + Z.of_nat n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - destruct (nth_error bs (Z.to_nat (a - A))) as [b'|] eqn:E.
    + exists b'. rewrite <- E. rewrite <- (B (Z.to_nat (a - A))) by lia. f_equal. f_equal. lia.
    + apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
Qed.

Lemma Z_mod_neg64 : forall e, -18446744073709551616 <= e < 0 ->
  e mod 18446744073709551616 = e + 18446744073709551616.
Proof.
  intros e H. replace e with ((e + 18446744073709551616) + (-1) * 18446744073709551616) at 1 by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* a branch condition on a 64-bit difference: the sign of the difference decides it; the branch where it cannot
   hold is closed at once *)
Ltac kmod K :=
  repeat match type of K with context [(?e mod 18446744073709551616)%Z] =>
    let H := fresh "SG" in
    destruct (Z_lt_le_dec e 0) as [H|H];
    [ rewrite (Z_mod_neg64 e) in K by lia | rewrite (Z.mod_small e) in K by lia ];
    try (exfalso; lia)
  end.

Ltac kif K := if_cases K; zify_cond K; kmod K.

(* disjunctions hidden from lia (it splits on every one in context): the walk keeps them only where a write
   needs one *)
Definition kh (P : Prop) : Prop := P.
Lemma kh_intro : forall P : Prop, P -> kh P. Proof. intros P H. exact H. Qed.
Ltac khide_all := repeat match goal with H : _ \/ _ |- _ => apply kh_intro in H end.

Lemma signed_lit64 : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. unfold bv_signed. rewrite unsigned_lit by lia. unfold bv_swrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_wrap 64 (z + 2 ^ 63)) with ((z + 2 ^ 63) mod 2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma idx11 : forall a, 0 <= a < 256 ->
  (Z.shiftr a 3 - (Z.shiftr (Z.shiftr a 3 * 1676976733973595602) 64 mod 18446744073709551616 * 11)
     mod 18446744073709551616) mod 18446744073709551616 = Z.shiftr a 3 mod 11.
Proof.
  intros a H.
  apply (by_enum256
    (fun a => (Z.shiftr a 3 - (Z.shiftr (Z.shiftr a 3 * 1676976733973595602) 64 mod 18446744073709551616 * 11)
                 mod 18446744073709551616) mod 18446744073709551616)
    (fun a => Z.shiftr a 3 mod 11)); [vm_compute; reflexivity | exact H].
Qed.

Lemma mod6 : forall a, 0 <= a < 256 ->
  a + (Z.shiftl (Z.shiftr (a * 3074457345618258603) 64 mod 18446744073709551616) 1 mod 18446744073709551616 -
       Z.shiftl (Z.shiftr (a * 3074457345618258603) 64 mod 18446744073709551616) 3 mod 18446744073709551616)
  = a mod 6.
Proof.
  intros a H.
  apply (by_enum256
    (fun a => a + (Z.shiftl (Z.shiftr (a * 3074457345618258603) 64 mod 18446744073709551616) 1 mod 18446744073709551616 -
       Z.shiftl (Z.shiftr (a * 3074457345618258603) 64 mod 18446744073709551616) 3 mod 18446744073709551616))
    (fun a => a mod 6)); [vm_compute; reflexivity | exact H].
Qed.

Lemma swrap32 : forall x, 0 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32 / 2) with 2147483648. change (2 ^ Z.of_N 32) with 4294967296.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma mod5 : forall b, 0 <= b < 256 ->
  (b - Z.shiftr (b * 3689348814741910324) 64 mod 18446744073709551616) mod 18446744073709551616 -
  Z.shiftl (Z.shiftr (b * 3689348814741910324) 64 mod 18446744073709551616) 2 mod 18446744073709551616 = b mod 5.
Proof.
  intros b H.
  apply (by_enum256
    (fun b => (b - Z.shiftr (b * 3689348814741910324) 64 mod 18446744073709551616) mod 18446744073709551616 -
      Z.shiftl (Z.shiftr (b * 3689348814741910324) 64 mod 18446744073709551616) 2 mod 18446744073709551616)
    (fun b => b mod 5)); [vm_compute; reflexivity | exact H].
Qed.

Lemma rd_all : forall m A l, bytes_at rsegs m A l -> ov_read_bytes rsegs m (wa A) (length l) = Some l.
Proof.
  intros m A l B.
  pose proof (bytes_at_ov_read rsegs m A l 0 (length l) B ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. change (skipn 0 l) with l in R.
  rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

(* ==========================================================================
   3. The blocks
   ========================================================================== *)

Section K07.
Hypothesis ATX : attr_text_contract.

Section Blk.
Variable c : kfix.
Hypothesis HC : kf_ok c.
Variables (k adv0 : Z) (kbs : list byte) (j n ci mc : Z).
Hypothesis HR : 1 <= n <= 3 /\ 0 <= ci < n /\ 0 <= j <= ci /\ 1 <= mc <= 5.
Hypothesis HG : kgnl c kbs j.
Hypothesis KAM : k_after_msg c k adv0 kbs j n ci mc.

(* the goal at a pc: every register but sp, gp, tp and s0 (the cursor) is a variable *)
Local Notation KE pc m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 :=
  (evt rsegs (kf_Q c)
     (MS (mkR x1 (Z_to_bv 64 (kSP c + -4336)) (kf_gp c) (kf_tp c) x5 x6 x7 (kf_a0 c) x9 x10 x11 x12 x13 x14 x15
              x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         (kf_F c) (Z_to_bv 64 pc) (kf_fc c) None m (seg_rom rsegs))).

(* kernel's state outside its frame (and its saved registers), which no block but the cursor reads touches *)
Definition kfar (m : word -> option byte) (adv : Z) (la : list byte) : Prop :=
  rw_cells rsegs m (kSP c + -104) (kfrs c) /\
  0 <= adv <= kWN c /\ adv0 <= adv /\
  rw_cells rsegs m (kCUR c) [C8 (Z_to_bv 64 (kWP c + adv)); C8 (Z_to_bv 64 (kWN c - adv))] /\
  bytes_at rsegs m (kWP c) (kf_d c) /\
  u8arr rsegs m 203648 kbs /\
  rw_cells rsegs m 476152 [CB (Z.to_nat 300) la; C1 (zb 0)] /\
  munch (kW c) (kf_m0 c) m /\ wmono rsegs (kf_m0 c) m.

(* the state inside a message of kind 0 / 7: the message starts at offset hd of the reply buffer *)
Definition kst (m : word -> option byte) (adv : Z) (la : list byte) (wn wf hd : Z) : Prop :=
  (exists j0 kd, kspill c m j0 (Z_to_bv 64 n) (Z_to_bv 64 ci) (Z_to_bv 64 mc) kd (Z_to_bv 64 hd)) /\
  kwbuf c m wn wf /\ kfar m adv la /\ mem_inv rsegs m /\ stk rsegs m (kf_lo c) (kSP c + -4336) /\
  0 <= hd <= 4096.

Lemma kst_intro : forall m adv la wn wf hd j0 kd wbj pad,
  rw_cells rsegs m (kSP c + -4336)
    [CB 16 j0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 203648); C8 (Z_to_bv 64 (kSP c + -120)); C8 (Z_to_bv 64 4112);
     C8 (Z_to_bv 64 465792); C8 (Z_to_bv 64 ci); C8 (Z_to_bv 64 mc); C8 kd; C8 (Z_to_bv 64 hd);
     C8 (Z_to_bv 64 4294967292); C8 (Z_to_bv 64 3074457345618258603); C8 (Z_to_bv 64 18446744073709547519);
     C8 (Z_to_bv 64 18446744073709547518)] ->
  rw_cells rsegs m (kSP c + -4216) [CB (Z.to_nat 4096) wbj] ->
  rw_cells rsegs m (kSP c + -120) [C8 (Z_to_bv 64 wn); C4 (Z_to_bv 64 wf); CB 4 pad] ->
  0 <= wn <= 4096 -> 0 <= wf <= 1 -> kfar m adv la -> mem_inv rsegs m ->
  stk rsegs m (kf_lo c) (kSP c + -4336) -> 0 <= hd <= 4096 ->
  kst m adv la wn wf hd.
Proof.
  intros m adv la wn wf hd j0 kd wbj pad SPL WB WNC WNR WFR KF MI ST HD.
  exact (conj (ex_intro _ j0 (ex_intro _ kd SPL))
          (conj (conj (ex_intro _ wbj WB) (conj (ex_intro _ pad WNC) (conj WNR WFR)))
          (conj KF (conj MI (conj ST HD))))).
Qed.

Lemma kst_msg : forall m adv la wn wf hd, kst m adv la wn wf hd ->
  kmsg_st c m adv kbs j la n ci mc wn wf /\ adv0 <= adv.
Proof.
  intros m adv la wn wf hd ((j0 & kd & SPL) & WBF & (FRS & ADV & A0 & CUR & IN & NK & LA & MU & WM) & MI & ST & HD).
  split; [|exact A0].
  destruct WBF as ((wbj & WB) & (pad & WNC) & WNR & WFR). destruct HR as (NR & CIR & JR & MCR).
  exact (kmsg_intro c m adv kbs j la n ci mc wn wf j0 kd (Z_to_bv 64 hd) wbj pad SPL WB WNC WNR WFR FRS ADV CUR IN
           NK HG LA MU WM MI ST NR CIR JR MCR).
Qed.

(* kfar does not see the writes of a block: they are all in [sp - 4416, sp - 104) (kernel's frame below the saved
   registers, and the callees' frames) *)
Lemma kfar_frame : forall m m' adv la,
  kfar m adv la -> munch [(kSP c + -4416, kSP c + -104)] m m' -> wmono rsegs m m' -> kfar m' adv la.
Proof.
  intros m m' adv la (FRS & ADV & A0 & CUR & IN & NK & LA & MU & WM) MUf WMf.
  pose proof (ko_lo c HC). pose proof (ko_k c HC). pose proof (ko_sp c HC).
  pose proof (ko_fg c HC). pose proof (ko_fla c HC). pose proof (ko_cf c HC). pose proof (ko_inl c HC).
  pose proof (ko_ia c HC) as KIA. unfold kapart in KIA.
  pose proof HG as (GL & _). unfold NK_SIZE in GL.
  unfold kfrs in *.
  split; [eapply rw_cells_transport; [exact FRS | exact MUf | exact WMf | cbn [disjoint_from cells_size csize]; lia]|].
  split; [exact ADV|]. split; [exact A0|].
  split; [eapply rw_cells_transport; [exact CUR | exact MUf | exact WMf | cbn [disjoint_from cells_size csize]; lia]|].
  split; [eapply bytes_at_transport; [exact IN | exact MUf | cbn [disjoint_from]; lia]|].
  split; [eapply u8arr_transport; [exact NK | exact MUf | exact WMf | cbn [disjoint_from]; lia]|].
  split; [eapply rw_cells_transport; [exact LA | exact MUf | exact WMf | cbn [disjoint_from cells_size csize]; lia]|].
  split.
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUf].
    unfold sub_fp, kW. cbn [outside]. intros x Hx. lia.
  - eapply wmono_trans; [exact WM | exact WMf].
Qed.

Lemma kfar_intro : forall m adv la,
  rw_cells rsegs m (kSP c + -104) (kfrs c) -> 0 <= adv <= kWN c -> adv0 <= adv ->
  rw_cells rsegs m (kCUR c) [C8 (Z_to_bv 64 (kWP c + adv)); C8 (Z_to_bv 64 (kWN c - adv))] ->
  bytes_at rsegs m (kWP c) (kf_d c) -> u8arr rsegs m 203648 kbs ->
  rw_cells rsegs m 476152 [CB (Z.to_nat 300) la; C1 (zb 0)] ->
  munch (kW c) (kf_m0 c) m -> wmono rsegs (kf_m0 c) m -> kfar m adv la.
Proof.
  intros m adv la FRS ADV A0 CUR IN NK LA MU WM.
  exact (conj FRS (conj ADV (conj A0 (conj CUR (conj IN (conj NK (conj LA (conj MU WM)))))))).
Qed.

(* kfar opened, with the facts lia needs to move its parts over a write outside the frame *)
Ltac kfar_open KF :=
  destruct KF as (FRS & ADV & A0 & CUR & IN & NK & LA & MU0 & WM0);
  pose proof (ko_fla c HC); pose proof (ko_cla c HC); pose proof (ko_fg c HC); pose proof (ko_cf c HC);
  pose proof (ko_cg c HC); pose proof (ko_inl c HC);
  let KIA := fresh "KIA" in pose proof (ko_ia c HC) as KIA; unfold kapart in KIA;
  destruct KIA as (?KIA & ?KIA & ?KIA & ?KIA);
  let GL := fresh "GL" in pose proof HG as (GL & _); unfold NK_SIZE in GL;
  pose proof (zr_word (kf_wn c)); pose proof (zr_word (kf_wp c)); pose proof (zr_word (kf_a0 c)); unfold inr64 in *;
  unfold kfrs in FRS; unfold kW in MU0.

(* open a block's state: the frame runs as hypotheses, kfar folded, and the block's footprint *)
Ltac kopen KS :=
  let j0 := fresh "j0" in let kd := fresh "kd" in let wbj := fresh "wbj" in let pad := fresh "pad" in
  destruct KS as ((j0 & kd & SPL) & ((wbj & WB) & (pad & WNC) & WNR & WFR) & KF & MI & ST & HDR);
  unfold kspill in SPL;
  lazymatch type of KF with kfar ?m _ _ =>
    pose proof (munch_refl [(kSP c + -4416, kSP c + -104)] m) as MUf;
    pose proof (wmono_refl rsegs m) as WMf end;
  pose proof (ko_lo c HC); pose proof (ko_k c HC); pose proof (ko_sp c HC);
  pose proof (zr_word (kf_sp c)) as RSP; unfold inr64 in RSP.

(* close it: kfar carried over the block's writes (or built by the block itself), and the state packed *)
Ltac kclose :=
  try lazymatch goal with KF : kfar ?ms _ _, MUf : munch _ ?ms ?me, WMf : wmono _ ?ms ?me |- _ =>
    let KF2 := fresh "KF" in
    pose proof (kfar_frame ms me _ _ KF MUf WMf) as KF2; clear KF MUf WMf end;
  let KS := fresh "KS" in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?me _) =>
    lazymatch goal with SPL : rw_cells _ me (kSP c + -4336) _, WB : rw_cells _ me (kSP c + -4216) _,
                        WNC : rw_cells _ me (kSP c + -120) _, KF2 : kfar me _ _, MI : mem_inv _ me,
                        ST : stk _ me _ _ |- _ =>
      pose proof (kst_intro _ _ _ _ _ _ _ _ _ _ SPL WB WNC ltac:(lia) ltac:(lia) KF2 MI ST ltac:(lia)) as KS;
      clear SPL WB WNC MI ST KF2
    end
  end.

(* the end of every path: the latch's state, through k_after_msg *)
Lemma kfin : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                     x30 x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 (kSP c + -4216) -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x26 = Z_to_bv 64 (-4093) ->
  KE 0x14de0 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS -> -> -> -> ->.
  destruct (kst_msg m adv la wn wf hd KS) as [KM A0].
  exact (KAM x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31 m adv la wn wf KM A0).
Qed.

Ltac kgo_tail := try (first [ eassumption | reflexivity | word_eq_tac | lia | (Z.div_mod_to_equations; lia) ]).
Ltac kgo L := kclose; eapply L; [ eassumption | .. ]; kgo_tail.
Ltac kgo_al L v := kclose; eapply L with (al := v); [ eassumption | .. ]; kgo_tail.
Ltac kgo_ns L v := kclose; eapply L with (ns := v); [ eassumption | .. ]; kgo_tail.

(* a run whose size is Z.to_nat e: the size as a variable with its value, so lia meets no Z.to_nat *)
Ltac gen_cb H :=
  lazymatch type of H with rw_cells _ _ _ [CB (Z.to_nat ?e) _] =>
    let nn := fresh "nn" in let En := fresh "En" in
    set (nn := Z.to_nat e) in H;
    assert (En : Z.of_nat nn = e) by (unfold nn; lia);
    clearbody nn
  end.

(* memset(E, _, L) on [E, E + L) inside the reply buffer: the buffer's run is cut in three around it, the call
   keeps the two outer pieces, and `kglue` puts the three back *)
Ltac kmemset E L :=
  let W1 := fresh "W1" in let W2 := fresh "W2" in let W3 := fresh "W3" in
  let E1 := fresh "E1" in let E3 := fresh "E3" in
  lazymatch goal with WB : rw_cells _ _ (kSP c + -4216) [CB _ _] |- _ =>
    destruct (cb_split3n _ _ _ _ E L WB ltac:(lia) ltac:(lia) ltac:(lia))
      as (? & ? & ? & ? & ? & W1 & W2 & W3 & E1 & E3);
    rewrite Z2Nat.id in E3 by lia;
    clear WB end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply memset_holds; [ unsigned_all; eapply rw_cells_cb_eq; [exact W2 | lia | lia] | eassumption ]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memset_post in PO; cbv beta in PO; unsigned_all_in PO; revert ms' PO;
      post_call rsegs mm ]
  end;
  lazymatch goal with H : rw_cells _ _ _ [CB (Z.to_nat _) (repeat _ _)] |- _ => gen_cb H end.

Ltac kglue :=
  match goal with
  | W1 : rw_cells _ ?mm (kSP c + -4216) [CB ?n1 _], W2 : rw_cells _ ?mm ?E2 [CB ?n2 _],
    W3 : rw_cells _ ?mm ?E3 [CB ?n3 _] |- _ =>
      let WB := fresh "WB" in
      destruct (cb_glue3n mm (kSP c + -4216) (Z.to_nat 4096) n1 n2 n3 E2 E3 _ _ _ W1 W2 W3
                  ltac:(lia) ltac:(lia) ltac:(lia)) as [? WB];
      clear W1 W2 W3
  end.

(* +0x804: nl_pad (kinds 0 and 7, and kind 7 when its end is not aligned): a2 = the aligned end al *)
Lemma k804 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                     x30 x31 : word) m adv la wn wf hd al,
  kst m adv la wn wf hd -> wn <= al <= wn + 3 -> al mod 4 = 0 ->
  x10 = Z_to_bv 64 wn -> x12 = Z_to_bv 64 al -> x19 = Z_to_bv 64 1 -> x21 = Z_to_bv 64 4097 ->
  x22 = Z_to_bv 64 k -> x24 = Z_to_bv 64 (kSP c + -120) -> x26 = Z_to_bv 64 (-4093) ->
  KE 0x14994 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd al KS AL1 AL2 -> -> -> -> -> -> ->.
  kopen KS.
  zstep. if_cases K; zify_cond K.
  - (* al < 4097: +0x814 *)
    zstep. if_cases K2; zify_cond K2.
    + (* al <> wn: +0x924, memset(w + wn, 0, al - wn) *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      kmemset (kSP c + -4216 + wn) (al - wn).
      zstep. zstep. zstep. zstep. zstep.
      kglue.
      kgo kfin.
    + (* al = wn: +0x818 *)
      zstep. zstep. zstep. zstep.
      kgo kfin.
  - (* full: +0x808 *)
    zstep. zstep. zstep.
    kgo kfin.
Qed.

(* +0x7d0: kind 7 with an aligned end puts one more byte and ends the message again; else nl_pad *)
Lemma k7d0 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                     x30 x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x10 = Z_to_bv 64 wn -> x11 = Z_to_bv 64 (hd + 4) -> x15 = Z_to_bv 64 hd -> x19 = Z_to_bv 64 1 ->
  x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k -> x24 = Z_to_bv 64 (kSP c + -120) ->
  x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  KE 0x14960 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS -> -> -> -> -> -> -> -> ->.
  kopen KS.
  assert (AL : Z.land (wn + 3) 4294967292 = wn + 3 - (wn + 3) mod 4) by (apply land_align; lia).
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K.
  - (* kind <> 7 *)
    kgo_al k804 (Z.land (wn + 3) 4294967292).
  - (* kind 7 *)
    zstep. if_cases K2; zify_cond K2.
    + kgo_al k804 (Z.land (wn + 3) 4294967292).
    + (* aligned end *)
      zstep. zstep. if_cases K3; zify_cond K3.
      * (* wn < 4096: +0x820 one byte more *)
        assert (W4 : wn < 4096) by (rewrite Z.shiftr_div_pow2 in K3 by lia; Z.div_mod_to_equations; lia).
        zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K4; zify_cond K4.
        -- kgo kfin.
        -- zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
           kgo kfin.
      * (* wn = 4096: +0x7f4 full *)
        zstep. zstep. zstep. if_cases K4; zify_cond K4.
        -- zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
           kgo kfin.
        -- zstep. kgo kfin.
Qed.

(* +0x7a0: nl_end, the message's length into its header when the header fits *)
Lemma k7a0 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                     x30 x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x10 = Z_to_bv 64 wn -> x19 = Z_to_bv 64 1 -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  KE 0x14930 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS -> -> -> -> -> -> ->.
  kopen KS.
  zstep. zstep. zstep. if_cases K; zify_cond K.
  - (* wn < hd + 4 *)
    kgo k7d0.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    kgo k7d0.
Qed.

(* ---- the attribute loop: its head +0x65c and its latch +0x794, with s4 = the attributes left ---- *)

Definition L65c (cnt : Z) : Prop :=
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x147ec m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.

Definition L794 (cnt : Z) : Prop :=
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x14924 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.

(* a string attr_text may take, in every memory kernel can be in: the C string at p, the slack strlen reads
   after it, and its place apart from kernel's frame and its callees' *)
Definition kstrp (la : list byte) (p : Z) (s : list byte) : Prop :=
  forall m', munch (kW c) (kf_m0 c) m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' 476152 [CB (Z.to_nat 300) la; C1 (zb 0)] ->
    p <> 0 /\ cstr_at m' p s /\
    (exists slack, bytes_at rsegs m' (p + Z.of_nat (length s) + 1) slack
                   /\ (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)) /\
    (p + Z.of_nat (length s) + 1 <= kSP c + -4416 \/ kSP c <= p).

Lemma kstr_txt : forall la p s slack, p <> 0 -> bytes_at rsegs (kf_m0 c) p (s ++ zb 0 :: slack) -> ~ In (zb 0) s ->
  (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
  kapart c p (Z.of_nat (length s) + 1 + Z.of_nat (length slack)) -> kstrp la p s.
Proof.
  intros la p s slack PNZ B NZ SLL KA m' MU MI LA. unfold kapart in KA.
  assert (B' : bytes_at rsegs m' p (s ++ zb 0 :: slack)).
  { eapply bytes_at_transport; [exact B | exact MU | unfold kW; cbn [disjoint_from]; rewrite length_app;
      cbn [length]; lia]. }
  replace (s ++ zb 0 :: slack) with ((s ++ [zb 0]) ++ slack) in B' by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B'. destruct B' as [B1 B2].
  split; [exact PNZ|]. split; [split; assumption|]. split.
  - exists slack. split; [|exact SLL]. rewrite length_app in B2. cbn [length] in B2.
    replace (p + Z.of_nat (length s + 1)) with (p + Z.of_nat (length s) + 1) in B2 by lia. exact B2.
  - lia.
Qed.

Lemma kstr_la : forall la, ~ In (zb 0) la -> length la = 300%nat -> kstrp la 476152 la.
Proof.
  intros la NZ LL m' MU MI LA.
  pose proof (ko_fla c HC). pose proof (ko_cla c HC). pose proof (ko_k c HC).
  destruct (ko_sl c HC) as (sl & SL & SLL).
  split; [lia|]. split; [split|].
  - pose proof LA as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - exact NZ.
  - rewrite LL. split.
    + exists sl. change (476152 + Z.of_nat 300 + 1) with 476453. split.
      * eapply bytes_at_transport; [exact SL | exact MU | unfold kW; cbn [disjoint_from]; rewrite SLL; lia].
      * rewrite SLL. Z.div_mod_to_equations; lia.
    + lia.
Qed.

Lemma kstr_empty : forall la, kstrp la 0x10368 [].
Proof.
  intros la m' MU MI LA.
  pose proof (ko_lo c HC). pose proof (ko_k c HC).
  assert (RA : 0x10368 + 8 <= kf_lo c \/ kSP c <= 0x10368)
    by (apply (ro_apart (kf_m0 c) (kf_lo c) (kSP c) 0x10368 8 (ko_mi c HC) (ko_st c HC));
        [lia | lia | lia | vm_compute; reflexivity]).
  split; [lia|]. split; [split|].
  - apply (ro_bytes_at rsegs m' 0x10368 ([] ++ [zb 0]) MI); [lia | cbn; lia | ].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - cbn. tauto.
  - split.
    + lazymatch eval vm_compute in (image_bytes rsegs 0x10369 7) with
      | Some ?l => exists l; split;
          [ apply (ro_bytes_at rsegs m' _ l MI); [cbn; lia | cbn; lia | ];
            apply ro_bytes_b_sound; vm_compute; reflexivity
          | cbn [length Z.of_nat]; Z.div_mod_to_equations; lia ]
      end.
    + cbn [length]. lia.
Qed.

Lemma kstr_x : forall la, kstrp la 0x10439 [zb 120].
Proof.
  intros la m' MU MI LA.
  pose proof (ko_lo c HC). pose proof (ko_k c HC).
  assert (RA : 0x10439 + 7 <= kf_lo c \/ kSP c <= 0x10439)
    by (apply (ro_apart (kf_m0 c) (kf_lo c) (kSP c) 0x10439 7 (ko_mi c HC) (ko_st c HC));
        [lia | lia | lia | vm_compute; reflexivity]).
  split; [lia|]. split; [split|].
  - apply (ro_bytes_at rsegs m' 0x10439 ([zb 120] ++ [zb 0]) MI); [lia | cbn; lia | ].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - cbn. intros [E|[]]. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate.
  - split.
    + lazymatch eval vm_compute in (image_bytes rsegs 0x1043b 5) with
      | Some ?l => exists l; split;
          [ apply (ro_bytes_at rsegs m' _ l MI); [cbn; lia | cbn; lia | ];
            apply ro_bytes_b_sound; vm_compute; reflexivity
          | cbn [length Z.of_nat]; Z.div_mod_to_equations; lia ]
      end.
    + cbn [length]. lia.
Qed.

(* at the jal to attr_text (a0 = w, a2 = p, kstrp la p s in context): the call by its contract, and the state
   back after it (the reply buffer from the contract's Post) *)
Ltac kattr :=
  lazymatch goal with KF : kfar ?m _ _, KSTR : kstrp _ ?p ?s, MI : mem_inv _ ?m,
                      WB : rw_cells _ ?m (kSP c + -4216) [CB _ ?wbj],
                      WNC : rw_cells _ ?m (kSP c + -120) [C8 (Z_to_bv 64 ?wn); C4 (Z_to_bv 64 ?wf); CB 4 ?pad],
                      WNR : 0 <= ?wn <= 4096, WFR : 0 <= ?wf <= 1 |- _ =>
    let LA0 := fresh "LA0" in let MU0 := fresh "MU0" in
    pose proof KF as (_ & _ & _ & _ & _ & _ & LA0 & MU0 & _);
    let PNZ := fresh "PNZ" in let CS := fresh "CS" in let slack := fresh "slack" in let SL := fresh "SL" in
    let SLL := fresh "SLL" in let PAP := fresh "PAP" in
    destruct (KSTR m MU0 MI LA0) as (PNZ & CS & (slack & SL & SLL) & PAP); clear LA0 MU0;
    let CS0 := fresh "CS0" in let CS1 := fresh "CS1" in
    pose proof CS as [[CS0 [CS1 _]] _]; rewrite length_app in CS1; cbn [length] in CS1;
    let WNC4 := fresh "WNC4" in
    assert (WNC4 : rw_cells rsegs m (kSP c + -4216 + 4096) [C8 (Z_to_bv 64 wn); C4 (Z_to_bv 64 wf); CB 4 pad])
      by (eapply rw_cells_at; [exact WNC | lia]);
    let bs := fresh "bs" in let NW := fresh "NW" in let NWF := fresh "NWF" in
    destruct (kw_nlw m (kSP c + -4216) wbj wn wf pad WB WNC4 WNR WFR) as (bs & NW & NWF & _ & _);
    clear WNC4;
    zstep;
    eapply (leaf_call _ _ _ _ _ ATX attr_text_post_ext (kf_Q c) (ko_qext c HC));
    [ cbv beta; exists bs, s; unfold apart_frame; rewrite mkR_a0, mkR_a2, mkR_sp; unsigned_all;
      refine (conj NW (conj NWF (conj PNZ (conj CS (conj (ex_intro _ slack (conj SL SLL)) (conj _ (conj _ _)))))));
      unfold NW_SIZE; lia
    | exact MI
    | unsigned_all; eassumption
    | unsigned_all; lia
    | unsigned_all; lia
    | let m3 := fresh "m" in let MUi := fresh "MUi" in let WMi := fresh "WMi" in let MIi := fresh "MIi" in
      let STi := fresh "STi" in let POi := fresh "POi" in
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? m3 MUi WMi MIi STi POi;
      cbv beta in POi, MUi; rewrite mkR_a0 in POi, MUi; unsigned_all_in POi; unsigned_all_in MUi;
      unsigned_all_in STi; unfold NW_SIZE in MUi;
      let bs' := fresh "bs" in let NW' := fresh "NW" in let NWF' := fresh "NWF" in
      destruct (POi bs NW) as (bs' & NW' & NWF' & _); clear POi NW NWF CS SL;
      transport_after_call rsegs m m3 MUi WMi;
      clear MUi WMi MI;
      try lazymatch goal with ST0 : stk _ m _ _ |- _ => clear ST0 end;
      let wbj' := fresh "wbj" in let pad' := fresh "pad" in let WB' := fresh "WB" in let WNC' := fresh "WNC" in
      destruct (nlw_kw m3 _ bs' NW' NWF') as (wbj' & pad' & WB' & WNC');
      let WNC2 := fresh "WNC" in
      pose proof (rw_cells_at _ _ (kSP c + -120) _ WNC' ltac:(lia)) as WNC2; clear WNC' NW';
      unfold nlw_wf, NL_CHUNK_MAX in NWF';
      rewrite ret_pc_even by (lia || reflexivity) ]
  end.

(* +0x790: attr_text(w, type, p, bare), back at the latch *)
Lemma k790 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd p s,
  kst m adv la wn wf hd -> kstrp la p s ->
  x10 = Z_to_bv 64 (kSP c + -4216) -> x12 = Z_to_bv 64 p ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x14920 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd p s KS KSTR -> -> -> -> -> -> -> -> -> ->.
  kopen KS.
  kattr.
  kgo K794.
Qed.

(* +0x760: attr_text(w, 20, s2, s1 & 0x80), case 0 and the empty input (s2 = "") *)
Lemma k760 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd p s,
  kst m adv la wn wf hd -> kstrp la p s -> x18 = Z_to_bv 64 p ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x148f0 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd p s KS KSTR -> -> -> -> -> -> -> -> ->.
  kopen KS.
  zstep. zstep. zstep. zstep. zstep.
  kgo (k790 cnt K794).
Qed.

(* +0x77c: attr_text(w, 3, "x", 0), case 4 *)
Lemma k77c : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x1490c m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd KS -> -> -> -> -> -> -> ->.
  pose proof (kstr_x la) as KSTR.
  kopen KS.
  zstep. zstep. zstep. zstep. zstep.
  kgo (k790 cnt K794).
Qed.

(* +0x738: memset(long_alias, 'a', 300), then attr_text(w, 20, long_alias, 0), case 1 *)
Lemma k738 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x148c8 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd KS -> -> -> -> -> -> -> ->.
  kopen KS. clear MUf WMf.
  kfar_open KF.
  destruct (proj1 (rw_cells_app m 476152 [CB (Z.to_nat 300) la] [C1 (zb 0)]) LA) as [LA1 LA2]. clear LA.
  cbn [cells_size csize] in LA2.
  pose proof (rw_cells_at _ _ 476452 _ LA2 ltac:(lia)) as LA3. clear LA2.
  pose proof (conj ST I) as STh. clear ST.
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut; [ eapply memset_holds; [ unsigned_all; exact LA1 | exact MI ] | ].
  intros ms' PO. unfold memset_post in PO. cbv beta in PO. unsigned_all_in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems & MUc
                  & WMc & MIc & LAc).
  subst ms'. clear LA1.
  pose proof (stk_after_write _ _ _ _ _ (Z.to_nat 300) _ (proj1 STh) MUc WMc LAc) as ST. clear STh.
  transport_after_call rsegs m m' MUc WMc.
  clear MUc WMc MI. rename MIc into MI.
  rewrite ret_pc_even by (lia || reflexivity).
  zstep. zstep. zstep. zstep. zstep.
  lazymatch type of LAc with rw_cells _ _ _ [CB _ ?l] =>
    assert (LAn : rw_cells rsegs m' 476152 [CB (Z.to_nat 300) l; C1 (zb 0)])
      by (apply (proj2 (rw_cells_app m' 476152 [CB (Z.to_nat 300) l] [C1 (zb 0)])); split;
          [exact LAc | eapply rw_cells_at; [exact LA3 | cbn [cells_size csize]; lia]]);
    assert (NZ : ~ In (zb 0) l)
      by (intros Hin; apply repeat_spec in Hin; apply (f_equal bv_unsigned) in Hin; vm_compute in Hin;
          discriminate);
    assert (LL : length l = 300%nat) by (rewrite repeat_length; reflexivity);
    pose proof (kstr_la l NZ LL) as KSTR
  end.
  clear LAc LA3.
  pose proof (kfar_intro _ _ _ FRS ADV A0 CUR IN NK LAn MU0 WM0) as KF.
  clear FRS CUR IN NK LAn MU0 WM0.
  kgo (k790 cnt K794).
Qed.

(* +0x580: attr_text(w, 1, t, a & 0x80) inside the nest, then nl_nest_end at ns *)
Lemma k580 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd p s ns,
  kst m adv la wn wf hd ->
  kstrp la p s -> 0 <= ns <= 4096 -> x18 = Z_to_bv 64 p -> x23 = Z_to_bv 64 ns ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x14710 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd p s ns KS KSTR NSR -> -> -> -> -> -> -> -> -> ->.
  kopen KS.
  zstep. zstep. zstep. zstep.
  kattr.
  zstep. zstep. zstep. kif K.
  - kgo K794.
  - zstep. zstep. zstep. zstep. zstep. zstep.
    kgo K794.
Qed.

(* +0x540: nl_pad after the "data" attribute *)
Lemma k540 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd p s ns,
  kst m adv la wn wf hd ->
  kstrp la p s -> 0 <= ns <= 4096 -> x10 = Z_to_bv 64 wn -> x18 = Z_to_bv 64 p -> x23 = Z_to_bv 64 ns ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x146d0 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd p s ns KS KSTR NSR -> -> -> -> -> -> -> -> -> -> ->.
  kopen KS.
  assert (AL1 : wn <= Z.land (wn + 3) 4294967292 <= wn + 3)
    by (rewrite land_align by lia; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep. zstep. kif K.
  - zstep. kif K2.
    + zstep. kgo_ns (k580 cnt K794) ns.
    + zstep. zstep. zstep. zstep. zstep.
      kmemset (kSP c + -4216 + wn) (Z.land (wn + 3) 4294967292 - wn).
      zstep. zstep. zstep. zstep.
      kglue.
      kgo_ns (k580 cnt K794) ns.
  - zstep. zstep. kgo_ns (k580 cnt K794) ns.
Qed.

(* +0x500: the 4 bytes "data" of the IFLA_INFO_DATA attribute *)
Lemma k500 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd p s ns,
  kst m adv la wn wf hd ->
  kstrp la p s -> 0 <= ns <= 4096 -> x10 = Z_to_bv 64 wn -> x18 = Z_to_bv 64 p -> x23 = Z_to_bv 64 ns ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x14690 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd p s ns KS KSTR NSR -> -> -> -> -> -> -> -> -> -> ->.
  kopen KS.
  zstep. zstep. zstep. kif K.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    kgo_ns (k540 cnt K794) ns.
  - zstep. zstep. kgo_ns (k540 cnt K794) ns.
Qed.

(* +0x490: after the nest header; a%6 = 3 puts the "data" attribute header first *)
Lemma k490 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd p s ns r,
  kst m adv la wn wf hd ->
  kstrp la p s -> 0 <= ns <= 4096 -> (r = 2 \/ r = 3) -> x10 = Z_to_bv 64 wn -> x11 = Z_to_bv 64 r ->
  x18 = Z_to_bv 64 p -> x23 = Z_to_bv 64 ns ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x14620 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd p s ns r KS KSTR NSR RR -> -> -> -> -> -> -> -> -> -> -> ->.
  kopen KS.
  zstep. zstep. kif K.
  - kgo_ns (k580 cnt K794) ns.
  - zstep. zstep. zstep. zstep. kif K2.
    + zstep. zstep. kgo_ns (k500 cnt K794) ns.
    + zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kif K3.
      * zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kgo_ns (k500 cnt K794) ns.
      * zstep. zstep. zstep. kgo_ns (k500 cnt K794) ns.
Qed.

(* +0x6d4: nl_nest(w, IFLA_LINKINFO) for a%6 in {2, 3} *)
Lemma k6d4 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd p s r,
  kst m adv la wn wf hd ->
  kstrp la p s -> (r = 2 \/ r = 3) -> x11 = Z_to_bv 64 r -> x18 = Z_to_bv 64 p ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x14864 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd p s r KS KSTR RR -> -> -> -> -> -> -> -> -> ->.
  kopen KS.
  zstep. zstep. zstep. zstep. zstep. zstep. kif K.
  - zstep. zstep. kgo_ns (k490 cnt K794) wn.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kif K2.
    + zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kgo_ns (k490 cnt K794) wn.
    + zstep. zstep. zstep. kgo_ns (k490 cnt K794) wn.
Qed.

(* +0x61c: nl_pad after the "abcd" attribute *)
Lemma k61c : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x10 = Z_to_bv 64 wn ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x147ac m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd KS -> -> -> -> -> -> -> -> ->.
  kopen KS.
  assert (AL1 : wn <= Z.land (wn + 3) 4294967292 <= wn + 3)
    by (rewrite land_align by lia; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep. zstep. kif K.
  - zstep. kif K2.
    + zstep. zstep. kgo K794.
    + zstep. zstep. zstep. zstep. zstep.
      kmemset (kSP c + -4216 + wn) (Z.land (wn + 3) 4294967292 - wn).
      zstep. zstep. zstep. zstep.
      kglue.
      kgo K794.
  - zstep. zstep. kgo K794.
Qed.

(* +0x5d8: the 4 bytes "abcd" of attribute 99 *)
Lemma k5d8 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x10 = Z_to_bv 64 wn ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x14768 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd KS -> -> -> -> -> -> -> -> ->.
  kopen KS.
  zstep. zstep. zstep. kif K.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    kgo (k61c cnt K794).
  - zstep. zstep. kgo (k61c cnt K794).
Qed.

(* +0x424: nl_attr_put(w, 99, "abcd", 4), a%6 = 5: its header *)
Lemma k424 : forall cnt, L794 cnt ->
  forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
          x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 cnt -> x21 = Z_to_bv 64 4097 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x145b4 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros cnt K794 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 m adv la wn wf hd KS  -> -> -> -> -> -> -> ->.
  kopen KS.
  zstep. zstep. zstep. zstep. zstep. kif K.
  - zstep. zstep. kgo (k5d8 cnt K794).
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kif K2.
    + zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kgo (k5d8 cnt K794).
    + zstep. zstep. zstep. kgo (k5d8 cnt K794).
Qed.

(* +0x65c: the loop head: the next byte a (or none), texts[(a >> 3) % 11], and the case a % 6 *)
Lemma k65c : forall cnt, L794 cnt -> L65c cnt.
Proof.
  intros cnt K794. unfold L65c.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS -> -> -> -> -> -> -> ->.
  kopen KS. clear MUf WMf. kfar_open KF.
  zstep. zstep. kif K.
  - (* no byte left: +0x720, s2 = "" *)
    zstep. zstep. zstep. zstep.
    pose proof (kfar_intro _ adv la FRS ADV A0 CUR IN NK LA MU0 WM0) as KF.
    clear FRS CUR IN NK LA MU0 WM0.
    pose proof (kstr_empty la) as KSTR.
    khide_all.
    kgo (k760 cnt K794).
  - (* +0x664: a = the next byte *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (bytes_at_rd1 _ (kWP c) (kf_d c) (kWP c + adv) (wa (kWP c + adv)) IN ltac:(lia) ltac:(lia) eq_refl)
      as HRB.
    replace (kWP c + adv - kWP c) with adv in HRB by lia.
    pose proof (rdn1_range (kf_d c) adv ltac:(lia) ltac:(lia)) as AR.
    replace (kWP c + adv + 1) with (kWP c + (adv + 1)) in CUR by lia.
    replace (kWN c - adv + -1) with (kWN c - (adv + 1)) in CUR by lia.
    assert (ADV' : 0 <= adv + 1 <= kWN c) by lia. assert (A0' : adv0 <= adv + 1) by lia.
    pose proof (kfar_intro _ (adv + 1) la FRS ADV' A0' CUR IN NK LA MU0 WM0) as KF.
    clear FRS CUR IN NK LA WM0 ADV A0 ADV' A0'.
    khide_all.
    zstep. clear HRB.
    rewrite zx8_wz by exact AR. unfold wz.
    set (a := rdn (kf_d c) adv 1) in *. clearbody a.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite idx11 by lia.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (Z.shiftr a 3) 11 ltac:(lia)) as IR.
    destruct (ko_tt c HC (Z.shiftr a 3 mod 11) IR) as (p & s & slack & U & PNZ & SB & SNZ & SLL & SLEN & SKA).
    assert (U' : bytes_at rsegs m (133104 + 8 * (Z.shiftr a 3 mod 11)) (le8 (wz p))).
    { pose proof (ko_ta c HC) as KTA. unfold kapart in KTA. unfold kh in *.
      eapply bytes_at_transport; [exact U | exact MU0 | cbn [disjoint_from]; rewrite length_le8; lia]. }
    clear MU0.
    pose proof (rd_all _ _ _ U') as HRT. rewrite length_le8 in HRT. clear U'.
    pose proof (kstr_txt la p s slack PNZ SB SNZ SLL SKA) as KSTR.
    pose proof SB as [SB0 [SB1 _]]. rewrite length_app in SB1. cbn [length] in SB1.
    clear U SB SNZ SLL SLEN SKA.
    zstep. zstep. clear HRT. unfold wz.
    zstep. zstep. zstep.
    rewrite mod6 by lia.
    pose proof (Z.mod_pos_bound a 6 ltac:(lia)) as R6.
    zstep. if_cases K6; unfold bv_lts in K6; rewrite (signed_lit64 1), (signed_lit64 (a mod 6)) in K6 by lia;
      zify_bool K6.
    + (* a % 6 <= 1: +0x730 *)
      zstep. kif K7.
      * (* 0: +0x760 *) kgo (k760 cnt K794).
      * zstep. kif K8.
        -- exfalso. lia.
        -- (* 1: +0x738 *) kgo (k738 cnt K794).
    + zstep. zstep. zstep. kif K9.
      * zstep. zstep. kif K10.
        -- (* 5: +0x424 *) kgo (k424 cnt K794).
        -- (* 4: +0x77c *) kgo (k77c cnt K794).
      * (* 2, 3: +0x6d4 *)
        assert (RR : a mod 6 = 2 \/ a mod 6 = 3) by lia.
        kgo (k6d4 cnt K794).
Qed.

Lemma k794 : forall cnt, 1 <= cnt <= 4 -> (1 <= cnt - 1 -> L65c (cnt - 1)) -> L794 cnt.
Proof.
  intros cnt CR IH. unfold L794.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS -> -> -> -> -> -> -> ->.
  kopen KS.
  zstep. rewrite swrap32 by lia. zstep. kif K.
  - assert (CR1 : 1 <= cnt - 1) by lia. pose proof (IH CR1) as IH1. unfold L65c in IH1.
    kgo IH1.
  - zstep. kgo k7a0.
Qed.

Lemma kloop : forall (nn : nat) cnt, cnt = Z.of_nat nn -> 1 <= cnt <= 4 -> L65c cnt.
Proof.
  induction nn as [|nn IH]; intros cnt E R; [lia|].
  apply k65c. apply k794; [lia|]. intros R'. apply (IH (cnt - 1)); lia.
Qed.

(* +0x3e0: s5 = 4097; nattr = (next byte) % 5, then the attribute loop or nl_end *)
Lemma k3e0 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                     x30 x31 : word) m adv la wn wf hd,
  kst m adv la wn wf hd ->
  x9 = Z_to_bv 64 (kWN c - adv) -> x10 = Z_to_bv 64 wn -> x19 = Z_to_bv 64 1 -> x22 = Z_to_bv 64 k ->
  x24 = Z_to_bv 64 (kSP c + -120) -> x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  x27 = Z_to_bv 64 (kSP c + -4216) ->
  KE 0x14570 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS -> -> -> -> -> -> -> ->.
  kopen KS. pose proof (zr_word (kf_wn c)) as RWN. unfold inr64 in RWN.
  pose proof KF as (_ & ADVp & _).
  zstep. zstep. zstep. kif K.
  - kgo k7a0.
  - clear MUf WMf ADVp. kfar_open KF.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    pose proof (bytes_at_rd1 _ (kWP c) (kf_d c) (kWP c + adv) (wa (kWP c + adv)) IN ltac:(lia) ltac:(lia) eq_refl)
      as HRB.
    replace (kWP c + adv - kWP c) with adv in HRB by lia.
    pose proof (rdn1_range (kf_d c) adv ltac:(lia) ltac:(lia)) as AR.
    replace (kWP c + adv + 1) with (kWP c + (adv + 1)) in CUR by lia.
    replace (kWN c - adv + -1) with (kWN c - (adv + 1)) in CUR by lia.
    assert (ADV' : 0 <= adv + 1 <= kWN c) by lia. assert (A0' : adv0 <= adv + 1) by lia.
    pose proof (kfar_intro _ (adv + 1) la FRS ADV' A0' CUR IN NK LA MU0 WM0) as KF.
    clear FRS CUR IN NK LA MU0 WM0 ADV A0 ADV' A0'.
    khide_all.
    zstep. clear HRB.
    rewrite zx8_wz by exact AR. unfold wz.
    set (b := rdn (kf_d c) adv 1) in *. clearbody b.
    zstep. zstep. zstep. zstep.
    rewrite mod5 by lia.
    pose proof (Z.mod_pos_bound b 5 ltac:(lia)) as R5.
    zstep. kif K2.
    + kgo k7a0.
    + zstep.
      pose proof (kloop (Z.to_nat (b mod 5)) (b mod 5) ltac:(lia) ltac:(lia)) as KL. unfold L65c in KL.
      kgo KL.
Qed.

Ltac kopen_pre KS A0 :=
  kmsg_unpack KS;
  let KF := fresh "KF" in
  lazymatch goal with FRS : rw_cells _ _ (kSP c + -104) _, ADV : 0 <= _ <= kWN c,
                      CUR : rw_cells _ _ (kCUR c) _, IN : bytes_at _ _ (kWP c) _, NK : u8arr _ _ 203648 _,
                      LA : rw_cells _ _ 476152 _, MU : munch _ (kf_m0 c) _, WM : wmono _ (kf_m0 c) _ |- _ =>
    pose proof (kfar_intro _ _ _ FRS ADV A0 CUR IN NK LA MU WM) as KF; clear FRS CUR IN NK LA MU WM end;
  lazymatch type of KF with kfar ?m _ _ =>
    pose proof (munch_refl [(kSP c + -4416, kSP c + -104)] m) as MUf;
    pose proof (wmono_refl rsegs m) as WMf end;
  pose proof (ko_lo c HC); pose proof (ko_k c HC); pose proof (ko_sp c HC);
  pose proof (zr_word (kf_sp c)) as RSP; unfold inr64 in RSP.

Ltac kgo_pre L v :=
  lazymatch goal with KF : kfar ?ms _ _, MUf : munch _ ?ms ?me, WMf : wmono _ ?ms ?me |- _ =>
    let KF2 := fresh "KF" in pose proof (kfar_frame ms me _ _ KF MUf WMf) as KF2; clear KF MUf WMf;
    destruct KF2 as (?FRS & ?ADV & ?A0 & ?CUR & ?IN & ?NK & ?LA & ?MU & ?WM) end;
  eapply L with (hd := v); [ kmsg_pack | .. ]; kgo_tail.
(* +0x3a0: the message start and kind into their spill slots, then the 16 bytes of ifinfomsg *)
Lemma k3a0 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                     x30 x31 : word) m adv la wn wf hd,
  kmsg_st c m adv kbs j la n ci mc wn wf -> adv0 <= adv -> 0 <= hd <= 4096 ->
  x9 = Z_to_bv 64 (kWN c - adv) -> x10 = Z_to_bv 64 wn -> x13 = Z_to_bv 64 hd -> x19 = Z_to_bv 64 1 ->
  x20 = Z_to_bv 64 (kSP c + -4216) -> x22 = Z_to_bv 64 k -> x24 = Z_to_bv 64 (kSP c + -120) ->
  x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  KE 0x14530 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS A0 HDR -> -> -> -> -> -> -> -> ->.
  kopen_pre KS A0.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. kif K.
  - zstep. zstep. zstep. zstep.
    kmemset (kSP c + -4216 + wn) 16.
    zstep. zstep. zstep.
    kglue.
    kgo k3e0.
  - zstep. zstep. kgo k3e0.
Qed.

(* +0x340: nlmsg_seq = 1 and nlmsg_pid = 0 *)
Lemma k340 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                     x30 x31 : word) m adv la wn wf hd,
  kmsg_st c m adv kbs j la n ci mc wn wf -> adv0 <= adv -> 0 <= hd <= 4096 ->
  x9 = Z_to_bv 64 (kWN c - adv) -> x10 = Z_to_bv 64 wn -> x13 = Z_to_bv 64 hd -> x19 = Z_to_bv 64 1 ->
  x20 = Z_to_bv 64 (kSP c + -4216) -> x22 = Z_to_bv 64 k -> x24 = Z_to_bv 64 (kSP c + -120) ->
  x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  KE 0x144d0 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS A0 HDR -> -> -> -> -> -> -> -> ->.
  kopen_pre KS A0.
  zstep. zstep. zstep. kif K.
  - zstep. zstep. kgo_pre k3a0 hd.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kif K2.
    + zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kgo_pre k3a0 hd.
    + zstep. zstep. kgo_pre k3a0 hd.
Qed.

(* +0x2e8: nlmsg_type = RTM_NEWLINK and nlmsg_flags = 0 *)
Lemma k2e8 : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
                     x30 x31 : word) m adv la wn wf hd,
  kmsg_st c m adv kbs j la n ci mc wn wf -> adv0 <= adv -> 0 <= hd <= 4096 ->
  x9 = Z_to_bv 64 (kWN c - adv) -> x10 = Z_to_bv 64 wn -> x13 = Z_to_bv 64 hd -> x19 = Z_to_bv 64 1 ->
  x20 = Z_to_bv 64 (kSP c + -4216) -> x22 = Z_to_bv 64 k -> x24 = Z_to_bv 64 (kSP c + -120) ->
  x25 = Z_to_bv 64 (kSP c + -4216 + hd) -> x26 = Z_to_bv 64 (-4093) ->
  KE 0x14478 m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf hd KS A0 HDR -> -> -> -> -> -> -> -> ->.
  kopen_pre KS A0.
  zstep. zstep. zstep. zstep. kif K.
  - zstep. zstep. kgo_pre k340 hd.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. kif K2.
    + zstep. zstep. zstep. zstep. zstep. zstep. kgo_pre k340 hd.
    + zstep. zstep. kgo_pre k340 hd.
Qed.

(* +0x2ac: kinds 0 and 7: nl_begin's length word (the message starts at the buffer's n) *)
Lemma k2ac : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
                     x29 x30 x31 : word) m adv la wn wf,
  kmsg_st c m adv kbs j la n ci mc wn wf -> adv0 <= adv ->
  x9 = Z_to_bv 64 (kWN c - adv) -> x19 = Z_to_bv 64 1 -> x20 = Z_to_bv 64 (kSP c + -4216) ->
  x22 = Z_to_bv 64 k -> x24 = Z_to_bv 64 (kSP c + -120) -> x26 = Z_to_bv 64 (-4093) ->
  KE 0x1443c m x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
     x31.
Proof.
  intros x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    m adv la wn wf KS A0 -> -> -> -> -> ->.
  kopen_pre KS A0.
  zstep. zstep. zstep. zstep. zstep. kif K.
  - zstep. zstep. zstep. zstep. zstep. zstep. zstep. kgo_pre k2e8 wn.
  - zstep. zstep. zstep. kgo_pre k2e8 wn.
Qed.

End Blk.

(* kinds 0 and 7, from 0x1443c to the latch 0x14de0 (lib/Prog/kn_k0.v k_kind07_stmt) *)
Lemma k_kind07 : k_kind07_stmt.
Proof.
  unfold k_kind07_stmt.
  intros c HC x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x18 x21 x23 x25 x27 x28 x29 x30 x31
    m adv kbs j la n ci mc k wn kd KS Hk Hkd KAM.
  pose proof KS as (_ & _ & (_ & _ & _ & _ & _ & GI & _) & NR & CIR & JR & MCR).
  eapply (k2ac c HC k adv kbs j n ci mc (conj NR (conj CIR (conj JR MCR))) GI KAM);
    [ exact KS | lia | reflexivity .. ].
Qed.

End K07.
