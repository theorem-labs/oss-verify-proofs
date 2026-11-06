(** strip (UBSan build, 0x15028, 176 bytes): proof of
    [strip_contract] (U/Prog/strip_c.v). Written new. A leaf: no frame, no call. The
    plain build has no strip function (clang inlines it into m_file) and the contract family states no plain
    contract, so there is no plain walk.

    Code:
      0x15028 or a2,a0,a1; andi a2,a2,7; 0x15030 bnez a2 -> TRAP        (both cells 8-aligned: not taken)
      0x15034 ld a3,0(a0); ld a2,0(a1); 0x1503c bgeu a3,a2 -> RET        (s0 = e0: the empty range)
      0x15040 a4 = 32; a5 = 0x100002200; a6 = 1; a7 = a3
      FWD  0x15058 beqz a3 -> TRAP (s > 0); lbu t0,0(a3); 0x15060 bltu a4,t0 -> BACK (above 32: not blank)
           srl t0,a5,t0; andi t0,t0,1; 0x1506c beqz t0 -> BACK (bit clear: not blank)
           a7 += 1; 0x15074 bgeu a6,a7 -> TRAP (s + 1 >= 2); a3 += 1; sd a3,0(a0); ld a2,0(a1)
           0x15084 bltu a3,a2 -> FWD; 0x15088 j RET                      (every byte blank)
      BACK 0x1508c beq a2,1 -> TRAP (e >= 2); lbu a3,-1(a2); 0x1509c bltu 32,a3 -> RET; a4 = 0x100002200
           srl a3,a4,a3; andi a3,a3,1; 0x150b4 beqz a3 -> RET; 0x150bc bltu a2,2 -> TRAP (e >= 2)
           a2 -= 1; sd a2,0(a1); ld a3,0(a0); 0x150cc bltu a3,a2 -> BACK  (always: s's byte is not blank)
      RET  0x150d0 ret.  TRAP 0x150d4 unimp
    The blank test (byte <= 32 and bit byte of 0x100002200 set) is SegModel.blank ([sp_blank_bit]). The forward loop
    leaves k = strip_lead (zs l) ([lead_exit], [lead_all]); the back loop then leaves j = strip_trail (zs l)
    ([trail_exit]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strip_c.
Import ListNotations.
Open Scope Z_scope.

(** ** The blank test as compiled *)
(** For a byte x <= 32, bit x of 0x100002200 (bits 9, 13, 32: tab, CR, space) is blank x. *)
Lemma sp_blank_bit : forall x, 0 <= x <= 32 ->
  Z.land (Z.shiftr 4294976000 x) 1 = if blank x then 1 else 0.
Proof.
  intros x Hx.
  assert (E : exists n, (n <= 32)%nat /\ x = Z.of_nat n) by (exists (Z.to_nat x); split; lia).
  destruct E as (n & Hn & ->).
  do 33 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma blank_gt : forall x, 32 < x -> blank x = false.
Proof.
  intros x Hx. unfold blank.
  destruct (Z.eqb_spec x 32), (Z.eqb_spec x 9), (Z.eqb_spec x 13); try lia; reflexivity.
Qed.

(** ** Lists *)
Lemma length_zs : forall bs, length (zs bs) = length bs.
Proof. intros bs. unfold zs. apply length_map. Qed.

Lemma zs_nth : forall (bs : list byte) i x, nth_error bs i = Some x -> nth i (zs bs) 0 = bv_unsigned x.
Proof.
  unfold zs. induction bs as [|y bs IH]; intros [|i] x H; cbn [nth_error] in H; try discriminate.
  - injection H as E. subst. reflexivity.
  - cbn [map nth]. apply IH. exact H.
Qed.

Lemma nth_skipn_z : forall k (d : list Z) i, nth i (skipn k d) 0 = nth (k + i) d 0.
Proof.
  induction k as [|k IH]; intros d i; [reflexivity|].
  destruct d as [|c r]; cbn [skipn Nat.add].
  - destruct i; reflexivity.
  - cbn [nth]. apply IH.
Qed.

(** k leading blanks, then a byte that is not blank. *)
Lemma lead_exit : forall (d : list Z) k, (k < length d)%nat ->
  (forall i, (i < k)%nat -> blank (nth i d 0) = true) -> blank (nth k d 0) = false ->
  length (takewhile blank d) = k /\ dropwhile blank d = skipn k d.
Proof.
  induction d as [|c r IH]; intros k Hk HB HN; cbn [length] in Hk; [lia|].
  destruct k as [|k].
  - cbn [nth] in HN. cbn [takewhile dropwhile skipn]. rewrite HN. split; reflexivity.
  - assert (Hc : blank c = true) by exact (HB 0%nat ltac:(lia)).
    cbn [takewhile dropwhile skipn]. rewrite Hc. cbn [length].
    destruct (IH k ltac:(lia) (fun i Hi => HB (S i) ltac:(lia)) HN) as [A B].
    split; [lia | exact B].
Qed.

(** Every byte blank. *)
Lemma lead_all : forall (d : list Z),
  (forall i, (i < length d)%nat -> blank (nth i d 0) = true) ->
  length (takewhile blank d) = length d /\ dropwhile blank d = [].
Proof.
  induction d as [|c r IH]; intros HB; [split; reflexivity|].
  assert (Hc : blank c = true) by exact (HB 0%nat ltac:(cbn [length]; lia)).
  cbn [takewhile dropwhile length]. rewrite Hc. cbn [length].
  destruct (IH (fun i Hi => HB (S i) ltac:(cbn [length]; lia))) as [A B].
  split; [lia | exact B].
Qed.

(** j trailing blanks, before them a byte that is not blank. *)
Lemma trail_exit : forall (r : list Z) j, (j < length r)%nat ->
  (forall i, (length r - j <= i < length r)%nat -> blank (nth i r 0) = true) ->
  blank (nth (length r - S j) r 0) = false ->
  length (takewhile blank (rev r)) = j.
Proof.
  intros r j Hj HB HN.
  assert (H1 : (j < length (rev r))%nat) by (rewrite length_rev; exact Hj).
  assert (H2 : forall i, (i < j)%nat -> blank (nth i (rev r) 0) = true).
  { intros i Hi. rewrite rev_nth by lia. apply HB. lia. }
  assert (H3 : blank (nth j (rev r) 0) = false) by (rewrite rev_nth by lia; exact HN).
  exact (proj1 (lead_exit (rev r) j H1 H2 H3)).
Qed.

(** One byte of a block in memory, as `lbu` reads it. *)
Lemma byte_read : forall m a (bs : list byte) i x,
  bytes_at rsegs m a bs -> nth_error bs i = Some x ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [x].
Proof.
  intros m a bs i x BA HX.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite HX; discriminate).
  rewrite (bytes_at_read rsegs m a bs (Z.of_nat i) 1 BA) by lia.
  rewrite Nat2Z.id. f_equal. clear BA.
  revert i Hi HX. induction bs as [|y bs IH]; intros [|i] Hi HX; cbn in HX |- *; try discriminate.
  - injection HX as E. subst. reflexivity.
  - apply IH; [cbn in Hi; lia | exact HX].
Qed.

(** ** Tactics *)
(** A branch the context excludes on one side. *)
Ltac nb :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in
      if_cases K; [ first [ exfalso; zify_cond K; Z.div_mod_to_equations; lia | idtac ] .. ]
  | _ => idtac
  end.
(** A register equation. *)
Ltac weq := first [ f_equal; lia | reflexivity | apply bv_eq; vm_compute; reflexivity ].

Section Strip.
Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (Sa Se lo sv ev : Z) (l : list byte).
Hypothesis Hsv : 0 < sv.
Hypothesis Hse : sv <= ev.
Hypothesis Hev : ev < 2 ^ 64.
Hypothesis HL : Z.of_nat (length l) = ev - sv.
Hypothesis Hcc : Sa + 8 <= Se \/ Se + 8 <= Sa.
Hypothesis Hlc : sv + (ev - sv) <= Sa \/ Sa + 8 <= sv.
Hypothesis Hle : sv + (ev - sv) <= Se \/ Se + 8 <= sv.

Local Abbreviation SW := [(Sa, Sa + 8); (Se, Se + 8)].
Local Abbreviation Post :=
  (ret_void rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 SW lo
     (fun m' => bytes_at rsegs m' Sa (le8 (Z_to_bv 64 (sv + Z.of_nat (strip_lead (zs l))))) /\
                bytes_at rsegs m' Se (le8 (Z_to_bv 64 (ev - Z.of_nat (strip_trail (zs l))))))).

(** The memory while the loops run: cell s holds s, cell e holds e. *)
Definition frm (m : word -> option byte) (s e : Z) : Prop :=
  rw_cells rsegs m Sa [C8 (Z_to_bv 64 s)] /\ rw_cells rsegs m Se [C8 (Z_to_bv 64 e)] /\
  bytes_at rsegs m sv l /\ munch SW m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp).

Ltac mk_frm := unfold frm; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); eassumption.

(** RET 0x150d0. *)
Lemma epi : forall m s e (x5 x12 x13 x14 x15 x16 x17 : word),
  frm m s e -> s = sv + Z.of_nat (strip_lead (zs l)) -> e = ev - Z.of_nat (strip_trail (zs l)) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 Sa) (Z_to_bv 64 Se) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x150d0) fc None m (seg_rom rsegs)).
Proof.
  intros m s e x5 x12 x13 x14 x15 x16 x17 (C1 & C2 & BA & MU & WM & MI & ST) Es Ee.
  zstep.
  apply evt_done. unfold ret_void. cbv beta.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  subst s e. split.
  - destruct C1 as [[_ B1] _]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1.
  - destruct C2 as [[_ B2] _]. cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2. exact B2.
Qed.

(** One pass of BACK 0x1508c with j trailing blanks dropped (e = e0 - j) and s = s0 + k fixed, k the leading
    blanks: the byte at e - 1 not blank returns, else the pass goes on to the next one ([K]). *)
Lemma back_step : forall k j s e m (x5 w12 x13 x14 x15 x16 x17 : word),
  (k + j < length l)%nat -> blank (nth k (zs l) 0) = false ->
  strip_lead (zs l) = k -> dropwhile blank (zs l) = skipn k (zs l) ->
  s = sv + Z.of_nat k -> e = ev - Z.of_nat j -> w12 = Z_to_bv 64 e ->
  (forall i, (length l - j <= i < length l)%nat -> blank (nth i (zs l) 0) = true) ->
  frm m s e ->
  (forall e' m' (y12 y13 y14 : word), (k + S j < length l)%nat -> e' = ev - Z.of_nat (S j) -> y12 = Z_to_bv 64 e' ->
     (forall i, (length l - S j <= i < length l)%nat -> blank (nth i (zs l) 0) = true) -> frm m' s e' ->
     evt rsegs Post
       (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 Sa) (Z_to_bv 64 Se) y12 y13 y14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1508c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 Sa) (Z_to_bv 64 Se) w12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1508c) fc None m (seg_rom rsegs)).
Proof.
  intros k j s e m x5 w12 x13 x14 x15 x16 x17 Hkj HN Hk Hdw Es Ee E12 HB FR K.
  subst w12.
  destruct FR as (C1 & C2 & BA & MU & WM & MI & ST).
  pose proof (bytes_at_bound _ _ _ _ BA) as BB.
  destruct (nth_error l (length l - S j)) as [x|] eqn:HX.
  2:{ exfalso. apply nth_error_None in HX. lia. }
  pose proof (zs_nth l _ x HX) as HXZ.
  assert (RD : ov_read_bytes rsegs m (wa (e + -1)) 1 = Some [x]).
  { replace (e + -1) with (sv + Z.of_nat (length l - S j)) by lia. exact (byte_read m sv l _ x BA HX). }
  pose proof (bv_unsigned_in_range 8 x) as Rx. change (bv_modulus 8) with 256 in Rx.
  (* this byte not blank: j = strip_trail *)
  assert (TR : blank (bv_unsigned x) = false -> strip_trail (zs l) = j).
  { intros HBx. unfold strip_trail. rewrite Hdw.
    apply trail_exit; rewrite length_skipn, length_zs.
    - lia.
    - intros i Hi. rewrite nth_skipn_z. apply HB. lia.
    - rewrite nth_skipn_z. replace (k + (length l - k - S j))%nat with (length l - S j)%nat by lia.
      rewrite HXZ. exact HBx. }
  (* 0x1508c addi a3, zero, 1; 0x15090 beq a2, a3: e > s >= 1 *)
  zstep. zstep. nb.
  (* 0x15094 lbu a3, -1(a2); 0x15098 addi a4, zero, 32 *)
  zstep. zstep.
  (* 0x1509c bltu a4, a3 *)
  zstep. if_cases Q1; zify_cond Q1.
  - (* above 32: not blank, RET *)
    eapply epi; [mk_frm | rewrite Hk; exact Es | rewrite (TR ltac:(apply blank_gt; lia)); exact Ee].
  - assert (Emod : bv_unsigned x mod 64 = bv_unsigned x) by (apply Z.mod_small; lia).
    (* lui, addiw, slli: a4 = 0x100002200; srl a3, a4, a3 *)
    zstep. zstep. zstep. zstep. rewrite ?Emod.
    (* andi a3, a3, 1 *)
    zstep. rewrite (sp_blank_bit (bv_unsigned x)) by lia.
    (* 0x150b4 beqz a3 *)
    zstep.
    destruct (blank (bv_unsigned x)) eqn:HBx.
    + nb.
      (* a blank byte is not s's byte: s < e - 1 *)
      assert (Hne : (length l - S j)%nat <> k).
      { intros E. rewrite E in HXZ. rewrite HXZ in HN. congruence. }
      (* 0x150b8 addi a3, zero, 2; 0x150bc bltu a2, a3: e >= 2 *)
      zstep. zstep. nb.
      (* 0x150c0 addi a2, a2, -1; 0x150c4 sd a2, 0(a1); 0x150c8 ld a3, 0(a0) *)
      zstep. zstep. zstep.
      (* 0x150cc bltu a3, a2: taken *)
      zstep. nb.
      eapply (K (e + -1)); [lia | lia | weq | | mk_frm].
      intros i Hi. destruct (Nat.eq_dec i (length l - S j)) as [->|Hne'];
        [rewrite HXZ; exact HBx | apply HB; lia].
    + (* bit clear: not blank, RET *)
      nb.
      eapply epi; [mk_frm | rewrite Hk; exact Es | rewrite (TR eq_refl); exact Ee].
Qed.

(** BACK from j trailing blanks dropped, q + 1 bytes left between s and e. *)
Lemma back : forall q k j s e m (x5 w12 x13 x14 x15 x16 x17 : word),
  (k + j + S q = length l)%nat -> blank (nth k (zs l) 0) = false ->
  strip_lead (zs l) = k -> dropwhile blank (zs l) = skipn k (zs l) ->
  s = sv + Z.of_nat k -> e = ev - Z.of_nat j -> w12 = Z_to_bv 64 e ->
  (forall i, (length l - j <= i < length l)%nat -> blank (nth i (zs l) 0) = true) ->
  frm m s e ->
  evt rsegs Post
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 Sa) (Z_to_bv 64 Se) w12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1508c) fc None m (seg_rom rsegs)).
Proof.
  induction q as [|q IH]; intros k j s e m x5 w12 x13 x14 x15 x16 x17 Hq HN Hk Hdw Es Ee E12 HB FR;
    (eapply (back_step k j s e);
       [lia | exact HN | exact Hk | exact Hdw | exact Es | exact Ee | exact E12 | exact HB | exact FR | ]);
    intros e' m' y12 y13 y14 Hlt Ee' E12' HB' FR'.
  - exfalso. lia.
  - eapply (IH k (S j) s e'); [lia | exact HN | exact Hk | exact Hdw | exact Es | exact Ee' | exact E12' | exact HB'
                               | exact FR'].
Qed.

(** One pass of FWD 0x15058 with k leading blanks passed (s = s0 + k): a byte that is not blank goes to BACK, a
    blank one stores s + 1 and goes on to the next byte ([K]) or, at e0, returns. *)
Lemma fwd_step : forall k s m (x5 w12 w13 w14 w15 w16 w17 : word),
  (k < length l)%nat -> s = sv + Z.of_nat k ->
  w12 = Z_to_bv 64 ev -> w13 = Z_to_bv 64 s -> w14 = Z_to_bv 64 32 ->
  w15 = Z_to_bv 64 4294976000 -> w16 = Z_to_bv 64 1 -> w17 = Z_to_bv 64 s ->
  (forall i, (i < k)%nat -> blank (nth i (zs l) 0) = true) ->
  frm m s ev ->
  (forall s' m' (y5 y12 y13 y17 : word), (S k < length l)%nat -> s' = sv + Z.of_nat (S k) ->
     y12 = Z_to_bv 64 ev -> y13 = Z_to_bv 64 s' -> y17 = Z_to_bv 64 s' ->
     (forall i, (i < S k)%nat -> blank (nth i (zs l) 0) = true) -> frm m' s' ev ->
     evt rsegs Post
       (MS (mkR ra sp gp tp y5 t1 t2 s0 s1 (Z_to_bv 64 Sa) (Z_to_bv 64 Se) y12 y13 w14 w15 w16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x15058) fc None m' (seg_rom rsegs))) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 Sa) (Z_to_bv 64 Se) w12 w13 w14 w15 w16 w17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15058) fc None m (seg_rom rsegs)).
Proof.
  intros k s m x5 w12 w13 w14 w15 w16 w17 Hkn Es E12 E13 E14 E15 E16 E17 HB FR K.
  subst w12 w13 w14 w15 w16 w17.
  destruct FR as (C1 & C2 & BA & MU & WM & MI & ST).
  pose proof (bytes_at_bound _ _ _ _ BA) as BB.
  destruct (nth_error l k) as [x|] eqn:HX.
  2:{ exfalso. apply nth_error_None in HX. lia. }
  pose proof (zs_nth l k x HX) as HXZ.
  assert (RD : ov_read_bytes rsegs m (wa s) 1 = Some [x]) by (rewrite Es; exact (byte_read m sv l k x BA HX)).
  pose proof (bv_unsigned_in_range 8 x) as Rx. change (bv_modulus 8) with 256 in Rx.
  (* 0x15058 beqz a3: s > 0 *)
  zstep. nb.
  (* 0x1505c lbu t0, 0(a3) *)
  zstep.
  (* 0x15060 bltu a4, t0 *)
  zstep. if_cases Q1; zify_cond Q1.
  - (* above 32: not blank, to BACK with no trailing blank dropped *)
    assert (HBx : blank (bv_unsigned x) = false) by (apply blank_gt; lia).
    rewrite <- HXZ in HBx.
    pose proof (lead_exit (zs l) k ltac:(rewrite length_zs; exact Hkn) HB HBx) as [Hk Hdw].
    eapply (back (length l - k - 1) k 0 s ev);
      [lia | exact HBx | exact Hk | exact Hdw | exact Es | lia | weq | intros i Hi; lia | mk_frm].
  - assert (Emod : bv_unsigned x mod 64 = bv_unsigned x) by (apply Z.mod_small; lia).
    (* srl t0, a5, t0 *)
    zstep. rewrite ?Emod.
    (* andi t0, t0, 1 *)
    zstep. rewrite (sp_blank_bit (bv_unsigned x)) by lia.
    (* 0x1506c beqz t0 *)
    zstep.
    destruct (blank (bv_unsigned x)) eqn:HBx.
    + nb.
      (* 0x15070 addi a7, a7, 1; 0x15074 bgeu a6, a7: s + 1 >= 2 *)
      zstep. zstep. nb.
      (* 0x15078 addi a3, a3, 1; 0x1507c sd a3, 0(a0); 0x15080 ld a2, 0(a1) *)
      zstep. zstep. zstep.
      (* 0x15084 bltu a3, a2 *)
      zstep. if_cases Q2; zify_cond Q2.
      * (* s + 1 < e0: the next byte *)
        eapply (K (s + 1)); [lia | lia | weq | weq | weq | | mk_frm].
        intros i Hi. destruct (Nat.eq_dec i k) as [->|Hne]; [rewrite HXZ; exact HBx | apply HB; lia].
      * (* s + 1 = e0: every byte blank; 0x15088 j RET *)
        zstep.
        assert (HA : forall i, (i < length (zs l))%nat -> blank (nth i (zs l) 0) = true).
        { rewrite length_zs. intros i Hi. destruct (Nat.eq_dec i k) as [->|Hne];
            [rewrite HXZ; exact HBx | apply HB; lia]. }
        destruct (lead_all (zs l) HA) as [Hk Hdw].
        eapply epi; [mk_frm | | ].
        -- unfold strip_lead. rewrite Hk, length_zs. lia.
        -- unfold strip_trail. rewrite Hdw. cbn [rev takewhile length]. lia.
    + (* bit clear: not blank, to BACK *)
      nb.
      rewrite <- HXZ in HBx.
      pose proof (lead_exit (zs l) k ltac:(rewrite length_zs; exact Hkn) HB HBx) as [Hk Hdw].
      eapply (back (length l - k - 1) k 0 s ev);
        [lia | exact HBx | exact Hk | exact Hdw | exact Es | lia | weq | intros i Hi; lia | mk_frm].
Qed.

(** FWD from k leading blanks passed, q + 1 bytes left. *)
Lemma fwd : forall q k s m (x5 w12 w13 w14 w15 w16 w17 : word),
  (k + S q = length l)%nat -> s = sv + Z.of_nat k ->
  w12 = Z_to_bv 64 ev -> w13 = Z_to_bv 64 s -> w14 = Z_to_bv 64 32 ->
  w15 = Z_to_bv 64 4294976000 -> w16 = Z_to_bv 64 1 -> w17 = Z_to_bv 64 s ->
  (forall i, (i < k)%nat -> blank (nth i (zs l) 0) = true) ->
  frm m s ev ->
  evt rsegs Post
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 Sa) (Z_to_bv 64 Se) w12 w13 w14 w15 w16 w17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15058) fc None m (seg_rom rsegs)).
Proof.
  induction q as [|q IH]; intros k s m x5 w12 w13 w14 w15 w16 w17 Hq Es E12 E13 E14 E15 E16 E17 HB FR;
    (eapply (fwd_step k s);
       [lia | exact Es | exact E12 | exact E13 | exact E14 | exact E15 | exact E16 | exact E17 | exact HB | exact FR
       | ]);
    intros s' m' y5 y12 y13 y17 Hlt Es' E12' E13' E17' HB' FR'.
  - exfalso. lia.
  - eapply (IH (S k) s'); [lia | exact Es' | exact E12' | exact E13' | exact E14 | exact E15 | exact E16 | exact E17'
                           | exact HB' | exact FR'].
Qed.

(** The whole function from its entry. *)
Lemma body : forall (x5 x12 x13 x14 x15 x16 x17 : word),
  Sa mod 8 = 0 -> Se mod 8 = 0 ->
  rw_cells rsegs m0 Sa [C8 (Z_to_bv 64 sv)] ->
  rw_cells rsegs m0 Se [C8 (Z_to_bv 64 ev)] ->
  bytes_at rsegs m0 sv l -> mem_inv rsegs m0 -> stk rsegs m0 lo (bv_unsigned sp) ->
  evt rsegs Post
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 Sa) (Z_to_bv 64 Se) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15028) fc None m0 (seg_rom rsegs)).
Proof.
  intros x5 x12 x13 x14 x15 x16 x17 H8a H8b C1 C2 BA MI ST.
  pose proof (munch_refl SW m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  pose proof (bytes_at_bound _ _ _ _ BA) as BB.
  pose proof (rw_cells_bound _ _ _ _ C1) as B1. pose proof (rw_cells_bound _ _ _ _ C2) as B2.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in B1, B2.
  assert (LA : Z.land (Z.lor Sa Se) 7 = 0).
  { rewrite Z.land_lor_distr_l. change 7 with (Z.ones 3). rewrite !Z.land_ones by lia.
    change (2 ^ 3) with 8. rewrite H8a, H8b. reflexivity. }
  (* or a2, a0, a1; andi a2, a2, 7; 0x15030 bnez a2: both cells 8-aligned *)
  zstep. zstep. rewrite ?LA.
  zstep. nb.
  (* ld a3, 0(a0); ld a2, 0(a1) *)
  zstep. zstep.
  (* 0x1503c bgeu a3, a2 *)
  zstep. if_cases Q0; zify_cond Q0.
  - (* s0 = e0: the empty range, RET *)
    assert (E0 : zs l = []) by (apply length_zero_iff_nil; rewrite length_zs; lia).
    eapply epi; [mk_frm | | ].
    + rewrite E0. unfold strip_lead. cbn [takewhile length]. lia.
    + rewrite E0. unfold strip_trail. cbn [dropwhile rev takewhile length]. lia.
  - (* addi a4, zero, 32; a5 = 0x100002200; addi a6, zero, 1; mv a7, a3 *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (fwd (length l - 1) 0 sv);
      [lia | lia | weq | weq | weq | weq | weq | weq | intros i Hi; lia | mk_frm].
Qed.

End Strip.

Theorem strip_holds : strip_contract.
Proof.
  unfold strip_contract, strip_pre, STRIP, STRIP_STACK, apart, stack_ok.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo sv ev l
    (H8a & H8b & Hcc & C1 & _ & C2 & _ & Hsv & Hev & BA & HL & Hlc & Hle & (ST & _ & _ & _) & MI).
  pose proof (Z_to_bv_bv_unsigned a0) as Ea0. pose proof (Z_to_bv_bv_unsigned a1) as Ea1.
  set (Sa := bv_unsigned a0) in *. set (Se := bv_unsigned a1) in *.
  rewrite <- Ea0, <- Ea1. clearbody Sa Se. clear Ea0 Ea1.
  eapply body; first [eassumption | lia].
Qed.
