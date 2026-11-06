(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 761 of its 797 lines of code are new or changed and 360 lines of the source are left out. *)
(* Segment F29 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the join 0x82750-0x82758 (plan-asan section 2
   row F29, no call, no check). rule 24: no function proved.
   v1.9 STATUS (2026-10-28): UNVERIFIED.  No build without probes has checked this file on v1.9.0.  It closed only
   in an ITERATION-ONLY build on the v1.9 bytes (FACTS 0bfe9aa0d452) with probes in Seg/Tac_slot.v and
   Seg/Tac_fsfree.v.  It waits for Seg/Tac_slot.v / Tac_fsfree.v re-fit to the regenerated Contract.v and FrameAPI.v.
   With s3 = S(fr) (the shadow byte of the frame base) the three instructions
     0x82750  sb s11,16(s3)
     0x82754  sb s11,17(s3)
     0x82758  sb s11,20(s3)
   store the low byte of s11 to the shadow bytes S(fr)+16, S(fr)+17 and S(fr)+20 (the shadow of fr+128 .. fr+143 and
   fr+160 .. fr+167). No register changes; the segment ends at 0x8275c.

   Cuts: the entry Inv_A82750_at and the exit Inv_A8275c_at are SlotInv.v's official bodies (the frame-loop skeleton
   `exists phi, CUTST g pc (hb1 phi (AC.a_size (flen g j))) ...` with HB and FLSI, LK, the frame-loop pass-through
   FLS and the hand-on bundle LT). FRA moves across the three shadow stores by
   Tac_slot.sl_fr_meta (f29_fra_meta; the heap invariant by Tac_fs.a_fs_ok_store_AH: each store is to the shadow of a
   frame byte, which is in the store set of the real-stack arm or the shadow of a side-stack byte of the side-stack
   arm), ENT by Tac_slot.ent_store and ent_mat. Every other carried fact (FLSI with PRO and FLC, LK, FLS, LT, HB)
   reads application memory, the spill block above the stack pointer, or the shadow of a byte outside
   [fr+128, fr+168) (the bytes at fr+2624, fr+2688 .. fr+2840, fr+2880 .. fr+2914, the harness block, the turn's
   block), none of which
   is S(fr)+16 .. S(fr)+20; the transports are the *_keep lemmas below, which F30 uses too.
   The pattern of f29_fra_meta is a Theorem Labs lane's F37.v (f37_fra_meta). A Theorem Labs lane independently re-fitted this
   segment on a working branch 0d49ba5949 (lemma AG_below for the frame_AG ranges below GT; ag_bound here plays
   that role). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 is the plain one here; the slot's
   cuts are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- Pure helpers (bytes, shadow arithmetic, the side stack's base word). *)

(* A one-byte store of a register writes its low byte. *)
Lemma le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

(* The 50 bytes of a frame's record (SlotModel.t_g = fr50 of its body). *)
Lemma t_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

(* bytes_at sub-range (as in a Theorem Labs lane's F18.v). *)
Lemma ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* n bytes that are all present form a list. *)
Lemma ba_present : forall m n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [exact Ha|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b0 & Hb0).
    assert (Hrest : forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + 1 + Z.of_nat i)) = Some b).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b & Hb). exists b.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrest) as (bs & (Ha' & Hl' & Hb') & Hlen).
    exists (b0 :: bs). split; [|cbn [length]; lia].
    split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. exact Hb0.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hb'. cbn [length] in Hi. lia.
Qed.

(* A present byte of a list read at its address. *)
Lemma ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma sh_frame_of : forall fr k, 0 <= fr -> fr mod 8 = 0 -> 0 <= k ->
  shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr k H0 H8 Hk. Z.div_mod_to_equations. lia. Qed.

Lemma sh_frame : forall fr y k, 0 <= fr -> fr mod 8 = 0 -> 0 <= y -> shadow_addr y = shadow_addr fr + k ->
  fr + 8 * k <= y < fr + 8 * k + 8.
Proof. unfold shadow_addr. intros fr y k H0 H8 Hy E. Z.div_mod_to_equations. lia. Qed.

Lemma sh_off : forall fr i k, 0 <= fr -> fr mod 8 = 0 -> 8 * k <= i < 8 * k + 8 ->
  shadow_addr (fr + i) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr i k H0 H8 Hi. Z.div_mod_to_equations. lia. Qed.

Lemma in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

(* addressable survives writes apart from the shadow bytes of its range. *)
Lemma addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

Lemma rg_mod : forall regs r a b, rg regs r a -> rg regs r b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  unfold rg. intros regs r a b Ha Hb. rewrite Ha in Hb. apply (f_equal bv_unsigned) in Hb.
  rewrite !Z_to_bv_unsigned in Hb. exact Hb.
Qed.

Lemma outside_app_r : forall W1 W2 x, outside (W1 ++ W2) x -> outside W2 x.
Proof. intros W1 W2 x H. exact (proj2 (outside_app W1 W2 x H)). Qed.

(* The side stack's base word: a word_mem witness and the le8 word at the same address agree mod 2^64. *)
Lemma wm_uniq : forall m x v (w : word), word_mem rsegs m x v -> bytes_at rsegs m x (le8 w) ->
  v mod 2 ^ 64 = bv_unsigned w.
Proof.
  intros m x v w Hv Hw.
  pose proof Hw as (Hx0 & Hx1 & _). rewrite length_le8 in Hx1. change (Z.of_nat 8) with 8 in Hx1.
  assert (Hv' : word_mem rsegs m x (v mod 2 ^ 64)).
  { intros k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold le_byte.
    change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)) as Hr.
  pose proof (word_mem_le8 rsegs m x (v mod 2 ^ 64) Hv' Hr Hx0 ltac:(lia)) as H8.
  pose proof (fl_le8_eq [] m m x _ _ H8 Hw (munch_refl [] m) (fun _ _ => I)) as E.
  apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. exact E.
Qed.

Lemma in_fs_range : forall m a (w : word), AC.a_in_fs AC.ASYMS m a -> bytes_at rsegs m RT_TP (le8 w) ->
  bv_unsigned w + AC.FS_SIZE <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> bv_unsigned w <= a < bv_unsigned w + AC.FS_SIZE.
Proof.
  intros m a w (b & Hbr & Hb & Hab) Hw Hsz Ha.
  change (AC.as_tp AC.ASYMS) with RT_TP in Hb.
  pose proof (wm_uniq m RT_TP b w Hb Hw) as E.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D.
  pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
  unfold AC.FS_SIZE in *. lia.
Qed.

(* The side stack's metadata cells lie in its first 36864 bytes. *)
Lemma fs_meta_ge : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [[c [Hc Hr]] | [c [jj [Hc [Hj Heq]]]]]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. pose proof (a_fs_flag_range FS c jj Hc Hj). lia.
Qed.

(* The registered globals (AF.frame_AG, 57 ranges) lie in [0x21140, 0x9f8e8), below the image top GT. *)
Lemma ag_bound : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hil & Hr). unfold AF.frame_AG in Hil. cbn [In] in Hil.
  repeat (destruct Hil as [E | Hil]; [injection E as <- <-; lia |]). destruct Hil.
Qed.

(* Below an 8-aligned bound, the shadow byte is below the bound's shadow byte. *)
Lemma sh_lt : forall y z, z mod 8 = 0 -> y < z -> shadow_addr y < shadow_addr z.
Proof. intros y z H8 H. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* Two in-range values of one register are the same value. *)
Lemma reg_eq : forall (regs : bvmap 5 word) (r : bv 5) a b,
  getr regs r = Z_to_bv 64 a -> getr regs r = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ra Rb.
  assert (E : Z_to_bv 64 a = Z_to_bv 64 b) by congruence.
  apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

(* A value of s1 within 416 bytes of the spill base A (both read through rg) is A. *)
Lemma rg_near : forall (regs : bvmap 5 word) (r : bv 5) a b, rg regs r a -> rg regs r b ->
  416 <= a -> a + 416 <= 2 ^ 64 -> -400 <= b -> b + 8 <= 2 ^ 64 -> b = a.
Proof.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  pose proof (rg_mod regs r b a Hb Ha) as E. rewrite (Z.mod_small a) in E by lia.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D. lia.
Qed.

(* A readable-and-writable range survives a run that keeps every byte of it backed. *)
Lemma stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
  rewrite wa_unsigned by lia. exact Ho.
Qed.

(* Every segment of the image ends below GT = 0x5fe000, so a read-only address is below it. *)
Local Definition f29_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Local Lemma f29_rsegs_top : f29_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma f29_find_below : forall segs top x n s,
  f29_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f29_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 0x5fe000.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (f29_find_below rsegs 0x5fe000 (bv_unsigned a) 1 s f29_rsegs_top E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

(* ---- The frame records of turn j (SlotInv's IDBe at fr + 2688, FGBe at fr + 2768) keep their sizes: the identity
   record is ID_SIZE = 38 bytes (ING keeps it) and the fragment state 72 bytes, so both lie in [fr + 2688, fr + 2840).
   (a Theorem Labs lane's F36.v, f36_tID_len / f36_fg_st_len / f36_tFG_len.) *)
Lemma tID_len : forall inp j, length (t_ID inp j) = ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH].
  - cbn [fst_at fs0 fs_id]. unfold ID0. apply repeat_length.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_id (turn s (t_len inp j) (t_g inp j)) =
                fg_id (rp_id (fs_id s) (t_len inp j) (t_g inp j)) (t_len inp j) (fs_fg s) (t_g inp j))
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E.
    assert (E1 : length (rp_id (fs_id s) (t_len inp j) (t_g inp j)) = ID_SIZE).
    { unfold rp_id. match goal with |- context [if ?b then _ else _] => destruct b end;
        [apply ING_length; exact IH | exact IH]. }
    unfold fg_id. match goal with |- context [if ?b then _ else _] => destruct b end;
      [apply ING_length; exact E1 | exact E1].
Qed.

Lemma fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg.
  assert (Hlf : 0 <= fg_lf st).
  { unfold fg_lf, bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat 7) st (Z_to_bv 8 0))) as R. lia. }
  assert (Hnn : forall len', fg_fr len' g = true -> 1 <= fg_n g <= 22).
  { intros len' Ef. unfold fg_fr in Ef. apply andb_prop in Ef as [Ef _]. apply andb_prop in Ef as [Ef E2].
    apply andb_prop in Ef as [_ E1]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia. }
  assert (HJ : 1 <= fg_n g <= 22 -> fg_T st g <= 64 -> length (fg_join st g) = 72%nat).
  { intros Hn HT. unfold fg_T in HT. unfold fg_join, fg_body, bsl.
    rewrite !length_app, !length_firstn, !length_skipn. rewrite Hs, Hg. unfold fg_T. lia. }
  assert (HC : forall l, length l = 72%nat -> length (fg_clear l) = 72%nat).
  { intros l Hl. unfold fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia. }
  unfold fg_st. destruct (fcls len st g) eqn:Ec; cbn [fg_next].
  - exact Hs.
  - exact Hs.
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    pose proof (Hnn len Ef) as Hn.
    unfold fg_first, fg_body, bsl. rewrite !length_app, !length_firstn, !length_skipn. cbn [length].
    rewrite Hs, Hg. lia.
  - exact (HC st Hs).
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    destruct (bat g 19 =? 1); [discriminate Ec|].
    destruct (fg_keep st g) eqn:Ek; cbn [negb] in Ec; [|discriminate Ec].
    unfold fg_keep in Ek. apply andb_prop in Ek as [_ E3]. apply Z.leb_le in E3.
    exact (HC _ (HJ (Hnn len Ef) E3)).
  - unfold fcls, fg_class in Ec. cbn [Z.eqb orb] in Ec.
    destruct (fg_fr len g) eqn:Ef; cbn [negb] in Ec; [|discriminate Ec].
    destruct (bat g 19 =? 1); [discriminate Ec|].
    destruct (fg_keep st g) eqn:Ek; cbn [negb] in Ec; [|discriminate Ec].
    unfold fg_keep in Ek. apply andb_prop in Ek as [_ E3]. apply Z.leb_le in E3.
    exact (HC _ (HJ (Hnn len Ef) E3)).
Qed.

Lemma tFG_len : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH].
  - cbn [fst_at fs0 fs_fg]. exact z72_length.
  - rewrite fst_at_S. set (s := fst_at inp j) in *.
    assert (E : fs_fg (turn s (t_len inp j) (t_g inp j)) = fg_st (t_len inp j) (fs_fg s) (t_g inp j))
      by (unfold turn; destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity).
    rewrite E. apply fg_st_len; [exact IH | unfold t_g; apply fr50_length].
Qed.

(* v1.9 FSb: the first fragment's body is at most the 23 bytes block[9 ..] of a 50-byte record (fs0's is empty),
   so it lies in [fr + 2880, fr + 2915), the 35 bytes FSb makes addressable. *)
Lemma fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at fs0 fs_body length]. lia.
  - rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn, t_g_length. lia.
Qed.

(* ---- Transports of the cut bundles across a run that writes W (shared with F30). *)

(* A spill at the spill base A (reg 9) moves across a run that misses [A, A + 416) and keeps reg 9. *)
Lemma spill_keep : forall regs regs' mem mem' W A off v,
  spill regs mem off v -> munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off <= 400 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  spill regs' mem' off v.
Proof.
  intros regs regs' mem mem' W A off v (A1 & HA1 & Hq) MU E9 Hr9 HA0 HA1' Ho HWA.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  assert (EA : A1 = A) by (apply (rg_near regs 9 A A1 Hr9 HA1); lia).
  subst A1. exists A. split; [unfold rg in *; rewrite E9; exact HA1|].
  unfold q64 in *. apply (fl_bytes _ mem mem' _ _ Hq MU). rewrite length_le8.
  intros x Hx. apply HWA. change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

(* PRO (push 14E): the eight prologue spills, our[]'s 6 bytes addressable, the harness block's bytes, (guarded
   by 0 < n) its live-block fact and addressability, and A4's four pointer spills [A+184] / [A+256] / [A+264] /
   [A+272]; v1.9: the former [A+200] is [A+208], and [A+32] = fr + 2880 is appended (16th). *)
Lemma pro_keep : forall g fr regs regs' mem mem' W A,
  PRO g fr regs mem -> munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall i, 0 <= i < 6 -> outside W (shadow_addr (fr + 2624 + i))) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  PRO g fr regs' mem'.
Proof.
  intros g fr regs regs' mem mem' W A
    (H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248 & Had & Hby & Hin & H184 & H256 & H264 & H272 & H32)
    MU E9 Hr9 HA0 HA1 HWA HWS HWP.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v)
    by (intros off v Ho Hs; exact (spill_keep regs regs' mem mem' W A off v Hs MU E9 Hr9 HA0 HA1 Ho HWA)).
  split; [apply SP; [lia | exact H40]|]. split; [apply SP; [lia | exact H120]|].
  split; [apply SP; [lia | exact H136]|]. split; [apply SP; [lia | exact H160]|].
  split; [apply SP; [lia | exact H168]|]. split; [apply SP; [lia | exact H176]|].
  split; [apply SP; [lia | exact H208]|]. split; [apply SP; [lia | exact H248]|].
  split; [exact (addr_keep W mem mem' _ _ Had MU HWS)|].
  split.
  { apply (fl_bytes _ mem mem' _ _ Hby MU). intros x Hx.
    exact (proj1 (HWP x ltac:(unfold g_n, nlen; lia))). }
  split.
  { intros Hn. destruct (Hin Hn) as (Hin' & Had'). split; [exact Hin'|].
    apply (addr_keep W mem mem' _ _ Had' MU). intros i Hi. exact (proj2 (HWP (g_p g + i) ltac:(lia))). }
  split; [apply SP; [lia | exact H184]|]. split; [apply SP; [lia | exact H256]|].
  split; [apply SP; [lia | exact H264]|]. split; [apply SP; [lia | exact H272]|]. apply SP; [lia | exact H32].
Qed.

(* FLSH = PRO, [A+128], the frame backed, [A+144] and the 17 bytes at fr + 2691 addressable. *)
Lemma flsh_keep : forall g j fr regs regs' mem mem' W A,
  FLSH g j fr regs mem -> munch W mem mem' -> wmono rsegs mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr <= x < fr + 3136 -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall i, 0 <= i < 6 -> outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 17 -> outside W (shadow_addr (fr + 2691 + i))) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  FLSH g j fr regs' mem'.
Proof.
  intros g j fr regs regs' mem mem' W A (HP & H128 & Hstk & H144 & Had17)
    MU WM E9 Hr9 HA0 HA1 HWA HWF HWS HWS17 HWP.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v)
    by (intros off v Ho Hs; exact (spill_keep regs regs' mem mem' W A off v Hs MU E9 Hr9 HA0 HA1 Ho HWA)).
  split; [exact (pro_keep g fr regs regs' mem mem' W A HP MU E9 Hr9 HA0 HA1 HWA HWS HWP)|].
  split; [apply SP; [lia | exact H128]|].
  split; [exact (stk_tr W mem mem' fr (fr + 3136) Hstk MU WM HWF)|].
  split; [apply SP; [lia | exact H144]|].
  exact (addr_keep W mem mem' _ _ Had17 MU HWS17).
Qed.

(* FLC (push 14E): ten frame-loop pointer spills, the 72 bytes at fragb fr = fr + 2768 and the 38 bytes at
   fr + 2688 addressable. Both ranges lie in [fr + 2688, fr + 2840), whose shadow bytes the run must miss.
   v1.9: the slots are renumbered and [A+56] = fr + 2889 / [A+48] = fr + 2890 are appended (13th / 14th). *)
Lemma flc_keep : forall fr regs regs' mem mem' W A,
  FLC fr regs mem -> munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall i, 0 <= i < 152 -> outside W (shadow_addr (fr + 2688 + i))) ->
  FLC fr regs' mem'.
Proof.
  intros fr regs regs' mem mem' W A
    (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfa & Cra & C72 & C64 & C56 & C48)
    MU E9 Hr9 HA0 HA1 HWA HWR.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v)
    by (intros off v Ho Hs; exact (spill_keep regs regs' mem mem' W A off v Hs MU E9 Hr9 HA0 HA1 Ho HWA)).
  split; [apply SP; [lia | exact C256]|]. split; [apply SP; [lia | exact C184]|].
  split; [apply SP; [lia | exact C192]|]. split; [apply SP; [lia | exact C80]|].
  split; [apply SP; [lia | exact C88]|]. split; [apply SP; [lia | exact C96]|].
  split; [apply SP; [lia | exact C272]|]. split; [apply SP; [lia | exact C264]|].
  split.
  { apply (addr_keep W mem mem' _ _ Cfa MU). intros i Hi. unfold fragb.
    replace (fr + 2768 + i) with (fr + 2688 + (80 + i)) by lia. apply HWR. lia. }
  split; [apply (addr_keep W mem mem' _ _ Cra MU); intros i Hi; apply HWR; lia|].
  split; [apply SP; [lia | exact C72]|]. split; [apply SP; [lia | exact C64]|].
  split; [apply SP; [lia | exact C56] | apply SP; [lia | exact C48]].
Qed.

(* FLSI: FLSH, the spills [A+216] / [A+224] / [A+248], the harness block f1_IN and FLC. *)
Lemma flsi_keep : forall g j fr regs regs' mem mem' W A,
  FLSI g j fr regs mem -> munch W mem mem' -> wmono rsegs mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr <= x < fr + 3136 -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall i, 0 <= i < 6 -> outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 17 -> outside W (shadow_addr (fr + 2691 + i))) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  (forall i, 0 <= i < 152 -> outside W (shadow_addr (fr + 2688 + i))) ->
  FLSI g j fr regs' mem'.
Proof.
  intros g j fr regs regs' mem mem' W A (HH & H216 & H224 & H248 & (Hin & Had & Hby) & HC)
    MU WM E9 Hr9 HA0 HA1 HWA HWF HWS HWS17 HWP HWR.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v)
    by (intros off v Ho Hs; exact (spill_keep regs regs' mem mem' W A off v Hs MU E9 Hr9 HA0 HA1 Ho HWA)).
  split; [exact (flsh_keep g j fr regs regs' mem mem' W A HH MU WM E9 Hr9 HA0 HA1 HWA HWF HWS HWS17 HWP)|].
  split; [apply SP; [lia | exact H216]|]. split; [apply SP; [lia | exact H224]|].
  split; [apply SP; [lia | exact H248]|].
  split.
  { split; [exact Hin|]. split.
    - apply (addr_keep W mem mem' _ _ Had MU). intros i Hi. exact (proj2 (HWP (g_p g + i) ltac:(lia))).
    - apply (fl_bytes _ mem mem' _ _ Hby MU). intros x Hx.
      exact (proj1 (HWP x ltac:(unfold g_n, nlen; lia))). }
  exact (flc_keep fr regs regs' mem mem' W A HC MU E9 Hr9 HA0 HA1 HWA HWR).
Qed.

(* FLS: FLSI, the turn's registers 18 / 22 / 23 / 24 / 25, the record part (under 50 <= len), the two turn
   spills. *)
Lemma fls_keep : forall g j phi fr regs regs' mem mem' W A,
  FLS g j phi fr regs mem -> munch W mem mem' -> wmono rsegs mem mem' ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr <= x < fr + 3136 -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall i, 0 <= i < 6 -> outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 17 -> outside W (shadow_addr (fr + 2691 + i))) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  (50 <= flen g j -> forall x, phi <= x < phi + flen g j -> outside W x) ->
  (forall i, 0 <= i < 152 -> outside W (shadow_addr (fr + 2688 + i))) ->
  FLS g j phi fr regs' mem'.
Proof.
  intros g j phi fr regs regs' mem mem' W A (HI & H18 & H22 & H23 & H24 & H25 & Hrec & H152 & H280)
    MU WM E9 E18 E22 E23 E24 E25 Hr9 HA0 HA1 HWA HWF HWS HWS17 HWP HWB HWR.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v)
    by (intros off v Ho Hs; exact (spill_keep regs regs' mem mem' W A off v Hs MU E9 Hr9 HA0 HA1 Ho HWA)).
  split; [exact (flsi_keep g j fr regs regs' mem mem' W A HI MU WM E9 Hr9 HA0 HA1 HWA HWF HWS HWS17 HWP HWR)|].
  split; [unfold rg in *; rewrite E18; exact H18|]. split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E23; exact H23|]. split; [unfold rg in *; rewrite E24; exact H24|].
  split; [unfold rg in *; rewrite E25; exact H25|].
  split.
  { intros H50. destruct (Hrec H50) as (Hp0 & Hp1 & Hg & Hpb & Hpl).
    split; [exact Hp0|]. split; [exact Hp1|].
    split.
    - apply (fl_bytes _ mem mem' _ _ Hg MU). rewrite t_g_length. intros x Hx.
      apply (HWB H50). change (Z.of_nat 50) with 50 in Hx. lia.
    - split; [|exact Hpl]. apply (fl_bytes _ mem mem' _ _ Hpb MU). intros x Hx. apply (HWB H50). lia. }
  split; [apply SP; [lia | exact H152] | apply SP; [lia | exact H280]].
Qed.

(* LK: the turn index in s5 and the 6 bytes OUR at fr + 2624. *)
Lemma lk_keep : forall g fr j regs regs' mem mem' W,
  LK g fr j regs mem -> munch W mem mem' -> getr regs' 21 = getr regs 21 ->
  (forall x, fr + 2624 <= x < fr + 2630 -> outside W x) ->
  LK g fr j regs' mem'.
Proof.
  intros g fr j regs regs' mem mem' W (Hj & H21 & HOUR) MU E21 HW.
  split; [exact Hj|]. split; [unfold rg in *; rewrite E21; exact H21|].
  unfold OURb in *. apply (fl_bytes _ mem mem' _ _ HOUR MU). rewrite OUR_length.
  intros x Hx. apply HW. change (Z.of_nat 6) with 6 in Hx. lia.
Qed.

(* LT = IFS g fr (S j): the frame records of turn j + 1 at fr + 2688 / fr + 2768 and, v1.9 FSb, the spills
   [A+104] / [A+112] and the first fragment's body at fr + 2880 with its 35 addressable bytes. *)
Lemma lt_keep : forall g fr j regs regs' mem mem' W A,
  LT g fr j regs mem -> munch W mem mem' -> getr regs' 9 = getr regs 9 ->
  rg regs 9 A -> 416 <= A -> A + 416 <= 2 ^ 64 ->
  (forall x, A <= x < A + 416 -> outside W x) ->
  (forall x, fr + 2688 <= x < fr + 2840 -> outside W x) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x /\ outside W (shadow_addr x)) ->
  LT g fr j regs' mem'.
Proof.
  intros g fr j regs regs' mem mem' W A HLT MU E9 Hr9 HA0 HA1 HWA HWF HWB.
  assert (SP : forall off v, 0 <= off <= 400 -> spill regs mem off v -> spill regs' mem' off v)
    by (intros off v Ho Hs; exact (spill_keep regs regs' mem mem' W A off v Hs MU E9 Hr9 HA0 HA1 Ho HWA)).
  destruct HLT as ((HIDB & Hok1) & (HFGB & Hok2) & (H104 & H112 & Hbody & Had & HFI)).
  split; [|split].
  - split; [|exact Hok1]. unfold IDBe in *.
    apply (fl_bytes _ mem mem' _ _ HIDB MU). rewrite tID_len. unfold ID_SIZE.
    intros x Hx. apply HWF. lia.
  - split; [|exact Hok2]. unfold FGBe in *.
    apply (fl_bytes _ mem mem' _ _ HFGB MU). rewrite tFG_len.
    intros x Hx. apply HWF. lia.
  - split; [apply SP; [lia | exact H104]|]. split; [apply SP; [lia | exact H112]|].
    split.
    { apply (fl_bytes _ mem mem' _ _ Hbody MU). pose proof (fs_body_len (g_in g) (S j)) as Hl.
      intros x Hx. exact (proj1 (HWB x ltac:(lia))). }
    split; [|exact HFI].
    apply (addr_keep W mem mem' _ _ Had MU). intros i Hi. exact (proj2 (HWB (fr + 2880 + i) ltac:(lia))).
Qed.

(* HB: the turn's block, nonzero and addressable over a_size len. *)
Lemma hb_keep : forall mem mem' W phi len,
  HB mem phi len -> munch W mem mem' ->
  (forall i, 0 <= i < AC.a_size len -> outside W (shadow_addr (phi + i))) ->
  HB mem' phi len.
Proof.
  intros mem mem' W phi len (H0 & Had) MU HW. split; [exact H0|].
  exact (addr_keep W mem mem' phi _ Had MU HW).
Qed.

(* ---- The run: three one-byte stores to S(fr)+16, +17, +20 (S3 = S(fr)). *)
Lemma f29_evt :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> rw_cells rsegs m (S3 + 16) [CB 5 bs] ->
    0 <= S3 -> S3 + 21 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                                          x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x8275c) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 16, S3 + 21)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' (S3 + 16) cs /\ cells_size cs = 5%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82750) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 bs -> HRW H0 H1.
  pose proof (munch_refl [(S3 + 16, S3 + 21)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite le1_byte. mem_after_store.
  step. rewrite le1_byte. mem_after_store.
  step. rewrite le1_byte. mem_after_store.
  match goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm (S3 + 16) ?cs |- _ =>
      apply evt_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* Lib-evt -> SR bridge (as in a Theorem Labs lane's F18.v: the run is a Lib.Exec.evt, which feeds evt_SR_canon_lazy). *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

Local Notation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Local Notation OWNED H mem md := (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md).

(* The frame's place (plan FP.1/FP.2): the side stack FS is the word at tp (RT's asan_fs_cells), below the real stack;
   the frame is on the real stack (at or above stklo) or inside FS; either way it is application memory at or above
   the image top GT. *)
Lemma fra_loc : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists FS, (exists w : word, bytes_at rsegs mem RT_TP (le8 w) /\ bv_unsigned w = FS) /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= STKLO mem md /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    HIGHMEM_BEG <= STKLO mem md /\
    0 <= fr /\ AC.GT <= fr /\ (forall a, fr <= a < fr + 3136 -> app_mem a) /\
    ((STKLO mem md <= fr /\ fr + 3136 <= APPMEM_END) \/ (FS <= fr /\ fr + 3136 <= FS + AC.FS_SIZE)).
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof Hwin as (Hw0 & Hw1 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSw & HFok) & _).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)).
  { change (AC.as_tp AC.ASYMS) with RT_TP. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ mem md (bv_unsigned FSw) HAH Hwm HFSr)
    as (HGT & HFSlo & _ & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  pose proof Hhdr1 as (Hfr0 & _).
  exists (bv_unsigned FSw).
  split; [exists FSw; split; [exact HFSw | reflexivity]|].
  split; [exact HGT|]. split; [exact HFSlo|]. split; [exact HFSapp|]. split; [exact Hhi|].
  split; [exact Hfr0|]. split; [exact HGTfr|]. split; [exact Hfrapp|].
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + 3135) ltac:(lia)) as R2. left. lia.
  - assert (HFS1 : bv_unsigned FSw + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK, APPMEM_END in *; lia).
    assert (Hin : forall a, fr <= a < fr + 3136 -> bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE).
    { intros a Ha. apply (in_fs_range mem a FSw (Hfs a Ha) HFSw HFS1).
      unfold AF.SLOT_STACK, AC.FS_SIZE, APPMEM_END in *. lia. }
    pose proof (Hin fr ltac:(lia)) as F1. pose proof (Hin (fr + 3135) ltac:(lia)) as F2.
    right. lia.
Qed.

(* A byte of a live heap block is not a frame byte (AH1: blocks lie below stklo and off FS). *)
Lemma fra_blk : forall g fr hb regs mem md p n a, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= a < p + n -> fr <= a < fr + 3136 -> False.
Proof.
  intros g fr hb regs mem md p n a HFRA Hin Ha Hfa.
  pose proof FRAME_BYTES_val as HFBv.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md p n HAH Hin) as (_ & _ & Hend & _ & Hall).
  destruct (Hall a Ha) as (_ & _ & _ & _ & Hnfs).
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal a Hfa). lia.
  - exact (Hnfs (Hfs a Hfa)).
Qed.

(* FRA across a run that writes n shadow bytes of the frame, [S(fr) + o, S(fr) + o + n) with o + n <= 392:
   Tac_slot.sl_fr_meta, with the heap invariant from Tac_fs.a_fs_ok_store_AH (each written byte is the shadow of
   a frame byte, which is in the store set of the real-stack arm or the shadow of a side-stack byte on the side
   arm).  The stack bounds and the allocator's byte set do not change either, which ENT reads. *)
Lemma f29_fra_meta : forall g fr hb regs regs' mem mem' md (o n : Z),
  FRA B APIf ra g fr hb regs mem md ->
  0 <= o -> 0 < n -> o + n <= 392 ->
  munch [(Sfr fr + o, Sfr fr + o + n)] mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, Sfr fr + o <= x < Sfr fr + o + n -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\
  STKLO mem' md = STKLO mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall q, OWNED (hb ++ g_H g) mem' md q <-> OWNED (hb ++ g_H g) mem md q).
Proof.
  intros g fr hb regs regs' mem mem' md o n HFRA Ho Hn Hon MU WM HroM HnewP E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_loc g fr hb regs mem md HFRA)
    as (FS & (FSw & HFSw & EFS) & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & HGTfr & Hfrapp & Hfrloc).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    (sh & Hsh & Hshl) & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  set (S3 := Sfr fr) in *.
  assert (HSh : forall x, S3 <= x < S3 + 392 ->
    in_shadow x /\ shadow_addr (fr + 8 * (x - S3)) = x /\ fr <= fr + 8 * (x - S3) < fr + 3136).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - S3)) = x)
      by (rewrite sh_frame_of by lia; unfold S3, Sfr; lia).
    split; [rewrite <- E; apply shadow_of_app, Hfrapp; lia | split; [exact E | lia]]. }
  pose proof (in_shadow_bnd _ (proj1 (HSh S3 ltac:(lia)))) as HS3a.
  pose proof (in_shadow_bnd _ (proj1 (HSh (S3 + 391) ltac:(lia)))) as HS3b.
  set (W := [(S3 + o, S3 + o + n)]) in *.
  assert (HWsh : forall x, S3 + o <= x < S3 + o + n -> in_shadow x) by (intros x Hx; apply HSh; lia).
  assert (HWapp : forall x, app_mem x -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin. exact (app_not_shadow x Hx (HWsh x Hin)). }
  assert (HWhi : forall x, HIGHMEM_BEG <= x -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
    pose proof (in_shadow_bnd _ (HWsh x Hin)). lia. }
  assert (HWsh2 : forall x, ~ (S3 <= x < S3 + 392) -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. lia. }
  assert (HpresM : forall x, 0 <= x < 2 ^ 64 -> (exists b, mrd rsegs mem (wa x) = Some b) ->
    exists b, mrd rsegs mem' (wa x) = Some b).
  { intros x Hx Hp. destruct (Z_le_gt_dec (S3 + o) x); [destruct (Z_lt_ge_dec x (S3 + o + n))|].
    - apply HnewP. lia.
    - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia | exact I].
    - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia | exact I]. }
  assert (Hsh' : exists sh', bytes_at rsegs mem' S3 sh' /\ length sh' = 392%nat).
  { apply ba_present; [unfold LOWMEM_END in *; lia | unfold HIGHMEM_BEG in *; lia |].
    intros i Hi. apply HpresM; [unfold LOWMEM_END, HIGHMEM_BEG in *; lia|].
    apply (ba_some mem S3 sh); [exact Hsh | rewrite Hshl; lia]. }
  assert (Hrtdj : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    unfold LOWMEM_END in HS3a. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  rewrite EFS in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { change (AC.as_tp AC.ASYMS) with RT_TP. rewrite <- EFS.
    exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  assert (Hfsz : FS + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hmeta : forall q, fs_meta FS q -> outside W q).
  { intros q Hq. apply HWapp. apply HFSapp. split; [exact (fs_meta_ge FS q Hq)|].
    pose proof (fs_meta_below FS q Hq). unfold AC.FS_SIZE. lia. }
  assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) q -> ~ (FS <= q < FS + AC.FS_SIZE) ->
    ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) -> mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
  { intros q Hq Hns Hnf Hnsh. apply MU. rewrite unsigned_lit by lia. cbn [outside]. split; [|exact I].
    intros Hin. destruct (HSh q ltac:(lia)) as (_ & Eq & Hb).
    destruct Hfrloc as [[Hlo Hhi'] | [Hlo Hhi']].
    - apply Hns. unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (q - S3)).
      split; [symmetry; exact Eq|]. right; left. lia.
    - apply Hnsh. exists (fr + 8 * (q - S3)). split; [lia | symmetry; exact Eq]. }
  destruct (a_fs_ok_store_AH AC.ASYMS _ _ _ _ W _ mem mem' md FS LAWS HAH Hwm HFSr Hfsz MU
              (fun q _ Hw => WM _ Hw) (fun q Hq Hp => HpresM q Hq Hp) Hmeta Hagree)
    as (HAH' & HOWN & HSTK & HSTKHI).
  assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
  { intros a Hin. pose proof (ag_bound a Hin) as Hab.
    apply (addr_keep W mem mem' a 1 (HAG a Hin) MU). intros i Hi.
    assert (Hlt : shadow_addr (a + i) < S3)
      by (unfold S3, Sfr; apply sh_lt; [exact Hfr8 | unfold AC.GT in HGTfr; lia]).
    apply HWsh2. lia. }
  split; [|split; [exact HSTK | split; [exact HSTKHI | exact HOWN]]].
  apply (sl_fr_meta B APIf ra empty FF g fr _ regs regs' mem mem' md W HFRA MU WM HroM Hrtdj HAH' HSTK
           Hfrapp HGTfr Hsh').
  - intros x Hx Hn1 Hn2. exact (HWsh2 x Hn2).
  - intros A1 HA1 HA1r x Hx.
    assert (EA : A1 = A) by (apply (reg_eq regs 9 A1 A HA1 Hr9 HA1r HA64)).
    apply HWhi. lia.
  - intros x Hx. apply HWhi. lia.
  - intros A1 HA1 HA1r x Hx.
    assert (EA : A1 = A) by (apply (reg_eq regs 9 A1 A HA1 Hr9 HA1r HA64)).
    apply HWhi. lia.
  - intros x Hx. left. apply HWhi. unfold AF.SLOT_STACK in *. lia.
  - exact HAG'.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.


Lemma seg_F29 : forall j, Hat B APIf ra (Inv_A8275c_at B APIf ra) j -> Hat B APIf ra (Inv_A82750_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HFLS & HLT).
  subst c. pose proof (proj1 FF) as SEGS.
  pose proof (fra_loc g fr _ regs mem md HFRA)
    as (FS & _ & _ & _ & _ & Hhi & Hfr0 & HGTfr & Hfrapp & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & (sh & Hsh & Hshl) & Hwin & Hsaved & Herrno & HAG & HWAd &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (HA416' : 416 <= A) by (unfold HIGHMEM_BEG in *; lia).
  assert (HAtop : A + 416 <= 2 ^ 64) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (HSh : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
      by (rewrite sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  pose proof (in_shadow_bnd _ (HSh (Sfr fr) ltac:(lia))) as HS3a.
  pose proof (in_shadow_bnd _ (HSh (Sfr fr + 391) ltac:(lia))) as HS3b.
  (* the five shadow bytes S(fr)+16 .. S(fr)+20, present and writable *)
  pose proof (ba_sub mem (Sfr fr) sh 16 5 Hsh ltac:(lia)) as Hsh5. change (Z.of_nat 16) with 16 in Hsh5.
  assert (Hwr5 : wr_at rsegs mem (Sfr fr + 16) 5).
  { split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|]. intros i Hi.
    exact (proj1 (RT_shadow_rw _ _ _ HRT (Sfr fr + 16 + i) (HSh (Sfr fr + 16 + i) ltac:(lia)))). }
  assert (HRW : rw_cells rsegs mem (Sfr fr + 16) [CB 5 (firstn 5 (skipn 16 sh))]).
  { split; [split|].
    - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hsh5.
    - cbn [cells_size csize Nat.add]. exact Hwr5. }
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x82750) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x8275c /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
       getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\ getr R0 25 = getr regs 25 /\
       getr R0 26 = getr regs 26 /\
       munch [(Sfr fr + 16, Sfr fr + 21)] mem mem' /\ wmono rsegs mem mem' /\
       exists cs, rw_cells rsegs mem' (Sfr fr + 16) cs /\ cells_size cs = 5%nat)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f29_evt with (m := mem) (S3 := Sfr fr);
        [unfold rg in Hr19; exact Hr19 | exact HRW | unfold LOWMEM_END in *; lia
        | unfold HIGHMEM_BEG in *; lia]. }
    { intros ms' (m' & E & MU & WM & cs & Hcs & Hcsl).
      eexists _, (Z_to_bv 64 0x8275c), m'. split; [exact E|].
      split; [reflexivity|].
      do 13 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM|]. exists cs. split; [exact Hcs | exact Hcsl]. }
  - intros R0 pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er21 & Er22 & Er23 & Er24 & Er25 & Er26 & MU & WM &
       cs & Hcs & Hcsl) Hreg Hmat.
    subst pc'.
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (F21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (F22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (F23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (F24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    (* the written bytes are present again *)
    assert (HnewP : forall x, Sfr fr + 16 <= x < Sfr fr + 16 + 5 -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      replace x with (Sfr fr + 16 + (x - (Sfr fr + 16))) by lia.
      apply (ba_some mem' (Sfr fr + 16) (cells_bytes cs)); [exact Hba | rewrite Hlen, Hcsl; cbn; lia]. }
    assert (MU5 : munch [(Sfr fr + 16, Sfr fr + 16 + 5)] mem mem')
      by (replace (Sfr fr + 16 + 5) with (Sfr fr + 21) by lia; exact MU).
    assert (HroM : ro_agree rsegs mem').
    { apply (ro_agree_same rsegs mem mem' Hro). intros a Ha.
      pose proof (ro_lo a Ha) as Hlo'. apply MU. cbn [outside]. split; [|exact I].
      unfold LOWMEM_END in HS3a. lia. }
    destruct (f29_fra_meta g fr _ regs regs' mem mem' md 16 5 HFRA ltac:(lia) ltac:(lia) ltac:(lia)
                MU5 WM HroM HnewP F2 F3 F4 F8 F9 F19 F26) as (HFRA1 & HSTK1 & HSTKHI1 & HOWN1).
    assert (HFRA2 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr _ regs' regs' mem' md md' HFRA1); try reflexivity; exact Hmat).
    (* ENT across the stores and the model's lazy materialisation *)
    assert (HENT1 : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md).
    { apply (ent_store B APIf ra g fr _ regs mem mem' md [(Sfr fr + 16, Sfr fr + 21)] HENT HFRA MU).
      - intros x Hx. destruct (Z_le_gt_dec (Sfr fr + 16) x); [destruct (Z_lt_ge_dec x (Sfr fr + 21))|].
        + right. right. right. lia.
        + left. cbn [outside]. split; [lia | exact I].
        + left. cbn [outside]. split; [lia | exact I].
      - exact HSTK1.
      - exact HSTKHI1.
      - intros a Hia Hio. exact (proj2 (HOWN1 a) Hio). }
    assert (HENT2 : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md')
      by exact (ent_mat APIf g _ mem' md md' HENT1 Hmat).
    (* what the three stores miss *)
    assert (HWhi : forall x, HIGHMEM_BEG <= x -> outside [(Sfr fr + 16, Sfr fr + 21)] x).
    { intros x Hx. cbn [outside]. split; [lia | exact I]. }
    assert (HWapp : forall x, app_mem x -> outside [(Sfr fr + 16, Sfr fr + 21)] x).
    { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
      exact (app_not_shadow x Hx (HSh x ltac:(lia))). }
    assert (HnotFR : forall y, 0 <= y -> ~ (fr + 128 <= y < fr + 168) ->
              outside [(Sfr fr + 16, Sfr fr + 21)] (shadow_addr y)).
    { intros y Hy0 Hy. cbn [outside]. split; [|exact I]. intros Hin.
      pose proof (sh_frame fr y (shadow_addr y - Sfr fr) Hfr0 Hfr8 Hy0 ltac:(unfold Sfr in *; lia)) as Hz.
      apply Hy. lia. }
    pose proof HFLSI as (_ & _ & _ & _ & (Hin & Hpad & _) & _).
    assert (HWP : forall x, g_p g <= x < g_p g + g_n g ->
              outside [(Sfr fr + 16, Sfr fr + 21)] x /\ outside [(Sfr fr + 16, Sfr fr + 21)] (shadow_addr x)).
    { intros x Hx.
      assert (Hxa : app_mem x) by (apply (addressable_app mem (g_p g) (g_n g) Hpad); lia).
      assert (Hnf : ~ (fr <= x < fr + 3136)).
      { intros Hc. apply (fra_blk g fr _ regs mem md (g_p g) (g_n g) x HFRA); [|lia|exact Hc].
        apply in_or_app. right. apply Hin. lia. }
      split; [exact (HWapp x Hxa)|].
      apply HnotFR; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia | intros Hc; apply Hnf; lia]. }
    destruct HHB as (Hphi0 & Hphad).
    assert (Hphapp : forall x, phi <= x < phi + AC.a_size (flen g j) -> app_mem x)
      by (intros x Hx; exact (addressable_app mem phi _ Hphad x Hx)).
    assert (Hphfr : forall x, phi <= x < phi + AC.a_size (flen g j) -> ~ (fr <= x < fr + 3136)).
    { intros x Hx Hc. exact (fra_blk g fr _ regs mem md phi _ x HFRA (or_introl eq_refl) Hx Hc). }
    assert (HWF : forall x, fr <= x < fr + 3136 ->
              outside [(Sfr fr + 16, Sfr fr + 21)] x \/ exists b, mrd rsegs mem' (wa x) = Some b)
      by (intros x Hx; left; exact (HWapp x (Hfrapp x Hx))).
    assert (HWA : forall x, A <= x < A + 416 -> outside [(Sfr fr + 16, Sfr fr + 21)] x)
      by (intros x Hx; apply HWhi; lia).
    assert (HWS : forall i, 0 <= i < 6 -> outside [(Sfr fr + 16, Sfr fr + 21)] (shadow_addr (fr + 2624 + i)))
      by (intros i Hi; apply HnotFR; [lia | intros Hc; lia]).
    assert (HWS17 : forall i, 0 <= i < 17 ->
              outside [(Sfr fr + 16, Sfr fr + 21)] (shadow_addr (fr + 2691 + i)))
      by (intros i Hi; apply HnotFR; [lia | intros Hc; lia]).
    assert (HWR : forall i, 0 <= i < 152 ->
              outside [(Sfr fr + 16, Sfr fr + 21)] (shadow_addr (fr + 2688 + i)))
      by (intros i Hi; apply HnotFR; [lia | intros Hc; lia]).
    assert (HWB : 50 <= flen g j -> forall x, phi <= x < phi + flen g j -> outside [(Sfr fr + 16, Sfr fr + 21)] x).
    { intros H50 x Hx. apply HWapp, Hphapp. unfold AC.a_size. lia. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr. split; [reflexivity|]. split; [exact HFRA2|]. split; [exact HENT2|].
    split; [exact Hgn|]. split; [exact Hj|].
    split.
    { split; [exact Hphi0|]. apply (addr_keep _ mem mem' phi _ Hphad MU).
      intros i Hi. pose proof (Hphapp (phi + i) ltac:(lia)) as Ha.
      apply HnotFR; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha; lia|].
      intros Hc. apply (Hphfr (phi + i)); lia. }
    split; [exact (flsi_keep g j fr regs regs' mem mem' _ A HFLSI MU WM F9 Hr9 HA416' HAtop HWA HWF HWS HWS17 HWP
                     HWR)|].
    split; [apply (lk_keep g fr j regs regs' mem mem' _ HLK MU F21); intros x Hx; apply HWapp, Hfrapp; lia|].
    split; [exact (fls_keep g j phi fr regs regs' mem mem' _ A HFLS MU WM F9 F18 F22 F23 F24 F25 Hr9 HA416' HAtop
                     HWA HWF HWS HWS17 HWP HWB HWR)|].
    apply (lt_keep g fr j regs regs' mem mem' _ A HLT MU F9 Hr9 HA416' HAtop HWA).
    + intros x Hx. apply HWapp, Hfrapp. lia.
    + intros x Hx. split; [apply HWapp, Hfrapp; lia|].
      apply HnotFR; [lia | intros Hc; lia].
Qed.

End S.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
