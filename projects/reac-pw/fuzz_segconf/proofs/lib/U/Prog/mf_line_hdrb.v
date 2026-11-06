(** m_file (UBSan build, image 1696d6c34ffd): the sub-piece S_MFU_HDRB of S_MF_LINE (U/Prog/mfu_cuts.v). From
    the cut HFIND 0x144ec (the header's name nm, 1 .. 15 bytes, at p + o: a1 and the cell 0x98(sp); s5 = |nm|) to
    the tail 0x146b4 (H_MF_TAIL). The model step is mh_find (Prog/mfu_facts.v).

    Code (the UBSan build's disassembly):
      0x144ec mv a0,s0; mv a2,s5; jal m_find 0x144f4
      0x144f8 beqz a0 -> 0x148d4 (not found)
      found: andi a1,a0,3; s4 = 1; bnez a1 -> trap (dead: g = c + 256 i, c 16-aligned); sd a0,0x30(sp) (cur = g);
             lw a0,0xfc(a0) (g->gen); lw a1,0x3b0(s8) (c->gen); bne -> 0x14948; else m_refuse 0x14520, j 0x14948
      0x148d4 lw a0,0(s8) (c->n); s4 = 1; blt a0,s10 -> 0x14900 (n < 32)
             full: lw/addi/sw 4(s8) (overflow++), m_refuse 0x148f4, sd zero,0x30(sp), j the tail
      0x14900 addi a1,a0,1; sw a1,0(s8) (c->n = n+1); bgeu a0,0x21 -> trap (dead: n < 32); slli a0,a0,8;
             ld a1,8(sp) (~c); bltu a1,a0 -> trap (dead: c + 9236 <= 2^64); add s1,s0,a0 (g = c + 256 n);
             memset(g,0,256) 0x1492c; ld a1,0x98(sp) (nm); sd s1,0x30(sp); memcpy(g,nm,|nm|) 0x14940; s4 = 1
      0x14948 ld a1,0x30(sp); andi a0,a1,3; bnez -> trap (dead); lw a0,0x3b0(s8) (c->gen); sw a0,0xfc(a1); j the tail
    The block store lemmas are in Prog/mfp_mconf.v; the call and tail lemmas in U/Prog/mfu_kit.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec mfu_facts mfp_facts mfp_mconf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts mfu_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import m_find_c memset_c memcpy_c m_refuse_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists and bytes *)

Lemma hb_list_eq_nth : forall (a b : list byte), length a = length b ->
  (forall i, (i < length a)%nat -> nth_error a i = nth_error b i) -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] HL H; cbn [length] in HL; try discriminate; [reflexivity|].
  injection HL as HL. f_equal.
  - specialize (H 0%nat ltac:(cbn [length]; lia)). cbn [nth_error] in H. injection H as H. exact H.
  - apply IH; [exact HL|]. intros i Hi. exact (H (S i) ltac:(cbn [length]; lia)).
Qed.

Lemma hb_upd_bytes_comm : forall (bs : list byte) k1 b1 k2 b2,
  (k1 + length b1 <= k2)%nat -> (k2 + length b2 <= length bs)%nat ->
  upd_bytes (upd_bytes bs k1 b1) k2 b2 = upd_bytes (upd_bytes bs k2 b2) k1 b1.
Proof.
  intros bs k1 b1 k2 b2 H1 H2.
  assert (L1 : length (upd_bytes bs k1 b1) = length bs) by (apply upd_bytes_length; lia).
  assert (L2 : length (upd_bytes bs k2 b2) = length bs) by (apply upd_bytes_length; lia).
  apply hb_list_eq_nth.
  - rewrite (upd_bytes_length (upd_bytes bs k1 b1) k2 b2) by lia.
    rewrite (upd_bytes_length (upd_bytes bs k2 b2) k1 b1) by lia. lia.
  - intros i Hi.
    assert (Hib : (i < length bs)%nat)
      by (rewrite (upd_bytes_length (upd_bytes bs k1 b1) k2 b2) in Hi by lia; lia).
    rewrite (upd_bytes_nth (upd_bytes bs k1 b1) k2 b2 i) by lia.
    rewrite (upd_bytes_nth (upd_bytes bs k2 b2) k1 b1 i) by lia.
    rewrite (upd_bytes_nth bs k1 b1 i) by lia.
    rewrite (upd_bytes_nth bs k2 b2 i) by lia.
    destruct (Nat.leb_spec k2 i); destruct (Nat.ltb_spec i (k2 + length b2));
      destruct (Nat.leb_spec k1 i); destruct (Nat.ltb_spec i (k1 + length b1));
      cbn [andb]; try reflexivity; try lia.
Qed.

(** An update of 4 bytes at k + 252 inside the 256-byte entry at k. *)
Lemma hb_upd_split : forall (PRE EN PO nb : list byte) k,
  length PRE = k -> length EN = 256%nat -> length nb = 4%nat ->
  upd_bytes (PRE ++ EN ++ PO) (k + 252) nb = PRE ++ upd_bytes EN 252 nb ++ PO.
Proof.
  intros PRE EN PO nb k HP HE HN.
  assert (E1 : firstn (k + 252) (PRE ++ EN ++ PO) = PRE ++ firstn 252 EN).
  { rewrite firstn_app. rewrite HP. rewrite firstn_all2 by lia.
    replace (k + 252 - k)%nat with 252%nat by lia.
    rewrite firstn_app. rewrite HE. replace (252 - 256)%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. reflexivity. }
  assert (E2 : skipn (k + 252 + 4) (PRE ++ EN ++ PO) = PO).
  { replace (k + 252 + 4)%nat with (k + 256)%nat by lia.
    rewrite skipn_app. rewrite HP. replace (k + 256 - k)%nat with 256%nat by lia.
    rewrite skipn_all2 by lia. cbn [app].
    rewrite skipn_app. rewrite HE. replace (256 - 256)%nat with 0%nat by lia.
    rewrite skipn_all2 by lia. cbn [skipn app]. reflexivity. }
  assert (E3 : skipn (252 + 4) EN = []).
  { replace (252 + 4)%nat with 256%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
  unfold upd_bytes. rewrite HN, E1, E2, E3. rewrite app_nil_r. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma hb_fld_fld : forall a n b k (l : list byte), (a + n <= k)%nat ->
  firstn n (skipn a (firstn k (skipn b l))) = firstn n (skipn (b + a) l).
Proof.
  intros a n b k l H. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (k - a)) with n by lia. rewrite (Nat.add_comm a b). reflexivity.
Qed.

Lemma hb_zb_zs : forall l : list byte, zb (zs l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. unfold zs, zb in *. cbn [map]. rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma hb_zs_len : forall l : list byte, length (zs l) = length l.
Proof. intros. unfold zs. apply length_map. Qed.

Lemma hb_zs_range : forall l : list byte, Forall (fun x => 0 <= x < 256) (zs l).
Proof.
  induction l as [|b l IH]; [constructor|]. unfold zs in *. cbn [map]. constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (Z.of_N 8) with 8 in R. lia.
Qed.

Lemma hb_zs_fs : forall (l : list byte) k j, zs (firstn k (skipn j l)) = firstn k (skipn j (zs l)).
Proof. intros. unfold zs. rewrite <- firstn_map, <- skipn_map. reflexivity. Qed.

Lemma hb_fs_app : forall (l1 l2 : list byte) k j, (k + j <= length l1)%nat ->
  firstn j (skipn k (l1 ++ l2)) = firstn j (skipn k l1).
Proof.
  intros l1 l2 k j H. rewrite skipn_app, firstn_app, length_skipn.
  replace (j - (length l1 - k))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma hb_in_fs : forall (l : list Z) k j x, In x (firstn k (skipn j l)) -> In x l.
Proof.
  intros l k j x H.
  rewrite <- (firstn_skipn j l). apply in_or_app. right.
  rewrite <- (firstn_skipn k (skipn j l)). apply in_or_app. left. exact H.
Qed.

Lemma hb_sub : forall m a (l : list byte) k j, bytes_at rsegs m a l -> (k + j <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn j (skipn k l)).
Proof.
  intros m a l k j H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn j (skipn k l)) in H. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Lemma hb_subz : forall m a (l : list byte) (k : Z) (j : nat), bytes_at rsegs m a l -> 0 <= k ->
  (Z.to_nat k + j <= length l)%nat -> bytes_at rsegs m (a + k) (firstn j (skipn (Z.to_nat k) l)).
Proof.
  intros m a l k j HB Hk HL. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
  apply hb_sub; [exact HB | exact HL].
Qed.

Lemma hb_wr_at_sub : forall m a n k j, wr_at rsegs m a n -> 0 <= k -> k + j <= n -> wr_at rsegs m (a + k) j.
Proof.
  intros m a n k j (Ha & Hn & H) Hk Hj. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma hb_wr_of_stk : forall m lo' hi', stk rsegs m lo' hi' -> wr_at rsegs m lo' (hi' - lo').
Proof.
  intros m lo' hi' (H1 & H2 & H). split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo' + i) ltac:(lia))).
Qed.

Lemma hb_rw_CB : forall m a (bs : list byte) k, length bs = k -> bytes_at rsegs m a bs ->
  wr_at rsegs m a (Z.of_nat k) -> rw_cells rsegs m a [CB k bs].
Proof.
  intros m a bs k HL HB HW. split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact HL | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Lemma hb_rw_CB_bytes : forall m a n (bs : list byte), rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof.
  intros m a n bs [[Hwf Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

(** ** The footprint *)

Lemma hb_mfu_W_len_eq : forall sp0 c k0 mca mcb pend,
  length (mc_seg mca) = length (mc_seg mcb) -> length (mc_kept mca) = length (mc_kept mcb) ->
  mfu_W sp0 c k0 mca pend = mfu_W sp0 c k0 mcb pend.
Proof. intros sp0 c k0 mca mcb pend Hs Hk. unfold mfu_W, M_FILE_W. rewrite Hs, Hk. reflexivity. Qed.

Lemma hb_mfu_W_mono : forall sp0 c k0 mca mcb, mf_grows mca mcb ->
  sub_fp (mfu_W sp0 c k0 mca false) (mfu_W sp0 c k0 mcb false).
Proof.
  intros sp0 c k0 mca mcb [Hs Hk].
  unfold sub_fp, mfu_W, M_FILE_W, mseg_addr, kept_addr, MSEG_SIZE, MC_KNOCK, MC_KEPT, MC_KEPT_LEN,
    MC_N, MC_REFUSED, MC_NKEPT, MC_READING.
  cbn [app outside]. intros x Hx.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; lia.
Qed.

(** The ranges of [mfu_W] a store or a callee's footprint lies in (proved away from the walk's context,
    where lia would case-split the block/stack disjunctions). *)
Lemma hb_in_frame : forall sp0 c k0 mcx a nb, sp0 - 6224 <= a -> a + nb <= sp0 ->
  inside (mfu_W sp0 c k0 mcx false) a nb.
Proof.
  intros sp0 c k0 mcx a nb H1 H2.
  unfold mfu_W, M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K. cbn [app inside]. left. lia.
Qed.

Lemma hb_in_seg : forall sp0 c k0 mcx a nb j, (j < length (mc_seg mcx))%nat ->
  c + 256 * Z.of_nat j <= a -> a + nb <= c + 256 * Z.of_nat j + 256 ->
  inside (mfu_W sp0 c k0 mcx false) a nb.
Proof.
  intros sp0 c k0 mcx a nb j Hj H1 H2.
  unfold mfu_W, M_FILE_W, mseg_addr, MSEG_SIZE. cbn [app inside]. right. left. lia.
Qed.

Lemma hb_in_hdr : forall sp0 c k0 mcx a nb, c + 8192 <= a -> a + nb <= c + 8204 ->
  inside (mfu_W sp0 c k0 mcx false) a nb.
Proof.
  intros sp0 c k0 mcx a nb H1 H2.
  unfold mfu_W, M_FILE_W, MC_N, MC_REFUSED. cbn [app inside]. right. right. left. lia.
Qed.

Lemma hb_fp_frame : forall sp0 c k0 mcx q1 q2, sp0 - 6224 <= q1 -> q2 <= sp0 ->
  sub_fp [(q1, q2)] (mfu_W sp0 c k0 mcx false).
Proof.
  intros sp0 c k0 mcx q1 q2 H1 H2.
  unfold sub_fp, mfu_W, M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K. cbn [app outside].
  intros x Hx. destruct Hx as [X1 _]. split; [lia | exact I].
Qed.

Lemma hb_fp_seg : forall sp0 c k0 mcx q1 q2 j, (j < length (mc_seg mcx))%nat ->
  c + 256 * Z.of_nat j <= q1 -> q2 <= c + 256 * Z.of_nat j + 256 ->
  sub_fp [(q1, q2)] (mfu_W sp0 c k0 mcx false).
Proof.
  intros sp0 c k0 mcx q1 q2 j Hj H1 H2.
  unfold sub_fp, mfu_W, M_FILE_W, mseg_addr, MSEG_SIZE. cbn [app outside].
  intros x Hx. destruct Hx as (_ & X2 & _). split; [lia | exact I].
Qed.

(** ** Words *)

Lemma hb_mod_pow_mod : forall z a b, 0 <= a <= b -> (z mod 2 ^ b) mod 2 ^ a = z mod 2 ^ a.
Proof.
  intros z a b H.
  assert (Hd : (2 ^ a | 2 ^ b)) by (exists (2 ^ (b - a)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
  apply Z.mod_mod_divide. exact Hd.
Qed.

Lemma hb_sx32_val : forall z, 0 <= z < 2 ^ 32 ->
  bv_unsigned (sx32 (Z_to_bv 64 z)) = if z <? 2 ^ 31 then z else z + 2 ^ 64 - 2 ^ 32.
Proof.
  intros z Hz. assert (Ez : bv_unsigned (Z_to_bv 64 z) = z) by (apply unsigned_lit; lia).
  unfold sx32. rewrite Ez, Z_to_bv_unsigned.
  unfold bv_swrap. unfold bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  destruct (Z.ltb_spec z (2 ^ 31)) as [Hl|Hl].
  - rewrite (Z.mod_small (z + 2 ^ 31) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
  - assert (E : (z + 2 ^ 31) mod 2 ^ 32 = z - 2 ^ 31).
    { replace (z + 2 ^ 31) with ((z - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
      apply Z.mod_small. lia. }
    rewrite E.
    replace (z - 2 ^ 31 - 2 ^ 31) with ((z - 2 ^ 31 - 2 ^ 31 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma hb_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. apply bv_eq. rewrite hb_sx32_val by lia. rewrite unsigned_lit by lia.
  destruct (Z.ltb_spec z (2 ^ 31)); [reflexivity | lia].
Qed.

Lemma hb_signed_lit : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2 ^ 64); lia).
  apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

Lemma hb_sx32_eq_iff : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  (bv_unsigned (sx32 (Z_to_bv 64 x)) = bv_unsigned (sx32 (Z_to_bv 64 y)) <-> x = y).
Proof.
  intros x y Hx Hy. split; [|intros ->; reflexivity].
  intros E. rewrite !hb_sx32_val in E by lia.
  destruct (Z.ltb_spec x (2 ^ 31)); destruct (Z.ltb_spec y (2 ^ 31)); lia.
Qed.

Lemma hb_sx32_mod : forall z, 0 <= z < 2 ^ 32 -> bv_unsigned (sx32 (Z_to_bv 64 z)) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z Hz. rewrite hb_sx32_val by lia.
  destruct (Z.ltb_spec z (2 ^ 31)); [reflexivity|].
  replace (z + 2 ^ 64 - 2 ^ 32) with (z + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma hb_le4_eqm : forall x y : word, bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned x) 32) by (cbn [Z.of_nat Pos.of_succ_nat]; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned y) 32) by (cbn [Z.of_nat Pos.of_succ_nat]; lia).
  rewrite H. reflexivity.
Qed.

Lemma hb_le4_sx32 : forall z, 0 <= z < 2 ^ 32 -> le4 (sx32 (Z_to_bv 64 z)) = le4 (Z_to_bv 64 z).
Proof.
  intros z Hz. apply hb_le4_eqm. rewrite hb_sx32_mod by lia. rewrite unsigned_lit by lia. reflexivity.
Qed.

Lemma hb_le4_addi : forall z d, 0 <= z < 2 ^ 32 ->
  le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 z)) + d)) = le4 (Z_to_bv 64 (z + d)).
Proof.
  intros z d Hz. apply hb_le4_eqm. rewrite !unsigned_lit_wrap. rewrite !hb_mod_pow_mod by lia.
  rewrite <- (Z.add_mod_idemp_l (bv_unsigned (sx32 (Z_to_bv 64 z))) d (2 ^ 32)) by lia.
  rewrite hb_sx32_mod by lia.
  rewrite (Z.add_mod_idemp_l z d (2 ^ 32)) by lia. reflexivity.
Qed.

Lemma hb_land3 : forall t, 0 <= t -> t mod 4 = 0 -> Z.land t 3 = 0.
Proof.
  intros t Ht Hm. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. exact Hm.
Qed.

Lemma hb_mf_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (mf_line_rest rest) as [[E _]|[E _]].
  - pose proof (f_equal (@length Z) E) as L. rewrite length_app in L. cbn [length] in L. lia.
  - pose proof (f_equal (@length Z) E) as L. lia.
Qed.

Lemma hb_saved_len : forall ws : list word, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; cbn [map concat length]; [reflexivity|].
  rewrite length_app, length_le8, IH; lia.
Qed.

Lemma hb_rd8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le8 v) 0 8 H) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma hb_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le4 v) 0 4 H) by (rewrite length_le4; lia).
  reflexivity.
Qed.

(** Normalise to [wa A] the address of the store the last step left. *)
Ltac hdb_addr A :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?aa _) _) =>
      replace aa with (wa A) by (unfold wa; f_equal; lia)
  end.

(** ** The walk *)
Section HdrB.
Variables (n : nat) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (mcut : word -> option byte) (lo : Z)
  (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat)
  (k0 : nat) (rest : list Z) (o : nat) (nm : list Z) (nmb : list byte).
Hypothesis HMF : m_find_contract.
Hypothesis HMS : memset_contract.
Hypothesis HMC : memcpy_contract.
Hypothesis HMR : m_refuse_contract.
Hypothesis HT : H_MF_TAIL n.
Hypothesis Hn : (length rest <= n)%nat.
Hypothesis Hne : rest <> [].
Hypothesis HL : m_file_loop mcut fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis Hnm : (0 < length nm < 16)%nat.
Hypothesis Ho : (o + length nm <= length (mf_line rest))%nat.
Hypothesis Hnmbz : zs nmb = nm.
Hypothesis Hnm0 : ~ In 0 nm.
Hypothesis Hc98 : cell8 mcut (bv_unsigned sp + 152) (p + Z.of_nat o).
Hypothesis Hnmbat : bytes_at rsegs mcut (p + Z.of_nat o) nmb.

Local Abbreviation hdb_post :=
  (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0
     (mf_fin (mh_find mc nm (line + 1)) line rest)).

Lemma hdb_nmb_len : length nmb = length nm.
Proof. rewrite <- Hnmbz. symmetry. apply hb_zs_len. Qed.

Lemma hdb_nm_range : Forall (fun x => 0 <= x < 256) nm.
Proof. rewrite <- Hnmbz. apply hb_zs_range. Qed.

(** The numbers of the loop facts. *)
Lemma hdb_facts :
  bv_unsigned sp + 272 = bv_unsigned sp0 /\ lo + 6224 <= bv_unsigned sp0 /\ 0 <= lo /\
  bv_unsigned sp0 < 2 ^ 63 /\ 0 < c /\ c + 9236 <= 2 ^ 64 /\ c mod 16 = 0 /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\ 0 <= p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64 /\
  1 <= Z.of_nat (length rest) /\ (o + length nm <= length rest)%nat /\
  mc_refused mc + Z.of_nat (length rest) < 2 ^ 32 /\ mc_overflow mc + Z.of_nat (length rest) < 2 ^ 32.
Proof.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (Hsp & _ & _ & _ & _ & _ & _ & _ & Hcne & Hc16 & _ & _ & HWR & _ & _ & _ &
                 _ & Hl0 & Hl1 & Href & Hovf & _ & _ & HCS & _ & _ & HPE & _ & _ & HSO & _).
  destruct HPE as (_ & _ & _ & _ & Hsp63). destruct HSO as ((Hlo0 & _) & Hlo & _ & _).
  destruct HWR as (Hc1 & Hc2 & _).
  destruct HCS as (bs & sl & BA & ZS & _ & _).
  assert (Lb : length bs = length rest) by (rewrite <- ZS; symmetry; apply hb_zs_len).
  apply bytes_at_bound in BA. rewrite length_app in BA. cbn [length] in BA.
  pose proof (hb_mf_line_le rest) as HLL.
  assert (Hr1 : (1 <= length rest)%nat).
  { destruct (Nat.eq_dec (length rest) 0) as [E|E]; [|lia]. apply length_zero_iff_nil in E. congruence. }
  unfold M_FILE_FRAME in Hsp. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in Hlo. unfold SEG_M_SIZE in Hc2.
  repeat split; try lia.
Qed.

Lemma hdb_apart : c + 9240 <= lo \/ bv_unsigned sp0 <= c.
Proof.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAP & _).
  unfold apart, SEG_M_SIZE in HAP. lia.
Qed.

Lemma hdb_apartp : p + Z.of_nat (length rest) + 8 <= lo \/ bv_unsigned sp0 <= p.
Proof.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                 _ & _ & _ & _ & _ & _ & _ & _ & HAP & _).
  unfold apart in HAP. lia.
Qed.

Lemma hdb_apartpc : p + Z.of_nat (length rest) <= c \/ c + 9236 <= p.
Proof.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                 _ & _ & _ & _ & _ & _ & _ & _ & _ & HAP & _).
  unfold apart, cstr_span, SEG_M_SIZE in HAP.
  pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma hdb_wr : forall m, wmono rsegs mcut m -> wr_at rsegs m c 9236.
Proof.
  intros m WM. pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWR & _).
  unfold SEG_M_SIZE in HWR. eapply wr_at_transport; [exact HWR | exact WM].
Qed.

(** A byte string of the frame, over a write inside the block. *)
Lemma hdb_keepb : forall (m : word -> option byte) A (bs0 : list byte) (a : Z) (w : list byte),
  bytes_at rsegs m A bs0 -> bv_unsigned sp <= A -> A + Z.of_nat (length bs0) <= bv_unsigned sp0 ->
  c <= a -> a + Z.of_nat (length w) <= c + 9236 ->
  bytes_at rsegs (write_to_mem m (wa a) w) A bs0.
Proof.
  intros m A bs0 a w HB H1 H2 H3 H4.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & _).
  pose proof hdb_apart as AP.
  apply (bytes_at_write_other rsegs m a w A bs0 HB); lia.
Qed.

(** A byte string anywhere, over a write in the frame cell 0x30(sp). *)
Lemma hdb_keepf : forall (m : word -> option byte) A (bs0 : list byte) (w : list byte),
  bytes_at rsegs m A bs0 -> Z.of_nat (length w) = 8 ->
  (A + Z.of_nat (length bs0) <= bv_unsigned sp + 48 \/ bv_unsigned sp + 56 <= A) ->
  bytes_at rsegs (write_to_mem m (wa (bv_unsigned sp + 48)) w) A bs0.
Proof.
  intros m A bs0 w HB HW HD.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & _).
  pose proof (u64_range sp) as Rsp.
  apply (bytes_at_write_other rsegs m (bv_unsigned sp + 48) w A bs0 HB); lia.
Qed.

(** A byte string over a callee's footprint [q1, q2). *)
Lemma hdb_keepw : forall (m1 m2 : word -> option byte) (q1 q2 : Z) A (bs0 : list byte),
  bytes_at rsegs m1 A bs0 -> munch [(q1, q2)] m1 m2 ->
  (A + Z.of_nat (length bs0) <= q1 \/ q2 <= A) -> bytes_at rsegs m2 A bs0.
Proof.
  intros m1 m2 q1 q2 A bs0 HB MU HD. eapply bytes_at_transport; [exact HB | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** The block and the stack region do not meet (kept small: lia case-splits [hdb_apart] here only). *)
Lemma hdb_stk_dj : forall q1 q2, c <= q1 -> q2 <= c + 9236 ->
  disjoint_from [(q1, q2)] lo (bv_unsigned sp0 - lo).
Proof.
  intros q1 q2 H1 H2.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & _). pose proof hdb_apart as AP.
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma hdb_frm_dj : forall q1 q2, bv_unsigned sp <= q1 -> q2 <= bv_unsigned sp0 ->
  disjoint_from [(q1, q2)] c 9236.
Proof.
  intros q1 q2 H1 H2.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & _). pose proof hdb_apart as AP.
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** A byte string of [sp, sp0) over m_refuse's footprint. *)
Lemma hdb_keepr : forall (m1 m2 : word -> option byte) (mcx : mconf) A (bs0 : list byte),
  bytes_at rsegs m1 A bs0 -> munch (m_refuse_W (bv_unsigned sp) c mcx) m1 m2 ->
  bv_unsigned sp <= A -> A + Z.of_nat (length bs0) <= bv_unsigned sp0 -> bytes_at rsegs m2 A bs0.
Proof.
  intros m1 m2 mcx A bs0 HB MU H1 H2. eapply bytes_at_transport; [exact HB | exact MU |].
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & _).
  pose proof hdb_apart as AP.
  unfold m_refuse_W, M_REFUSE_STACK, PRINTF_K, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED.
  destruct (Z.of_nat (length (mc_kept mcx)) <? 8) eqn:E8; cbn [app disjoint_from].
  - apply Z.ltb_lt in E8. repeat split; lia.
  - repeat split; lia.
Qed.

(** The block's bytes and its gen field. *)
Lemma hdb_blk : forall (m : word -> option byte) (mcx : mconf),
  mconf_atp rsegs false m c mcx ->
  exists bs, bytes_at rsegs m c bs /\ Z.of_nat (length bs) = 9236 /\ mconf_enc mcx bs /\
             bytes_at rsegs m (c + 9136) (le4 (Z_to_bv 64 (mc_gen mcx))) /\ 0 <= mc_gen mcx < 2 ^ 32.
Proof.
  intros m mcx HA.
  destruct (mconf_atp_bytes rsegs false m c mcx HA) as (bs & HB & HE & HL9).
  pose proof HE as HE0. destruct HE0 as (HLZ & _). unfold SEG_M_SIZE in HLZ.
  exists bs. split; [exact HB|]. split; [exact HLZ|]. split; [exact HE|].
  pose proof HE as HE'.
  destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG & _).
  unfold u32_enc, fldz, fld, MC_GEN in HG. destruct HG as [HGb HGe].
  split; [|exact HGb].
  replace (c + 9136) with (c + 0x23b0) by lia.
  rewrite <- HGe. apply hb_subz; [exact HB | lia | lia].
Qed.

(** The gen field of entry i. *)
Lemma hdb_seg_gen : forall (m : word -> option byte) (mcx : mconf) (bs : list byte) (i : nat),
  bytes_at rsegs m c bs -> Z.of_nat (length bs) = 9236 -> mconf_enc mcx bs ->
  (i < length (mc_seg mcx))%nat ->
  bytes_at rsegs m (c + 256 * Z.of_nat i + 252) (le4 (Z_to_bv 64 (ms_gen (nth i (mc_seg mcx) mseg_d)))) /\
  0 <= ms_gen (nth i (mc_seg mcx) mseg_d) < 2 ^ 32 /\ (i < 32)%nat.
Proof.
  intros m mcx bs i HB HBL HE Hi.
  assert (Hi32 : (i < 32)%nat) by (destruct HE as (_ & H32 & _); lia).
  pose proof HE as HE'. destruct HE' as (_ & _ & HSG & _). specialize (HSG i Hi).
  destruct HSG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGG).
  unfold u32_enc, fldz, fld, MS_GEN in HGG. destruct HGG as [HGb HGe].
  split; [|split; [exact HGb | exact Hi32]].
  rewrite <- HGe. rewrite hb_fld_fld by lia.
  replace (256 * i + Z.to_nat 0xfc)%nat with (Z.to_nat (256 * Z.of_nat i + 252)) by lia.
  replace (c + 256 * Z.of_nat i + 252) with (c + (256 * Z.of_nat i + 252)) by lia.
  apply hb_subz; [exact HB | lia | lia].
Qed.

(** The state at a program point inside the piece. *)
Definition hdb_mid (m : word -> option byte) (mcx : mconf) (curx : option nat) : Prop :=
  munch (mfu_W (bv_unsigned sp0) c k0 mcx false) mcut m /\ wmono rsegs mcut m /\ mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp0) /\ mconf_atp rsegs false m c mcx /\
  saved_at rsegs m (bv_unsigned sp + 168) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] /\
  cell8 m (bv_unsigned sp + 8) (- 1 - c) /\ cell8 m (bv_unsigned sp + 16) (c + 9100) /\
  cell8 m (bv_unsigned sp + 24) (- 1 - (c + 9100)) /\ cell8 m (bv_unsigned sp + 32) (c + 9140) /\
  cell8 m (bv_unsigned sp + 40) (c + 8192) /\ cell8 m (bv_unsigned sp + 48) (cur_ptr c curx) /\
  cell8 m (bv_unsigned sp + 152) (p + Z.of_nat o) /\ bytes_at rsegs m (p + Z.of_nat o) nmb.

(** ** 0x14948: g->gen = c->gen, then the tail *)
Lemma hdb_gen : forall (m : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s5 t3 t4 t5 t6 : word)
    (mcf : mconf) (i : nat) (bs : list byte) (gv : Z),
  mh_find mc nm (line + 1) = (mcf, Some i) ->
  mf_grows mc mcf -> mc_refused mcf <= mc_refused mc + 1 -> mc_overflow mcf <= mc_overflow mc + 1 ->
  (i < length (mc_seg mcf))%nat -> (i < 32)%nat ->
  bytes_at rsegs m c bs -> Z.of_nat (length bs) = 9236 -> wr_at rsegs m c 9236 ->
  bytes_at rsegs m (c + 9136) (le4 (Z_to_bv 64 gv)) -> 0 <= gv < 2 ^ 32 ->
  mconf_enc mcf (upd_bytes bs (256 * i + 252)%nat (le4 (Z_to_bv 64 gv))) ->
  munch (mfu_W (bv_unsigned sp0) c k0 mcf false) mcut m -> wmono rsegs mcut m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp0) ->
  saved_at rsegs m (bv_unsigned sp + 168) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] ->
  cell8 m (bv_unsigned sp + 8) (- 1 - c) -> cell8 m (bv_unsigned sp + 16) (c + 9100) ->
  cell8 m (bv_unsigned sp + 24) (- 1 - (c + 9100)) -> cell8 m (bv_unsigned sp + 32) (c + 9140) ->
  cell8 m (bv_unsigned sp + 40) (c + 8192) -> cell8 m (bv_unsigned sp + 48) (c + 256 * Z.of_nat i) ->
  frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  evt rsegs hdb_post
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) s5 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + 8192)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b)
             t3 t4 t5 t6)
        F' (Z_to_bv 64 0x14948) fc' None m (seg_rom rsegs)).
Proof.
  intros m F' fc' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s5 t3 t4 t5 t6 mcf i bs gv
    HMH HGR HRF HOV Hi Hi32 HB HBL HWR HGB Hgv HENC MU WM MI ST HSV C08 C10 C18 C20 C28 C30 FRM FREL.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hc16 & Hl0 & Hl1 & Hp1 & Hp2 & Hr1 & Hon & Href & Hovf).
  pose proof (u64_range sp) as Rsp.
  unfold cell8 in C08, C10, C18, C20, C28, C30. unfold saved_at in HSV.
  pose proof (hb_rd8 m (bv_unsigned sp + 48) (Z_to_bv 64 (c + 256 * Z.of_nat i)) C30) as RD30.
  pose proof (hb_rd4 m (c + 9136) (Z_to_bv 64 gv) HGB) as RDG.
  step.
  step. rewrite (unsigned_lit (c + 256 * Z.of_nat i)) by lia.
  replace (Z.land (c + 256 * Z.of_nat i) 3) with 0
    by (symmetry; apply hb_land3; [lia | Z.div_mod_to_equations; lia]).
  step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
  step.
  assert (SOK : store_ok rsegs m (wa (c + Z.of_nat (256 * i + 252))) 4 = true).
  { replace (wa (c + Z.of_nat (256 * i + 252))) with (wa (c + (256 * Z.of_nat i + 252)))
      by (unfold wa; f_equal; lia).
    apply (wr_at_store_ok rsegs m c 9236 (256 * Z.of_nat i + 252) 4 HWR); lia. }
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?ww) _) =>
      replace ww with (le4 (Z_to_bv 64 gv)) by (symmetry; first [reflexivity | apply hb_le4_sx32; lia])
  end.
  hdb_addr (c + Z.of_nat (256 * i + 252)).
  pose proof (bytes_at_write_inside rsegs m c bs (Z.of_nat (256 * i + 252)) (le4 (Z_to_bv 64 gv)) HB
                ltac:(lia) ltac:(rewrite length_le4; lia)) as HB2.
  rewrite Nat2Z.id in HB2.
  assert (KP : forall A (bs0 : list byte), bytes_at rsegs m A bs0 -> bv_unsigned sp <= A ->
                 A + Z.of_nat (length bs0) <= bv_unsigned sp0 ->
                 bytes_at rsegs (write_to_mem m (wa (c + Z.of_nat (256 * i + 252))) (le4 (Z_to_bv 64 gv))) A bs0).
  { intros A bs0 HBa H1 H2. apply (hdb_keepb m A bs0); try lia; [exact HBa|]. rewrite length_le4. lia. }
  pose proof (KP _ _ HSV ltac:(lia) ltac:(rewrite hb_saved_len; cbn [length]; lia)) as HSV2.
  pose proof (KP _ _ C08 ltac:(lia) ltac:(rewrite length_le8; lia)) as C08'.
  pose proof (KP _ _ C10 ltac:(lia) ltac:(rewrite length_le8; lia)) as C10'.
  pose proof (KP _ _ C18 ltac:(lia) ltac:(rewrite length_le8; lia)) as C18'.
  pose proof (KP _ _ C20 ltac:(lia) ltac:(rewrite length_le8; lia)) as C20'.
  pose proof (KP _ _ C28 ltac:(lia) ltac:(rewrite length_le8; lia)) as C28'.
  pose proof (KP _ _ C30 ltac:(lia) ltac:(rewrite length_le8; lia)) as C30'.
  assert (MU2 : munch (mfu_W (bv_unsigned sp0) c k0 mcf false) mcut
                  (write_to_mem m (wa (c + Z.of_nat (256 * i + 252))) (le4 (Z_to_bv 64 gv)))).
  { apply (munch_write _ mcut m); [exact MU | lia | rewrite length_le4; lia|].
    rewrite length_le4. eapply hb_in_seg with (j := i); [exact Hi | lia | lia]. }
  assert (WM2 : wmono rsegs mcut (write_to_mem m (wa (c + Z.of_nat (256 * i + 252))) (le4 (Z_to_bv 64 gv))))
    by (apply wmono_write; exact WM).
  assert (MI2 : mem_inv rsegs (write_to_mem m (wa (c + Z.of_nat (256 * i + 252))) (le4 (Z_to_bv 64 gv)))).
  { apply (mem_inv_store rsegs m _ _ MI). rewrite length_le4. exact SOK. }
  assert (ST2 : stk rsegs (write_to_mem m (wa (c + Z.of_nat (256 * i + 252))) (le4 (Z_to_bv 64 gv))) lo
                  (bv_unsigned sp0)) by (apply stk_write; [exact ST | lia | rewrite length_le4; lia]).
  step.
  rewrite HMH.
  eapply (mfu_tail n) with (Fc := F) (fcc := fc) (mcut := mcut) (p := p) (mc := mc) (cur := cur).
  - exact HT.
  - exact Hn.
  - exact Hne.
  - exact HL.
  - unfold mfu_mid. split; [exact MU2|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    exists (upd_bytes bs (256 * i + 252)%nat (le4 (Z_to_bv 64 gv))). split; [exact HB2 | exact HENC].
  - unfold saved_at, M_FILE_SAVE. exact HSV2.
  - exact C08'.
  - unfold cell8, MC_KNOCK. exact C10'.
  - unfold cell8, MC_KNOCK. exact C18'.
  - unfold cell8, MC_READING. exact C20'.
  - unfold cell8, MC_N. exact C28'.
  - unfold cell8, cur_ptr, mseg_addr, MSEG_SIZE. exact C30'.
  - exact HGR.
  - unfold cur_ok. exact Hi.
  - exact HRF.
  - exact HOV.
  - exact FRM.
  - exact FREL.
  - unfold m_file_regs, MC_N, BLANK_MASK. repeat split; reflexivity.
Qed.

(** ** 0x144fc: m_find found entry i *)
Lemma hdb_found : forall (m : word -> option byte) (i : nat)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s4 t3 t4 t5 t6 : word),
  m_find mc nm = Some i -> hdb_mid m mc cur -> frm0 fc ->
  evt rsegs hdb_post
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 (c + 256 * Z.of_nat i)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 (Z_to_bv 64 (Z.of_nat (length nm)))
             (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23) (Z_to_bv 64 (c + 8192)) (Z_to_bv 64 BLANK_MASK)
             (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 0x144fc) fc None m (seg_rom rsegs)).
Proof.
  intros m i ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s4 t3 t4 t5 t6 HFI MID FRM.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hc16 & Hl0 & Hl1 & Hp1 & Hp2 & Hr1 & Hon & Href & Hovf).
  pose proof hdb_apart as AP. pose proof hdb_apartp as APP. pose proof (u64_range sp) as Rsp.
  destruct MID as (MU & WM & MI & ST & HMA & HSV & C08 & C10 & C18 & C20 & C28 & C30 & C98 & NMB).
  unfold cell8 in C08, C10, C18, C20, C28, C30, C98. unfold saved_at in HSV.
  assert (Hi : (i < length (mc_seg mc))%nat) by (eapply m_find_lt; exact HFI).
  destruct (hdb_blk m mc HMA) as (bs & HB & HBL & HE & HGB & Hgen).
  destruct (hdb_seg_gen m mc bs i HB HBL HE Hi) as (GB & Hgi & Hi32).
  pose proof (hdb_wr m WM) as HWR.
  pose proof hdb_nmb_len as Lnmb.
  step. rewrite (unsigned_lit (c + 256 * Z.of_nat i)) by lia.
  replace (Z.land (c + 256 * Z.of_nat i) 3) with 0
    by (symmetry; apply hb_land3; [lia | Z.div_mod_to_equations; lia]).
  step.
  step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
  assert (SOK : store_ok rsegs m (Z_to_bv 64 (bv_unsigned sp + 48)) 8 = true).
  { replace (Z_to_bv 64 (bv_unsigned sp + 48)) with (wa (lo + (bv_unsigned sp + 48 - lo)))
      by (unfold wa; f_equal; lia).
    apply (wr_at_store_ok rsegs m lo (bv_unsigned sp0 - lo) (bv_unsigned sp + 48 - lo) 8);
      [apply hb_wr_of_stk; exact ST | lia | lia]. }
  step.
  hdb_addr (bv_unsigned sp + 48).
  assert (KF : forall A (bs0 : list byte),
                 bytes_at rsegs m A bs0 ->
                 (A + Z.of_nat (length bs0) <= bv_unsigned sp + 48 \/ bv_unsigned sp + 56 <= A) ->
                 bytes_at rsegs (write_to_mem m (wa (bv_unsigned sp + 48))
                                   (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i)))) A bs0)
    by (intros A bs0 HBa HD; apply (hdb_keepf m A bs0); [exact HBa | rewrite length_le8; lia | exact HD]).
  pose proof (KF _ _ HSV ltac:(rewrite hb_saved_len; cbn [length]; lia)) as HSV1.
  pose proof (KF _ _ C08 ltac:(rewrite length_le8; lia)) as C08'.
  pose proof (KF _ _ C10 ltac:(rewrite length_le8; lia)) as C10'.
  pose proof (KF _ _ C18 ltac:(rewrite length_le8; lia)) as C18'.
  pose proof (KF _ _ C20 ltac:(rewrite length_le8; lia)) as C20'.
  pose proof (KF _ _ C28 ltac:(rewrite length_le8; lia)) as C28'.
  pose proof (KF _ _ C98 ltac:(rewrite length_le8; lia)) as C98'.
  pose proof (KF _ _ HB ltac:(lia)) as HB'.
  pose proof (KF _ _ GB ltac:(rewrite length_le4; lia)) as GB'.
  pose proof (KF _ _ HGB ltac:(rewrite length_le4; lia)) as HGB'.
  pose proof (KF _ _ NMB ltac:(rewrite Lnmb; lia)) as NMB'.
  assert (C30' : bytes_at rsegs (write_to_mem m (wa (bv_unsigned sp + 48))
                                   (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i)))) (bv_unsigned sp + 48)
                   (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i))))
    by (apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (MU1 : munch (mfu_W (bv_unsigned sp0) c k0 mc false) mcut
                  (write_to_mem m (wa (bv_unsigned sp + 48)) (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i))))).
  { apply (munch_write _ mcut m); [exact MU | lia | rewrite length_le8; lia|].
    rewrite length_le8. apply hb_in_frame; lia. }
  assert (WM1 : wmono rsegs mcut (write_to_mem m (wa (bv_unsigned sp + 48))
                                    (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i))))) by (apply wmono_write; exact WM).
  assert (MI1 : mem_inv rsegs (write_to_mem m (wa (bv_unsigned sp + 48))
                                 (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i))))).
  { apply (mem_inv_store rsegs m _ _ MI). rewrite length_le8. exact SOK. }
  assert (ST1 : stk rsegs (write_to_mem m (wa (bv_unsigned sp + 48))
                             (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i)))) lo (bv_unsigned sp0))
    by (apply stk_write; [exact ST | lia | rewrite length_le8; lia]).
  assert (HWR1 : wr_at rsegs (write_to_mem m (wa (bv_unsigned sp + 48))
                                (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i)))) c 9236)
    by (apply hdb_wr; exact WM1).
  set (m1 := write_to_mem m (wa (bv_unsigned sp + 48)) (le8 (Z_to_bv 64 (c + 256 * Z.of_nat i)))) in *.
  pose proof (hb_rd4 m1 (c + 256 * Z.of_nat i + 252)
                (Z_to_bv 64 (ms_gen (nth i (mc_seg mc) mseg_d))) GB') as RDSG.
  pose proof (hb_rd4 m1 (c + 9136) (Z_to_bv 64 (mc_gen mc)) HGB') as RDCG.
  step. step.
  step. if_cases K2; cbv iota.
  - (* the gens differ *)
    zify_cond K2.
    assert (NE : (ms_gen (nth i (mc_seg mc) mseg_d) =? mc_gen mc) = false).
    { apply Z.eqb_neq. intros EQ. apply K2. apply (proj2 (hb_sx32_eq_iff _ _ Hgi Hgen)). exact EQ. }
    eapply hdb_gen with (m := m1) (F' := F) (fc' := fc) (mcf := m_upd mc i (ms_with_gen (mc_gen mc)))
      (i := i) (bs := bs) (gv := mc_gen mc).
    + unfold mh_find. rewrite HFI, NE. reflexivity.
    + apply m_upd_grows.
    + unfold m_upd, m_set_segs. cbn [mc_refused]. lia.
    + unfold m_upd, m_set_segs. cbn [mc_overflow]. lia.
    + unfold m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length. exact Hi.
    + exact Hi32.
    + exact HB'.
    + exact HBL.
    + exact HWR1.
    + exact HGB'.
    + exact Hgen.
    + apply (mconf_enc_seg false mc bs i (ms_with_gen (mc_gen mc)) 252 (le4 (Z_to_bv 64 (mc_gen mc))) HE Hi);
        [rewrite length_le4; lia|].
      intros fb Hfb. change 252%nat with (Z.to_nat MS_GEN). apply mseg_enc_gen; [exact Hfb | exact Hgen].
    + rewrite (hb_mfu_W_len_eq _ _ _ (m_upd mc i (ms_with_gen (mc_gen mc))) mc);
        [exact MU1 | unfold m_upd, m_set_segs; cbn [mc_seg]; rewrite upd_nth_length; reflexivity
        | reflexivity].
    + exact WM1.
    + exact MI1.
    + exact ST1.
    + unfold saved_at. exact HSV1.
    + exact C08'.
    + exact C10'.
    + exact C18'.
    + exact C20'.
    + exact C28'.
    + exact C30'.
    + exact FRM.
    + intros k Hk. reflexivity.
  - (* the gens agree: m_refuse *)
    zify_cond K2.
    assert (EQ : ms_gen (nth i (mc_seg mc) mseg_d) = mc_gen mc)
      by (apply (proj1 (hb_sx32_eq_iff _ _ Hgi Hgen)); exact K2).
    assert (EB : (ms_gen (nth i (mc_seg mc) mseg_d) =? mc_gen mc) = true) by (apply Z.eqb_eq; exact EQ).
    assert (MID1 : mfu_mid mcut m1 (bv_unsigned sp0) lo c k0 mc false).
    { unfold mfu_mid. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      exists bs. split; [exact HB' | exact HE]. }
    step. step. step.
    eapply (mfu_refuse HMR).
    + exact HL.
    + exact Hne.
    + exact MID1.
    + apply mf_grows_refl.
    + reflexivity.
    + exact FRM.
    + rewrite unsigned_lit by lia; reflexivity.
    + rewrite unsigned_lit by lia; reflexivity.
    + intros m2 F2 fc2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MID2 MUr WMr FRM2 FREL2.
      rewrite ret_pc_even by (try lia; reflexivity).
      destruct MID2 as (MU2 & WM2 & MI2 & ST2 & HMA2).
      destruct (hdb_blk m2 (m_refuse mc (line + 1) false) HMA2) as (bs2 & HB2 & HBL2 & HE2 & HGB2 & Hgen2).
      unfold m_refuse in HGB2, Hgen2. cbn [mc_gen] in HGB2, Hgen2.
      step.
      eapply hdb_gen with (m := m2) (F' := F2) (fc' := fc2)
        (mcf := m_upd (m_refuse mc (line + 1) false) i (ms_with_gen (mc_gen mc)))
        (i := i) (bs := bs2) (gv := mc_gen mc).
      * unfold mh_find. rewrite HFI, EB. reflexivity.
      * eapply mf_grows_trans; [apply m_refuse_grows | apply m_upd_grows].
      * unfold m_upd, m_set_segs, m_refuse. cbn [mc_refused]. lia.
      * unfold m_upd, m_set_segs, m_refuse. cbn [mc_overflow]. lia.
      * unfold m_upd, m_set_segs, m_refuse. cbn [mc_seg]. rewrite upd_nth_length. exact Hi.
      * exact Hi32.
      * exact HB2.
      * exact HBL2.
      * apply hdb_wr. eapply wmono_trans; [exact WM1 | exact WMr].
      * exact HGB2.
      * exact Hgen.
      * apply (mconf_enc_seg false (m_refuse mc (line + 1) false) bs2 i (ms_with_gen (mc_gen mc)) 252
                 (le4 (Z_to_bv 64 (mc_gen mc))) HE2);
          [unfold m_refuse; cbn [mc_seg]; exact Hi | rewrite length_le4; lia|].
        intros fb Hfb. change 252%nat with (Z.to_nat MS_GEN). apply mseg_enc_gen; [exact Hfb | exact Hgen].
      * rewrite (hb_mfu_W_len_eq _ _ _ (m_upd (m_refuse mc (line + 1) false) i (ms_with_gen (mc_gen mc)))
                   (m_refuse mc (line + 1) false));
          [exact MU2 | unfold m_upd, m_set_segs; cbn [mc_seg]; rewrite upd_nth_length; reflexivity
          | reflexivity].
      * eapply wmono_trans; [exact WM1 | exact WMr].
      * exact MI2.
      * exact ST2.
      * unfold saved_at. eapply (hdb_keepr m1 m2 mc); [exact HSV1 | exact MUr | lia |
          rewrite hb_saved_len; cbn [length]; lia].
      * unfold cell8. eapply (hdb_keepr m1 m2 mc); [exact C08' | exact MUr | lia | rewrite length_le8; lia].
      * unfold cell8. eapply (hdb_keepr m1 m2 mc); [exact C10' | exact MUr | lia | rewrite length_le8; lia].
      * unfold cell8. eapply (hdb_keepr m1 m2 mc); [exact C18' | exact MUr | lia | rewrite length_le8; lia].
      * unfold cell8. eapply (hdb_keepr m1 m2 mc); [exact C20' | exact MUr | lia | rewrite length_le8; lia].
      * unfold cell8. eapply (hdb_keepr m1 m2 mc); [exact C28' | exact MUr | lia | rewrite length_le8; lia].
      * unfold cell8. eapply (hdb_keepr m1 m2 mc); [exact C30' | exact MUr | lia | rewrite length_le8; lia].
      * exact FRM2.
      * exact FREL2.
Qed.

(** ** 0x14900: a new entry at index nn = c->n < 32 *)
Lemma hdb_new : forall (m : word -> option byte) (nn : nat)
    (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 t3 t4 t5 t6 : word),
  m_find mc nm = None -> length (mc_seg mc) = nn -> (nn < 32)%nat -> hdb_mid m mc cur -> frm0 fc ->
  evt rsegs hdb_post
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 (Z.of_nat nn)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1)
             (Z_to_bv 64 (Z.of_nat (length nm))) (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + 8192)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14900) fc None m (seg_rom rsegs)).
Proof.
  intros m nn ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 t3 t4 t5 t6 HFI Hnn Hlt MID FRM.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hc16 & Hl0 & Hl1 & Hp1 & Hp2 & Hr1 & Hon & Href & Hovf).
  pose proof hdb_apart as AP. pose proof hdb_apartp as APP. pose proof hdb_apartpc as APC.
  pose proof (u64_range sp) as Rsp. pose proof hdb_nmb_len as Lnmb. pose proof hdb_nm_range as HR256.
  destruct MID as (MU & WM & MI & ST & HMA & HSV & C08 & C10 & C18 & C20 & C28 & C30 & C98 & NMB).
  unfold cell8 in C08, C10, C18, C20, C28, C30, C98. unfold saved_at in HSV.
  destruct (hdb_blk m mc HMA) as (bs & HB & HBL & HE & HGB & Hgen).
  pose proof (hdb_wr m WM) as HWR.
  set (gseg := ms_with_gen (mc_gen mc) (mseg0 nm)) in *.
  set (mcf := m_set_segs mc (mc_seg mc ++ [gseg])) in *.
  assert (Lmcf : length (mc_seg mcf) = S nn)
    by (unfold mcf, m_set_segs; cbn [mc_seg]; rewrite length_app; cbn [length]; lia).
  assert (Kmcf : length (mc_kept mcf) = length (mc_kept mc)) by (unfold mcf, m_set_segs; reflexivity).
  (* 0x14900 addi a1,a0,1 ; 0x14904 sw a1, 0(s8) *)
  step.
  assert (SOKn : store_ok rsegs m (wa (c + 8192)) 4 = true)
    by (apply (wr_at_store_ok rsegs m c 9236 8192 4 HWR); lia).
  step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?ww) _) =>
      replace ww with (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))
        by (symmetry; first [reflexivity | rewrite unsigned_lit by lia; reflexivity])
  end.
  hdb_addr (c + 8192).
  pose proof (bytes_at_write_inside rsegs m c bs 8192 (le4 (Z_to_bv 64 (Z.of_nat nn + 1))) HB
                ltac:(lia) ltac:(rewrite length_le4; lia)) as HB1.
  idtac.
  assert (KB : forall A (bs0 : list byte), bytes_at rsegs m A bs0 -> bv_unsigned sp <= A ->
                 A + Z.of_nat (length bs0) <= bv_unsigned sp0 ->
                 bytes_at rsegs (write_to_mem m (wa (c + 8192)) (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))) A bs0).
  { intros A bs0 HBa H1 H2. apply (hdb_keepb m A bs0); try lia; [exact HBa|]. rewrite length_le4. lia. }
  pose proof (KB _ _ HSV ltac:(lia) ltac:(rewrite hb_saved_len; cbn [length]; lia)) as HSV1.
  pose proof (KB _ _ C08 ltac:(lia) ltac:(rewrite length_le8; lia)) as C08'.
  pose proof (KB _ _ C10 ltac:(lia) ltac:(rewrite length_le8; lia)) as C10'.
  pose proof (KB _ _ C18 ltac:(lia) ltac:(rewrite length_le8; lia)) as C18'.
  pose proof (KB _ _ C20 ltac:(lia) ltac:(rewrite length_le8; lia)) as C20'.
  pose proof (KB _ _ C28 ltac:(lia) ltac:(rewrite length_le8; lia)) as C28'.
  pose proof (KB _ _ C30 ltac:(lia) ltac:(rewrite length_le8; lia)) as C30'.
  pose proof (KB _ _ C98 ltac:(lia) ltac:(rewrite length_le8; lia)) as C98'.
  assert (HGB1 : bytes_at rsegs (write_to_mem m (wa (c + 8192))
                   (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))) (c + 9136) (le4 (Z_to_bv 64 (mc_gen mc))))
    by (apply (bytes_at_write_other rsegs m (c + 8192) _ _ _ HGB); rewrite ?length_le4; lia).
  assert (NMB1 : bytes_at rsegs (write_to_mem m (wa (c + 8192))
                   (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))) (p + Z.of_nat o) nmb)
    by (apply (bytes_at_write_other rsegs m (c + 8192) _ _ _ NMB); rewrite ?length_le4, ?Lnmb; lia).
  assert (MU1 : munch (mfu_W (bv_unsigned sp0) c k0 mcf false) mcut
                  (write_to_mem m (wa (c + 8192)) (le4 (Z_to_bv 64 (Z.of_nat nn + 1))))).
  { apply (munch_write _ mcut m).
    - eapply munch_weaken; [|exact MU]. apply hb_mfu_W_mono. unfold mf_grows. rewrite Lmcf, Kmcf. lia.
    - lia.
    - rewrite length_le4; lia.
    - rewrite length_le4. apply hb_in_hdr; lia. }
  assert (WM1 : wmono rsegs mcut (write_to_mem m (wa (c + 8192)) (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))))
    by (apply wmono_write; exact WM).
  assert (MI1 : mem_inv rsegs (write_to_mem m (wa (c + 8192)) (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))))
    by (apply (mem_inv_store rsegs m _ _ MI); rewrite length_le4; exact SOKn).
  assert (ST1 : stk rsegs (write_to_mem m (wa (c + 8192)) (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))) lo
                  (bv_unsigned sp0)) by (apply stk_write; [exact ST | lia | rewrite length_le4; lia]).
  assert (HWR1 : wr_at rsegs (write_to_mem m (wa (c + 8192)) (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))) c 9236)
    by (apply hdb_wr; exact WM1).
  set (bs1 := upd_bytes bs (Z.to_nat 8192) (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))) in *.
  assert (Lbs1 : Z.of_nat (length bs1) = 9236)
    by (unfold bs1; rewrite upd_bytes_length; [exact HBL | rewrite length_le4; lia]).
  set (m1 := write_to_mem m (wa (c + 8192)) (le4 (Z_to_bv 64 (Z.of_nat nn + 1)))) in *.
  (* 0x14908 a1 = 33 ; 0x1490c the bound trap ; 0x14910 slli ; 0x14914 ld a1,8(sp) ; 0x14918 the wrap trap *)
  step.
  step. if_cases K1; cbv iota;
    [exfalso; zify_cond K1; rewrite ?unsigned_lit, ?Z.mod_small in K1 by lia; lia|].
  step. rewrite (unsigned_lit (Z.of_nat nn)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  pose proof (hb_rd8 m1 (bv_unsigned sp + 8) (Z_to_bv 64 (- 1 - c)) C08') as RD08.
  step.
  step. if_cases K3; cbv iota;
    [exfalso; zify_cond K3; rewrite ?unsigned_lit_wrap in K3; Z.div_mod_to_equations; lia|].
  (* 0x1491c add s1,s0,a0 *)
  step. rewrite ?(unsigned_lit c), ?(unsigned_lit (Z.of_nat nn * 256)) by lia.
  (* the destination cell *)
  assert (GBYT : bytes_at rsegs m1 (c + Z.of_nat (256 * nn)) (firstn 256 (skipn (256 * nn) bs1)))
    by (apply hb_sub; [exact HB1 | lia]).
  assert (GLEN : length (firstn 256 (skipn (256 * nn) bs1)) = 256%nat)
    by (rewrite length_firstn, length_skipn; lia).
  assert (GRW : rw_cells rsegs m1 (c + Z.of_nat (256 * nn)) [CB 256 (firstn 256 (skipn (256 * nn) bs1))]).
  { apply hb_rw_CB; [exact GLEN | exact GBYT |].
    apply (hb_wr_at_sub m1 c 9236); [exact HWR1 | lia | lia]. }
  (* 0x14920 a2 = 256 ; 0x14924 a0 = s1 ; 0x14928 a1 = 0 ; 0x1492c jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply HMS with (junk := firstn 256 (skipn (256 * nn) bs1)).
    - rewrite !unsigned_lit by lia. change (Z.to_nat 256) with 256%nat.
      replace (c + Z.of_nat nn * 256) with (c + Z.of_nat (256 * nn)) by lia. exact GRW.
    - exact MI1. }
  intros ms' POST.
  destruct POST as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 &
                    Ems & MUs & WMs & MIs & RWs).
  subst ms'. rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !unsigned_lit in MUs by lia. rewrite !unsigned_lit in RWs by lia.
  change (Z.to_nat 256) with 256%nat in RWs. change (0 mod 256) with 0 in RWs.
  assert (KM : forall A (bs0 : list byte), bytes_at rsegs m1 A bs0 ->
                 (A + Z.of_nat (length bs0) <= c + Z.of_nat nn * 256 \/
                  c + Z.of_nat nn * 256 + 256 <= A) -> bytes_at rsegs m2 A bs0)
    by (intros A bs0 HBa HD; eapply hdb_keepw; [exact HBa | exact MUs | lia]).
  pose proof (KM _ _ HSV1 ltac:(rewrite hb_saved_len; cbn [length]; lia)) as HSV2.
  pose proof (KM _ _ C08' ltac:(rewrite length_le8; lia)) as C08''.
  pose proof (KM _ _ C10' ltac:(rewrite length_le8; lia)) as C10''.
  pose proof (KM _ _ C18' ltac:(rewrite length_le8; lia)) as C18''.
  pose proof (KM _ _ C20' ltac:(rewrite length_le8; lia)) as C20''.
  pose proof (KM _ _ C28' ltac:(rewrite length_le8; lia)) as C28''.
  pose proof (KM _ _ C30' ltac:(rewrite length_le8; lia)) as C30''.
  pose proof (KM _ _ C98' ltac:(rewrite length_le8; lia)) as C98''.
  pose proof (KM _ _ HGB1 ltac:(rewrite length_le4; lia)) as HGB2.
  pose proof (KM _ _ NMB1 ltac:(rewrite Lnmb; lia)) as NMB2.
  assert (PREB : bytes_at rsegs m2 c (firstn (256 * nn) bs1)).
  { apply KM; [|rewrite length_firstn; lia].
    apply (bytes_at_app rsegs m1 c (firstn (256 * nn) bs1) (skipn (256 * nn) bs1)).
    rewrite firstn_skipn. exact HB1. }
  assert (POSTB : bytes_at rsegs m2 (c + Z.of_nat (256 * nn + 256)) (skipn (256 * nn + 256) bs1)).
  { apply KM; [|rewrite length_skipn; lia].
    replace (skipn (256 * nn + 256) bs1)
      with (firstn (length bs1 - (256 * nn + 256)) (skipn (256 * nn + 256) bs1))
      by (rewrite firstn_all2; [reflexivity | rewrite length_skipn; lia]).
    apply hb_sub; [exact HB1 | lia]. }
  assert (STs : stk rsegs m2 lo (bv_unsigned sp0))
    by (eapply stk_transport_disjoint; [exact ST1 | exact MUs | exact WMs |
          apply hdb_stk_dj; lia]).
  assert (MUs2 : munch (mfu_W (bv_unsigned sp0) c k0 mcf false) mcut m2).
  { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [|exact MUs].
    eapply hb_fp_seg with (j := nn); [rewrite Lmcf; lia | lia | lia]. }
  assert (WMs2 : wmono rsegs mcut m2) by (eapply wmono_trans; [exact WM1 | exact WMs]).
  (* 0x14930 ld a1, 0x98(sp) *)
  pose proof (hb_rd8 m2 (bv_unsigned sp + 152) (Z_to_bv 64 (p + Z.of_nat o)) C98'') as RD98.
  step.
  (* 0x14934 sd s1, 0x30(sp) *)
  assert (SOK2 : store_ok rsegs m2 (Z_to_bv 64 (bv_unsigned sp + 48)) 8 = true).
  { replace (Z_to_bv 64 (bv_unsigned sp + 48)) with (wa (lo + (bv_unsigned sp + 48 - lo)))
      by (unfold wa; f_equal; lia).
    apply (wr_at_store_ok rsegs m2 lo (bv_unsigned sp0 - lo) (bv_unsigned sp + 48 - lo) 8);
      [apply hb_wr_of_stk; exact STs | lia | lia]. }
  step.
  hdb_addr (bv_unsigned sp + 48).
  assert (KF2 : forall A (bs0 : list byte), bytes_at rsegs m2 A bs0 ->
                  (A + Z.of_nat (length bs0) <= bv_unsigned sp + 48 \/ bv_unsigned sp + 56 <= A) ->
                  bytes_at rsegs (write_to_mem m2 (wa (bv_unsigned sp + 48))
                                    (le8 (Z_to_bv 64 (c + Z.of_nat nn * 256)))) A bs0)
    by (intros A bs0 HBa HD; apply (hdb_keepf m2 A bs0); [exact HBa | rewrite length_le8; lia | exact HD]).
  pose proof (KF2 _ _ HSV2 ltac:(rewrite hb_saved_len; cbn [length]; lia)) as HSV3.
  pose proof (KF2 _ _ C08'' ltac:(rewrite length_le8; lia)) as C08'''.
  pose proof (KF2 _ _ C10'' ltac:(rewrite length_le8; lia)) as C10'''.
  pose proof (KF2 _ _ C18'' ltac:(rewrite length_le8; lia)) as C18'''.
  pose proof (KF2 _ _ C20'' ltac:(rewrite length_le8; lia)) as C20'''.
  pose proof (KF2 _ _ C28'' ltac:(rewrite length_le8; lia)) as C28'''.
  pose proof (KF2 _ _ HGB2 ltac:(rewrite length_le4; lia)) as HGB3.
  pose proof (KF2 _ _ NMB2 ltac:(rewrite Lnmb; lia)) as NMB3.
  pose proof (KF2 _ _ PREB ltac:(rewrite length_firstn; lia)) as PREB3.
  pose proof (KF2 _ _ POSTB ltac:(rewrite length_skipn; lia)) as POSTB3.
  pose proof (KF2 _ _ (hb_rw_CB_bytes m2 (c + Z.of_nat nn * 256) 256 (repeat (Z_to_bv 8 0) 256) RWs)
                ltac:(rewrite repeat_length; lia)) as ZB3.
  assert (C30''' : bytes_at rsegs (write_to_mem m2 (wa (bv_unsigned sp + 48))
                                    (le8 (Z_to_bv 64 (c + Z.of_nat nn * 256)))) (bv_unsigned sp + 48)
                     (le8 (Z_to_bv 64 (c + Z.of_nat nn * 256))))
    by (apply bytes_at_write_same; [lia | rewrite length_le8; lia]).
  assert (MU3 : munch (mfu_W (bv_unsigned sp0) c k0 mcf false) mcut
                  (write_to_mem m2 (wa (bv_unsigned sp + 48)) (le8 (Z_to_bv 64 (c + Z.of_nat nn * 256))))).
  { apply (munch_write _ mcut m2); [exact MUs2 | lia | rewrite length_le8; lia|].
    rewrite length_le8. apply hb_in_frame; lia. }
  assert (WM3 : wmono rsegs mcut (write_to_mem m2 (wa (bv_unsigned sp + 48))
                                    (le8 (Z_to_bv 64 (c + Z.of_nat nn * 256)))))
    by (apply wmono_write; exact WMs2).
  assert (MI3 : mem_inv rsegs (write_to_mem m2 (wa (bv_unsigned sp + 48))
                                 (le8 (Z_to_bv 64 (c + Z.of_nat nn * 256)))))
    by (apply (mem_inv_store rsegs m2 _ _ MIs); rewrite length_le8; exact SOK2).
  assert (ST3 : stk rsegs (write_to_mem m2 (wa (bv_unsigned sp + 48))
                            (le8 (Z_to_bv 64 (c + Z.of_nat nn * 256)))) lo (bv_unsigned sp0))
    by (apply stk_write; [exact STs | lia | rewrite length_le8; lia]).
  set (m3 := write_to_mem m2 (wa (bv_unsigned sp + 48)) (le8 (Z_to_bv 64 (c + Z.of_nat nn * 256)))) in *.
  assert (HWR3 : wr_at rsegs m3 c 9236) by (apply hdb_wr; exact WM3).
  (* the memcpy destination *)
  pose proof ZB3 as ZB3'.
  rewrite <- (firstn_skipn (length nm) (repeat (Z_to_bv 8 0) 256)) in ZB3'.
  apply bytes_at_app in ZB3'. destruct ZB3' as [DSTB TAILB3].
  rewrite length_firstn, repeat_length in TAILB3.
  replace (Nat.min (length nm) 256) with (length nm) in TAILB3 by lia.
  assert (DSTRW : rw_cells rsegs m3 (c + Z.of_nat (256 * nn))
                    [CB (length nm) (firstn (length nm) (repeat (Z_to_bv 8 0) 256))]).
  { apply hb_rw_CB; [rewrite length_firstn, repeat_length; lia | |].
    - replace (c + Z.of_nat (256 * nn)) with (c + Z.of_nat nn * 256) by lia. exact DSTB.
    - apply (hb_wr_at_sub m3 c 9236); [exact HWR3 | lia | lia]. }
  (* 0x14938 a0 = s1 ; 0x1493c a2 = s5 ; 0x14940 jal memcpy *)
  step. step. step.
  eapply evt_cut.
  { eapply HMC with (src := nmb) (junk := firstn (length nm) (repeat (Z_to_bv 8 0) 256)).
    - rewrite unsigned_lit by lia. exact NMB3.
    - rewrite unsigned_lit by lia. rewrite Nat2Z.id. exact Lnmb.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id.
      replace (c + Z.of_nat nn * 256) with (c + Z.of_nat (256 * nn)) by lia. exact DSTRW.
    - rewrite !unsigned_lit by lia. lia.
    - exact MI3. }
  intros ms2 POST2.
  destruct POST2 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 &
                     Ems2 & MUc & WMc & MIc & RWc & SRC).
  subst ms2. rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in RWc by lia. rewrite Nat2Z.id in RWc.
  assert (KC : forall A (bs0 : list byte), bytes_at rsegs m3 A bs0 ->
                 (A + Z.of_nat (length bs0) <= c + Z.of_nat nn * 256 \/
                  c + Z.of_nat nn * 256 + Z.of_nat (length nm) <= A) -> bytes_at rsegs m4 A bs0)
    by (intros A bs0 HBa HD; eapply hdb_keepw; [exact HBa | exact MUc | lia]).
  pose proof (KC _ _ HSV3 ltac:(rewrite hb_saved_len; cbn [length]; lia)) as HSV4.
  pose proof (KC _ _ C08''' ltac:(rewrite length_le8; lia)) as C08f.
  pose proof (KC _ _ C10''' ltac:(rewrite length_le8; lia)) as C10f.
  pose proof (KC _ _ C18''' ltac:(rewrite length_le8; lia)) as C18f.
  pose proof (KC _ _ C20''' ltac:(rewrite length_le8; lia)) as C20f.
  pose proof (KC _ _ C28''' ltac:(rewrite length_le8; lia)) as C28f.
  pose proof (KC _ _ C30''' ltac:(rewrite length_le8; lia)) as C30f.
  pose proof (KC _ _ HGB3 ltac:(rewrite length_le4; lia)) as HGBf.
  pose proof (KC _ _ PREB3 ltac:(rewrite length_firstn; lia)) as PREBf.
  pose proof (KC _ _ POSTB3 ltac:(rewrite length_skipn; lia)) as POSTBf.
  pose proof (KC _ _ TAILB3 ltac:(rewrite length_skipn, repeat_length; lia)) as TAILBf.
  pose proof (hb_rw_CB_bytes m4 (c + Z.of_nat nn * 256) (length nm) nmb RWc) as MIDB1.
  set (EN := upd_bytes (repeat (Z_to_bv 8 0) 256) 0 nmb) in *.
  assert (LEN : length EN = 256%nat)
    by (unfold EN; rewrite upd_bytes_length; [apply repeat_length | rewrite repeat_length, Lnmb; lia]).
  assert (MIDB : bytes_at rsegs m4 (c + Z.of_nat (256 * nn)) EN).
  { unfold EN, upd_bytes. rewrite firstn_O. cbn [app Nat.add]. rewrite Lnmb.
    replace (c + Z.of_nat (256 * nn)) with (c + Z.of_nat nn * 256) by lia.
    apply bytes_at_app. split; [exact MIDB1|]. rewrite Lnmb. exact TAILBf. }
  assert (BLKf : bytes_at rsegs m4 c (firstn (256 * nn) bs1 ++ EN ++ skipn (256 * nn + 256) bs1)).
  { apply bytes_at_app. split; [exact PREBf|]. rewrite length_firstn.
    replace (Nat.min (256 * nn) (length bs1)) with (256 * nn)%nat by lia.
    apply bytes_at_app. split; [exact MIDB|].
    rewrite LEN. replace (c + Z.of_nat (256 * nn) + Z.of_nat 256)
      with (c + Z.of_nat (256 * nn + 256)) by lia. exact POSTBf. }
  assert (EQB : forall X : list byte, length X = 256%nat ->
             firstn (256 * nn) bs1 ++ X ++ skipn (256 * nn + 256) bs1 = upd_bytes bs1 (256 * nn) X)
    by (intros X HX; unfold upd_bytes; rewrite HX; reflexivity).
  (* 0x14944 s4 = 1 ; 0x14948 *)
  step.
  eapply hdb_gen with (m := m4) (F' := F) (fc' := fc) (mcf := mcf) (i := nn)
    (bs := firstn (256 * nn) bs1 ++ EN ++ skipn (256 * nn + 256) bs1) (gv := mc_gen mc).
  - unfold mh_find. rewrite HFI.
    replace (32 <=? length (mc_seg mc))%nat with false by (symmetry; apply Nat.leb_gt; lia).
    rewrite Hnn. reflexivity.
  - unfold mf_grows. rewrite Lmcf, Kmcf. lia.
  - unfold mcf, m_set_segs. cbn [mc_refused]. lia.
  - unfold mcf, m_set_segs. cbn [mc_overflow]. lia.
  - rewrite Lmcf. lia.
  - lia.
  - exact BLKf.
  - rewrite !length_app, length_firstn, length_skipn, LEN. lia.
  - apply hdb_wr. eapply wmono_trans; [exact WM3 | exact WMc].
  - exact HGBf.
  - exact Hgen.
  - replace (256 * nn + 252)%nat with (256 * nn + 252)%nat by lia.
    rewrite (hb_upd_split (firstn (256 * nn) bs1) EN (skipn (256 * nn + 256) bs1)
               (le4 (Z_to_bv 64 (mc_gen mc))) (256 * nn));
      [ | rewrite length_firstn; lia | exact LEN | rewrite length_le4; lia].
    rewrite (EQB (upd_bytes EN 252 (le4 (Z_to_bv 64 (mc_gen mc)))))
      by (rewrite upd_bytes_length; [exact LEN | rewrite LEN, length_le4; lia]).
    unfold bs1. rewrite <- hb_upd_bytes_comm;
      [ | rewrite upd_bytes_length; [lia | rewrite LEN, length_le4; lia]
      | rewrite length_le4; lia].
    rewrite <- Hnn.
    unfold mcf, gseg. apply (mconf_enc_append false mc bs); [exact HE | lia|].
    pose proof (mseg_enc_new nm (mc_gen mc) ltac:(lia) Hnm0 HR256 Hgen) as MN.
    replace (zb nm) with nmb in MN by (rewrite <- Hnmbz; symmetry; apply hb_zb_zs).
    change (Z.to_nat MS_GEN) with 252%nat in MN. exact MN.
  - eapply munch_trans; [exact MU3|]. eapply munch_weaken; [|exact MUc].
    eapply hb_fp_seg with (j := nn); [rewrite Lmcf; lia | lia | lia].
  - eapply wmono_trans; [exact WM3 | exact WMc].
  - exact MIc.
  - eapply stk_transport_disjoint; [exact ST3 | exact MUc | exact WMc | apply hdb_stk_dj; lia].
  - unfold saved_at. exact HSV4.
  - exact C08f.
  - exact C10f.
  - exact C18f.
  - exact C20f.
  - exact C28f.
  - replace (c + 256 * Z.of_nat nn) with (c + Z.of_nat nn * 256) by lia. exact C30f.
  - exact FRM.
  - intros k Hk. reflexivity.
Qed.

(** ** 0x148d4: m_find found nothing *)
Lemma hdb_notfound : forall (m : word -> option byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s4 t3 t4 t5 t6 : word),
  m_find mc nm = None -> hdb_mid m mc cur -> frm0 fc ->
  evt rsegs hdb_post
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 (Z_to_bv 64 (Z.of_nat (length nm)))
             (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23) (Z_to_bv 64 (c + 8192)) (Z_to_bv 64 BLANK_MASK)
             (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 0x148d4) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s4 t3 t4 t5 t6 HFI MID FRM.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hc16 & Hl0 & Hl1 & Hp1 & Hp2 & Hr1 & Hon & Href & Hovf).
  pose proof hdb_apart as AP. pose proof (u64_range sp) as Rsp.
  pose proof MID as MIDc.
  destruct MID as (MU & WM & MI & ST & HMA & HSV & C08 & C10 & C18 & C20 & C28 & C30 & C98 & NMB).
  unfold cell8 in C08, C10, C18, C20, C28, C30, C98. unfold saved_at in HSV.
  destruct (hdb_blk m mc HMA) as (bs & HB & HBL & HE & HGB & Hgen).
  pose proof (hdb_wr m WM) as HWR.
  assert (Hnn32 : (length (mc_seg mc) <= 32)%nat) by (destruct HE as (_ & H32 & _); exact H32).
  pose proof (mconf_rd_n rsegs false m c mc HMA) as RDN. unfold MC_N in RDN.
  step. rewrite (hb_sx32_small (Z.of_nat (length (mc_seg mc)))) by lia.
  step.
  step. if_cases K; cbv iota.
  - (* n < 32: the new entry *)
    zify_cond K. rewrite ?hb_signed_lit in K by lia.
    eapply hdb_new with (nn := length (mc_seg mc));
      [exact HFI | reflexivity | lia | exact MIDc | exact FRM].
  - (* n >= 32: overflow and a refusal *)
    zify_cond K. rewrite ?hb_signed_lit in K by lia.
    assert (Hnn : length (mc_seg mc) = 32%nat) by lia.
    pose proof (mconf_rd_overflow rsegs false m c mc HMA) as RDO. unfold MC_OVERFLOW in RDO.
    assert (Hov : 0 <= mc_overflow mc < 2 ^ 32)
      by (destruct HE as (_ & _ & _ & _ & HO & _); destruct HO as [HO _]; exact HO).
    step. step.
    assert (SOKo : store_ok rsegs m (wa (c + 8196)) 4 = true)
      by (apply (wr_at_store_ok rsegs m c 9236 8196 4 HWR); lia).
    step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?ww) _) =>
        replace ww with (le4 (Z_to_bv 64 (mc_overflow mc + 1)))
          by (symmetry; first [reflexivity | apply (hb_le4_addi (mc_overflow mc) 1); lia])
    end.
    hdb_addr (c + 8196).
    set (mcov := mc_set_overflow (mc_overflow mc + 1) mc) in *.
    assert (Lov1 : length (mc_seg mcov) = length (mc_seg mc)) by reflexivity.
    assert (Lov2 : length (mc_kept mcov) = length (mc_kept mc)) by reflexivity.
    assert (HMAo : mconf_atp rsegs false (write_to_mem m (wa (c + 8196))
                     (le4 (Z_to_bv 64 (mc_overflow mc + 1)))) c mcov).
    { apply (mconf_atp_store rsegs false false m c mc mcov (c + 8196)); [exact HMA | lia |
        rewrite length_le4; unfold SEG_M_SIZE; lia|].
      intros bsx Hbsx. replace (Z.to_nat (c + 8196 - c)) with (Z.to_nat MC_OVERFLOW) by (unfold MC_OVERFLOW; f_equal; lia).
      apply mconf_enc_overflow; [exact Hbsx | lia]. }
    assert (KO : forall A (bs0 : list byte), bytes_at rsegs m A bs0 -> bv_unsigned sp <= A ->
                   A + Z.of_nat (length bs0) <= bv_unsigned sp0 ->
                   bytes_at rsegs (write_to_mem m (wa (c + 8196)) (le4 (Z_to_bv 64 (mc_overflow mc + 1)))) A bs0).
    { intros A bs0 HBa H1 H2. apply (hdb_keepb m A bs0); try lia; [exact HBa|]. rewrite length_le4. lia. }
    pose proof (KO _ _ HSV ltac:(lia) ltac:(rewrite hb_saved_len; cbn [length]; lia)) as HSV1.
    pose proof (KO _ _ C08 ltac:(lia) ltac:(rewrite length_le8; lia)) as C08'.
    pose proof (KO _ _ C10 ltac:(lia) ltac:(rewrite length_le8; lia)) as C10'.
    pose proof (KO _ _ C18 ltac:(lia) ltac:(rewrite length_le8; lia)) as C18'.
    pose proof (KO _ _ C20 ltac:(lia) ltac:(rewrite length_le8; lia)) as C20'.
    pose proof (KO _ _ C28 ltac:(lia) ltac:(rewrite length_le8; lia)) as C28'.
    assert (MU1 : munch (mfu_W (bv_unsigned sp0) c k0 mcov false) mcut
                    (write_to_mem m (wa (c + 8196)) (le4 (Z_to_bv 64 (mc_overflow mc + 1))))).
    { rewrite (hb_mfu_W_len_eq _ _ _ mcov mc false Lov1 Lov2).
      apply (munch_write _ mcut m); [exact MU | lia | rewrite length_le4; lia|].
      rewrite length_le4. apply hb_in_hdr; lia. }
    assert (WM1 : wmono rsegs mcut (write_to_mem m (wa (c + 8196)) (le4 (Z_to_bv 64 (mc_overflow mc + 1)))))
      by (apply wmono_write; exact WM).
    assert (MI1 : mem_inv rsegs (write_to_mem m (wa (c + 8196)) (le4 (Z_to_bv 64 (mc_overflow mc + 1)))))
      by (apply (mem_inv_store rsegs m _ _ MI); rewrite length_le4; exact SOKo).
    assert (ST1 : stk rsegs (write_to_mem m (wa (c + 8196)) (le4 (Z_to_bv 64 (mc_overflow mc + 1)))) lo
                    (bv_unsigned sp0)) by (apply stk_write; [exact ST | lia | rewrite length_le4; lia]).
    set (m1 := write_to_mem m (wa (c + 8196)) (le4 (Z_to_bv 64 (mc_overflow mc + 1)))) in *.
    step. step. step.
    eapply (mfu_refuse HMR).
    + exact HL.
    + exact Hne.
    + unfold mfu_mid. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      exact HMAo.
    + unfold mf_grows. rewrite Lov1, Lov2. lia.
    + reflexivity.
    + exact FRM.
    + rewrite unsigned_lit by lia; reflexivity.
    + rewrite unsigned_lit by lia; reflexivity.
    + intros m2 F2 fc2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MID2 MUr WMr FRM2 FREL2.
      rewrite ret_pc_even by (try lia; reflexivity).
      destruct MID2 as (MU2 & WM2 & MI2 & ST2 & HMA2).
      assert (SOK2 : store_ok rsegs m2 (Z_to_bv 64 (bv_unsigned sp + 48)) 8 = true).
      { replace (Z_to_bv 64 (bv_unsigned sp + 48)) with (wa (lo + (bv_unsigned sp + 48 - lo)))
          by (unfold wa; f_equal; lia).
        apply (wr_at_store_ok rsegs m2 lo (bv_unsigned sp0 - lo) (bv_unsigned sp + 48 - lo) 8);
          [apply hb_wr_of_stk; exact ST2 | lia | lia]. }
      assert (HSV2 : bytes_at rsegs m2 (bv_unsigned sp + 168)
                       (concat (map le8 [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0])))
        by (eapply (hdb_keepr m1 m2 mcov); [exact HSV1 | exact MUr | lia |
              rewrite hb_saved_len; cbn [length]; lia]).
      assert (C08b : bytes_at rsegs m2 (bv_unsigned sp + 8) (le8 (Z_to_bv 64 (- 1 - c))))
        by (eapply (hdb_keepr m1 m2 mcov); [exact C08' | exact MUr | lia | rewrite length_le8; lia]).
      assert (C10b : bytes_at rsegs m2 (bv_unsigned sp + 16) (le8 (Z_to_bv 64 (c + 9100))))
        by (eapply (hdb_keepr m1 m2 mcov); [exact C10' | exact MUr | lia | rewrite length_le8; lia]).
      assert (C18b : bytes_at rsegs m2 (bv_unsigned sp + 24) (le8 (Z_to_bv 64 (- 1 - (c + 9100)))))
        by (eapply (hdb_keepr m1 m2 mcov); [exact C18' | exact MUr | lia | rewrite length_le8; lia]).
      assert (C20b : bytes_at rsegs m2 (bv_unsigned sp + 32) (le8 (Z_to_bv 64 (c + 9140))))
        by (eapply (hdb_keepr m1 m2 mcov); [exact C20' | exact MUr | lia | rewrite length_le8; lia]).
      assert (C28b : bytes_at rsegs m2 (bv_unsigned sp + 40) (le8 (Z_to_bv 64 (c + 8192))))
        by (eapply (hdb_keepr m1 m2 mcov); [exact C28' | exact MUr | lia | rewrite length_le8; lia]).
      step.
      hdb_addr (bv_unsigned sp + 48).
      assert (KF2 : forall A (bs0 : list byte), bytes_at rsegs m2 A bs0 ->
                      (A + Z.of_nat (length bs0) <= bv_unsigned sp + 48 \/ bv_unsigned sp + 56 <= A) ->
                      bytes_at rsegs (write_to_mem m2 (wa (bv_unsigned sp + 48)) (le8 (Z_to_bv 64 0))) A bs0)
        by (intros A bs0 HBa HD; apply (hdb_keepf m2 A bs0); [exact HBa | rewrite length_le8; lia | exact HD]).
      step.
      cbv beta.
      replace (mh_find mc nm (line + 1)) with (m_refuse mcov (line + 1) false, @None nat)
        by (unfold mh_find; rewrite HFI;
            replace (32 <=? length (mc_seg mc))%nat with true by (symmetry; apply Nat.leb_le; lia);
            reflexivity).
      eapply (mfu_tail n) with (Fc := F) (fcc := fc) (mcut := mcut) (p := p) (mc := mc) (cur := cur).
      * exact HT.
      * exact Hn.
      * exact Hne.
      * exact HL.
      * unfold mfu_mid.
        split; [apply (munch_write _ mcut m2); [exact MU2 | lia | rewrite length_le8; lia|];
                rewrite length_le8; apply hb_in_frame; lia|].
        split; [apply wmono_write; exact WM2|].
        split; [apply (mem_inv_store rsegs m2 _ _ MI2); rewrite length_le8; exact SOK2|].
        split; [apply stk_write; [exact ST2 | lia | rewrite length_le8; lia]|].
        eapply mconf_atp_transport; [exact HMA2 |
          apply (munch_write [(bv_unsigned sp + 48, bv_unsigned sp + 56)] m2 m2);
            [apply munch_refl | lia | rewrite length_le8; lia |
             cbn [inside]; rewrite length_le8; left; lia] |].
        unfold SEG_M_SIZE. apply hdb_frm_dj; lia.
      * unfold saved_at, M_FILE_SAVE. apply KF2; [exact HSV2 | rewrite hb_saved_len; cbn [length]; lia].
      * unfold cell8. apply KF2; [exact C08b | rewrite length_le8; lia].
      * unfold cell8, MC_KNOCK. apply KF2; [exact C10b | rewrite length_le8; lia].
      * unfold cell8, MC_KNOCK. apply KF2; [exact C18b | rewrite length_le8; lia].
      * unfold cell8, MC_READING. apply KF2; [exact C20b | rewrite length_le8; lia].
      * unfold cell8, MC_N. apply KF2; [exact C28b | rewrite length_le8; lia].
      * unfold cell8, cur_ptr. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
      * eapply mf_grows_trans; [|apply m_refuse_grows]. unfold mf_grows. rewrite Lov1, Lov2. lia.
      * exact I.
      * unfold m_refuse. cbn [mc_refused]. unfold mcov, mc_set_overflow. cbn [mc_refused]. lia.
      * unfold m_refuse. cbn [mc_overflow]. unfold mcov, mc_set_overflow. cbn [mc_overflow]. lia.
      * exact FRM2.
      * exact FREL2.
      * unfold m_file_regs, MC_N, BLANK_MASK. repeat split; reflexivity.
Qed.

(** ** 0x144ec: the cut *)
Lemma hdb_main : forall (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s1 s4 t3 t4 t5 t6 : word), frm0 fc ->
  evt rsegs hdb_post
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 (Z_to_bv 64 (p + Z.of_nat o)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) s4 (Z_to_bv 64 (Z.of_nat (length nm)))
             (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23) (Z_to_bv 64 (c + 8192)) (Z_to_bv 64 BLANK_MASK)
             (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 0x144ec) fc None mcut (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s1 s4 t3 t4 t5 t6 FRM.
  destruct hdb_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hc16 & Hl0 & Hl1 & Hp1 & Hp2 & Hr1 & Hon & Href & Hovf).
  pose proof hdb_apart as AP. pose proof hdb_apartp as APP. pose proof (u64_range sp) as Rsp.
  pose proof hdb_nmb_len as Lnmb.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & HSV & C08 & C10 & C18 & C20 & C28 & C30 & Hcne & _ & _ & HMA & HWR & _ & _ & _ &
                 _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSO & MI).
  destruct HSO as (ST & _ & Hsp16 & Hrom).
  unfold cell8 in C08, C10, C18, C20, C28, C30, Hc98. unfold saved_at in HSV.
  destruct (stk_split rsegs mcut lo (bv_unsigned sp) (bv_unsigned sp0) ST ltac:(lia)) as [STlo SThi].
  (* 0x144ec mv a0,s0 ; 0x144f0 mv a2,s5 ; 0x144f4 jal m_find *)
  step. step. step.
  eapply evt_cut.
  { eapply HMF with (lo := lo) (mc := mc) (l := nmb).
    unfold m_find_pre, M_FIND_STACK. rewrite !unsigned_lit by lia.
    split; [exact Hcne|]. split; [exact Hc16|]. split; [exact HMA|].
    split; [unfold apart, SEG_M_SIZE; lia|].
    split; [exact Hnmbat|]. split; [rewrite Lnmb; reflexivity|].
    split; [unfold apart; lia|].
    split; [|exact MI].
    unfold stack_ok. split; [exact STlo|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
    intros a Ha. apply Hrom. lia. }
  intros ms' POST.
  destruct POST as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 &
                    Ems & MUs & WMs & MIs & STs & _).
  subst ms'. rewrite ret_pc_even by (try lia; reflexivity). unfold M_FIND_STACK in MUs.
  rewrite (unsigned_lit c) in * by lia. rewrite Hnmbz in *.
  (* the state after the call *)
  assert (KC : forall A (bs0 : list byte), bytes_at rsegs mcut A bs0 ->
                 (A + Z.of_nat (length bs0) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= A) ->
                 bytes_at rsegs m1 A bs0)
    by (intros A bs0 HBa HD; eapply hdb_keepw; [exact HBa | exact MUs | lia]).
  assert (MID : hdb_mid m1 mc cur).
  { unfold hdb_mid. split.
    - eapply munch_weaken; [|exact MUs]. apply hb_fp_frame; lia.
    - split; [exact WMs|]. split; [exact MIs|].
      split.
      { eapply stk_merge; [exact STs | | lia].
        eapply stk_transport_disjoint; [exact SThi | exact MUs | exact WMs |
          cbn [disjoint_from]; split; [lia | exact I]]. }
      split.
      { eapply mconf_atp_transport; [exact HMA | exact MUs |].
        unfold SEG_M_SIZE. cbn [disjoint_from]. split; [lia | exact I]. }
      split; [unfold saved_at; apply KC; [exact HSV | rewrite hb_saved_len; cbn [length]; lia]|].
      split; [unfold cell8; apply KC; [exact C08 | rewrite length_le8; lia]|].
      split; [unfold cell8; apply KC; [exact C10 | rewrite length_le8; lia]|].
      split; [unfold cell8; apply KC; [exact C18 | rewrite length_le8; lia]|].
      split; [unfold cell8; apply KC; [exact C20 | rewrite length_le8; lia]|].
      split; [unfold cell8; apply KC; [exact C28 | rewrite length_le8; lia]|].
      split; [unfold cell8; apply KC; [exact C30 | rewrite length_le8; lia]|].
      split; [unfold cell8; apply KC; [exact Hc98 | rewrite length_le8; lia]|].
      apply KC; [exact Hnmbat | rewrite Lnmb; lia]. }
  assert (Hseg32 : (length (mc_seg mc) <= 32)%nat).
  { destruct (hdb_blk mcut mc HMA) as (bsx & _ & _ & HEx & _). destruct HEx as (_ & H32 & _). exact H32. }
  unfold m_find_ptr.
  destruct (m_find mc nm) as [i|] eqn:HFI.
  - assert (Hi : (i < length (mc_seg mc))%nat) by (eapply m_find_lt; exact HFI).
    unfold mseg_addr, MSEG_SIZE.
    step. if_cases K; cbv iota;
      [exfalso; zify_cond K; rewrite ?unsigned_lit, ?Z.mod_small in K by lia; lia|].
    eapply hdb_found; [exact HFI | exact MID | exact FRM].
  - step. if_cases K; cbv iota;
      [|exfalso; zify_cond K; rewrite ?unsigned_lit, ?Z.mod_small in K by lia; lia].
    eapply hdb_notfound; [exact HFI | exact MID | exact FRM].
Qed.

End HdrB.

Lemma mfu_hdrb_holds : m_find_contract -> memset_contract -> memcpy_contract -> m_refuse_contract -> S_MFU_HDRB.
Proof.
  intros HMF HMS HMC HMR n HT.
  unfold H_MFU_HFIND.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest o nm
    Hn Hne HL HR Hs6 Hnm Ho Hfn Ha1 Hc98 Hs5.
  destruct HR as (E0 & E2 & E3 & E7 & E8 & E9 & E10 & E11).
  subst s0 s2 s3 s6 s7 s8 s9 s10 s11 s5 a1.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                 _ & _ & _ & _ & _ & _ & _ & HCS & _ & _ & HPE & _ & _ & _ & _).
  destruct HPE as (FRM & _).
  (* the name's bytes inside the text *)
  destruct HCS as (tb & sl & TBA & TZ & TN & _).
  assert (TL : length tb = length rest) by (rewrite <- TZ; symmetry; apply hb_zs_len).
  pose proof (hb_mf_line_le rest) as HLL.
  assert (Hor : (o + length nm <= length tb)%nat) by lia.
  unfold MFU_PC_HFIND, MC_N.
  eapply hdb_main with (nmb := firstn (length nm) (skipn o tb)) (n := n) (cur := cur).
  all: try eassumption.
  all: try assumption.
  all: try (rewrite hb_zs_fs, TZ; exact Hfn).
  all: try (rewrite <- Hfn; intros HIn; apply TN; eapply hb_in_fs; exact HIn).
  all: try (rewrite <- (hb_fs_app tb (ZERO :: sl) o (length nm) Hor);
            apply hb_sub; [exact TBA | rewrite length_app; cbn [length]; lia]).
  all: try exact FRM.
Qed.
