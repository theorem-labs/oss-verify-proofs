(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/CellsX.v; 569 of its 595 lines of code are new or changed and 31 lines of the source are left out. *)
(** Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c / pinned 1696d6c34ffd), the
    stretch ACC: the duplicate test and the append of the inlined m_declared (fuzz_segconf.c:361-368), pcs
    0x140cc .. 0x1419c, 0x141a0 and the out-of-line -1 exit 0x14254 .. 0x14260 (UBSan binary).
    Proves [V01D.V01_ACC] from the contracts of its two callees, strcmp (0x1f594) and
    memcpy (0x1eec8), both in [MainB.K_V01].

    Code (s0 = vid, the 20-byte mvlan (p, vid) at sp+0x60, frame cells from V01D.V01_cells):
      0x140cc ld a1,0x28(sp) (mn); 0x140d0 blez a1 -> 0x14140
      0x140d4-0x140f0 s8 = 0, s5 = 0, s3 = 20 mn (sgtz/neg/and/mul), s7 = mt
      DUP 0x140f4 (s8 = 20 k, s7 = mt + 20 k): bltu ~mt,s8 -> trap (dead: mt + 20 k is inside mt's block);
           beqz 0x40(sp) -> trap (dead: the cell holds 1); lw a0,0x10(s7) (mt[k].vid); sext.w a1,s0;
           bne a0,a1 -> a0 = 0; else strcmp(mt[k].parent, sp+0x60), seqz; s5 |= a0; s8, s7 += 20; bne s3,s8 -> DUP
      0x14138 ld a1,0x28(sp); bnez s5 -> 0x141a0 (a duplicate: the join with the same table)
      0x14140 ld a0,0x10(sp) (cap); bge a1,a0 -> 0x14254 (full: added = -1, s3 = m, the tail 0x141ac)
      0x14148-0x14174 a0 = mt + 20 mn; beqz a0 and the wrap test -> trap (dead: mt >= 4096, mt + 20 mn < 2^64)
      0x14178-0x14180 memcpy(mt + 20 mn, sp+0x60, 20)
      0x14184-0x1419c added = addiw added 1 (blt -> trap: dead, added <= 32), mn = addiw mn 1, both stored
      0x141a0 ld s3,0x50(sp); j 0x13fb8 (the join with tb ++ [(p, vid)] and added + 1).
    The dup loop has no early exit: its invariant is s5 = existsb (the model's duplicate test) over mt[0 .. k).
    The vid test compares sign-extended 32-bit words: bv_swrap 32 is injective on [0, 2^32) and vid <= 4094, so
    sext32 e = vid exactly when e = vid ([V01AccPure.sx32_eqb]); the parent test is strcmp on NUL-free strings
    (strcmp_contract's r = 0 <-> equal, SegBridge.bridge_strcmp for the model's strcmp).

    Part of the proof of LLVMFuzzerTestOneInput (its segment V01, stretch ACC); no released proof of
    fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import memcpy_c strcmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import V01D MainB.
Import ListNotations.
Open Scope Z_scope.

(** ** Build-independent facts: lists, words, byte views, the model's m_declared step. *)
Module V01AccPure.

Lemma firstn_S_nth : forall {A} (l : list A) j d, (j < length l)%nat -> firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
  intros A l. induction l as [|x l IH]; intros j d Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH j d) by lia. reflexivity.
Qed.

Lemma existsb_snoc : forall {A} (f : A -> bool) l x, existsb f (l ++ [x]) = existsb f l || f x.
Proof. intros. rewrite existsb_app. cbn [existsb]. rewrite orb_false_r. reflexivity. Qed.

Lemma b2z_lor : forall x y, Z.lor (Z.b2z x) (Z.b2z y) = Z.b2z (x || y).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma skipn_nth_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(** sext32 against a small non-negative value: bv_swrap 32 is injective on [0, 2^32). *)
Lemma sx32_eqb : forall e v, 0 <= e < 2 ^ 32 -> 0 <= v < 2 ^ 31 ->
  bv_eqb (sx32 (Z_to_bv 64 e)) (Z_to_bv 64 v) = (e =? v).
Proof.
  intros e v He Hv. unfold sx32, bv_eqb. rewrite (unsigned_lit e) by lia. rewrite (unsigned_lit v) by lia.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  apply eq_true_iff_eq. rewrite !Z.eqb_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma swrap32_id : forall z, -2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed_small : forall x, 0 <= x < 2 ^ 63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit by lia.
  replace (x <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(** s3 at 0x140f0: sgtz, neg, and, mul of mn > 0 give 20 mn. *)
Lemma s3_val : forall n, 0 < n < 2 ^ 32 ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (0 -
      bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 n))))) (bv_unsigned (Z_to_bv 64 n)))) * 20) =
  Z_to_bv 64 (20 * n).
Proof.
  intros n Hn.
  assert (E : v_slt (Z_to_bv 64 0) (Z_to_bv 64 n) = Z_to_bv 64 1).
  { unfold v_slt, c_lts. rewrite bv_lts_zero_l, unsigned_lit by lia.
    replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (n <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  rewrite E. rewrite (unsigned_lit 1) by lia. rewrite (unsigned_lit_wrap (0 - 1)).
  change ((0 - 1) mod 2 ^ 64) with 18446744073709551615. rewrite (unsigned_lit n) by lia.
  replace (Z.land 18446744073709551615 n) with n.
  2:{ change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
      rewrite Z.mod_small by lia. reflexivity. }
  rewrite (unsigned_lit n) by lia. f_equal. lia.
Qed.

(** ** Byte views (as check_declared.v's, over any segment list) *)
Lemma cstr_split : forall cap s f, cstr_enc cap s f ->
  exists sx, firstn (S (length s)) f = sx ++ [Z_to_bv 8 0] /\ zs sx = s /\ ~ In (Z_to_bv 8 0) sx.
Proof.
  intros cap s f (Hl & Hs & Hn & Hz).
  assert (Zp : zs (firstn (S (length s)) f) = s ++ [0]) by (unfold zs in *; rewrite <- firstn_map; exact Hz).
  assert (NE : firstn (S (length s)) f <> []).
  { intros E. rewrite E in Zp. cbn in Zp. destruct s; discriminate. }
  destruct (exists_last NE) as (sx & b & E).
  rewrite E in Zp. unfold zs in Zp. rewrite map_app in Zp. cbn [map] in Zp.
  apply app_inj_tail in Zp as [Z1 Z2].
  exists sx. split; [rewrite E; repeat f_equal; apply bv_eq; rewrite Z2; reflexivity|].
  split; [exact Z1|].
  intros Hin. apply Hn. rewrite <- Z1. unfold zs. apply in_map_iff. exists (Z_to_bv 8 0). split; [reflexivity|exact Hin].
Qed.

Lemma fld_fld : forall a n b k (l : list byte), (a + n <= k)%nat ->
  firstn n (skipn a (firstn k (skipn b l))) = firstn n (skipn (b + a) l).
Proof.
  intros a n b k l H. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (k - a)) with n by lia. rewrite (Nat.add_comm a b). reflexivity.
Qed.

Lemma wr_at_app : forall segs m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros k Hk. apply H. lia.
    + intros k Hk. replace (a + n1 + k) with (a + (n1 + k)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros k Hk. destruct (Z.lt_ge_cases k n1).
    + apply HA. lia.
    + replace (a + k) with (a + n1 + (k - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_ext : forall segs m A cs cs', rw_cells segs m A cs -> cs = cs' -> rw_cells segs m A cs'.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_CB_bytes : forall segs m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs.
Proof. intros segs m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Section Bytes.
Variable segs : list Segment.

Lemma bat_sub : forall m a (l : list byte) k n, bytes_at segs m a l -> (k + n <= length l)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

(** Entry i of the model's table: the vid's four bytes at mt + 20 i + 16, and the parent's string with its NUL at
    mt + 20 i. *)
Lemma mtab_entry : forall m mt wt bm i, bytes_at segs m mt bm -> mtab_enc wt bm -> (i < length wt)%nat ->
  ov_read_bytes segs m (wa (mt + 20 * Z.of_nat i + 16)) 4 = Some (le4 (Z_to_bv 64 (snd (nth i wt ([], 0))))) /\
  0 <= snd (nth i wt ([], 0)) < 2 ^ 32 /\
  exists sy, bytes_at segs m (mt + 20 * Z.of_nat i) (sy ++ [Z_to_bv 8 0]) /\ zs sy = fst (nth i wt ([], 0)) /\
             ~ In (Z_to_bv 8 0) sy.
Proof.
  intros m mt wt bm i HB [HL HE] Hi.
  destruct (HE i Hi) as (L20 & HC & HV & H4).
  split; [|split; [exact HV|]].
  - rewrite <- H4. unfold fld. rewrite fld_fld by lia.
    replace (mt + 20 * Z.of_nat i + 16) with (mt + Z.of_nat (20 * i + 16)) by lia.
    apply (bytes_at_ov_read segs m mt bm (20 * i + 16) 4 HB). lia.
  - pose proof HC as (_ & Hlt & _).
    destruct (cstr_split 16 _ _ HC) as (sy & E & Z1 & N1).
    exists sy. split; [|split; [exact Z1 | exact N1]].
    rewrite <- E. unfold fld. rewrite fld_fld by lia. rewrite firstn_firstn, Nat.add_0_r.
    replace (Nat.min (S (length (fst (nth i wt ([], 0))))) 16) with (S (length (fst (nth i wt ([], 0))))) by lia.
    replace (mt + 20 * Z.of_nat i) with (mt + Z.of_nat (20 * i)) by lia.
    apply bat_sub; [exact HB | lia].
Qed.

(** The parent string of an mvlan buffer, with its NUL. *)
Lemma mvlan_parent : forall m A p v bs, bytes_at segs m A bs -> mvlan_enc (p, v) bs ->
  exists sx, bytes_at segs m A (sx ++ [Z_to_bv 8 0]) /\ zs sx = p /\ ~ In (Z_to_bv 8 0) sx.
Proof.
  intros m A p v bs HB (HL & HC & _). cbn [fst] in HC.
  pose proof HC as (_ & Hlt & _).
  destruct (cstr_split 16 _ _ HC) as (sx & E & Z1 & N1).
  exists sx. split; [|split; [exact Z1 | exact N1]].
  rewrite <- E. unfold fld. cbn [skipn]. rewrite firstn_firstn.
  replace (Nat.min (S (length p)) 16) with (S (length p)) by lia.
  pose proof (bat_sub m A bs 0 (S (length p)) HB ltac:(lia)) as H. cbn [skipn] in H.
  replace (A + Z.of_nat 0) with A in H by lia. exact H.
Qed.
End Bytes.

(** Appending one encoded entry to an encoded table. *)
Lemma mtab_enc_app : forall t bm e f, mtab_enc t bm -> mvlan_enc e f -> mtab_enc (t ++ [e]) (bm ++ f).
Proof.
  intros t bm e f [HL HE] Hf. pose proof Hf as (Lf & _).
  split; [rewrite !length_app, HL, Lf; cbn [length]; lia|].
  intros k Hk. rewrite length_app in Hk. cbn [length] in Hk.
  destruct (Nat.lt_ge_cases k (length t)) as [Lt|Ge].
  - rewrite app_nth1 by lia. unfold fld. rewrite skipn_app. replace (20 * k - length bm)%nat with 0%nat by lia.
    rewrite firstn_app. rewrite length_skipn. replace (20 - (length bm - 20 * k))%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. apply HE. exact Lt.
  - replace k with (length t) by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    unfold fld. rewrite skipn_app. rewrite skipn_all2 by lia. replace (20 * length t - length bm)%nat with 0%nat by lia.
    change (skipn 0 f) with f. cbn [app]. rewrite firstn_all2 by lia. exact Hf.
Qed.

(** ** The model: one turn of m_decl_go whose name split to (p, vid). *)
Section Model.
Variables (segs : list mseg) (i : nat) (tb : list (list Z * Z)) (cap a : Z) (p : list Z) (vid : Z).
Hypothesis Hi : (i < length segs)%nat.
Hypothesis Hig : ms_ignore (nth i segs mseg_d) = false.
Hypothesis Hsp : m_split (ms_name (nth i segs mseg_d)) = Some (p, vid).

Lemma decl_dup : existsb (fun e : list Z * Z => (snd e =? vid) && (SegModel.strcmp (fst e) p =? 0)) tb = true ->
  m_decl_go (skipn i segs) tb cap a = m_decl_go (skipn (S i) segs) tb cap a.
Proof.
  intros Hx. rewrite (skipn_nth_cons segs i mseg_d Hi). cbn [m_decl_go]. rewrite Hig. cbv beta iota.
  rewrite Hsp. cbv beta iota. rewrite Hx. reflexivity.
Qed.

Lemma decl_full : existsb (fun e : list Z * Z => (snd e =? vid) && (SegModel.strcmp (fst e) p =? 0)) tb = false ->
  cap <= Z.of_nat (length tb) -> m_decl_go (skipn i segs) tb cap a = (-1, tb).
Proof.
  intros Hx Hc. rewrite (skipn_nth_cons segs i mseg_d Hi). cbn [m_decl_go]. rewrite Hig. cbv beta iota.
  rewrite Hsp. cbv beta iota. rewrite Hx. replace (cap <=? Z.of_nat (length tb)) with true
    by (symmetry; apply Z.leb_le; exact Hc). reflexivity.
Qed.

Lemma decl_app : existsb (fun e : list Z * Z => (snd e =? vid) && (SegModel.strcmp (fst e) p =? 0)) tb = false ->
  Z.of_nat (length tb) < cap ->
  m_decl_go (skipn i segs) tb cap a = m_decl_go (skipn (S i) segs) (tb ++ [(p, vid)]) cap (a + 1).
Proof.
  intros Hx Hc. rewrite (skipn_nth_cons segs i mseg_d Hi). cbn [m_decl_go]. rewrite Hig. cbv beta iota.
  rewrite Hsp. cbv beta iota. rewrite Hx. replace (cap <=? Z.of_nat (length tb)) with false
    by (symmetry; apply Z.leb_gt; exact Hc). reflexivity.
Qed.
End Model.

End V01AccPure.
Import V01AccPure.

(** ** The walk *)
Section Acc.
Variable X : vctx.
Hypothesis HG : V01_geo X.
Hypothesis HSC : strcmp_contract.
Hypothesis HMC : memcpy_contract.
Variables (i : nat) (tb : list (list Z * Z)) (a : Z) (p : list Z) (vid : Z) (bs : list byte).
Hypothesis HJ : V01_JOINat X i.
Hypothesis HT : V01_TAIL X.
Hypothesis Hbs : mvlan_enc (p, vid) bs.
Hypothesis Hvid : 0 < vid <= 4094.
Hypothesis Hinv : V01_inv X i tb a.
Hypothesis Hi : (i < length (v_segs X))%nat.
Hypothesis Hig : ms_ignore (nth i (v_segs X) mseg_d) = false.
Hypothesis Hsplit : m_split (ms_name (nth i (v_segs X) mseg_d)) = Some (p, vid).
Hypothesis H32 : (length (v_segs X) <= 32)%nat.

Local Abbreviation Post := (V01_post X).
Local Abbreviation SP := (Z_to_bv 64 (v_sp X)).
Local Abbreviation R9 := (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)).
Local Abbreviation R18 := (Z_to_bv 64 (18446744073709551615 - v_mm X)).
Local Abbreviation R20 := (Z_to_bv 64 18446744073709551615).
Local Abbreviation R22 := (Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i))).
Local Abbreviation R25 := (Z_to_bv 64 (Z.of_nat i)).
Local Abbreviation R26 := (Z_to_bv 64 4094).
Local Abbreviation R27 := (Z_to_bv 64 (v_mm X + MC_N)).
Local Abbreviation W8 := (Z_to_bv 64 (18446744073709551615 - v_buf X)).
Local Abbreviation W30 := (Z_to_bv 64 MASK_PARENT).
Local Abbreviation W38 := (Z_to_bv 64 (18446744073709551615 - v_mt X)).
Local Abbreviation DF := (fun e : list Z * Z => (snd e =? vid) && (SegModel.strcmp (fst e) p =? 0)).
Local Abbreviation n := (Z.of_nat (length tb)).

(** The numbers of the context the walk uses (no disjunction, so lia stays fast). *)
Lemma g_num : v_S X mod 16 = 0 /\ 0x60000 < v_lo X /\ v_S X <= 2 ^ 47 /\ 0 <= v_cap X < 40 /\
  4096 <= v_mt X /\ v_mt X + v_nmt X <= v_lo X /\ v_sp X = v_S X - 240 /\ v_lo X = v_S X - 65536 /\
  v_buf X = v_sp X + 96 /\ v_nmt X = 20 * (v_cap X + 1) /\ v_ntab X = 18 * (v_cap X + 1).
Proof.
  destruct HG as (S16 & Lo & S47 & _ & Cap & _ & _ & _ & _ & _ & _ & _ & _ & _ & Mt0 & _ & Mt & _).
  repeat split; try assumption; try lia; reflexivity.
Qed.

Lemma n0_le : Z.of_nat (v_n0 X) <= v_cap X.
Proof.
  pose proof g_num as (_ & _ & _ & Cap & _).
  unfold v_n0, v_tab0, seg_tab0. unfold v_cap, seg_cap in *. apply vlan_init_len. lia.
Qed.

Lemma a_rng : 0 <= a <= Z.of_nat i /\ (i < 32)%nat.
Proof. destruct Hinv as (_ & Ha & _). split; [exact Ha | lia]. Qed.

Ltac nums := pose proof g_num as (S16 & Lo & S47 & Cap & Mt0 & Mt & Esp & Elo & Ebuf & Enmt & Entab);
  pose proof a_rng as (Arng & I32).

(** Every memory fact of an interface point except main's frame cells and mem_inv. *)
Definition REST (t : list (list Z * Z)) (m : word -> option byte) : Prop :=
  stk rsegs m (v_lo X) (v_sp X) /\
  (forall x, v_lo X <= x < v_S X -> seg_rom rsegs (wa x) = None) /\
  bytes_at rsegs m (sa_got_guard SA) (le8 (Z_to_bv 64 (sa_guard SA))) /\
  (exists gv : word, bytes_at rsegs m (sa_guard SA) (le8 gv)) /\
  (exists ev : word, rw_cells rsegs m V01_ERRNO [C4 ev]) /\
  bytes_at rsegs m V01_ENP (zb (S_enp ++ [0])) /\
  rconf_at rsegs m (v_c X) (v_rc X) /\
  mconf_at rsegs m (v_mm X) (v_mc X) /\
  (exists jn : list byte, rw_cells rsegs m (v_sp X + 0x58) [CB 4 jn; C4 (Z_to_bv 64 (Z.of_nat (v_n0 X)))]) /\
  rw_cells rsegs m (v_buf X) [CB 20 bs] /\
  rtab_at rsegs m (v_tab X) (v_tab0 X) /\
  guard_at rsegs m (v_tab X) (v_cap X) /\
  (exists ft : list byte, rw_cells rsegs m (v_tab X + RVLAN_SIZE * Z.of_nat (v_n0 X))
     [CB (Z.to_nat (RVLAN_SIZE * (v_cap X - Z.of_nat (v_n0 X)))) ft]) /\
  mtab_at rsegs m (v_mt X) t /\
  (exists fm : list byte, rw_cells rsegs m (v_mt X + MVLAN_SIZE * Z.of_nat (length t))
     [CB (Z.to_nat (MVLAN_SIZE * (v_cap X + 1 - Z.of_nat (length t)))) fm]) /\
  Z.of_nat (length t) <= v_cap X /\
  munch (V01_W X) (v_m0 X) m /\ wmono rsegs (v_m0 X) m.

Lemma lmem_of : forall t ad m, REST t m -> mem_inv rsegs m ->
  rw_cells rsegs m (v_sp X) (V01_cells X W8 W30 W38 ad (Z.of_nat (length t))) -> V01_lmem X ad t m.
Proof.
  intros t ad m (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9' & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18')
    MI HF.
  split; [exact (conj MI (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 R8)))))))) |].
  split; [exact HF |]. split; [exact R9' |]. split; [exists bs; exact R10 |].
  exact (conj R11 (conj R12 (conj R13 (conj R14 (conj R15 (conj R16 (conj R17 R18'))))))).
Qed.

(** The regions REST names lie below the stack window or in main's frame above sp + 0x58. *)
Lemma rest_frame : forall t m m', REST t m -> munch [(v_sp X, v_sp X + 88)] m m' -> wmono rsegs m m' -> REST t m'.
Proof.
  intros t m m' (R1 & R2 & R3 & (gv & R4) & (ev & R5) & R6 & (bc & R7 & E7) & (bmm & R8 & E8) & (jn & R9') & R10 &
    (bt & R11 & E11) & R12 & (ft & R13) & (bm & R14 & E14) & (fm & R15) & R16 & R17 & R18') MU WM.
  nums. pose proof n0_le as N0.
  pose proof E7 as (L7 & _). pose proof E8 as (L8 & _). pose proof E11 as (L11 & _). pose proof E14 as (L14 & _).
  destruct HG as (_ & _ & _ & _ & _ & _ & _ & C0 & _ & _ & M0 & _ & _ & T0 & _).
  unfold SEG_C_SIZE, SEG_M_SIZE in *.
  assert (DJ : forall A k, A + k <= v_lo X \/ v_sp X + 88 <= A -> disjoint_from [(v_sp X, v_sp X + 88)] A k).
  { intros A k H. cbn [disjoint_from]. split; [lia | exact I]. }
  refine (conj _ (conj R2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj R16 (conj _ _))))))))))))))))).
  - apply (stk_transport_disjoint rsegs _ m m' _ _ R1 MU WM). cbn [disjoint_from]. split; [lia | exact I].
  - apply (bytes_at_transport rsegs _ m m' _ _ R3 MU). apply DJ. rewrite length_le8. cbn. lia.
  - exists gv. apply (bytes_at_transport rsegs _ m m' _ _ R4 MU). apply DJ. rewrite length_le8. cbn. lia.
  - exists ev. apply (rw_cells_transport rsegs _ m m' _ _ R5 MU WM). apply DJ. cbn. unfold V01_ERRNO. lia.
  - apply (bytes_at_transport rsegs _ m m' _ _ R6 MU). apply DJ.
    replace (length (zb (S_enp ++ [0]))) with 7%nat by reflexivity. unfold V01_ENP. lia.
  - exists bc. split; [|exact E7]. apply (bytes_at_transport rsegs _ m m' _ _ R7 MU). apply DJ. lia.
  - exists bmm. split; [|exact E8]. apply (bytes_at_transport rsegs _ m m' _ _ R8 MU). apply DJ. lia.
  - exists jn. apply (rw_cells_transport rsegs _ m m' _ _ R9' MU WM). apply DJ. lia.
  - apply (rw_cells_transport rsegs _ m m' _ _ R10 MU WM). apply DJ. lia.
  - exists bt. split; [|exact E11]. apply (bytes_at_transport rsegs _ m m' _ _ R11 MU). apply DJ.
    rewrite L11. unfold v_n0 in N0. lia.
  - unfold guard_at in *. apply (bytes_at_transport rsegs _ m m' _ _ R12 MU). apply DJ.
    replace (length GUARD_BYTES) with 18%nat by reflexivity. unfold RVLAN_SIZE. lia.
  - exists ft. apply (rw_cells_transport rsegs _ m m' _ _ R13 MU WM). apply DJ. cbn [cells_size csize].
    unfold RVLAN_SIZE. lia.
  - exists bm. split; [|exact E14]. apply (bytes_at_transport rsegs _ m m' _ _ R14 MU). apply DJ.
    rewrite L14. lia.
  - exists fm. apply (rw_cells_transport rsegs _ m m' _ _ R15 MU WM). apply DJ. cbn [cells_size csize].
    unfold MVLAN_SIZE. lia.
  - apply (munch_trans _ _ m _ R17). apply (munch_weaken [(v_sp X, v_sp X + 88)] _ m m'); [|exact MU].
    intros x Hx. unfold V01_W in Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
  - exact (wmono_trans rsegs _ _ _ R18' WM).
Qed.

(** memcpy's write [mt + 20 n, mt + 20 n + 20) is the first free entry of mt: everything else REST names keeps,
    and the table grows by the buffer's entry. *)
Lemma rest_memcpy : forall m m', REST tb m -> n < v_cap X ->
  munch [(v_mt X + 20 * n, v_mt X + 20 * n + 20)] m m' -> wmono rsegs m m' ->
  rw_cells rsegs m' (v_mt X + 20 * n) [CB 20 bs] -> REST (tb ++ [(p, vid)]) m'.
Proof.
  intros m m' (R1 & R2 & R3 & (gv & R4) & (ev & R5) & R6 & (bc & R7 & E7) & (bmm & R8 & E8) & (jn & R9') & R10 &
    (bt & R11 & E11) & R12 & (ft & R13) & (bm & R14 & E14) & (fm & R15) & R16 & R17 & R18') Hn MU WM NEW.
  nums. pose proof n0_le as N0.
  pose proof E7 as (L7 & _). pose proof E8 as (L8 & _). pose proof E11 as (L11 & _). pose proof E14 as (L14 & _).
  unfold SEG_C_SIZE, SEG_M_SIZE in *.
  destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC & _ & AM & AT & _ & _ &
    _ & AE & _ & AG & _ & AGG & _ & AN & _).
  assert (DJ : forall B nb A k, apart B nb (v_mt X) (v_mt X + v_nmt X) -> B <= A -> A + k <= B + nb ->
    disjoint_from [(v_mt X + 20 * n, v_mt X + 20 * n + 20)] A k).
  { intros B nb A k H H1 H2. unfold apart in H. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (DS : forall A k, v_lo X <= A -> disjoint_from [(v_mt X + 20 * n, v_mt X + 20 * n + 20)] A k).
  { intros A k H. cbn [disjoint_from]. split; [lia | exact I]. }
  unfold REST. unfold MVLAN_SIZE in R15 |- *. rewrite length_app. cbn [length].
  (* the free entries: the first 20 bytes are the new entry, the rest stay free *)
  set (K := Z.to_nat (20 * (v_cap X + 1 - n))) in R15.
  assert (EK : K = (20 + Z.to_nat (20 * (v_cap X + 1 - Z.of_nat (length tb + 1))))%nat) by (unfold K; lia).
  apply (rw_cells_split_CB rsegs m _ [] K fm [] [20%nat; Z.to_nat (20 * (v_cap X + 1 - Z.of_nat (length tb + 1)))])
    in R15; [|cbn [sum_nat]; lia].
  cbn [app mk_CB_cells] in R15. apply (rw_cells_app rsegs m _ [_] [_]) in R15 as [_ R15].
  cbn [cells_size csize] in R15.
  refine (conj _ (conj R2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))))))).
  - apply (stk_transport_disjoint rsegs _ m m' _ _ R1 MU WM). cbn [disjoint_from]. split; [lia | exact I].
  - apply (bytes_at_transport rsegs _ m m' _ _ R3 MU). rewrite length_le8.
    apply (DJ (sa_got_guard SA) 8); [exact AGG | lia | lia].
  - exists gv. apply (bytes_at_transport rsegs _ m m' _ _ R4 MU). rewrite length_le8.
    apply (DJ (sa_guard SA) 8); [exact AG | lia | lia].
  - exists ev. apply (rw_cells_transport rsegs _ m m' _ _ R5 MU WM). cbn [cells_size csize].
    apply (DJ V01_ERRNO 4); [exact AE | lia | lia].
  - apply (bytes_at_transport rsegs _ m m' _ _ R6 MU).
    replace (length (zb (S_enp ++ [0]))) with 7%nat by reflexivity. apply (DJ V01_ENP 7); [exact AN | lia | lia].
  - exists bc. split; [|exact E7]. apply (bytes_at_transport rsegs _ m m' _ _ R7 MU).
    apply (DJ (v_c X) 16616); [exact AC | lia | lia].
  - exists bmm. split; [|exact E8]. apply (bytes_at_transport rsegs _ m m' _ _ R8 MU).
    apply (DJ (v_mm X) 9236); [exact AM | lia | lia].
  - exists jn. apply (rw_cells_transport rsegs _ m m' _ _ R9' MU WM). apply DS. lia.
  - apply (rw_cells_transport rsegs _ m m' _ _ R10 MU WM). apply DS. lia.
  - exists bt. split; [|exact E11]. apply (bytes_at_transport rsegs _ m m' _ _ R11 MU).
    apply (DJ (v_tab X) (v_ntab X)); [exact AT | lia | unfold v_n0 in N0; lia].
  - unfold guard_at in *. apply (bytes_at_transport rsegs _ m m' _ _ R12 MU).
    replace (length GUARD_BYTES) with 18%nat by reflexivity. unfold RVLAN_SIZE.
    apply (DJ (v_tab X) (v_ntab X)); [exact AT | lia | lia].
  - exists ft. apply (rw_cells_transport rsegs _ m m' _ _ R13 MU WM). cbn [cells_size csize]. unfold RVLAN_SIZE.
    apply (DJ (v_tab X) (v_ntab X)); [exact AT | lia | lia].
  - exists (bm ++ bs). split; [|exact (mtab_enc_app _ _ _ _ E14 Hbs)].
    apply bytes_at_app. split.
    + apply (bytes_at_transport rsegs _ m m' _ _ R14 MU). cbn [disjoint_from]. split; [lia | exact I].
    + rewrite L14. replace (v_mt X + Z.of_nat (20 * length tb)) with (v_mt X + 20 * n) by lia.
      exact (rw_cells_CB_bytes rsegs m' _ _ _ NEW).
  - eexists. replace (v_mt X + 20 * Z.of_nat (length tb + 1)) with (v_mt X + 20 * n + Z.of_nat 20) by lia.
    apply (rw_cells_transport rsegs _ m m' _ _ R15 MU WM). cbn [disjoint_from]. split; [lia | exact I].
  - lia.
  - apply (munch_trans _ _ m _ R17).
    apply (munch_weaken [(v_mt X + 20 * n, v_mt X + 20 * n + 20)] _ m m'); [|exact MU].
    intros x Hx. unfold V01_W in Hx. cbn [outside] in *. destruct Hx as (_ & _ & Hx & _). split; [lia | exact I].
  - exact (wmono_trans rsegs _ _ _ R18' WM).
Qed.

(** The model facts of the three exits. *)
Lemma inv_dup : existsb DF tb = true -> V01_inv X (S i) tb a.
Proof.
  intros Hx. destruct Hinv as (_ & Ha & Hd). split; [lia|]. split; [lia|].
  rewrite <- Hd. symmetry. exact (decl_dup _ _ _ _ _ _ _ Hi Hig Hsplit Hx).
Qed.

Lemma inv_full : existsb DF tb = false -> v_cap X <= n -> m_declared (v_mc X) (v_tab0 X) (v_cap X) = (-1, tb).
Proof.
  intros Hx Hc. destruct Hinv as (_ & _ & Hd). rewrite <- Hd. exact (decl_full _ _ _ _ _ _ _ Hi Hig Hsplit Hx Hc).
Qed.

Lemma inv_app : existsb DF tb = false -> n < v_cap X -> V01_inv X (S i) (tb ++ [(p, vid)]) (a + 1).
Proof.
  intros Hx Hc. destruct Hinv as (_ & Ha & Hd). split; [lia|]. split; [lia|].
  rewrite <- Hd. symmetry. exact (decl_app _ _ _ _ _ _ _ Hi Hig Hsplit Hx Hc).
Qed.

(** 0x141a0: s3 = m, then the join 0x13fb8 with table t and added ad. *)
Lemma w_join : forall t ad m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 : word),
  REST t m -> mem_inv rsegs m -> rw_cells rsegs m (v_sp X) (V01_cells X W8 W30 W38 ad (Z.of_nat (length t))) ->
  V01_inv X (S i) t ad ->
  evt rsegs Post (MS (mkR x1 SP (v_gp X) (v_tp X) x5 x6 x7 x8 R9 x10 x11 x12 x13 x14 x15 x16 x17 R18 x19 R20 x21
    R22 x23 x24 R25 R26 R27 x28 x29 x30 x31) (v_F X) (Z_to_bv 64 0x141a0) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros t ad m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 HR MI HF HI.
  pose proof (lmem_of t ad m HR MI HF) as LM. unfold V01_cells in HF.
  step. step.
  eapply HJ; [exact LM | exact HI | lia].
Qed.

(** 0x14254, the full table: added = -1, s3 = m, the tail. *)
Lemma w_full : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 : word),
  REST tb m -> mem_inv rsegs m -> rw_cells rsegs m (v_sp X) (V01_cells X W8 W30 W38 a n) ->
  m_declared (v_mc X) (v_tab0 X) (v_cap X) = (-1, tb) ->
  evt rsegs Post (MS (mkR x1 SP (v_gp X) (v_tp X) x5 x6 x7 x8 R9 x10 x11 x12 x13 x14 x15 x16 x17 R18 x19 R20 x21
    R22 x23 x24 R25 R26 R27 x28 x29 x30 x31) (v_F X) (Z_to_bv 64 0x14254) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 HR MI HF HD.
  nums. unfold V01_cells in HF.
  pose proof (munch_refl [(v_sp X, v_sp X + 88)] m) as MS0. pose proof (wmono_refl rsegs m) as WM0.
  step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) => rename M into m2 end.
  eapply HT with (want := -1) (wt := tb) (w8 := W8) (w30 := W30) (w38 := W38); [exact HD | lia |].
  apply (lmem_of tb (-1) m2); [exact (rest_frame tb m m2 HR MS0 WM0) | assumption |].
  unfold V01_cells. eapply rw_cells_ext; [eassumption|].
  replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
  reflexivity.
Qed.

(** 0x14148, room in mt (mn < cap) and no duplicate: memcpy(&mt[mn], &v, 20), added++, mn++, the join. *)
Lemma w_app : forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 : word),
  REST tb m -> mem_inv rsegs m -> rw_cells rsegs m (v_sp X) (V01_cells X W8 W30 W38 a n) ->
  existsb DF tb = false -> n < v_cap X ->
  evt rsegs Post (MS (mkR x1 SP (v_gp X) (v_tp X) x5 x6 x7 x8 R9 x10 (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17 R18
    x19 R20 x21 R22 x23 x24 R25 R26 R27 x28 x29 x30 x31) (v_F X) (Z_to_bv 64 0x14148) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 HR MI HF Hx Hn.
  nums. unfold V01_cells in HF.
  (* the buffer's bytes and the first free entry of mt *)
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RB & _ & _ & _ & _ & (fm & RF) & _).
  apply rw_cells_CB_bytes in RB. rewrite Ebuf in RB.
  unfold MVLAN_SIZE in RF.
  apply (rw_cells_split_CB rsegs m _ [] _ fm [] [20%nat; Z.to_nat (20 * (v_cap X + 1 - n)) - 20]%nat) in RF;
    [|cbn [sum_nat]; lia].
  cbn [app mk_CB_cells] in RF. apply (rw_cells_app rsegs m _ [_] [_]) in RF as [RF _].
  (* 0x14148 - 0x14174: a0 = mt + 20 mn and the dead traps *)
  zstep. zstep. zstep. zstep. zstep.
  if_cases K; cbv iota; [exfalso; zify_cond K; lia|]. clear K.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases K; cbv iota.
  { exfalso. replace (n * 20 + v_mt X <? v_mt X) with false in K by (symmetry; apply Z.ltb_ge; lia).
    replace (Z.lxor n 9223372036854775808 <? 9223372036854775808) with false in K
      by (symmetry; apply Z.ltb_ge; change 9223372036854775808 with (2 ^ 63);
          rewrite zb_lxor_pow2_small by lia; lia).
    vm_compute in K. discriminate K. }
  clear K. replace (n * 20 + v_mt X) with (v_mt X + 20 * n) by lia.
  (* 0x14178 - 0x14180: memcpy(mt + 20 mn, sp + 0x60, 20) *)
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HMC with (src := bs) (junk := firstn 20 fm).
    - rewrite unsigned_lit by lia. exact RB.
    - rewrite unsigned_lit by lia. destruct Hbs as (Lb & _). exact Lb.
    - rewrite !unsigned_lit by lia. exact RF.
    - rewrite !unsigned_lit by lia. lia.
    - exact MI. }
  intros ms' PO. unfold memcpy_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU & WM &
    MI1 & NEW & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !unsigned_lit in MU, NEW by lia.
  pose proof (rest_memcpy m m1 HR Hn MU WM NEW) as HR1.
  assert (HF1 := rw_cells_transport rsegs _ m m1 _ _ HF MU WM
    ltac:(cbn [disjoint_from cells_size csize]; split; [lia | exact I])).
  clear MU WM NEW RF RB HR MI HF.
  pose proof (munch_refl [(v_sp X, v_sp X + 88)] m1) as MS0. pose proof (wmono_refl rsegs m1) as WM0.
  (* 0x14184 - 0x1419c: added++ (the overflow trap is dead), mn++, both stored *)
  zstep. zstep. rewrite swrap32_id by lia.
  zstep. if_cases K; cbv iota.
  { exfalso. unfold bv_lts in K. rewrite !signed_small in K by lia. apply Z.ltb_lt in K. lia. }
  clear K.
  zstep. zstep. rewrite swrap32_id by lia.
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) => rename M into m3 end.
  eapply (w_join (tb ++ [(p, vid)]) (a + 1) m3); [exact (rest_frame _ m1 m3 HR1 MS0 WM0) | assumption | |
    exact (inv_app Hx Hn)].
  unfold V01_cells. eapply rw_cells_ext; [eassumption|]. rewrite length_app. cbn [length].
  repeat f_equal; lia.
Qed.

(** 0x14140, no duplicate: cap from 0x10(sp); mn >= cap is the -1 exit, else the append. *)
Lemma w_nodup : forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 : word),
  REST tb m -> mem_inv rsegs m -> rw_cells rsegs m (v_sp X) (V01_cells X W8 W30 W38 a n) ->
  existsb DF tb = false ->
  evt rsegs Post (MS (mkR x1 SP (v_gp X) (v_tp X) x5 x6 x7 x8 R9 x10 (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17 R18
    x19 R20 x21 R22 x23 x24 R25 R26 R27 x28 x29 x30 x31) (v_F X) (Z_to_bv 64 0x14140) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x28 x29 x30 x31 HR MI HF Hx.
  nums. pose proof HF as HF0. unfold V01_cells in HF.
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
  step. step.
  if_cases K; cbv iota.
  - unfold bv_lts in K. rewrite !signed_small in K by lia. cbn [negb] in K.
    apply negb_true_iff, Z.ltb_ge in K.
    eapply w_full; [exact HR | exact MI | exact HF0 | exact (inv_full Hx K)].
  - unfold bv_lts in K. rewrite !signed_small in K by lia.
    apply negb_false_iff, Z.ltb_lt in K.
    eapply w_app; [exact HR | exact MI | exact HF0 | exact Hx | exact K].
Qed.

(** The dup loop 0x140f4 at entry j, k entries left: s3 = 20 mn, s5 = the model's duplicate test over mt[0 .. j),
    s7 = mt + 20 j, s8 = 20 j. It runs to its end (no early exit) and leaves s5 = the test over the whole table. *)
Lemma dloop : forall m bm sx,
  bytes_at rsegs m (v_mt X) bm -> mtab_enc tb bm ->
  bytes_at rsegs m (v_sp X + 96) (sx ++ [Z_to_bv 8 0]) -> zs sx = p -> ~ In (Z_to_bv 8 0) sx ->
  rw_cells rsegs m (v_sp X) (V01_cells X W8 W30 W38 a n) ->
  (forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x28 x29 x30 x31 w21 : word),
     w21 = Z_to_bv 64 (Z.b2z (existsb DF tb)) ->
     evt rsegs Post (MS (mkR x1 SP (v_gp X) (v_tp X) x5 x6 x7 (Z_to_bv 64 vid) R9 x10 x11 x12 x13 x14 x15 x16 x17 R18
       x19 R20 w21 R22 x23 x24 R25 R26 R27 x28 x29 x30 x31) (v_F X) (Z_to_bv 64 0x14138) (v_fc X) None m
       (seg_rom rsegs))) ->
  forall k j (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w19 w21 w23 w24 : word),
  (j + k = length tb)%nat -> (0 < k)%nat ->
  w19 = Z_to_bv 64 (20 * n) -> w21 = Z_to_bv 64 (Z.b2z (existsb DF (firstn j tb))) ->
  w23 = Z_to_bv 64 (v_mt X + 20 * Z.of_nat j) -> w24 = Z_to_bv 64 (20 * Z.of_nat j) ->
  evt rsegs Post (MS (mkR x1 SP (v_gp X) (v_tp X) x5 x6 x7 (Z_to_bv 64 vid) R9 x10 x11 x12 x13 x14 x15 x16 x17 R18
    w19 R20 w21 R22 w23 w24 R25 R26 R27 x28 x29 x30 x31) (v_F X) (Z_to_bv 64 0x140f4) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros m bm sx HB HE BX ZX NX HF EXIT. nums. unfold V01_cells in HF.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. pose proof HE as [LB _].
  induction k as [|k IH]; intros j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w19 w21 w23 w24
    Hjk Hk E19 E21 E23 E24; [lia|].
  subst w19 w21 w23 w24.
  assert (Hj : (j < length tb)%nat) by lia.
  destruct (mtab_entry rsegs m (v_mt X) tb bm j HB HE Hj) as (RD & RV & sy & BY & ZY & NY).
  assert (ES : existsb DF (firstn (S j) tb) = existsb DF (firstn j tb) || DF (nth j tb ([], 0)))
    by (rewrite (firstn_S_nth tb j ([], 0)) by lia; rewrite existsb_snoc; reflexivity).
  (* 0x140f4 - 0x14100: the two dead traps *)
  step. step. if_cases K; cbv iota; [exfalso; zify_cond K; lia|]. clear K.
  step. step. if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|]. clear K.
  (* 0x14104 - 0x1410c: mt[j].vid against vid *)
  step. step. rewrite (unsigned_lit vid) by lia. rewrite Z.add_0_r, swrap32_id by lia.
  step.
  if_cases K; cbv iota; rewrite (sx32_eqb _ vid RV ltac:(lia)) in K.
  - (* another vid: a0 = 0 *)
    apply negb_true_iff, Z.eqb_neq in K.
    step. step. step. step. step.
    assert (DFj : DF (nth j tb ([], 0)) = false).
    { cbv beta. rewrite (proj2 (Z.eqb_neq _ _) K). reflexivity. }
    destruct k as [|k].
    + if_cases K1; cbv iota; [exfalso; zify_cond K1; lia|].
      rewrite firstn_all2 in ES by lia.
      eapply EXIT. zsimp. rewrite ES, DFj, orb_false_r, Z.lor_0_l. reflexivity.
    + if_cases K1; cbv iota; [|exfalso; zify_cond K1; lia].
      eapply (IH (S j)); [lia | lia | reflexivity | | f_equal; lia | f_equal; lia].
      zsimp. rewrite ES, DFj, orb_false_r, Z.lor_0_l. reflexivity.
  - (* the same vid: strcmp(mt[j].parent, sp + 0x60), seqz *)
    apply negb_false_iff, Z.eqb_eq in K.
    step. step. step.
    eapply evt_cut.
    { eapply HSC with (sx := sy) (sy := sx);
        [rewrite unsigned_lit by lia; exact BY | exact NY | rewrite unsigned_lit by lia; exact BX | exact NX]. }
    intros ms' (r & y11 & y12 & y13 & -> & Hr).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (EA : (bv_unsigned r <? 1) = (SegModel.strcmp (fst (nth j tb ([], 0))) p =? 0)).
    { apply eq_true_iff_eq. rewrite Z.ltb_lt, Z.eqb_eq, <- ZY, <- ZX, (SegBridge.bridge_strcmp sy sx NY NX), <- Hr.
      pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr.
      split; intros H.
      - apply bv_eq. rewrite (unsigned_lit 0) by lia. lia.
      - subst r. rewrite (unsigned_lit 0) by lia. lia. }
    assert (DFj : DF (nth j tb ([], 0)) = (bv_unsigned r <? 1)).
    { cbv beta. rewrite K, Z.eqb_refl, EA. reflexivity. }
    step. step. step. step. step. step.
    destruct k as [|k].
    + if_cases K1; cbv iota; [exfalso; zify_cond K1; lia|].
      rewrite firstn_all2 in ES by lia.
      eapply EXIT. zsimp. rewrite ES, DFj, <- b2z_lor, Z.lor_comm. reflexivity.
    + if_cases K1; cbv iota; [|exfalso; zify_cond K1; lia].
      eapply (IH (S j)); [lia | lia | reflexivity | | f_equal; lia | f_equal; lia].
      zsimp. rewrite ES, DFj, <- b2z_lor, Z.lor_comm. reflexivity.
Qed.

(** 0x140cc, the stretch's entry. *)
Lemma w_acc : forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word),
  REST tb m -> mem_inv rsegs m -> rw_cells rsegs m (v_sp X) (V01_cells X W8 W30 W38 a n) ->
  evt rsegs Post (MS (mkR x1 SP (v_gp X) (v_tp X) x5 x6 x7 (Z_to_bv 64 vid) R9 x10 x11 x12 x13 x14 x15 x16 x17 R18
    (Z_to_bv 64 (v_mm X)) R20 x21 R22 R9 x24 R25 R26 R27 x28 x29 x30 x31) (v_F X) (Z_to_bv 64 0x140cc) (v_fc X) None m
    (seg_rom rsegs)).
Proof.
  intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 HR MI HF.
  nums. pose proof HF as HF0. unfold V01_cells in HF.
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RB & _ & _ & _ & (bm & HB & HE) & _ & Hn & _).
  apply rw_cells_CB_bytes in RB. rewrite Ebuf in RB.
  destruct (mvlan_parent rsegs m _ p vid bs RB Hbs) as (sx & BX & ZX & NX).
  (* 0x14138: mn again, then bnez s5: a duplicate is the join with the same table, else 0x14140 *)
  assert (EXIT : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x28 x29 x30 x31 w21 : word),
     w21 = Z_to_bv 64 (Z.b2z (existsb DF tb)) ->
     evt rsegs Post (MS (mkR x1 SP (v_gp X) (v_tp X) x5 x6 x7 (Z_to_bv 64 vid) R9 x10 x11 x12 x13 x14 x15 x16 x17 R18
       x19 R20 w21 R22 x23 x24 R25 R26 R27 x28 x29 x30 x31) (v_F X) (Z_to_bv 64 0x14138) (v_fc X) None m
       (seg_rom rsegs))).
  { intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y23 y24 y28 y29 y30 y31 w21 E21. subst w21.
    step. step.
    destruct (existsb DF tb) eqn:EB.
    - if_cases K; cbv iota; [|exfalso; vm_compute in K; discriminate K].
      eapply w_join; [exact HR | exact MI | exact HF0 | exact (inv_dup EB)].
    - if_cases K; cbv iota; [exfalso; vm_compute in K; discriminate K|].
      eapply w_nodup; [exact HR | exact MI | exact HF0 | exact EB]. }
  step. step.
  if_cases K; cbv iota.
  - (* mn <= 0: no entry to compare *)
    rewrite bv_lts_zero_l, (unsigned_lit n) in K by lia. apply negb_true_iff, andb_false_iff in K.
    assert (L0 : length tb = 0%nat) by (destruct K as [K|K]; apply Z.ltb_ge in K; lia).
    eapply w_nodup; [exact HR | exact MI | exact HF0 |].
    apply length_zero_iff_nil in L0. rewrite L0. reflexivity.
  - rewrite bv_lts_zero_l, (unsigned_lit n) in K by lia. apply negb_false_iff, andb_true_iff in K.
    destruct K as [K _]. apply Z.ltb_lt in K.
    step. step. step. step. step. step. step. step.
    eapply (dloop m bm sx HB HE BX ZX NX HF0 EXIT (length tb) 0);
      [lia | lia | apply s3_val; lia | reflexivity | f_equal; lia | reflexivity].
Qed.
End Acc.

(** The stretch: from the state 0x140cc the run reaches V01_post, given the join and the tail. *)
Theorem v01_acc : forall X : V01D.vctx, V01D.V01_geo X -> MainB.K_V01 -> V01D.V01_ACC X.
Proof.
  intros X HG (_ & HMC & _ & HSC & _ & _). unfold V01_ACC, V01_ACCat.
  intros i HJ HT tb a p vid bs m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31
    HE HF HJN HB Hbs HRT HGD HFT HMT HFM Hlen HMU HWM Hinv Hi Hig Hsp Hvid.
  destruct HE as (MI & ST & ROM & GG & GV & EV & ENP & RC & MC).
  assert (H32 : (length (v_segs X) <= 32)%nat) by (destruct MC as (bmm & _ & (_ & N32 & _)); exact N32).
  eapply (w_acc X HG HSC HMC i tb a p vid bs HJ HT Hbs Hvid Hinv Hi Hig Hsp H32 m); [| exact MI | exact HF].
  exact (conj ST (conj ROM (conj GG (conj GV (conj EV (conj ENP (conj RC (conj MC (conj HJN (conj HB (conj HRT
    (conj HGD (conj HFT (conj HMT (conj HFM (conj Hlen (conj HMU HWM))))))))))))))))).
Qed.
