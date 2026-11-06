(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/fuzz_catalogue_row.v, with its module paths, module names, addresses and numbers changed; 265 of its 363 lines of code are new or changed and 201 lines of the source are left out. *)
(** m_find (UBSan build, 0x14ccc, 208 bytes): proof of [m_find_contract] (U/Prog/m_find_c.v) from the contracts of
    its two callees, strlen (U/Prog/strlen_c.v, 0x1f5cc) and bcmp (U/Prog/bcmp_c.v, 0x1edc8). Written new; the
    plain walk is lib/Prog/m_find.v.

    Code (the UBSan build's disassembly):
      0x14ccc-0x14cec  frame of 64: ra s0 s1 s2 s3 s4 s5 s6 at sp+56 .. sp+0
      0x14cf0 mv s0,a0; andi a0,a0,3; 0x14cf8 bnez a0 -> TRAP (c 4-aligned)
      0x14cfc lui a0,2; add a0,s0,a0; 0x14d04 lw a0,0(a0) (n = c->n); 0x14d08 blez a0 -> NONE
      0x14d0c s1 = len; s2 = name; s3 = 0; s4 = ~c; s5 = (n > 0 ? n : 0) = n; s6 = 32
      LOOP 0x14d2c beqz s6 -> TRAP (i = 32); 0x14d30 bltu s4,s3 -> TRAP (c + 256 i wraps)
           mv a0,s0; 0x14d38 jal strlen; 0x14d3c bne a0,s1 -> NEXT
           mv a0,s0; mv a1,s2; mv a2,s1; 0x14d4c jal bcmp; 0x14d50 beqz a0 -> EPI (a0 = s0 = &c->seg[k])
      NEXT 0x14d54 s5 -= 1; s0 += 0x100; s3 += 0x100; s6 -= 1; 0x14d64 bnez s5 -> LOOP
      NONE 0x14d68 mv s0,zero
      EPI  0x14d6c mv a0,s0; restore ra s0-s6; addi sp,sp,64; ret.  TRAP 0x14d98 unimp
    The traps are not reached: c mod 16 = 0, i < n <= 32 (mconf_enc), c + 9236 <= 2^64 (bytes_at of the block).
    The rest as the plain walk: strlen gets the name of c->seg[k], its NUL and the rest of the 16-byte name field as
    slack; bcmp gets the name and the n bytes at name; the model side through U/Spec/SegBridge.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require Import StrFun SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strlen_c bcmp_c m_find_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists, bytes and words (the forms of seg_query_facts.v's sq_* lemmas this walk uses) *)
Lemma mf_skipn_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d H; cbn [length] in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma mf_fld_fld : forall (l : list byte) a n b k, (a + n <= k)%nat -> fld a n (fld b k l) = fld (b + a) n l.
Proof.
  intros l a n b k H. unfold fld. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  rewrite Nat.min_l by lia. rewrite Nat.add_comm. reflexivity.
Qed.

Lemma mf_firstn_S : forall (l : list byte) n d, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction l as [|x l IH]; intros n d H; cbn [length] in H; [lia|].
  destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma mf_byte_eq : forall x y : byte, bv_unsigned x = bv_unsigned y -> x = y.
Proof. intros x y H. apply bv_eq. exact H. Qed.

Lemma mf_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(** `lw` of a small non-negative word. *)
Lemma mf_sx32 : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2^31). lia.
Qed.

(** ** The model *)
Lemma mf_go_step : forall segs nm k, (k < length segs)%nat ->
  m_find_go (skipn k segs) nm k =
  if (SegModel.strlen (ms_name (nth k segs mseg_d)) =? length nm)%nat &&
     SegModel.leqb (firstn (length nm) (ms_name (nth k segs mseg_d))) nm
  then Some k else m_find_go (skipn (S k) segs) nm (S k).
Proof. intros segs nm k H. rewrite (mf_skipn_cons segs k mseg_d H). reflexivity. Qed.

Lemma mf_go_end : forall segs nm, m_find_go (skipn (length segs) segs) nm (length segs) = None.
Proof. intros segs nm. rewrite skipn_all. reflexivity. Qed.

(** m_find_go's test on a name of bytes sx against the bytes l: false when the lengths differ, the [leqb] that
    bcmp's zero decides when they agree. *)
Lemma mf_cond_ne : forall sx l : list byte, ~ In (Z_to_bv 8 0) sx -> length sx <> length l ->
  (SegModel.strlen (zs sx) =? length (zs l))%nat && SegModel.leqb (firstn (length (zs l)) (zs sx)) (zs l) = false.
Proof.
  intros sx l H E. rewrite bridge_strlen by exact H.
  assert (Lz : length (zs l) = length l) by (unfold zs; apply length_map). rewrite Lz.
  destruct (Nat.eqb_spec (length sx) (length l)) as [Q|Q]; [contradiction | reflexivity].
Qed.

Lemma mf_cond_eq : forall sx l : list byte, ~ In (Z_to_bv 8 0) sx -> length sx = length l ->
  (SegModel.strlen (zs sx) =? length (zs l))%nat && SegModel.leqb (firstn (length (zs l)) (zs sx)) (zs l) =
  SegModel.leqb (zs sx) (zs l).
Proof.
  intros sx l H E. rewrite bridge_strlen by exact H.
  assert (Lz : length (zs l) = length sx) by (unfold zs; rewrite length_map; symmetry; exact E).
  rewrite Lz, Nat.eqb_refl, andb_true_l. rewrite firstn_all2; [reflexivity|].
  unfold zs. rewrite length_map. lia.
Qed.

Lemma mf_mm_range : forall n (l r : list byte) v, StrFun.memcmp_model l r n = Some v -> -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v H.
  - cbn in H. injection H as <-. lia.
  - destruct l as [|a l]; [cbn in H; discriminate|]. destruct r as [|b r]; [cbn in H; discriminate|].
    cbn [StrFun.memcmp_model] in H.
    destruct (bv_unsigned a =? bv_unsigned b); [exact (IH l r v H)|].
    injection H as <-. pose proof (byte_range a). pose proof (byte_range b). lia.
Qed.

(** ** Words *)
Lemma mf_eqb0 : forall v, -2^64 < v < 2^64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [E|E]; [subst; reflexivity|]. apply Z.eqb_neq. intros E'.
  apply E. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

(** strlen's slack: a 16-aligned 16-byte field holds the name, its NUL and the rest of the field, which reaches
    the next 8-byte boundary after the NUL. *)
Lemma mf_slack : forall a (sx sl : list byte), a mod 16 = 0 -> (length sx + 1 + length sl = 16)%nat ->
  (- (a + Z.of_nat (length sx) + 1)) mod 8 <= Z.of_nat (length sl).
Proof. intros a sx sl Ha Hl. Z.div_mod_to_equations. lia. Qed.

Lemma mf_mod16 : forall c k, c mod 16 = 0 -> (c + 256 * Z.of_nat k) mod 16 = 0.
Proof. intros c k H. Z.div_mod_to_equations. lia. Qed.

(** The values the prologue computes. *)
Lemma mf_andi3 : forall c, 0 <= c < 2^64 -> c mod 16 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 c)) 3 = 0.
Proof.
  intros c Hc H. rewrite unsigned_lit by lia. change 3 with (Z.ones 2).
  rewrite Z.land_ones by lia. change (2 ^ 2) with 4. Z.div_mod_to_equations. lia.
Qed.

(** s4 = ~c (`not s4,s0`, as the step leaves it). *)
Lemma mf_not : forall c, 0 <= c < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) 18446744073709551615)) = 18446744073709551615 - c.
Proof.
  intros c Hc. rewrite (unsigned_lit c) by lia. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia.
Qed.

Lemma mf_slt_pos : forall n, 0 < n < 2^63 -> v_slt (Z_to_bv 64 0) (Z_to_bv 64 n) = Z_to_bv 64 1.
Proof.
  intros n Hn. unfold v_slt, c_lts. rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace ((0 <? n) && (n <? 2^63)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(** s5 = (n > 0 ? n : 0) = n (`sgtz a1,a0; neg a1,a1; and s5,a1,a0`, as the steps leave it). *)
Lemma mf_s5 : forall n, 0 < n < 2^63 ->
  Z.land (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_slt (Z_to_bv 64 0) (Z_to_bv 64 n))))) (bv_unsigned (Z_to_bv 64 n))
  = n.
Proof.
  intros n Hn. rewrite mf_slt_pos by lia. rewrite (unsigned_lit 1), (unsigned_lit n) by lia.
  change (bv_unsigned (Z_to_bv 64 (0 - 1))) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(** A branch that the facts in the context say is not taken (the traps). *)
Ltac mf_ntk := let K := fresh "K" in if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia | clear K].

(** A register equation the steps leave. *)
Ltac mf_eq := first [assumption | f_equal; lia | reflexivity].

(** ** Memory *)
Section Mem.
Variable segs : list Segment.

Lemma mf_bytes_at_sub : forall m a bs k n, bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H L.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(** m->n: the 4 bytes at m + 0x2000. *)
Lemma mf_n : forall m c bs mc, bytes_at segs m c bs -> mconf_enc mc bs ->
  ov_read_bytes segs m (wa (c + MC_N)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc))))).
Proof.
  intros m c bs mc HB HE. destruct HE as (L & _ & _ & (_ & HN) & _). unfold fldz in HN. unfold SEG_M_SIZE in L.
  rewrite (bytes_at_read segs m c bs MC_N 4 HB) by (unfold MC_N; lia).
  rewrite <- HN. reflexivity.
Qed.

(** The name field of m->seg[k]: the name sx, its NUL and the rest sl of the 16 bytes. *)
Lemma mf_name : forall m a bs mc k, bytes_at segs m a bs -> mconf_enc mc bs -> (k < length (mc_seg mc))%nat ->
  exists sx sl, bytes_at segs m (a + 256 * Z.of_nat k) (sx ++ ZERO :: sl) /\ ~ In (Z_to_bv 8 0) sx /\
    zs sx = ms_name (nth k (mc_seg mc) mseg_d) /\ (length sx + 1 + length sl = 16)%nat.
Proof.
  intros m a bs mc k HB (L & L32 & HS & _) Hk.
  destruct (HS k Hk) as (Lf & (HL & Hlt & HN & HF) & _).
  unfold SEG_M_SIZE in L.
  rewrite mf_fld_fld in HL, HF by lia. rewrite Nat.add_0_r in HL, HF.
  remember (ms_name (nth k (mc_seg mc) mseg_d)) as s eqn:Es.
  remember (fld (256 * k) 16 bs) as g eqn:Eg.
  assert (G : firstn (S (length s)) g = firstn (length s) g ++ [nth (length s) g ZERO]) by (apply mf_firstn_S; lia).
  unfold zs in HF. rewrite firstn_map, G, map_app in HF. cbn [map] in HF.
  apply app_inj_tail in HF as [H1 H2].
  assert (Z0 : nth (length s) g ZERO = Z_to_bv 8 0) by (apply mf_byte_eq; rewrite H2; reflexivity).
  assert (Eg2 : g = firstn (length s) g ++ ZERO :: skipn (S (length s)) g).
  { rewrite <- (firstn_skipn (S (length s)) g) at 1. rewrite G, Z0, <- app_assoc. reflexivity. }
  exists (firstn (length s) g), (skipn (S (length s)) g).
  split; [|split; [|split]].
  - rewrite <- Eg2. subst g.
    replace (a + 256 * Z.of_nat k) with (a + Z.of_nat (256 * k)) by lia.
    unfold fld. apply mf_bytes_at_sub; [exact HB | lia].
  - apply nul_free_bytes. unfold zs. rewrite H1. exact HN.
  - unfold zs. exact H1.
  - rewrite length_firstn, length_skipn. lia.
Qed.

End Mem.

(** ** The walk *)
Section Find.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (c name Sp lo : Z) (bs l : list byte) (mc : mconf).
Hypothesis HSL : strlen_contract.
Hypothesis HBC : bcmp_contract.
Hypothesis HB0 : bytes_at rsegs m0 c bs.
Hypothesis HE : mconf_enc mc bs.
Hypothesis HL : Z.of_nat (length bs) = 9236.
Hypothesis Hc : 0 < c.
Hypothesis Hc16 : c mod 16 = 0.
Hypothesis Hcb : c + 9236 <= 2^64.
Hypothesis HcA : c + 9236 <= lo \/ Sp <= c.
Hypothesis HN0 : bytes_at rsegs m0 name l.
Hypothesis Hname : 0 <= name < 2^64.
Hypothesis Hn : Z.of_nat (length l) < 2^64.
Hypothesis HnA : name + Z.of_nat (length l) <= lo \/ Sp <= name.
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 64 <= Sp.
Hypothesis HS : Sp < 2^64.

Local Abbreviation Post := (fun ms' : machine_state =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (m_find_ptr c mc (zs l)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp - 64, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp).

(** The frame between the prologue and the epilogue. *)
Definition frm (m : word -> option byte) : Prop :=
  rw_cells rsegs m (Sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (Sp + -64) /\ munch [(Sp - 64, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

Lemma frm_mi : forall m, frm m -> mem_inv rsegs m.
Proof. intros m (_ & _ & _ & _ & MI). exact MI. Qed.

Lemma frm_blk : forall m, frm m -> bytes_at rsegs m c bs.
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HB0 | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma frm_name : forall m, frm m -> bytes_at rsegs m name l.
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HN0 | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** strlen and bcmp write nothing. *)
Lemma frm_call : forall m m', frm m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm m'.
Proof.
  intros m m' (FR & ST & MU & WM & _) MU' WM' MI'.
  split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I]|].
  split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; intros x _; exact I|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
Qed.

Lemma mf_nlt : (length (mc_seg mc) <= 32)%nat.
Proof. destruct HE as (_ & H & _). exact H. Qed.

(** The exit 0x14d6c: a0 = s0 = r, restore ra and s0-s6, return. *)
Lemma epi : forall r m (x1 y0 y1 y2 w9 w10 w11 w12 z3 z4 z5 z6 z7 w18 w19 w20 w21 w22 u3 u4 u5 u6 : word),
  r = m_find_ptr c mc (zs l) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -64)) gp tp y0 y1 y2 (Z_to_bv 64 r) w9 w10 w11 w12 z3 z4 z5 z6 z7
             w18 w19 w20 w21 w22 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x14d6c) fc None m (seg_rom rsegs)).
Proof.
  intros r m x1 y0 y1 y2 w9 w10 w11 w12 z3 z4 z5 z6 z7 w18 w19 w20 w21 w22 u3 u4 u5 u6 Er (FR & ST & MU & WM & MI).
  do 11 step.
  apply evt_done. exists y0, y1, y2, w11, w12, z3, z4, z5, z6, z7, u3, u4, u5, u6, m.
  split; [subst r; unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  pose proof (stk_release rsegs m lo (Sp + -64) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -64 + Z.of_nat 64) with Sp in R by lia. exact R.
Qed.

(** The loop head 0x14d2c with k entries done (none of them named l) and j = n - k left: s0 = &c->seg[k],
    s1 = n, s2 = name, s3 = 256 k, s4 = ~c, s5 = j, s6 = 32 - k. *)
Lemma loop : forall j k m (x1 y0 y1 y2 w10 w11 w12 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w9 w18 w19 w20 w21 w22 : word),
  w8 = Z_to_bv 64 (c + 256 * Z.of_nat k) -> w9 = Z_to_bv 64 (Z.of_nat (length l)) ->
  w18 = Z_to_bv 64 name -> w19 = Z_to_bv 64 (256 * Z.of_nat k) ->
  bv_unsigned w20 = 18446744073709551615 - c -> w21 = Z_to_bv 64 (Z.of_nat j) ->
  w22 = Z_to_bv 64 (32 - Z.of_nat k) ->
  (k + j = length (mc_seg mc))%nat -> (0 < j)%nat ->
  m_find mc (zs l) = m_find_go (skipn k (mc_seg mc)) (zs l) k -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -64)) gp tp y0 y1 y2 w8 w9 w10 w11 w12 z3 z4 z5 z6 z7 w18 w19 w20 w21 w22
             s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x14d2c) fc None m (seg_rom rsegs)).
Proof.
  induction j as [|j IH];
    intros k m x1 y0 y1 y2 w10 w11 w12 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w9 w18 w19 w20 w21 w22
      E8 E9 E18 E19 E20 E21 E22 Hkj Hj RF FRM; [lia|].
  subst w8 w9 w18 w19 w21 w22. pose proof mf_nlt as NL.
  assert (Hk : (k < length (mc_seg mc))%nat) by lia.
  destruct (mf_name rsegs m c bs mc k (frm_blk m FRM) HE Hk) as (sx & sl & HX & HXN & HXZ & HXL).
  rewrite (mf_go_step _ (zs l) k Hk), <- HXZ in RF.
  (* 0x14d54: the next entry, or the end of the table. *)
  assert (NEXT : forall m' (x1' y0' y1' y2' w10' w11' w12' z3' z4' z5' z6' z7' u3' u4' u5' u6' : word),
    m_find mc (zs l) = m_find_go (skipn (S k) (mc_seg mc)) (zs l) (S k) -> frm m' ->
    evt rsegs Post
      (MS (mkR x1' (Z_to_bv 64 (Sp + -64)) gp tp y0' y1' y2' (Z_to_bv 64 (c + 256 * Z.of_nat k))
               (Z_to_bv 64 (Z.of_nat (length l))) w10' w11' w12' z3' z4' z5' z6' z7'
               (Z_to_bv 64 name) (Z_to_bv 64 (256 * Z.of_nat k)) w20 (Z_to_bv 64 (Z.of_nat (S j)))
               (Z_to_bv 64 (32 - Z.of_nat k)) s7 s8 s9 s10 s11 u3' u4' u5' u6')
          F (Z_to_bv 64 0x14d54) fc None m' (seg_rom rsegs))).
  { intros m' x1' y0' y1' y2' w10' w11' w12' z3' z4' z5' z6' z7' u3' u4' u5' u6' RF' FRM'.
    do 5 step.
    rewrite mf_eqb_lit by lia.
    destruct (Z.eqb_spec (Z.of_nat (S j) + -1) 0) as [J0|J0]; cbn [negb]; cbv iota.
    - (* that was the last entry: NULL *)
      assert (j = 0%nat) by lia. subst j.
      replace (S k) with (length (mc_seg mc)) in RF' by lia. rewrite mf_go_end in RF'.
      step.
      eapply epi; [|exact FRM'].
      unfold m_find_ptr. rewrite RF'. reflexivity.
    - eapply (IH (S k)); [mf_eq | mf_eq | mf_eq | mf_eq | mf_eq | mf_eq | mf_eq | lia | lia | exact RF' | exact FRM']. }
  (* the traps: i = 32, c + 256 i wrapping *)
  step. mf_ntk.
  step. mf_ntk.
  (* strlen(c->seg[k].name) *)
  step. step.
  eapply evt_cut.
  { eapply HSL with (str := sx) (slack := sl); rewrite ?unsigned_lit by lia.
    - exact HX.
    - exact HXN.
    - apply mf_slack; [apply mf_mod16; exact Hc16 | exact HXL].
    - exact (frm_mi m FRM). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
              MU1 & WM1 & MI1 & BS1).
  pose proof (frm_call m m1 FRM MU1 WM1 MI1) as FRM1.
  rewrite unsigned_lit in BS1 by lia. apply bytes_at_app in BS1 as [BX1 _].
  clear MU1 WM1.
  rewrite ret_pc_even by (try lia; reflexivity).
  step.
  rewrite mf_eqb_lit by lia.
  destruct (Z.eqb_spec (Z.of_nat (length sx)) (Z.of_nat (length l))) as [EL|EL]; cbn [negb]; cbv iota.
  - (* strlen = n: bcmp(c->seg[k].name, name, n) *)
    apply Nat2Z.inj in EL.
    step. step. step. step.
    destruct (bridge_memcmp_total sx l (length l) EL eq_refl) as (v & Hv & _).
    pose proof (bridge_memcmp_leqb sx l (length l) v EL eq_refl Hv) as VQ.
    pose proof (mf_mm_range _ _ _ _ Hv) as VR.
    eapply evt_cut.
    { eapply HBC with (ls := sx) (rs := l) (v := v); rewrite ?unsigned_lit by lia.
      - exact BX1.
      - exact (frm_name m1 FRM1).
      - rewrite Nat2Z.id. exact Hv.
      - exact MI1. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                m2 & -> & MU2 & WM2 & MI2 & _ & _).
    pose proof (frm_call m1 m2 FRM1 MU2 WM2 MI2) as FRM2.
    clear MU2 WM2.
    rewrite ret_pc_even by (try lia; reflexivity).
    step.
    rewrite mf_eqb0 by lia.
    rewrite (mf_cond_eq sx l HXN EL), <- VQ in RF.
    destruct (v =? 0) eqn:V0; rewrite ?V0 in RF; cbv iota in RF |- *.
    + (* the entry is l's: &c->seg[k] *)
      eapply epi; [|exact FRM2].
      unfold m_find_ptr. rewrite RF. unfold mseg_addr, MSEG_SIZE. reflexivity.
    + eapply NEXT; [exact RF | exact FRM2].
  - (* strlen <> n: the next entry *)
    rewrite (mf_cond_ne sx l HXN) in RF by (intros E; apply EL; rewrite E; reflexivity).
    cbv iota in RF.
    eapply NEXT; [exact RF | exact FRM1].
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 name)
             (Z_to_bv 64 (Z.of_nat (length l))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ccc) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypotheses [loop] and [epi] use: take them
     first. *)
  pose proof (loop (length (mc_seg mc)) 0) as LP. pose proof epi as EP. pose proof mf_nlt as NL.
  pose proof (munch_refl [(Sp - 64, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 64 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 64) with 64 in ST1, FR.
  replace (Sp - 64) with (Sp + -64) in ST1, FR by lia.
  do 9 step.
  pose proof (mf_n rsegs _ c bs mc HB0 HE) as RN. unfold MC_N in RN.
  step.
  step. rewrite mf_andi3 by lia.
  step. rewrite mf_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  step. step. step.
  rewrite mf_sx32 by lia.
  step.
  rewrite bv_lts_zero_l, unsigned_lit by lia.
  replace (Z.of_nat (length (mc_seg mc)) <? 2^63) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite andb_true_r.
  destruct (Z.ltb_spec 0 (Z.of_nat (length (mc_seg mc)))) as [P|P]; cbn [negb]; cbv iota.
  - do 8 step.
    eapply LP; [ mf_eq | mf_eq | mf_eq | mf_eq | apply mf_not; lia | f_equal; apply mf_s5; lia | mf_eq
               | lia | lia | reflexivity | ].
    refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
  - (* no entry: NULL *)
    step.
    eapply EP; [|refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption].
    unfold m_find_ptr, m_find. destruct (mc_seg mc) as [|e r] eqn:Eq; [reflexivity|].
    cbn [length] in P. lia.
Qed.

End Find.

Theorem m_find_holds : strlen_contract -> bcmp_contract -> m_find_contract.
Proof.
  intros HSL HBC. unfold m_find_contract, m_find_pre, M_FIND_STACK, M_FIND.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo mc l
    (Hc0 & Hc16 & (bs & HB & HE) & HcA & HN & HLn & HnA & (ST & HK & H16 & HW) & MI).
  unfold apart, SEG_M_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  change (bv_modulus 64) with (2^64) in Rsp, Ra0, Ra1, Ra2.
  pose proof HE as (HL & _).
  unfold SEG_M_SIZE in HL.
  pose proof (bytes_at_bound _ _ _ _ HB) as Bc.
  pose proof (proj1 ST) as Hlo.
  rewrite <- HLn in HnA, Ra2.
  assert (Ea2 : a2 = Z_to_bv 64 (Z.of_nat (length l))) by (rewrite HLn; symmetry; apply Z_to_bv_lit_self).
  subst a2. clear HLn.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  pose proof (Z_to_bv_lit_self a1) as Ea1.
  set (Sp := bv_unsigned sp) in *. set (c := bv_unsigned a0) in *. set (name := bv_unsigned a1) in *.
  rewrite <- Esp, <- Ea0, <- Ea1. clearbody Sp c name. clear Esp Ea0 Ea1.
  eapply evt_mono.
  - eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m c name Sp lo bs l mc);
      first [eassumption | lia].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI' & ST').
    unfold ret_post. rewrite unsigned_lit by lia.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST' | exact I].
Qed.
