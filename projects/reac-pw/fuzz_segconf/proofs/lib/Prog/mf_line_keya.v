(** m_file (plain build, image 3776ca44d75c, 0x13fb4): the sub-piece S_MF_KEYA of the line walk (Prog/mf_cuts.v,
    family F3). From the cut KEY 0x14200 (m_key inline, fuzz_segconf.c:197-211; the stripped line sl = [s, e) in
    s5 / s6, its first byte not '[') to the cut KDISP 0x142f8 or, through m_refuse, to the tail 0x143d4:
    - 0x14200-0x14208 memchr(s, '=', e - s); 0x1420c `ld a1, 0x20(sp)` (the cur cell); cur = NULL (0x14210) or no
      '=' (0x14214) go to 0x143c8: m_refuse(c, line + 1) (0x143d0), then the tail with m_key = m_refuse;
    - else the key strip on [s, eq): forward 0x14218-0x14240 (s5), backward 0x14244-0x14268 (a1); the value strip on
      [eq + 1, e): forward 0x1426c-0x14290 (s4), backward 0x14294-0x142b4 (s6); the quote pair 0x142b8-0x142ec;
      s8 = the key's length, s7 = the value's (0x142f0 / 0x142f4); then KDISP with the step mk_disp.
    The strip loops' invariants are the index facts [ka_fwd] / [ka_bwd] (the blank test as the code computes it:
    `bltu s11 (= ' ')`, then bit c of 0x100002200); memchr writes nothing, so the walk after it runs on the memory
    memchr returns, and the post moves back to the cut's memory with mf_common.mf_post_back. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c mf_cuts
  mfu_facts m_refuse_c memchr_c mf_common mfp_facts.
Import ListNotations.
Open Scope Z_scope.

(** ** Bytes *)
Lemma ka_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma ka_zxb : forall x, 0 <= x < 256 -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zxb. rewrite (ka_u8 x Hx). reflexivity. Qed.

Lemma ka_blank_gt : forall x, 32 < x -> blank x = false.
Proof.
  intros x Hx. unfold blank.
  rewrite (proj2 (Z.eqb_neq x 32)), (proj2 (Z.eqb_neq x 9)), (proj2 (Z.eqb_neq x 13)) by lia. reflexivity.
Qed.

(** The blank test of the loops: bit c of the mask 0x100002200 (bits 9, 13, 32) for c <= ' '. *)
Lemma ka_bit_raw : forall x, 0 <= x <= 32 -> Z.land (Z.shiftr 4294976000 x) 1 = if blank x then 1 else 0.
Proof.
  intros x Hx. replace x with (Z.of_nat (Z.to_nat x)) by lia.
  assert (Hn : (Z.to_nat x <= 32)%nat) by lia. revert Hn. generalize (Z.to_nat x) as k. intros k Hk. clear Hx.
  do 33 (destruct k as [|k]; [reflexivity|]). lia.
Qed.

Lemma ka_bit : forall x, 0 <= x <= 32 -> Z.land (Z.shiftr 4294976000 (x mod 64)) 1 = if blank x then 1 else 0.
Proof. intros x Hx. rewrite Z.mod_small by lia. apply ka_bit_raw. exact Hx. Qed.

(** ** memchr over the bytes of a list *)
Lemma ka_find_byte : forall l c, Forall (fun x => 0 <= x < 256) l -> find_byte c (zb l) = SegModel.memchr l c.
Proof.
  unfold zb. induction l as [|b l IH]; intros c H; [reflexivity|].
  inversion H as [|? ? Hb Hl]; subst. cbn [map find_byte SegModel.memchr]. rewrite (ka_u8 b Hb).
  destruct (b =? c); [reflexivity|]. rewrite (IH c Hl). destruct (SegModel.memchr l c); reflexivity.
Qed.

Lemma ka_memchr_ok : forall A c n buf, n <= Z.of_nat (length buf) -> memchr_ok A c n buf.
Proof. intros A c n buf H. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat n) buf)); [left|]; exact H. Qed.

Lemma ka_memchr_res : forall A (w1 w2 : word) l, bv_unsigned w1 mod 256 = 61 ->
  bv_unsigned w2 = Z.of_nat (length l) -> Forall (fun x => 0 <= x < 256) l ->
  memchr_res A (bv_unsigned w1 mod 256) (bv_unsigned w2) (zb l) =
  match SegModel.memchr l 61 with Some e => A + Z.of_nat e | None => 0 end.
Proof.
  intros A w1 w2 l H1 H2 H3. unfold memchr_res. rewrite H1, H2, Nat2Z.id.
  rewrite firstn_all2 by (unfold zb; rewrite length_map; lia).
  rewrite (ka_find_byte l 61 H3). reflexivity.
Qed.

Lemma ka_Forall_fs : forall {A} (P : A -> Prop) l a b, Forall P l -> Forall P (firstn a (skipn b l)).
Proof.
  intros A P l a b H. rewrite Forall_forall in H |- *. intros x Hx. apply H.
  rewrite <- (firstn_skipn b l). apply in_or_app. right.
  rewrite <- (firstn_skipn a (skipn b l)). apply in_or_app. left. exact Hx.
Qed.

(** ** Slices of the line *)
Lemma ka_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (mf_line_rest rest) as [[H _]|[H _]]; apply (f_equal (@length Z)) in H;
    [rewrite length_app in H; cbn [length] in H|]; lia.
Qed.

Lemma ka_firstn_slice : forall (L : list Z) I J e, (e <= J - I)%nat -> firstn e (slice I J L) = slice I (I + e) L.
Proof.
  intros L I J e H. unfold slice. rewrite firstn_firstn. replace (Nat.min e (J - I)) with e by lia.
  replace (I + e - I)%nat with e by lia. reflexivity.
Qed.

Lemma ka_skipn_slice : forall (L : list Z) I J e, (e <= J - I)%nat -> skipn e (slice I J L) = slice (I + e) J L.
Proof.
  intros L I J e H. unfold slice. rewrite skipn_firstn_comm, skipn_skipn.
  replace (J - (I + e))%nat with (J - I - e)%nat by lia. replace (e + I)%nat with (I + e)%nat by lia. reflexivity.
Qed.

(** The strip loops' results: the forward loop from a stops at the first non-blank o (or at b), the backward loop
    from b stops at o' with u[o' - 1] not blank (or at a). *)
Definition ka_fwd (L : list Z) (a b o : nat) : Prop :=
  (a <= o <= b)%nat /\ all_blank L a o /\ (o = b \/ blank (nth o L 0) = false).
Definition ka_bwd (L : list Z) (a b o : nat) : Prop :=
  (a <= o <= b)%nat /\ all_blank L o b /\ (o = a \/ blank (nth (o - 1) L 0) = false).

Lemma ka_strip_slice : forall L x y o o', (y <= length L)%nat -> ka_fwd L x y o -> ka_bwd L o y o' ->
  h_strip (slice x y L) = slice o o' L.
Proof.
  intros L x y o o' Hy (Ho & Hf1 & Hf2) (Ho' & Hb1 & Hb2).
  assert (Len : length (slice x y L) = (y - x)%nat) by (apply slice_length; lia).
  rewrite (h_strip_idx (slice x y L) (o - x) (o' - x)).
  - rewrite slice_slice by lia. f_equal; lia.
  - rewrite Len. lia.
  - unfold all_blank. intros k Hk. rewrite slice_nth by lia. apply Hf1. lia.
  - rewrite Len. destruct (Nat.eq_dec o y) as [->|Hoy]; [left; lia|right].
    destruct Hf2 as [Hf2|Hf2]; [lia|].
    rewrite slice_nth by lia. replace (x + (o - x))%nat with o by lia. exact Hf2.
  - unfold all_blank. rewrite Len. intros k Hk. rewrite slice_nth by lia. apply Hb1. lia.
  - destruct (Nat.eq_dec o' o) as [->|Hne]; [left; reflexivity|].
    destruct Hb2 as [Hb2|Hb2]; [lia|right].
    rewrite slice_nth by lia. replace (x + (o' - x - 1))%nat with (o' - 1)%nat by lia. exact Hb2.
Qed.

Lemma ka_unquote_slice : forall (L : list Z) vs ve, (vs <= ve <= length L)%nat ->
  h_unquote (slice vs ve L) =
  if (2 <=? ve - vs)%nat && ((nth vs L 0 =? DQ) || (nth vs L 0 =? SQ)) && (nth (ve - 1) L 0 =? nth vs L 0)
  then slice (S vs) (ve - 1) L else slice vs ve L.
Proof.
  intros L vs ve H. rewrite h_unquote_idx. rewrite slice_length by lia.
  destruct (Nat.leb_spec 2 (ve - vs)) as [H2|H2]; cbn [andb]; [|reflexivity].
  rewrite !slice_nth by lia. replace (vs + 0)%nat with vs by lia.
  replace (vs + (ve - vs - 1))%nat with (ve - 1)%nat by lia.
  match goal with |- (if ?b then _ else _) = _ => destruct b end; [|reflexivity].
  rewrite slice_slice by lia. f_equal; lia.
Qed.

(** ** Frame cells and the memory memchr returns *)
Lemma ka_cell8_rd : forall m a v, cell8 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold cell8 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite length_le8; lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. rewrite R. f_equal.
  all: cbn [skipn]; apply firstn_all2; rewrite length_le8; lia.
Qed.

Lemma ka_seg32 : forall m c mc, mconf_at rsegs m c mc -> (length (mc_seg mc) <= 32)%nat.
Proof. intros m c mc (bs & _ & HE). unfold mconf_enc, mconf_encp in HE. destruct HE as (_ & H & _). exact H. Qed.

(** A callee that writes nothing keeps the loop facts. *)
Lemma ka_loop_nil : forall m m1, munch [] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  forall fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  m_file_loop m1 fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m m1 MU WM MI fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 HL.
  apply mf_loop_iff in HL as (HC & HX & HS). apply mf_loop_iff.
  destruct HS as (HMC & HCE & HR).
  pose proof HC as HC'. unfold mf_ctx in HC'.
  destruct HC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FRM & _) & _ & _ & (STK & _) & _).
  split; [|split].
  - eapply mf_ctx_transport; [exact HC | exact MU | exact WM | exact MI | | exact FRM | | apply sub_fp_nil].
    + eapply mf_task_mem with (pend := false); [exact HC | exact HMC | exact MU | apply sub_fp_nil].
    + eapply stk_transport_disjoint; [exact STK | exact MU | exact WM | exact I].
  - eapply mf_text_transport; [exact HX | exact MU | apply sub_fp_nil].
  - split; [|split; [|exact HR]].
    + destruct HMC as (bs & B & EN). exists bs. split; [|exact EN].
      eapply bytes_at_transport; [exact B | exact MU | exact I].
    + eapply cell8_transport; [exact HCE | exact MU | exact I].
Qed.

(** ** The refusal 0x143c8-0x143d0: m_refuse(c, line + 1), then the tail with (m_refuse mc (line + 1) false, cur) *)
Lemma ka_refuse : m_refuse_contract -> forall n, H_MF_TAIL n ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
    (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat)
    (k0 : nat) (rest : list Z),
  (length rest <= n)%nat -> rest <> [] ->
  m_file_loop m fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
    ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  m_file_regs c (mf_next p rest) (line + 1) s0 s1 s2 s3 s7 s8 s9 s10 s11 ->
  evt rsegs
    (mf_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0
       (mf_fin (m_refuse mc (line + 1) false, cur) line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x143c8) fc None m (seg_rom rsegs)).
Proof.
  intros HMR n HT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest Hn Hne HL HR.
  pose proof HL as HL0. apply mf_loop_iff in HL0 as (HC & HX & HS).
  destruct HS as (HMC & HCE & HCO & HK0 & Hl0 & Hl1 & Hr & Ho).
  pose proof HC as HC'. unfold mf_ctx in HC'. destruct HC' as (Hspf & _).
  assert (Hlen : (0 < length rest)%nat) by (destruct rest; [congruence | cbn [length]; lia]).
  destruct HR as (-> & -> & -> & -> & -> & -> & -> & -> & ->).
  step. step. step.
  eapply (mf_refuse_call HMR 0x143d0) with (knock := false) (mc := mc);
    [lia | lia | reflexivity | exact HC | exact HX | exact HCE | exact HMC | lia | lia |].
  intros m' F' fc' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HC1 HX1 HCE1 HMC1 MU1 WM1 HF1.
  destruct (m_refuse_sizes mc (line + 1) false) as [Eseg Ekept].
  assert (Hcur' : cur_ok (m_refuse mc (line + 1) false) cur).
  { destruct cur as [gi|]; [|exact I]. unfold cur_ok in *. rewrite Eseg. exact HCO. }
  assert (Hkept' : (k0 <= length (mc_kept (m_refuse mc (line + 1) false)))%nat) by lia.
  eapply mf_post_back with (F1 := F') (m1 := m') (W1 := m_refuse_W (bv_unsigned sp) c mc);
    [exact HF1 | exact MU1 | exact WM1 | |].
  - apply (sub_fp_trans _ (M_FILE_W (bv_unsigned sp0) c k0 (m_refuse mc (line + 1) false))).
    + apply mf_W_refuse; [unfold M_FILE_STACK, M_FILE_FRAME, M_REFUSE_STACK in *; lia | unfold M_FILE_FRAME in *; lia |
                          exact HK0].
    + apply (mf_W_fin (bv_unsigned sp0) c k0 (m_refuse mc (line + 1) false, cur) line rest). exact Hcur'.
  - unfold mf_post, mf_fin. eapply HT.
    + pose proof (mf_rest_lt rest Hne). lia.
    + eapply mf_tail_loop; [exact HC1 | exact HX1 | exact Hne | exact HMC1 | exact HCE1 | exact Hcur' | exact Hkept' |
                            exact Hl0 | exact Hl1 | |].
      * apply (mf_cnt_next (mc_refused mc)); [exact Hne | exact Hr | unfold m_refuse; cbn [mc_refused]; lia].
      * apply (mf_cnt_next (mc_overflow mc)); [exact Hne | exact Ho | unfold m_refuse; cbn [mc_overflow]; lia].
    + unfold m_file_regs; repeat split.
Qed.

(** ** The strips and the quotes, 0x14218-0x142f8
    The walk runs on one memory (memchr's); the registers it does not touch are fixed here. [L] is the line at p:
    its bytes readable and below 256, p + |L| below 2^64 ([ka_text]). *)
Definition ka_text (m : word -> option byte) (p : Z) (L : list Z) : Prop :=
  (forall o, (o < length L)%nat -> ov_read_bytes rsegs m (wa (p + Z.of_nat o)) 1 = Some [Z_to_bv 8 (nth o L 0)]) /\
  (forall o, 0 <= nth o L 0 < 256) /\ 0 < p /\ p + Z.of_nat (length L) < 2 ^ 64 /\ Z.of_nat (length L) < 2 ^ 63.

Lemma ka_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt x (2 ^ 63))) by lia. rewrite (proj2 (Z.ltb_lt y (2 ^ 63))) by lia. reflexivity.
Qed.

Lemma ka_lxor_ne : forall x y, 0 <= x -> 0 <= y -> y <> x -> (Z.lxor y x <? 1) = false.
Proof.
  intros x y Hx Hy Hne. apply Z.ltb_ge. assert (H0 : 0 <= Z.lxor y x) by (apply Z.lxor_nonneg; lia).
  assert (H1 : Z.lxor y x <> 0) by (rewrite Z.lxor_eq_0_iff; lia). lia.
Qed.

Lemma ka_lxor_eq : forall x, (Z.lxor x x <? 1) = true.
Proof. intros x. rewrite Z.lxor_nilpotent. reflexivity. Qed.

Ltac ka_eq := first [reflexivity | f_equal; lia | word_eq_tac].
Ltac ka_vac := unfold all_blank; intros ? ?; lia.

Section Strip.
Variables (Q : machine_state -> Prop)
  (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s10 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (L : list Z).
Hypothesis HKT : ka_text m p L.

(** The state of the strip code: a0, a1, a2, s4, s5, s6, s7, s8 vary; s9 = the mask, s11 = ' '. *)
Definition kst (pc : Z) (x10 x11 x12 x20 x21 x22 x23 x24 : word) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 a3 a4 a5 a6 a7 s2 s3 x20 x21 x22 x23 x24
          (Z_to_bv 64 4294976000) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

(** The key's forward loop 0x14224-0x14240 (s5 from s up to eq). *)
Lemma ka_kf : forall k o (w0 w1 w2 w4 w5 w6 w7 w8 : word) (a E : nat),
  (o + k = E)%nat -> (0 < k)%nat -> (E <= length L)%nat -> (a <= o)%nat -> all_blank L a o ->
  w0 = Z_to_bv 64 (p + Z.of_nat E) -> w1 = Z_to_bv 64 (p + Z.of_nat E) -> w5 = Z_to_bv 64 (p + Z.of_nat o) ->
  (forall o' (x2 x5 : word), ka_fwd L a E o' -> x5 = Z_to_bv 64 (p + Z.of_nat o') ->
     evt rsegs Q (kst 0x14244 w0 w1 x2 w4 x5 w6 w7 w8)) ->
  evt rsegs Q (kst 0x14224 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  induction k as [|k IH]; intros o w0 w1 w2 w4 w5 w6 w7 w8 a E Hk Hk0 HE Hao HB E0 E1 E5 K; [lia|].
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w0 w1 w5.
  pose proof (HRD o ltac:(lia)) as RD. pose proof (HBY o) as BY.
  unfold kst. step. rewrite (ka_zxb _ BY).
  step. if_cases B1; cbv iota.
  - zify_cond B1. eapply (K o); [|ka_eq]. split; [lia|]. split; [exact HB|]. right. apply ka_blank_gt. lia.
  - zify_cond B1. step. step. step. if_cases B2; cbv iota.
    + zify_cond B2. rewrite ka_bit in B2 by lia. destruct (blank (nth o L 0)) eqn:Hbx; [discriminate B2|].
      eapply (K o); [|ka_eq]. split; [lia|]. split; [exact HB|]. right. exact Hbx.
    + zify_cond B2. rewrite ka_bit in B2 by lia.
      destruct (blank (nth o L 0)) eqn:Hbx; [|exfalso; apply B2; reflexivity].
      assert (HB' : all_blank L a (S o)).
      { unfold all_blank in *. intros t Ht. destruct (Nat.eq_dec t o) as [->|Hto]; [exact Hbx|]. apply HB. lia. }
      step. step. if_cases B3; cbv iota.
      * zify_cond B3.
        eapply (IH (S o)) with (a := a) (E := E); [lia | lia | exact HE | lia | exact HB' | ka_eq | ka_eq | ka_eq |
                                                   exact K].
      * zify_cond B3. step.
        eapply (K E); [|ka_eq]. split; [lia|]. split; [|left; lia].
        replace E with (S o) by lia. exact HB'.
Qed.

(** The key's backward loop 0x1424c-0x14268 (a1 from eq down to s5). *)
Lemma ka_kb : forall k u (w0 w1 w2 w4 w5 w6 w7 w8 : word) (ks b : nat),
  (ks + k = u)%nat -> (0 < k)%nat -> (u <= b)%nat -> (b <= length L)%nat -> all_blank L u b ->
  w1 = Z_to_bv 64 (p + Z.of_nat u) -> w5 = Z_to_bv 64 (p + Z.of_nat ks) ->
  (forall u' (x1 x2 : word), ka_bwd L ks b u' -> x1 = Z_to_bv 64 (p + Z.of_nat u') ->
     evt rsegs Q (kst 0x1426c w0 x1 x2 w4 w5 w6 w7 w8)) ->
  evt rsegs Q (kst 0x1424c w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  induction k as [|k IH]; intros u w0 w1 w2 w4 w5 w6 w7 w8 ks b Hk Hk0 Hub HbL HB E1 E5 K; [lia|].
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w1 w5.
  pose proof (HRD (u - 1)%nat ltac:(lia)) as RD. pose proof (HBY (u - 1)%nat) as BY.
  unfold kst. step. rewrite (ka_zxb _ BY).
  step. if_cases B1; cbv iota.
  - zify_cond B1. eapply (K u); [|ka_eq]. split; [lia|]. split; [exact HB|]. right. apply ka_blank_gt. lia.
  - zify_cond B1. step. step. step. if_cases B2; cbv iota.
    + zify_cond B2. rewrite ka_bit in B2 by lia. destruct (blank (nth (u - 1) L 0)) eqn:Hbx; [discriminate B2|].
      eapply (K u); [|ka_eq]. split; [lia|]. split; [exact HB|]. right. exact Hbx.
    + zify_cond B2. rewrite ka_bit in B2 by lia.
      destruct (blank (nth (u - 1) L 0)) eqn:Hbx; [|exfalso; apply B2; reflexivity].
      assert (HB' : all_blank L (u - 1) b).
      { unfold all_blank in *. intros t Ht. destruct (Nat.eq_dec t (u - 1)%nat) as [->|Hto]; [exact Hbx|].
        apply HB. lia. }
      step. step. if_cases B3; cbv iota.
      * zify_cond B3.
        eapply (IH (u - 1)%nat) with (ks := ks) (b := b); [lia | lia | lia | exact HbL | exact HB' | ka_eq | ka_eq |
                                                          exact K].
      * zify_cond B3. step.
        eapply (K ks); [|ka_eq]. split; [lia|]. split; [|left; reflexivity].
        replace ks with (u - 1)%nat by lia. exact HB'.
Qed.

(** 0x14244-0x14248: a1 = eq, then the backward loop unless the key is empty. *)
Lemma ka_k2 : forall (I ks E : nat) (w0 w1 w2 w4 w5 w6 w7 w8 : word),
  ka_fwd L I E ks -> (E <= length L)%nat ->
  w0 = Z_to_bv 64 (p + Z.of_nat E) -> w5 = Z_to_bv 64 (p + Z.of_nat ks) ->
  (forall ke (x1 x2 : word), ka_bwd L ks E ke -> x1 = Z_to_bv 64 (p + Z.of_nat ke) ->
     evt rsegs Q (kst 0x1426c w0 x1 x2 w4 w5 w6 w7 w8)) ->
  evt rsegs Q (kst 0x14244 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  intros I ks E w0 w1 w2 w4 w5 w6 w7 w8 (Hks & _ & _) HE E0 E5 K.
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w0 w5. unfold kst. step. step. if_cases B1; cbv iota.
  - zify_cond B1. eapply (K ks); [|ka_eq]. split; [lia|]. split; [ka_vac | left; reflexivity].
  - zify_cond B1.
    eapply (ka_kb (E - ks) E) with (ks := ks) (b := E); [lia | lia | lia | exact HE | ka_vac | ka_eq | ka_eq | exact K].
Qed.

(** 0x14218: the key strip on [s, eq). *)
Lemma ka_key : forall (I E : nat) (w0 w1 w2 w4 w5 w6 w7 w8 : word),
  (I <= E <= length L)%nat ->
  w0 = Z_to_bv 64 (p + Z.of_nat E) -> w5 = Z_to_bv 64 (p + Z.of_nat I) ->
  (forall (ks ke : nat) (x1 x2 x5 : word), ka_fwd L I E ks -> ka_bwd L ks E ke ->
     x1 = Z_to_bv 64 (p + Z.of_nat ke) -> x5 = Z_to_bv 64 (p + Z.of_nat ks) ->
     evt rsegs Q (kst 0x1426c w0 x1 x2 w4 x5 w6 w7 w8)) ->
  evt rsegs Q (kst 0x14218 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  intros I E w0 w1 w2 w4 w5 w6 w7 w8 HIE E0 E5 K.
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w0 w5. unfold kst. step. if_cases B1; cbv iota.
  - zify_cond B1.
    assert (Hf : ka_fwd L I E I) by (split; [lia|]; split; [ka_vac | left; lia]).
    eapply (ka_k2 I I E); [exact Hf | lia | ka_eq | ka_eq |].
    intros ke x1 x2 Hb E1. eapply (K I ke); [exact Hf | exact Hb | exact E1 | ka_eq].
  - zify_cond B1. zstep. zstep.
    eapply (ka_kf (E - I) I) with (a := I) (E := E); [lia | lia | lia | lia | ka_vac | ka_eq | ka_eq | ka_eq |].
    intros o' x2 x5 Hf E5'.
    eapply (ka_k2 I o' E); [exact Hf | lia | ka_eq | exact E5' |].
    intros ke x1 x2' Hb E1. eapply (K o' ke); [exact Hf | exact Hb | exact E1 | exact E5'].
Qed.

(** The value's forward loop 0x14274-0x14290 (s4 from eq + 1 up to e). *)
Lemma ka_vf : forall k o (w0 w1 w2 w4 w5 w6 w7 w8 : word) (a J : nat),
  (o + k = J)%nat -> (0 < k)%nat -> (J <= length L)%nat -> (a <= o)%nat -> all_blank L a o ->
  w4 = Z_to_bv 64 (p + Z.of_nat o) -> w6 = Z_to_bv 64 (p + Z.of_nat J) ->
  (forall o' (x0 x4 : word), ka_fwd L a J o' -> x4 = Z_to_bv 64 (p + Z.of_nat o') ->
     evt rsegs Q (kst 0x14294 x0 w1 w2 x4 w5 w6 w7 w8)) ->
  evt rsegs Q (kst 0x14274 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  induction k as [|k IH]; intros o w0 w1 w2 w4 w5 w6 w7 w8 a J Hk Hk0 HJ Hao HB E4 E6 K; [lia|].
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w4 w6.
  pose proof (HRD o ltac:(lia)) as RD. pose proof (HBY o) as BY.
  unfold kst. step. rewrite (ka_zxb _ BY).
  step. if_cases B1; cbv iota.
  - zify_cond B1. eapply (K o); [|ka_eq]. split; [lia|]. split; [exact HB|]. right. apply ka_blank_gt. lia.
  - zify_cond B1. step. step. step. if_cases B2; cbv iota.
    + zify_cond B2. rewrite ka_bit in B2 by lia. destruct (blank (nth o L 0)) eqn:Hbx; [discriminate B2|].
      eapply (K o); [|ka_eq]. split; [lia|]. split; [exact HB|]. right. exact Hbx.
    + zify_cond B2. rewrite ka_bit in B2 by lia.
      destruct (blank (nth o L 0)) eqn:Hbx; [|exfalso; apply B2; reflexivity].
      assert (HB' : all_blank L a (S o)).
      { unfold all_blank in *. intros t Ht. destruct (Nat.eq_dec t o) as [->|Hto]; [exact Hbx|]. apply HB. lia. }
      step. step. if_cases B3; cbv iota.
      * zify_cond B3.
        eapply (IH (S o)) with (a := a) (J := J); [lia | lia | exact HJ | lia | exact HB' | ka_eq | ka_eq | exact K].
      * zify_cond B3. step.
        eapply (K J); [|ka_eq]. split; [lia|]. split; [|left; lia].
        replace J with (S o) by lia. exact HB'.
Qed.

(** The value's backward loop 0x14298-0x142b4 (s6 from e down to s4). *)
Lemma ka_vb : forall k u (w0 w1 w2 w4 w5 w6 w7 w8 : word) (vs b : nat),
  (vs + k = u)%nat -> (0 < k)%nat -> (u <= b)%nat -> (b <= length L)%nat -> all_blank L u b ->
  w4 = Z_to_bv 64 (p + Z.of_nat vs) -> w6 = Z_to_bv 64 (p + Z.of_nat u) ->
  (forall u' (x0 x6 : word), ka_bwd L vs b u' -> x6 = Z_to_bv 64 (p + Z.of_nat u') ->
     evt rsegs Q (kst 0x142b8 x0 w1 w2 w4 w5 x6 w7 w8)) ->
  evt rsegs Q (kst 0x14298 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  induction k as [|k IH]; intros u w0 w1 w2 w4 w5 w6 w7 w8 vs b Hk Hk0 Hub HbL HB E4 E6 K; [lia|].
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w4 w6.
  pose proof (HRD (u - 1)%nat ltac:(lia)) as RD. pose proof (HBY (u - 1)%nat) as BY.
  unfold kst. step. rewrite (ka_zxb _ BY).
  step. if_cases B1; cbv iota.
  - zify_cond B1. eapply (K u); [|ka_eq]. split; [lia|]. split; [exact HB|]. right. apply ka_blank_gt. lia.
  - zify_cond B1. step. step. step. if_cases B2; cbv iota.
    + zify_cond B2. rewrite ka_bit in B2 by lia. destruct (blank (nth (u - 1) L 0)) eqn:Hbx; [discriminate B2|].
      eapply (K u); [|ka_eq]. split; [lia|]. split; [exact HB|]. right. exact Hbx.
    + zify_cond B2. rewrite ka_bit in B2 by lia.
      destruct (blank (nth (u - 1) L 0)) eqn:Hbx; [|exfalso; apply B2; reflexivity].
      assert (HB' : all_blank L (u - 1) b).
      { unfold all_blank in *. intros t Ht. destruct (Nat.eq_dec t (u - 1)%nat) as [->|Hto]; [exact Hbx|].
        apply HB. lia. }
      step. step. if_cases B3; cbv iota.
      * zify_cond B3.
        eapply (IH (u - 1)%nat) with (vs := vs) (b := b); [lia | lia | lia | exact HbL | exact HB' | ka_eq | ka_eq |
                                                          exact K].
      * zify_cond B3. step.
        eapply (K vs); [|ka_eq]. split; [lia|]. split; [|left; reflexivity].
        replace vs with (u - 1)%nat by lia. exact HB'.
Qed.

(** 0x14294: the backward loop unless the value is empty. *)
Lemma ka_v2 : forall (vs J : nat) (w0 w1 w2 w4 w5 w6 w7 w8 : word),
  (vs <= J)%nat -> (J <= length L)%nat ->
  w4 = Z_to_bv 64 (p + Z.of_nat vs) -> w6 = Z_to_bv 64 (p + Z.of_nat J) ->
  (forall ve (x0 x6 : word), ka_bwd L vs J ve -> x6 = Z_to_bv 64 (p + Z.of_nat ve) ->
     evt rsegs Q (kst 0x142b8 x0 w1 w2 w4 w5 x6 w7 w8)) ->
  evt rsegs Q (kst 0x14294 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  intros vs J w0 w1 w2 w4 w5 w6 w7 w8 HvJ HJ E4 E6 K.
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w4 w6. unfold kst. step. if_cases B1; cbv iota.
  - zify_cond B1. eapply (K J); [|ka_eq]. split; [lia|]. split; [ka_vac | left; lia].
  - zify_cond B1.
    eapply (ka_vb (J - vs) J) with (vs := vs) (b := J); [lia | lia | lia | exact HJ | ka_vac | ka_eq | ka_eq | exact K].
Qed.

(** 0x1426c: the value strip on [eq + 1, e). *)
Lemma ka_val : forall (E J : nat) (w0 w1 w2 w4 w5 w6 w7 w8 : word),
  (E < J)%nat -> (J <= length L)%nat ->
  w0 = Z_to_bv 64 (p + Z.of_nat E) -> w6 = Z_to_bv 64 (p + Z.of_nat J) ->
  (forall (vs ve : nat) (x0 x4 x6 : word), ka_fwd L (S E) J vs -> ka_bwd L vs J ve ->
     x4 = Z_to_bv 64 (p + Z.of_nat vs) -> x6 = Z_to_bv 64 (p + Z.of_nat ve) ->
     evt rsegs Q (kst 0x142b8 x0 w1 w2 x4 w5 x6 w7 w8)) ->
  evt rsegs Q (kst 0x1426c w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  intros E J w0 w1 w2 w4 w5 w6 w7 w8 HEJ HJ E0 E6 K.
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w0 w6. unfold kst. zstep. step. if_cases B1; cbv iota.
  - zify_cond B1.
    assert (Hf : ka_fwd L (S E) J (S E)) by (split; [lia|]; split; [ka_vac | left; lia]).
    eapply (ka_v2 (S E) J); [lia | exact HJ | ka_eq | ka_eq |].
    intros ve x0 x6 Hb E6'. eapply (K (S E) ve); [exact Hf | exact Hb | ka_eq | exact E6'].
  - zify_cond B1.
    eapply (ka_vf (J - S E) (S E)) with (a := S E) (J := J); [lia | lia | exact HJ | lia | ka_vac | ka_eq | ka_eq |].
    intros o' x0 x4 Hf E4'. pose proof Hf as (Ho' & _).
    eapply (ka_v2 o' J); [lia | exact HJ | exact E4' | ka_eq |].
    intros ve x0' x6 Hb E6'. eapply (K o' ve); [exact Hf | exact Hb | exact E4' | exact E6'].
Qed.

(** 0x142d8-0x142f4, the first byte of the value a quote: one pair off when the last byte matches it. *)
Lemma ka_q2 : forall (vs ve ks ke : nat) (w0 w1 w2 w4 w5 w6 w7 w8 : word),
  (vs + 2 <= ve)%nat -> (ve <= length L)%nat -> (ks <= ke)%nat -> (ke <= length L)%nat ->
  (nth vs L 0 = DQ \/ nth vs L 0 = SQ) ->
  w0 = Z_to_bv 64 (nth vs L 0) -> w1 = Z_to_bv 64 (p + Z.of_nat ke) -> w4 = Z_to_bv 64 (p + Z.of_nat vs) ->
  w5 = Z_to_bv 64 (p + Z.of_nat ks) -> w6 = Z_to_bv 64 (p + Z.of_nat ve) ->
  (forall (ov vl : nat) (x0 x2 x4 x6 x7 x8 : word),
     (vs <= ov)%nat -> (ov + vl <= ve)%nat -> h_unquote (slice vs ve L) = slice ov (ov + vl) L ->
     x4 = Z_to_bv 64 (p + Z.of_nat ov) -> x6 = Z_to_bv 64 (p + Z.of_nat (ov + vl)) ->
     x7 = Z_to_bv 64 (Z.of_nat vl) -> x8 = Z_to_bv 64 (Z.of_nat (ke - ks)) ->
     evt rsegs Q (kst 0x142f8 x0 w1 x2 x4 w5 x6 x7 x8)) ->
  evt rsegs Q (kst 0x142d8 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  intros vs ve ks ke w0 w1 w2 w4 w5 w6 w7 w8 Hv HvL Hk HkL HQ E0 E1 E4 E5 E6 K.
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w0 w1 w4 w5 w6.
  assert (HU : h_unquote (slice vs ve L) =
               if nth (ve - 1) L 0 =? nth vs L 0 then slice (S vs) (ve - 1) L else slice vs ve L).
  { rewrite ka_unquote_slice by lia. rewrite (proj2 (Nat.leb_le 2 (ve - vs))) by lia.
    destruct HQ as [HQ|HQ]; rewrite HQ; reflexivity. }
  rewrite HU in K. clear HU.
  pose proof (HRD (ve - 1)%nat ltac:(lia)) as RD. pose proof (HBY (ve - 1)%nat) as BY. pose proof (HBY vs) as BYv.
  unfold kst. step. rewrite (ka_zxb _ BY). step. if_cases B1; cbv iota.
  - zify_cond B1. zstep. zstep.
    rewrite (ka_lxor_ne (nth vs L 0) (nth (ve - 1) L 0)) by lia. cbn [Z.b2z].
    zstep. zstep. zstep.
    eapply (K vs (ve - vs)%nat); [lia | lia | | ka_eq | ka_eq | ka_eq | ka_eq].
    rewrite (proj2 (Z.eqb_neq _ _) B1). replace (vs + (ve - vs))%nat with ve by lia. reflexivity.
  - zify_cond B1. zstep. zstep. zstep. rewrite B1, ka_lxor_eq. cbn [Z.b2z].
    zstep. zstep. zstep.
    eapply (K (S vs) (ve - vs - 2)%nat); [lia | lia | | ka_eq | ka_eq | ka_eq | ka_eq].
    rewrite B1, Z.eqb_refl. f_equal. lia.
Qed.

(** 0x142b8-0x142f4: the quotes, then s8 = the key's length and s7 = the value's. *)
Lemma ka_q : forall (vs ve ks ke : nat) (w0 w1 w2 w4 w5 w6 w7 w8 : word),
  (vs <= ve <= length L)%nat -> (ks <= ke)%nat -> (ke <= length L)%nat ->
  w1 = Z_to_bv 64 (p + Z.of_nat ke) -> w4 = Z_to_bv 64 (p + Z.of_nat vs) ->
  w5 = Z_to_bv 64 (p + Z.of_nat ks) -> w6 = Z_to_bv 64 (p + Z.of_nat ve) ->
  (forall (ov vl : nat) (x0 x2 x4 x6 x7 x8 : word),
     (vs <= ov)%nat -> (ov + vl <= ve)%nat -> h_unquote (slice vs ve L) = slice ov (ov + vl) L ->
     x4 = Z_to_bv 64 (p + Z.of_nat ov) -> x6 = Z_to_bv 64 (p + Z.of_nat (ov + vl)) ->
     x7 = Z_to_bv 64 (Z.of_nat vl) -> x8 = Z_to_bv 64 (Z.of_nat (ke - ks)) ->
     evt rsegs Q (kst 0x142f8 x0 w1 x2 x4 w5 x6 x7 x8)) ->
  evt rsegs Q (kst 0x142b8 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  intros vs ve ks ke w0 w1 w2 w4 w5 w6 w7 w8 Hv Hk HkL E1 E4 E5 E6 K.
  pose proof HKT as (HRD & HBY & Hp & HpL & HL63).
  subst w1 w4 w5 w6.
  unfold kst. zstep. zstep. step. rewrite ka_lts by lia. if_cases B1; cbv iota.
  - apply Z.ltb_lt in B1. zstep. zstep.
    eapply (K vs (ve - vs)%nat); [lia | lia | | ka_eq | ka_eq | ka_eq | ka_eq].
    rewrite ka_unquote_slice by lia. replace (vs + (ve - vs))%nat with ve by lia.
    destruct (Nat.leb_spec 2 (ve - vs)); [lia|]. reflexivity.
  - apply Z.ltb_ge in B1.
    pose proof (HRD vs ltac:(lia)) as RD. pose proof (HBY vs) as BY.
    step. rewrite (ka_zxb _ BY). step. step. if_cases B2; cbv iota.
    + zify_cond B2.
      eapply (ka_q2 vs ve ks ke); [lia | lia | lia | lia | right; exact B2 | ka_eq | ka_eq | ka_eq | ka_eq | ka_eq |
                                   exact K].
    + zify_cond B2. step. step. if_cases B3; cbv iota.
      * zify_cond B3. zstep. zstep.
        eapply (K vs (ve - vs)%nat); [lia | lia | | ka_eq | ka_eq | ka_eq | ka_eq].
        rewrite ka_unquote_slice by lia. replace (vs + (ve - vs))%nat with ve by lia.
        rewrite (proj2 (Nat.leb_le 2 (ve - vs))) by lia.
        rewrite (proj2 (Z.eqb_neq (nth vs L 0) 34)) by exact B3.
        rewrite (proj2 (Z.eqb_neq (nth vs L 0) 39)) by exact B2. reflexivity.
      * zify_cond B3.
        eapply (ka_q2 vs ve ks ke); [lia | lia | lia | lia | left; exact B3 | ka_eq | ka_eq | ka_eq | ka_eq | ka_eq |
                                     exact K].
Qed.

(** 0x14218 to the cut KDISP 0x142f8: the key k = [ok, ok + kl) = strip [s, eq), the value v = [ov, ov + vl) =
    unquote (strip [eq + 1, e)), in the line's offsets. *)
Lemma ka_strip : forall (I E J : nat) (w0 w1 w2 w4 w5 w6 w7 w8 : word),
  (I <= E)%nat -> (E < J)%nat -> (J <= length L)%nat ->
  w0 = Z_to_bv 64 (p + Z.of_nat E) -> w5 = Z_to_bv 64 (p + Z.of_nat I) -> w6 = Z_to_bv 64 (p + Z.of_nat J) ->
  (forall (ok kl ov vl : nat) (x0 x1 x2 x4 x5 x6 x7 x8 : word),
     (ok + kl <= E)%nat -> (S E <= ov)%nat -> (ov + vl <= J)%nat ->
     h_strip (slice I E L) = slice ok (ok + kl) L ->
     h_unquote (h_strip (slice (S E) J L)) = slice ov (ov + vl) L ->
     x4 = Z_to_bv 64 (p + Z.of_nat ov) -> x5 = Z_to_bv 64 (p + Z.of_nat ok) ->
     x6 = Z_to_bv 64 (p + Z.of_nat (ov + vl)) -> x7 = Z_to_bv 64 (Z.of_nat vl) -> x8 = Z_to_bv 64 (Z.of_nat kl) ->
     evt rsegs Q (kst 0x142f8 x0 x1 x2 x4 x5 x6 x7 x8)) ->
  evt rsegs Q (kst 0x14218 w0 w1 w2 w4 w5 w6 w7 w8).
Proof.
  intros I E J w0 w1 w2 w4 w5 w6 w7 w8 HIE HEJ HJ E0 E5 E6 K.
  eapply (ka_key I E); [lia | exact E0 | exact E5 |].
  intros ks ke x1 x2 x5 Hf Hb E1 E5'.
  eapply (ka_val E J); [exact HEJ | exact HJ | exact E0 | exact E6 |].
  intros vs ve x0 x4 x6 Hvf Hvb E4 E6'.
  pose proof Hf as (Hks & _). pose proof Hb as (Hke & _). pose proof Hvf as (Hvs & _). pose proof Hvb as (Hve & _).
  eapply (ka_q vs ve ks ke); [lia | lia | lia | exact E1 | exact E4 | exact E5' | exact E6' |].
  intros ov vl y0 y2 y4 y6 y7 y8 Hov Hovl HU E4' E6'' E7 E8.
  eapply (K ks (ke - ks)%nat ov vl); [lia | lia | lia | | | exact E4' | exact E5' | exact E6'' | exact E7 | exact E8].
  - replace (ks + (ke - ks))%nat with ke by lia. apply (ka_strip_slice L I E ks ke); [lia | exact Hf | exact Hb].
  - rewrite (ka_strip_slice L (S E) J vs ve); [exact HU | exact HJ | exact Hvf | exact Hvb].
Qed.

End Strip.

(** ** The piece *)
Lemma mf_keya_holds : memchr_contract -> m_refuse_contract -> S_MF_KEYA.
Proof.
  intros HMC HMR n HT HKD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest i j Hn Hne HL HR Hlong Hij HjL Hsl Hlbr
    E5 E6 E2.
  rewrite <- Hsl.
  pose proof HL as HL0. apply mf_loop_iff in HL0 as (HC & HX & HS).
  destruct HS as (HMC0 & HCE0 & HCO0 & HK00 & Hl0 & Hl1 & Hr0 & Ho0).
  pose proof HC as HCb. apply mf_ctx_bounds in HCb.
  destruct HCb as (_ & _ & _ & _ & _ & _ & Hc0 & Hc64). unfold SEG_M_SIZE in Hc64.
  pose proof HX as HXp. apply mf_text_props in HXp. destruct HXp as (Hnul & Hbyt & Hp0 & Hspan & Hspan8).
  pose proof HC as HC'. unfold mf_ctx in HC'.
  destruct HC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  pose proof (ka_line_len rest) as HLr.
  assert (Hcs : Z.of_nat (length rest) + 1 <= cstr_span p rest).
  { unfold cstr_span. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length rest) + 1)) 8 ltac:(lia)). lia. }
  assert (HpL : p + Z.of_nat (length (mf_line rest)) < 2 ^ 64) by lia.
  destruct HR as (E0 & E1 & E2' & E3 & E7 & E8 & E9 & E10 & E11).
  subst s0 s1 s2 s3 s7 s8 s9 s10 s11 s5 s6 a2.
  unfold BLANK_MASK, MF_PC_KEY.
  assert (Es : slice i j (mf_line rest) = firstn (j - i) (skipn i rest)).
  { rewrite mf_line_firstn by lia. f_equal. lia. }
  assert (Hsb : Forall (fun x => 0 <= x < 256) (slice i j (mf_line rest))).
  { rewrite Es. apply ka_Forall_fs. exact Hbyt. }
  assert (Hbuf : bytes_at rsegs m (p + Z.of_nat i) (zb (slice i j (mf_line rest)))).
  { rewrite Es. apply (mf_text_bytes m (bv_unsigned sp0) lo c p rest i (j - i) HX). lia. }
  assert (Hsl_len : length (slice i j (mf_line rest)) = (j - i)%nat) by (apply slice_length; lia).
  (* 0x14200-0x14208: memchr(s, '=', e - s) *)
  step. step. step.
  eapply evt_cut.
  { eapply HMC with (buf := zb (slice i j (mf_line rest))).
    - rewrite unsigned_lit by lia. rewrite ?Z.add_0_r. exact Hbuf.
    - apply ka_memchr_ok. rewrite unsigned_lit by lia. unfold zb. rewrite length_map, Hsl_len. lia.
    - exact MI. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> &
              MU1 & WM1 & MI1 & _).
  rewrite (ka_memchr_res _ _ _ (slice i j (mf_line rest)));
    [| vm_compute; reflexivity | rewrite unsigned_lit by lia; rewrite Hsl_len; reflexivity | exact Hsb].
  rewrite ret_pc_even by (try lia; reflexivity).
  (* the loop facts on memchr's memory *)
  assert (HL1 := HL). apply (ka_loop_nil m m1 MU1 WM1 MI1) in HL1.
  pose proof HL1 as HL1'. apply mf_loop_iff in HL1' as (HC1 & HX1 & HS1).
  destruct HS1 as (HMC1 & HCE1 & HCO1 & _).
  assert (HKT1 : ka_text m1 p (mf_line rest)).
  { split; [|split; [|split; [exact Hp0 | split; [exact HpL | lia]]]].
    - intros o Ho. rewrite <- (mf_line_nth rest o Ho).
      apply (mf_text_byte m1 (bv_unsigned sp0) lo c p rest o HX1). lia.
    - intros o. destruct (Nat.lt_ge_cases o (length (mf_line rest))) as [Ho|Ho].
      + rewrite <- (mf_line_nth rest o Ho). rewrite Forall_forall in Hbyt. apply Hbyt. apply nth_In. lia.
      + rewrite nth_overflow by exact Ho. lia. }
  pose proof (ka_cell8_rd _ _ _ HCE1) as RDc.
  (* 0x1420c: the cur cell *)
  step.
  destruct cur as [gi|]; cbn [cur_ptr cur_ok] in *.
  - (* cur = Some gi: a1 <> 0 *)
    pose proof (ka_seg32 _ _ _ HMC1) as H32. unfold mseg_addr, MSEG_SIZE in *.
    step. if_cases B1; cbv iota; [exfalso; zify_cond B1; lia|].
    destruct (SegModel.memchr (slice i j (mf_line rest)) 61) as [ei|] eqn:HM.
    + (* '=' at s + ei: the strips, then KDISP *)
      pose proof (memchr_some _ _ _ HM) as (Hei & _ & _). rewrite Hsl_len in Hei.
      step. if_cases B2; cbv iota; [exfalso; zify_cond B2; lia|].
      rewrite (m_key_disp mc gi (slice i j (mf_line rest)) (line + 1) ei HM).
      eapply mf_post_back with (F1 := F) (m1 := m1) (W1 := []);
        [intros; reflexivity | exact MU1 | exact WM1 | apply sub_fp_nil |].
      eapply ka_strip with (p := p) (L := mf_line rest) (I := i) (E := (i + ei)%nat) (J := j);
        [exact HKT1 | lia | lia | exact HjL | ka_eq | ka_eq | ka_eq |].
      intros ok kl ov vl x0 x1 x2 x4 x5 x6 x7 x8 Hokl Hov Hovl Hk Hv E4' E5' E6' E7' E8'.
      unfold kst. unfold H_MF_KDISP, H_MF_KAT in HKD.
      eapply HKD with (ok := ok) (kl := kl) (ov := ov) (vl := vl);
        [exact Hn | exact Hne | exact HL1 | | | constructor].
      * unfold mk_regs. repeat split; assumption.
      * unfold mk_kv. split; [lia|]. split; [lia|]. split.
        -- rewrite mf_line_firstn by lia. rewrite (ka_firstn_slice (mf_line rest) i j ei) by lia.
           rewrite Hk. reflexivity.
        -- rewrite mf_line_firstn by lia. rewrite (ka_skipn_slice (mf_line rest) i j (S ei)) by lia.
           replace (i + S ei)%nat with (S (i + ei)) by lia. rewrite Hv. reflexivity.
    + (* no '=': the refusal *)
      step. if_cases B2; cbv iota; [|exfalso; vm_compute in B2; discriminate B2].
      rewrite (m_key_refuse mc (Some gi) (slice i j (mf_line rest)) (line + 1) (or_introl HM)).
      eapply mf_post_back with (F1 := F) (m1 := m1) (W1 := []);
        [intros; reflexivity | exact MU1 | exact WM1 | apply sub_fp_nil |].
      eapply (ka_refuse HMR n HT); [exact Hn | exact Hne | exact HL1 | unfold m_file_regs; repeat split].
  - (* cur = NULL: the refusal *)
    step. if_cases B1; cbv iota; [|exfalso; vm_compute in B1; discriminate B1].
    rewrite (m_key_refuse mc None (slice i j (mf_line rest)) (line + 1) (or_intror eq_refl)).
    eapply mf_post_back with (F1 := F) (m1 := m1) (W1 := []);
      [intros; reflexivity | exact MU1 | exact WM1 | apply sub_fp_nil |].
    eapply (ka_refuse HMR n HT); [exact Hn | exact Hne | exact HL1 | unfold m_file_regs; repeat split].
Qed.
