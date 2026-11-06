(** The copy tail ent_build's kinds 6 and 7 share in the UBSan image (pod.h:346-347, 355-356, fuzz.h:59-65): the
    size word stored (kind 7, 0x13d9c), n = min(size, bytes left) (0x13da0 / 0x13da4), the pointer check
    `not a1,s7` (0x13da8), s9 = cursor + n, s10 = left - n, memcpy(sp + 0xf0, cursor, n) (0x13dc0), t1 = s10, to the
    join 0x13ee4. The form is reac-pw/fuzz_role's U/Prog/RoleBuild/Ent6.v tail67 at rate's registers. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac Image ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** A pointer-overflow check `bltu (not p), n` with p + n below 2^64: not taken (the `not` of a register leaves
    an lxor with the ones). *)
Lemma t67_not_lt_false : forall x y, 0 <= x -> 0 <= y -> x + y < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite !unsigned_lit_wrap.
  rewrite (Z.mod_small x) by lia. rewrite zb_lxor_ones by lia.
  rewrite (Z.mod_small (18446744073709551615 - x)) by lia. rewrite (Z.mod_small y) by lia.
  apply Z.ltb_ge. lia.
Qed.

(** A zero-extended byte's value. *)
Lemma t67_zxb_un : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

(** The body of a pod whose size is sz and whose copied prefix is p, inside the 96-byte array. *)
Lemma t67_body_pad : forall (p : list byte) (sz : Z), (length p <= Z.to_nat sz)%nat -> (Z.to_nat sz <= 96)%nat ->
  p ++ zeros (96 - length p) =
  (p ++ zeros (Z.to_nat sz - length p)) ++ zeros (96 - length (p ++ zeros (Z.to_nat sz - length p))).
Proof.
  intros p sz H1 H2. rewrite length_app, length_zeros, <- app_assoc. f_equal.
  rewrite <- zeros_app. f_equal. lia.
Qed.

Section Tail67.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.

Local Abbreviation QE := (QJ sp gp tp s3 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x188)).
Local Abbreviation S1 := (Z_to_bv 64 4).
Local Abbreviation S2 := (Z_to_bv 64 95).
Local Abbreviation S4 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S5 := (Z_to_bv 64 10).
Local Abbreviation S6 := (Z_to_bv 64 0x4000).

(** A slice of the input in any memory the turn reaches. *)
Lemma t67_in_slice : forall mm t' sz' bd' (j n : nat), MemC sp m lo mm t' sz' bd' -> (j <= length r)%nat ->
  bytes_at rsegs mm (src + Z.of_nat j) (firstn n (skipn j r)).
Proof.
  intros mm t' sz' bd' j n MC Hj.
  pose proof (MemC_in sp m r src pp lo HE _ _ _ _ MC) as HI.
  rewrite <- (firstn_skipn j r) in HI. apply bytes_at_app in HI as [_ HS].
  rewrite length_firstn in HS. replace (Nat.min j (length r)) with j in HS by lia.
  rewrite <- (firstn_skipn n (skipn j r)) in HS. apply bytes_at_app in HS as [HP _]. exact HP.
Qed.

(** 0x13da8 -> the join: n = c = min(sz, left) in a2, the check, the copy of the next sz bytes of the input (from
    offset j) into the body, t1 = left - c, s9 = cursor + c. *)
Lemma tail_13da8 : forall (ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t szw : word) m1
    (j : nat) (cur left sz c : Z) (p r' : list byte) (e : ent),
  ent_build r = (e, r') -> e_size e = sz -> e_body e = p ++ zeros (Z.to_nat sz - length p) ->
  0 <= sz <= 96 -> (j <= length r)%nat -> cur = src + Z.of_nat j -> left = Z.of_nat (length r - j) ->
  p = firstn (Z.to_nat sz) (skipn j r) -> r' = skipn (Z.to_nat sz) (skipn j r) -> c = Z.min sz left ->
  MemC sp m lo m1 t szw (zeros 96) -> le4 t = le32 (e_type e) -> le4 szw = le32 sz ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (Z_to_bv 64 left) a1 (Z_to_bv 64 c) a3 a4 a5 a6 a7
             S2 s3 S4 S5 S6 (Z_to_bv 64 cur) (Z_to_bv 64 pp) s9 s10 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13da8) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t szw m1 j cur left sz c p r' e EB Esz Ebd Hsz Hj
    Ecur Eleft Ep Er' Ec MC Et Eszw.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (Lp : length p = Nat.min (Z.to_nat sz) (length r - j)%nat)
    by (rewrite Ep, length_firstn, length_skipn; reflexivity).
  assert (Lr' : length r' = (length r - j - length p)%nat)
    by (rewrite Er', length_skipn, length_skipn; lia).
  assert (Ec' : c = Z.of_nat (length p)) by lia.
  clear Ec.
  subst c.
  assert (Hcl : cur + Z.of_nat (length p) <= lo) by lia.
  (* 0x13da8 not a1,s7; 0x13dac bltu a1,a2 (trap, not taken) *)
  step. step. first [ rewrite t67_not_lt_false by lia; cbv iota | brf ].
  (* 0x13db0 add s9,s7,a2; sub s10,a0,a2; addi a0,sp,0xf0; mv a1,s7; jal memcpy *)
  do 5 step.
  pose proof (t67_in_slice m1 _ _ _ j (Z.to_nat sz) MC Hj) as HB.
  destruct (MemC_cells sp m r src pp lo HE _ _ _ _ (bv_unsigned sp + 240) (length p) MC
              ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as (junk & Lj & CJ).
  rewrite <- Ecur, <- Ep in HB.
  eapply evt_cut.
  { eapply MCPY;
      [ rewrite unsigned_lit by lia; exact HB
      | rewrite unsigned_lit by lia; lia
      | rewrite !unsigned_lit by lia; rewrite Nat2Z.id; exact CJ
      | rewrite !unsigned_lit by lia; lia
      | exact (MemC_mem_inv _ _ _ _ _ _ _ MC) ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E &
              MU2 & WM2 & MI2 & CE2 & SB2).
  subst ms'. rewrite ret_pc_even by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU2, CE2 by lia. rewrite Nat2Z.id in CE2.
  assert (MC2 : MemC sp m lo m2 t szw (upd_bytes (zeros 96) 0 p)).
  { eapply (MemC_call_bd sp m r src pp lo HE m1 m2 t szw (zeros 96) (bv_unsigned sp + 240) 0%nat p MC);
      [ exact MU2 | exact WM2 | exact MI2 | exact (proj1 (rw_CB_bytes m2 _ _ _ CE2))
      | cbn [Z.of_nat]; lia | cbn [length]; lia ]. }
  clear MC MU2 WM2 MI2 CE2 SB2 HB CJ Lj junk.
  rewrite (upd_zeros0 p 96) in MC2 by lia.
  (* 0x13dc4 mv t1,s10; 0x13dc8 j 0x13ee4 *)
  step. step.
  eapply join_13ee4; [exact EB | | | exact MC2 | exact Et | rewrite Esz; exact Eszw | ].
  - f_equal. rewrite ?unsigned_lit by lia. lia.
  - f_equal. rewrite ?unsigned_lit by lia. lia.
  - rewrite Ebd. apply t67_body_pad; lia.
Qed.

(** 0x13da4 (left <= sz): n = left (`mv a2,a0`), then [tail_13da8]. *)
Lemma tail_13da4 : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t szw : word) m1
    (j : nat) (cur left sz : Z) (p r' : list byte) (e : ent),
  ent_build r = (e, r') -> e_size e = sz -> e_body e = p ++ zeros (Z.to_nat sz - length p) ->
  0 <= sz <= 96 -> (j <= length r)%nat -> cur = src + Z.of_nat j -> left = Z.of_nat (length r - j) ->
  p = firstn (Z.to_nat sz) (skipn j r) -> r' = skipn (Z.to_nat sz) (skipn j r) -> left <= sz ->
  MemC sp m lo m1 t szw (zeros 96) -> le4 t = le32 (e_type e) -> le4 szw = le32 sz ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (Z_to_bv 64 left) a1 a2 a3 a4 a5 a6 a7
             S2 s3 S4 S5 S6 (Z_to_bv 64 cur) (Z_to_bv 64 pp) s9 s10 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13da4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t szw m1 j cur left sz p r' e EB Esz Ebd Hsz Hj
    Ecur Eleft Ep Er' Hle MC Et Eszw.
  (* 0x13da4 mv a2,a0 *)
  step.
  eapply (tail_13da8 ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t szw m1 j cur left sz left p r' e);
    first [ eassumption | lia ].
Qed.

(** 0x13d9c (kind 7): the size word stored, then n = min(sz, left) by `bltu a2,a0` (0x13da0) and the tail. *)
Lemma tail_13d9c : forall (ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t : word) m1
    (j : nat) (cur left sz : Z) (p r' : list byte) (e : ent),
  ent_build r = (e, r') -> e_size e = sz -> e_body e = p ++ zeros (Z.to_nat sz - length p) ->
  0 <= sz <= 96 -> (j <= length r)%nat -> cur = src + Z.of_nat j -> left = Z.of_nat (length r - j) ->
  p = firstn (Z.to_nat sz) (skipn j r) -> r' = skipn (Z.to_nat sz) (skipn j r) ->
  MemC sp m lo m1 t (Z_to_bv 64 0) (zeros 96) -> le4 t = le32 (e_type e) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (Z_to_bv 64 left) a1 (Z_to_bv 64 sz) a3 a4 a5 a6 a7
             S2 s3 S4 S5 S6 (Z_to_bv 64 cur) (Z_to_bv 64 pp) s9 s10 (Z_to_bv 64 (pp + POD_LEN_OFF)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13d9c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t m1 j cur left sz p r' e EB Esz Ebd Hsz Hj
    Ecur Eleft Ep Er' MC Et.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13d9c sw a2,0xec(sp) *)
  est_sz HE MC.
  (* 0x13da0 bltu a2,a0: sz < left keeps n = sz (to 0x13da8), else 0x13da4 *)
  step.
  destruct (Z_lt_ge_dec sz left) as [X|X].
  - brt.
    eapply (tail_13da8 ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t (Z_to_bv 64 sz) _ j cur left sz sz
              p r' e);
      first [ eassumption | lia | apply le4_le32 ].
  - brf.
    eapply (tail_13da4 ra t0 t1 t2 a1 (Z_to_bv 64 sz) a3 a4 a5 a6 a7 s9 s10 t3 t4 t5 t6 t (Z_to_bv 64 sz) _ j
              cur left sz p r' e);
      first [ eassumption | lia | apply le4_le32 ].
Qed.

End Tail67.
