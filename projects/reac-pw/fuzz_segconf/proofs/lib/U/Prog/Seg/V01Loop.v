(** Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c / pinned 1696d6c34ffd):
    the OUTER LOOP of the inlined m_declared, the stretch HEAD 0x13f98 .. 0x13fb4 and JOIN 0x13fb8 .. 0x13fcc
    (UBSan binary), proof of [V01D.V01_HEAD] from the split stretch, the
    acceptance stretch and the tail ([v01_loop]).

    Code:
      HEAD 0x13f98  addi a0,zero,0x20; beq s9,a0 -> trap 0x14264 (dead: i < m->n <= 32)
           0x13fa0  slli s7,s9,8; bltu s2,s7 -> trap (dead: s2 = ~m and m + 9236 <= lo < 2^47)
           0x13fa8  ld s3,0x50(sp) (= m); add s7,s3,s7 (= m + 256 i); lw a0,0x18(s7) (= seg[i].ignore)
           0x13fb4  beqz a0 -> 0x13fd0 (the split stretch), else the join
      JOIN 0x13fb8  lw a0,0(s11) (= m->n); s9 += 1; s6 -= 256; s1 += 256; blt s9,a0 -> 0x13f98; j 0x141ac (tail)
    By induction on the turns left: at the join after turn i, i + 1 < m->n goes to the head of turn i + 1 and
    i + 1 >= m->n goes to the tail, where skipn (i + 1) segs = [] turns [V01_inv] into m_declared's answer. At the
    head of turn i an ignored segment goes to the join directly (m_decl_go skips it) and the others to the split.
    Part of the proof of LLVMFuzzerTestOneInput (its V01 loop stretch, UBSan); no released proof of fuzz_segconf's
    LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import V01D.
Import ListNotations.
Open Scope Z_scope.

(** ** Build-independent facts (SegModel, lists, Z) *)
Module V01LoopPure.

Lemma skipn_nth_cons : forall {A} (l : list A) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
  intros A l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma skipn_ge_nil : forall {A} (l : list A) i, (length l <= i)%nat -> skipn i l = [].
Proof.
  intros A l. induction l as [|x l IH]; intros [|i] H; cbn [length] in H; try lia; try reflexivity.
  cbn [skipn]. apply IH. lia.
Qed.

(** m_decl_go skips an ignored segment. *)
Lemma decl_skip : forall segs i tb cap a, (i < length segs)%nat -> ms_ignore (nth i segs mseg_d) = true ->
  m_decl_go (skipn i segs) tb cap a = m_decl_go (skipn (S i) segs) tb cap a.
Proof.
  intros segs i tb cap a Hi Hg. rewrite (skipn_nth_cons segs i mseg_d Hi). cbn [m_decl_go]. rewrite Hg.
  reflexivity.
Qed.

(** After the last segment m_decl_go returns the count and the table it has. *)
Lemma decl_end : forall segs i tb cap a, (length segs <= i)%nat -> m_decl_go (skipn i segs) tb cap a = (a, tb).
Proof. intros segs i tb cap a H. rewrite (skipn_ge_nil segs i H). reflexivity. Qed.

(** Bytes [a, a + n) of the field [b, b + k) of l. *)
Lemma fld_fld : forall a n b k (l : list byte), (a + n <= k)%nat ->
  firstn n (skipn a (firstn k (skipn b l))) = firstn n (skipn (b + a) l).
Proof.
  intros a n b k l H. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (k - a)) with n by lia. rewrite (Nat.add_comm a b). reflexivity.
Qed.

Lemma shl8 : forall x, Z.shiftl x 8 = 256 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia. Qed.

End V01LoopPure.
Import V01LoopPure.

(** ** Words *)
Lemma sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). reflexivity.
Qed.

Lemma sgn_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed. rewrite unsigned_lit by lia.
  destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

(** A register equation at a cut. *)
Ltac weq := first [ reflexivity | f_equal; lia
                  | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

(** A trap branch the bounds refute. *)
Ltac dead K := exfalso; zify_cond K; rewrite ?shl8 in K; rewrite ?Z.mod_small in K by lia; lia.

(** ** The reads of the stretch *)
(** m->n, the u32 at m + 0x2000. *)
Lemma rd_n : forall X m bs, bytes_at rsegs m (v_mm X) bs -> mconf_enc (v_mc X) bs ->
  ov_read_bytes rsegs m (wa (v_mm X + MC_N)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (v_segs X))))).
Proof.
  intros X m bs B (L & _ & _ & (_ & E) & _). unfold SEG_M_SIZE in L.
  pose proof (bytes_at_ov_read rsegs m (v_mm X) bs (Z.to_nat MC_N) 4 B ltac:(unfold MC_N; lia)) as R.
  rewrite Z2Nat.id in R by (unfold MC_N; lia). rewrite R. f_equal. exact E.
Qed.

(** seg[i].ignore, the flag at m + 256 i + 0x18. *)
Lemma rd_ign : forall X m bs i b, bytes_at rsegs m (v_mm X) bs -> mconf_enc (v_mc X) bs ->
  (i < length (v_segs X))%nat -> ms_ignore (nth i (v_segs X) mseg_d) = b ->
  ov_read_bytes rsegs m (wa (v_mm X + 256 * Z.of_nat i + 24)) 4 = Some (le4 (Z_to_bv 64 (if b then 1 else 0))).
Proof.
  intros X m bs i b B (L & N32 & SG & _) Hi Hb. unfold v_segs in Hi, Hb. unfold SEG_M_SIZE in L.
  destruct (SG i Hi) as (L256 & _ & _ & _ & FI & _).
  rewrite Hb in FI. unfold flag_enc in FI.
  pose proof (bytes_at_ov_read rsegs m (v_mm X) bs (256 * i + 24) 4 B ltac:(lia)) as R.
  replace (v_mm X + 256 * Z.of_nat i + 24) with (v_mm X + Z.of_nat (256 * i + 24)) by lia.
  rewrite R. f_equal. rewrite <- FI. unfold fldz, fld.
  change (Z.to_nat MS_IGNORE) with 24%nat. change (Z.to_nat 4) with 4%nat.
  rewrite fld_fld by lia. reflexivity.
Qed.

(** ** The walk *)
Section Loop.
Variable X : vctx.
Hypothesis HG : V01_geo X.
Hypothesis HSP : V01_SPLIT X.
Hypothesis HAC : V01_ACC X.
Hypothesis HTL : V01_TAIL X.

Lemma nums : 0x60000 < v_S X - 65536 /\ v_S X <= 2 ^ 47 /\ 4096 <= v_mm X /\ v_mm X + 9236 <= v_S X - 65536.
Proof.
  pose proof HG as (_ & Hlo & HS & _ & _ & _ & _ & _ & Hm1 & _ & Hm2 & _).
  unfold v_lo, SEG_M_SIZE in *. lia.
Qed.

Lemma mc_of : forall a tb m, V01_lmem X a tb m -> exists bs, bytes_at rsegs m (v_mm X) bs /\ mconf_enc (v_mc X) bs.
Proof. intros a tb m ((_ & _ & _ & _ & _ & _ & _ & _ & MC) & _). exact MC. Qed.

Lemma len32 : forall a tb m, V01_lmem X a tb m -> (length (v_segs X) <= 32)%nat.
Proof. intros a tb m HM. destruct (mc_of a tb m HM) as (bs & _ & (_ & N & _)). exact N. Qed.

Lemma cells_of : forall a tb m, V01_lmem X a tb m ->
  rw_cells rsegs m (v_sp X)
    [C8 (Z_to_bv 64 (v_tab X)); C8 (Z_to_bv 64 (18446744073709551615 - v_buf X)); C8 (Z_to_bv 64 (v_cap X));
     C8 (Z_to_bv 64 (v_mt X)); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (Z.of_nat (length tb)));
     C8 (Z_to_bv 64 MASK_PARENT); C8 (Z_to_bv 64 (18446744073709551615 - v_mt X)); C8 (Z_to_bv 64 1);
     C8 (Z_to_bv 64 (v_c X)); C8 (Z_to_bv 64 (v_mm X))].
Proof. intros a tb m (_ & FC & _). exact FC. Qed.

(** An ignored segment: the invariant moves to the next turn unchanged. *)
Lemma inv_skip : forall i tb a, V01_inv X i tb a -> (i < length (v_segs X))%nat ->
  ms_ignore (nth i (v_segs X) mseg_d) = true -> V01_inv X (S i) tb a.
Proof.
  intros i tb a (H1 & H2 & H3) Hi IG. split; [lia|]. split; [lia|].
  rewrite <- H3. symmetry. apply decl_skip; assumption.
Qed.

(** The cut states with the registers the steps compute as equations. *)
Lemma head_eq : forall i, V01_HEADat X i ->
  forall tb a m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 w9 w19 w22 w25 : word),
  w9 = Z_to_bv 64 (v_mm X + 256 * Z.of_nat i) -> w19 = Z_to_bv 64 (v_mm X) ->
  w22 = Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i)) -> w25 = Z_to_bv 64 (Z.of_nat i) ->
  V01_lmem X a tb m -> V01_inv X i tb a -> (i < length (v_segs X))%nat ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8 w9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (18446744073709551615 - v_mm X)) w19 (Z_to_bv 64 18446744073709551615)
             x21 w22 x23 x24 w25 (Z_to_bv 64 4094) (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 V01_PC_HEAD) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros i H tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 w9 w19 w22 w25
    E9 E19 E22 E25. subst w9 w19 w22 w25.
  exact (H tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31).
Qed.

Lemma join_eq : forall i, V01_JOINat X i ->
  forall tb a m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 w19 : word),
  w19 = Z_to_bv 64 (v_mm X) ->
  V01_lmem X a tb m -> V01_inv X (S i) tb a -> (S i <= length (v_segs X))%nat ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8
             (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (18446744073709551615 - v_mm X)) w19 (Z_to_bv 64 18446744073709551615)
             x21 (Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i))) x23 x24
             (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 4094) (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 V01_PC_JOIN) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros i H tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 w19 E19.
  subst w19. exact (H tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31).
Qed.

Lemma split_eq : forall i, V01_SPLITat X i ->
  forall tb a m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 w19 w23 : word),
  w19 = Z_to_bv 64 (v_mm X) -> w23 = Z_to_bv 64 (v_mm X + 256 * Z.of_nat i) ->
  V01_lmem X a tb m -> V01_inv X i tb a -> (i < length (v_segs X))%nat ->
  ms_ignore (nth i (v_segs X) mseg_d) = false ->
  evt rsegs (V01_post X)
    (MS (mkR x1 (Z_to_bv 64 (v_sp X)) (v_gp X) (v_tp X) x5 x6 x7 x8
             (Z_to_bv 64 (v_mm X + 256 * Z.of_nat i)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (18446744073709551615 - v_mm X)) w19 (Z_to_bv 64 18446744073709551615)
             x21 (Z_to_bv 64 (0 - (v_mm X + 256 * Z.of_nat i))) w23 x24
             (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 4094) (Z_to_bv 64 (v_mm X + MC_N)) x28 x29 x30 x31)
        (v_F X) (Z_to_bv 64 V01_PC_SPLIT) (v_fc X) None m (seg_rom rsegs)).
Proof.
  intros i H tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 w19 w23 E19 E23.
  subst w19 w23. exact (H tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31).
Qed.

(** The join after turn i, given the head of turn i + 1. *)
Lemma join_at : forall i, (S i < length (v_segs X) -> V01_HEADat X (S i))%nat -> V01_JOINat X i.
Proof.
  intros i IHh tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 HM HI Hi.
  pose proof (len32 a tb m HM) as N32.
  pose proof nums as (S1 & S2 & M1 & M2).
  destruct (mc_of a tb m HM) as (bs & B & E).
  pose proof (rd_n X m bs B E) as RN. clear B E.
  (* 0x13fb8 lw a0,0(s11) *)
  zstep. rewrite ?(sx32_small (Z.of_nat (length (v_segs X)))) by lia.
  (* 0x13fbc s9 += 1; 0x13fc0 s6 -= 256; 0x13fc4 s1 += 256 *)
  zstep. zstep. zstep.
  (* 0x13fc8 blt s9,a0 *)
  zstep. if_cases K; cbv iota.
  - zify_cond K. rewrite ?sgn_small in K by lia.
    eapply (head_eq (S i) (IHh ltac:(lia))); [weq | weq | weq | weq | exact HM | exact HI | lia].
  - zify_cond K. rewrite ?sgn_small in K by lia.
    (* 0x13fcc j 0x141ac *)
    zstep.
    destruct HI as (_ & HA & HD).
    rewrite decl_end in HD by lia.
    eapply HTL; [symmetry; exact HD | lia | exact HM].
Qed.

(** The head of turn i, given the join after it. *)
Lemma head_at : forall i, V01_JOINat X i -> V01_HEADat X i.
Proof.
  intros i JN tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 HM HI Hi.
  pose proof (len32 a tb m HM) as N32.
  pose proof nums as (S1 & S2 & M1 & M2).
  pose proof (cells_of a tb m HM) as FC.
  destruct (mc_of a tb m HM) as (bs & B & E).
  destruct (ms_ignore (nth i (v_segs X) mseg_d)) eqn:IG.
  - pose proof (rd_ign X m bs i true B E Hi IG) as RI. change (if true then 1 else 0) with 1 in RI. clear B E.
    (* 0x13f98 a0 = 32; 0x13f9c beq s9,a0 -> trap *)
    zstep. zstep. if_cases K; cbv iota; [dead K|].
    (* 0x13fa0 s7 = i << 8; 0x13fa4 bltu s2,s7 -> trap *)
    zstep. rewrite ?shl8.
    zstep. if_cases K0; cbv iota; [dead K0|].
    (* 0x13fa8 ld s3,0x50(sp); 0x13fac s7 = m + 256 i; 0x13fb0 lw a0,0x18(s7) *)
    zstep. zstep. zstep.
    (* 0x13fb4 beqz a0: ignore = 1, falls into the join *)
    zstep. if_cases K1; cbv iota; [exfalso; vm_compute in K1; discriminate K1|].
    eapply (join_eq i JN); [weq | exact HM | apply inv_skip; assumption | lia].
  - pose proof (rd_ign X m bs i false B E Hi IG) as RI. change (if false then 1 else 0) with 0 in RI. clear B E.
    zstep. zstep. if_cases K; cbv iota; [dead K|].
    zstep. rewrite ?shl8.
    zstep. if_cases K0; cbv iota; [dead K0|].
    zstep. zstep. zstep.
    (* 0x13fb4 beqz a0: ignore = 0, the split stretch at 0x13fd0 *)
    zstep. if_cases K1; cbv iota; [|exfalso; vm_compute in K1; discriminate K1].
    eapply (split_eq i (HSP i JN (HAC i JN HTL))); [weq | weq | exact HM | exact HI | exact Hi | exact IG].
Qed.

(** By induction on the turns left. *)
Lemma loop : forall k i, (i + k = length (v_segs X))%nat -> V01_HEADat X i /\ V01_JOINat X i.
Proof.
  induction k as [|k IH]; intros i Hik.
  - split.
    + intros tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 HM HI Hi. lia.
    + intros tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 HM HI Hi. lia.
  - assert (JN : V01_JOINat X i).
    { apply join_at. intros Hs. exact (proj1 (IH (S i) ltac:(lia))). }
    split; [apply head_at; exact JN | exact JN].
Qed.

Lemma head_all : V01_HEAD X.
Proof.
  intros i. destruct (Nat.le_gt_cases (length (v_segs X)) i) as [Hge|Hlt].
  - intros tb a m x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 HM HI Hi. lia.
  - exact (proj1 (loop (length (v_segs X) - i) i ltac:(lia))).
Qed.

End Loop.

Lemma v01_loop : forall X : V01D.vctx, V01D.V01_geo X -> V01D.V01_SPLIT X -> V01D.V01_ACC X -> V01D.V01_TAIL X ->
  V01D.V01_HEAD X.
Proof. intros X HG HSP HAC HTL. apply head_all; assumption. Qed.
