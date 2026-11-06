(** m_file (UBSan build, image 1696d6c34ffd): the sub-piece S_MFU_LONGP of S_MF_LINE (U/Prog/mfu_cuts.v). From
    the cut LONG 0x143a4 (the line [p, p + |l|) has 512 bytes or more; s5 = p, a0 = p + |l|) to the tail 0x146b4
    (H_MF_TAIL).

    Code (the UBSan build's disassembly):
      0x143a4 bgeu s5,a0 -> 0x146a8 (not taken: |l| >= 512)
      0x143a8 lbu a1,0(s5); bltu s10,a1 -> 0x14690 (a byte above ' ' is not blank); srl a2,s9,a1; andi a2,a2,1;
              beqz a2 -> 0x14690 (the blank mask); s5 += 1; bne s5,a0 -> 0x143a8; j 0x146a8 (all blank)
      0x14690 a0 = (a1 = '[') - 1 (seqz, addi -1); cur cell 0x30(sp) &= a0 (ld, and, sd): cur = NULL on '['
      0x146a8 a0 = s0 = c; a1 = s3 = line + 1; jal m_refuse 0x146b0; then the tail 0x146b4.
    The model: m_line's long branch (Prog/mfp_facts.v m_line_long), the first non-blank byte by dropwhile_blank_idx.
    The call: mfu_refuse of U/Prog/mfu_kit.v; the tail: mfu_tail. The frame cells the tail asks for are transported
    from the cut memory over the cur store (the cell 0x30 only) and over m_refuse's footprint (below sp and the block). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec mfu_facts mfp_facts mfp_mconf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts mfu_kit m_refuse_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists, bytes and words *)
Lemma longu_firstn1 : forall {A} (l : list A) i d, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  intros A l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Lemma longu_saved_len : forall ws : list word, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; cbn [map concat length]; [reflexivity|].
  rewrite length_app, length_le8, IH; lia.
Qed.

(** Byte i of a C string. *)
Lemma longu_byte : forall m a s i, cstr_at rsegs m a s -> (i < length s)%nat ->
  exists b, ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [b] /\ bv_unsigned b = nth i s 0.
Proof.
  intros m a s i (bs & sl & BA & ZS & _ & _) Hi.
  assert (Lb : length bs = length s) by (rewrite <- ZS; unfold zs; rewrite length_map; reflexivity).
  exists (nth i bs ZERO). split.
  - rewrite (bytes_at_ov_read rsegs m a (bs ++ ZERO :: sl) i 1 BA) by (rewrite length_app; cbn [length]; lia).
    rewrite (longu_firstn1 _ i ZERO) by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by lia; reflexivity.
  - rewrite <- ZS. unfold zs. rewrite <- (map_nth bv_unsigned bs ZERO i). apply nth_indep. rewrite length_map. lia.
Qed.

Lemma longu_cstr_bound : forall m a s, cstr_at rsegs m a s -> 0 <= a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m a s (bs & sl & BA & ZS & _ & _).
  assert (Lb : length bs = length s) by (rewrite <- ZS; unfold zs; rewrite length_map; reflexivity).
  apply bytes_at_bound in BA. rewrite length_app in BA. cbn [length] in BA. lia.
Qed.

Lemma longu_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
  intros rest. destruct (mf_line_rest rest) as [[E _]|[E _]].
  - pose proof (f_equal (@length Z) E) as L. rewrite length_app in L. cbn [length] in L. lia.
  - pose proof (f_equal (@length Z) E) as L. lia.
Qed.

(** An 8-byte frame cell inside the stack region, as a writable cell, and back. *)
Lemma longu_rw_of_cell : forall m lo hi A v, bytes_at rsegs m A (le8 v) -> stk rsegs m lo hi -> lo <= A ->
  A + 8 <= hi -> rw_cells rsegs m A [C8 v].
Proof.
  intros m lo hi A v B (H1 & H2 & H) HA HB.
  pose proof (bytes_at_bound rsegs m A (le8 v) B) as BB. rewrite length_le8 in BB.
  unfold rw_cells, cells_at, wr_at. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (H (A + i) ltac:(lia))).
Qed.

Lemma longu_cell_of_rw : forall m A v, rw_cells rsegs m A [C8 v] -> bytes_at rsegs m A (le8 v).
Proof. intros m A v [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

(** The blank test 0x143b0-0x143b8 for a byte x <= ' ': bit x of the mask. *)
Lemma longu_blank_bit : forall x, 0 <= x <= 32 ->
  (Z.land (Z.shiftr 4294976000 (x mod 64)) 1 = 0 <-> blank x = false).
Proof.
  intros x Hx. rewrite (Z.mod_small x 64) by lia. rewrite (blank_mask x Hx).
  assert (E : Z.land (Z.shiftr 4294976000 x) 1 = Z.shiftr 4294976000 x mod 2)
    by exact (Z.land_ones (Z.shiftr 4294976000 x) 1 ltac:(lia)).
  assert (R : 0 <= Z.shiftr 4294976000 x mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  rewrite E. split; intros H.
  - rewrite H; reflexivity.
  - apply Z.eqb_neq in H. lia.
Qed.

(** The cursor value 0x14690-0x146a0: cur & ((b = '[') - 1). *)
Lemma longu_mask_val : forall x v, 0 <= x < 256 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (x + -91)) 1) + -1)))
                     (bv_unsigned (Z_to_bv 64 v)))
  = Z_to_bv 64 (if x =? LBR then 0 else v).
Proof.
  intros x v Hx. unfold v_sltiu.
  destruct (Z.eqb_spec x 91) as [->|Hne].
  - match goal with |- context [Z.land ?a _] => replace a with 0 by (vm_compute; reflexivity) end.
    rewrite Z.land_0_l; reflexivity.
  - try rewrite (proj2 (Z.eqb_neq x 91) Hne).
    replace (bv_unsigned (Z_to_bv 64 (x + -91)) <? bv_wrap 64 1) with false.
    2: { first [symmetry; apply Z.ltb_ge | apply Z.ltb_ge]. rewrite unsigned_lit_wrap.
         try change (bv_wrap 64 1) with 1. try change (2 ^ 64) with 18446744073709551616.
         Z.div_mod_to_equations. lia. }
    match goal with |- context [Z.land ?a _] => replace a with 18446744073709551615 by (vm_compute; reflexivity) end.
    rewrite Z.land_comm, Z_to_bv_land64; apply Z_to_bv_lit_self.
Qed.

(** ** The walk *)
Section Long.
Variables (n : nat) (ra sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (mcut : word -> option byte) (lo : Z)
  (ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (c p line : Z) (mc : mconf) (cur : option nat)
  (k0 : nat) (rest : list Z).
Hypothesis HMR : m_refuse_contract.
Hypothesis HT : H_MF_TAIL n.
Hypothesis Hn : (length rest <= n)%nat.
Hypothesis Hne : rest <> [].
Hypothesis HL : m_file_loop mcut fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis Hlong : (512 <= length (mf_line rest))%nat.

(** The numbers of the loop facts. *)
Lemma longu_facts :
  bv_unsigned sp + 272 = bv_unsigned sp0 /\ lo + 6224 <= bv_unsigned sp0 /\ 0 <= lo /\
  bv_unsigned sp0 < 2 ^ 63 /\ 0 <= c /\ c + 9236 <= 2 ^ 64 /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\ 0 <= p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64.
Proof.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWR & _ & _ & _ &
                 _ & Hl0 & Hl1 & _ & _ & _ & _ & HCS & _ & _ & HPE & _ & _ & HSO & _).
  destruct HPE as (_ & _ & _ & _ & Hsp63). destruct HSO as ((Hlo0 & _) & Hlo & _ & _).
  destruct HWR as (Hc1 & Hc2 & _). destruct (longu_cstr_bound _ _ _ HCS) as [Hp1 Hp2].
  unfold M_FILE_FRAME in Hsp. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in Hlo. unfold SEG_M_SIZE in Hc2.
  repeat split; lia.
Qed.

Lemma longu_apart : c + 9240 <= lo \/ bv_unsigned sp0 <= c.
Proof.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAP & _).
  unfold apart, SEG_M_SIZE in HAP. lia.
Qed.

(** The frame cells across the cur store and across m_refuse. *)
Lemma longu_keep1 : forall m m1 A bs, bytes_at rsegs m A bs ->
  munch [(bv_unsigned sp + 48, bv_unsigned sp + 56)] m m1 ->
  A + Z.of_nat (length bs) <= bv_unsigned sp + 48 \/ bv_unsigned sp + 56 <= A ->
  bytes_at rsegs m1 A bs.
Proof.
  intros m m1 A bs B MU D. eapply bytes_at_transport; [exact B | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma longu_keep2 : forall m1 m2 A bs, bytes_at rsegs m1 A bs ->
  munch (m_refuse_W (bv_unsigned sp) c mc) m1 m2 ->
  bv_unsigned sp <= A -> A + Z.of_nat (length bs) <= bv_unsigned sp0 ->
  bytes_at rsegs m2 A bs.
Proof.
  intros m1 m2 A bs B MU H1 H2. eapply bytes_at_transport; [exact B | exact MU |].
  destruct longu_facts as (Hsp & Hlo & _ & _ & Hc1 & Hc2 & _).
  pose proof longu_apart as AP.
  unfold m_refuse_W, M_REFUSE_STACK, PRINTF_K, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED.
  destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:E8; cbn [app disjoint_from].
  - apply Z.ltb_lt in E8. repeat split; lia.
  - repeat split; lia.
Qed.

(** 0x146a8: m_refuse(c, line + 1), then the tail, from a memory m that differs from the cut's in the cur cell
    only, which holds cur'. *)
Lemma longu_refuse : forall (cur' : option nat) (m : word -> option byte)
    (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
  munch [(bv_unsigned sp + 48, bv_unsigned sp + 56)] mcut m -> wmono rsegs mcut m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp0) -> cell8 m (bv_unsigned sp + 48) (cur_ptr c cur') -> cur_ok mc cur' ->
  evt rsegs (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0
               (mf_fin (m_refuse mc (line + 1) false, cur') line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) s5 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x146a8) fc None m (seg_rom rsegs)).
Proof.
  intros cur' m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 MU WM MI ST CC HCO'.
  destruct longu_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hl0 & Hl1 & Hp1 & Hp2).
  pose proof longu_apart as AP.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & HSV & C08 & C10 & C18 & C20 & C28 & _ & _ & _ & _ & HMA & _ & _ & _ & _ &
                 _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPE & _ & _ & _ & _).
  destruct HPE as (FRM & _).
  pose proof (u64_range sp) as Rsp.
  assert (MID : mfu_mid mcut m (bv_unsigned sp0) lo c k0 mc false).
  { unfold mfu_mid. split; [|split; [exact WM|split; [exact MI|split; [exact ST|]]]].
    - eapply munch_weaken; [|exact MU]. unfold sub_fp, mfu_W, M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K.
      cbn [outside app]. intros x [H1 _]. split; [lia | exact I].
    - eapply mconf_atp_transport; [exact HMA | exact MU |]. unfold SEG_M_SIZE. cbn [disjoint_from].
      split; [lia | exact I]. }
  clear HMA.
  do 3 step.
  eapply (mfu_refuse HMR).
  - exact HL.
  - exact Hne.
  - exact MID.
  - apply mf_grows_refl.
  - reflexivity.
  - exact FRM.
  - rewrite unsigned_lit by lia; lia.
  - rewrite unsigned_lit by lia; lia.
  - intros m' F' fc' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID' MUr WMr FRM' FREL.
    rewrite ret_pc_even by (try lia; reflexivity).
    unfold cell8 in *.
    eapply (mfu_tail n) with (Fc := F) (fcc := fc) (mcut := mcut) (p := p) (mc := mc) (cur := cur).
    + exact HT.
    + exact Hn.
    + exact Hne.
    + exact HL.
    + exact MID'.
    + unfold saved_at in *. unfold M_FILE_SAVE in *.
      apply (longu_keep2 m); [apply (longu_keep1 mcut); [exact HSV | exact MU |] | exact MUr | |];
        rewrite ?longu_saved_len; cbn [length]; lia.
    + unfold cell8. apply (longu_keep2 m); [apply (longu_keep1 mcut); [exact C08 | exact MU |] | exact MUr | |];
        rewrite ?length_le8; lia.
    + unfold cell8. apply (longu_keep2 m); [apply (longu_keep1 mcut); [exact C10 | exact MU |] | exact MUr | |];
        rewrite ?length_le8; lia.
    + unfold cell8. apply (longu_keep2 m); [apply (longu_keep1 mcut); [exact C18 | exact MU |] | exact MUr | |];
        rewrite ?length_le8; lia.
    + unfold cell8. apply (longu_keep2 m); [apply (longu_keep1 mcut); [exact C20 | exact MU |] | exact MUr | |];
        rewrite ?length_le8; lia.
    + unfold cell8. apply (longu_keep2 m); [apply (longu_keep1 mcut); [exact C28 | exact MU |] | exact MUr | |];
        rewrite ?length_le8; lia.
    + unfold cell8. apply (longu_keep2 m); [exact CC | exact MUr | |]; rewrite ?length_le8; lia.
    + apply m_refuse_grows.
    + destruct cur' as [j|]; [exact HCO' | exact I].
    + change (mc_refused (m_refuse mc (line + 1) false)) with (mc_refused mc + 1). lia.
    + change (mc_overflow (m_refuse mc (line + 1) false)) with (mc_overflow mc). lia.
    + exact FRM'.
    + exact FREL.
    + unfold m_file_regs. repeat split; reflexivity.
Qed.

(** 0x14690: the first non-blank byte x = l[i]: cur = NULL when x is '[', then 0x146a8. *)
Lemma longu_nb : forall i x (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word),
  (i < length (mf_line rest))%nat -> all_blank (mf_line rest) 0 i -> nth i (mf_line rest) 0 = x ->
  blank x = false -> 0 <= x < 256 ->
  evt rsegs (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0
               (mf_fin (m_refuse mc (line + 1) false,
                        if hd0 (dropwhile blank (mf_line rest)) =? LBR then None else cur) line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 a0 (Z_to_bv 64 x) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) s5 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14690) fc None mcut (seg_rom rsegs)).
Proof.
  intros i x t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 Hi HB Hx Hbx Hx8.
  assert (HD : hd0 (dropwhile blank (mf_line rest)) = x).
  { rewrite (dropwhile_blank_idx (mf_line rest) i); [| lia | exact HB | right; rewrite Hx; exact Hbx].
    rewrite hd0_skipn. exact Hx. }
  rewrite HD.
  destruct longu_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hl0 & Hl1 & Hp1 & Hp2).
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & C30 & _ & _ & _ & _ & _ & _ & _ & HCO &
                 _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSO & MI).
  destruct HSO as (ST & _).
  pose proof (u64_range sp) as Rsp.
  pose proof (longu_rw_of_cell mcut lo (bv_unsigned sp0) (bv_unsigned sp + 48) (Z_to_bv 64 (cur_ptr c cur))
                C30 ST ltac:(lia) ltac:(lia)) as RW.
  clear C30.
  pose proof (munch_refl [(bv_unsigned sp + 48, bv_unsigned sp + 56)] mcut) as MU.
  pose proof (wmono_refl rsegs mcut) as WM.
  do 6 step.
  rewrite (longu_mask_val x (cur_ptr c cur) Hx8) in RW.
  eapply longu_refuse.
  - exact MU.
  - exact WM.
  - exact MI.
  - exact ST.
  - unfold cell8.
    replace (cur_ptr c (if x =? LBR then None else cur)) with (if x =? LBR then 0 else cur_ptr c cur)
      by (destruct (x =? LBR); reflexivity).
    apply longu_cell_of_rw. exact RW.
  - destruct (x =? LBR); [exact I | exact HCO].
Qed.

(** The blank skip 0x143a8 at byte i of the line (k bytes left, all before i blank): s5 = p + i, a0 = p + |l|. *)
Lemma longu_loop : forall k i (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w5 : word),
  (i + k = length (mf_line rest))%nat -> (0 < k)%nat -> all_blank (mf_line rest) 0 i ->
  w5 = Z_to_bv 64 (p + Z.of_nat i) ->
  evt rsegs (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0
               (mf_fin (m_refuse mc (line + 1) false,
                        if hd0 (dropwhile blank (mf_line rest)) =? LBR then None else cur) line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 (p + Z.of_nat (length (mf_line rest)))) a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) w5
             (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK)
             (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 0x143a8) fc None mcut (seg_rom rsegs)).
Proof.
  destruct longu_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hl0 & Hl1 & Hp1 & Hp2).
  pose proof (longu_line_len rest) as HLL.
  pose proof HL as X. unfold m_file_loop in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & C30 & _ & _ & _ & _ & _ & _ & _ & HCO &
                 _ & _ & _ & _ & _ & _ & _ & HCS & _ & _ & _ & _ & _ & HSO & MI).
  destruct HSO as (ST & _).
  induction k as [|k IH]; intros i t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w5 Hik Hk HB E5; [lia|].
  subst w5. unfold BLANK_MASK.
  assert (Hi : (i < length (mf_line rest))%nat) by lia.
  destruct (longu_byte mcut p rest i HCS ltac:(lia)) as (b & RD & Eb).
  rewrite (mf_line_nth rest i Hi) in Eb.
  assert (EX : exists x, nth i (mf_line rest) 0 = x) by (eexists; reflexivity).
  destruct EX as (x & Ex). rewrite Ex in Eb.
  assert (Hx8 : 0 <= x < 256).
  { rewrite <- Eb. pose proof (bv_unsigned_in_range 8 b) as R8. unfold bv_modulus in R8.
    change (Z.of_N 8) with 8 in R8. lia. }
  step. unfold zxb. rewrite Eb.
  step. if_cases K; cbv iota.
  - zify_cond K. rewrite ?Z.mod_small in K by lia.
    eapply longu_nb; [exact Hi | exact HB | exact Ex | apply blank_gt32; lia | exact Hx8].
  - zify_cond K. rewrite ?Z.mod_small in K by lia.
    step. step. step. if_cases K2; cbv iota.
    + zify_cond K2.
      apply (proj1 (longu_blank_bit x ltac:(lia))) in K2.
      eapply longu_nb; [exact Hi | exact HB | exact Ex | exact K2 | exact Hx8].
    + zify_cond K2.
      assert (Bx : blank x = true).
      { destruct (blank x) eqn:B; [reflexivity|]. exfalso. apply K2.
        apply (proj2 (longu_blank_bit x ltac:(lia))). exact B. }
      assert (HB' : all_blank (mf_line rest) 0 (S i)).
      { unfold all_blank in *. intros k' Hk'.
        destruct (Nat.eq_dec k' i) as [->|Hne']; [rewrite Ex; exact Bx | apply HB; lia]. }
      step. step. if_cases K3; cbv iota.
      * zify_cond K3. rewrite ?Z.mod_small in K3 by lia.
        eapply (IH (S i)); [lia | lia | exact HB' | f_equal; lia].
      * zify_cond K3. rewrite ?Z.mod_small in K3 by lia.
        step.
        assert (HD : hd0 (dropwhile blank (mf_line rest)) = 0).
        { rewrite (dropwhile_blank_idx (mf_line rest) (length (mf_line rest)));
            [| lia | unfold all_blank in *; intros k' Hk'; apply HB'; lia | left; reflexivity].
          rewrite hd0_skipn. apply nth_overflow. lia. }
        rewrite HD. change (if 0 =? LBR then None else cur) with cur.
        eapply longu_refuse; [apply munch_refl | apply wmono_refl | exact MI | exact ST | exact C30 | exact HCO].
Qed.

(** From the cut LONG 0x143a4. *)
Lemma longu_main : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0
               (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) s1 (Z_to_bv 64 (p + Z.of_nat (length (mf_line rest)))) a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) (Z_to_bv 64 p)
             (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK)
             (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) t3 t4 t5 t6)
        F (Z_to_bv 64 MFU_PC_LONG) fc None mcut (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  destruct longu_facts as (Hsp & Hlo & Hlo0 & Hsp63 & Hc1 & Hc2 & Hl0 & Hl1 & Hp1 & Hp2).
  pose proof (longu_line_len rest) as HLL.
  rewrite (m_line_long mc cur (line + 1) (mf_line rest) Hlong).
  unfold MFU_PC_LONG.
  step. if_cases K; cbv iota; [exfalso; zify_cond K; rewrite ?Z.mod_small in K by lia; lia|].
  eapply (longu_loop (length (mf_line rest)) 0); [lia | lia | unfold all_blank; intros k' Hk'; lia | f_equal; lia].
Qed.

End Long.

Lemma mfu_longp_holds : m_refuse_contract -> S_MFU_LONGP.
Proof.
  intros HMR n HT. unfold H_MFU_LONG.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest Hn Hne HL HR E4 E6 E5 E0 Hlong.
  destruct HR as (Es0 & Es2 & Es3 & Es7 & Es8 & Es9 & Es10 & Es11).
  subst s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0.
  eapply longu_main; eassumption.
Qed.
