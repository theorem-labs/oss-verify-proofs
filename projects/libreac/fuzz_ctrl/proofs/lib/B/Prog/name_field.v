From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes
  ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib RcAsan
  RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_memset_c name_field_c.
Import ListNotations.
Open Scope Z_scope.

(* name_field in the asan-ubsan image (0x879e4 .. 0x87af8), ported from the ubsan proof lib/U/Prog/name_field.v.
   The code: a 32-byte frame that holds ra, s0, s1, s2; the shadow base 0x7fff8000 into s2 (two loads, through the
   cell at 0xa08f0 and the cell at 0xa96b8); __asan_memset(N, 0, 16) (0x52600); the 8-alignment check of m (branch to
   unimp at 0x87ae8); the instrumented check of the 8-byte load at m + 280 (the shadow byte must be 0, else the error
   path at 0x87af0); the load of the name pointer, and when it is not 0 the copy loop of at most 16 bytes, each step
   with: the instrumented check of the 8-byte load at m + 280 again, the overflow and null checks of name + i (branches
   to unimp), the instrumented check of the 1-byte load at name + i (slow path at 0x87ab4, error path at 0x87af4), the
   stop on a zero byte, the bound check of N + i (branch to unimp), the instrumented check of the 1-byte store at N + i
   (slow path at 0x87ac0, error path through 0x87ac8), the store; then the epilogue. Each check passes because the
   bytes are addressable (premises addressable m (m + 280) 8, addressable m name (length nb), addressable m N 16); no
   branch to unimp or to the error path is taken. *)

(* The shadow byte of X = base + j for addressable base len (the instrumented check of a 1-byte access). *)
Lemma nf_sh : forall mc base len X j, addressable mc base len -> 0 <= j < len -> X = base + j ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + 2147450880)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc base len X j AD Hj ->.
  pose proof (rt_shadow_rd mc base len [] AD (fun x _ => I)) as HSR.
  pose proof (rt_addressable mc base len AD) as HAD.
  destruct (asan_shadow_read rsegs mc ASAN_K base len [] j HSR Hj) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [exact (HAD j k Hj BK) | apply rc_byte_signed].
Qed.

(* The shadow byte of an 8-aligned addressable 8-byte range is 0 (the instrumented check of an 8-byte load). *)
Lemma nf_sh8 : forall mc p, addressable mc p 8 -> p mod 8 = 0 ->
  ov_read_bytes rsegs mc (wa (p / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros mc p AD Hm.
  pose proof (rt_shadow_rd mc p 8 [] AD (fun x _ => I)) as HSR.
  pose proof (rt_addressable mc p 8 AD) as HAD.
  pose proof (rt_rt3 mc p 8 AD) as H3.
  destruct (asan_shadow_read rsegs mc ASAN_K p 8 [] 0 HSR ltac:(lia)) as (k & RK & BK).
  pose proof (asan_check_8 rsegs mc ASAN_K p 8 0 k HAD H3 ltac:(lia) ltac:(lia)
                ltac:(rewrite Z.add_0_r; exact Hm) BK) as K0.
  rewrite Z.add_0_r in RK.
  replace (Z_to_bv 8 0) with k; [exact RK|].
  apply bv_eq. rewrite (rc_signed0_unsigned0 k K0). reflexivity.
Qed.

Lemma nf_mod280 : forall a, a mod 8 = 0 -> (a + 280) mod 8 = 0.
Proof. intros a H. Z.div_mod_to_equations. lia. Qed.

(* The function's write window: the stack window and the 16 bytes at N, all application memory. *)
Lemma nf_aw : forall mc sp wn, HIGHMEM_BEG <= sp - 2240 -> sp <= APPMEM_END -> addressable mc wn 16 ->
  all_app [(sp - 2240, sp); (wn, wn + 16)].
Proof.
  intros mc sp wn H1 H2 AD. cbn [all_app]. split; [|split; [exact (addressable_app mc wn 16 AD) | exact I]].
  intros x Hx. unfold app_mem. right. lia.
Qed.

Lemma nf_drt : forall sp wn, HIGHMEM_BEG <= sp - 2240 -> (wn + 16 <= RT_LO \/ RT_HI <= wn) ->
  disjoint_from [(sp - 2240, sp); (wn, wn + 16)] RT_LO (RT_HI - RT_LO).
Proof.
  intros sp wn H1 H2. cbn [disjoint_from]. unfold RT_LO, RT_HI, HIGHMEM_BEG in *.
  split; [lia | split; [lia | exact I]].
Qed.

(* A branch whose condition is a closed term that computes to false. *)
Ltac nf_pc_false_vm :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (vm_compute; reflexivity); cbv iota
  end.

Section NF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wm wn name : word) (nb : list byte).
  Hypothesis Rsp : 2240 <= bv_unsigned sp < 2^64.
  Hypothesis Hm288 : bv_unsigned wm + 288 <= 2^64.
  Hypothesis Hm8 : bv_unsigned wm mod 8 = 0.
  Hypothesis HN16 : bv_unsigned wn + 16 <= 2^64.
  Hypothesis Hname : bv_unsigned name <> 0 -> name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64.
  Hypothesis Dfm : bv_unsigned sp <= bv_unsigned wm + 280 \/ bv_unsigned wm + 288 <= bv_unsigned sp - 2240.
  Hypothesis Dfn : bv_unsigned sp <= bv_unsigned name \/
                   bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned sp - 2240.
  Hypothesis DfN : bv_unsigned sp <= bv_unsigned wn \/ bv_unsigned wn + 16 <= bv_unsigned sp - 2240.
  Hypothesis DNm : bv_unsigned wn + 16 <= bv_unsigned wm + 280 \/ bv_unsigned wm + 288 <= bv_unsigned wn.
  Hypothesis DNn : bv_unsigned wn + 16 <= bv_unsigned name \/ bv_unsigned name + Z.of_nat (length nb) <= bv_unsigned wn.
  Hypothesis HC : asan_cells m.
  Hypothesis HSW : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 2240.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis ADm : addressable m (bv_unsigned wm + 280) 8.
  Hypothesis ADn : addressable m (bv_unsigned name) (Z.of_nat (length nb)).
  Hypothesis ADN : addressable m (bv_unsigned wn) 16.
  Hypothesis HRT : bv_unsigned wn + 16 <= RT_LO \/ RT_HI <= bv_unsigned wn.

  Local Abbreviation W0 := [(bv_unsigned sp - 2240, bv_unsigned sp); (bv_unsigned wn, bv_unsigned wn + 16)].
  Local Abbreviation SPm := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Local Abbreviation A0w := (Z_to_bv 64 (bv_unsigned wm + 280)).
  Local Abbreviation SAw := (Z_to_bv 64 ((bv_unsigned wm + 280) / 8 + 2147450880)).
  Local Abbreviation SKw := (Z_to_bv 64 2147450880).
  Local Abbreviation PFX i := (firstn i nb ++ repeat (Z_to_bv 8 0) (16 - i)).

  Definition Qn : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wn) (nmf nb)
      /\ munch W0 m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp - 2240) (bv_unsigned sp)
      /\ asan_cells m' /\ shadow_rw m'.

  (* The loop invariant: the 16 bytes at N hold cur, the frame holds the four saved registers, the bytes at m + 280
     and at name are unchanged, and the memory differs from m only inside the window W0. *)
  Definition ninv (m' : word -> option byte) (cur : list byte) : Prop :=
    wr_at rsegs m' (bv_unsigned wn) 16 /\ length cur = 16%nat /\ bytes_at rsegs m' (bv_unsigned wn) cur /\
    rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
    bytes_at rsegs m' (bv_unsigned wm + 280) (le8 name) /\ bytes_at rsegs m' (bv_unsigned name) nb /\
    munch W0 m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' (bv_unsigned sp - 2240) (bv_unsigned sp + -32).

  Lemma AW0 : all_app W0.
  Proof. exact (nf_aw m (bv_unsigned sp) (bv_unsigned wn) HHM HAE ADN). Qed.

  Lemma DRT0 : disjoint_from W0 RT_LO (RT_HI - RT_LO).
  Proof. exact (nf_drt (bv_unsigned sp) (bv_unsigned wn) HHM HRT). Qed.

  Lemma nf_mk : forall m', munch W0 m m' -> meta_kept m m'.
  Proof. intros m' MU. exact (munch_meta _ m m' MU AW0). Qed.

  Lemma nf_adm : forall m', munch W0 m m' -> addressable m' (bv_unsigned wm + 280) 8.
  Proof. intros m' MU. exact (addressable_kept m m' _ _ ADm (nf_mk m' MU)). Qed.

  Lemma nf_adn : forall m', munch W0 m m' -> addressable m' (bv_unsigned name) (Z.of_nat (length nb)).
  Proof. intros m' MU. exact (addressable_kept m m' _ _ ADn (nf_mk m' MU)). Qed.

  Lemma nf_adN : forall m', munch W0 m m' -> addressable m' (bv_unsigned wn) 16.
  Proof. intros m' MU. exact (addressable_kept m m' _ _ ADN (nf_mk m' MU)). Qed.

  Lemma nf_cells : forall m', munch W0 m m' -> wmono rsegs m m' -> asan_cells m' /\ shadow_rw m'.
  Proof.
    intros m' MU WM. split; [exact (asan_cells_kept _ m m' HC MU DRT0)|].
    exact (shadow_rw_kept m m' HSW (nf_mk m' MU) WM).
  Qed.

  (* The epilogue (0x87ad0 .. 0x87ae4): the four restores, addi sp,sp,32 and ret. *)
  Lemma epi : forall (x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 : word) m',
    ninv m' (nmf nb) ->
    evt rsegs Qn
      (MS (mkR x1 SPm gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
               s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87ad0) fc None m' (seg_rom rsegs)).
  Proof.
    intros x1 u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m'
      (HW & _ & HB & FR & HM & HNm & MU & WM & MI & ST).
    destruct (nf_cells m' MU WM) as [HC' HSW'].
    step. step. step. step. step. step.
    apply evt_done. unfold Qn. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [|split; [exact HC' | exact HSW']].
    release_frame FR ST (bv_unsigned sp). exact ST.
  Qed.

  Lemma ninv_store : forall m' cur i (c : byte), ninv m' cur -> (i < 16)%nat ->
    ninv (write_to_mem m' (wa (bv_unsigned wn + Z.of_nat i)) [c]) (upd_bytes cur i [c]).
  Proof.
    intros m' cur i c (HW & Hlen & HB & FR & HM & HNm & MU & WM & MI & ST) Hi.
    pose proof (bytes_at_bound rsegs m' _ _ HB) as BB.
    pose proof (bytes_at_bound rsegs m' _ _ HNm) as BN.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wn) 16 (Z.of_nat i) 1 HW ltac:(lia) ltac:(lia)) as HS.
    split; [apply wr_at_write; exact HW|].
    split; [rewrite upd_bytes_length by (cbn [length]; lia); exact Hlen|].
    split.
    { pose proof (bytes_at_write_inside rsegs m' (bv_unsigned wn) cur (Z.of_nat i) [c] HB ltac:(lia)
                    ltac:(rewrite Nat2Z.id; cbn [length]; lia)) as H.
      rewrite Nat2Z.id in H. exact H. }
    split.
    { apply rw_cells_frame; [exact FR | lia | cbn [length]; lia |].
      cbn [cells_size csize Nat.add length]. lia. }
    split; [apply bytes_at_write_other; [exact HM | lia | cbn [length]; lia | rewrite length_le8; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact HNm | lia | cbn [length]; lia | cbn [length]; lia]|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; right; left; split; lia]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    apply stk_write; [exact ST | lia | cbn [length]; lia].
  Qed.

  (* The state at the loop head 0x87a4c for step i. *)
  Definition head_ok (i : nat) : Prop :=
    forall (x1 u0 u1 u2 x11 x14 x16 x17 u3 u4 u5 u6 : word) (m' : word -> option byte),
      bv_unsigned x14 = 18446744073709551615 - bv_unsigned wn ->
      (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
      ninv m' (PFX i) ->
      evt rsegs Qn
        (MS (mkR x1 SPm gp tp u0 u1 u2 wn wm A0w x11 SAw (Z_to_bv 64 (Z.of_nat i)) x14 (Z_to_bv 64 16) x16 x17
                 SKw s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x87a4c) fc None m' (seg_rom rsegs)).

  (* 0x87aa4 .. : the store of the byte at N + i, the loop test, and the next step or the epilogue. *)
  Lemma l_store : forall i, (i < 16)%nat -> (i < length nb)%nat -> bv_unsigned name <> 0 ->
    (S i < 16 -> head_ok (S i))%nat ->
    (forall j, (j <= i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
    forall (x1 u0 u1 u2 x14 x17 u3 u4 u5 u6 : word) (m' : word -> option byte),
      bv_unsigned x14 = 18446744073709551615 - bv_unsigned wn ->
      ninv m' (PFX i) ->
      evt rsegs Qn
        (MS (mkR x1 SPm gp tp u0 u1 u2 wn wm A0w (Z_to_bv 64 (bv_unsigned wn + Z.of_nat i)) SAw
                 (Z_to_bv 64 (Z.of_nat i)) x14 (Z_to_bv 64 16) (zxb (nth i nb (Z_to_bv 8 0))) x17
                 SKw s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x87aa4) fc None m' (seg_rom rsegs)).
  Proof.
    intros i Hi16 Hi NZ HNX Hnz x1 u0 u1 u2 x14 x17 u3 u4 u5 u6 m' H14 NI.
    destruct (Hname NZ) as (OK & Lnb).
    pose proof NI as (HW & Hlen & HB & FR & HM & HNm & MU & WM & MI & ST).
    pose proof (zr_word wn) as RN. unfold inr64 in RN.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wn) 16 (Z.of_nat i) 1 HW ltac:(lia) ltac:(lia)) as HS.
    step. step.
    rewrite le1_zxb.
    pose proof (ninv_store m' _ i (nth i nb (Z_to_bv 8 0)) NI ltac:(lia)) as NI'.
    rewrite upd_prefix in NI' by lia.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 16) by lia.
    destruct (Nat.lt_ge_cases (S i) 16) as [Hlt | Hge].
    - replace (Z.of_nat i + 1 =? 16) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      pose proof (HNX Hlt) as HH. unfold head_ok in HH.
      apply HH; [exact H14 | | exact NI'].
      intros j' Hj'. apply Hnz. lia.
    - replace (Z.of_nat i + 1 =? 16) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      step.
      assert (L16 : length nb = 16%nat) by (destruct OK as (OKl & _ & _); lia).
      replace (S i) with 16%nat in NI' by lia.
      rewrite <- (nmf_full nb L16) in NI'.
      2:{ intros j' Hj'. apply Hnz. lia. }
      apply epi. exact NI'.
  Qed.

  (* 0x87a84 .. : the byte nb[i], the stop on 0, the bound check of N + i, the instrumented check of the store at
     N + i (fast path, or the slow path at 0x87ac0 with (N + i) mod 8 < k), then l_store. *)
  Lemma l_byte : forall i, (i < 16)%nat -> (i < length nb)%nat -> bv_unsigned name <> 0 ->
    (S i < 16 -> head_ok (S i))%nat ->
    (forall j, (j < i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0) ->
    forall (x1 u0 u1 u2 x14 x16 x17 u3 u4 u5 u6 : word) (m' : word -> option byte),
      bv_unsigned x14 = 18446744073709551615 - bv_unsigned wn ->
      ninv m' (PFX i) ->
      evt rsegs Qn
        (MS (mkR x1 SPm gp tp u0 u1 u2 wn wm A0w (Z_to_bv 64 (bv_unsigned name + Z.of_nat i)) SAw
                 (Z_to_bv 64 (Z.of_nat i)) x14 (Z_to_bv 64 16) x16 x17
                 SKw s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x87a84) fc None m' (seg_rom rsegs)).
  Proof.
    intros i Hi16 Hi NZ HNX Hnz x1 u0 u1 u2 x14 x16 x17 u3 u4 u5 u6 m' H14 NI.
    destruct (Hname NZ) as (OK & Lnb).
    pose proof NI as (HW & Hlen & HB & FR & HM & HNm & MU & WM & MI & ST).
    pose proof (zr_word wn) as RN. unfold inr64 in RN.
    pose proof (rd_byte rsegs m' (bv_unsigned name) nb i HNm Hi) as RD.
    step. step.
    rewrite rc_zxb_eqb0.
    destruct (Z.eqb_spec (bv_unsigned (nth i nb (Z_to_bv 8 0))) 0) as [C0 | CNZ].
    - cbv iota.
      rewrite <- (nmf_stop nb i Hi ltac:(lia) Hnz C0) in NI.
      apply epi. exact NI.
    - cbv iota.
      clear RD.
      step.
      rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x14) by (rewrite unsigned_lit by lia; lia).
      cbv iota.
      step. step.
      rewrite (unsigned_lit (bv_unsigned wn + Z.of_nat i)) by lia. rewrite rc_shr3.
      step.
      destruct (nf_sh m' (bv_unsigned wn) 16 (bv_unsigned wn + Z.of_nat i) (Z.of_nat i) (nf_adN m' MU)
                  ltac:(lia) eq_refl) as (k & RK & OKk & KR).
      step.
      clear RK.
      step.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
      assert (Hnz' : forall j, (j <= i)%nat -> bv_unsigned (nth j nb (Z_to_bv 8 0)) <> 0).
      { intros j Hj. destruct (Nat.eq_dec j i) as [->|Ne]; [exact CNZ | apply Hnz; lia]. }
      destruct (Z.eqb_spec (bv_signed k) 0) as [K0 | K0]; cbn [negb]; cbv iota.
      + apply l_store; assumption.
      + step.
        rewrite (unsigned_lit (bv_unsigned wn + Z.of_nat i)) by lia. rewrite rc_land7.
        step.
        rewrite (rc_lts_signed ((bv_unsigned wn + Z.of_nat i) mod 8) (bv_signed k))
          by (pose proof (Z.mod_pos_bound (bv_unsigned wn + Z.of_nat i) 8 ltac:(lia)); lia).
        replace ((bv_unsigned wn + Z.of_nat i) mod 8 <? bv_signed k) with true
          by (symmetry; apply Z.ltb_lt; lia).
        cbv iota.
        apply l_store; assumption.
  Qed.

  (* 0x87a4c .. : the instrumented check of the 8-byte load at m + 280, the load of name, the checks of name + i
     (no unsigned wrap, no wrap to 0, name <> 0), the instrumented check of the 1-byte load at name + i (fast path, or
     the slow path at 0x87ab4 with (name + i) mod 8 < k), then l_byte. *)
  Lemma l_head : forall i, (i < 16)%nat -> bv_unsigned name <> 0 -> (S i < 16 -> head_ok (S i))%nat -> head_ok i.
  Proof.
    intros i Hi16 NZ HNX. unfold head_ok.
    intros x1 u0 u1 u2 x11 x14 x16 x17 u3 u4 u5 u6 m' H14 Hnz NI.
    destruct (Hname NZ) as (OK & Lnb).
    pose proof (name_ok_lt nb i OK Hi16 Hnz) as Hi.
    pose proof NI as (HW & Hlen & HB & FR & HM & HNm & MU & WM & MI & ST).
    pose proof (zr_word name) as Rn. unfold inr64 in Rn.
    pose proof (nf_sh8 m' (bv_unsigned wm + 280) (nf_adm m' MU) (nf_mod280 _ Hm8)) as RS8.
    pose proof (rd_le8 rsegs m' _ name HM) as HR.
    step. step.
    nf_pc_false_vm.
    step. step. step.
    rewrite (rc_ltu_ge name (Z_to_bv 64 (bv_unsigned name + Z.of_nat i))) by (rewrite unsigned_lit by lia; lia).
    cbv iota.
    step. step. step. step.
    rewrite (rc_ubchk name (Z_to_bv 64 (bv_unsigned name + Z.of_nat i))) by (try rewrite unsigned_lit by lia; lia).
    cbv iota.
    step.
    rewrite (rc_neq0w name NZ). cbv iota.
    clear RS8 HR.
    step.
    rewrite (unsigned_lit (bv_unsigned name + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    destruct (nf_sh m' (bv_unsigned name) (Z.of_nat (length nb)) (bv_unsigned name + Z.of_nat i) (Z.of_nat i)
                (nf_adn m' MU) ltac:(lia) eq_refl) as (k & RK & OKk & KR).
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0 | K0]; cbn [negb]; cbv iota.
    - eapply l_byte; eassumption.
    - step.
      rewrite (unsigned_lit (bv_unsigned name + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((bv_unsigned name + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (bv_unsigned name + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((bv_unsigned name + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb]. cbv iota.
      step.
      eapply l_byte; eassumption.
  Qed.

  Lemma loop : forall k i, (i + k = 16)%nat -> (0 < k)%nat -> bv_unsigned name <> 0 -> head_ok i.
  Proof.
    induction k as [|k IH]; intros i Hik Hk NZ; [lia|].
    apply l_head; [lia | exact NZ |].
    intros Hlt. apply IH; [lia | lia | exact NZ].
  Qed.
End NF.

Theorem name_field_holds : asan_memset_contract -> name_field_contract.
Proof.
  intros AMS. unfold asan_memset_contract, ASAN_MEMSET_K in AMS. cbv zeta in AMS.
  unfold name_field_contract, NAME_FIELD, NAME_FIELD_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    name nb junk ST Hm0 Hm8 Hm288 HNW HN16 HN HNB Dfm Dfn DfN DNm DNn MI HC HSW HHM HAE ADm ADn ADN HAN HRT.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (zr_word a1) as Ra1. unfold inr64 in Ra1.
  pose proof (zr_word name) as Rnm. unfold inr64 in Rnm.
  pose proof ST as (Rlo & _ & _).
  assert (HBn : bytes_at rsegs m (bv_unsigned name) nb /\
                (bv_unsigned name <> 0 -> name_ok nb /\ bv_unsigned name + Z.of_nat (length nb) <= 2^64) /\
                (bv_unsigned name = 0 -> nb = [])).
  { destruct HNB as [(E & ->) | (E & OK & L & B)].
    - split; [apply bytes_at_nil; pose proof (zr_word name) as R; unfold inr64 in R; lia|]. split; [tauto|]. auto.
    - split; [exact B|]. split; [auto|]. intros; contradiction. }
  clear HNB. destruct HBn as (HBn & Hname & Hnil).
  pose proof (nf_aw m (bv_unsigned sp) (bv_unsigned a1) HHM HAE ADN) as AW.
  pose proof (nf_drt (bv_unsigned sp) (bv_unsigned a1) HHM HRT) as DRT.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* addi sp,sp,-32 ; the four saves *)
  step.
  carve_frame 32%nat ST.
  step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  pose proof (asan_cells_kept _ m mA HC MU DRT) as HCA.
  pose proof (shadow_rw_kept m mA HSW (munch_meta _ m mA MU AW) WM) as HSWA.
  pose proof (addressable_kept m mA _ _ ADN (munch_meta _ m mA MU AW)) as ADNA.
  pose proof HCA as (Hk & Hg & _).
  pose proof (rd_le8 rsegs mA _ _ Hg) as RG. pose proof (rd_le8 rsegs mA _ _ Hk) as RC.
  unfold GOT_CELL_K, CELL_K, ASAN_K in RG, RC.
  clear Hk Hg.
  (* mv s0,a1 ; auipc ; ld a1 (cell) ; ld s2 (shadow base) *)
  step. step. step. step.
  clear RG RC.
  (* mv s1,a0 ; li a2,16 ; mv a0,s0 ; li a1,0 ; jal __asan_memset *)
  step. step. step. step. step.
  assert (EU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  pose proof ADNA as (_ & _ & _ & HA7).
  pose proof (proj1 (HA7 7 ltac:(lia))) as A7.
  eapply evt_cut.
  { eapply AMS with (junk := junk) (lo := bv_unsigned sp - 2240).
    all: rewrite ?EU; try change (bv_unsigned (Z_to_bv 64 16)) with 16.
    - exact HN.
    - lia.
    - exact ADNA.
    - unfold end_in_app. right. exact HAN.
    - right. exact A7.
    - exact HRT.
    - lia.
    - exact ST.
    - lia.
    - exact HHM.
    - lia.
    - exact HCA.
    - exact HSWA.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              -> & MU2 & WM2 & MI2 & ST2 & RW2 & HC2 & HSW2).
  unfold ASAN_MEMSET_K in MU2.
  rewrite !unsigned_lit in MU2 by lia.
  rewrite unsigned_lit in ST2 by lia.
  rewrite !unsigned_lit in RW2 by lia.
  change (Z.to_nat 16) with 16%nat in RW2.
  change (0 mod 256) with 0 in RW2.
  transport_after_call rsegs mA m2 MU2 WM2.
  clear MU2 WM2.
  replace (ret_pc (Z_to_bv 64 555548)) with (Z_to_bv 64 555548) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RW2 as [[_ HB1] HW1]. cbn [cells_bytes cbytes cells_size csize Nat.add] in HB1, HW1.
  rewrite app_nil_r in HB1.
  pose proof (nf_sh8 m2 (bv_unsigned a0 + 280) (addressable_kept m m2 _ _ ADm (munch_meta _ m m2 MU AW))
                (nf_mod280 _ Hm8)) as RS8.
  pose proof (rd_le8 rsegs m2 _ name HNW) as HR.
  (* andi a0,s1,7 ; bnez a0 (not taken: m mod 8 = 0) *)
  step. step.
  replace (Z.land (bv_unsigned a0) 7) with 0
    by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; rewrite Hm8; reflexivity).
  if_false.
  (* addi a0,s1,280 ; srli ; add s2 ; lbu (shadow byte 0) ; bnez (not taken) *)
  step. step.
  rewrite (unsigned_lit (bv_unsigned a0 + 280)) by lia. rewrite rc_shr3.
  step. step. step.
  nf_pc_false_vm.
  (* ld a1,0(a0) ; beqz a1 *)
  step. step.
  destruct (Z.eq_dec (bv_unsigned name) 0) as [Z0 | NZ].
  - rewrite (rc_eq0w name Z0). cbv iota.
    assert (EN : nmf nb = repeat (Z_to_bv 8 0) 16) by (rewrite (Hnil Z0); reflexivity).
    eapply epi with (wm := a0) (wn := a1) (name := name) (nb := nb).
    all: try eassumption.
    all: try lia.
    all: try (unfold ninv; rewrite EN;
              split; [exact HW1|]; split; [reflexivity|]; split; [exact HB1|]; split; [exact FR|];
              split; [exact HNW|]; split; [exact HBn|]; split; [exact MU|]; split; [exact WM|];
              split; [exact MI2 | exact ST2]).
  - rewrite (rc_neq0w name NZ). cbv iota.
    (* li a3,0 ; not a4,s0 ; li a5,16 *)
    step. step. step.
    pose proof loop as HL. unfold head_ok in HL.
    eapply HL with (k := 16%nat) (i := 0%nat) (wm := a0) (wn := a1) (name := name) (nb := nb).
    all: try eassumption.
    all: try lia.
    all: try (intros; lia).
    all: try (rewrite (zb_lxor_ones (bv_unsigned a1)) by lia; rewrite unsigned_lit by lia; reflexivity).
    all: try (unfold ninv; change (firstn 0 nb ++ repeat (Z_to_bv 8 0) (16 - 0)) with (repeat (Z_to_bv 8 0) 16);
              split; [exact HW1|]; split; [reflexivity|]; split; [exact HB1|]; split; [exact FR|];
              split; [exact HNW|]; split; [exact HBn|]; split; [exact MU|]; split; [exact WM|];
              split; [exact MI2 | exact ST2]).
Qed.
