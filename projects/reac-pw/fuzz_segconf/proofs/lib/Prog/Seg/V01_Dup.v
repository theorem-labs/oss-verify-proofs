(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): the duplicate loop of the
   inline m_declared (fuzz_segconf.c:361-362), 0x13e80 .. 0x13eac (plain binary):
     0x13e80 lw a0,0x10(s7)    mt[k].vid (sign-extended)       0x13e84 sext.w a1,s5     vid
     0x13e88 bne a0,a1 -> 0x13ea0                              0x13e8c addi a1,sp,0x40  &v.parent
     0x13e90 mv a0,s7          mt[k].parent                    0x13e94 jal strcmp (0x1ebf8)
     0x13e98 seqz a0,a0        0x13e9c j 0x13ea4               0x13ea0 mv a0,zero
     0x13ea4 addi s7,s7,0x14   0x13ea8 or s3,a0,s3             0x13eac bne s7,s6 -> 0x13e80 (else 0x13eb0)
   v01_dup (V01_Inv.v's v01_dup_stmt, from strcmp's contract strcmp_c.v): one turn (TURN) reads entry k of T through
   mtab_at (V01DupPure.mt_entry: the parent's bytes and NUL at mt + 20 k, the vid's 4 bytes at mt + 20 k + 16); the
   `lw` sign-extends, so the `bne` falls through exactly when the vid is vid (V01DupPure.sx32_neq); strcmp's result
   r is 0 exactly when the parents are one byte string, which is SegModel.strcmp = 0 (V01DupPure.seqz_bridge, on
   check_segments.v's CsPure.bridge_strcmp). The latch is handled by induction on the entries left (LOOP): s3 is
   acc OR the model's test of every entry seen (V01DupPure.ex_step, ex_last).
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame
  Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec strcmp_c check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import V01_Inv.
Import ListNotations.
Open Scope Z_scope.
Import CsPure.

Module V01DupPure.

Lemma lt_add_S : forall k d n, (k + S d = n)%nat -> (k < n)%nat.
Proof. intros k d n <-. rewrite Nat.add_succ_r. apply Nat.lt_succ_r. apply Nat.le_add_r. Qed.

Lemma len_Z : forall k d n, (k + S d = n)%nat -> Z.of_nat n = Z.of_nat k + Z.of_nat d + 1.
Proof. intros k d n <-. rewrite Nat2Z.inj_add, Nat2Z.inj_succ. unfold Z.succ. ring. Qed.

Lemma skipn_nth : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d H.
  - cbn in H. apply Nat.nlt_0_r in H. destruct H.
  - destruct k as [|k].
    + reflexivity.
    + change (skipn (S k) (x :: l)) with (skipn k l).
      change (nth (S k) (x :: l) d) with (nth k l d).
      change (skipn (S (S k)) (x :: l)) with (skipn (S k) l).
      apply IH. cbn in H. apply Nat.succ_lt_mono. exact H.
Qed.

(* One entry more of the existsb the exit's s3 holds. *)
Lemma ex_step : forall {A} (f : A -> bool) (T : list A) k d acc, (k < length T)%nat ->
  acc || existsb f (skipn k T) = (acc || f (nth k T d)) || existsb f (skipn (S k) T).
Proof.
  intros A f T k d acc H. rewrite (skipn_nth T k d H). cbn [existsb]. apply orb_assoc.
Qed.

(* The last entry. *)
Lemma ex_last : forall {A} (f : A -> bool) (T : list A) k d acc, (k + 1 = length T)%nat ->
  acc || existsb f (skipn k T) = acc || f (nth k T d).
Proof.
  intros A f T k d acc H.
  assert (Hk : (k < length T)%nat) by (rewrite <- H, Nat.add_1_r; apply Nat.lt_succ_diag_r).
  assert (E : skipn (S k) T = []) by (apply skipn_all2; rewrite <- H, Nat.add_1_r; apply le_n).
  rewrite (skipn_nth T k d Hk), E. cbn [existsb]. rewrite orb_false_r. reflexivity.
Qed.

(* Entry k of a table T at mt (struct mvlan, 20 bytes): the parent's bytes sx and NUL at mt + 20 k, the vid vk's
   4 little-endian bytes at mt + 20 k + 16. *)
Lemma mt_entry : forall segs m mt T k, mtab_at segs m mt T -> (k < length T)%nat ->
  exists sx vk, nth k T ([], 0) = (zs sx, vk) /\ bytes_at segs m (mt + 20 * Z.of_nat k) (sx ++ [ZERO]) /\
    ~ In ZERO sx /\ 0 <= vk < 2 ^ 32 /\
    ov_read_bytes segs m (wa (mt + 20 * Z.of_nat k + 16)) 4 = Some (le4 (Z_to_bv 64 vk)).
Proof.
  intros segs m mt T k (bs & B & L & E) Hk.
  destruct (E k Hk) as (Lf & Hc & Hv).
  assert (Bf : bytes_at segs m (mt + Z.of_nat (20 * k)) (fld (20 * k) 20 bs)).
  { unfold fld. apply bytes_at_sub; [exact B|].
    rewrite L, <- Nat.mul_succ_r. apply Nat.mul_le_mono_l. exact Hk. }
  replace (mt + Z.of_nat (20 * k)) with (mt + 20 * Z.of_nat k) in Bf by (rewrite Nat2Z.inj_mul; reflexivity).
  assert (L16 : (16 <= length (fld (20 * k) 20 bs))%nat) by (rewrite Lf; apply Nat.leb_le; reflexivity).
  destruct (cstr_bytes segs m _ _ 16 _ Bf L16 Hc) as (sx & Bx & Nx & Zx).
  exists sx, (snd (nth k T ([], 0))).
  split; [rewrite Zx; destruct (nth k T ([], 0)); reflexivity|].
  split; [exact Bx|]. split; [exact Nx|]. split; [exact (proj1 Hv)|].
  assert (L20 : 16 + 4 <= Z.of_nat (length (fld (20 * k) 20 bs))) by (rewrite Lf; lia).
  exact (cs_rd4 segs m _ _ 16 _ Bf ltac:(lia) L20 Hv).
Qed.

(* `seqz` of strcmp's result is SegModel's strcmp test. *)
Lemma seqz_bridge : forall (r : word) (sx sy : list byte), ~ In ZERO sx -> ~ In ZERO sy ->
  (r = Z_to_bv 64 0 <-> sx = sy) -> (bv_unsigned r <? 1) = (strcmp (zs sx) (zs sy) =? 0).
Proof.
  intros r sx sy Nx Ny Hr.
  pose proof (bridge_strcmp sx sy Nx Ny) as Hb.
  pose proof (bv_unsigned_in_range 64 r) as R.
  destruct (Z.ltb_spec (bv_unsigned r) 1) as [L|L]; symmetry.
  - apply Z.eqb_eq. apply Hb. apply Hr. apply bv_eq. rewrite unsigned_lit by lia. lia.
  - apply Z.eqb_neq. intros E. apply Hb in E. apply Hr in E. subst r.
    rewrite unsigned_lit in L by lia. lia.
Qed.

(* `lw` sign-extends a u32: the word differs from a small vid w unless the u32 is w. *)
Lemma sx32_neq : forall v w, 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 31 -> v <> w ->
  bv_eqb (sx32 (Z_to_bv 64 v)) (Z_to_bv 64 w) = false.
Proof.
  intros v w Hv Hw Hne. unfold bv_eqb. apply Z.eqb_neq. unfold sx32.
  rewrite (unsigned_lit v) by lia. rewrite (unsigned_lit w) by lia. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma lor_b2z : forall a b, Z.lor (Z.b2z a) (Z.b2z b) = Z.b2z (b || a).
Proof. intros [|] [|]; reflexivity. Qed.

(* `sext.w` of a small non-negative value. *)
Lemma swrap_small0 : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 (z + 0) = z.
Proof.
  intros z Hz. rewrite Z.add_0_r. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

End V01DupPure.

Lemma v01_dup : strcmp_contract -> v01_dup_stmt.
Proof.
  intros SC. unfold v01_dup_stmt.
  intros Q m mt spv vid T sy k0 acc0 ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s8 s9 s10 s11 t3 t4 t5 t6
    F fc HT Hk0 Hmt0 Hmtb Hsp0 Hspb By Ny Hvid KX0.
  unfold vst, MVLAN_SIZE in *.
  (* TURN: one entry k, 0x13e80 .. 0x13ea8, to the latch 0x13eac with s3 = acc OR the entry's test. *)
  assert (TURN : forall k acc (ra a0 a1 a2 a3 : word), (k < length T)%nat ->
    (forall b (x1 x10 x11 x12 x13 w3 w7 : word),
       b = acc || ((snd (nth k T ([], 0)) =? vid) && (strcmp (fst (nth k T ([], 0))) (zs sy) =? 0)) ->
       w3 = Z_to_bv 64 (Z.b2z b) -> w7 = Z_to_bv 64 (mt + 20 * Z.of_nat k + 20) ->
       evt rsegs Q (MS (mkR x1 (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 w3 s4
                           (Z_to_bv 64 vid) (Z_to_bv 64 (mt + 20 * Z.of_nat (length T))) w7 s8 s9 s10 s11
                           t3 t4 t5 t6) F (Z_to_bv 64 0x13eac) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
                        (Z_to_bv 64 (Z.b2z acc)) s4 (Z_to_bv 64 vid) (Z_to_bv 64 (mt + 20 * Z.of_nat (length T)))
                        (Z_to_bv 64 (mt + 20 * Z.of_nat k)) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13e80) fc None m (seg_rom rsegs))).
  { intros k acc ra' a0' a1' a2' a3' Hk NEXT.
    destruct (V01DupPure.mt_entry rsegs m mt T k HT Hk) as (sx & vk & Ee & Bx & Nx & Rv & RD).
    rewrite Ee in NEXT. cbn [fst snd] in NEXT.
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hk) as HkZ.
    pose proof (Nat2Z.is_nonneg k) as Hkp.
    (* the join 0x13ea4: a0 = the entry's test *)
    assert (TL : forall x1 x10 x11 x12 x13 : word,
      x10 = Z_to_bv 64 (Z.b2z ((vk =? vid) && (strcmp (zs sx) (zs sy) =? 0))) ->
      evt rsegs Q (MS (mkR x1 (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2
                          (Z_to_bv 64 (Z.b2z acc)) s4 (Z_to_bv 64 vid) (Z_to_bv 64 (mt + 20 * Z.of_nat (length T)))
                          (Z_to_bv 64 (mt + 20 * Z.of_nat k)) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13ea4) fc None m (seg_rom rsegs))).
    { intros x1 x10 x11 x12 x13 E10. subst x10.
      (* 0x13ea4 addi s7,s7,0x14 ; 0x13ea8 or s3,a0,s3 *)
      zstep. zstep.
      eapply (NEXT (acc || ((vk =? vid) && (strcmp (zs sx) (zs sy) =? 0)))).
      - reflexivity.
      - rewrite V01DupPure.lor_b2z. reflexivity.
      - first [reflexivity | f_equal; lia]. }
    (* 0x13e80 lw a0,0x10(s7) ; 0x13e84 sext.w a1,s5 *)
    zstep. zstep.
    rewrite (V01DupPure.swrap_small0 vid) by lia.
    destruct (Z.eq_dec vk vid) as [Ev|Nv].
    - subst vk. rewrite (sx32_small vid) by lia.
      (* 0x13e88 bne a0,a1: equal, falls through *)
      zstep.
      let K := fresh "K" in if_cases K; [ exfalso; rewrite bv_eqb_refl in K; discriminate K | clear K ].
      (* 0x13e8c addi a1,sp,0x40 ; 0x13e90 mv a0,s7 ; 0x13e94 jal strcmp *)
      zstep. zstep. zstep.
      eapply evt_cut.
      { eapply SC with (sx := sx) (sy := sy).
        - eapply bytes_at_eq; [exact Bx | rewrite ?unsigned_lit by lia; lia].
        - exact Nx.
        - eapply bytes_at_eq; [exact By | rewrite ?unsigned_lit by lia; lia].
        - exact Ny. }
      intros ms' (r & y11 & y12 & y13 & -> & Hr).
      rewrite ret_pc_even by (try lia; reflexivity).
      (* 0x13e98 seqz a0,a0 ; 0x13e9c j 0x13ea4 *)
      zstep. zstep.
      eapply TL.
      rewrite Z.eqb_refl, andb_true_l, (V01DupPure.seqz_bridge r sx sy Nx Ny Hr). reflexivity.
    - (* 0x13e88 bne a0,a1: taken *)
      zstep.
      let K := fresh "K" in if_cases K;
        [ clear K
        | exfalso; rewrite (V01DupPure.sx32_neq vk vid) in K by lia; discriminate K ].
      (* 0x13ea0 mv a0,zero *)
      zstep.
      eapply TL.
      rewrite (proj2 (Z.eqb_neq vk vid) Nv). reflexivity. }
  (* LOOP: the entries k .. k + d of T left; the latch 0x13eac. *)
  assert (LOOP : forall d k acc (ra a0 a1 a2 a3 : word), (k + S d = length T)%nat ->
    (forall ra' a0' a1' a2' a3' s7' w3,
       w3 = Z_to_bv 64 (Z.b2z (acc || existsb (fun e => (snd e =? vid) && (strcmp (fst e) (zs sy) =? 0))
                                            (skipn k T))) ->
       evt rsegs Q (MS (mkR ra' (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 w3 s4
                           (Z_to_bv 64 vid) (Z_to_bv 64 (mt + 20 * Z.of_nat (length T))) s7' s8 s9 s10 s11
                           t3 t4 t5 t6) F (Z_to_bv 64 0x13eb0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
                        (Z_to_bv 64 (Z.b2z acc)) s4 (Z_to_bv 64 vid) (Z_to_bv 64 (mt + 20 * Z.of_nat (length T)))
                        (Z_to_bv 64 (mt + 20 * Z.of_nat k)) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x13e80) fc None m (seg_rom rsegs))).
  { induction d as [|d IH]; intros k acc ra' a0' a1' a2' a3' Ed KX.
    - (* k is the last entry: s7 + 20 = s6, the latch falls through to 0x13eb0 *)
      pose proof (V01DupPure.len_Z _ _ _ Ed) as EZ. change (Z.of_nat 0) with 0 in EZ.
      apply (TURN k acc ra' a0' a1' a2' a3' (V01DupPure.lt_add_S _ _ _ Ed)).
      intros b x1 x10 x11 x12 x13 w3 w7 Eb E3 E7. subst w3 w7.
      zstep. cs_ntk.
      eapply KX. f_equal. f_equal. rewrite Eb.
      rewrite (V01DupPure.ex_last _ T k ([], 0) acc Ed). reflexivity.
    - (* entries after k: the latch goes back to 0x13e80 with k + 1 *)
      pose proof (V01DupPure.len_Z _ _ _ Ed) as EZ. rewrite Nat2Z.inj_succ in EZ. unfold Z.succ in EZ.
      pose proof (Nat2Z.is_nonneg d) as Hdp.
      apply (TURN k acc ra' a0' a1' a2' a3' (V01DupPure.lt_add_S _ _ _ Ed)).
      intros b x1 x10 x11 x12 x13 w3 w7 Eb E3 E7. subst w3 w7.
      zstep. cs_tkn.
      replace (Z_to_bv 64 (mt + 20 * Z.of_nat k + 20)) with (Z_to_bv 64 (mt + 20 * Z.of_nat (S k)))
        by (f_equal; rewrite Nat2Z.inj_succ; unfold Z.succ; lia).
      eapply (IH (S k) b).
      + first [ rewrite Nat.add_succ_comm; exact Ed | rewrite <- Nat.add_succ_comm; exact Ed ].
      + intros ra'' a0'' a1'' a2'' a3'' s7'' w3 E. apply KX. rewrite E. f_equal. f_equal. rewrite Eb.
        rewrite (V01DupPure.ex_step _ T k ([], 0) acc (V01DupPure.lt_add_S _ _ _ Ed)). reflexivity. }
  assert (E0 : (k0 + S (length T - S k0) = length T)%nat).
  { rewrite <- Nat.sub_succ_l by exact Hk0. rewrite Nat.sub_succ. rewrite Nat.add_comm.
    apply Nat.sub_add. apply Nat.lt_le_incl. exact Hk0. }
  change (b2z acc0) with (Z.b2z acc0).
  apply (LOOP (length T - S k0)%nat k0 acc0 ra a0 a1 a2 a3 E0).
  intros ra' a0' a1' a2' a3' s7' w3 ->. exact (KX0 ra' a0' a1' a2' a3' s7').
Qed.
