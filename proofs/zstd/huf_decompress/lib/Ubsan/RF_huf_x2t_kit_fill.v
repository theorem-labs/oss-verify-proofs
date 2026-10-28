From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model
  RF_huf_x2t_model RF_huf_x2t_c1.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PHUF_FILL_X2 : Z := 0x1a0f0.
Definition X2FILL_STACK : Z := 48.
Local Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map,
  ?omerge_length, ?ox2_length, ?upd_bytes_length in *.

Definition xf_inv (m m1 : fmem) (FA lo : Z) (FC : list cell) (DT SY : Z) (js jt : list byte) (sorted : list (option Z))
    (ncells : nat) (dt : list (option deltX2)) : Prop :=
  u8arr usegs m1 (DT + 4) (ox2 jt dt) /\ length dt = ncells /\ bytes_at usegs m1 SY (omerge js sorted)
  /\ rw_cells usegs m1 FA FC /\ stk usegs m1 lo FA
  /\ munch [(FA, FA + 48); (DT + 4, DT + 4 + 4 * Z.of_nat ncells)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

Lemma sy_rd : forall m SY js sorted s v, bytes_at usegs m SY (omerge js sorted) -> length js = length sorted ->
  length sorted = 256%nat -> 0 <= s < 256 -> nth (Z.to_nat s) sorted None = Some v ->
  ov_read_bytes usegs m (Z_to_bv 64 (SY + s)) 1 = Some [Z_to_bv 8 v].
Proof.
  intros m SY js sorted s v B LJ LS Hs N.
  pose proof (omerge_nth sorted js (Z.to_nat s) v LJ N) as E.
  pose proof (bytes_at_read usegs m SY (omerge js sorted) s 1 B ltac:(lia)) as R.
  rewrite omerge_length in R. specialize (R ltac:(lia)).
  unfold wa in R. rewrite R. f_equal.
  clear - E. revert E. generalize (omerge js sorted). generalize (Z.to_nat s). clear.
  induction n as [|n IH]; intros l E; destruct l as [|b l]; cbn in *; try discriminate.
  - injection E as ->. reflexivity.
  - apply IH. exact E.
Qed.

Lemma oload_Ok : forall l i v, oload l i = Ok v -> 0 <= i < Z.of_nat (length l) /\ nth (Z.to_nat i) l None = Some v.
Proof.
  intros l i v H. unfold oload, FseNCount.Zlength in H.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (Z.of_nat (length l))); cbn in H; try discriminate.
  destruct (nth (Z.to_nat i) l None) eqn:N; inversion H; subst; repeat split; try lia; assumption.
Qed.

Lemma ffw_iter : forall f dt base b e nb tl bs lvl sorted r, b <> e -> 0 <= tl - nb < 32 ->
  fill_for_weight (S f) dt base b e nb tl bs lvl sorted = Ok r ->
  exists sym dt', 0 <= b < Z.of_nat (length sorted) /\ nth (Z.to_nat b) sorted None = Some sym /\
    store_run (Z.to_nat (2 ^ (tl - nb))) dt base (build_x2 sym nb bs lvl) = Ok dt' /\
    fill_for_weight f dt' (base + 2 ^ (tl - nb)) (b + 1) e nb tl bs lvl sorted = Ok r.
Proof.
  intros f dt base b e nb tl bs lvl sorted r NE RG HF.
  rewrite ffw_step in HF by exact NE.
  rewrite land31, shl32_1 in HF by lia. cbn [bind] in HF.
  destruct (oload sorted b) as [sym| | |] eqn:OL; cbn [bind] in HF; try discriminate.
  apply oload_Ok in OL. destruct OL as (B & N).
  destruct (store_run (Z.to_nat (2 ^ (tl - nb))) dt base (build_x2 sym nb bs lvl)) as [dt'| | |] eqn:SR;
    cbn [bind] in HF; try discriminate.
  exists sym, dt'. repeat split; auto; lia.
Qed.

Lemma lor_b3 : forall a b c, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c ->
  Z.lor (b * 256) (a + c * 65536) = a + b * 256 + c * 65536.
Proof.
  intros a b c Ha Hb Hc.
  assert (E1 : a + c * 65536 = Z.lor a (Z.shiftl (c * 256) 8)) by (rewrite lor_shiftl8_add by lia; lia).
  assert (E2 : b * 256 = Z.shiftl b 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (E3 : Z.lor b (Z.shiftl c 8) = b + 256 * c) by (apply lor_shiftl8_add; lia).
  assert (E4 : c * 256 = Z.shiftl c 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite E1. rewrite E2 at 1.
  rewrite (Z.lor_comm (Z.shiftl b 8)), <- Z.lor_assoc, <- Z.shiftl_lor.
  rewrite E4, (Z.lor_comm (Z.shiftl c 8) b), E3.
  rewrite lor_shiftl8_add by lia. lia.
Qed.

Section F1A.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (DT SY e nb tl bs FA lo : Z) (FC : list cell) (sorted : list (option Z)) (js jt : list byte)
    (ncells : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4.
  Hypothesis HSY : 0 < SY /\ SY + 256 <= 2^47.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HTL : tl - nb = 0.
  Hypothesis HE : e <= 256.
  Hypothesis HBS : 0 <= bs < 256.
  Variables (j : list byte).
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ SY + 256 <= lo /\ lo <= FA /\ FA + 48 <= 2^47.
  Notation INV m1 dt := (xf_inv m m1 FA lo [CB 8 j; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8] DT SY js jt sorted ncells dt).
  Notation D := (nb * 65536 + 16777216).

  Lemma f1a_loop : forall f s dt u m1 r (x5 : word),
    fill_for_weight f dt u s e nb tl bs 1 sorted = Ok r ->
    Z.of_nat f = e - s + 1 -> 0 <= s < e -> 0 <= u -> INV m1 dt ->
    (forall m2 dt' (y5 y10 y11 y17 : word),
       r = (dt', u + (e - s)) -> INV m2 dt' ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 (SY + e)) (Z_to_bv 64 D) (Z_to_bv 64 5)
                               (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 (-1)) y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                               x28 x29 x30 x31)
                          F (Z_to_bv 64 0x1a4e0) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * u)) (Z_to_bv 64 (SY + s))
                            (Z_to_bv 64 (SY + e)) (Z_to_bv 64 D) (Z_to_bv 64 5) (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 (-1))
                            (Z_to_bv 64 (DT + 4 + 4 * u)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1a370) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH]; intros s dt u m1 r x5 HF Hf Hs Hu INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
    destruct (ffw_iter f dt u s e nb tl bs 1 sorted r ltac:(lia) ltac:(lia) HF) as (sym & dt1 & HB & NS & SR & HF1).
    rewrite HTL in SR, HF1. change (Z.to_nat (2 ^ 0)) with 1%nat in SR. cbn [store_run bind] in SR.
    destruct (ostore2 dt u (build_x2 sym nb bs 1)) as [dt2| | |] eqn:OS; cbn [bind] in SR; try discriminate.
    injection SR as <-.
    apply ostore2_Ok in OS. destruct OS as (HU & ->).
    pose proof (HSYR _ _ NS) as SYM.
    destruct (build_x2_fields sym nb bs 1 SYM ltac:(lia) ltac:(lia) ltac:(left; reflexivity)) as (CS & CN & CL).
    rewrite Z.eqb_refl in CS.
    assert (UN : u < Z.of_nat ncells) by lia.
    zstep. zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
    pose proof (sy_rd m1 SY js sorted s sym SYB HJS HLS ltac:(lia) NS) as RD.
    zstep.
    set (c := build_x2 sym nb bs 1) in *.
    assert (L2H : le2 (Z_to_bv 64 (D ≫ 16)) = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
      by (rewrite CN, CL; apply v1_hi; lia).
    xh (DT + 4) ARR (4 * u + 2).
    zstep.
    assert (L2L : le2 (Z_to_bv 64 (Z.lor D (bv_unsigned (Z_to_bv 8 sym))))
                  = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
      by (rewrite (byte_lit sym SYM), CS; apply v1_lo; lia).
    xh (DT + 4) ARR (4 * u).
    replace (Z.to_nat (4 * u)) with (4 * Z.to_nat u)%nat in ARR by lia.
    replace (Z.to_nat (4 * u + 2)) with (4 * Z.to_nat u + 2)%nat in ARR by lia.
    rewrite ox2_store_rev in ARR by (rewrite ?oset2_length by lia; lia).
    zstep. if_cases U2; zify_cond U2; [exfalso; lia|].
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (INV2 : INV mc (oset2 dt (Z.to_nat u) c))
        by (unfold xf_inv; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
            first [rewrite oset2_length by lia; exact LDT | assumption]) end.
    replace (Z.of_nat (length dt)) with (Z.of_nat ncells) in HU by (rewrite LDT; reflexivity).
    rewrite Z.pow_0_r in HF1.
    zstep. if_cases K; zify_cond K.
    - replace (DT + 4 + 4 * u + 4) with (DT + 4 + 4 * (u + 1)) by lia.
      replace (SY + s + 1) with (SY + (s + 1)) by lia.
      eapply (IH (s + 1) _ (u + 1) _ r); [exact HF1 | lia | lia | lia | exact INV2 |].
      intros m2 dt' y5 y10 y11 y17 HR INV3. eapply CONT; [rewrite HR; f_equal; lia | exact INV3].
    - zstep.
      destruct f as [|f]; [lia|].
      replace (s + 1) with e in HF1 by lia. rewrite ffw_stop in HF1. injection HF1 as <-.
      eapply CONT; [f_equal; lia | exact INV2].
  Qed.
End F1A.

Section F1B.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x6 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (DT SY e nb tl bs FA lo : Z) (FC : list cell) (sorted : list (option Z)) (js jt : list byte)
    (ncells : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4.
  Hypothesis HSY : 0 < SY /\ SY + 256 <= 2^47.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HTL : tl - nb = 0.
  Hypothesis HE : e <= 256.
  Hypothesis HBS : 0 <= bs < 256.
  Variables (j : list byte).
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ SY + 256 <= lo /\ lo <= FA /\ FA + 48 <= 2^47.
  Notation INV m1 dt := (xf_inv m m1 FA lo [CB 8 j; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8] DT SY js jt sorted ncells dt).
  Notation D := (Z.lor bs (nb * 65536 + 33554432)).

  Lemma f1b_loop : forall f s dt u m1 r (x5 : word),
    fill_for_weight f dt u s e nb tl bs 2 sorted = Ok r ->
    Z.of_nat f = e - s + 1 -> 0 <= s < e -> 0 <= u -> INV m1 dt ->
    (forall m2 dt' (y5 y10 y11 y17 : word),
       r = (dt', u + (e - s)) -> INV m2 dt' ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 (SY + e)) (Z_to_bv 64 D) (Z_to_bv 64 4)
                               (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 (-1)) y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                               x28 x29 x30 x31)
                          F (Z_to_bv 64 0x1a4e0) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * u)) (Z_to_bv 64 (SY + s))
                            (Z_to_bv 64 (SY + e)) (Z_to_bv 64 D) (Z_to_bv 64 4) (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 (-1))
                            (Z_to_bv 64 (DT + 4 + 4 * u)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1a43c) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH]; intros s dt u m1 r x5 HF Hf Hs Hu INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
    destruct (ffw_iter f dt u s e nb tl bs 2 sorted r ltac:(lia) ltac:(lia) HF) as (sym & dt1 & HB & NS & SR & HF1).
    rewrite HTL in SR, HF1. change (Z.to_nat (2 ^ 0)) with 1%nat in SR. cbn [store_run bind] in SR.
    destruct (ostore2 dt u (build_x2 sym nb bs 2)) as [dt2| | |] eqn:OS; cbn [bind] in SR; try discriminate.
    injection SR as <-.
    apply ostore2_Ok in OS. destruct OS as (HU & ->).
    pose proof (HSYR _ _ NS) as SYM.
    destruct (build_x2_fields sym nb bs 2 SYM ltac:(lia) ltac:(lia) ltac:(right; reflexivity)) as (CS & CN & CL).
    change (2 =? 1) with false in CS. cbv iota in CS.
    assert (UN : u < Z.of_nat ncells) by lia.
    pose proof (sy_rd m1 SY js sorted s sym SYB HJS HLS ltac:(lia) NS) as RD.
    zstep. zstep. if_cases U1; zify_cond U1; [exfalso; lia|].
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => fail
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a ?v) _) => fail
      | |- _ => zstep end).
    cbv beta. rewrite (byte_lit sym SYM).
    set (c := build_x2 sym nb bs 2) in *.
    assert (DV : D = bs + nb * 65536 + 33554432).
    { replace (nb * 65536 + 33554432) with (Z.shiftl (nb * 256 + 131072) 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      rewrite lor_shiftl8_add by lia. lia. }
    assert (L2H : le2 (Z_to_bv 64 (D ≫ 16)) = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)]).
    { rewrite CN, CL. apply le2_hi; try lia. rewrite DV.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
      replace ((bs + nb * 65536 + 33554432) / 65536) with (nb + 512)
        by (apply Z.div_unique with (r := bs); lia).
      rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. lia. }
    xh (DT + 4) ARR (4 * u + 2).
    zstep. zstep.
    assert (VV : Z.lor (sym ≪ 8 mod 18446744073709551616) D = bs + sym * 256 + (nb + 512) * 65536).
    { rewrite DV. replace (bs + nb * 65536 + 33554432) with (bs + (nb + 512) * 65536) by lia.
      rewrite Z.mod_small by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. apply lor_b3; lia. }
    assert (L2L : le2 (Z_to_bv 64 (Z.lor (sym ≪ 8 mod 18446744073709551616) D))
                  = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)]).
    { rewrite VV. apply le2_of_mod16. rewrite unsigned_lit by lia.
      rewrite Z_mod_plus_full, Z.mod_small by lia. rewrite CS. reflexivity. }
    xh (DT + 4) ARR (4 * u).
    replace (Z.to_nat (4 * u)) with (4 * Z.to_nat u)%nat in ARR by lia.
    replace (Z.to_nat (4 * u + 2)) with (4 * Z.to_nat u + 2)%nat in ARR by lia.
    rewrite ox2_store_rev in ARR by (rewrite ?oset2_length by lia; lia).
    zstep. if_cases U2; zify_cond U2; [exfalso; lia|].
    repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => fail
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a43c) _ _ _ _) => fail
      | |- _ => zstep end).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (INV2 : INV mc (oset2 dt (Z.to_nat u) c))
        by (unfold xf_inv; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
            first [rewrite oset2_length by lia; exact LDT | assumption]) end.
    replace (Z.of_nat (length dt)) with (Z.of_nat ncells) in HU by (rewrite LDT; reflexivity).
    rewrite Z.pow_0_r in HF1.
    lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases K; zify_cond K
      | |- _ => zstep; if_cases K; zify_cond K end.
    - replace (DT + 4 + 4 * u + 4) with (DT + 4 + 4 * (u + 1)) by lia.
      replace (SY + s + 1) with (SY + (s + 1)) by lia.
      eapply (IH (s + 1) _ (u + 1) _ r); [exact HF1 | lia | lia | lia | exact INV2 |].
      intros m2 dt' y5 y10 y11 y17 HR INV3. eapply CONT; [rewrite HR; f_equal; lia | exact INV3].
    - zstep.
      destruct f as [|f]; [lia|].
      replace (s + 1) with e in HF1 by lia. rewrite ffw_stop in HF1. injection HF1 as <-.
      eapply CONT; [f_equal; lia | exact INV2].
  Qed.

End F1B.

Section F2.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word).
  Variables (m : fmem) (DT SY e nb tl bs lvl LV FA lo : Z) (FC : list cell) (sorted : list (option Z))
    (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4.
  Hypothesis HSY : 0 < SY /\ SY + 256 <= 2^47.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HTL : tl - nb = 1.
  Hypothesis HE : e <= 256.
  Hypothesis HBS : 0 <= bs < 256.
  Hypothesis HLV : (lvl = 1 /\ LV = 16777216) \/ (lvl = 2 /\ LV = 33554432).
  Variables (j : list byte).
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ SY + 256 <= lo /\ lo <= FA /\ FA + 48 <= 2^47.
  Notation INV m1 dt := (xf_inv m m1 FA lo [CB 8 j; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8] DT SY js jt sorted ncells dt).
  Notation D := (nb * 65536 + LV).

  Lemma f2_loop : forall f s dt u m1 r (x28 x29 : word),
    fill_for_weight f dt u s e nb tl bs lvl sorted = Ok r ->
    Z.of_nat f = e - s + 1 -> 0 <= s < e -> 0 <= u -> INV m1 dt ->
    (forall m2 dt' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       r = (dt', u + 2 * (e - s)) -> INV m2 dt' ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24
                               x25 x26 x27 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x1a4e0) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp (Z_to_bv 64 D) (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 (-9)) x8 x9
                            (Z_to_bv 64 (DT + 4 + 4 * u)) (Z_to_bv 64 (SY + s)) (Z_to_bv 64 (SY + e)) (Z_to_bv 64 1)
                            (Z_to_bv 64 (-5)) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 (-1)) x18 x19 x20 x21 x22 x23
                            x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1a14c) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH]; intros s dt u m1 r x28 x29 HF Hf Hs Hu INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
    destruct (ffw_iter f dt u s e nb tl bs lvl sorted r ltac:(lia) ltac:(lia) HF) as (sym & dt1 & HB & NS & SR & HF1).
    rewrite HTL in SR, HF1. change (Z.to_nat (2 ^ 1)) with 2%nat in SR. cbn [store_run bind] in SR.
    rewrite Z.pow_1_r in HF1.
    destruct (ostore2 dt u (build_x2 sym nb bs lvl)) as [dt2| | |] eqn:OS; cbn [bind] in SR; try discriminate.
    destruct (ostore2 dt2 (u + 1) (build_x2 sym nb bs lvl)) as [dt3| | |] eqn:OS2; cbn [bind] in SR; try discriminate.
    assert (dt1 = dt3) by congruence; subst dt1; clear SR.
    apply ostore2_Ok in OS. destruct OS as (HU & ->).
    apply ostore2_Ok in OS2. destruct OS2 as (HU2 & ->).
    pose proof (HSYR _ _ NS) as SYM.
    destruct (build_x2_fields sym nb bs lvl SYM ltac:(lia) ltac:(lia) ltac:(lia)) as (CS & CN & CL).
    pose proof (sy_rd m1 SY js sorted s sym SYB HJS HLS ltac:(lia) NS) as RD.
    assert (UN : u + 1 < Z.of_nat ncells) by (rewrite oset2_length in HU2 by lia; lia).
    set (c := build_x2 sym nb bs lvl) in *.
    assert (L2H : le2 (Z_to_bv 64 (D ≫ 16)) = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)]).
    { rewrite CN, CL. apply le2_hi; try lia. rewrite Z.shiftr_div_pow2 by lia. rewrite unsigned_lit by lia. lia. }
    zstep. zstep. if_cases K; zify_cond K;
      [ replace (lvl =? 1) with true in CS by (symmetry; apply Z.eqb_eq; lia);
        assert (VV : Z.lor (bv_unsigned (Z_to_bv 8 sym)) D = D + x2_seq c)
          by (rewrite (byte_lit sym SYM), CS, Z.lor_comm; apply lor_add with (k := 16); lia);
        assert (L2L : le2 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D))
                      = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (apply le2_of_mod16; rewrite VV, unsigned_lit by lia; lia);
        assert (L2H2 : le2 (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≫ 16))
                       = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite VV, CN, CL; apply le2_hi; try lia;
              rewrite Z.shiftr_div_pow2 by lia; rewrite unsigned_lit by lia; lia)
      | replace (lvl =? 1) with false in CS by (symmetry; apply Z.eqb_neq; lia);
        assert (VV : Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D = D + x2_seq c)
          by (rewrite (byte_lit sym SYM), CS, Z.shiftl_mul_pow2 by lia;
              rewrite (Z.mod_small (sym * 2 ^ 8)) by lia; rewrite (lor_add (sym * 2 ^ 8) bs 8) by lia;
              rewrite Z.lor_comm, (lor_add D (sym * 2 ^ 8 + bs) 16) by lia; lia);
        assert (L2L : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D))
                      = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (apply le2_of_mod16; rewrite VV, unsigned_lit by lia; lia);
        assert (L2H2 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D
                                         ≫ 16))
                       = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite VV, CN, CL; apply le2_hi; try lia;
              rewrite Z.shiftr_div_pow2 by lia; rewrite unsigned_lit by lia; lia) ].
    all: repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
          let b := eval vm_compute in (existsb (Z.eqb pc) [0x1a14c; 0x1a4e0]) in
          lazymatch b with
          | true => fail
          | false => first [ zstep | xcell (DT + 4) ARR u | xcell (DT + 4) ARR (u + 1) ] end
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
      end).
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (INV2 : INV mc (oset2 (oset2 dt (Z.to_nat u) c) (Z.to_nat (u + 1)) c))
        by (unfold xf_inv; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
            first [ rewrite oset2_length by (rewrite oset2_length by lia; lia);
                    rewrite oset2_length by lia; exact LDT
                  | assumption ]) end.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a14c) _ _ _ _) =>
          replace (DT + 4 + 4 * u + 8) with (DT + 4 + 4 * (u + 2)) by lia;
          replace (SY + s + 1) with (SY + (s + 1)) by lia;
          eapply (IH (s + 1) _ (u + 2) _ r); [exact HF1 | lia | lia | lia | exact INV2 |];
          intros m2 dt' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HR INV3;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV3]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a4e0) _ _ _ _) =>
          destruct f as [|f]; [lia|];
          replace (s + 1) with e in HF1 by lia; rewrite ffw_stop in HF1;
          lazymatch type of HF1 with Ok ?v = Ok ?rr => assert (HR : rr = v) by congruence end;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV2]
      end.
  Qed.
End F2.

Lemma land1_even : forall DT start, DT mod 2 = 0 ->
  Z_to_bv 64 (Z.land ((DT + 4 + 4 * start) mod 18446744073709551616) 1) = Z_to_bv 64 0.
Proof.
  intros DT start H. f_equal.
  pose proof (Z.land_ones ((DT + 4 + 4 * start) mod 18446744073709551616) 1 ltac:(lia)) as L.
  change (Z.ones 1) with 1 in L. rewrite L, Z.pow_1_r. lia.
Qed.

Ltac olen := repeat (rewrite oset2_length by lia); lia.

Section F4A.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word).
  Variables (m : fmem) (DT SY e nb tl bs FA lo : Z) (FC : list cell) (sorted : list (option Z))
    (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4.
  Hypothesis HSY : 0 < SY /\ SY + 256 <= 2^47.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HTL : tl - nb = 2.
  Hypothesis HE : e <= 256.
  Hypothesis HBS : 0 <= bs < 256.
  Variables (j : list byte).
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ SY + 256 <= lo /\ lo <= FA /\ FA + 48 <= 2^47.
  Notation INV m1 dt := (xf_inv m m1 FA lo [CB 8 j; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8] DT SY js jt sorted ncells dt).
  Notation D := (nb * 65536 + 16777216).

  Lemma f4a_loop : forall f s dt u m1 r (x5 x6 x7 x28 : word),
    fill_for_weight f dt u s e nb tl bs 1 sorted = Ok r ->
    Z.of_nat f = e - s + 1 -> 0 <= s < e -> 0 <= u -> INV m1 dt ->
    (forall m2 dt' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       r = (dt', u + 4 * (e - s)) -> INV m2 dt' ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24
                               x25 x26 x27 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x1a4e0) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9
                            (Z_to_bv 64 (DT + 4 + 4 * u)) (Z_to_bv 64 (SY + s)) (Z_to_bv 64 (SY + e)) (Z_to_bv 64 0)
                            (Z_to_bv 64 (-9)) (Z_to_bv 64 (-1)) (Z_to_bv 64 D) (Z_to_bv 64 (-17)) x18 x19 x20 x21 x22 x23
                            x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1a3cc) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH]; intros s dt u m1 r x5 x6 x7 x28 HF Hf Hs Hu INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
    destruct (ffw_iter f dt u s e nb tl bs 1 sorted r ltac:(lia) ltac:(lia) HF) as (sym & dt1 & HB & NS & SR & HF1).
    rewrite HTL in SR, HF1. change (Z.to_nat (2 ^ 2)) with 4%nat in SR.
    pose proof (store_run_Ok _ _ _ _ _ SR ltac:(lia)) as [_ BR]. specialize (BR ltac:(lia)).
    cbn [store_run bind] in SR.
    change (2 ^ 2) with 4 in HF1.
    set (c := build_x2 sym nb bs 1) in *.
    destruct (ostore2 dt u c) as [d1| | |] eqn:O1; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d1 (u + 1) c) as [d2| | |] eqn:O2; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d2 (u + 1 + 1) c) as [d3| | |] eqn:O3; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d3 (u + 1 + 1 + 1) c) as [d4| | |] eqn:O4; cbn [bind] in SR; try discriminate.
    assert (dt1 = d4) by congruence; subst dt1; clear SR.
    replace (u + 1 + 1 + 1) with (u + 3) in O4 by lia. replace (u + 1 + 1) with (u + 2) in O3 by lia.
    apply ostore2_Ok in O1. destruct O1 as (HU1 & ->).
    apply ostore2_Ok in O2. destruct O2 as (HU2 & ->).
    apply ostore2_Ok in O3. destruct O3 as (HU3 & ->).
    apply ostore2_Ok in O4. destruct O4 as (HU4 & ->).
    pose proof (HSYR _ _ NS) as SYM.
    destruct (build_x2_fields sym nb bs 1 SYM ltac:(lia) ltac:(lia) ltac:(left; reflexivity)) as (CS & CN & CL).
    rewrite Z.eqb_refl in CS. fold c in CS, CN, CL.
    pose proof (sy_rd m1 SY js sorted s sym SYB HJS HLS ltac:(lia) NS) as RD.
    assert (UN : u + 3 < Z.of_nat ncells) by lia.
    assert (VDE : Z.lor D (bv_unsigned (Z_to_bv 8 sym)) = D + x2_seq c)
      by (rewrite (byte_lit sym SYM), CS; apply lor_add with (k := 16); lia).
    assert (H0 : le2 (Z_to_bv 64 (Z.lor (Z.lor D (bv_unsigned (Z_to_bv 8 sym)) ≪ 32 mod 18446744073709551616)
                                         (Z.lor D (bv_unsigned (Z_to_bv 8 sym)))))
                 = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
      by (apply le2_of_mod16; rewrite rep_h0 by (rewrite VDE; lia); rewrite VDE; lia).
    assert (H1 : le2 (Z_to_bv 64 (Z.lor (Z.lor D (bv_unsigned (Z_to_bv 8 sym)) ≪ 32 mod 18446744073709551616)
                                         (Z.lor D (bv_unsigned (Z_to_bv 8 sym))) ≫ 16))
                 = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
      by (rewrite CN, CL; apply le2_hi; try lia; rewrite rep_h1 by (rewrite VDE; lia); rewrite VDE; lia).
    assert (H2 : le2 (Z_to_bv 64 (Z.lor (Z.lor D (bv_unsigned (Z_to_bv 8 sym)) ≪ 32 mod 18446744073709551616)
                                         (Z.lor D (bv_unsigned (Z_to_bv 8 sym))) ≫ 32))
                 = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
      by (apply le2_of_mod16; rewrite rep_h2 by (rewrite VDE; lia); rewrite VDE; lia).
    assert (H3 : le2 (Z_to_bv 64 (Z.lor (Z.lor D (bv_unsigned (Z_to_bv 8 sym)) ≪ 32 mod 18446744073709551616)
                                         (Z.lor D (bv_unsigned (Z_to_bv 8 sym))) ≫ 48))
                 = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
      by (rewrite CN, CL; apply le2_hi; try lia; rewrite rep_h3 by (rewrite VDE; lia); rewrite VDE; lia).
    zstep.
    all: repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
          let b := eval vm_compute in (existsb (Z.eqb pc) [0x1a3cc; 0x1a4e0]) in
          lazymatch b with
          | true => fail
          | false => first [ zstep | xcell (DT + 4) ARR u | xcell (DT + 4) ARR (u + 1)
                           | xcell (DT + 4) ARR (u + 2) | xcell (DT + 4) ARR (u + 3) ] end
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
      end).
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (INV2 : INV mc (oset2 (oset2 (oset2 (oset2 dt (Z.to_nat u) c) (Z.to_nat (u + 1)) c) (Z.to_nat (u + 2)) c)
                               (Z.to_nat (u + 3)) c))
        by (unfold xf_inv; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
            first [ assumption | olen ]) end.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a3cc) _ _ _ _) =>
          replace (DT + 4 + 4 * u + 16) with (DT + 4 + 4 * (u + 4)) by lia;
          replace (SY + s + 1) with (SY + (s + 1)) by lia;
          eapply (IH (s + 1) _ (u + 4) _ r); [exact HF1 | lia | lia | lia | exact INV2 |];
          intros m2 dt' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HR INV3;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV3]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a4e0) _ _ _ _) =>
          destruct f as [|f]; [lia|];
          replace (s + 1) with e in HF1 by lia; rewrite ffw_stop in HF1;
          lazymatch type of HF1 with Ok ?v = Ok ?rr => assert (HR : rr = v) by congruence end;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV2]
      end.
  Qed.
End F4A.

Section F4B.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word).
  Variables (m : fmem) (DT SY e nb tl bs FA lo : Z) (FC : list cell) (sorted : list (option Z))
    (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4.
  Hypothesis HSY : 0 < SY /\ SY + 256 <= 2^47.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HTL : tl - nb = 2.
  Hypothesis HE : e <= 256.
  Hypothesis HBS : 0 <= bs < 256.
  Variables (j : list byte).
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ SY + 256 <= lo /\ lo <= FA /\ FA + 48 <= 2^47.
  Notation INV m1 dt := (xf_inv m m1 FA lo [CB 8 j; C8 x20; C8 x19; C8 x18; C8 x9; C8 x8] DT SY js jt sorted ncells dt).
  Notation D := (Z.lor bs (nb * 65536 + 33554432)).

  Lemma f4b_loop : forall f s dt u m1 r (x5 x6 x7 x28 : word),
    fill_for_weight f dt u s e nb tl bs 2 sorted = Ok r ->
    Z.of_nat f = e - s + 1 -> 0 <= s < e -> 0 <= u -> INV m1 dt ->
    (forall m2 dt' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       r = (dt', u + 4 * (e - s)) -> INV m2 dt' ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24
                               x25 x26 x27 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x1a4e0) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9
                            (Z_to_bv 64 (DT + 4 + 4 * u)) (Z_to_bv 64 (SY + s)) (Z_to_bv 64 (SY + e)) (Z_to_bv 64 0)
                            (Z_to_bv 64 (-9)) (Z_to_bv 64 (-1)) (Z_to_bv 64 D) (Z_to_bv 64 (-17)) x18 x19 x20 x21 x22 x23
                            x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x1a484) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH]; intros s dt u m1 r x5 x6 x7 x28 HF Hf Hs Hu INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
    destruct (ffw_iter f dt u s e nb tl bs 2 sorted r ltac:(lia) ltac:(lia) HF) as (sym & dt1 & HB & NS & SR & HF1).
    rewrite HTL in SR, HF1. change (Z.to_nat (2 ^ 2)) with 4%nat in SR.
    pose proof (store_run_Ok _ _ _ _ _ SR ltac:(lia)) as [_ BR]. specialize (BR ltac:(lia)).
    cbn [store_run bind] in SR.
    change (2 ^ 2) with 4 in HF1.
    set (c := build_x2 sym nb bs 2) in *.
    destruct (ostore2 dt u c) as [d1| | |] eqn:O1; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d1 (u + 1) c) as [d2| | |] eqn:O2; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d2 (u + 1 + 1) c) as [d3| | |] eqn:O3; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d3 (u + 1 + 1 + 1) c) as [d4| | |] eqn:O4; cbn [bind] in SR; try discriminate.
    assert (dt1 = d4) by congruence; subst dt1; clear SR.
    replace (u + 1 + 1 + 1) with (u + 3) in O4 by lia. replace (u + 1 + 1) with (u + 2) in O3 by lia.
    apply ostore2_Ok in O1. destruct O1 as (HU1 & ->).
    apply ostore2_Ok in O2. destruct O2 as (HU2 & ->).
    apply ostore2_Ok in O3. destruct O3 as (HU3 & ->).
    apply ostore2_Ok in O4. destruct O4 as (HU4 & ->).
    pose proof (HSYR _ _ NS) as SYM.
    destruct (build_x2_fields sym nb bs 2 SYM ltac:(lia) ltac:(lia) ltac:(right; reflexivity)) as (CS & CN & CL).
    change (2 =? 1) with false in CS. cbv iota in CS. fold c in CS, CN, CL.
    pose proof (sy_rd m1 SY js sorted s sym SYB HJS HLS ltac:(lia) NS) as RD.
    assert (UN : u + 3 < Z.of_nat ncells) by lia.
    assert (DV : D = bs + (nb + 512) * 65536) by (rewrite Z.lor_comm, (lor_add _ bs 8) by lia; lia).
    assert (VDE : Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D = (nb + 512) * 65536 + x2_seq c)
      by (rewrite (byte_lit sym SYM), CS, DV, Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256;
          rewrite (Z.mod_small (sym * 256)) by lia; rewrite lor_b3 by lia; lia).
    assert (H0 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D ≪ 32 mod 18446744073709551616)
                                         (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D)))
                 = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
      by (apply le2_of_mod16; rewrite rep_h0 by (rewrite VDE; lia); rewrite VDE; lia).
    assert (H1 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D ≪ 32 mod 18446744073709551616)
                                         (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D) ≫ 16))
                 = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
      by (rewrite CN, CL; apply le2_hi; try lia; rewrite rep_h1 by (rewrite VDE; lia); rewrite VDE; lia).
    assert (H2 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D ≪ 32 mod 18446744073709551616)
                                         (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D) ≫ 32))
                 = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
      by (apply le2_of_mod16; rewrite rep_h2 by (rewrite VDE; lia); rewrite VDE; lia).
    assert (H3 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D ≪ 32 mod 18446744073709551616)
                                         (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) D) ≫ 48))
                 = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
      by (rewrite CN, CL; apply le2_hi; try lia; rewrite rep_h3 by (rewrite VDE; lia); rewrite VDE; lia).
    zstep.
    all: repeat (lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
          let b := eval vm_compute in (existsb (Z.eqb pc) [0x1a484; 0x1a4e0]) in
          lazymatch b with
          | true => fail
          | false => first [ zstep | xcell (DT + 4) ARR u | xcell (DT + 4) ARR (u + 1)
                           | xcell (DT + 4) ARR (u + 2) | xcell (DT + 4) ARR (u + 3) ] end
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
      end).
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (INV2 : INV mc (oset2 (oset2 (oset2 (oset2 dt (Z.to_nat u) c) (Z.to_nat (u + 1)) c) (Z.to_nat (u + 2)) c)
                               (Z.to_nat (u + 3)) c))
        by (unfold xf_inv; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
            first [ assumption | olen ]) end.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a484) _ _ _ _) =>
          replace (DT + 4 + 4 * u + 16) with (DT + 4 + 4 * (u + 4)) by lia;
          replace (SY + s + 1) with (SY + (s + 1)) by lia;
          eapply (IH (s + 1) _ (u + 4) _ r); [exact HF1 | lia | lia | lia | exact INV2 |];
          intros m2 dt' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HR INV3;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV3]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a4e0) _ _ _ _) =>
          destruct f as [|f]; [lia|];
          replace (s + 1) with e in HF1 by lia; rewrite ffw_stop in HF1;
          lazymatch type of HF1 with Ok ?v = Ok ?rr => assert (HR : rr = v) by congruence end;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV2]
      end.
  Qed.
End F4B.

Ltac fwk stops := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) stops) in
      lazymatch b with true => fail | false => zstep end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
  end).
Ltac fpc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let z := eval vm_compute in pc in change (Z_to_bv 64 pc) with (Z_to_bv 64 z) end.

Section F8.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 sv0 sv1 : word).
  Variables (m : fmem) (DT SY e nb tl bs lvl LV FA lo : Z) (FC : list cell) (sorted : list (option Z))
    (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4.
  Hypothesis HSY : 0 < SY /\ SY + 256 <= 2^47.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HTL : tl - nb = 3.
  Hypothesis HE : e <= 256.
  Hypothesis HBS : 0 <= bs < 256.
  Hypothesis HLV : (lvl = 1 /\ LV = 16777216) \/ (lvl = 2 /\ LV = 33554432).
  Variables (j : list byte).
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ SY + 256 <= lo /\ lo <= FA /\ FA + 48 <= 2^47.
  Notation INV m1 dt := (xf_inv m m1 FA lo [CB 8 j; C8 x20; C8 x19; C8 x18; C8 sv1; C8 sv0] DT SY js jt sorted ncells dt).
  Notation D := (nb * 65536 + LV).

  Lemma f8_loop : forall f s dt u m1 r (x8 x9 x30 x31 : word),
    fill_for_weight f dt u s e nb tl bs lvl sorted = Ok r ->
    Z.of_nat f = e - s + 1 -> 0 <= s < e -> 0 <= u -> INV m1 dt ->
    (forall m2 dt' (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       r = (dt', u + 8 * (e - s)) -> INV m2 dt' ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24
                               x25 x26 x27 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x1a4e0) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)) (Z_to_bv 64 (-1)) x8 x9
                            (Z_to_bv 64 (DT + 4 + 4 * u)) (Z_to_bv 64 (SY + s)) (Z_to_bv 64 (SY + e)) (Z_to_bv 64 0)
                            (Z_to_bv 64 1) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 (-9)) x18 x19 x20 x21 x22 x23
                            x24 x25 x26 x27 (Z_to_bv 64 D) (Z_to_bv 64 (-33)) x30 x31)
                       F (Z_to_bv 64 0x1a1cc) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH]; intros s dt u m1 r x8 x9 x30 x31 HF Hf Hs Hu INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
    destruct (ffw_iter f dt u s e nb tl bs lvl sorted r ltac:(lia) ltac:(lia) HF) as (sym & dt1 & HB & NS & SR & HF1).
    rewrite HTL in SR, HF1. change (Z.to_nat (2 ^ 3)) with 8%nat in SR.
    pose proof (store_run_Ok _ _ _ _ _ SR ltac:(lia)) as [_ BR]. specialize (BR ltac:(lia)).
    cbn [store_run bind] in SR.
    change (2 ^ 3) with 8 in HF1.
    set (c := build_x2 sym nb bs lvl) in *.
    destruct (ostore2 dt u c) as [d1| | |] eqn:O1; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d1 (u + 1) c) as [d2| | |] eqn:O2; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d2 (u + 1 + 1) c) as [d3| | |] eqn:O3; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d3 (u + 1 + 1 + 1) c) as [d4| | |] eqn:O4; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d4 (u + 1 + 1 + 1 + 1) c) as [d5| | |] eqn:O5; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d5 (u + 1 + 1 + 1 + 1 + 1) c) as [d6| | |] eqn:O6; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d6 (u + 1 + 1 + 1 + 1 + 1 + 1) c) as [d7| | |] eqn:O7; cbn [bind] in SR; try discriminate.
    destruct (ostore2 d7 (u + 1 + 1 + 1 + 1 + 1 + 1 + 1) c) as [d8| | |] eqn:O8; cbn [bind] in SR; try discriminate.
    assert (dt1 = d8) by congruence; subst dt1; clear SR.
    replace (u + 1 + 1 + 1 + 1 + 1 + 1 + 1) with (u + 7) in O8 by lia.
    replace (u + 1 + 1 + 1 + 1 + 1 + 1) with (u + 6) in O7 by lia.
    replace (u + 1 + 1 + 1 + 1 + 1) with (u + 5) in O6 by lia.
    replace (u + 1 + 1 + 1 + 1) with (u + 4) in O5 by lia.
    replace (u + 1 + 1 + 1) with (u + 3) in O4 by lia.
    replace (u + 1 + 1) with (u + 2) in O3 by lia.
    apply ostore2_Ok in O1. destruct O1 as (HU1 & ->).
    apply ostore2_Ok in O2. destruct O2 as (HU2 & ->).
    apply ostore2_Ok in O3. destruct O3 as (HU3 & ->).
    apply ostore2_Ok in O4. destruct O4 as (HU4 & ->).
    apply ostore2_Ok in O5. destruct O5 as (HU5 & ->).
    apply ostore2_Ok in O6. destruct O6 as (HU6 & ->).
    apply ostore2_Ok in O7. destruct O7 as (HU7 & ->).
    apply ostore2_Ok in O8. destruct O8 as (HU8 & ->).
    pose proof (HSYR _ _ NS) as SYM.
    destruct (build_x2_fields sym nb bs lvl SYM ltac:(lia) ltac:(lia) ltac:(lia)) as (CS & CN & CL).
    fold c in CS, CN, CL.
    pose proof (sy_rd m1 SY js sorted s sym SYB HJS HLS ltac:(lia) NS) as RD.
    assert (UN : u + 7 < Z.of_nat ncells) by lia.
    zstep. zstep. if_cases K; zify_cond K;
      [ replace (lvl =? 1) with true in CS by (symmetry; apply Z.eqb_eq; lia);
        assert (VV : Z.lor (bv_unsigned (Z_to_bv 8 sym)) D = D + x2_seq c)
          by (rewrite (byte_lit sym SYM), CS, Z.lor_comm; apply lor_add with (k := 16); lia);
        assert (H0 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≪ 32 mod 18446744073709551616) (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D mod 4294967296)))
                     = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); apply le2_of_mod16;
              rewrite rep_h0 by (rewrite VV; lia); rewrite VV; lia);
        assert (H1 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≪ 32 mod 18446744073709551616) (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D mod 4294967296) ≫ 16))
                     = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); rewrite CN, CL; apply le2_hi; try lia;
              rewrite rep_h1 by (rewrite VV; lia); rewrite VV; lia);
        assert (H2 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≪ 32 mod 18446744073709551616) (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D mod 4294967296) ≫ 32))
                     = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); apply le2_of_mod16;
              rewrite rep_h2 by (rewrite VV; lia); rewrite VV; lia);
        assert (H3 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≪ 32 mod 18446744073709551616) (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D mod 4294967296) ≫ 48))
                     = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); rewrite CN, CL; apply le2_hi; try lia;
              rewrite rep_h3 by (rewrite VV; lia); rewrite VV; lia)
      | replace (lvl =? 1) with false in CS by (symmetry; apply Z.eqb_neq; lia);
        assert (VV : Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D = D + x2_seq c)
          by (rewrite (byte_lit sym SYM), CS, Z.shiftl_mul_pow2 by lia;
              rewrite (Z.mod_small (sym * 2 ^ 8)) by lia; rewrite (lor_add (sym * 2 ^ 8) bs 8) by lia;
              rewrite Z.lor_comm, (lor_add D (sym * 2 ^ 8 + bs) 16) by lia; lia);
        assert (H0 : le2 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D ≪ 32 mod 18446744073709551616) (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D mod 4294967296)))
                     = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); apply le2_of_mod16;
              rewrite rep_h0 by (rewrite VV; lia); rewrite VV; lia);
        assert (H1 : le2 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D ≪ 32 mod 18446744073709551616) (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D mod 4294967296) ≫ 16))
                     = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); rewrite CN, CL; apply le2_hi; try lia;
              rewrite rep_h1 by (rewrite VV; lia); rewrite VV; lia);
        assert (H2 : le2 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D ≪ 32 mod 18446744073709551616) (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D mod 4294967296) ≫ 32))
                     = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); apply le2_of_mod16;
              rewrite rep_h2 by (rewrite VV; lia); rewrite VV; lia);
        assert (H3 : le2 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D ≪ 32 mod 18446744073709551616) (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D mod 4294967296) ≫ 48))
                     = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); rewrite CN, CL; apply le2_hi; try lia;
              rewrite rep_h3 by (rewrite VV; lia); rewrite VV; lia) ].
    all: fwk [0x1a1cc; 0x1a4e0].
    all: xcell (DT + 4) ARR u; fwk [0x1a1cc; 0x1a4e0].
    all: xcell (DT + 4) ARR (u + 1); fwk [0x1a1cc; 0x1a4e0].
    all: xcell (DT + 4) ARR (u + 2); fwk [0x1a1cc; 0x1a4e0].
    all: xcell (DT + 4) ARR (u + 3); fwk [0x1a1cc; 0x1a4e0].
    all: xcell (DT + 4) ARR (u + 4); fwk [0x1a1cc; 0x1a4e0].
    all: xcell (DT + 4) ARR (u + 5); fwk [0x1a1cc; 0x1a4e0].
    all: xcell (DT + 4) ARR (u + 6); fwk [0x1a1cc; 0x1a4e0].
    all: xcell (DT + 4) ARR (u + 7); fwk [0x1a1cc; 0x1a4e0].
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (INV2 : INV mc (oset2 (oset2 (oset2 (oset2 (oset2 (oset2 (oset2 (oset2 dt (Z.to_nat u) c) (Z.to_nat (u + 1)) c) (Z.to_nat (u + 2)) c) (Z.to_nat (u + 3)) c) (Z.to_nat (u + 4)) c) (Z.to_nat (u + 5)) c) (Z.to_nat (u + 6)) c) (Z.to_nat (u + 7)) c))
        by (unfold xf_inv; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
            first [ assumption | olen ]) end.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1cc) _ _ _ _) =>
          replace (DT + 4 + 4 * u + 32) with (DT + 4 + 4 * (u + 8)) by lia;
          replace (SY + s + 1) with (SY + (s + 1)) by lia;
          eapply (IH (s + 1) _ (u + 8) _ r); [exact HF1 | lia | lia | lia | exact INV2 |];
          intros m2 dt' y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HR INV3;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV3]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a4e0) _ _ _ _) =>
          destruct f as [|f]; [lia|];
          replace (s + 1) with e in HF1 by lia; rewrite ffw_stop in HF1;
          lazymatch type of HF1 with Ok ?v = Ok ?rr => assert (HR : rr = v) by congruence end;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV2]
      end.
  Qed.
End F8.

Section FD.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x21 x22 x23 x24 x25 x26 x27 sv0 sv1 sv2 sv3 sv4 : word).
  Variables (m : fmem) (DT SY e nb tl bs lvl LV FA lo : Z) (FC : list cell) (sorted : list (option Z))
    (js jt : list byte) (ncells : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis HJT : length jt = (4 * ncells)%nat.
  Hypothesis HJS : length js = length sorted.
  Hypothesis HLS : length sorted = 256%nat.
  Hypothesis HSYR : forall i v, nth i sorted None = Some v -> 0 <= v < 256.
  Hypothesis HDT : 0 < DT /\ DT + 4 + 4 * Z.of_nat ncells <= 2^47.
  Hypothesis DJ : DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4.
  Hypothesis HSY : 0 < SY /\ SY + 256 <= 2^47.
  Hypothesis HNB : 1 <= nb <= 12.
  Hypothesis HTL : 4 <= tl - nb <= 11.
  Hypothesis HE : e <= 256.
  Hypothesis HBS : 0 <= bs < 256.
  Hypothesis HLV : (lvl = 1 /\ LV = 16777216) \/ (lvl = 2 /\ LV = 33554432).
  Variables (j : list byte).
  Hypothesis HLO : DT + 4 + 4 * Z.of_nat ncells <= lo /\ SY + 256 <= lo /\ lo <= FA /\ FA + 48 <= 2^47.
  Notation INV m1 dt := (xf_inv m m1 FA lo [CB 8 j; C8 sv4; C8 sv3; C8 sv2; C8 sv1; C8 sv0] DT SY js jt sorted ncells dt).
  Notation D := (nb * 65536 + LV).
  Notation LEN := (2 ^ (tl - nb)).

  Hypothesis HDT2 : DT mod 2 = 0.

  Lemma fdi_loop : forall (k : nat) p pe dt dt' m1 c (w0 w1 w2 w3 x7 x11 x12 x13 x15 x16 x28 x29 x30 : word),
    store_run (8 * k) dt p c = Ok dt' -> (0 < k)%nat -> 0 <= p -> pe = p + 8 * Z.of_nat k -> pe <= Z.of_nat ncells ->
    le2 w0 = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)] ->
    le2 w1 = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)] ->
    le2 w2 = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)] ->
    le2 w3 = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)] ->
    INV m1 dt ->
    (forall m2, INV m2 dt' ->
       evt usegs POST (MS (mkR x1 sp gp tp (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33)) x7 (Z_to_bv 64 0) w0
                               (Z_to_bv 64 (DT + 4 + 4 * pe)) x11 x12 x13 (Z_to_bv 64 (-9)) x15 x16 (Z_to_bv 64 (-17))
                               w3 w2 w1 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (DT + 4 + 4 * pe)))
                          F (Z_to_bv 64 0x1a338) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33)) x7 (Z_to_bv 64 0) w0
                            (Z_to_bv 64 (DT + 4 + 4 * p)) x11 x12 x13 (Z_to_bv 64 (-9)) x15 x16 (Z_to_bv 64 (-17))
                            w3 w2 w1 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (DT + 4 + 4 * pe)))
                       F (Z_to_bv 64 0x1a2dc) fc None m1 (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros p pe dt dt' m1 c w0 w1 w2 w3 x7 x11 x12 x13 x15 x16 x28 x29 x30
      SR Hk Hp Hpe HPE W0 W1 W2 W3 INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
    replace (8 * S k)%nat with (8 + 8 * k)%nat in SR by lia. rewrite store_run_add in SR.
    destruct (store_run 8 dt p c) as [d8| | |] eqn:S8; cbn [bind] in SR; try discriminate.
    pose proof (store_run_Ok _ _ _ _ _ S8 ltac:(lia)) as [L8 B8]. specialize (B8 ltac:(lia)).
    cbn [store_run bind] in S8.
    destruct (ostore2 dt p c) as [o1| | |] eqn:O1; cbn [bind] in S8; try discriminate.
    destruct (ostore2 o1 (p + 1) c) as [o2| | |] eqn:O2; cbn [bind] in S8; try discriminate.
    destruct (ostore2 o2 (p + 1 + 1) c) as [o3| | |] eqn:O3; cbn [bind] in S8; try discriminate.
    destruct (ostore2 o3 (p + 1 + 1 + 1) c) as [o4| | |] eqn:O4; cbn [bind] in S8; try discriminate.
    destruct (ostore2 o4 (p + 1 + 1 + 1 + 1) c) as [o5| | |] eqn:O5; cbn [bind] in S8; try discriminate.
    destruct (ostore2 o5 (p + 1 + 1 + 1 + 1 + 1) c) as [o6| | |] eqn:O6; cbn [bind] in S8; try discriminate.
    destruct (ostore2 o6 (p + 1 + 1 + 1 + 1 + 1 + 1) c) as [o7| | |] eqn:O7; cbn [bind] in S8; try discriminate.
    destruct (ostore2 o7 (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) c) as [o8| | |] eqn:O8; cbn [bind] in S8; try discriminate.
    assert (d8 = o8) by congruence; subst d8; clear S8.
    replace (p + 1 + 1 + 1 + 1 + 1 + 1 + 1) with (p + 7) in O8 by lia.
    replace (p + 1 + 1 + 1 + 1 + 1 + 1) with (p + 6) in O7 by lia.
    replace (p + 1 + 1 + 1 + 1 + 1) with (p + 5) in O6 by lia.
    replace (p + 1 + 1 + 1 + 1) with (p + 4) in O5 by lia.
    replace (p + 1 + 1 + 1) with (p + 3) in O4 by lia.
    replace (p + 1 + 1) with (p + 2) in O3 by lia.
    apply ostore2_Ok in O1. destruct O1 as (HU1 & ->).
    apply ostore2_Ok in O2. destruct O2 as (HU2 & ->).
    apply ostore2_Ok in O3. destruct O3 as (HU3 & ->).
    apply ostore2_Ok in O4. destruct O4 as (HU4 & ->).
    apply ostore2_Ok in O5. destruct O5 as (HU5 & ->).
    apply ostore2_Ok in O6. destruct O6 as (HU6 & ->).
    apply ostore2_Ok in O7. destruct O7 as (HU7 & ->).
    apply ostore2_Ok in O8. destruct O8 as (HU8 & ->).
    zstep. all: fwk [0x1a2dc; 0x1a338].
    all: xcell (DT + 4) ARR p; fwk [0x1a2dc; 0x1a338].
    all: xcell (DT + 4) ARR (p + 1); fwk [0x1a2dc; 0x1a338].
    all: xcell (DT + 4) ARR (p + 2); fwk [0x1a2dc; 0x1a338].
    all: xcell (DT + 4) ARR (p + 3); fwk [0x1a2dc; 0x1a338].
    all: xcell (DT + 4) ARR (p + 4); fwk [0x1a2dc; 0x1a338].
    all: xcell (DT + 4) ARR (p + 5); fwk [0x1a2dc; 0x1a338].
    all: xcell (DT + 4) ARR (p + 6); fwk [0x1a2dc; 0x1a338].
    all: xcell (DT + 4) ARR (p + 7); fwk [0x1a2dc; 0x1a338].
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (INV2 : INV mc (oset2 (oset2 (oset2 (oset2 (oset2 (oset2 (oset2 (oset2 dt (Z.to_nat p) c) (Z.to_nat (p + 1)) c) (Z.to_nat (p + 2)) c) (Z.to_nat (p + 3)) c) (Z.to_nat (p + 4)) c) (Z.to_nat (p + 5)) c) (Z.to_nat (p + 6)) c) (Z.to_nat (p + 7)) c))
        by (unfold xf_inv; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))));
            first [ assumption | olen ]) end.
    all: change (Z.of_nat 8) with 8 in SR.
    all: fpc.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a2dc) _ _ _ _) =>
          replace (DT + 4 + 4 * p + 32) with (DT + 4 + 4 * (p + 8)) by lia;
          eapply (IH (p + 8) pe _ dt' _ c w0 w1 w2 w3 x7 x11 x12 x13 x15 x16 x28 x29 x30 SR);
            [lia | lia | lia | lia | exact W0 | exact W1 | exact W2 | exact W3 | exact INV2 | exact CONT]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a338) _ _ _ _) =>
          destruct k as [|k]; [|lia];
          change (8 * 0)%nat with 0%nat in SR; cbn [store_run] in SR;
          lazymatch type of SR with Ok ?v = Ok ?w => assert (HD : w = v) by congruence end;
          replace (DT + 4 + 4 * p + 32) with (DT + 4 + 4 * pe) by lia;
          apply CONT; rewrite HD; exact INV2
      end.
  Qed.


  Lemma fdo_loop : forall f s dt u m1 r (x8 x9 x18 x19 x20 x31 : word),
    fill_for_weight f dt u s e nb tl bs lvl sorted = Ok r ->
    Z.of_nat f = e - s + 1 -> 0 <= s < e -> 0 <= u -> INV m1 dt ->
    (forall m2 dt' (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 : word),
       r = (dt', u + LEN * (e - s)) -> INV m2 dt' ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 x21 x22 x23 x24
                               x25 x26 x27 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x1a4e0) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33)) (Z_to_bv 64 D) x8 x9
                            (Z_to_bv 64 (DT + 4 + 4 * u)) (Z_to_bv 64 (SY + s)) (Z_to_bv 64 (SY + e)) (Z_to_bv 64 1)
                            (Z_to_bv 64 (-9)) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 (-17)) x18 x19 x20 x21 x22 x23
                            x24 x25 x26 x27 (Z_to_bv 64 (4 * LEN)) (Z_to_bv 64 (4 * LEN)) (Z_to_bv 64 (-1)) x31)
                       F (Z_to_bv 64 0x1a298) fc None m1 (seg_rom usegs)).
  Proof.
    induction f as [|f IH]; intros s dt u m1 r x8 x9 x18 x19 x20 x31 HF Hf Hs Hu INV CONT; [lia|].
    destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
    destruct (ffw_iter f dt u s e nb tl bs lvl sorted r ltac:(lia) ltac:(lia) HF) as (sym & dt1 & HB & NS & SR & HF1).
    pose proof (store_run_Ok _ _ _ _ _ SR ltac:(lia)) as [LR BR].
    assert (L16 : 16 <= LEN <= 2048).
    { destruct (pow2_small_cases (tl - nb) ltac:(lia)) as [[? ?]|[[? ?]|[[? ?]|[[? ?]|[? ?]]]]]; lia. }
    specialize (BR ltac:(lia)). rewrite Z2Nat.id in BR by lia.
    set (c := build_x2 sym nb bs lvl) in *.
    pose proof (HSYR _ _ NS) as SYM.
    destruct (build_x2_fields sym nb bs lvl SYM ltac:(lia) ltac:(lia) ltac:(lia)) as (CS & CN & CL).
    fold c in CS, CN, CL.
    pose proof (sy_rd m1 SY js sorted s sym SYB HJS HLS ltac:(lia) NS) as RD.
    assert (X8 : Z_to_bv 64 (Z.land (DT + 4 + 4 * u) 1) = Z_to_bv 64 0).
    { f_equal. pose proof (Z.land_ones (DT + 4 + 4 * u) 1 ltac:(lia)) as LO.
      change (Z.ones 1) with 1 in LO. rewrite LO, Z.pow_1_r. lia. }
    assert (L8 : LEN = 8 * 2 ^ (tl - nb - 3)).
    { replace (tl - nb) with (3 + (tl - nb - 3)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    assert (SR8 : store_run (8 * Z.to_nat (2 ^ (tl - nb - 3))) dt u c = Ok dt1).
    { rewrite <- SR. f_equal. rewrite L8, Z2Nat.inj_mul by lia. reflexivity. }
    zstep. zstep. if_cases K; zify_cond K;
      [ replace (lvl =? 1) with true in CS by (symmetry; apply Z.eqb_eq; lia);
        assert (VV : Z.lor (bv_unsigned (Z_to_bv 8 sym)) D = D + x2_seq c)
          by (rewrite (byte_lit sym SYM), CS, Z.lor_comm; apply lor_add with (k := 16); lia);
        assert (H0 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≪ 32 mod 18446744073709551616) (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D mod 4294967296)))
                     = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); apply le2_of_mod16;
              rewrite rep_h0 by (rewrite VV; lia); rewrite VV; lia);
        assert (H1 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≪ 32 mod 18446744073709551616) (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D mod 4294967296) ≫ 16))
                     = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); rewrite CN, CL; apply le2_hi; try lia;
              rewrite rep_h1 by (rewrite VV; lia); rewrite VV; lia);
        assert (H2 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≪ 32 mod 18446744073709551616) (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D mod 4294967296) ≫ 32))
                     = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); apply le2_of_mod16;
              rewrite rep_h2 by (rewrite VV; lia); rewrite VV; lia);
        assert (H3 : le2 (Z_to_bv 64 (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D ≪ 32 mod 18446744073709551616) (Z.lor (bv_unsigned (Z_to_bv 8 sym)) D mod 4294967296) ≫ 48))
                     = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); rewrite CN, CL; apply le2_hi; try lia;
              rewrite rep_h3 by (rewrite VV; lia); rewrite VV; lia)
      | replace (lvl =? 1) with false in CS by (symmetry; apply Z.eqb_neq; lia);
        assert (VV : Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D = D + x2_seq c)
          by (rewrite (byte_lit sym SYM), CS, Z.shiftl_mul_pow2 by lia;
              rewrite (Z.mod_small (sym * 2 ^ 8)) by lia; rewrite (lor_add (sym * 2 ^ 8) bs 8) by lia;
              rewrite Z.lor_comm, (lor_add D (sym * 2 ^ 8 + bs) 16) by lia; lia);
        assert (H0 : le2 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D ≪ 32 mod 18446744073709551616) (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D mod 4294967296)))
                     = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); apply le2_of_mod16;
              rewrite rep_h0 by (rewrite VV; lia); rewrite VV; lia);
        assert (H1 : le2 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D ≪ 32 mod 18446744073709551616) (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D mod 4294967296) ≫ 16))
                     = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); rewrite CN, CL; apply le2_hi; try lia;
              rewrite rep_h1 by (rewrite VV; lia); rewrite VV; lia);
        assert (H2 : le2 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D ≪ 32 mod 18446744073709551616) (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D mod 4294967296) ≫ 32))
                     = [Z_to_bv 8 (x2_seq c); Z_to_bv 8 (x2_seq c / 256)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); apply le2_of_mod16;
              rewrite rep_h2 by (rewrite VV; lia); rewrite VV; lia);
        assert (H3 : le2 (Z_to_bv 64 (Z.lor (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D ≪ 32 mod 18446744073709551616) (Z.lor (Z.lor (bv_unsigned (Z_to_bv 8 sym) ≪ 8 mod 18446744073709551616) bs) D mod 4294967296) ≫ 48))
                     = [Z_to_bv 8 (x2_nbBits c); Z_to_bv 8 (x2_len c)])
          by (rewrite (Z.mod_small _ 4294967296) by (rewrite VV; lia); rewrite CN, CL; apply le2_hi; try lia;
              rewrite rep_h3 by (rewrite VV; lia); rewrite VV; lia) ].
    all: fwk [0x1a298; 0x1a2dc; 0x1a4e0].
    all: rewrite X8; replace (DT + 4 + 4 * u + 4 * LEN) with (DT + 4 + 4 * (u + LEN)) by lia.
    all: eapply (fdi_loop (Z.to_nat (2 ^ (tl - nb - 3))) u (u + LEN) dt dt1 _ c);
      [exact SR8 | lia | lia | rewrite Z2Nat.id by lia; lia | lia | exact H0 | exact H1 | exact H2 | exact H3
      | unfold xf_inv; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); assumption | ].
    all: intros m2 INV3; fwk [0x1a298; 0x1a4e0].
    all: fpc.
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a298) _ _ _ _) =>
          replace (SY + s + 1) with (SY + (s + 1)) by lia;
          eapply (IH (s + 1) _ (u + LEN) _ r); [exact HF1 | lia | lia | lia | exact INV3 |];
          intros m3 dt' y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 HR INV4;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV4]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a4e0) _ _ _ _) =>
          destruct f as [|f]; [lia|];
          replace (s + 1) with e in HF1 by lia; rewrite ffw_stop in HF1;
          lazymatch type of HF1 with Ok ?v = Ok ?rr => assert (HR : rr = v) by congruence end;
          eapply CONT; [rewrite HR; f_equal; lia | exact INV3]
      end.
  Qed.
End FD.

Definition x2fill_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : fmem) (DT SY : Z) (js jt : list byte) (sorted : list (option Z)) (ncells : nat)
    (r : list (option deltX2) * Z) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ u8arr usegs m' (DT + 4) (ox2 jt (fst r)) /\ length (fst r) = ncells
    /\ bytes_at usegs m' SY (omerge js sorted)
    /\ munch [(bv_unsigned sp - X2FILL_STACK, bv_unsigned sp); (DT + 4, DT + 4 + 4 * Z.of_nat ncells)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp).

Definition x2fill_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DT SY b e nb tl bs lvl start lo : Z)
         (sorted : list (option Z)) (js jt : list byte) (ncells : nat) (dt : list (option deltX2))
         (r : list (option deltX2) * Z),
  fill_for_weight (S (Z.to_nat (e - b))) dt start b e nb tl bs lvl sorted = Ok r ->
  1 <= nb <= tl -> tl <= 12 -> (lvl = 1 \/ lvl = 2) -> 0 <= bs < 256 ->
  0 <= b <= e -> e <= 256 -> 0 <= start ->
  length jt = (4 * ncells)%nat -> length js = length sorted -> length sorted = 256%nat ->
  (forall i v, nth i sorted None = Some v -> 0 <= v < 256) ->
  0 < DT -> DT mod 2 = 0 -> DT + 4 + 4 * Z.of_nat ncells <= lo -> 0 < SY -> SY + 256 <= lo ->
  (DT + 4 + 4 * Z.of_nat ncells <= SY \/ SY + 256 <= DT + 4) ->
  u8arr usegs m (DT + 4) (ox2 jt dt) -> length dt = ncells -> bytes_at usegs m SY (omerge js sorted) ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X2FILL_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv usegs m ->
  evt usegs (x2fill_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DT SY js jt sorted ncells r lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (DT + 4 + 4 * start)) (Z_to_bv 64 (SY + b)) (Z_to_bv 64 (SY + e))
               (Z_to_bv 64 nb) (Z_to_bv 64 tl) (Z_to_bv 64 bs) (Z_to_bv 64 lvl) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_FILL_X2) fc None m (seg_rom usegs)).

Lemma len_norm : forall k, 0 <= k <= 11 -> bv_swrap 32 (1 ≪ ((bv_swrap 32 k mod 18446744073709551616) mod 32)) = 2 ^ k.
Proof.
  intros k Hk.
  assert (HH : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  repeat (destruct HH as [-> | HH]; [vm_compute; reflexivity|]); subst; vm_compute; reflexivity.
Qed.

Definition X2F_STOPS : list Z := [0x1a14c; 0x1a1cc; 0x1a298; 0x1a2dc; 0x1a370; 0x1a3cc; 0x1a43c; 0x1a484; 0x1a4e0].

Ltac zgo := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) X2F_STOPS) in
      lazymatch b with true => fail | false => zstep end
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; lia)
  | |- _ => zstep end).

Lemma xf_exit : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m m1 : fmem) (DT SY lo : Z) (js jt : list byte) (sorted : list (option Z)) (ncells : nat)
    (r : list (option deltX2) * Z) (j : list byte)
    (y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 : word),
  bv_unsigned sp <= 2^47 -> lo <= bv_unsigned sp - 48 ->
  xf_inv m m1 (bv_unsigned sp - 48) lo [CB 8 j; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] DT SY js jt sorted ncells (fst r) ->
  evt usegs (x2fill_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DT SY js jt sorted ncells r lo)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20
             s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (Z_to_bv 64 0x1a4e0) fc None m1 (seg_rom usegs)).
Proof.
  intros until y31. intros SP47 LOS INV.
  destruct INV as (ARR & LDT & SYB & FR & ST & MU & WM & MI).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
  pose proof (stk_release usegs m1 lo _ _ ST FR LOS) as ST2. cbn [cells_size csize Nat.add] in ST2.
  replace (bv_unsigned sp - 48 + Z.of_nat 48) with (bv_unsigned sp) in ST2 by lia.
  replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) in * by lia. rewrite Z_to_bv_bv_unsigned.
  apply evt_done. unfold x2fill_post.
  do 15 eexists. eexists. split; [reflexivity|].
  refine (conj ARR (conj LDT (conj SYB (conj _ (conj WM (conj MI ST2)))))).
  exact MU.
Qed.

Ltac fixpc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let z := eval vm_compute in pc in change (Z_to_bv 64 pc) with (Z_to_bv 64 z) end.

Ltac xinv := unfold xf_inv;
  try (match goal with |- context [?a - 48 + 48] => replace (a - 48 + 48) with a by lia end);
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); eassumption.

Ltac xf_done :=
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a4e0) _ _ _ _) => idtac end;
  match goal with K : ?S + ?b = ?S + ?e |- _ => assert (EB : e = b) by lia; subst e end;
  match goal with HF : fill_for_weight _ _ _ _ _ _ _ _ _ _ = Ok _ |- _ =>
    rewrite Z.sub_diag in HF; change (Z.to_nat 0) with O in HF; rewrite ffw_stop in HF; injection HF as <- end;
  eapply xf_exit; [lia | lia | ];
  unfold xf_inv; cbn [fst];
  try (match goal with |- context [?a - 48 + 48] => replace (a - 48 + 48) with a by lia end);
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); eassumption.

Lemma len4_hi : forall L, 0 <= L < 2^30 -> Z_to_bv 64 ((L ≪ 32 mod 18446744073709551616) ≫ 30) = Z_to_bv 64 (4 * L).
Proof.
  intros L HL. f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 30) with 1073741824.
  replace (L * 4294967296) with (4 * L * 1073741824) by lia. apply Z.div_mul. lia.
Qed.

Lemma len4_lo : forall L, 0 <= L < 2^30 -> Z_to_bv 64 ((L mod 4294967296) ≪ 2) = Z_to_bv 64 (4 * L).
Proof.
  intros L HL. f_equal. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Theorem x2fill_proof : x2fill_stmt.
Proof.
  unfold x2fill_stmt. intros until r.
  intros HF HNB HTL HLV HBS HBE HE HST LJT LJS LLS HSYR HDT0 HDT2 HDTL HSY0 HSYL DJ ARR LDT SYB STK STKL SP47 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - X2FILL_STACK, bv_unsigned sp); (DT + 4, DT + 4 + 4 * Z.of_nat ncells)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold X2FILL_STACK in *.
  carve_frame 48%nat STK.
  do 11 zstep.
  rewrite (len_norm (tl - nb)) by lia.
  destruct (pow2_small_cases (tl - nb) ltac:(lia)) as [[K0 P]|[[K0 P]|[[K0 P]|[[K0 P]|[K0 P]]]]]; try rewrite P;
    destruct HLV as [-> | ->].
  all: zgo.
  all: replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in * by lia.
  all: fixpc.
  all: try (xf_done; fail).
  all: repeat (lazymatch goal with |- context [?c + ?n ≪ 16] =>
         replace (c + n ≪ 16) with (n * 65536 + c) in * by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 16) with 65536; lia) end).
  all: repeat rewrite (Z.mod_small (nb * 65536 + 16777216)) by lia.
  all: repeat rewrite (Z.mod_small (nb * 65536 + 33554432)) by lia.
  all: try (rewrite (Z.mod_small (Z.lor bs (nb * 65536 + 33554432)) 4294967296)
              by (rewrite Z.lor_comm, (lor_add _ bs 8) by lia; lia)).
  all: try rewrite (land1_even DT start HDT2).
  all: try rewrite (len4_hi (2 ^ (tl - nb))) by lia.
  all: try rewrite (len4_lo (2 ^ (tl - nb))) by lia.
  all: assert (BE : b < e) by lia.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a370) _ _ _ _) =>
        eapply f1a_loop with (FA := bv_unsigned sp - 48) (lo := lo) (f := S (Z.to_nat (e - b))) (s := b) (u := start)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a43c) _ _ _ _) =>
        eapply f1b_loop with (FA := bv_unsigned sp - 48) (lo := lo) (f := S (Z.to_nat (e - b))) (s := b) (u := start)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a14c) _ _ _ _) =>
        eapply f2_loop with (FA := bv_unsigned sp - 48) (lo := lo) (f := S (Z.to_nat (e - b))) (s := b) (u := start)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a3cc) _ _ _ _) =>
        eapply f4a_loop with (FA := bv_unsigned sp - 48) (lo := lo) (f := S (Z.to_nat (e - b))) (s := b) (u := start)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a484) _ _ _ _) =>
        eapply f4b_loop with (FA := bv_unsigned sp - 48) (lo := lo) (f := S (Z.to_nat (e - b))) (s := b) (u := start)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a1cc) _ _ _ _) =>
        eapply f8_loop with (FA := bv_unsigned sp - 48) (lo := lo) (f := S (Z.to_nat (e - b))) (s := b) (u := start)
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1a298) _ _ _ _) =>
        eapply fdo_loop with (FA := bv_unsigned sp - 48) (lo := lo) (f := S (Z.to_nat (e - b))) (s := b) (u := start)
    end.
  all: try eassumption.
  all: try xinv.
  all: try lia.
  all: try (repeat split; lia).
  all: try (left; split; reflexivity).
  all: try (right; split; reflexivity).
  all: try (intros; match goal with HR : _ = (_, _), INV2 : xf_inv _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
             eapply xf_exit; [lia | lia | rewrite HR; exact INV2] end).
Qed.
