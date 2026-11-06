From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import reac_frame_inspect_c reac_decode_c ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

Lemma decode_ok_spec : forall len bs nch ns,
  decode_ok len bs nch ns = true <->
  inspect_wf len bs = true /\ 0 < nch /\ nch mod 2 = 0 /\ 0 < ns /\ nch * ns <= 480.
Proof.
  intros. unfold decode_ok. rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq, Z.leb_le. tauto.
Qed.

Lemma braid_pos_lin : forall s ch nch k, 0 <= k < 3 ->
  braid_pos s ch nch k = 3 * (s * nch + (ch - ch mod 2)) +
    (if k =? 0 then 3 + ch mod 2 else if k =? 1 then 5 * (ch mod 2) else 1 + ch mod 2).
Proof.
  intros s ch nch k Hk. unfold braid_pos.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  destruct (Z.eqb_spec (ch mod 2) 0) as [E|E];
  destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); try rewrite E; lia.
Qed.

Lemma braid_byte_at : forall bs nch ns ch s k, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  braid_byte bs nch ns (3 * (ch * ns + s) + k) = nth (Z.to_nat (50 + braid_pos s ch nch k)) bs (Z_to_bv 8 0).
Proof.
  intros bs nch ns ch s k Hch Hs Hk. unfold braid_byte.
  destruct (braid_div ch s k ns Hch Hs Hk) as (D1 & D2 & D3 & D4). rewrite D1, D2, D3, D4. reflexivity.
Qed.

Section RD.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 a1 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw mode out nch ns lo : Z).

Definition PostD : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                  (Z_to_bv 64 (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    (if decode_ok (bv_unsigned a1) bs nch ns
     then munch [(bv_unsigned sp - 32, bv_unsigned sp); (out, out + 3 * nch * ns)] m m' /\
          bytes_at rsegs m' out (braid_out bs nch ns)
     else munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m').

Local Notation SP := (bv_unsigned sp).
Local Notation FR mk := (rw_cells rsegs mk (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
Local Notation N := (3 * nch * ns).
Local Notation STATE pc mm x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 :=
  (MS (mkR (Z_to_bv 64 0x136b8) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 (Z_to_bv 64 raw)
        x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 mode) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 32 <= SP.
Hypothesis Hlo : 0 <= lo.

Lemma rd_exit : forall (m1 : word -> option byte) (r : Z)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 : word),
  FR m1 -> stk rsegs m1 lo (SP + -32) -> wmono rsegs m m1 ->
  r = (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1) ->
  (if decode_ok (bv_unsigned a1) bs nch ns
   then munch [(SP + -32, SP); (out, out + N)] m m1 /\ bytes_at rsegs m1 out (braid_out bs nch ns)
   else munch [(SP + -32, SP)] m m1) ->
  evt rsegs PostD (MS (mkR x1 (Z_to_bv 64 (SP + -32)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16
      x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6) F (Z_to_bv 64 0x1377c) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 6 step.
  apply evt_done. unfold PostD. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, t6, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -32) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -32 + Z.of_nat 32) with SP in ST2 by lia. exact ST2.
  - replace (SP - 32) with (SP + -32) by lia. exact HM.
Qed.

Hypothesis Hlen : length bs = 1492%nat.
Hypothesis Hraw : 0 <= raw.
Hypothesis Hraw2 : raw + 1492 <= 2^64.
Hypothesis Hout : 0 <= out.
Hypothesis HoutN : out + N < 2^64.
Hypothesis Hnch : 0 < nch.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.
Hypothesis DOR : out + N <= raw \/ raw + 1492 <= out.
Hypothesis DOS : out + N <= SP - 32 \/ SP <= out.
Hypothesis OK : decode_ok (bv_unsigned a1) bs nch ns = true.

Definition INVD (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ FR mk /\ stk rsegs mk lo (SP + -32) /\ wr_at rsegs mk out N /\
  munch [(SP + -32, SP); (out, out + N)] m mk /\ wmono rsegs m mk /\
  (forall i, 0 <= i < j -> mrd rsegs mk (Z_to_bv 64 (out + i)) = Some (braid_byte bs nch ns i)).

Lemma INVD_idx : forall mk j j', INVD mk j -> j = j' -> INVD mk j'.
Proof. intros; subst; assumption. Qed.

Lemma INVD_rd : forall mk j ch s k, INVD mk j -> 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 ->
  ov_read_bytes rsegs mk (Z_to_bv 64 (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) +
    (if k =? 0 then 3 + ch mod 2 else if k =? 1 then 5 * (ch mod 2) else 1 + ch mod 2))))) 1 =
  Some [braid_byte bs nch ns (3 * (ch * ns + s) + k)].
Proof.
  intros mk j ch s k (HB & _) Hch Hs Hk. rewrite braid_byte_at by lia. rewrite <- braid_pos_lin by lia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  apply rd1; [exact HB|]. rewrite Hlen. rewrite braid_pos_lin by lia.
  destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); nia.
Qed.

Lemma INVD_wr : forall mk j q, INVD mk j -> 0 <= q < N -> store_ok rsegs mk (Z_to_bv 64 (out + q)) 1 = true.
Proof.
  intros mk j q (_ & _ & _ & HW & _) Hq. change (Z_to_bv 64 (out + q)) with (wa (out + q)).
  apply (wr_at_store_ok rsegs mk out N q 1 HW); lia.
Qed.

Lemma INVD_store : forall mk j0 j j2, INVD mk j0 -> j0 = j -> 0 <= j < N -> j2 = j + 1 ->
  INVD (write_to_mem mk (Z_to_bv 64 (out + j)) [braid_byte bs nch ns j]) j2.
Proof.
  intros mk j0 j j2 (HB & HF & ST & HW & MU & WM & HP) E Hj E2. subst j0 j2.
  change (Z_to_bv 64 (out + j)) with (wa (out + j)).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply bytes_at_write_other; [exact HB | lia | cbn; lia | rewrite Hlen; cbn; lia].
  - apply rw_cells_frame; [exact HF | lia | cbn; lia | cbn; lia].
  - apply stk_write; [exact ST | lia | cbn; lia].
  - apply wr_at_write. exact HW.
  - apply munch_write; [exact MU | lia | cbn; lia | cbn [inside]; cbn; lia].
  - apply wmono_write. exact WM.
  - intros i Hi. change (wa (out + j)) with (Z_to_bv 64 (out + j)).
    rewrite mrd_write1 by lia.
    destruct (Z.eqb_spec (out + i) (out + j)) as [E|E].
    + replace i with j by lia. reflexivity.
    + apply HP. lia.
Qed.

Lemma INVD_out : forall mk, INVD mk N -> bytes_at rsegs mk out (braid_out bs nch ns).
Proof.
  intros mk (_ & _ & _ & _ & _ & _ & HP). unfold braid_out.
  apply bytes_at_of_fun; [lia | lia |]. intros i Hi. apply HP. lia.
Qed.

Ltac do_store I0 I1 jj :=
  rewrite ?le1_zxb;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mk ?a ?b) _) =>
    assert (I1 : INVD (write_to_mem mk a b) (jj + 1)) by (eapply INVD_store; [exact I0 | lia | lia | lia]);
    let m2 := fresh "m" in set (m2 := write_to_mem mk a b) in *; clearbody m2; clear I0
  end.

Lemma rd_inner : forall (ch : Z) (x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 : word),
  0 <= ch < nch -> bv_unsigned x6 = raw + 50 + ch mod 2 + 3 -> bv_unsigned x7 = raw + 50 + ch mod 2 + 1 ->
  bv_unsigned x14 = raw + 50 -> bv_unsigned x16 = 3 * nch -> bv_unsigned x17 = out + 3 * (ch * ns + ns) ->
  bv_unsigned x28 = 5 * (ch mod 2) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x5 x8 x29 x30 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns ->
  bv_unsigned x5 = 3 * (ch - ch mod 2) + 3 * nch * s -> bv_unsigned x8 = out + 3 * (ch * ns + s) ->
  INVD m1 (3 * (ch * ns + s)) ->
  (forall (m2 : word -> option byte) (y5 y8 y29 y30 : word), bv_unsigned y8 = out + 3 * (ch * ns + ns) ->
     INVD m2 (3 * (ch * ns + ns)) ->
     evt rsegs PostD (STATE 0x1376c m2 y5 x6 x7 y8 x10 x11 x12 x13 x14 x15 x16 x17 x28 y29 y30)) ->
  evt rsegs PostD (STATE 0x13738 m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30).
Proof.
  intros ch x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 Hch H6 H7 H14 H16 H17 H28 K.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x5 x8 x29 x30 HK Hs H5 H8 I0 CONT.
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (nch <= 480 /\ ns <= 480) by nia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  apply wv in H5, H6, H7, H8, H14, H16, H17, H28. subst x5 x6 x7 x8 x14 x16 x17 x28.
  pose proof (INVD_rd m1 _ ch s 0 I0 Hch Hs ltac:(lia)) as HR. cbn [Z.eqb Pos.eqb] in HR.
  pose proof (INVD_wr m1 _ (3 * (ch * ns + s) + 0) I0 ltac:(nia)) as HS.
  step. step. step. step. step. clear HR HS. do_store I0 I1 (3 * (ch * ns + s) + 0).
  pose proof (INVD_rd _ _ ch s 1 I1 ltac:(lia) ltac:(lia) ltac:(lia)) as HR. cbn [Z.eqb Pos.eqb] in HR.
  pose proof (INVD_wr _ _ (3 * (ch * ns + s) + 1) I1 ltac:(nia)) as HS.
  step. step. step. clear HR HS. do_store I1 I2 (3 * (ch * ns + s) + 1).
  pose proof (INVD_rd _ _ ch s 2 I2 ltac:(lia) ltac:(lia) ltac:(lia)) as HR. cbn [Z.eqb Pos.eqb] in HR.
  pose proof (INVD_wr _ _ (3 * (ch * ns + s) + 2) I2 ltac:(nia)) as HS.
  step. step. clear HR HS. do_store I2 I3 (3 * (ch * ns + s) + 2).
  step. step. step.
  brq BR.
  - eapply CONT; [rewrite unsigned_lit by lia; lia | eapply INVD_idx; [exact I3 | lia]].
  - eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1));
      [ reflexivity | lia | rewrite unsigned_lit by nia; nia | rewrite unsigned_lit by lia; lia
      | eapply INVD_idx; [exact I3 | lia] | exact CONT ].
Qed.

Lemma rd_outer : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x8 = out + 3 * (ch * ns) -> bv_unsigned x10 = ch -> x11 = Z_to_bv 64 nch -> x12 = Z_to_bv 64 ns ->
  bv_unsigned x13 = ch -> bv_unsigned x14 = raw + 50 -> bv_unsigned x15 = 3 * ns -> bv_unsigned x16 = 3 * nch ->
  INVD m1 (3 * (ch * ns)) ->
  evt rsegs PostD (STATE 0x13708 m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 HK Hch H8 H10 E11 E12 H13 H14 H15 H16 I0.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (nch <= 480 /\ ns <= 480) by nia.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  apply wv in H8, H10, H13, H14, H15, H16. subst x8 x10 x11 x12 x13 x14 x15 x16.
  do 12 step.
  rewrite (unsigned_lit ch) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (ch * 2 ^ 2)) by lia.
  rewrite land_m8, land_m2 by lia. rewrite !land1.
  assert (P : ch mod 2 = 0 \/ ch mod 2 = 1) by lia.
  assert (EQ5 : bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 (ch mod 2)) 1)
    + -1))) 5)) = 5 * (ch mod 2)) by (destruct P as [P|P]; rewrite P; vm_compute; reflexivity).
  eapply (rd_inner ch) with (K := Z.to_nat (ns - 0)) (s := 0);
    [ lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | exact EQ5 | reflexivity | lia
    | rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8))) by (Z.div_mod_to_equations; lia);
      rewrite (unsigned_lit (2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
      rewrite unsigned_lit by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia
    | rewrite unsigned_lit by lia; lia | eapply INVD_idx; [exact I0 | lia] | ].
  intros m2 y5 y8 y29 y30 H8' I2. apply wv in H8'. subst y8.
  step. rewrite (unsigned_lit ch) by lia. rewrite swrap32_id by lia.
  step. step.
  brq BR.
  - assert (EN : nch * ns = ch * ns + ns) by (replace nch with (ch + 1) by lia; ring).
    step.
    destruct I2 as (HB2 & HF2 & ST2 & HW2 & MU2 & WM2 & HP2).
    eapply rd_exit with (r := ns); [exact HF2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. split; [exact MU2|]. apply INVD_out. apply (INVD_idx m2 (3 * (ch * ns + ns))); [|lia].
    exact (conj HB2 (conj HF2 (conj ST2 (conj HW2 (conj MU2 (conj WM2 HP2)))))).
  - eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1));
      [ reflexivity | lia | rewrite unsigned_lit by lia; nia | rewrite unsigned_lit by lia; lia | reflexivity
      | reflexivity | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia | eapply INVD_idx; [exact I2 | nia] ].
Qed.

End RD.

Ltac ucalc ns nch :=
  rewrite ?(unsigned_lit ns), ?(unsigned_lit nch) by lia; rewrite ?Z.shiftl_mul_pow2 by lia;
  rewrite ?unsigned_lit by nia; nia.

Theorem reac_decode_holds : reac_frame_inspect_contract -> reac_decode_contract.
Proof.
  intros HI. unfold reac_decode_contract, REAC_DECODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO.
  subst a0 a2 a3.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 9 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_cut; [eapply (HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 bs) |] end.
  { intros L. destruct (HB L) as [LEN BB]. split; [exact LEN|]. rewrite unsigned_lit by lia.
    eapply bytes_at_transport; [exact BB | exact MU |]. cbn [disjoint_from]. rewrite LEN.
    specialize (DR L). split; [lia | exact I]. }
  intros ms' (a1' & a2' & ->).
  replace (ret_pc (Z_to_bv 64 79544)) with (Z_to_bv 64 79544) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. rewrite inspect_valid_bit. step. step.
  destruct (inspect_wf (bv_unsigned a1) bs) eqn:W.
  2:{ if_true.
      assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false) by (unfold decode_ok; rewrite W; reflexivity).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  if_false.
  assert (L : bv_unsigned a1 = 1492) by (unfold inspect_wf in W; rewrite !andb_true_iff, !Z.eqb_eq in W; tauto).
  destruct (HB L) as [LEN BB]. specialize (DR L).
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
  apply bytes_at_app in HM. destruct HM as [HM1 HM2]. rewrite length_le4 in HM2.
  replace (mode + 4 + Z.of_nat 4) with (mode + 8) in HM2 by lia.
  pose proof (rd_all _ _ _ HM1) as HR1. rewrite length_le4 in HR1.
  pose proof (rd_all _ _ _ HM2) as HR2. rewrite length_le4 in HR2.
  step. rewrite sx32_lit by lia.
  step. rewrite lts0_lit by lia. brq BN.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  step. rewrite (unsigned_lit nch) by lia. rewrite land1.
  step. brq BE.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  step. step. rewrite sextw_zx32 by lia.
  step. rewrite lts0_lit by lia. brq BS.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  rewrite zx32_lit by lia.
  assert (0 <= ns * nch < 2^62) by nia.
  step. step. step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia. brq BM.
  { assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  assert (PO : decode_ok (bv_unsigned a1) bs nch ns = true) by (rewrite decode_ok_spec; split; [exact W | lia]).
  destruct (HO PO) as (HW & HoutN & DOR & DOS).
  do 7 step.
  assert (I0 : INVD ra sp s0 s1 s2 m bs raw out nch ns lo m1 0).
  { split; [|split; [exact FR|split; [exact ST|split; [|split; [|split; [exact WM|]]]]]].
    - eapply bytes_at_transport; [exact BB | exact MU |]. cbn [disjoint_from]. rewrite LEN. split; [lia | exact I].
    - eapply wr_at_transport; [exact HW | exact WM].
    - apply munch_extend. exact MU.
    - intros i Hi. lia. }
  eapply (rd_outer ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 a1 F fc m bs raw mode out nch ns lo)
    with (K := Z.to_nat (nch - 0)) (ch := 0).
  all: first [ assumption | reflexivity | lia | (eapply INVD_idx; [exact I0 | lia]) | ucalc ns nch ].
Qed.

