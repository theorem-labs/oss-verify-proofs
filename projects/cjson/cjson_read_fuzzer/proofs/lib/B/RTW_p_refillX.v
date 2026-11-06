(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_scommon_lg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_snp3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_emb.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_oom_an.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_scommon_lg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_snp3.RTW_sec_snp1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_snp3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_p_oom_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_oom_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma upd_mid : forall {X} (a : list X) (y : X) (c : list X) (b : X), upd (a ++ y :: c) (length a) b = a ++ b :: c.
Proof. induction a as [|z a IH]; intros y c b; cbn; [reflexivity| f_equal; apply IH]. Qed.
Lemma upd_mid' : forall {X} (a : list X) (y : X) (c : list X) (b : X) n, n = length a -> upd (a ++ y :: c) n b = a ++ b :: c.
Proof. intros X a y c b n ->. apply upd_mid. Qed.

Lemma firstn4_le8_small : forall d, 0 <= d < 256 -> firstn 4 (le8 (Z_to_bv 64 d)) = le4 (Z_to_bv 64 d).
Proof.
  intros d Hd. unfold le8, le4, word_to_le_bytes. rewrite !unsigned_lit by lia.
  cbn -[Z.modulo Z.div Z_to_bv bv_unsigned Z.pow Z.shiftr]. unfold Z_to_le_bytes. cbn -[Z.modulo Z.div Z_to_bv bv_unsigned Z.shiftr Z.pow].
  reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint words_of (n : nat) (bs : list byte) : list word :=
  match n with O => [] | S n' => le_bytes_to_word (firstn 8 bs) :: words_of n' (skipn 8 bs) end.
Lemma words_of_length : forall n bs, length (words_of n bs) = n.
Proof. induction n; intros bs; cbn; [reflexivity| f_equal; apply IHn]. Qed.
Lemma u64s_words_of : forall n bs, length bs = (8 * n)%nat -> u64s (words_of n bs) = bs.
Proof.
  induction n as [|n IH]; intros bs Hl; cbn -[le8 firstn skipn].
  - destruct bs; [reflexivity| cbn in Hl; lia].
  - rewrite rt_le8_of_bytes by (rewrite length_firstn; lia). rewrite IH by (rewrite length_skipn; lia). apply firstn_skipn.
Qed.
Lemma u64arr_of_u8arr : forall n m A bs, u8arr bsegs m A bs -> length bs = (8 * n)%nat ->
  exists ws, length ws = n /\ u64arr bsegs m A ws.
Proof.
  intros n m A bs [BY WR] Hl. exists (words_of n bs). split; [apply words_of_length|].
  split; [rewrite u64s_words_of by exact Hl; exact BY| rewrite words_of_length; replace (8 * Z.of_nat n) with (Z.of_nat (length bs)) by lia; exact WR].
Qed.

Lemma skipn_cons_nth : forall {X} (l : list X) n (d : X), (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
Proof. induction l as [|x l IH]; intros [|n] d H; cbn in H |- *; try lia; [reflexivity| apply IH; lia]. Qed.

Lemma buf_step : forall (buf ds : list byte) (c : nat) (b : byte), (c + length ds < length buf)%nat ->
  upd (firstn c buf ++ ds ++ skipn (c + length ds) buf) (c + length ds) b = firstn c buf ++ (ds ++ [b]) ++ skipn (c + length (ds ++ [b])) buf.
Proof.
  intros buf ds c b H.
  assert (Lp : (c + length ds)%nat = length (firstn c buf ++ ds)) by (rewrite length_app, length_firstn; lia).
  rewrite (skipn_cons_nth buf (c + length ds) b) by lia.
  rewrite (app_assoc (firstn c buf) ds). rewrite (upd_mid' _ _ _ _ _ Lp).
  rewrite length_app. cbn [length]. rewrite <- !app_assoc. cbn [app]. do 2 f_equal. f_equal. f_equal. lia.
Qed.

Lemma lor48_digit : forall d, 0 <= d <= 9 -> Z.lor d 48 = d + 48.
Proof.
  intros d Hd. assert (H : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.
Lemma land254_digit : forall d, 0 <= d <= 9 -> Z.land d 254 <= 9.
Proof.
  intros d Hd. assert (H : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; apply Z.leb_le; vm_compute; reflexivity.
Qed.

Lemma u64arr_read4_small : forall m A ws (i d : Z) a, u64arr bsegs m A ws -> nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 d) ->
  0 <= d < 256 -> 0 <= i -> a = wa (A + 8 * i) -> ov_read_bytes bsegs m a 4 = Some (le4 (Z_to_bv 64 d)).
Proof.
  intros m A ws i d a [BY _] Hn Hd Hi ->.
  (nelim (u64s_split _ _ _ Hn) 6%nat; intros pre post E Hlen Eu Hlu).
  replace (8 * i) with (Z.of_nat (8 * Z.to_nat i)) by lia.
  rewrite (bytes_at_read bsegs m A (u64s ws) (Z.of_nat (8 * Z.to_nat i)) 4 BY) by (try lia; rewrite Nat2Z.id, Eu, !length_app, length_le8, Hlu; lia).
  rewrite Nat2Z.id, Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app. rewrite length_le8. replace (4 - 8)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
  rewrite firstn4_le8_small by lia. reflexivity.
Qed.

Lemma land_ones64 : forall x, Z.land x 18446744073709551615 = x mod 2^64.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.
Lemma land_ones32 : forall x, Z.land x 4294967295 = x mod 2^32.
Proof. intros x. change 4294967295 with (Z.ones 32). apply Z.land_ones. lia. Qed.
Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx.
  assert (E : 18446744073709551615 - x = Z.lnot x mod 2^64).
  { unfold Z.lnot. rewrite <- Z.sub_1_r. replace (- x - 1) with ((18446744073709551615 - x) + (-1) * 2^64) by lia.
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
  rewrite E. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases i 64) as [L|L].
  - rewrite Z.ones_spec_low, Z.mod_pow2_bits_low, Z.lnot_spec by lia. apply Bool.xorb_true_r.
  - rewrite Z.ones_spec_high, Z.mod_pow2_bits_high by lia. rewrite Bool.xorb_false_r.
    destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma zbv_eqm : forall x y, x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. rewrite <- (Z_to_bv_mod64 x), <- (Z_to_bv_mod64 y). f_equal. exact H. Qed.
Ltac swrap_arith :=
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z; change (4294967296 `div` 2)%Z with 2147483648%Z;
  rewrite ?land_ones64, ?land_ones32; rewrite ?lxor_ones64 by (Z.div_mod_to_equations; lia);
  rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2^3)%Z with 8%Z; try change (2^32)%Z with 4294967296%Z; try change (2^29)%Z with 536870912%Z;
  Z.div_mod_to_equations; lia.
Ltac breg r v := let old := reg_val r in replace old with (Z_to_bv 64 v : word) by (apply zbv_eqm; swrap_arith).

(* [comment removed for export] *)
Section AN10.
  Variables (sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (BP bend B cur v N lo : Z) (buf : list byte).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 336 <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp + 8 <= 2^47.
  Hypothesis HV : 1 <= v < 10 ^ N.
  Hypothesis HN : 1 <= N <= 19.
  (* [comment removed for export] *)
  Hypothesis HBP : bv_unsigned sp <= BP /\ BP + 8 <= 2^47.
  Hypothesis HB : bv_unsigned sp <= B /\ B + Z.of_nat (length buf) <= 2^47.
  Hypothesis HBPB : BP + 8 <= B \/ B + Z.of_nat (length buf) <= BP.
  Hypothesis HCUR : 0 <= cur /\ B + cur + N <= bend /\ bend <= B + Z.of_nat (length buf).
  Let NB : Z := bv_unsigned sp + -328.   (* [comment removed for export] *)

  Ltac gi := lstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia | _ => idtac end.

  (* [comment removed for export] *)
  Lemma an10_A : forall (ra t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (POST : machine_state -> Prop),
    4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
    (forall (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte) (j8 : list byte) (ws : list word),
       munch [(bv_unsigned sp + -336, bv_unsigned sp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       stk bsegs m1 lo (bv_unsigned sp + -336) -> an_hi sp s2 s3 s4 s5 s6 s7 s8 s9 ra s0 s1 m1 ->
       rw_cells bsegs m1 (bv_unsigned sp + -336) [CB 8 j8] -> u64arr bsegs m1 NB ws -> length ws = 30%nat ->
       evt bsegs POST
         (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz 0) (wz 30) (wz 0) x13 x14 x15 x16 x17
                  (wz 0) (wz 0) (wz 10) (wz v) (wz NB) (wz 0) (wz 1) (wz 0) s10 s11 x28 x29 x30 x31)
             F (wz 0x68fec) fc None m1 (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz BP) (wz bend) (wz v) (wz 10) (wz 0) (wz 0) (wz 0) (wz 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_APPNUM) fc None m (seg_rom bsegs)).
  Proof.
    intros until POST. intros RA1 RA2 K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (munch_refl [(bv_unsigned sp + -336, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (V64 : v < 2^64). { assert (10 ^ N <= 10 ^ 19) by (apply Z.pow_le_mono_r; lia). change (10^19) with 10000000000000000000 in H. lia. }
    unfold A_APPNUM. cbv beta delta [wz] in *.
    carve_frame 336%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 240; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 12 lstep. (* [comment removed for export] *)
    do 7 gi. (* [comment removed for export] *)
    gi. gi. gi. (* [comment removed for export] *)
    gi. gi. (* [comment removed for export] *)
    gi. gi. gi. gi. fl. (* [comment removed for export] *)
    gi. (* [comment removed for export] *)
    gi. gi. gi. gi. gi. fl. (* [comment removed for export] *)
    replace (bv_unsigned sp + -336 + 8) with NB by (unfold NB; lia).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
        pose proof (proj1 (RT_kit.rw_cells_app mm (bv_unsigned sp + -336) [c0] (c1 :: rest)) FR) as [FR8 FRa];
        pose proof (proj1 (RT_kit.rw_cells_app mm _ [c1] rest) FRa) as [FRnb FRhi]; clear FR FRa;
        cbn [cells_size Cells.csize Nat.add] in FRnb, FRhi
      end end.
    replace (bv_unsigned sp + -336 + Z.of_nat 8) with NB in FRnb, FRhi by (unfold NB; lia).
    replace (NB + Z.of_nat 240) with (bv_unsigned sp + -88) in FRhi by (unfold NB; lia).
    lstep. (* [comment removed for export] *)
    eapply evt_cut; [eapply (ims240 sp) with (P := NB); [exact FRnb| assumption| unfold NB; lia| unfold NB; lia]|].
    cbv beta. intros ms1 nelH_; (nelim nelH_ 10%nat; intros a1' a2' a3' m1 j240 -> MU1 WM1 MI1 FRnb1).
    replace (ret_pc (Z_to_bv 64 0x68fdc)) with (Z_to_bv 64 0x68fdc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim (u64arr_of_u8arr 30 m1 NB j240 (u8arr_of_rw_cells bsegs _ _ _ _ FRnb1) ltac:(exact (RTW_sec_snp3.cb_len _ _ _ _ _ FRnb1))) 3%nat; intros ws WL WA).
    lstep. lstep. lstep. fl. lstep. (* [comment removed for export] *)
    eapply K.
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. unfold NB, sub_fp. cbn. intros; lia.
    - exact (wmono_trans bsegs _ _ _ WM WM1).
    - exact MI1.
    - eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| unfold NB; cbn; lia].
    - unfold an_hi. eapply rw_cells_transport; [exact FRhi| exact MU1| exact WM1| unfold NB; cbn; lia].
    - eapply rw_cells_transport; [exact FR8| exact MU1| exact WM1| unfold NB; cbn; lia].
    - exact WA.
    - exact WL.
  Qed.

  (* [comment removed for export] *)
  Lemma an10_digits : forall (cnt : nat) (k u : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mk : word -> option byte) (ws : list word)
      (POST : machine_state -> Prop),
    mem_inv bsegs mk -> u64arr bsegs mk NB ws -> length ws = 30%nat ->
    0 <= k -> k + 1 <= N -> 1 <= u -> u < 10 ^ (N - k) ->
    (forall j, 0 <= j < k -> exists d, nth_error ws (Z.to_nat j) = Some (wz d) /\ 0 <= d <= 9) ->
    Z.of_nat cnt = N - k ->
    (forall (nd ul : Z) (y13 y14 : word) (mk' : word -> option byte) (ws' : list word),
       k + 1 <= nd <= N -> 1 <= ul <= 9 -> mem_inv bsegs mk' -> munch [(NB, NB + 240)] mk mk' -> wmono bsegs mk mk' ->
       u64arr bsegs mk' NB ws' -> length ws' = 30%nat ->
       (forall j, 0 <= j < nd -> exists d, nth_error ws' (Z.to_nat j) = Some (wz d) /\ 0 <= d <= 9) ->
       nth_error ws' (Z.to_nat (nd - 1)) = Some (wz ul) ->
       evt bsegs POST
         (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (- nd)) (wz (30 - nd)) (wz (- (8 * nd))) y13 y14 x15 x16 x17
                  (wz 0) (wz 0) (wz 10) (wz 0) (wz (NB + 8 * nd)) (wz 0) (wz 1) (wz 0) s10 s11 x28 x29 x30 x31)
             F (wz 0x69018) fc None mk' (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (- k)) (wz (30 - k)) (wz (- (8 * k))) x13 x14 x15 x16 x17
               (wz 0) (wz 0) (wz 10) (wz u) (wz (NB + 8 * k)) (wz 0) (wz 1) (wz 0) s10 s11 x28 x29 x30 x31)
          F (wz 0x68fec) fc None mk (seg_rom bsegs)).
  Proof.
    intros cnt. induction cnt as [cnt IH] using lt_wf_ind.
    intros until POST. intros MIk UA WL Hk HkN Hu1 Hu2 DIG Hcnt K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (munch_refl [(NB, NB + 240)] mk) as MU. pose proof (wmono_refl bsegs mk) as WM.
    assert (ENB : NB = bv_unsigned sp + -328) by reflexivity. clearbody NB.
    assert (P10 : 0 < 10 ^ (N - k)) by (apply Z.pow_pos_nonneg; lia).
    assert (U64 : u < 2^64). { assert (10 ^ (N - k) <= 10 ^ 19) by (apply Z.pow_le_mono_r; lia). change (10^19) with 10000000000000000000 in H. lia. }
    assert (Q1 : 0 <= u / 10 <= u) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    assert (Q2 : 0 <= u - u / 10 * 10 <= 9) by (Z.div_mod_to_equations; lia).
    cbv beta delta [wz] in *.
    gi. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) rewrite (an_divu_lit u 10) by lia.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    breg 10 (- (k + 1)).
    set (d := u - u / 10 * 10) in *.
    pose proof (u64arr_store_ok bsegs _ _ _ k (Z_to_bv 64 (NB + 8 * k)) UA ltac:(lia) eq_refl) as SOK.
    lstep. (* [comment removed for export] *)
    pose proof (u64arr_write bsegs _ _ _ k (Z_to_bv 64 d) UA ltac:(lia)) as UA'. clear UA. store_done.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) breg 12 (- (8 * (k + 1))).
    assert (DIG' : forall j, 0 <= j < k + 1 -> exists d', nth_error (upd ws (Z.to_nat k) (Z_to_bv 64 d)) (Z.to_nat j) = Some (wz d') /\ 0 <= d' <= 9).
    { intros j Hj. destruct (Z.eq_dec j k) as [->|NE].
      - exists d. split; [apply nth_error_upd_same; lia| lia].
      - (nelim (DIG j ltac:(lia)) 3%nat; intros d' Hd' Rd'). exists d'. split; [rewrite nth_error_upd_other by lia; exact Hd'| exact Rd']. }
    replace (NB + 8 * k + 8) with (NB + 8 * (k + 1)) by lia. replace (30 - k + -1) with (30 - (k + 1)) by lia.
    lstep. (* [comment removed for export] *)
    if_cases Kgo; zify_cond Kgo.
    - (* [comment removed for export] *)
      eapply (IH (cnt - 1)%nat ltac:(lia) (k + 1) (u / 10)); [eassumption| exact UA'| rewrite upd_length; exact WL| lia| | lia| | exact DIG'| lia|].
      + (* [comment removed for export] *)
        destruct (Z_lt_le_dec (k + 1) N) as [|GE]; [lia|]. exfalso. assert (E : N - k = 1) by lia. rewrite E in Hu2. change (10 ^ 1) with 10 in Hu2. lia.
      + replace (N - (k + 1)) with (N - k - 1) by lia. apply Z.div_lt_upper_bound; [lia|].
        replace (10 * 10 ^ (N - k - 1)) with (10 ^ (N - k)); [lia|]. rewrite <- Z.pow_succ_r by lia. f_equal. lia.
      + intros nd ul y13 y14 mk' ws' Hnd Hul MI' MU' WM' UA2 WL2 DIG2 TOP. eapply K; [lia| exact Hul| exact MI'| | | exact UA2| exact WL2| exact DIG2| exact TOP].
        * eapply munch_trans; [exact MU| exact MU'].
        * eapply wmono_trans; [exact WM| exact WM'].
    - (* [comment removed for export] *)
      replace (u / 10) with 0 by (symmetry; apply Z.div_small; lia).
      assert (Ed : d = u) by (subst d; rewrite (Z.div_small u 10) by lia; lia).
      eapply (K (k + 1) d); [lia| lia| eassumption| exact MU| exact WM| exact UA'| rewrite upd_length; exact WL| exact DIG'|].
      replace (k + 1 - 1) with k by lia. apply nth_error_upd_same. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma an10_C : forall (nd ul : Z) (x5 x6 x7 y13 y14 x15 x16 x17 x28 x29 x30 x31 : word) (mk : word -> option byte) (ws : list word) (POST : machine_state -> Prop),
    mem_inv bsegs mk -> u64arr bsegs mk NB ws -> length ws = 30%nat -> 1 <= nd <= N -> 1 <= ul <= 9 ->
    nth_error ws (Z.to_nat (nd - 1)) = Some (wz ul) -> rw_cells bsegs mk BP [C8 (wz (B + cur))] ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (nd - 1)) (wz nd) (wz 87) (wz (B + cur)) (wz (NB + 8 * (nd - 1))) (wz 10) x16 x17
               (wz 0) (wz 0) (wz nd) (wz 0) (wz (NB + 8 * nd)) (wz 0) (wz 1) (wz 0) s10 s11 x28 x29 x30 x31)
          F (wz 0x6917c) fc None mk (seg_rom bsegs)) ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (- nd)) (wz (30 - nd)) (wz (- (8 * nd))) y13 y14 x15 x16 x17
               (wz 0) (wz 0) (wz 10) (wz 0) (wz (NB + 8 * nd)) (wz 0) (wz 1) (wz 0) s10 s11 x28 x29 x30 x31)
          F (wz 0x69018) fc None mk (seg_rom bsegs)).
  Proof.
    intros until POST. intros MIk UA WL Hnd Hul TOP HPC K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    assert (ENB : NB = bv_unsigned sp + -328) by reflexivity. clearbody NB.
    cbv beta delta [wz] in *.
    lstep. (* [comment removed for export] *) breg 20 nd.
    gi. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) breg 11 (nd - 1).
    gi. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) breg 10 nd.
    lstep. (* [comment removed for export] *) replace (bv_unsigned sp + -336 + 8) with NB by lia.
    lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *) breg 13 (NB + 8 * (nd - 1)).
    pose proof (u64arr_read bsegs _ _ _ (nd - 1) (Z_to_bv 64 ul) (Z_to_bv 64 (NB + 8 * (nd - 1))) UA TOP ltac:(lia) eq_refl) as RD.
    lstep. (* [comment removed for export] *) try rewrite le_bytes_to_word_le8.
    gi. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    gi. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    gi. (* [comment removed for export] *)
    gi. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    gi. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    breg 10 (nd - 1). breg 11 nd. breg 14 (NB + 8 * (nd - 1)).
    exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma an10_out : forall (cnt : nat) (j nd : Z) (x5 x6 x7 x16 x17 x28 x29 x30 x31 : word) (mk : word -> option byte) (ws : list word) (ds : list byte)
      (POST : machine_state -> Prop),
    mem_inv bsegs mk -> u64arr bsegs mk NB ws -> length ws = 30%nat ->
    (forall i, 0 <= i < nd -> exists d, nth_error ws (Z.to_nat i) = Some (wz d) /\ 0 <= d <= 9) ->
    1 <= j <= nd -> nd <= N -> Z.of_nat cnt = j ->
    rw_cells bsegs mk BP [C8 (wz (B + cur + (nd - j)))] ->
    u8arr bsegs mk B (firstn (Z.to_nat cur) buf ++ ds ++ skipn (Z.to_nat cur + length ds) buf) -> Z.of_nat (length ds) = nd - j -> msg_ok ds ->
    (forall (y16 y17 : word) (mk' : word -> option byte) (ds' : list byte),
       mem_inv bsegs mk' -> munch [(BP, BP + 8); (B + cur, B + cur + nd)] mk mk' -> wmono bsegs mk mk' ->
       rw_cells bsegs mk' BP [C8 (wz (B + cur + nd))] ->
       u8arr bsegs mk' B (firstn (Z.to_nat cur) buf ++ ds' ++ skipn (Z.to_nat cur + length ds') buf) -> Z.of_nat (length ds') = nd -> msg_ok ds' ->
       evt bsegs POST
         (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (nd - 1)) (wz 0) (wz 87) (wz (B + cur + nd)) (wz (NB + 8 * (0 - 1))) (wz 10) y16 y17
                  (wz 0) (wz 0) (wz nd) (wz 0) (wz (NB + 8 * nd)) (wz 0) (wz 1) (wz 0) s10 s11 x28 x29 x30 x31)
             F (wz 0x690f4) fc None mk' (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (nd - 1)) (wz j) (wz 87) (wz (B + cur + (nd - j))) (wz (NB + 8 * (j - 1))) (wz 10) x16 x17
               (wz 0) (wz 0) (wz nd) (wz 0) (wz (NB + 8 * nd)) (wz 0) (wz 1) (wz 0) s10 s11 x28 x29 x30 x31)
          F (wz 0x6917c) fc None mk (seg_rom bsegs)).
  Proof.
    intros cnt. induction cnt as [cnt IH] using lt_wf_ind.
    intros until POST. intros MIk UA WL DIG Hj HndN Hcnt HPC UB LDS OK K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    assert (ENB : NB = bv_unsigned sp + -328) by reflexivity. clearbody NB.
    pose proof (munch_refl [(BP, BP + 8); (B + cur, B + cur + nd)] mk) as MU. pose proof (wmono_refl bsegs mk) as WM.
    (nelim (DIG (j - 1) ltac:(lia)) 3%nat; intros d Hd Rd).
    assert (LFB : length (firstn (Z.to_nat cur) buf ++ ds ++ skipn (Z.to_nat cur + length ds) buf) = length buf).
    { rewrite !length_app, length_firstn, length_skipn. lia. }
    cbv beta delta [wz] in *.
    gi. (* [comment removed for export] *)
    pose proof (u64arr_read4_small mk NB ws (j - 1) d (Z_to_bv 64 (NB + 8 * (j - 1))) UA Hd ltac:(lia) ltac:(lia) eq_refl) as RD.
    lstep. (* [comment removed for export] *) try rewrite sext_extract_le4. rewrite sx32_lit by lia.
    lstep. (* [comment removed for export] *) pose proof (land254_digit d Rd) as L254.
    gi. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) rewrite (lor48_digit d Rd).
    lstep. (* [comment removed for export] *)
    pose proof (u8arr_store_ok bsegs _ _ _ (cur + (nd - j)) (Z_to_bv 64 (B + cur + (nd - j))) UB ltac:(rewrite LFB; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    lstep. (* [comment removed for export] *) rewrite RTW_m_lib2.le1_lit.
    pose proof (u8arr_write bsegs _ _ _ (cur + (nd - j)) (Z_to_bv 8 (d + 48)) UB ltac:(rewrite LFB; lia)) as UB'. clear UB.
    replace (B + (cur + (nd - j))) with (B + cur + (nd - j)) in UB' by lia.
    replace (Z.to_nat (cur + (nd - j))) with (Z.to_nat cur + length ds)%nat in UB' by lia.
    rewrite buf_step in UB' by lia.
    assert (LF1 : length (firstn (Z.to_nat cur) buf) = Z.to_nat cur) by (rewrite length_firstn; lia).
    assert (LS1 : length (skipn (Z.to_nat cur + (length ds + 1)) buf) = (length buf - (Z.to_nat cur + (length ds + 1)))%nat) by (rewrite length_skipn; lia).
    store_done.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    assert (OK' : msg_ok (ds ++ [Z_to_bv 8 (d + 48)])).
    { apply msg_ok_app; [exact OK|]. constructor; [| constructor]. rewrite unsigned_lit8 by lia. lia. }
    assert (LDS' : Z.of_nat (length (ds ++ [Z_to_bv 8 (d + 48)])) = nd - (j - 1)) by (rewrite length_app; cbn [length]; lia).
    replace (B + cur + (nd - j) + 1) with (B + cur + (nd - (j - 1))) in * by lia.
    replace (NB + 8 * (j - 1) + -8) with (NB + 8 * ((j - 1) - 1)) in * by lia.
    lstep. (* [comment removed for export] *)
    if_cases Kend; zify_cond Kend.
    - (* [comment removed for export] *)
      assert (Ej : j = 1) by lia. clear Hcnt IH. subst j.
      replace (nd - (1 - 1)) with nd in * by lia. replace (1 + -1) with 0 by lia. replace (1 - 1 - 1) with (0 - 1) by lia.
      eapply K; [eassumption| exact MU| exact WM| eassumption| exact UB'| exact LDS'| exact OK'].
    - replace (j + -1) with (j - 1) by lia.
      eapply (IH (cnt - 1)%nat ltac:(lia) (j - 1) nd); [eassumption| exact UA| exact WL| exact DIG| lia| lia| lia| eassumption| exact UB'| exact LDS'| exact OK'|].
      + intros y16 y17 mk' ds' MI' MU' WM' HPC' UB2 LDS2 OK2. eapply K; [exact MI'| | | exact HPC'| exact UB2| exact LDS2| exact OK2].
        * eapply munch_trans; [exact MU| exact MU'].
        * eapply wmono_trans; [exact WM| exact WM'].
  Qed.

  (* [comment removed for export] *)
  Lemma nb_chunk : forall mk ws, u64arr bsegs mk NB ws -> length ws = 30%nat -> rw_cells bsegs mk NB [CB 240 (u64s ws)].
  Proof.
    intros mk ws [BY WR] WL. replace 240%nat with (length (u64s ws)) by (rewrite u64s_length; lia).
    apply rw_cells_of_u8arr. split; [exact BY|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact WR.
  Qed.

  (* [comment removed for export] *)
  Lemma an10_fin : forall (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) (nd : Z)
      (mk : word -> option byte) (ws : list word) (j8 : list byte) (POST : machine_state -> Prop),
    mem_inv bsegs mk -> 1 <= nd <= N -> 4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
    stk bsegs mk lo (bv_unsigned sp + -336) -> an_hi sp s2 s3 s4 s5 s6 s7 s8 s9 ra s0 s1 mk ->
    rw_cells bsegs mk (bv_unsigned sp + -336) [CB 8 j8] -> u64arr bsegs mk NB ws -> length ws = 30%nat ->
    (stk bsegs mk lo (bv_unsigned sp) ->
     evt bsegs POST
       (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz nd) (wz 0) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
           F (ret_pc ra) fc None mk (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR (wz 0x68fdc) (Z_to_bv 64 (bv_unsigned sp + -336)) gp tp x5 x6 x7 (wz bend) (wz BP) (wz (nd - 1)) (wz 0) x12 x13 x14 x15 x16 x17
               (wz 0) (wz 0) x20 (wz 0) (wz (NB + 8 * nd)) (wz 0) (wz 1) (wz 0) s10 s11 x28 x29 x30 x31)
          F (wz 0x690f4) fc None mk (seg_rom bsegs)).
  Proof.
    intros until POST. intros MIk Hnd RA1 RA2 STk FRhi FR8 UA WL K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    assert (ENB : NB = bv_unsigned sp + -328) by reflexivity.
    pose proof (nb_chunk mk ws UA WL) as FRnb. clearbody NB.
    unfold an_hi in FRhi. cbv beta delta [wz] in *.
    lstep. (* [comment removed for export] *) breg 10 nd.
    do 11 lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    rewrite ENB in FRnb. replace (bv_unsigned sp + -328) with (bv_unsigned sp + -336 + 8) in FRnb by lia.
    replace (bv_unsigned sp + -88) with (bv_unsigned sp + -336 + 248) in FRhi by lia.
    glue FR8 FRnb. glue FR8 FRhi. rename FR8 into FR.
    release_frame FR STk (bv_unsigned sp).
    lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
    apply K. exact STk.
  Qed.

  (* [comment removed for export] *)
  Lemma appnum10_spec : forall (ra t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (POST : machine_state -> Prop),
    4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
    rw_cells bsegs m BP [C8 (wz (B + cur))] -> u8arr bsegs m B buf ->
    (forall (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : word -> option byte) (ds : list byte) (nd : Z),
       1 <= nd <= N -> mem_inv bsegs m' ->
       munch [(bv_unsigned sp - 336, bv_unsigned sp); (BP, BP + 8); (B + cur, B + cur + nd)] m m' -> wmono bsegs m m' ->
       stk bsegs m' lo (bv_unsigned sp) ->
       rw_cells bsegs m' BP [C8 (wz (B + cur + nd))] ->
       u8arr bsegs m' B (firstn (Z.to_nat cur) buf ++ ds ++ skipn (Z.to_nat cur + length ds) buf) -> Z.of_nat (length ds) = nd -> msg_ok ds ->
       evt bsegs POST
         (MS (mkR ra sp gp tp y5 y6 y7 s0 s1 (wz nd) y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz BP) (wz bend) (wz v) (wz 10) (wz 0) (wz 0) (wz 0) (wz 0) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_APPNUM) fc None m (seg_rom bsegs)).
  Proof.
    intros until POST. intros RA1 RA2 HPC UB K.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof CEIL as CEIL'. idtac.
    pose proof (u8arr_bound bsegs _ _ _ UB) as UBB || pose proof I as UBB.
    eapply an10_A; [exact RA1| exact RA2|].
    intros x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 j8 ws MU01 WM01 MI1 ST1 FRhi1 FR81 UA1 WL1.
    pose proof HPC as HPC1. eapply (rw_cells_transport bsegs _ m m1) in HPC1; [| exact MU01| exact WM01| cbn; lia].
    pose proof UB as UB1. eapply (u8arr_transport bsegs _ m m1) in UB1; [| exact MU01| exact WM01| cbn; lia].
    cbv beta delta [wz] in *.
    replace (Z_to_bv 64 NB : word) with (Z_to_bv 64 (NB + 8 * 0) : word) by (f_equal; lia).
    eapply (an10_digits (Z.to_nat N) 0 v); [exact MI1| exact UA1| exact WL1| lia| lia| lia| rewrite Z.sub_0_r; lia| intros j Hj; lia| lia|].
    intros nd ul y13 y14 m2 ws2 Hnd Hul MI2 MU12 WM12 UA2 WL2 DIG2 TOP2. cbv beta delta [wz] in *.
    assert (D12 : forall A n, bv_unsigned sp <= A -> 0 <= n -> disjoint_from [(NB, NB + 240)] A n) by (intros A n HA Hn; cbn; unfold NB; lia).
    pose proof HPC1 as HPC2. eapply (rw_cells_transport bsegs _ m1 m2) in HPC2; [| exact MU12| exact WM12| apply D12; lia].
    pose proof UB1 as UB2. eapply (u8arr_transport bsegs _ m1 m2) in UB2; [| exact MU12| exact WM12| apply D12; lia].
    eapply (an10_C nd ul); [exact MI2| exact UA2| exact WL2| lia| lia| exact TOP2| exact HPC2|].
    (* [comment removed for export] *)
    cbv beta delta [wz] in *.
    replace (Z_to_bv 64 (B + cur) : word) with (Z_to_bv 64 (B + cur + (nd - nd)) : word) by (f_equal; lia).
    replace (Z_to_bv 64 (B + cur) : word) with (Z_to_bv 64 (B + cur + (nd - nd)) : word) in HPC2 by (f_equal; lia).
    assert (EQL : buf = firstn (Z.to_nat cur) buf ++ [] ++ skipn (Z.to_nat cur + length (@nil byte)) buf).
    { cbn [length app]. rewrite Nat.add_0_r. symmetry. apply firstn_skipn. }
    rewrite EQL in UB2 at 1 || (pattern buf at 1 in UB2; rewrite EQL in UB2).
    eapply (an10_out (Z.to_nat nd) nd nd); [exact MI2| exact UA2| exact WL2| exact DIG2| lia| lia| lia| exact HPC2| exact UB2| cbn; lia| constructor|].
    intros y16 y17 m3 ds MI3 MU23 WM23 HPC3 UB3 LDS3 OK3. cbv beta delta [wz] in *.
    assert (D23 : forall A n, A + n <= bv_unsigned sp -> disjoint_from [(BP, BP + 8); (B + cur, B + cur + nd)] A n) by (intros A n HA; cbn; lia).
    eapply (an10_fin ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9); [exact MI3| lia| exact RA1| exact RA2| | | | | exact WL2|].
    - eapply stk_transport_disjoint; [eapply stk_transport_disjoint; [exact ST1| exact MU12| exact WM12| cbn; unfold NB; lia]| exact MU23| exact WM23| apply D23; lia].
    - unfold an_hi in *. eapply rw_cells_transport; [eapply rw_cells_transport; [exact FRhi1| exact MU12| exact WM12| cbn; unfold NB; lia]| exact MU23| exact WM23| apply D23; cbn; lia].
    - eapply rw_cells_transport; [eapply rw_cells_transport; [exact FR81| exact MU12| exact WM12| cbn; unfold NB; lia]| exact MU23| exact WM23| apply D23; cbn; lia].
    - eapply u64arr_transport; [exact UA2| exact MU23| exact WM23| apply D23; rewrite WL2; cbn; unfold NB; lia].
    - intros ST3. eapply K; [lia| exact MI3| | | exact ST3| exact HPC3| exact UB3| exact LDS3| exact OK3].
      + eapply munch_trans; [eapply munch_weaken; [| exact MU01]; intros x Hx; cbn in Hx |- *; lia|].
        eapply munch_trans; [eapply munch_weaken; [| exact MU12]; intros x Hx; cbn in Hx |- *; unfold NB in *; lia|].
        eapply munch_weaken; [| exact MU23]; intros x Hx; cbn in Hx |- *; lia.
      + eapply wmono_trans; [exact WM01|]. eapply wmono_trans; [exact WM12| exact WM23].
  Qed.
End AN10.


End CeilWrap.
(* [comment removed for export] *)
Ltac swrap_arith :=
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
  change (2 ^ Z.of_N 32)%Z with 4294967296%Z; change (4294967296 `div` 2)%Z with 2147483648%Z;
  rewrite ?land_ones64, ?land_ones32; rewrite ?lxor_ones64 by (Z.div_mod_to_equations; lia);
  rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2^3)%Z with 8%Z; try change (2^32)%Z with 4294967296%Z; try change (2^29)%Z with 536870912%Z;
  Z.div_mod_to_equations; lia.
Ltac breg r v := let old := reg_val r in replace old with (Z_to_bv 64 v : word) by (apply zbv_eqm; swrap_arith).
End RTW_oom_an.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
Module RTW_oom_vsn.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_scommon_lg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_snp3.RTW_sec_snp1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_snp3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_p_oom_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_oom_lib RTW_oom_an.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition litb (b : byte) : Prop := bv_unsigned b <> 0 /\ bv_unsigned b <> 37.

Lemma arr_eqv : forall m A xs ys, u8arr bsegs m A xs -> xs = ys -> u8arr bsegs m A ys.
Proof. intros m A xs ys H <-. exact H. Qed.
Lemma u8ro_of_ro_cells : forall m A n bs, ro_cells bsegs m A [CB n bs] -> u8ro bsegs m A bs.
Proof. intros m A n bs [_ Hb]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma u8ro_app_l : forall m A xs ys, u8ro bsegs m A (xs ++ ys) -> u8ro bsegs m A xs.
Proof. intros m A xs ys H. exact (proj1 (proj1 (bytes_at_app bsegs m A xs ys) H)). Qed.
Lemma u8ro_app_r : forall m A xs ys, u8ro bsegs m A (xs ++ ys) -> u8ro bsegs m (A + Z.of_nat (length xs)) ys.
Proof. intros m A xs ys H. exact (proj2 (proj1 (bytes_at_app bsegs m A xs ys) H)). Qed.
Lemma u8ro_cons_tl : forall m A x ys, u8ro bsegs m A (x :: ys) -> u8ro bsegs m (A + 1) ys.
Proof. intros m A x ys H. exact (u8ro_app_r m A [x] ys H). Qed.
Lemma u8ro_len_bound : forall m A bs, u8ro bsegs m A bs -> 0 <= A /\ A + Z.of_nat (length bs) <= 2^64.
Proof. intros m A bs H. exact (bytes_at_bound bsegs m A bs H). Qed.

(* [comment removed for export] *)
Lemma jt_s_cells : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x20bf0 [CB 4 (zbs [140; 124; 4; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x20bf0 (zbs [140; 124; 4; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.
Lemma jt_u_cells : forall m, mem_inv bsegs m -> ro_cells bsegs m 0x20bf8 [CB 4 (zbs [100; 124; 4; 0])].
Proof. intros m MI. apply (ro_cells_image bsegs m 0x20bf8 (zbs [100; 124; 4; 0]) MI); [vm_compute; reflexivity| lia| cbn; lia]. Qed.

(* [comment removed for export] *)
Lemma neg_small_tests : forall n, 0 < n < 2^63 ->
  (0 <? Z.land (- n) 18446744073709551615) && (Z.land (- n) 18446744073709551615 <? 9223372036854775808) = false.
Proof.
  intros n Hn. rewrite land_ones64. replace ((- n) mod 2^64) with (2^64 - n) by (Z.div_mod_to_equations; lia).
  apply Bool.andb_false_intro2. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Section VSN.
  (* [comment removed for export] *)
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (B VA lo : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 464 <= bv_unsigned sp.
  Hypothesis HB : bv_unsigned sp <= B /\ B + 400 <= VA.
  Hypothesis HVA : VA + 56 <= 2^47.

  Ltac gi := lstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia | _ => idtac end.
  Ltac prep :=
    let RSP := fresh "RSP" in
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
    let CEIL' := fresh "CEIL'" in pose proof CEIL as CEIL'.

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation LH ra x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mm :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 32) (Z_to_bv 64 cnt) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 va) (Z_to_bv 64 (B + 399)) (Z_to_bv 64 115) (Z_to_bv 64 37) (Z_to_bv 64 45) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 46)
             (Z_to_bv 64 fa) (Z_to_bv 64 108) x28 x29 x30 x31)
        F (Z_to_bv 64 0x686a4) fc None mm (seg_rom bsegs)).
  #[warnings="-notation-for-abbreviation"]
  Notation LX pc ra x5 x6 x7 cnt a0 a1 a2 a3 a4 x15 x16 x17 va fa x28 x29 x30 x31 mm :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 32) (Z_to_bv 64 cnt) a0 a1 a2 a3 a4 x15 x16 x17
             (Z_to_bv 64 va) (Z_to_bv 64 (B + 399)) (Z_to_bv 64 115) (Z_to_bv 64 37) (Z_to_bv 64 45) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 46)
             (Z_to_bv 64 fa) (Z_to_bv 64 108) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition vsn_lo (fmt : Z) (mm : word -> option byte) : Prop :=
    rw_cells bsegs mm (bv_unsigned sp + -128) [C8 (wz fmt); C8 (wz (B + 400))].
  Definition vsn_cur (cur : Z) (mm : word -> option byte) : Prop :=
    rw_cells bsegs mm (bv_unsigned sp + -112) [C8 (wz cur)].
  Definition vsn_hi (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mm : word -> option byte) : Prop :=
    rw_cells bsegs mm (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma vsn_A : forall (ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : word -> option byte) (fmt : Z)
      (POST : machine_state -> Prop),
    mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> 0 < fmt /\ fmt + 1 <= AIMG_HI ->
    (forall m1, mem_inv bsegs m1 -> munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 -> wmono bsegs m m1 ->
       stk bsegs m1 lo (bv_unsigned sp + -128) ->
       vsn_lo fmt m1 -> vsn_cur B m1 -> vsn_hi ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 ->
       evt bsegs POST (LH ra t0 t1 t2 0 (wz (B + 400)) (wz 400) (wz fmt) (wz VA) a4 a5 a6 a7 VA fmt t3 t4 t5 t6 m1)) ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz B) (wz 400) (wz fmt) (wz VA) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_VSNPRINTF) fc None m (seg_rom bsegs)).
  Proof using CEIL LO HB HVA.
    intros until POST. intros MI ST Hfmt K. prep.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold A_VSNPRINTF, AIMG_HI, vsn_lo, vsn_cur, vsn_hi in *. cbv beta delta [wz] in *.
    carve_frame 128%nat ST.
    apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 15 gi. (* [comment removed for export] *)
    gi. lstep. if_lit. (* [comment removed for export] *)
    do 16 (gi; try fl). (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
        pose proof (proj1 (RT_kit.rw_cells_app mm _ [c0; c1] (c2 :: rest)) FR) as [FRlo FRb]; cbn [cells_size Cells.csize Nat.add] in FRb;
        pose proof (proj1 (RT_kit.rw_cells_app mm _ [c2] rest) FRb) as [CUR FRhi]; cbn [cells_size Cells.csize Nat.add] in FRhi; clear FR FRb
      end end.
    replace (bv_unsigned sp + -128 + Z.of_nat 16) with (bv_unsigned sp + -112) in CUR, FRhi by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp + -104) in FRhi by lia.
    eapply K; [assumption| exact MU| exact WM| exact ST| exact FRlo| exact CUR| exact FRhi].
  Qed.

  (* [comment removed for export] *)
  Lemma vsn_lits : forall (seg pre rest : list byte) (ra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (cnt va fa lp ls : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    mem_inv bsegs mk -> u8ro bsegs mk fa seg -> Forall litb seg -> 0 < fa /\ fa + ls <= AIMG_HI ->
    Z.of_nat (length pre) = lp -> Z.of_nat (length seg) = ls ->
    vsn_cur (B + lp) mk -> u8arr bsegs mk B (pre ++ rest) -> length (pre ++ rest) = 400%nat ->
    lp + ls <= 398 -> 0 <= cnt -> cnt + ls < 2^31 ->
    (forall (y10 y11 : word) (mk' : word -> option byte),
       mem_inv bsegs mk' ->
       munch [(bv_unsigned sp + -112, bv_unsigned sp + -104); (B + lp, B + lp + ls)] mk mk' -> wmono bsegs mk mk' ->
       vsn_cur (B + lp + ls) mk' -> u8arr bsegs mk' B ((pre ++ seg) ++ skipn (length seg) rest) ->
       evt bsegs POST (LH ra x5 x6 x7 (cnt + ls) y10 y11 x12 x13 x14 x15 x16 x17 va (fa + ls) x28 x29 x30 x31 mk')) ->
    evt bsegs POST (LH ra x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    induction seg as [|b seg IH]; intros until POST; intros MI RO LIT Hfa Hlp Hls CUR UB LEN ROOM Hc1 Hc2 K.
    - cbn [length Z.of_nat] in Hls. subst ls. rewrite !Z.add_0_r in K. cbn [app skipn] in K. rewrite app_nil_r in K.
      eapply K; [exact MI| apply munch_refl| apply wmono_refl| exact CUR| exact UB].
    - prep. unfold vsn_cur, AIMG_HI in *. cbv beta delta [wz] in *.
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -104); (B + lp, B + lp + ls)] mk) as MU. pose proof (wmono_refl bsegs mk) as WM.
      cbn [length] in Hls.
      destruct rest as [|r rest]; [rewrite app_nil_r in LEN; lia|].
      inversion LIT as [|b_ seg_ [NZ NP] LIT']; subst b_ seg_. clear LIT.
      pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
      pose proof (u8ro_read bsegs _ fa _ 0 b (Z_to_bv 64 fa) RO eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      lstep. (* [comment removed for export] *) cbv beta.
      gi. gi. (* [comment removed for export] *)
      gi. gi. (* [comment removed for export] *)
      pose proof (u8arr_store_ok bsegs _ _ _ lp (Z_to_bv 64 (B + lp)) UB ltac:(rewrite LEN; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
      lstep. (* [comment removed for export] *) change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
      pose proof (u8arr_write bsegs _ _ _ lp b UB ltac:(rewrite LEN; lia)) as UB'. clear UB.
      rewrite (upd_mid' pre r rest b) in UB' by lia.
      store_done.
      gi. gi. (* [comment removed for export] *)
      gi. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *) breg 9 (cnt + 1).
      gi. (* [comment removed for export] *)
      replace (B + lp + 1) with (B + (lp + 1)) in CUR by lia.
      replace (pre ++ b :: rest) with ((pre ++ [b]) ++ rest) in UB' by (rewrite <- app_assoc; reflexivity).
      eapply (IH (pre ++ [b]) rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cnt + 1) va (fa + 1) (lp + 1) (ls - 1));
        [exact MI| exact (u8ro_cons_tl _ _ _ _ RO)| exact LIT'| lia| rewrite length_app; cbn [length]; lia| lia| exact CUR| exact UB'
        | revert LEN; rewrite !length_app; cbn [length]; lia| lia| lia| lia|].
      intros y10 y11 mk' MI' MU' WM' CUR' UB2.
      replace (cnt + 1 + (ls - 1)) with (cnt + ls) by lia. replace (fa + 1 + (ls - 1)) with (fa + ls) by lia.
      eapply K; [exact MI'| | | | ].
      + eapply munch_trans; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn; intros; lia|].
        eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn; intros; lia.
      + exact (wmono_trans bsegs _ _ _ WM WM').
      + replace (B + lp + ls) with (B + (lp + 1) + (ls - 1)) by lia. exact CUR'.
      + cbn [length skipn]. eapply arr_eqv; [exact UB2|]. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma vsn_scopy : forall (sfx pre rest : list byte) (b : byte) (ra x5 x6 x7 x10 x15 x16 x17 x28 x29 x30 x31 : word)
      (cnt va fa j sa lp ls : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    mem_inv bsegs mk -> u8ro bsegs mk (sa + 1) (sfx ++ [Z_to_bv 8 0]) -> Forall (fun c : byte => bv_unsigned c <> 0) sfx ->
    0 < sa /\ sa + 2 + ls <= AIMG_HI -> bv_unsigned b <> 0 ->
    Z.of_nat (length pre) = lp -> Z.of_nat (length sfx) = ls ->
    vsn_cur (B + lp) mk -> u8arr bsegs mk B (pre ++ rest) -> length (pre ++ rest) = 400%nat ->
    lp + 1 + ls <= 398 -> 0 <= j -> j + 1 + ls < 2^31 ->
    (forall (mk' : word -> option byte),
       mem_inv bsegs mk' ->
       munch [(bv_unsigned sp + -112, bv_unsigned sp + -104); (B + lp, B + lp + 1 + ls)] mk mk' -> wmono bsegs mk mk' ->
       vsn_cur (B + lp + 1 + ls) mk' -> u8arr bsegs mk' B ((pre ++ b :: sfx) ++ skipn (S (length sfx)) rest) ->
       evt bsegs POST (LX 0x688e0 ra x5 x6 x7 cnt x10 (wz (j + 1 + ls)) (wz (sa + 2 + ls)) (wz (B + lp + 1 + ls)) (wz 0) x15 x16 x17 va fa x28 x29 x30 x31 mk')) ->
    evt bsegs POST (LX 0x688a8 ra x5 x6 x7 cnt x10 (wz j) (wz (sa + 1)) (wz (B + lp)) (wz (bv_unsigned b)) x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    induction sfx as [|c sfx IH]; intros until POST; intros MI RO NN Hsa Hb Hlp Hls CUR UB LEN ROOM Hj1 Hj2 K;
      prep; unfold vsn_cur, AIMG_HI in *; cbv beta delta [wz] in *;
      pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -104); (B + lp, B + lp + 1 + ls)] mk) as MU; pose proof (wmono_refl bsegs mk) as WM;
      cbn [length] in Hls;
      (destruct rest as [|r rest]; [rewrite app_nil_r in LEN; lia|]);
      pose proof (bv_unsigned_in_range 8 b) as Rb; unfold bv_modulus in Rb; cbn in Rb.
    - (* [comment removed for export] *)
      gi. (* [comment removed for export] *)
      pose proof (u8arr_store_ok bsegs _ _ _ lp (Z_to_bv 64 (B + lp)) UB ltac:(rewrite LEN; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
      lstep. (* [comment removed for export] *) change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
      pose proof (u8arr_write bsegs _ _ _ lp b UB ltac:(rewrite LEN; lia)) as UB'. clear UB.
      rewrite (upd_mid' pre r rest b) in UB' by lia.
      store_done.
      gi. gi. gi. gi. (* [comment removed for export] *)
      pose proof (u8ro_read bsegs _ (sa + 1) _ 0 (Z_to_bv 8 0) (Z_to_bv 64 (sa + 1)) RO eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      lstep. (* [comment removed for export] *) cbv beta. rewrite (unsigned_lit8 0) by lia.
      gi. gi. gi. (* [comment removed for export] *)
      assert (Els : ls = 0) by (cbn in Hls; lia). clear Hls. subst ls. rewrite !Z.add_0_r in K. rewrite !Z.add_0_r in MU.
      eapply K; [exact MI| exact MU| exact WM| exact CUR| cbn [length skipn]; rewrite <- app_assoc; cbn [app]; exact UB'].
    - (* [comment removed for export] *)
      inversion NN as [|c_ sfx_ NZc NN']; subst c_ sfx_. clear NN.
      pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
      gi. (* [comment removed for export] *)
      pose proof (u8arr_store_ok bsegs _ _ _ lp (Z_to_bv 64 (B + lp)) UB ltac:(rewrite LEN; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
      lstep. (* [comment removed for export] *) change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
      pose proof (u8arr_write bsegs _ _ _ lp b UB ltac:(rewrite LEN; lia)) as UB'. clear UB.
      rewrite (upd_mid' pre r rest b) in UB' by lia.
      store_done.
      gi. gi. gi. gi. (* [comment removed for export] *)
      pose proof (u8ro_read bsegs _ (sa + 1) _ 0 c (Z_to_bv 64 (sa + 1)) RO eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      lstep. (* [comment removed for export] *) cbv beta.
      gi. gi. gi. (* [comment removed for export] *)
      replace (B + lp + 1) with (B + (lp + 1)) in CUR |- * by lia. replace (sa + 2) with (sa + 1 + 1) by lia.
      replace (pre ++ b :: rest) with ((pre ++ [b]) ++ rest) in UB' by (rewrite <- app_assoc; reflexivity).
      eapply (IH (pre ++ [b]) rest c _ _ _ _ _ _ _ _ _ _ _ _ cnt va fa (j + 1) (sa + 1) (lp + 1) (ls - 1));
        [exact MI| cbn [app] in RO; exact (u8ro_cons_tl _ _ _ _ RO)| exact NN'| lia| exact NZc| rewrite length_app; cbn [length]; lia| lia| exact CUR| exact UB'
        | revert LEN; rewrite !length_app; cbn [length]; lia| lia| lia| lia|].
      intros mk' MI' MU' WM' CUR' UB2.
      replace (j + 1 + 1 + (ls - 1)) with (j + 1 + ls) by lia. replace (sa + 1 + 2 + (ls - 1)) with (sa + 2 + ls) by lia.
      replace (B + (lp + 1) + 1 + (ls - 1)) with (B + lp + 1 + ls) in CUR' |- * by lia.
      eapply K; [exact MI'| | exact (wmono_trans bsegs _ _ _ WM WM')| exact CUR'|].
      + eapply munch_trans; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn; intros; lia|].
        eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn; intros; lia.
      + eapply arr_eqv; [exact UB2|]. rewrite <- !app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma vsn_s : forall (sbs pre rest : list byte) (ra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (cnt va fa S lp ls : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    mem_inv bsegs mk -> u8ro bsegs mk fa (zbs [37; 115]) -> 0 < fa /\ fa + 2 <= AIMG_HI ->
    rw_cells bsegs mk va [C8 (wz S)] -> VA <= va /\ va + 8 <= VA + 56 ->
    u8ro bsegs mk S (sbs ++ [Z_to_bv 8 0]) -> Forall (fun c : byte => bv_unsigned c <> 0) sbs -> 0 < S /\ S + ls + 1 <= AIMG_HI ->
    Z.of_nat (length pre) = lp -> Z.of_nat (length sbs) = ls -> 0 < ls ->
    vsn_cur (B + lp) mk -> u8arr bsegs mk B (pre ++ rest) -> length (pre ++ rest) = 400%nat ->
    lp + ls <= 398 -> 0 <= cnt -> cnt + ls < 2^31 ->
    (forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (mk' : word -> option byte),
       mem_inv bsegs mk' ->
       munch [(bv_unsigned sp + -112, bv_unsigned sp + -104); (B + lp, B + lp + ls)] mk mk' -> wmono bsegs mk mk' ->
       vsn_cur (B + lp + ls) mk' -> u8arr bsegs mk' B ((pre ++ sbs) ++ skipn (length sbs) rest) ->
       evt bsegs POST (LH ra y5 y6 y7 (cnt + ls) y10 y11 y12 y13 y14 y15 y16 y17 (va + 8) (fa + 2) y28 y29 y30 y31 mk')) ->
    evt bsegs POST (LH ra x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    intros until POST; intros MI ROF Hfa VAC Hva ROS NN HS Hlp Hls LS CUR UB LEN ROOM Hc1 Hc2 K.
    prep. unfold vsn_cur, AIMG_HI in *. cbv beta delta [wz] in *.
    pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp + -104); (B + lp, B + lp + ls)] mk) as MU. pose proof (wmono_refl bsegs mk) as WM.
    destruct sbs as [|b0 sfx]; [cbn in Hls; lia|]. cbn [length] in Hls.
    inversion NN as [|b_ s_ NZ0 NN']; subst b_ s_. clear NN.
    pose proof (bv_unsigned_in_range 8 b0) as Rb0. unfold bv_modulus in Rb0. cbn in Rb0.
    pose proof (jt_s_cells mk MI) as JT.
    pose proof (u8ro_read bsegs _ fa _ 0 (Z_to_bv 8 37) (Z_to_bv 64 fa) ROF eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
    pose proof (u8ro_read bsegs _ fa _ 1 (Z_to_bv 8 115) (Z_to_bv 64 (fa + 1)) ROF eq_refl ltac:(lia) eq_refl) as RD1.
    lstep. cbv beta. rewrite (unsigned_lit8 37) by lia. gi. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 115) by lia. gi. (* [comment removed for export] *)
    gi. gi. gi. gi. fl. (* [comment removed for export] *)
    pose proof (u8ro_read bsegs _ fa _ 1 (Z_to_bv 8 115) (Z_to_bv 64 (fa - 1 + 2)) ROF eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD2.
    lstep. cbv beta. rewrite (unsigned_lit8 115) by lia. (* [comment removed for export] *)
    gi. gi. gi. (* [comment removed for export] *)
    gi. gi. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 115) by lia. (* [comment removed for export] *)
    gi. gi. fl. gi. fl. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 115) by lia. gi. (* [comment removed for export] *)
    gi. gi. gi. fl. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 115) by lia. (* [comment removed for export] *)
    gi. fl. gi. fl. gi. gi. (* [comment removed for export] *)
    gi. fl. gi. fl. gi. fl. gi. (* [comment removed for export] *)
    gi. fl. gi. fl. gi. fl. gi. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (sext 64 (bv_extract 0 32 (le_bytes_to_word (zbs [140; 124; 4; 0])))) with (Z_to_bv 64 294028 : word) by (apply bv_eq; vm_compute; reflexivity).
    gi. fl. lstep. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 428048)) with (Z_to_bv 64 428048 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    gi. gi. gi. gi. (* [comment removed for export] *)
    gi. gi. (* [comment removed for export] *)
    pose proof (u8ro_read bsegs _ S _ 0 b0 (Z_to_bv 64 S) ROS eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD3.
    lstep. cbv beta. gi. (* [comment removed for export] *)
    gi. gi. gi. (* [comment removed for export] *)
    gi. gi. gi. (* [comment removed for export] *)
    eapply (vsn_scopy sfx pre rest b0 _ _ _ _ _ _ _ _ _ _ _ _ cnt va (fa + 1) 0 S lp (ls - 1));
      [exact MI| cbn [app] in ROS; exact (u8ro_cons_tl _ _ _ _ ROS)| exact NN'| unfold AIMG_HI; lia| exact NZ0| exact Hlp| lia| exact CUR| exact UB| exact LEN| lia| lia| lia|].
    intros mk' MI' MU' WM' CUR' UB2.
    replace (0 + 1 + (ls - 1)) with ls by lia. replace (S + 2 + (ls - 1)) with (S + 1 + ls) by lia. replace (B + lp + 1 + (ls - 1)) with (B + lp + ls) in CUR', MU' |- * by lia.
    cbv beta delta [wz] in *.
    lstep. (* [comment removed for export] *) breg 12 (- ls).
    lstep. (* [comment removed for export] *) if_cases Kc; zify_cond Kc. all: try (exfalso; match goal with H : Z.land (- _) _ < _ |- _ => rewrite land_ones64 in H; revert H end; Z.div_mod_to_equations; lia).
    all: try clear Kc.
    gi. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) breg 9 (cnt + ls).
    gi. gi. (* [comment removed for export] *)
    replace (fa + 1 + 1) with (fa + 2) by lia.
    eapply K; [exact MI'| exact MU'| exact WM'| exact CUR'| exact UB2].
  Qed.

  (* [comment removed for export] *)
  Lemma vsn_zu : forall (pre rest : list byte) (ra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (cnt va fa v N lp : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    mem_inv bsegs mk -> stk bsegs mk lo (bv_unsigned sp + -128) ->
    u8ro bsegs mk fa (zbs [37; 122; 117]) -> 0 < fa /\ fa + 3 <= AIMG_HI ->
    rw_cells bsegs mk va [C8 (wz v)] -> VA <= va /\ va + 8 <= VA + 56 ->
    1 <= v < 10 ^ N -> 1 <= N <= 19 ->
    Z.of_nat (length pre) = lp -> vsn_cur (B + lp) mk -> u8arr bsegs mk B (pre ++ rest) -> length (pre ++ rest) = 400%nat ->
    lp + N <= 398 -> 0 <= cnt -> cnt + N < 2^31 ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (mk' : word -> option byte) (ds : list byte) (nd : Z),
       mem_inv bsegs mk' -> 1 <= nd <= N -> Z.of_nat (length ds) = nd -> msg_ok ds ->
       munch [(bv_unsigned sp + -464, bv_unsigned sp + -128); (bv_unsigned sp + -112, bv_unsigned sp + -104); (B + lp, B + lp + nd)] mk mk' ->
       wmono bsegs mk mk' -> stk bsegs mk' lo (bv_unsigned sp + -128) ->
       vsn_cur (B + lp + nd) mk' -> u8arr bsegs mk' B ((pre ++ ds) ++ skipn (length ds) rest) ->
       evt bsegs POST (LH y1 y5 y6 y7 (cnt + nd) y10 y11 y12 y13 y14 y15 y16 y17 (va + 8) (fa + 3) y28 y29 y30 y31 mk')) ->
    evt bsegs POST (LH ra x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    intros until POST; intros MI ST ROF Hfa VAC Hva HV HN Hlp CUR UB LEN ROOM Hc1 Hc2 K.
    prep. unfold vsn_cur, AIMG_HI in *. cbv beta delta [wz] in *.
    assert (V64 : v < 2^64). { assert (10 ^ N <= 10 ^ 19) by (apply Z.pow_le_mono_r; lia). change (10^19) with 10000000000000000000 in H. lia. }
    pose proof (jt_u_cells mk MI) as JT.
    pose proof (u8ro_read bsegs _ fa _ 0 (Z_to_bv 8 37) (Z_to_bv 64 fa) ROF eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
    pose proof (u8ro_read bsegs _ fa _ 1 (Z_to_bv 8 122) (Z_to_bv 64 (fa + 1)) ROF eq_refl ltac:(lia) eq_refl) as RD1.
    pose proof (u8ro_read bsegs _ fa _ 1 (Z_to_bv 8 122) (Z_to_bv 64 (fa - 1 + 2)) ROF eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD2.
    pose proof (u8ro_read bsegs _ fa _ 2 (Z_to_bv 8 117) (Z_to_bv 64 (fa + 1 + 1)) ROF eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD3.
    lstep. cbv beta. rewrite (unsigned_lit8 37) by lia. gi. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 122) by lia. gi. (* [comment removed for export] *)
    gi. gi. gi. gi. fl. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 122) by lia. (* [comment removed for export] *)
    gi. gi. gi. (* [comment removed for export] *)
    gi. gi. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 122) by lia. (* [comment removed for export] *)
    gi. gi. fl. gi. fl. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 117) by lia. gi. (* [comment removed for export] *)
    gi. gi. gi. fl. (* [comment removed for export] *)
    lstep. cbv beta. rewrite (unsigned_lit8 117) by lia. (* [comment removed for export] *)
    gi. fl. gi. fl. gi. gi. (* [comment removed for export] *)
    gi. fl. gi. fl. gi. fl. gi. (* [comment removed for export] *)
    gi. fl. gi. fl. gi. fl. gi. fl. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    replace (sext 64 (bv_extract 0 32 (le_bytes_to_word (zbs [100; 124; 4; 0])))) with (Z_to_bv 64 293988 : word) by (apply bv_eq; vm_compute; reflexivity).
    gi. fl. lstep. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 428008)) with (Z_to_bv 64 428008 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    gi. gi. gi. (* [comment removed for export] *)
    gi. gi. gi. (* [comment removed for export] *)
    gi. gi. fl. gi. gi. fl. gi. fl. (* [comment removed for export] *)
    gi. gi. gi. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    eapply (appnum10_spec (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp _ _ F fc _ (bv_unsigned sp + -112) (B + 399) B lp v N lo (pre ++ rest));
      [ assumption| rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
      | exact HV| exact HN| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; rewrite LEN; lia| lia| rewrite LEN; lia
      | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity| exact CUR| exact UB|].
    intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 mk' ds nd Hnd MI' MU' WM' ST' CUR' UB' LDS OK.
    rewrite unsigned_lit in MU', ST' by lia. cbv beta delta [wz] in *.
    replace (ret_pc (Z_to_bv 64 0x68a40)) with (Z_to_bv 64 0x68a40 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lstep. (* [comment removed for export] *) breg 9 (cnt + nd).
    gi. gi. (* [comment removed for export] *)
    replace (fa + 2 + 1) with (fa + 3) by lia.
    eapply K; [exact MI'| exact Hnd| exact LDS| exact OK| | exact WM'| exact ST'| exact CUR'|].
    - eapply munch_weaken; [| exact MU']. unfold sub_fp; cbn; intros; lia.
    - eapply arr_eqv; [exact UB'|]. rewrite firstn_app, firstn_all2, skipn_app, skipn_all2 by lia.
      replace (Z.to_nat lp - length pre)%nat with 0%nat by lia. replace (Z.to_nat lp + length ds - length pre)%nat with (length ds) by lia.
      cbn [firstn app]. rewrite app_nil_r, <- app_assoc. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma vsn_end : forall (pre rest : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (cnt va fa fmt lp : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    mem_inv bsegs mk -> stk bsegs mk lo (bv_unsigned sp + -128) ->
    u8ro bsegs mk fa [Z_to_bv 8 0] -> 0 < fa /\ fa + 1 <= AIMG_HI ->
    Z.of_nat (length pre) = lp -> vsn_lo fmt mk -> vsn_cur (B + lp) mk -> vsn_hi ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mk ->
    u8arr bsegs mk B (pre ++ rest) -> length (pre ++ rest) = 400%nat -> lp <= 398 -> 0 <= cnt < 2^31 ->
    (forall (mk' : word -> option byte), mem_inv bsegs mk' ->
       munch [(bv_unsigned sp + -128, bv_unsigned sp); (B + lp, B + lp + 1)] mk mk' -> wmono bsegs mk mk' -> stk bsegs mk' lo (bv_unsigned sp) ->
       u8arr bsegs mk' B ((pre ++ [Z_to_bv 8 0]) ++ skipn 1 rest) ->
       evt bsegs POST (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz cnt) (wz (B + 400)) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (ret_pc ra) fc None mk' (seg_rom bsegs))) ->
    evt bsegs POST (LH x1 x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    intros until POST; intros MI ST ROF Hfa Hlp FLO CUR FHI UB LEN ROOM Hc K.
    prep. unfold vsn_lo, vsn_cur, vsn_hi, AIMG_HI in *. cbv beta delta [wz] in *.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (B + lp, B + lp + 1)] mk) as MU. pose proof (wmono_refl bsegs mk) as WM.
    destruct rest as [|r rest]; [rewrite app_nil_r in LEN; lia|].
    pose proof (u8ro_read bsegs _ fa _ 0 (Z_to_bv 8 0) (Z_to_bv 64 fa) ROF eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0.
    lstep. cbv beta. rewrite (unsigned_lit8 0) by lia. gi. gi. (* [comment removed for export] *)
    gi. gi. gi. gi. (* [comment removed for export] *)
    pose proof (u8arr_store_ok bsegs _ _ _ lp (Z_to_bv 64 (B + lp)) UB ltac:(rewrite LEN; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    lstep. (* [comment removed for export] *)
    try rewrite (le1_lit2 0) by lia.
    pose proof (u8arr_write bsegs _ _ _ lp (Z_to_bv 8 0) UB ltac:(rewrite LEN; lia)) as UB'. clear UB.
    rewrite (upd_mid' pre r rest (Z_to_bv 8 0)) in UB' by lia.
    store_done.
    gi. (* [comment removed for export] *)
    do 13 gi. gi. (* [comment removed for export] *)
    replace (bv_unsigned sp + -112) with (bv_unsigned sp + -128 + 16) in CUR by lia.
    replace (bv_unsigned sp + -104) with (bv_unsigned sp + -128 + 24) in FHI by lia.
    glue FLO CUR. glue FLO FHI.
    release_frame FLO ST (bv_unsigned sp).
    gi. (* [comment removed for export] *)
    eapply K; [assumption| exact MU| exact WM| exact ST|].
    cbn [skipn]. rewrite <- app_assoc. cbn [app]. exact UB'.
  Qed.
End VSN.


End CeilWrap.
End RTW_oom_vsn.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
Module RTW_oom_vsn2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_scommon_lg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_snp3.RTW_sec_snp1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_snp3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_p_oom_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_oom_lib RTW_oom_an RTW_oom_vsn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMT1 : Z := 0x1e954.
Definition FMT2 : Z := 0x20217.
Definition FMT1_D1 : list byte := zbs [37; 115].   (* [comment removed for export] *)
Lemma ro_FMT1_D1 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT1 + 0) FMT1_D1.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT1_D1) FMT1_D1). apply (ro_cells_image bsegs m (FMT1 + 0) FMT1_D1 MI); [vm_compute; reflexivity| unfold FMT1; lia| cbn; unfold FMT1; lia]. Qed.
Definition FMT1_L1 : list byte := zbs [58; 32; 79; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121; 46; 32].   (* [comment removed for export] *)
Lemma ro_FMT1_L1 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT1 + 2) FMT1_L1.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT1_L1) FMT1_L1). apply (ro_cells_image bsegs m (FMT1 + 2) FMT1_L1 MI); [vm_compute; reflexivity| unfold FMT1; lia| cbn; unfold FMT1; lia]. Qed.
Definition FMT1_Z : list byte := zbs [0].   (* [comment removed for export] *)
Lemma ro_FMT1_Z : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT1 + 19) FMT1_Z.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT1_Z) FMT1_Z). apply (ro_cells_image bsegs m (FMT1 + 19) FMT1_Z MI); [vm_compute; reflexivity| unfold FMT1; lia| cbn; unfold FMT1; lia]. Qed.
Definition FMT2_L1 : list byte := zbs [84; 104; 101; 32; 112; 114; 111; 99; 101; 115; 115; 32; 104; 97; 115; 32; 101; 120; 104; 97; 117; 115; 116; 101; 100; 32].   (* [comment removed for export] *)
Lemma ro_FMT2_L1 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT2 + 0) FMT2_L1.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT2_L1) FMT2_L1). apply (ro_cells_image bsegs m (FMT2 + 0) FMT2_L1 MI); [vm_compute; reflexivity| unfold FMT2; lia| cbn; unfold FMT2; lia]. Qed.
Definition FMT2_D1 : list byte := zbs [37; 122; 117].   (* [comment removed for export] *)
Lemma ro_FMT2_D1 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT2 + 26) FMT2_D1.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT2_D1) FMT2_D1). apply (ro_cells_image bsegs m (FMT2 + 26) FMT2_D1 MI); [vm_compute; reflexivity| unfold FMT2; lia| cbn; unfold FMT2; lia]. Qed.
Definition FMT2_L2 : list byte := zbs [32; 77; 66; 32; 102; 111; 114; 32; 115; 105; 122; 101; 32; 99; 108; 97; 115; 115; 32].   (* [comment removed for export] *)
Lemma ro_FMT2_L2 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT2 + 29) FMT2_L2.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT2_L2) FMT2_L2). apply (ro_cells_image bsegs m (FMT2 + 29) FMT2_L2 MI); [vm_compute; reflexivity| unfold FMT2; lia| cbn; unfold FMT2; lia]. Qed.
Definition FMT2_D2 : list byte := zbs [37; 122; 117].   (* [comment removed for export] *)
Lemma ro_FMT2_D2 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT2 + 48) FMT2_D2.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT2_D2) FMT2_D2). apply (ro_cells_image bsegs m (FMT2 + 48) FMT2_D2 MI); [vm_compute; reflexivity| unfold FMT2; lia| cbn; unfold FMT2; lia]. Qed.
Definition FMT2_L3 : list byte := zbs [32; 40].   (* [comment removed for export] *)
Lemma ro_FMT2_L3 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT2 + 51) FMT2_L3.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT2_L3) FMT2_L3). apply (ro_cells_image bsegs m (FMT2 + 51) FMT2_L3 MI); [vm_compute; reflexivity| unfold FMT2; lia| cbn; unfold FMT2; lia]. Qed.
Definition FMT2_D3 : list byte := zbs [37; 122; 117].   (* [comment removed for export] *)
Lemma ro_FMT2_D3 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT2 + 53) FMT2_D3.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT2_D3) FMT2_D3). apply (ro_cells_image bsegs m (FMT2 + 53) FMT2_D3 MI); [vm_compute; reflexivity| unfold FMT2; lia| cbn; unfold FMT2; lia]. Qed.
Definition FMT2_L4 : list byte := zbs [32; 98; 121; 116; 101; 115; 41; 46; 10].   (* [comment removed for export] *)
Lemma ro_FMT2_L4 : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT2 + 56) FMT2_L4.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT2_L4) FMT2_L4). apply (ro_cells_image bsegs m (FMT2 + 56) FMT2_L4 MI); [vm_compute; reflexivity| unfold FMT2; lia| cbn; unfold FMT2; lia]. Qed.
Definition FMT2_Z : list byte := zbs [0].   (* [comment removed for export] *)
Lemma ro_FMT2_Z : forall m, mem_inv bsegs m -> u8ro bsegs m (FMT2 + 65) FMT2_Z.
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length FMT2_Z) FMT2_Z). apply (ro_cells_image bsegs m (FMT2 + 65) FMT2_Z MI); [vm_compute; reflexivity| unfold FMT2; lia| cbn; unfold FMT2; lia]. Qed.
Definition S_TOOL : list byte := zbs [65; 100; 100; 114; 101; 115; 115; 83; 97; 110; 105; 116; 105; 122; 101; 114].   (* [comment removed for export] *)
Lemma ro_S_TOOL : forall m, mem_inv bsegs m -> u8ro bsegs m A_ASAN_STR (S_TOOL ++ [Z_to_bv 8 0]).
Proof. intros m MI. apply (u8ro_of_ro_cells m _ (length (S_TOOL ++ [Z_to_bv 8 0])) (S_TOOL ++ [Z_to_bv 8 0])). apply (ro_cells_image bsegs m A_ASAN_STR (S_TOOL ++ [Z_to_bv 8 0]) MI); [vm_compute; reflexivity| unfold A_ASAN_STR; lia| cbn; unfold A_ASAN_STR; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lit_forall := unfold zbs; cbn [map]; repeat (apply Forall_cons; [split; (vm_compute; discriminate)|]); apply Forall_nil.
Ltac nz_forall := unfold zbs; cbn [map]; repeat (apply Forall_cons; [vm_compute; discriminate|]); apply Forall_nil.

Lemma litb_msg_ok_lits : forall bs, Forall (fun b : byte => bv_unsigned b <> 0 /\ bv_unsigned b <> 27) bs -> msg_ok bs.
Proof. intros bs H. exact H. Qed.

(* [comment removed for export] *)
Definition vsn_contract (fmt : Z) (v1 v2 v3 : word) (Lmax : Z) : Prop :=
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (B VA lo : Z),
    alloc_ceiling <= lo -> lo + 464 <= bv_unsigned sp -> bv_unsigned sp <= B /\ B + 400 <= VA -> VA + 56 <= 2^47 ->
  forall (ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : word -> option byte) (junk : list byte)
         (POST : machine_state -> Prop),
    mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) ->
    rw_cells bsegs m VA [C8 v1] -> rw_cells bsegs m (VA + 8) [C8 v2] -> rw_cells bsegs m (VA + 16) [C8 v3] ->
    u8arr bsegs m B junk -> length junk = 400%nat ->
    (forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) (bs rest : list byte),
       mem_inv bsegs m' -> munch [(bv_unsigned sp + -464, bv_unsigned sp); (B, B + 400)] m m' -> wmono bsegs m m' ->
       stk bsegs m' lo (bv_unsigned sp) ->
       u8arr bsegs m' B (bs ++ Z_to_bv 8 0 :: rest) -> length (bs ++ Z_to_bv 8 0 :: rest) = 400%nat ->
       msg_ok bs -> 0 < Z.of_nat (length bs) <= Lmax ->
       evt bsegs POST (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz (Z.of_nat (length bs))) x11 x12 x13 x14 x15 x16 x17
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz B) (wz 400) (wz fmt) (wz VA) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (wz A_VSNPRINTF) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Section VSN2.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (B VA lo : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 464 <= bv_unsigned sp.
  Hypothesis HB : bv_unsigned sp <= B /\ B + 400 <= VA.
  Hypothesis HVA : VA + 56 <= 2^47.
  Variables (m0 : word -> option byte) (fmt : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (v1 v2 v3 : word).

  #[warnings="-notation-for-abbreviation"]
  Notation LH ra x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mm :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 32) (Z_to_bv 64 cnt) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 va) (Z_to_bv 64 (B + 399)) (Z_to_bv 64 115) (Z_to_bv 64 37) (Z_to_bv 64 45) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 46)
             (Z_to_bv 64 fa) (Z_to_bv 64 108) x28 x29 x30 x31)
        F (Z_to_bv 64 0x686a4) fc None mm (seg_rom bsegs)).

  Let W0 : list (Z * Z) := [(bv_unsigned sp + -464, bv_unsigned sp); (B, B + 400)].

  (* [comment removed for export] *)
  Definition vst (pre rest : list byte) (mk : word -> option byte) : Prop :=
    mem_inv bsegs mk /\ stk bsegs mk lo (bv_unsigned sp + -128) /\ munch W0 m0 mk /\ wmono bsegs m0 mk
    /\ vsn_lo sp B fmt mk /\ vsn_hi sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mk
    /\ vsn_cur sp (B + Z.of_nat (length pre)) mk
    /\ u8arr bsegs mk B (pre ++ rest) /\ length (pre ++ rest) = 400%nat
    /\ rw_cells bsegs mk VA [C8 v1] /\ rw_cells bsegs mk (VA + 8) [C8 v2] /\ rw_cells bsegs mk (VA + 16) [C8 v3].

  Ltac prep2 :=
    let RSP := fresh "RSP" in
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  Ltac subfp2 := unfold sub_fp; cbn; intros; lia.

  (* [comment removed for export] *)
  Lemma vst_step : forall (W' : list (Z * Z)) (pre rest pre' rest' : list byte) (mk mk' : word -> option byte),
    vst pre rest mk -> mem_inv bsegs mk' -> munch W' mk mk' -> wmono bsegs mk mk' ->
    sub_fp W' W0 ->
    Forall (fun iv : Z * Z => (bv_unsigned sp + -464 <= fst iv /\ snd iv <= bv_unsigned sp + -128)
                              \/ (bv_unsigned sp + -112 <= fst iv /\ snd iv <= bv_unsigned sp + -104)
                              \/ (B <= fst iv /\ snd iv <= B + 400)) W' ->
    stk bsegs mk' lo (bv_unsigned sp + -128) ->
    vsn_cur sp (B + Z.of_nat (length pre')) mk' -> u8arr bsegs mk' B (pre' ++ rest') -> length (pre' ++ rest') = 400%nat ->
    vst pre' rest' mk'.
  Proof using CEIL LO HB HVA.
    intros W' pre rest pre' rest' mk mk' (MI & ST & MU & WM & FLO & FHI & CUR & UB & LEN & A1 & A2 & A3) MI' MU' WM' SUB FA ST' CUR' UB' LEN'.
    prep2. unfold vst, vsn_lo, vsn_hi in *.
    assert (DJ : forall a n, (a + n <= bv_unsigned sp + -112 /\ bv_unsigned sp + -128 <= a) \/ (bv_unsigned sp + -104 <= a /\ a + n <= B) \/ B + 400 <= a ->
                 disjoint_from W' a n).
    { intros a n Ha. clear - FA Ha HB. induction FA as [|[l h] W'' Hiv _ IH]; [exact I|]. cbn [fst snd] in Hiv. cbn [disjoint_from]. split; [lia| exact IH]. }
    split; [exact MI'|]. split; [exact ST'|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [exact SUB| exact MU']]|].
    split; [exact (wmono_trans bsegs _ _ _ WM WM')|].
    split; [eapply (rw_cells_transport bsegs _ mk mk'); [exact FLO| exact MU'| exact WM'| apply DJ; cbn; lia]|].
    split; [eapply (rw_cells_transport bsegs _ mk mk'); [exact FHI| exact MU'| exact WM'| apply DJ; cbn; lia]|].
    split; [exact CUR'|]. split; [exact UB'|]. split; [exact LEN'|].
    split; [eapply (rw_cells_transport bsegs _ mk mk'); [exact A1| exact MU'| exact WM'| apply DJ; cbn; lia]|].
    split; [eapply (rw_cells_transport bsegs _ mk mk'); [exact A2| exact MU'| exact WM'| apply DJ; cbn; lia]|].
    eapply (rw_cells_transport bsegs _ mk mk'); [exact A3| exact MU'| exact WM'| apply DJ; cbn; lia].
  Qed.

  Lemma len_app_skip : forall (pre seg rest : list byte), length (pre ++ rest) = 400%nat ->
    Z.of_nat (length pre) + Z.of_nat (length seg) <= 398 -> length ((pre ++ seg) ++ skipn (length seg) rest) = 400%nat.
  Proof. intros pre seg rest LEN ROOM. revert LEN. rewrite !length_app, length_skipn. lia. Qed.

  (* [comment removed for export] *)
  Lemma vw_A : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte) (POST : machine_state -> Prop),
    mem_inv bsegs m0 -> stk bsegs m0 lo (bv_unsigned sp) -> 0 < fmt /\ fmt + 1 <= AIMG_HI ->
    rw_cells bsegs m0 VA [C8 v1] -> rw_cells bsegs m0 (VA + 8) [C8 v2] -> rw_cells bsegs m0 (VA + 16) [C8 v3] ->
    u8arr bsegs m0 B junk -> length junk = 400%nat ->
    (forall m1, vst [] junk m1 ->
       evt bsegs POST (LH ra t0 t1 t2 0 (wz (B + 400)) (wz 400) (wz fmt) (wz VA) a4 a5 a6 a7 VA fmt t3 t4 t5 t6 m1)) ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz B) (wz 400) (wz fmt) (wz VA) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz A_VSNPRINTF) fc None m0 (seg_rom bsegs)).
  Proof using CEIL LO HB HVA.
    intros until POST. intros MI ST Hfmt A1 A2 A3 UB LEN K. prep2.
    eapply (vsn_A sp gp tp F fc B VA lo CEIL LO HB HVA); [exact MI| exact ST| exact Hfmt|].
    intros m1 MI1 MU1 WM1 ST1 FLO CUR FHI. apply K. unfold vst.
    split; [exact MI1|]. split; [exact ST1|]. split; [eapply munch_weaken; [| exact MU1]; subfp2|]. split; [exact WM1|].
    split; [exact FLO|]. split; [exact FHI|]. split; [cbn [length Z.of_nat]; rewrite Z.add_0_r; exact CUR|].
    split; [cbn [app]; eapply (u8arr_transport bsegs _ m0 m1); [exact UB| exact MU1| exact WM1| cbn; lia]|].
    split; [exact LEN|].
    split; [eapply (rw_cells_transport bsegs _ m0 m1); [exact A1| exact MU1| exact WM1| cbn; lia]|].
    split; [eapply (rw_cells_transport bsegs _ m0 m1); [exact A2| exact MU1| exact WM1| cbn; lia]|].
    eapply (rw_cells_transport bsegs _ m0 m1); [exact A3| exact MU1| exact WM1| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma vw_lits : forall (seg pre rest : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (cnt va fa : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    vst pre rest mk -> u8ro bsegs mk fa seg -> Forall litb seg -> 0 < fa /\ fa + Z.of_nat (length seg) <= AIMG_HI ->
    Z.of_nat (length pre) + Z.of_nat (length seg) <= 398 -> 0 <= cnt -> cnt + Z.of_nat (length seg) < 2^31 ->
    (forall (y10 y11 : word) (mk' : word -> option byte), vst (pre ++ seg) (skipn (length seg) rest) mk' ->
       evt bsegs POST (LH x1 x5 x6 x7 (cnt + Z.of_nat (length seg)) y10 y11 x12 x13 x14 x15 x16 x17 va (fa + Z.of_nat (length seg)) x28 x29 x30 x31 mk')) ->
    evt bsegs POST (LH x1 x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    intros until POST. intros V RO LIT Hfa ROOM Hc1 Hc2 K. prep2.
    pose proof V as (MI & ST & MU & WM & FLO & FHI & CUR & UB & LEN & A1 & A2 & A3).
    eapply (vsn_lits sp gp tp F fc B VA lo CEIL LO HB HVA seg pre rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cnt va fa (Z.of_nat (length pre)) (Z.of_nat (length seg)));
      [exact MI| exact RO| exact LIT| exact Hfa| reflexivity| reflexivity| exact CUR| exact UB| exact LEN| exact ROOM| exact Hc1| exact Hc2|].
    intros y10 y11 mk' MI' MU' WM' CUR' UB'. apply K.
    eapply (vst_step _ pre rest _ _ mk mk' V MI' MU' WM').
    - subfp2.
    - repeat constructor; cbn [fst snd]; lia.
    - eapply stk_transport_disjoint; [exact ST| exact MU'| exact WM'| cbn; lia].
    - rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact CUR'.
    - exact UB'.
    - apply len_app_skip; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma vw_s : forall (sbs pre rest : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (cnt va fa S : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    vst pre rest mk -> u8ro bsegs mk fa (zbs [37; 115]) -> 0 < fa /\ fa + 2 <= AIMG_HI ->
    rw_cells bsegs mk va [C8 (wz S)] -> VA <= va /\ va + 8 <= VA + 56 ->
    u8ro bsegs mk S (sbs ++ [Z_to_bv 8 0]) -> Forall (fun c : byte => bv_unsigned c <> 0) sbs -> 0 < S /\ S + Z.of_nat (length sbs) + 1 <= AIMG_HI ->
    0 < Z.of_nat (length sbs) ->
    Z.of_nat (length pre) + Z.of_nat (length sbs) <= 398 -> 0 <= cnt -> cnt + Z.of_nat (length sbs) < 2^31 ->
    (forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (mk' : word -> option byte),
       vst (pre ++ sbs) (skipn (length sbs) rest) mk' ->
       evt bsegs POST (LH x1 y5 y6 y7 (cnt + Z.of_nat (length sbs)) y10 y11 y12 y13 y14 y15 y16 y17 (va + 8) (fa + 2) y28 y29 y30 y31 mk')) ->
    evt bsegs POST (LH x1 x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    intros until POST. intros V ROF Hfa VAC Hva ROS NN HS LS ROOM Hc1 Hc2 K. prep2.
    pose proof V as (MI & ST & MU & WM & FLO & FHI & CUR & UB & LEN & A1 & A2 & A3).
    eapply (vsn_s sp gp tp F fc B VA lo CEIL LO HB HVA sbs pre rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cnt va fa S (Z.of_nat (length pre)) (Z.of_nat (length sbs)));
      [exact MI| exact ROF| exact Hfa| exact VAC| exact Hva| exact ROS| exact NN| exact HS| reflexivity| reflexivity| exact LS| exact CUR| exact UB| exact LEN
      | exact ROOM| exact Hc1| exact Hc2|].
    intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 mk' MI' MU' WM' CUR' UB'. apply K.
    eapply (vst_step _ pre rest _ _ mk mk' V MI' MU' WM').
    - subfp2.
    - repeat constructor; cbn [fst snd]; lia.
    - eapply stk_transport_disjoint; [exact ST| exact MU'| exact WM'| cbn; lia].
    - rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact CUR'.
    - exact UB'.
    - apply len_app_skip; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma vw_zu : forall (pre rest : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (cnt va fa v N : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    vst pre rest mk -> u8ro bsegs mk fa (zbs [37; 122; 117]) -> 0 < fa /\ fa + 3 <= AIMG_HI ->
    rw_cells bsegs mk va [C8 (wz v)] -> VA <= va /\ va + 8 <= VA + 56 ->
    1 <= v < 10 ^ N -> 1 <= N <= 19 ->
    Z.of_nat (length pre) + N <= 398 -> 0 <= cnt -> cnt + N < 2^31 ->
    (forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (mk' : word -> option byte) (ds : list byte),
       1 <= Z.of_nat (length ds) <= N -> msg_ok ds ->
       vst (pre ++ ds) (skipn (length ds) rest) mk' ->
       evt bsegs POST (LH y1 y5 y6 y7 (cnt + Z.of_nat (length ds)) y10 y11 y12 y13 y14 y15 y16 y17 (va + 8) (fa + 3) y28 y29 y30 y31 mk')) ->
    evt bsegs POST (LH x1 x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    intros until POST. intros V ROF Hfa VAC Hva HV HN ROOM Hc1 Hc2 K. prep2.
    pose proof V as (MI & ST & MU & WM & FLO & FHI & CUR & UB & LEN & A1 & A2 & A3).
    eapply (vsn_zu sp gp tp F fc B VA lo CEIL LO HB HVA pre rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cnt va fa v N (Z.of_nat (length pre)));
      [exact MI| exact ST| exact ROF| exact Hfa| exact VAC| exact Hva| exact HV| exact HN| reflexivity| exact CUR| exact UB| exact LEN
      | exact ROOM| exact Hc1| exact Hc2|].
    intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 mk' ds nd MI' Hnd LDS OK MU' WM' ST' CUR' UB'. subst nd. apply K; [exact Hnd| exact OK|].
    eapply (vst_step _ pre rest _ _ mk mk' V MI' MU' WM').
    - subfp2.
    - repeat constructor; cbn [fst snd]; lia.
    - exact ST'.
    - rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact CUR'.
    - exact UB'.
    - apply len_app_skip; [assumption| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma vw_end : forall (pre rest : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      (cnt va fa : Z) (mk : word -> option byte) (POST : machine_state -> Prop),
    vst pre rest mk -> u8ro bsegs mk fa [Z_to_bv 8 0] -> 0 < fa /\ fa + 1 <= AIMG_HI ->
    Z.of_nat (length pre) <= 398 -> 0 <= cnt < 2^31 ->
    (forall (mk' : word -> option byte), mem_inv bsegs mk' -> munch W0 m0 mk' -> wmono bsegs m0 mk' -> stk bsegs mk' lo (bv_unsigned sp) ->
       u8arr bsegs mk' B (pre ++ Z_to_bv 8 0 :: skipn 1 rest) -> length (pre ++ Z_to_bv 8 0 :: skipn 1 rest) = 400%nat ->
       evt bsegs POST (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz cnt) (wz (B + 400)) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                          F (ret_pc ra) fc None mk' (seg_rom bsegs))) ->
    evt bsegs POST (LH x1 x5 x6 x7 cnt x10 x11 x12 x13 x14 x15 x16 x17 va fa x28 x29 x30 x31 mk).
  Proof using CEIL LO HB HVA.
    intros until POST. intros V ROF Hfa ROOM Hc K. prep2.
    pose proof V as (MI & ST & MU & WM & FLO & FHI & CUR & UB & LEN & A1 & A2 & A3).
    eapply (vsn_end sp gp tp F fc B VA lo CEIL LO HB HVA pre rest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 cnt va fa fmt (Z.of_nat (length pre)));
      [exact MI| exact ST| exact ROF| exact Hfa| reflexivity| exact FLO| exact CUR| exact FHI| exact UB| exact LEN| exact ROOM| exact Hc|].
    intros mk' MI' MU' WM' ST' UB'. apply K; [exact MI'| | exact (wmono_trans bsegs _ _ _ WM WM')| exact ST'| |].
    - eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']; subfp2].
    - rewrite <- app_assoc in UB'. cbn [app] in UB'. exact UB'.
    - revert LEN. rewrite !length_app. cbn [length]. rewrite length_skipn. lia.
  Qed.
End VSN2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma len_S_TOOL : Z.of_nat (length S_TOOL) = 16. Proof. reflexivity. Qed.
Lemma len_F1L1 : Z.of_nat (length FMT1_L1) = 17. Proof. reflexivity. Qed.
Lemma len_F2L1 : Z.of_nat (length FMT2_L1) = 26. Proof. reflexivity. Qed.
Lemma len_F2L2 : Z.of_nat (length FMT2_L2) = 19. Proof. reflexivity. Qed.
Lemma len_F2L3 : Z.of_nat (length FMT2_L3) = 2. Proof. reflexivity. Qed.
Lemma len_F2L4 : Z.of_nat (length FMT2_L4) = 9. Proof. reflexivity. Qed.
Ltac lens := rewrite ?length_app, ?Nat2Z.inj_add, ?len_S_TOOL, ?len_F1L1, ?len_F2L1, ?len_F2L2, ?len_F2L3, ?len_F2L4; cbn [length Z.of_nat]; try lia.

Lemma msg_ok_nil : msg_ok []. Proof. apply Forall_nil. Qed.

Theorem vsn_fmt1 : forall v2 v3, vsn_contract FMT1 (wz A_ASAN_STR) v2 v3 33.
Proof.
  unfold vsn_contract. intros v2 v3 sp gp tp F fc B VA lo CEIL LO HB HVA. intros until POST. intros MI ST A1 A2 A3 UB LEN K.
  eapply (vw_A sp gp tp F fc B VA lo CEIL LO HB HVA m FMT1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz A_ASAN_STR) v2 v3);
    [exact MI| exact ST| unfold FMT1, AIMG_HI; lia| exact A1| exact A2| exact A3| exact UB| exact LEN|].
  intros m1 V1. pose proof V1 as (MI1 & _ & _ & _ & _ & _ & _ & _ & _ & A11 & _ & _).
  eapply (vw_s sp gp tp F fc B VA lo CEIL LO HB HVA m FMT1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz A_ASAN_STR) v2 v3
            S_TOOL [] junk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 VA FMT1 A_ASAN_STR m1);
    [exact V1| pose proof (ro_FMT1_D1 m1 MI1) as X; rewrite Z.add_0_r in X; exact X| unfold FMT1, AIMG_HI; lia| exact A11| lia
    | exact (ro_S_TOOL m1 MI1)| unfold S_TOOL; nz_forall| rewrite len_S_TOOL; unfold A_ASAN_STR, AIMG_HI; lia| rewrite len_S_TOOL; lia
    | lens| lia| lens|].
  intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 V2. pose proof V2 as (MI2 & _).
  eapply (vw_lits sp gp tp F fc B VA lo CEIL LO HB HVA m FMT1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz A_ASAN_STR) v2 v3
            FMT1_L1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2);
    [exact V2| exact (ro_FMT1_L1 m2 MI2)| unfold FMT1_L1; lit_forall| rewrite len_F1L1; unfold FMT1, AIMG_HI; lia| lens| lens| lens|].
  intros z10 z11 m3 V3. pose proof V3 as (MI3 & _).
  eapply (vw_end sp gp tp F fc B VA lo CEIL LO HB HVA m FMT1 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz A_ASAN_STR) v2 v3
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3);
    [exact V3| pose proof (ro_FMT1_Z m3 MI3) as X; replace (FMT1 + 2 + Z.of_nat (length FMT1_L1)) with (FMT1 + 19) by (rewrite len_F1L1; lia); exact X
    | rewrite len_F1L1; unfold FMT1, AIMG_HI; lia| lens| lens|].
  intros m4 MI4 MU4 WM4 ST4 UB4 LEN4.
  replace (0 + Z.of_nat (length S_TOOL) + Z.of_nat (length FMT1_L1)) with (Z.of_nat (length (([] ++ S_TOOL) ++ FMT1_L1))) by reflexivity.
  eapply K; [exact MI4| exact MU4| exact WM4| exact ST4| exact UB4| exact LEN4| | lens].
  apply msg_ok_app; [apply msg_ok_app; [apply msg_ok_nil| unfold S_TOOL; lit_forall]| unfold FMT1_L1; lit_forall].
Qed.

Theorem vsn_fmt2 : forall c sz, 1 <= c <= 30 -> 1 <= sz < 10 ^ 5 -> vsn_contract FMT2 (wz 4096) (wz c) (wz sz) 67.
Proof.
  unfold vsn_contract. intros c sz Hc Hsz sp gp tp F fc B VA lo CEIL LO HB HVA. intros until POST. intros MI ST A1 A2 A3 UB LEN K.
  eapply (vw_A sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz));
    [exact MI| exact ST| unfold FMT2, AIMG_HI; lia| exact A1| exact A2| exact A3| exact UB| exact LEN|].
  intros m1 V1. pose proof V1 as (MI1 & _).
  (* [comment removed for export] *)
  eapply (vw_lits sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz)
            FMT2_L1 [] junk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 VA FMT2 m1);
    [exact V1| pose proof (ro_FMT2_L1 m1 MI1) as X; rewrite Z.add_0_r in X; exact X| unfold FMT2_L1; lit_forall| rewrite len_F2L1; unfold FMT2, AIMG_HI; lia
    | lens| lens| lens|].
  intros a10 a11 m2 V2. pose proof V2 as (MI2 & _ & _ & _ & _ & _ & _ & _ & _ & A21 & _ & _). rewrite len_F2L1.
  (* [comment removed for export] *)
  eapply (vw_zu sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ VA (FMT2 + 26) 4096 4 m2);
    [exact V2| exact (ro_FMT2_D1 m2 MI2)| unfold FMT2, AIMG_HI; lia| exact A21| lia| lia| lia| lens| lens| lens|].
  intros b1 b5 b6 b7 b10 b11 b12 b13 b14 b15 b16 b17 b28 b29 b30 b31 m3 ds1 Hd1 OK1 V3. pose proof V3 as (MI3 & _).
  (* [comment removed for export] *)
  eapply (vw_lits sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz)
            FMT2_L2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3);
    [exact V3| replace (FMT2 + 26 + 3) with (FMT2 + 29) by lia; exact (ro_FMT2_L2 m3 MI3)| unfold FMT2_L2; lit_forall| rewrite len_F2L2; unfold FMT2, AIMG_HI; lia
    | lens| lens| lens|].
  intros c10 c11 m4 V4. pose proof V4 as (MI4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & A42 & _). rewrite len_F2L2.
  (* [comment removed for export] *)
  eapply (vw_zu sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (VA + 8) (FMT2 + 26 + 3 + 19) c 2 m4);
    [exact V4| replace (FMT2 + 26 + 3 + 19) with (FMT2 + 48) by lia; exact (ro_FMT2_D2 m4 MI4)| unfold FMT2, AIMG_HI; lia| exact A42| lia| lia| lia| lens| lens| lens|].
  intros d1 d5 d6 d7 d10 d11 d12 d13 d14 d15 d16 d17 d28 d29 d30 d31 m5 ds2 Hd2 OK2 V5. pose proof V5 as (MI5 & _).
  (* [comment removed for export] *)
  eapply (vw_lits sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz)
            FMT2_L3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5);
    [exact V5| replace (FMT2 + 26 + 3 + 19 + 3) with (FMT2 + 51) by lia; exact (ro_FMT2_L3 m5 MI5)| unfold FMT2_L3; lit_forall| rewrite len_F2L3; unfold FMT2, AIMG_HI; lia
    | lens| lens| lens|].
  intros e10 e11 m6 V6. pose proof V6 as (MI6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A63). rewrite len_F2L3.
  (* [comment removed for export] *)
  eapply (vw_zu sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (VA + 8 + 8) (FMT2 + 26 + 3 + 19 + 3 + 2) sz 5 m6);
    [exact V6| replace (FMT2 + 26 + 3 + 19 + 3 + 2) with (FMT2 + 53) by lia; exact (ro_FMT2_D3 m6 MI6)| unfold FMT2, AIMG_HI; lia
    | replace (VA + 8 + 8) with (VA + 16) by lia; exact A63| lia| lia| lia| lens| lens| lens|].
  intros f1 f5 f6 f7 f10 f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31 m7 ds3 Hd3 OK3 V7. pose proof V7 as (MI7 & _).
  (* [comment removed for export] *)
  eapply (vw_lits sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz)
            FMT2_L4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7);
    [exact V7| replace (FMT2 + 26 + 3 + 19 + 3 + 2 + 3) with (FMT2 + 56) by lia; exact (ro_FMT2_L4 m7 MI7)| unfold FMT2_L4; lit_forall| rewrite len_F2L4; unfold FMT2, AIMG_HI; lia
    | lens| lens| lens|].
  intros g10 g11 m8 V8. pose proof V8 as (MI8 & _). rewrite len_F2L4.
  eapply (vw_end sp gp tp F fc B VA lo CEIL LO HB HVA m FMT2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 4096) (wz c) (wz sz)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8);
    [exact V8| replace (FMT2 + 26 + 3 + 19 + 3 + 2 + 3 + 9) with (FMT2 + 65) by lia; exact (ro_FMT2_Z m8 MI8)| unfold FMT2, AIMG_HI; lia| lens| lens|].
  intros m9 MI9 MU9 WM9 ST9 UB9 LEN9.
  match goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (wz ?n) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    match type of UB9 with u8arr _ _ _ (?bs ++ _ :: _) => replace n with (Z.of_nat (length bs)) by lens end end.
  eapply K; [exact MI9| exact MU9| exact WM9| exact ST9| exact UB9| exact LEN9| | lens].
  repeat (apply msg_ok_app; [| first [assumption| unfold FMT2_L1, FMT2_L2, FMT2_L3, FMT2_L4; lit_forall]]). apply msg_ok_nil.
Qed.

End CeilWrap.
End RTW_oom_vsn2.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_secz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
Module RTW_p_oom_pf.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_emb0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_snp3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_p_oom_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_p_oom_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_oom_lib RTW_oom_an OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb RTW_oom_vsn RTW_oom_vsn2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition NOBUF_STACK : Z := 640.     (* [comment removed for export] *)
Definition PRINTF_STACK : Z := 1152.   (* [comment removed for export] *)

Ltac gi := lstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia | _ => idtac end.
Ltac fa_lia := repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.
Ltac retlit n := replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

Lemma msg_at_of_u8arr : forall m B bs rest, u8arr bsegs m B (bs ++ Z_to_bv 8 0 :: rest) -> msg_ok bs -> msg_at m B bs.
Proof.
  intros m B bs rest [UB _] OK. split; [| apply msg_ok_nonul; exact OK].
  replace (bs ++ Z_to_bv 8 0 :: rest) with ((bs ++ [Z_to_bv 8 0]) ++ rest) in UB by (rewrite <- app_assoc; reflexivity).
  exact (u8ro_app_l m B _ _ UB).
Qed.

Lemma stack_fp_ok : forall lo W, alloc_ceiling <= lo -> Forall (fun iv : Z * Z => lo <= fst iv) W -> Forall emb_fp_ok W.
Proof.
  intros lo W CEIL H. pose proof alloc_ceiling_range as ACR. induction H as [|iv W' Hiv _ IH]; [apply Forall_nil|].
  apply Forall_cons; [right; unfold AIMG_HI; lia| exact IH].
Qed.

(* [comment removed for export] *)
Definition nobuf_frame (a b c : word) (va : word) (s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 a; C8 b; C8 c; C8 va; C8 va; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition nobuf1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (B VA lo fmt Lmax : Z) : machine_state -> Prop :=
  fun ms1 => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte) (bs rest : list byte),
    ms1 = MS (mkR x1 (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz fmt) (wz 0) x10 x11 x12 x13 x14 x15 x16 x17
                  (wz B) (wz 400) s4 (wz (Z.of_nat (length bs))) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (wz 0x692e4) fc None m1 (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (B, B + 400)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp + -128)
    /\ rw_cells bsegs m1 (bv_unsigned sp + -128) (nobuf_frame (wz 0) (wz 0) (wz 0) (wz VA) s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ u8arr bsegs m1 B (bs ++ Z_to_bv 8 0 :: rest) /\ length (bs ++ Z_to_bv 8 0 :: rest) = 400%nat
    /\ msg_ok bs /\ 0 < Z.of_nat (length bs) <= Lmax.

Lemma nobuf1 : forall (fmt : Z) (v1 v2 v3 : word) (Lmax : Z), vsn_contract fmt v1 v2 v3 Lmax -> 0 < Lmax <= EMB_MSG ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B VA lo : Z) (junk : list byte),
  mem_inv bsegs m -> R_link m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + NOBUF_STACK <= bv_unsigned sp ->
  bv_unsigned sp <= B -> B + 400 <= VA -> VA + 56 <= 2^47 ->
  rw_cells bsegs m VA [C8 v1] -> rw_cells bsegs m (VA + 8) [C8 v2] -> rw_cells bsegs m (VA + 16) [C8 v3] ->
  u8arr bsegs m B junk -> length junk = 400%nat ->
  evt bsegs (nobuf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m B VA lo fmt Lmax)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz B) (wz fmt) (wz VA) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x691e4) fc None m (seg_rom bsegs)).
Proof.
  intros fmt v1 v2 v3 Lmax VSN HLmax. intros until junk. intros MI HL ST CEIL LO HB1 HB2 HVA A1 A2 A3 UB LEN.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof alloc_ceiling_range as ACR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (B, B + 400)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold NOBUF_STACK, EMB_MSG in *. cbv beta delta [wz] in *.
  carve_frame 128%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 12 gi. (* [comment removed for export] *)
  do 4 gi. (* [comment removed for export] *)
  do 5 gi. (* [comment removed for export] *)
  gi. (* [comment removed for export] *)
  gi. gi. gi. gi. gi. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  eapply (VSN (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp F fc B VA lo);
    [exact CEIL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact HVA| exact MI| rewrite unsigned_lit by lia; exact ST
    | exact A1| exact A2| exact A3| exact UB| exact LEN|].
  intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 bs rest MI2 MU2 WM2 ST2 UB2 LEN2 OK HLb.
  rewrite unsigned_lit in MU2, ST2 by lia.
  clear ST UB. transport_after_call bsegs m1 m2 MU2 WM2. clear MU2 WM2 MI.
  retlit 0x692c4.
  remember (Z.of_nat (length bs)) as L eqn:EL.
  lstep. (* [comment removed for export] *)
  cbv beta delta [wz] in *. rewrite (unsigned_lit L) by lia. breg 21 L.
  lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite (AShadow.signed_lit_small L) in Kc by lia; lia| clear Kc]. (* [comment removed for export] *)
  gi. lstep. (* [comment removed for export] *)
  assert (FPOK : Forall emb_fp_ok [(lo, bv_unsigned sp); (B, B + 400)]).
  { apply (stack_fp_ok lo); [exact CEIL|]. fa_lia. }
  eapply (rawwrite_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 B lo bs);
    [exact MI2| exact (link_keep _ m m2 HL MU WM FPOK)| exact (msg_at_of_u8arr m2 B bs rest UB2 OK)| rewrite unsigned_lit by lia; lia| rewrite <- EL; lia
    | rewrite unsigned_lit by lia; exact ST2| exact CEIL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; reflexivity|].
  intros m3 MI3 MU3 WM3 ST3. rewrite unsigned_lit in MU3, ST3 by lia.
  clear ST2. transport_after_call bsegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
  retlit 0x692d4. cbv beta delta [wz] in *.
  gi. lstep. (* [comment removed for export] *)
  assert (LR : Z.of_nat (length bs) + 1 + Z.of_nat (length rest) = 400).
  { revert LEN2. rewrite length_app. cbn [length]. lia. }
  rewrite <- EL in LR.
  eapply (ansi_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 B lo bs rest);
    [exact MI3| exact UB2| exact OK| rewrite <- EL; lia| rewrite unsigned_lit by lia; lia| lia
    | rewrite unsigned_lit by lia; exact ST3| exact CEIL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; reflexivity|].
  intros m4 y10 y11 y13 MI4 MU4 WM4 ST4 UB4. rewrite unsigned_lit in MU4, ST4 by lia.
  clear ST3 UB2. transport_after_call bsegs m3 m4 MU4 WM4. clear MU4 WM4 MI3.
  retlit 0x692dc. cbv beta delta [wz] in *.
  gi. lstep. (* [comment removed for export] *)
  eapply onprint_spec; [rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity|].
  retlit 0x692e4.
  subst L. apply evt_done. unfold nobuf1_post, nobuf_frame. cbv beta delta [wz].
  nexists 16%nat. exists m4, bs, rest. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact FR|].
  split; [exact UB4|]. split; [exact LEN2|]. split; [exact OK| exact HLb].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nobuf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms1 => exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : word -> option byte),
    ms1 = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m1 (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp).

Lemma nobuf2 : forall (ra sp gp tp x1 x5 x6 x7 c8 c9 x10 x11 x12 x13 x14 x15 x16 x17 c19 c20 c21 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (B VA lo : Z),
  mem_inv bsegs m -> R_link m -> R_consts_rest st m ->
  stk bsegs m lo (bv_unsigned sp + -128) -> alloc_ceiling <= lo -> lo + NOBUF_STACK <= bv_unsigned sp -> bv_unsigned sp + 8 <= 2^47 ->
  4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
  rw_cells bsegs m (bv_unsigned sp + -128) (nobuf_frame (wz 0) (wz 0) (wz 0) (wz VA) s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
  evt bsegs (nobuf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR x1 (wz (bv_unsigned sp + -128)) gp tp x5 x6 x7 c8 c9 x10 x11 x12 x13 x14 x15 x16 x17 (wz B) c19 c20 c21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz 0x692f8) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI HL HCR ST CEIL LO SPH RA1 RA2 FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof alloc_ceiling_range as ACR.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold NOBUF_STACK, nobuf_frame in *. cbv beta delta [wz] in *.
  gi. lstep. (* [comment removed for export] *)
  eapply (logmsg_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m st); [exact HL| exact HCR| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity|].
  retlit 0x69300. cbv beta delta [wz] in *.
  gi. gi. gi. lstep. (* [comment removed for export] *)
  eapply (unmap00_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo);
    [exact MI| rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity|].
  intros m3 MI3 MU3 WM3 ST3. rewrite unsigned_lit in MU3, ST3 by lia.
  clear ST. transport_after_call bsegs m m3 MU3 WM3. clear MU3 WM3 MI.
  retlit 0x69310. cbv beta delta [wz] in *.
  do 11 gi. gi. (* [comment removed for export] *)
  release_frame FR ST3 (bv_unsigned sp).
  gi. (* [comment removed for export] *)
  apply evt_done. unfold nobuf2_post. nexists 15%nat. exists m3. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3| exact ST3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ceil_fp_disj : forall W a n, Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> a + n <= alloc_ceiling -> disjoint_from W a n.
Proof. intros W a n H Ha. induction H as [|[l h] W' Hiv _ IH]; [exact I|]. cbn [fst] in Hiv. cbn [disjoint_from]. split; [lia| exact IH]. Qed.

Lemma emb_cells_keep : forall W m m' d sz, emb_cells m d sz -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> (d <> 0 -> d + EMB_CAP <= alloc_ceiling) -> emb_cells m' d sz.
Proof.
  intros W m m' d sz [[j0 [j1 EC]] VIS] MU WM HW HD. pose proof alloc_ceiling_range as ACR. split.
  - exists j0, j1. eapply (rw_cells_transport bsegs _ m m'); [exact EC| exact MU| exact WM|]. apply ceil_fp_disj; [exact HW|]. unfold A_EMB. cbn. lia.
  - intros NZ. eapply stk_transport_disjoint; [exact (VIS NZ)| exact MU| exact WM|]. apply ceil_fp_disj; [exact HW|]. specialize (HD NZ). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition emb_step (mo : Model) (R d : Z) (mo' : Model) (R' d' : Z) : Prop :=
  (d <> 0 /\ d' = d /\ mo' = mo /\ R' = R)
  \/ (d = 0 /\ d' <> 0 /\ mmap_grant mo (wz d') EMB_CAP /\ mo' = mm_add_map (wz d') (wz EMB_CAP) mo /\ R' = R - EMB_CAP).

Lemma nobuf_spec : forall (fmt : Z) (v1 v2 v3 : word) (Lmax : Z), vsn_contract fmt v1 v2 v3 Lmax -> 0 < Lmax <= EMB_MSG ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z)
         (st : rtstate) (d sz B VA lo : Z) (junk : list byte) (P : machine_state -> Model -> lghost -> Prop),
  mem_inv bsegs m -> R_link m -> R_consts_rest st m -> 4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
  emb_cells m d sz -> 0 <= sz -> (d = 0 -> sz = 0) -> sz + Lmax <= EMB_CAP ->
  (d <> 0 -> AIMG_HI <= d /\ d + EMB_CAP <= alloc_ceiling /\ d mod 4096 = 0) ->
  (d = 0 -> EMB_CAP <= R /\ mmap_placeable mo EMB_CAP) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + NOBUF_STACK <= bv_unsigned sp ->
  bv_unsigned sp <= B -> B + 400 <= VA -> VA + 56 <= 2^47 ->
  rw_cells bsegs m VA [C8 v1] -> rw_cells bsegs m (VA + 8) [C8 v2] -> rw_cells bsegs m (VA + 16) [C8 v3] ->
  u8arr bsegs m B junk -> length junk = 400%nat ->
  (forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) (mo' : Model) (R' d' L : Z),
     mem_inv bsegs m' ->
     munch [(lo, bv_unsigned sp); (B, B + 400); (A_EMB, A_EMB + 56); (d', d' + EMB_CAP)] m m' -> wmono bsegs m m' ->
     stk bsegs m' lo (bv_unsigned sp) -> emb_cells m' d' (sz + L) -> 0 < L <= Lmax ->
     emb_step mo R d mo' R' d' -> d' + EMB_CAP <= alloc_ceiling ->
     R_link m' -> R_consts_rest st m' ->
     forall buf' : list byte, u8arr bsegs m' B buf' -> length buf' = 400%nat ->
     LSCPS bsegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (ret_pc ra) fc None m' (seg_rom bsegs)) mo' (mkG G R')) ->
  LSCPS bsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz B) (wz fmt) (wz VA) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz 0x691e4) fc None m (seg_rom bsegs)) mo (mkG G R).
Proof.
  intros fmt v1 v2 v3 Lmax VSN HLmax. intros until P.
  intros MI HL HCR RA1 RA2 EC SZ0 SZD SZL DNZ DZ ST CEIL LO HB1 HB2 HVA A1 A2 A3 UB LEN K.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof alloc_ceiling_range as ACR.
  apply lscps_assume. intros NWX HOK HBINV.
  apply lscps_step_evt.
  eapply evt_cut.
  { eapply (nobuf1 fmt v1 v2 v3 Lmax VSN HLmax ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B VA lo junk);
      [exact MI| exact HL| exact ST| exact CEIL| exact LO| exact HB1| exact HB2| exact HVA| exact A1| exact A2| exact A3| exact UB| exact LEN]. }
  intros ms1 nelH_; (nelim nelH_ 29%nat; intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m1 bs rest -> MU1 WM1 MI1 ST1 FR1 UB1 LEN1 OK1 HL1).
  unfold NOBUF_STACK in LO.
  assert (FPOK : Forall emb_fp_ok [(lo, bv_unsigned sp); (B, B + 400)]).
  { apply (stack_fp_ok lo); [exact CEIL|]. fa_lia. }
  assert (FPC : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) [(lo, bv_unsigned sp); (B, B + 400)]).
  { fa_lia. }
  pose proof (link_keep _ m m1 HL MU1 WM1 FPOK) as HL1'.
  pose proof (consts_rest_keep st _ m m1 HCR MU1 WM1 FPOK) as HCR1.
  assert (EC1 : emb_cells m1 d sz).
  { apply (emb_cells_keep _ m m1 d sz EC MU1 WM1 FPC). intros NZ. (nelim (DNZ NZ) 3%nat; intros _ X _). exact X. }
  pose proof (printfcb_cell st m1 HCR1) as CB. unfold A_PRINTF_CB, A_EMB_CB, NOBUF_STACK, EMB_MSG in *. cbv beta delta [wz] in *.
  lstep. lstep. fl. (* [comment removed for export] *)
  gi. (* [comment removed for export] *)
  gi. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done.
  pose proof emb_append_proof as EAP. unfold emb_append_stmt in EAP. cbn zeta in EAP.
  eapply EAP with (st := st) (msg := B) (bs := bs) (d := d) (sz := sz) (lo := lo);
    [exact MI1| exact HL1'| exact HCR1| reflexivity| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity
    | exact (msg_at_of_u8arr m1 B bs rest UB1 OK1)| unfold EMB_MSG; lia| rewrite unsigned_lit by lia; lia| lia
    | exact EC1| exact SZ0| exact SZD| lia| exact DNZ| exact DZ| rewrite unsigned_lit by lia; exact ST1| exact CEIL
    | rewrite unsigned_lit by lia; unfold EMB_APPEND_STACK; lia| rewrite unsigned_lit by lia; lia|].
  intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 mo' R' d' MI2 MU2 WM2 ST2 EC2 DISJ HL2 HCR2 MA2.
  rewrite unsigned_lit in MU2, ST2 by lia.
  assert (DHI : d' + EMB_CAP <= alloc_ceiling /\ AIMG_HI <= d').
  { destruct DISJ as [(NZ & -> & _ & _)|(_ & NZ' & GR & _ & _)].
    - (nelim (DNZ NZ) 3%nat; intros X1 X2 _). split; assumption.
    - pose proof (grant_above_image mo (wz d') EMB_CAP HOK GR ltac:(unfold EMB_CAP; lia)) as ALO.
      (nelim GR 4%nat; intros _ GP GC _). unfold wz in *.
      assert (D64 : 0 <= d' < 2^64 \/ ~ (0 <= d' < 2^64)) by lia. destruct D64 as [D64|D64].
      + rewrite unsigned_lit in GC, ALO by lia. split; [exact GC| exact ALO].
      + exfalso. clear - EC2 NZ' D64. destruct EC2 as [_ VIS]. specialize (VIS NZ'). (nelim VIS 3%nat; intros V1 V2 _). unfold EMB_CAP in *. lia. }
  destruct DHI as [DHI DLO].
  eapply (rw_cells_transport bsegs _ m1 m2) in FR1; [| exact MU2| exact WM2| unfold nobuf_frame, A_EMB, EMB_CAP, AIMG_HI in *; cbn; lia].
  eapply (u8arr_transport bsegs _ m1 m2) in UB1; [| exact MU2| exact WM2| cbn [disjoint_from]; rewrite LEN1; unfold A_EMB, EMB_CAP, AIMG_HI in *; lia].
  assert (MU02 : munch [(lo, bv_unsigned sp); (B, B + 400); (A_EMB, A_EMB + 56); (d', d' + EMB_CAP)] m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; subfp|]. eapply munch_weaken; [| exact MU2]; subfp. }
  pose proof (wmono_trans bsegs _ _ _ WM1 WM2) as WM02.
  apply lscps_step_evt. retlit 0x692f8.
  eapply evt_cut.
  { eapply (nobuf2 ra sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 st B VA lo);
      [exact MI2| exact HL2| exact HCR2| exact ST2| exact CEIL| unfold NOBUF_STACK; lia| lia| exact RA1| exact RA2| exact FR1]. }
  intros ms3 nelH_; (nelim nelH_ 21%nat; intros z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 -> MU3 WM3 MI3 ST3).
  assert (FP3 : Forall emb_fp_ok [(lo, bv_unsigned sp)]) by (apply (stack_fp_ok lo); [exact CEIL| fa_lia]).
  assert (FPC3 : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) [(lo, bv_unsigned sp)]) by fa_lia.
  eapply (u8arr_transport bsegs _ m2 m3) in UB1; [| exact MU3| exact WM3| cbn [disjoint_from]; rewrite LEN1; lia].
  apply evt_done.
  eapply (K z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 mo' R' d' (Z.of_nat (length bs)));
    [exact MI3| | exact (wmono_trans bsegs _ _ _ WM02 WM3)| exact ST3| | exact HL1| exact DISJ| exact DHI
    | exact (link_keep _ m2 m3 HL2 MU3 WM3 FP3)| exact (consts_rest_keep st _ m2 m3 HCR2 MU3 WM3 FP3)| exact UB1| exact LEN1].
  - eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU3]; subfp.
  - apply (emb_cells_keep _ m2 m3 d' _ EC2 MU3 WM3 FPC3). intros _. exact DHI.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma printf_spec : forall (fmt : Z) (v1 v2 v3 : word) (Lmax : Z), vsn_contract fmt v1 v2 v3 Lmax -> 0 < Lmax <= EMB_MSG ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z)
         (st : rtstate) (d sz lo : Z) (P : machine_state -> Model -> lghost -> Prop),
  mem_inv bsegs m -> R_link m -> R_consts_rest st m -> 4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
  emb_cells m d sz -> 0 <= sz -> (d = 0 -> sz = 0) -> sz + Lmax <= EMB_CAP ->
  (d <> 0 -> AIMG_HI <= d /\ d + EMB_CAP <= alloc_ceiling /\ d mod 4096 = 0) ->
  (d = 0 -> EMB_CAP <= R /\ mmap_placeable mo EMB_CAP) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + PRINTF_STACK <= bv_unsigned sp -> bv_unsigned sp + 8 <= 2^47 ->
  (forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : word -> option byte) (mo' : Model) (R' d' L : Z),
     mem_inv bsegs m' ->
     munch [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56); (d', d' + EMB_CAP)] m m' -> wmono bsegs m m' ->
     stk bsegs m' lo (bv_unsigned sp) -> emb_cells m' d' (sz + L) -> 0 < L <= Lmax ->
     emb_step mo R d mo' R' d' -> d' + EMB_CAP <= alloc_ceiling ->
     R_link m' -> R_consts_rest st m' ->
     LSCPS bsegs P (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (ret_pc ra) fc None m' (seg_rom bsegs)) mo' (mkG G R')) ->
  LSCPS bsegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz fmt) v1 v2 v3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz 0x68bdc) fc None m (seg_rom bsegs)) mo (mkG G R).
Proof.
  intros fmt v1 v2 v3 Lmax VSN HLmax. intros until P.
  intros MI HL HCR RA1 RA2 EC SZ0 SZD SZL DNZ DZ ST CEIL LO SPH K.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof alloc_ceiling_range as ACR. unfold PRINTF_STACK in LO.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply lscps_step_evt. cbv beta delta [wz] in *.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  rename FR into FRP.
  do 15 gi. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  carve_frame 432%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [400;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 5 gi. (* [comment removed for export] *)
  do 6 gi. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (proj1 (RT_kit.rw_cells_app m0 _ [CB 400 (firstn 400 junk0)] [C8 s2; C8 s1; C8 s0; C8 (Z_to_bv 64 429084)]) FR) as [BUF FRS];
    cbn [cells_size Cells.csize Nat.add] in FRS; clear FR.
  replace (bv_unsigned sp + -512 + Z.of_nat 400) with (bv_unsigned sp + -112) in FRS by lia.
  call internal_memset_Z; [exact MI| lia| lia| lia| exact BUF| rewrite unsigned_lit by lia; exact ST| exact CEIL|].
  after_call.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  do 4 gi. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (u8arr_of_rw_cells bsegs _ _ _ _ POST) as UB. clear POST.
  (* [comment removed for export] *)
  pose proof (proj1 (RT_kit.rw_cells_app mc _ [C8 (Z_to_bv 64 (bv_unsigned sp + -56)); C8 ra; CB 8 (firstn 8 (skipn 8 (skipn 8 junk)))]
                       [C8 v1; C8 v2; C8 v3; C8 a4; C8 a5; C8 a6; C8 a7]) FRP) as [_ VA1]; cbn [cells_size Cells.csize Nat.add] in VA1.
  replace (bv_unsigned sp + -80 + Z.of_nat 24) with (bv_unsigned sp + -56) in VA1 by lia.
  pose proof (proj1 (RT_kit.rw_cells_app mc _ [C8 v1] [C8 v2; C8 v3; C8 a4; C8 a5; C8 a6; C8 a7]) VA1) as [A1 VA2]; cbn [cells_size Cells.csize Nat.add] in VA2.
  replace (bv_unsigned sp + -56 + Z.of_nat 8) with (bv_unsigned sp + -56 + 8) in VA2 by lia.
  pose proof (proj1 (RT_kit.rw_cells_app mc _ [C8 v2] [C8 v3; C8 a4; C8 a5; C8 a6; C8 a7]) VA2) as [A2 VA3]; cbn [cells_size Cells.csize Nat.add] in VA3.
  replace (bv_unsigned sp + -56 + 8 + Z.of_nat 8) with (bv_unsigned sp + -56 + 16) in VA3 by lia.
  pose proof (proj1 (RT_kit.rw_cells_app mc _ [C8 v3] [C8 a4; C8 a5; C8 a6; C8 a7]) VA3) as [A3 _]. clear VA1 VA2 VA3.
  assert (FPOK : Forall emb_fp_ok [(lo, bv_unsigned sp)]) by (apply (stack_fp_ok lo); [exact CEIL| fa_lia]).
  assert (FPC : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) [(lo, bv_unsigned sp)]) by fa_lia.
  apply evt_done.
  eapply (nobuf_spec fmt v1 v2 v3 Lmax VSN HLmax) with (st := st) (d := d) (sz := sz) (B := bv_unsigned sp + -512) (VA := bv_unsigned sp + -56) (lo := lo)
                                                       (junk := repeat (zb 170) (Z.to_nat 400));
    [exact MI| exact (link_keep _ m mc HL MU WM FPOK)| exact (consts_rest_keep st _ m mc HCR MU WM FPOK)
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity
    | apply (emb_cells_keep _ m mc d sz EC MU WM FPC); intros NZ; (nelim (DNZ NZ) 3%nat; intros _ X _); exact X
    | exact SZ0| exact SZD| exact SZL| exact DNZ| exact DZ| rewrite unsigned_lit by lia; exact ST| exact CEIL
    | rewrite unsigned_lit by lia; unfold NOBUF_STACK; lia| rewrite unsigned_lit by lia; lia| lia| lia| exact A1| exact A2| exact A3| exact UB
    | apply repeat_length|].
  intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' mo' R' d' L MI' MU' WM' ST' EC' HL' STEP DHI HL2 HCR2 buf' UB' LEN'.
  rewrite unsigned_lit in MU', ST' by lia.
  eapply (rw_cells_transport bsegs _ mc m') in FRP; [| exact MU'| exact WM'| unfold A_EMB, EMB_CAP in *; cbn; lia].
  eapply (rw_cells_transport bsegs _ mc m') in FRS; [| exact MU'| exact WM'| unfold A_EMB, EMB_CAP in *; cbn; lia].
  assert (MU2 : munch [(lo, bv_unsigned sp); (A_EMB, A_EMB + 56); (d', d' + EMB_CAP)] m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU]; subfp|]. eapply munch_weaken; [| exact MU']; subfp. }
  pose proof (wmono_trans bsegs _ _ _ WM WM') as WM2. clear MU WM MU' WM' A1 A2 A3 UB ST MI.
  apply lscps_step_evt. retlit 0x68c6c. cbv beta delta [wz] in *.
  do 4 gi. gi. (* [comment removed for export] *)
  pose proof (rw_cells_of_u8arr bsegs _ _ _ UB') as BUF'. rewrite LEN' in BUF'. clear UB'.
  replace (bv_unsigned sp + -112) with (bv_unsigned sp + -512 + 400) in FRS by lia.
  glue BUF' FRS.
  release_frame BUF' ST' (bv_unsigned sp + -80).
  gi. (* [comment removed for export] *)
  gi. gi. (* [comment removed for export] *)
  release_frame FRP ST' (bv_unsigned sp).
  gi. (* [comment removed for export] *)
  apply evt_done.
  eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' mo' R' d' L); [exact MI'| exact MU2| exact WM2| exact ST'| exact EC'| exact HL'| exact STEP| exact DHI| exact HL2| exact HCR2].
Qed.

End CeilWrap.
End RTW_p_oom_pf.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Module RTW_p_oom.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_emb0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_p_oom_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_p_oom_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_oom_lib RTW_oom_an OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb RTW_oom_vsn2 RTW_p_oom_pf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac gi := lstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_lia | _ => idtac end.
Ltac retlit n := replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac fa_lia := repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

(* [comment removed for export] *)
Definition emb_sep (st : rtstate) (mo : Model) (Rc : Z) : Prop :=
  forall d' : Z, (emb_d st <> 0 /\ d' = emb_d st) \/ (emb_d st = 0 /\ mmap_grant mo (wz d') EMB_CAP) ->
    d' + EMB_CAP <= Rc \/ Rc + 128 <= d'.

Definition oom_arm_sep_stmt : Prop :=
  forall (sp gp tp x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z)
         (st : rtstate) (Rc c lo : Z) (fs6 fs5 fs4 fs3 fs2 fs1 fs0 fra : word)
         (al z1 mp z2 : word) (jr je js : list byte)
         (P : machine_state -> Model -> lghost -> Prop),
  R_link m -> R_consts st m -> RTWF st ->
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + OOM_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 64 <= 2^47 ->
  rw_cells bsegs m (bv_unsigned sp) (pop_frame fs6 fs5 fs4 fs3 fs2 fs1 fs0 fra) ->
  rw_cells bsegs m (Rc + 32) [C8 al; C8 z1; C8 mp; C8 z2; CB 4 jr; C1 (Z_to_bv 8 0); CB 3 je; CB 56 js] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling ->
  1 <= c <= 30 ->
  0 <= emb_sz st -> emb_sz st + EMB_MSG <= EMB_MSG * 33 ->
  (emb_d st = 0 -> EMB_CAP <= R /\ mmap_placeable mo EMB_CAP) ->
  emb_sep st mo Rc ->
  (forall (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (m' : word -> option byte) (mo' : Model) (R' : Z) (d' sz' : Z),
     mem_inv bsegs m' ->
     munch ([(lo, bv_unsigned sp + 64); (Rc + 68, Rc + 69); (A_EMB, A_EMB + 56)] ++ (if d' =? 0 then [] else [(d', d' + EMB_CAP)])) m m' ->
     wmono bsegs m m' ->
     stk bsegs m' lo (bv_unsigned sp + 64) ->
     rw_cells bsegs m' (Rc + 32) [C8 al; C8 z1; C8 mp; C8 z2; CB 4 jr; C1 (Z_to_bv 8 1); CB 3 je; CB 56 js] ->
     emb_cells m' d' sz' ->
     emb_sz st <= sz' <= emb_sz st + EMB_MSG ->
     ((emb_d st <> 0 /\ d' = emb_d st /\ mo' = mo /\ R' = R)
      \/ (emb_d st = 0 /\ d' <> 0 /\ mmap_grant mo (wz d') EMB_CAP
          /\ mo' = mm_add_map (wz d') (wz EMB_CAP) mo /\ R' = R - EMB_CAP)) ->
     R_link m' ->
     LSCPS bsegs P (MS (mkR fra (wz (bv_unsigned sp + 64)) gp tp y5 y6 y7 fs0 fs1 (wz 0) y11 y12 y13 y14 y15 y16 y17
                          fs2 fs3 fs4 fs5 fs6 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                     F (ret_pc fra) fc None m' (seg_rom bsegs)) mo' (mkG G R')) ->
  LSCPS bsegs P (MS (mkR (wz 0x370cc) sp gp tp x5 x6 x7 (wz Rc) x9 x10 x11 (wz c) x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                   F (wz A_OOM_ARM) fc None m (seg_rom bsegs)) mo (mkG G R).

(* [comment removed for export] *)
Lemma emb_cells_keep2 : forall W m m' d sz, emb_cells m d sz -> munch W m m' -> wmono bsegs m m' ->
  disjoint_from W A_EMB 56 -> (d <> 0 -> AIMG_HI <= d) -> emb_cells m' d sz.
Proof.
  intros W m m' d sz [[j0 [j1 EC]] VIS] MU WM DJ HD. split.
  - exists j0, j1. eapply (rw_cells_transport bsegs _ m m'); [exact EC| exact MU| exact WM| exact DJ].
  - intros NZ. eapply stk_wmono_noseg; [exact (VIS NZ)| exact WM| exact (HD NZ)].
Qed.

Theorem oom_arm_proof : oom_arm_sep_stmt.
Proof.
  unfold oom_arm_sep_stmt. intros until P.
  intros HL HC WF MI ST CEIL LO SPH FRP RC RCLO RCHI Hc SZ0 SZM DZ SEP K.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof alloc_ceiling_range as ACR.
  destruct (R_consts_split st m HC) as [HCR HE]. pose proof (emb_cells_of_R_emb st m HE) as EC.
  pose proof (got_toolname m HL) as G1. pose proof (toolname_cell st m HCR) as G2.
  pose proof (munch_refl [(lo, bv_unsigned sp + 64); (Rc + 68, Rc + 69)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_OOM_ARM, OOM_STACK, GOT_TOOLNAME, A_TOOLNAME, A_ASAN_STR, KHIGHMEM_BEG, pop_frame in *. cbv beta delta [wz] in *.
  apply lscps_assume. intros NWX HOK HBINV.
  apply lscps_step_evt.
  lstep. lstep. fl. (* [comment removed for export] *)
  gi. (* [comment removed for export] *)
  gi. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  lstep. lstep. fl. (* [comment removed for export] *)
  gi. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  assert (FP1 : Forall emb_fp_ok [(lo, bv_unsigned sp + 64); (Rc + 68, Rc + 69)]).
  { apply Forall_cons; [right; unfold AIMG_HI; cbn [fst]; lia|]. apply Forall_cons; [right; unfold AIMG_HI; cbn [fst]; lia| apply Forall_nil]. }
  pose proof (link_keep _ m m1 HL MU WM FP1) as HL1.
  pose proof (consts_rest_keep st _ m m1 HCR MU WM FP1) as HCR1.
  assert (DR : emb_d st <> 0 -> AIMG_HI <= emb_d st /\ emb_d st + EMB_CAP <= alloc_ceiling /\ emb_d st mod 4096 = 0).
  { intros NZ. destruct (emb_block_range st WF NZ) as (BK & X2 & X3). split; [exact (ablk_img _ _ BK)| split; assumption]. }
  assert (EC1 : emb_cells m1 (emb_d st) (emb_sz st)).
  { apply (emb_cells_keep2 _ m m1 _ _ EC MU WM); [unfold A_EMB; cbn; lia| intros NZ; exact (proj1 (DR NZ))]. }
  apply evt_done.
  eapply (printf_spec FMT1 (Z_to_bv 64 131939) (Z_to_bv 64 c) x13 33 (vsn_fmt1 (Z_to_bv 64 c) x13) ltac:(unfold EMB_MSG; lia))
    with (st := st) (d := emb_d st) (sz := emb_sz st) (lo := lo);
    [exact MI| exact HL1| exact HCR1| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity
    | exact EC1| exact SZ0| exact (wb_emb_d0 st (wf_base_ok st WF))| unfold EMB_MSG, EMB_CAP in *; lia| exact DR| exact DZ| exact ST| exact CEIL
    | unfold PRINTF_STACK; lia| lia|].
  intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 mo1 R1 d1 L1 MI2 MU2 WM2 ST2 EC2 HL1b STEP1 DHI1 HL2 HCR2.
  (* [comment removed for export] *)
  assert (D1 : d1 <> 0 /\ AIMG_HI <= d1 /\ d1 mod 4096 = 0 /\ (d1 + EMB_CAP <= Rc \/ Rc + 128 <= d1)).
  { destruct STEP1 as [(NZ & -> & _ & _)|(Z0 & NZ' & GR & _ & _)].
    - destruct (DR NZ) as (X1 & _ & X3). split; [exact NZ|]. split; [exact X1|]. split; [exact X3|]. apply SEP. left. split; [exact NZ| reflexivity].
    - split; [exact NZ'|]. pose proof (SEP d1 (or_intror (conj Z0 GR))) as SP1.
      pose proof (grant_above_image mo (Z_to_bv 64 d1) EMB_CAP HOK GR ltac:(unfold EMB_CAP; lia)) as ALO.
      destruct GR as (GA & GP & _ & _). unfold page_size in GA.
      assert (D64 : 0 <= d1 < 2^64).
      { pose proof (SysStep.stk_lo_nonneg _ _ _ _ (proj2 EC2 NZ')) as D0. unfold EMB_CAP in *. lia. }
      rewrite unsigned_lit in GA, ALO by lia. split; [exact ALO|]. split; [exact GA| exact SP1]. }
  destruct D1 as (D1nz & D1lo & D1al & D1sep).
  eapply (rw_cells_transport bsegs _ m1 m2) in RC; [| exact MU2| exact WM2| unfold A_EMB, EMB_CAP in *; cbn; lia].
  eapply (rw_cells_transport bsegs _ m1 m2) in FRP; [| exact MU2| exact WM2| unfold A_EMB, EMB_CAP in *; cbn; lia].
  assert (MU02 : munch [(lo, bv_unsigned sp + 64); (Rc + 68, Rc + 69); (A_EMB, A_EMB + 56); (d1, d1 + EMB_CAP)] m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU]; subfp|]. eapply munch_weaken; [| exact MU2]; subfp. }
  pose proof (wmono_trans bsegs _ _ _ WM WM2) as WM02. clear MU WM MU2 WM2 G1 G2 EC1 HL1 HCR1 MI ST.
  apply lscps_step_evt. retlit 0x37404. cbv beta delta [wz] in *.
  pose proof (csize_pos c ltac:(lia)) as CS1. pose proof (csize_max c Hc) as CS2.
  (* [comment removed for export] *)
  eapply evt_cut with (P := fun ms => exists a0' a1' : word,
     ms = MS (mkR (Z_to_bv 64 0x37404) sp gp tp y5 y6 y7 (Z_to_bv 64 c) x9 a0' a1' (Z_to_bv 64 c) (Z_to_bv 64 (csize c)) y14 y15 y16 y17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31) F (Z_to_bv 64 0x37468) fc None m2 (seg_rom bsegs)).
  { gi. gi. gi. (* [comment removed for export] *)
    gi. (* [comment removed for export] *)
    destruct (Z_le_gt_dec c 16) as [C16|C17].
    - gi. (* [comment removed for export] *)
      lstep. fl. (* [comment removed for export] *)
      gi. (* [comment removed for export] *)
      replace (Z.shiftl c 5) with (32 * c) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      apply evt_done. do 2 eexists. rewrite (csize_small c ltac:(lia)). reflexivity.
    - gi. (* [comment removed for export] *)
      eapply oom_size17; [lia|]. intros a0' a1'. apply evt_done. exists a0', a1'. reflexivity. }
  intros ms (a0' & a1' & ->).
  lstep. lstep. fl. (* [comment removed for export] *)
  gi. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  apply evt_done.
  eapply (printf_spec FMT2 (Z_to_bv 64 4096) (Z_to_bv 64 c) (Z_to_bv 64 (csize c)) 67 (vsn_fmt2 c (csize c) Hc ltac:(lia)) ltac:(unfold EMB_MSG; lia))
    with (st := st) (d := d1) (sz := emb_sz st + L1) (lo := lo);
    [exact MI2| exact HL2| exact HCR2| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; reflexivity
    | exact EC2| lia| intros Z1; exfalso; exact (D1nz Z1)| unfold EMB_MSG, EMB_CAP in *; lia
    | intros _; split; [exact D1lo| split; [exact DHI1| exact D1al]]| intros Z1; exfalso; exact (D1nz Z1)| exact ST2| exact CEIL
    | unfold PRINTF_STACK; lia| lia|].
  intros z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m3 mo2 R2 d2 L2 MI3 MU3 WM3 ST3 EC3 HL2b STEP2 DHI2 HL3 HCR3.
  destruct STEP2 as [(_ & -> & -> & ->)|(Z1 & _)]; [| exfalso; exact (D1nz Z1)].
  eapply (rw_cells_transport bsegs _ m2 m3) in RC; [| exact MU3| exact WM3| unfold A_EMB, EMB_CAP in *; cbn; lia].
  eapply (rw_cells_transport bsegs _ m2 m3) in FRP; [| exact MU3| exact WM3| unfold A_EMB, EMB_CAP in *; cbn; lia].
  assert (MU03 : munch [(lo, bv_unsigned sp + 64); (Rc + 68, Rc + 69); (A_EMB, A_EMB + 56); (d1, d1 + EMB_CAP)] m m3).
  { eapply munch_trans; [exact MU02|]. eapply munch_weaken; [| exact MU3]; subfp. }
  pose proof (wmono_trans bsegs _ _ _ WM02 WM3) as WM03. clear MU02 WM02 MU3 WM3 MI2 ST2.
  apply lscps_step_evt. retlit 0x37478. cbv beta delta [wz] in *.
  gi. gi. (* [comment removed for export] *)
  gi. (* [comment removed for export] *)
  do 8 gi. gi. (* [comment removed for export] *)
  release_frame FRP ST3 (bv_unsigned sp + 64).
  gi. (* [comment removed for export] *)
  apply evt_done.
  eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo1 R1 d1 (emb_sz st + L1 + L2));
    [exact MI3| | exact WM03| exact ST3| exact RC| exact EC3| unfold EMB_MSG; lia| | exact HL3].
  - replace (d1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact D1nz). cbn [app]. exact MU03.
  - destruct STEP1 as [(NZ & E1 & E2 & E3)|(Z0 & NZ' & GR & E2 & E3)];
      [left; exact (conj NZ (conj E1 (conj E2 E3)))| right; exact (conj Z0 (conj NZ' (conj GR (conj E2 E3))))].
Qed.

End CeilWrap.
End RTW_p_oom.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_mmapN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_mmapN.RTW_sec_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_kit RTW_p_map.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_loops.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_efa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_pop1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_finx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_finx.RTW_p_pop2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_gfa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_refillw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_zone RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_cd_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_cd_main.RTW_p_absf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_pop RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_cost RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_finx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_finx.RTW_p_refillA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_refill RT_grant RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_emb0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_embz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_embz.RT_emb.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_embz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_emb.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_emb.RTW_p_oom_iface.
Import RTW_p_oom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_finx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac3 RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_libo.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_kitL.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac djlr := first [left; lia | right; lia | lia].

Lemma outside_in : forall W x l h, outside W x -> In (l, h) W -> ~ (l <= x < h).
Proof. induction W as [|[l' h'] W IH]; intros x l h HO Hin; [destruct Hin|]. cbn in HO. destruct HO as [H1 H2]. destruct Hin as [E|Hin]; [injection E as <- <-; exact H1| exact (IH x l h H2 Hin)]. Qed.
Lemma sub_fp_incl : forall W W' : list (Z * Z), Forall (fun iv => exists l h, In (l, h) W' /\ l <= fst iv /\ snd iv <= h) W -> sub_fp W W'.
Proof.
  intros W W' H x HO. induction H as [|[l0 h0] W0 (l & h & Hin & H1 & H2) _ IH]; [exact I|]. cbn [fst snd] in *. cbn. split; [| exact IH].
  intros Hx. apply (outside_in W' x l h HO Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma fail_tail : forall (sp gp tp v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v18 v20 v21 v22 v24 v25 v26 v27 v28 v29 v30 v31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m' : word -> option byte)
    (Rc pc n nf cls lo : Z) (jG jR : list byte),
  mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp + -32 + -128) -> alloc_ceiling <= lo -> lo + 160 <= bv_unsigned sp ->
  rw_cells bsegs m' (bv_unsigned sp + -32 + -128) (gfa_frame jG s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 (wz n) (wz pc) (wz 0x36d50)) ->
  rw_cells bsegs m' (bv_unsigned sp + -32) (refill_frame jR s1 s0 ra) ->
  rw_cells bsegs m' Rc [C8 (wz MTX_LOCKED); C8 (wz 0); C8 (Z_to_bv 64 nf)] ->
  rw_cells bsegs m' pc [W4 0; W4 (cmaxcount cls); W8 (csize cls)] ->
  KHIGHMEM_BEG <= Rc -> Rc + 128 <= alloc_ceiling -> Rc mod 8 = 0 ->
  (4096 <= pc /\ (pc + 80 <= AIMG_LO \/ AIMG_HI <= pc)) -> pc + 80 <= alloc_ceiling -> (pc + 80 <= Rc \/ Rc + 128 <= pc) -> 1 <= n <= 8 ->
  evt bsegs (fun ms5 => exists (w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 : word) (m'' : word -> option byte),
      ms5 = MS (mkR ra sp gp tp w5 w6 w7 s0 s1 (wz 0) w11 w12 w13 w14 w15 w16 w17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w28 w29 w30 w31) F (ret_pc ra) fc None m'' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (Rc, Rc + 8); (pc, pc + 4)] m' m'' /\ wmono bsegs m' m'' /\ mem_inv bsegs m'' /\ stk bsegs m'' lo (bv_unsigned sp)
      /\ rw_cells bsegs m'' Rc [C8 (wz 0); C8 (wz 0); C8 (Z_to_bv 64 nf)] /\ rw_cells bsegs m'' pc [W4 0; W4 (cmaxcount cls); W8 (csize cls)])
    (MS (mkR (wz 0x370cc) (wz (bv_unsigned (wz (bv_unsigned sp + -32)) + -128)) gp tp v5 v6 v7 (wz Rc) (wz A_ALLOC) (wz 0) v11 v12 v13 v14 v15 v16 v17
             v18 (wz 2305843009213693952) v20 v21 v22 (wz MTX_LOCKED) v24 v25 v26 v27 v28 v29 v30 v31)
        F (ret_pc (wz 0x370cc)) fc None m' (seg_rom bsegs)).
Proof.
  intros until jR. intros MI' ST' HCE LO2 FRG' FRR' RIa' PCC' RC1 RC2 RC8 PC1 PC2 RCP NR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof alloc_ceiling_range as ACR.
  assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (unfold wz; apply unsigned_lit; lia).
  cbv beta delta [wz]. replace (ret_pc (Z_to_bv 64 225484)) with (Z_to_bv 64 225484 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  eapply evt_cut.
  { eapply (gfa_fail (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp) with (lo := lo);
      [exact MI'| unfold wz in E32; rewrite E32; exact ST'| exact HCE| unfold wz in E32; rewrite E32; lia| unfold wz in E32; rewrite E32; exact FRG'| exact RIa'
      | exact RC1| exact RC2| exact RC8]. }
  cbv beta. intros ms4 nelH_; (nelim nelH_ 21%nat; intros z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 -> MU4 WM4 MI4 ST4 RIa4).
  unfold wz in E32. rewrite E32 in MU4, ST4. cbv beta delta [wz].
  replace (ret_pc (Z_to_bv 64 224592)) with (Z_to_bv 64 224592 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  pose proof FRR' as FRR4. eapply (rw_cells_transport bsegs _ m' m4) in FRR4; [| exact MU4| exact WM4| unfold refill_frame, KHIGHMEM_BEG in *; cbn; lia].
  pose proof PCC' as PCC4. eapply (rw_cells_transport bsegs _ m' m4) in PCC4; [| exact MU4| exact WM4| unfold KHIGHMEM_BEG in *; cbn; lia].
  eapply evt_cut.
  { eapply (refill_ret sp gp tp) with (lo := lo) (r := 0); [exact MI4| exact ST4| exact HCE| lia| exact FRR4| exact PCC4| exact PC1| exact PC2| lia| lia]. }
  cbv beta. intros ms5 nelH_; (nelim nelH_ 21%nat; intros w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m5 -> MU5 WM5 MI5 ST5 PCC5).
  cbn [Z.eqb] in PCC5.
  apply evt_done. nexists 14%nat. exists m5. split; [reflexivity|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_weaken; [| exact MU5]]; clear; subfp. }
  split; [eapply wmono_trans; [exact WM4| exact WM5]|]. split; [exact MI5|]. split; [exact ST5|].
  split; [| exact PCC5].
  eapply (rw_cells_transport bsegs _ m4 m5); [exact RIa4| exact MU5| exact WM5| unfold KHIGHMEM_BEG in *; cbn; lia].
Qed.

Theorem refill_proof : refill_spec.
Proof.
  unfold refill_spec.
  intros ra sp gp tp x5 x6 x7 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mo g st0 cls lo.
  intros HRTS Hc HC0 -> -> -> -> TP HPV ST HCE LO2 MI.
  destruct g as [G R]. cbn [g_res] in HPV. (nelim HRTS 6%nat; intros HR WF HM HG HFR HSW).
  destruct st0 as [z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5].
  set (st := mkRT z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5) in *.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  set (r := rg st cls) in *. set (nf := num_freed st cls) in *. set (n := nrefill cls) in *. set (S := csize cls).
  set (alloc := r_allocated r). set (mapped := r_mapped r) in *. set (fam := r_mapped_fa r).
  set (pop := nf <? n). set (um := pop && (mapped <? alloc + S * (n - nf))).
  set (Nv := if pop then (mapped + (if um then 262144 else 0) - alloc) / S else 0).
  set (fm := pop && (fam <? 4 * (nf + Nv))). set (nm := (4 * (nf + Nv) + 262143) / 262144 * 262144).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof HCE as HCEn. idtac. unfold AREFILL_STACK in LO2.
  (nelim (refill_cells st m cls HR WF Hc HC0) 14%nat; intros jr je js _ _ _ _ _ _ _ _ _ RIb _). fold r alloc mapped in RIb.
  assert (NAV : navail st cls = nf) by (unfold navail, avail_cptrs; fold r; rewrite HC0, app_nil_r; reflexivity).
  pose proof (nrefill_eq cls ltac:(lia)) as [_ NR]. fold n in NR.
  pose proof (wf_class_ok st WF cls Hcls) as WC.
  pose proof (wc_alloc_mapped st cls WC) as AM. pose proof (wc_fa_nonneg st cls WC) as FA0. pose proof (wc_fa_align st cls WC) as FAL. pose proof (wc_num_freed st cls WC) as NFF. pose proof (wc_residue st cls WC) as RES.
  fold r in AM, FA0, FAL, NFF, RES. fold alloc mapped in AM. fold fam in FA0, FAL, NFF. fold alloc mapped in RES. unfold num_freed in NFF. fold r nf in NFF. change (zlen (r_fa r)) with nf in NFF.
  pose proof (csize_pos cls ltac:(lia)) as CP. fold S in CP.
  assert (G8 : 0 <= nf) by (unfold nf, num_freed; apply zlen_nonneg).
  (* [comment removed for export] *)
  assert (FAM0 : fm = true -> fam = 0 /\ nm = 262144).
  { intros Efm. unfold fm in Efm. apply andb_true_iff in Efm as [Ep Ef]. apply Z.ltb_lt in Ef.
    assert (NVB : Nv <= 16385).
    { unfold Nv. rewrite Ep. apply Z.div_le_upper_bound; [lia|]. assert (32 * 16384 <= S * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). destruct um; lia. }
    unfold pop in Ep. apply Z.ltb_lt in Ep.
    assert (fam = 0) by (clear -Ef FAL FA0 NVB G8 Ep NR; Z.div_mod_to_equations; nia). split; [exact H|]. unfold nm. clear -NVB G8 Ep NR H Ef. Z.div_mod_to_equations. nia. }
  assert (HRR : (if um then LUMP else 0) + (if fm then LUMP else 0) <= R).
  { pose proof (prov_cls_le st cls WF Hc) as PC.
    assert (PU : um = true -> LUMP <= provU st cls).
    { intros Eum. unfold um in Eum. apply andb_true_iff in Eum as [Ep Eu]. unfold pop in Ep. apply Z.ltb_lt in Ep. apply Z.ltb_lt in Eu.
      unfold LUMP. apply (lumpU_ok st cls WF Hc HC0); [exact Ep| exact Eu]. }
    assert (PF : fm = true -> LUMP <= provF st cls) by (intros Efm; destruct (FAM0 Efm) as [FZ _]; unfold LUMP; apply (lumpF_ok st cls WF Hc); exact FZ).
    pose proof (prov_classes_nonneg st). assert (0 <= provU st cls /\ 0 <= provF st cls) by (unfold provU, provF; lia).
    destruct um; destruct fm; try specialize (PU eq_refl); try specialize (PF eq_refl); lia. }
  apply lscps_assume. intros NWX HOK HBINV.
  eapply (refill_walk ra sp gp tp x5 x6 x7 s0 s1 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mo G R st cls lo
            HR WF HM HG Hc HC0 TP MI ST ltac:(split; [exact HCE| unfold AREFILL_STACK; clear -LO2; lia]) pop um fm false _ jr je js RIb eq_refl eq_refl eq_refl HRR).
  - (* [comment removed for export] *)
    intros Ep Eu EX EM w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m' MI' MU' WM' ST' RIa' RI24' RIb' PCH' PCO'.
    apply lscps_done. unfold refill_post, rt_post_std.
    exists w5, w6, w7, (wz 0), w11, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m'.
    eexists (mkRT z1 z2 z3 (updz z4 cls (r_f z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls false)) true
                   z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5).
    assert (RIbF : rw_cells bsegs m' (rinfo st cls + 32) [C8 (Z_to_bv 64 (r_allocated r)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (r_mapped r + 0)); C8 (Z_to_bv 64 0); CB 4 jr;
                                                     C1 (Z_to_bv 8 (if r_exhausted r then 1 else 0)); CB 3 je; CB 56 js]).
    { rewrite Z.add_0_r. replace (r_exhausted r) with true by (symmetry; exact EX). exact RIb'. }
    assert (HUMF : false = true -> nf < nrefill cls /\ r_mapped r < r_allocated r + (nrefill cls - nf) * csize cls /\ r_mapped r + 262144 <= KFREEARRAY_OFF) by (intros E; discriminate E).
    assert (HR0 : (if false then LUMP else 0) <= R) by (unfold LUMP in *; destruct um; destruct fm; lia).
    set (stF := mkRT z1 z2 z3 (updz z4 cls (r_f z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls false)) true z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5).
    assert (XS : RTS stF m' mo (mkG G (R - 0))).
    { eapply (RTS_finf z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls false); (first [eassumption| exact I| idtac]).
      unfold CEIL; lia. }
    assert (XG : gmono (mkG G R) (mkG G (R - 0))) by (intros w Hw; exact Hw).
    assert (XB : budget_ok st (mkG G R) stF (mkG G (R - 0)) 0).
    { eapply (budget_finf z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls false); (first [eassumption| exact I| idtac]). all: try (unfold CEIL; lia). }
    rewrite Z.sub_0_r in XS, XG, XB.
    split; [reflexivity|]. split; [exact MI'|]. exists 0. split; [reflexivity|].
    split; [eapply (rel_finf z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls false); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [exact XS|].
    split; [exact ST'|].
    split; [eapply (cli_pres_finf z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls false); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply (rt_frame_finf' z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls false); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [exact XG| exact XB].
  - (* [comment removed for export] *)
    intros Ep Eu EX EM u5 u6 u7 u15 u16 u17 u18 u24 u25 u28 u29 u30 u31 m1 jR jG tj1 tj2 sa MI1 MU1 WM1 ST1 FRR1 FRG1 FRP1 RIa1 RI241 RIb1 TST1 SA1 PCH1 PCO1.
    (* [comment removed for export] *)
    (nelimp (cls_facts st WF cls Hc) 14%nat; intros CF1 CF2 CF3 CF4 CF5 CF6 CF7 CF8 CF9 CF10 CF11 CF12 CF13 CF14).
    pose proof (t_range st WF) as [TRo TRc]. (nelimp (oclr_lin _ _ TRo ltac:(lia)) 3%nat; intros TRa TRb TRi). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TRb, TRi.
    pose proof (loose_vs_prim st WF (st_t st) 4096 (wb_t_loose st (wf_base_ok st WF))) as TDJ.
    (nelimp (S_range st WF) 3%nat; intros SR1 SR2 SR3).
    assert (ERIS : ris st = st_spacebeg st + 137438953472) by reflexivity.
    assert (RCG : KHIGHMEM_BEG <= rinfo st cls /\ rinfo st cls + 128 <= alloc_ceiling /\ rinfo st cls mod 8 = 0
                  /\ st_pbase st <= rinfo st cls /\ rinfo st cls + 128 <= st_pbase st + PRIM_RES_SIZE).
    { rewrite CF14, ERIS. clear -CF1 CF2 CF3 CF4 CF5 SR1 SR2 SR3 ERIS Hc. rewrite ERIS in *. unfold KHIGHMEM_BEG, PRIM_RES_SIZE, KREGIONSIZE, CEIL, KSPACESIZE in *.
      repeat split; try lia; (Z.div_mod_to_equations; lia). }
    (nelim RCG 5%nat; intros RC1 RC2 RC8 RCP1 RCP2).
    assert (PCG : pcaddr st cls = st_t st + 208 + 80 * cls) by reflexivity.
    assert (RCT : st_t st + 4096 <= rinfo st cls \/ rinfo st cls + 128 <= st_t st) by (clear -TDJ RCP1 RCP2; destruct TDJ; [right| left]; lia).
    assert (E224 : bv_unsigned (wz (bv_unsigned sp + -32 + -128 + -64)) = bv_unsigned sp + -32 + -128 + -64) by (unfold wz; apply unsigned_lit; clear -RSP LO2 HCEn; lia).
    (* [comment removed for export] *)
    pose proof (WTOT_facts st cls lo (bv_unsigned sp) (Z.min 262144 (3758096384 - r_mapped (rg st cls))) WF Hc HCE ltac:(clear -LO2; lia)
                  ltac:(unfold KFREEARRAY_OFF in *; fold r mapped in EM |- *; lia) ltac:(unfold KFREEARRAY_OFF in *; fold r mapped in EM |- *; lia)) as [WT WTF].
    cbv zeta in WT, WTF.
    assert (WTz : Forall (pz_ok st cls) (WTOT lo (bv_unsigned sp) (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) (rbeg st cls + r_mapped (rg st cls))
                                              (Z.min 262144 (3758096384 - r_mapped (rg st cls))) (fabeg st cls) (num_freed st cls)))
      by (eapply Forall_impl; [| exact WT]; intros iv [H _]; exact H).
    (nelim (pz_others st WF cls Hc _ WTz m m1 MU1 WM1 HR) 3%nat; intros HL1 HCO1 _).
    (* [comment removed for export] *)
    assert (BSEP : forall d' : Z, (emb_d st <> 0 /\ d' = emb_d st) \/ (emb_d st = 0 /\ mmap_grant mo (wz d') EMB_CAP) -> 0 <= d' < 2^64 ->
               (d' + EMB_CAP <= st_pbase st \/ st_pbase st + PRIM_RES_SIZE <= d') /\ (d' + EMB_CAP <= st_t st \/ st_t st + 4096 <= d')).
    { intros d' [(NZ & ->)|(Z0 & GR)] D64.
      - pose proof (wb_emb_loose st (wf_base_ok st WF) NZ) as LS. split.
        + destruct (loose_vs_prim st WF _ _ LS); [right| left]; lia.
        + pose proof (wb_pwdj st (wf_base_ok st WF)) as PW.
          assert (I1 : In (emb_d st, emb_d st + EMB_CAP) (rt_ranges st)) by (unfold rt_ranges; do 2 right; rewrite !in_app_iff; left; apply in_map_iff; exists (emb_d st, EMB_CAP); split; [reflexivity| exact LS]).
          assert (I2 : In (st_t st, st_t st + 4096) (rt_ranges st)) by (unfold rt_ranges; do 2 right; rewrite !in_app_iff; left; apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))]).
          destruct (pwdj_In _ _ _ PW I1 I2) as [E|D]; [injection E as E1 E2; unfold EMB_CAP in E2; lia| cbn [fst snd] in D; lia].
      - pose proof (grant_fresh st mo (wz d') EMB_CAP HOK HM WF ltac:(unfold EMB_CAP; lia) GR) as FR. unfold wz in FR. rewrite unsigned_lit in FR by lia. split.
        + destruct (FR (st_pbase st, st_pbase st + PRIM_RES_SIZE) ltac:(left; reflexivity)) as [D|D]; cbn [fst snd] in D; [left| right]; lia.
        + destruct (FR (st_t st, st_t st + 4096) ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; left; apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))])) as [D|D];
            cbn [fst snd] in D; [left| right]; lia. }
    assert (SEP : emb_sep st mo (rinfo st cls)).
    { intros d' Hd'. destruct (Z_lt_ge_dec d' 0) as [NEG|NN]; [left; unfold EMB_CAP, KHIGHMEM_BEG in *; lia|].
      destruct (Z_lt_ge_dec d' (2^64)) as [LT|GE]; [| right; pose proof alloc_ceiling_range; lia].
      destruct (BSEP d' Hd' ltac:(lia)) as [[D|D] _]; [left| right]; lia. }
    assert (SP47 : bv_unsigned (wz (bv_unsigned sp + -32 + -128 + -64)) + 64 <= 2^47).
    { rewrite E224. destruct FRP1 as [[_ Hb] _]. pose proof (Mem.bytes_at_task bsegs m1 _ _ MI1 bsegs_task Hb ltac:(unfold pop_frame; cbn; discriminate)) as TS.
      unfold pop_frame in TS. cbn [cells_bytes cbytes length app] in TS. rewrite !length_app in TS. cbn [length] in TS. unfold TASK_SIZE in TS. rewrite !length_le8 in TS || idtac. lia. }
    pose proof (wb_emb_sz st (wf_base_ok st WF)) as ESZ. pose proof (nexh_bound_wf st WF) as NXB.
    pose proof oom_arm_proof as OOM. unfold oom_arm_sep_stmt in OOM.
    eapply (OOM (wz (bv_unsigned sp + -32 + -128 + -64)) gp tp) with (st := st) (Rc := rinfo st cls) (c := cls) (lo := lo);
      [exact HL1| exact HCO1| exact WF| exact MI1| rewrite E224; exact ST1| exact HCE| rewrite E224; unfold OOM_STACK; clear -LO2; lia| exact SP47
      | rewrite E224; exact FRP1| exact RIb1| exact RC1| exact RC2| exact Hc| lia| unfold EMB_MSG in *; lia| | exact SEP|].
    { (* [comment removed for export] *)
      intros Z0. pose proof (prov_emb_nonneg st) as PE. (nelimp (rt_prov_parts_nonneg st WF) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8). pose proof (prov_l24_nonneg st) as Q9.
      assert (PV : prov_emb st <= rt_prov st) by (unfold rt_prov; lia). unfold prov_emb in PV. rewrite Z0 in PV. cbn [Z.eqb] in PV.
      split; [lia|]. apply (FRONTR_placeable mo R EMB_CAP HOK HFR); unfold EMB_CAP, FR_NMAX; lia. }
    intros q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 m3 mo' R' d' sz' MI3 MU3 WM3 ST3 RIb3 EC3 HSZ3 STEP3 HL3.
    rewrite E224 in MU3, ST3.
    (* [comment removed for export] *)
    assert (D3 : d' <> 0 /\ ((emb_d st <> 0 /\ d' = emb_d st) \/ (emb_d st = 0 /\ mmap_grant mo (wz d') EMB_CAP))).
    { destruct STEP3 as [(NZ & E & _)|(Z0 & NZ & GR & _)]; [split; [rewrite E; exact NZ| left; split; assumption]| split; [exact NZ| right; split; assumption]]. }
    destruct D3 as [D3nz D3c].
    assert (D64 : 0 <= d' < 2^64).
    { pose proof (proj2 EC3 D3nz) as V. pose proof (SysStep.stk_lo_nonneg _ _ _ _ V) as V0. (nelim V 3%nat; intros _ V2 _). unfold EMB_CAP in *. lia. }
    destruct (BSEP d' D3c D64) as [BP BT].
    (nelimp (P_range st WF) 3%nat; intros PR1 _ _).
    assert (DHI : d' + EMB_CAP <= alloc_ceiling).
    { destruct D3c as [(NZ & ->)|(_ & GR)]; [exact (proj1 (proj2 (emb_block_range st WF NZ)))|]. (nelim GR 4%nat; intros _ _ GC _). unfold wz in GC. rewrite unsigned_lit in GC by lia. exact GC. }
    replace (d' =? 0) with false in MU3 by (symmetry; apply Z.eqb_neq; exact D3nz). cbn [app] in MU3.
    assert (DJ3 : forall a k, (bv_unsigned sp + -32 + -128 <= a /\ a + k <= 2^64) \/ (st_pbase st <= a /\ a + k <= rinfo st cls + 68) \/ (st_t st <= a /\ a + k <= st_t st + 4096) ->
               disjoint_from [(lo, bv_unsigned sp + -32 + -128 + -64 + 64); (rinfo st cls + 68, rinfo st cls + 69); (A_EMB, A_EMB + 56); (d', d' + EMB_CAP)] a k).
    { intros a k Ha. pose proof alloc_ceiling_range as ACR. unfold A_EMB, EMB_CAP, PRIM_RES_SIZE, KHIGHMEM_BEG in *. cbn [disjoint_from].
      clear -Ha ACR HCEn LO2 RSP RC1 RC2 RCP1 RCP2 RCT BP BT TRa TRb TRi TRc PR1 DHI. repeat split; lia. }
    eapply (rw_cells_transport bsegs _ m1 m3) in FRG1; [| exact MU3| exact WM3| apply DJ3; left; unfold gfa_frame; cbn; clear -RSP; lia].
    eapply (rw_cells_transport bsegs _ m1 m3) in FRR1; [| exact MU3| exact WM3| apply DJ3; left; unfold refill_frame; cbn; clear -RSP; lia].
    eapply (rw_cells_transport bsegs _ m1 m3) in RIa1; [| exact MU3| exact WM3| apply DJ3; right; left; cbn [cells_size Cells.csize Nat.add]; clear -RCP1; lia].
    eapply (rw_cells_transport bsegs _ m1 m3) in RI241; [| exact MU3| exact WM3| apply DJ3; right; left; cbn [cells_size Cells.csize Nat.add]; clear -RCP1; lia].
    assert (PCH3 : pch_at st cls m3 0).
    { intros c Hc'. eapply (rw_cells_transport bsegs _ m1 m3); [exact (PCH1 c Hc')| exact MU3| exact WM3|]. apply DJ3. right; right.
      change (pcaddr st c) with (st_t st + 208 + 80 * c). unfold KNUMCLASSES in Hc'. cbn. clear -Hc'. lia. }
    assert (PCO3 : pco_at st m3).
    { intros c i Hc' Hi. eapply (rw_cells_transport bsegs _ m1 m3); [exact (PCO1 c i Hc' Hi)| exact MU3| exact WM3|]. apply DJ3. right; right.
      change (pcaddr st c) with (st_t st + 208 + 80 * c). pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CL. pose proof (cmaxcount_le16 c) as CM.
      unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add]. clear -Hc' Hi CL CM. lia. }
    (* [comment removed for export] *)
    pose proof (PCH3 cls Hcls) as PCC3. rewrite Z.eqb_refl in PCC3. replace (cls =? 0) with false in PCC3 by (symmetry; apply Z.eqb_neq; clear -Hc; lia).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (unfold wz; apply unsigned_lit; clear -RSP LO2 HCEn; lia).
    apply lscps_step_evt.
    replace (wz (bv_unsigned (wz (bv_unsigned sp + -32 + -128 + -64)) + 64)) with (wz (bv_unsigned (wz (bv_unsigned sp + -32)) + -128)) by (rewrite E224, E32; f_equal; clear; lia).
    eapply evt_cut.
    { eapply (fail_tail sp gp tp) with (lo := lo) (Rc := rinfo st cls) (pc := pcaddr st cls) (n := nrefill cls) (nf := num_freed st cls) (cls := cls);
        [exact MI3| replace (bv_unsigned sp + -32 + -128) with (bv_unsigned sp + -32 + -128 + -64 + 64) by (clear; lia); exact ST3| exact HCE| clear -LO2; lia
        | exact FRG1| exact FRR1| exact RIa1| exact PCC3| exact RC1| exact RC2| exact RC8| | | | clear -NR; lia].
      - rewrite PCG. unfold AIMG_LO, AIMG_HI. clear -TRa TRi Hc. lia.
      - rewrite PCG. clear -TRc Hc. lia.
      - rewrite PCG. clear -RCT Hc. lia. }
    intros ms5 nelH_; (nelim nelH_ 22%nat; intros w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m5 -> MU5 WM5 MI5 ST5 RIa5 PCC5).
    (* [comment removed for export] *)
    assert (DJ5 : forall a k, (st_pbase st <= a /\ rinfo st cls + 8 <= a /\ a + k <= st_pbase st + PRIM_RES_SIZE) \/ (a + k <= AIMG_HI /\ AIMG_LO <= a)
                              \/ (st_t st <= a /\ a + k <= st_t st + 4096 /\ (a + k <= pcaddr st cls \/ pcaddr st cls + 4 <= a)) ->
               disjoint_from [(lo, bv_unsigned sp); (rinfo st cls, rinfo st cls + 8); (pcaddr st cls, pcaddr st cls + 4)] a k).
    { intros a k Ha. pose proof alloc_ceiling_range as ACR. rewrite PCG in *. unfold PRIM_RES_SIZE, KHIGHMEM_BEG, AIMG_HI, AIMG_LO in *. cbn [disjoint_from].
      clear -Ha ACR HCEn LO2 RSP RC1 RC2 RCP1 RCP2 RCT TRa TRb TRi TRc PR1 CF5 Hc TDJ. unfold CEIL, PRIM_RES_SIZE in CF5. repeat split; lia. }
    eapply (rw_cells_transport bsegs _ m3 m5) in RI241; [| exact MU5| exact WM5| apply DJ5; left; cbn [cells_size Cells.csize Nat.add]; clear -RCP1 RCP2; lia].
    eapply (rw_cells_transport bsegs _ m3 m5) in RIb3; [| exact MU5| exact WM5| apply DJ5; left].
    2:{ cbn [cells_size Cells.csize Nat.add]. clear -RCP1 RCP2. lia. }
    assert (PCH5 : pch_at st cls m5 0).
    { intros c Hc'. destruct (Z.eqb_spec c cls) as [->|NE].
      - replace (cls =? 0) with false by (symmetry; apply Z.eqb_neq; clear -Hc; lia). exact PCC5.
      - pose proof (PCH3 c Hc') as X. replace (c =? cls) with false in X by (symmetry; apply Z.eqb_neq; exact NE).
        eapply (rw_cells_transport bsegs _ m3 m5); [exact X| exact MU5| exact WM5|]. apply DJ5. right; right.
        change (pcaddr st c) with (st_t st + 208 + 80 * c). rewrite PCG. unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add]. clear -Hc' NE Hc. lia. }
    assert (PCO5 : pco_at st m5).
    { intros c i Hc' Hi. destruct (Z.eq_dec c cls) as [->|NE]; [exfalso; rewrite HC0 in Hi; unfold zlen in Hi; cbn [length Z.of_nat] in Hi; clear -Hi; lia|].
      eapply (rw_cells_transport bsegs _ m3 m5); [exact (PCO3 c i Hc' Hi)| exact MU5| exact WM5|]. apply DJ5. right; right.
      pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CL. pose proof (cmaxcount_le16 c) as CM.
      change (pcaddr st c) with (st_t st + 208 + 80 * c). rewrite PCG. unfold KNUMCLASSES in Hc'. cbn [cells_size Cells.csize Nat.add]. clear -Hc' NE Hc Hi CL CM. lia. }
    assert (BK : ablk d' (d' + EMB_CAP)).
    { destruct D3c as [(NZ & ->)|(_ & GR)]; [exact (proj1 (emb_block_range st WF NZ))|].
      pose proof (grant_ablk st mo (wz d') EMB_CAP HOK HM ltac:(unfold EMB_CAP; lia) GR) as X. unfold wz in X. rewrite unsigned_lit in X by lia. exact X. }
    assert (EC5 : emb_cells m5 d' sz').
    { apply (emb_cells_keep2 _ m3 m5 d' sz' EC3 MU5 WM5); [apply DJ5; right; left; unfold A_EMB, AIMG_HI, AIMG_LO; lia| intros _; exact (ablk_img _ _ BK)]. }
    (* [comment removed for export] *)
    set (W1 := WTOT lo (bv_unsigned sp) (acache st) (pcaddr st cls) (st_t st) (rinfo st cls) (rbeg st cls + r_mapped (rg st cls))
                    (Z.min 262144 (3758096384 - r_mapped (rg st cls))) (fabeg st cls) (num_freed st cls)) in *.
    set (W2 := [(A_EMB, A_EMB + 56); (d', d' + EMB_CAP)]).
    assert (IN_stk : In (lo, bv_unsigned sp) (W1 ++ W2)) by (apply in_or_app; left; left; reflexivity).
    assert (IN_pc : In (pcaddr st cls, pcaddr st cls + 80) (W1 ++ W2)) by (apply in_or_app; left; unfold W1, WTOT; apply in_or_app; right; right; left; reflexivity).
    assert (IN_rc : In (rinfo st cls, rinfo st cls + 128) (W1 ++ W2)) by (apply in_or_app; left; unfold W1, WTOT; apply in_or_app; right; right; right; right; left; reflexivity).
    assert (IN_emb : In (A_EMB, A_EMB + 56) (W1 ++ W2)) by (apply in_or_app; right; left; reflexivity).
    assert (IN_blk : In (d', d' + EMB_CAP) (W1 ++ W2)) by (apply in_or_app; right; right; left; reflexivity).
    assert (MUt : munch (W1 ++ W2) m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]|].
      { intros x Hx. clear -Hx. induction W1 as [|[l h] W IH]; [exact I|]. cbn in Hx |- *. destruct Hx as [H1 H2]. split; [exact H1| exact (IH H2)]. }
      eapply munch_trans; [eapply munch_weaken; [| exact MU3]| eapply munch_weaken; [| exact MU5]]; apply sub_fp_incl.
      - apply Forall_cons; [exists lo, (bv_unsigned sp); split; [exact IN_stk| cbn [fst snd]; clear; lia]|].
        apply Forall_cons; [exists (rinfo st cls), (rinfo st cls + 128); split; [exact IN_rc| cbn [fst snd]; clear; lia]|].
        apply Forall_cons; [exists A_EMB, (A_EMB + 56); split; [exact IN_emb| cbn [fst snd]; clear; lia]|].
        apply Forall_cons; [exists d', (d' + EMB_CAP); split; [exact IN_blk| cbn [fst snd]; clear; lia]| apply Forall_nil].
      - apply Forall_cons; [exists lo, (bv_unsigned sp); split; [exact IN_stk| cbn [fst snd]; clear; lia]|].
        apply Forall_cons; [exists (rinfo st cls), (rinfo st cls + 128); split; [exact IN_rc| cbn [fst snd]; clear; lia]|].
        apply Forall_cons; [exists (pcaddr st cls), (pcaddr st cls + 80); split; [exact IN_pc| cbn [fst snd]; clear; lia]| apply Forall_nil]. }
    pose proof (wmono_trans bsegs _ _ _ WM1 (wmono_trans bsegs _ _ _ WM3 WM5)) as WMt.
    (* [comment removed for export] *)
    assert (HXX : r_mapped (rg st cls) = KFREEARRAY_OFF /\ r_mapped (rg st cls) < r_allocated (rg st cls) + csize cls).
    { split; [exact EM|]. pose proof (wc_delta st cls WC ltac:(clear -Hc; lia)) as [DL|[DL1 DL2]]; [exact DL| exfalso].
      unfold um in Eu. apply andb_true_iff in Eu as [_ Eu]. apply Z.ltb_lt in Eu. pose proof (csize_le64k' cls Hc) as CL. (nelimp (slack_ok' cls Hc) 3%nat; intros SL _ _).
      fold r in DL1, DL2. fold alloc mapped in DL1, DL2. fold n S in SL. fold S in CL.
      assert (SQ : S * (n - nf) <= 262144).
      { assert (S * (n - nf) <= S * n) by (apply Z.mul_le_mono_nonneg_l; clear -CP NR G8; lia). clear -H CL SL CP NR. nia. }
      clear -Eu SQ DL1. lia. }
    assert (HD64' : emb_d st <> 0 -> d' = emb_d st) by (intros NZ; destruct STEP3 as [(_ & E & _)|(Z0 & _)]; [exact E| exfalso; exact (NZ Z0)]).
    destruct (fx_emb st cls d' sz' HD64') as [FXD FXS].
    assert (HBLK : (forall r0, In r0 (rt_ranges st) -> d' + EMB_CAP <= fst r0 \/ snd r0 <= d') \/ (emb_d st <> 0 /\ d' = emb_d st /\ d' + EMB_CAP = emb_d st + EMB_CAP)).
    { destruct D3c as [(NZ & E)|(_ & GR)]; [right; split; [exact NZ| split; [exact E| rewrite E; reflexivity]]| left].
      pose proof (grant_fresh st mo (wz d') EMB_CAP HOK HM WF ltac:(unfold EMB_CAP; lia) GR) as FR. unfold wz in FR. rewrite unsigned_lit in FR by lia. exact FR. }
    assert (HZ2 : forall a k, (a + k <= A_EMB \/ A_EMB + 56 <= a) -> a + k <= CEIL -> (a + k <= d' \/ d' + EMB_CAP <= a) -> disjoint_from W2 a k).
    { apply (ez_z_of W2 d' (d' + EMB_CAP)). apply Forall_cons; [apply ez_ok_cells; clear; lia|]. apply Forall_cons; [apply ez_ok_block; clear; lia| apply Forall_nil]. }
    assert (RINFO5 : exists jr0 je0 js0, rw_cells bsegs m5 (rinfo st cls) (rinfo_cells (st_fx st cls d' sz') cls jr0 je0 js0)).
    { exists jr, je, js. unfold rinfo_cells. rewrite (fx_num_freed st cls d' sz' WF Hc). (nelim (fx_proj st cls d' sz' WF Hc cls) 4%nat; intros P1 P2 P3 _).
      rewrite P1, P2, P3, (fx_exhausted st cls d' sz' WF Hc), Z.eqb_refl.
      apply (rinfo_join3 m5 (rinfo st cls)); [exact RIa5| exact RI241| exact RIb3| reflexivity| reflexivity]. }
    assert (EMB5 : R_emb (st_fx st cls d' sz') m5) by (unfold R_emb; rewrite FXD, FXS; exact EC5).
    assert (HBK : (emb_d st <> 0 /\ d' = emb_d st) \/ (ablk d' (d' + EMB_CAP) /\ forall r0, In r0 (rt_ranges st) -> d' + EMB_CAP <= fst r0 \/ snd r0 <= d')).
    { destruct D3c as [X|(_ & GR)]; [left; exact X| right; split; [exact BK|]].
      pose proof (grant_fresh st mo (wz d') EMB_CAP HOK HM WF ltac:(unfold EMB_CAP; lia) GR) as FR. unfold wz in FR. rewrite unsigned_lit in FR by lia. exact FR. }
    (nelim (fx_addr st cls d' sz') 4%nat; intros _ AI AB _). (nelim (fx_geom st cls d' sz') 3%nat; intros _ GT _).
    apply evt_done. apply lscps_done. unfold refill_post, rt_post_std.
    exists w5, w6, w7, (wz 0), w11, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m5, (st_fx st cls d' sz').
    split; [reflexivity|]. split; [exact MI5|]. exists 0. split; [reflexivity|].
    split; [exact (rel_fx st cls d' sz' WF Hc HC0)|].
    split.
    { apply RTS_intro.
      - exact (RTREP_fx st cls d' sz' WF Hc HC0 W1 W2 d' (d' + EMB_CAP) m m5 WTz BK HZ2 HBLK HR MUt WMt RINFO5 PCH5 PCO5 EMB5).
      - eapply RTWF_fx; eassumption.
      - eapply RTMODEL_fx; eassumption.
      - eapply GWIN_fx; eassumption.
      - eapply FRONTR_fx; eassumption.
      - eapply SWIN_fx; eassumption. }
    split; [exact ST5|].
    assert (HSPc : CEIL <= bv_unsigned sp) by (unfold CEIL; clear -HCEn LO2; lia).
    assert (HDf : d' <> 0 /\ emb_d (st_fx st cls d' sz') = d') by (split; [exact D3nz| exact FXD]).
    pose proof (WTF (st_fx st cls d' sz') (AB cls) (AI cls) GT) as WTF'.
    split; [eapply cli_pres_fx with (cls := cls) (d := d') (W1 := W1); first [exact WF| exact Hc| exact HSPc| exact WT| exact HBK| exact MUt| exact WMt| exact HDf| eassumption]|].
    split; [eapply rt_frame_fx with (cls := cls) (d := d') (W1 := W1); first [exact WF| exact Hc| exact HSPc| exact WT| exact WTF'| exact HBK| exact MUt| exact WMt| exact HDf| eassumption]|].
    split; [eapply gmono_fx| eapply budget_fx; eassumption].
  - exact I.
  - exact I.
  - (* [comment removed for export] *)
    intros NEX w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m' js' fa MI' MU' WM' ST' RIa' RI24' RIb' VFA' FILL' VU' VF' FL FN CHU' PCH' PCO'.
    apply lscps_done. unfold refill_post, rt_post_std.
    exists w5, w6, w7, (wz 1), w11, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m'.
    eexists (mkRT z1 z2 z3 (updz z4 cls (r_new z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls n Nv nm um fm pop)) true
                   (updz z6 cls (skipn (Z.to_nat (nf + Nv - n)) (r_fa r ++ newc cls (ncarved st cls) Nv))) z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5).
    pose proof (csize_le64k' cls Hc) as CL. fold S in CL. (nelimp (slack_ok' cls Hc) 3%nat; intros SL _ _). fold n S in SL.
    assert (SQ : S * (n - nf) <= 262144).
    { assert (S * (n - nf) <= S * n) by (apply Z.mul_le_mono_nonneg_l; clear -CP NR G8; lia). clear -H CL SL CP NR. nia. }
    assert (NvQ : pop = true -> n - nf <= Nv).
    { intros Ep. unfold Nv. rewrite Ep. apply Z.div_le_lower_bound; [clear -CP; lia|]. unfold um. rewrite Ep. cbn [andb].
      destruct (Z.ltb_spec0 mapped (alloc + S * (n - nf))) as [LTm|GEm]; [clear -SQ AM LTm| clear -SQ AM GEm]; lia. }
    assert (HNv : 0 <= Nv /\ n <= nf + Nv).
    { unfold Nv in *. destruct pop eqn:Ep.
      - split; [apply Z.div_pos; [destruct um; lia| lia]| specialize (NvQ eq_refl); rewrite Ep in NvQ || idtac; lia].
      - unfold pop in Ep. apply Z.ltb_ge in Ep. lia. }
    assert (HPOP : pop = true -> nf < n /\ Nv = (r_mapped r + (if um then 262144 else 0) - r_allocated r) / S
        /\ um = (r_mapped r <? r_allocated r + (n - nf) * S) /\ (um = true -> r_mapped r + 262144 <= KFREEARRAY_OFF)
        /\ fm = (r_mapped_fa r <? 4 * (nf + Nv)) /\ nm = (4 * (nf + Nv) + 262143) / 262144 * 262144).
    { intros Ep. split; [unfold pop in Ep; apply Z.ltb_lt in Ep; exact Ep|]. split; [unfold Nv; rewrite Ep; reflexivity|].
      split; [unfold um; rewrite Ep; cbn [andb]; fold alloc mapped; rewrite (Z.mul_comm (n - nf) S); reflexivity|].
      split; [exact NEX|]. split; [unfold fm; rewrite Ep; reflexivity| reflexivity]. }
    assert (HHAVE : pop = false -> Nv = 0 /\ um = false /\ fm = false) by (intros Ep; unfold fm, Nv, um; rewrite Ep; cbn [andb]; repeat split; reflexivity).
    assert (NVB : Nv <= 16385).
    { unfold Nv. destruct pop; [| lia]. apply Z.div_le_upper_bound; [lia|]. assert (32 * 16384 <= S * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). destruct um; lia. }
    pose proof (conj FL FN) as Hfa. clear FL FN RIb.
    split; [reflexivity|]. split; [exact MI'|]. exists 1. split; [reflexivity|].
    split; [eapply rel_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply RTS_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [exact ST'|].
    split; [eapply (cli_pres_fins z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls) with (um := um); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply rt_frame_fins'; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply gmono_fins with (lo := lo) (SP := bv_unsigned sp); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    eapply budget_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia.
Qed.

End CeilWrap.
