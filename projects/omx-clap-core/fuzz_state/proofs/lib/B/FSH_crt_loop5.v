(* check_round_trip (fs.asan-ubsan 0x81b9c), build B, SEGMENT 5's LOOP: the inlined expected_text of fs.c:107-121
   (call site fs.c:288), image B = lib/B/YB1v.v tfibsegs (the pinned fuzz_state.asan-ubsan, sha256
   5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204), machine code 0x81e10 .. 0x81fd4 (MEASURED, capstone
   over the pinned image, (internal path)), head 0x81e18, back edge `bltu a3, s4, -0x1c4`
   at 0x81fd4 to 0x81e10 (`bltu a4, a3` UBSan test, `mv t6, s6`), |bs| / 3 trips, exit 0x81fd8 `j` 0x82094. Walked with
   the TOKEN engine (FSW_K fsw_aj_run_to_tokU over Reusable/YCbn.v): a `lb` of a shadow byte becomes a token atom and the
   following `bnez` is resolved by the engine's slow-block pattern, so the PARTIAL-GRANULE slow paths 0x8203c .. 0x82088
   are taken by the engine itself and the __asan_report_* arms are never reached.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 5e9786b4b6c)
   Port source: a working branch 5e9786b4b6c proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_loop5.v (4597 lines,
   crt5_seg5), itself PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/
   check_round_trip_loops.v (et_pre :349, crt_expected_text :1008, et_iter / et_loop); the function's rule-24 line, with
   the full reuse search and the checker's CONFIRM (a Theorem Labs lane, 04:3xZ), is lines 6-21 of the lane head
   (internal path). Same Definition / Lemma names and statement shapes as the A
   file, over image B (S0 a9edd281227's lib/B kit, the B interface lib/B/FSH_crt_base.v v33 / FSH_crt_site.v); every pc,
   register and atom RE-MEASURED on B and mapped from A by instruction meaning (crt.A2B.tsv). The pure arithmetic is
   REUSED by Require from lib/Prog/check_round_trip_loops.v, as on A. A new file: no licence lines.

   A name -> A pc -> B pc (names keep their A form, content is B's):
     crt5_ssH / crt5_head_at / crt5_toHead / crt5_phH        0x81d0c -> 0x81e18 (head)
     crt5_ssB / crt5_toB / crt5_phB                          0x81d7c -> 0x81e8c (bytes read, first class open)
     crt5_ssC / crt5_toC / crt5_phC_in / crt5_phC_out        0x81dd8 -> 0x81ef4 (first character stored)
     crt5_ssD1 / crt5_toD1 / crt5_phD_in / crt5_phD_out      0x81e38 -> 0x81f60 (second character stored)
     crt5_ssE1 / crt5_toE1 / crt5_phE_more / crt5_phE_last   0x81e68 -> 0x81f98 (third character stored)
     crt5_ssOut / crt5_exit_at / crt5_toOut                  0x81f58 -> 0x82098 (after `addi a0, t6, 4`; A's ssOut is
                                                             after A's `addi a0, t4, 4` 0x81f54)
     crt5_seg5                                               crt_ss_ret 0x81f58 crt_cs1e -> crt_ss_ret 0x820a4 crt_cs1e
                                                             (exit), crt_ss_ret 0x81d0c crt_cs1e -> crt_ss_ret 0x81e18
                                                             crt_cs1L (entry; lib/B/FSH_crt_base.v:153-166)

   What differs from A, carried into the proofs:
   - the walk's atoms are A's + 1 (B's crt_E pins 32 .. 50, atom 50 = En; A: 32 .. 49), and atom 82 holds a4 = ~bd, the
     bound of B's UBSan overflow tests 0x81e10 / 0x81e3c / 0x81e68 (A has none); a7 = -1 is the literal of the pointer-
     overflow tests 0x81ecc / 0x81f30 / 0x81f74 / 0x81fac;
   - B's registers (crt5_regsH .. crt5_regsOut, crt5_mregs .. crt5_mregsO): a3 = i, s3 = t6 = q, s6 = the store cursor,
     a5 = bd + 1, a4 = ~bd, s10 = SF (A: a0 = a2 = t4 = q, a4 = bd + 1, s3 = SF); the carried registers are ra a0 a1 a2
     s6 s8 s9 s7 s11 t3 t5 at 65 .. 75 (A: ra a1 s7 s10 s6 s8 s9 s11 t4 t5 t6 at 64 .. 74); crt5_EA pins ~bd at 82 where
     A held the passive s6 = En (B keeps En in slot 0x28);
   - at D1 / E1 the store cursor s6 is q + 1 / q + 2 (B 0x81f2c `addi s6, t6, 1` ..; A stores through t4 with immediate
     offsets), so those two re-keys keep atom 54 (crt5_PQ / crt5_rekeyQ);
   - the exit: the loop's trip ends at 0x82098, and crt5_seg5 runs the three slot reloads 0x82098 `ld s3, 0x38(s1)`,
     0x8209c `ld s6, 0x10(s1)`, 0x820a0 `ld s11, 0x28(s1)` from the boundary state crt_ss_ret 0x82098 crt_cs1L crt_csF to
     0x820a4 and re-enters crt_ss_ret 0x820a4 crt_cs1e crt_csF with lib/B/FSH_crt_segB0.v's crtB0_reenter (A: none). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL02 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0l YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat FSW_K FSW_crt_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_crt_base FSH_crt_site.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require check_round_trip_loops.
(* crtB0_reenter (the boundary at the stop pc of a run, rebuilt from the engine's state), reached qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_crt_segB0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module CRTL := check_round_trip_loops.

(* ================= the pure step of the encoding ================= *)
Lemma crt5_firstn_add : forall {A} n m (l : list A), firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
intros A n. induction n as [|n IH]; intros m l; [reflexivity|].
destruct l as [|x l]; simpl; [rewrite firstn_nil; reflexivity | f_equal; apply IH].
Qed.
Lemma crt5_nth_big : forall (l : list Z) n, (length l <= n)%nat -> nth n l 0 = 0.
Proof.
induction l as [|x l IH]; intros [|n] H; cbn [nth length] in *; try reflexivity; try lia.
apply IH. lia.
Qed.
Lemma crt5_nth_skipn : forall (l : list Z) n j, nth j (skipn n l) 0 = nth (n + j) l 0.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l j; [reflexivity|].
destruct l as [|x l]; cbn [skipn nth]; [destruct j; reflexivity | apply IH].
Qed.

(* the four characters iteration i writes: the released b64_enc of the (up to) three bytes at i *)
Definition crt5_quad (bs : list Z) (l i : Z) : list Z :=
  [b64c (nth (Z.to_nat i) bs 0 / 4);
   b64c (nth (Z.to_nat i) bs 0 mod 4 * 16 + nth (Z.to_nat (i + 1)) bs 0 / 16);
   (if i + 1 <? l then b64c (nth (Z.to_nat (i + 1)) bs 0 mod 16 * 4 + nth (Z.to_nat (i + 2)) bs 0 / 64) else 61);
   (if i + 2 <? l then b64c (nth (Z.to_nat (i + 2)) bs 0 mod 64) else 61)].

Lemma crt5_quad_step : forall (bs : list Z) (l i : Z),
  Z.of_nat (length bs) = l -> 0 <= i < l -> i mod 3 = 0 ->
  b64_enc (firstn (Z.to_nat (i + 3)) bs) = b64_enc (firstn (Z.to_nat i) bs) ++ crt5_quad bs l i.
Proof.
intros bs l i HL Hi Hm.
assert (E3 : Z.to_nat (i + 3) = (Z.to_nat i + 3)%nat) by lia.
rewrite E3, crt5_firstn_add.
rewrite (CRTL.b64_enc_app3 (Z.to_nat (i / 3))) by (rewrite firstn_length_le by lia; lia).
f_equal.
assert (HS : Z.of_nat (length (skipn (Z.to_nat i) bs)) = l - i) by (rewrite length_skipn; lia).
unfold crt5_quad.
assert (N0 : nth 0 (skipn (Z.to_nat i) bs) 0 = nth (Z.to_nat i) bs 0)
  by (rewrite crt5_nth_skipn; f_equal; lia).
assert (N1 : nth 1 (skipn (Z.to_nat i) bs) 0 = nth (Z.to_nat (i + 1)) bs 0)
  by (rewrite crt5_nth_skipn; f_equal; lia).
assert (N2 : nth 2 (skipn (Z.to_nat i) bs) 0 = nth (Z.to_nat (i + 2)) bs 0)
  by (rewrite crt5_nth_skipn; f_equal; lia).
destruct (Z_lt_ge_dec (i + 2) l) as [H2 | H2].
- (* three bytes *)
  destruct (skipn (Z.to_nat i) bs) as [|x0 [|x1 [|x2 r]]] eqn:ES; cbn [length] in HS; try lia.
  cbn [firstn b64_enc]. cbn [nth] in N0, N1, N2. rewrite <- N0, <- N1, <- N2.
  replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
- destruct (Z_lt_ge_dec (i + 1) l) as [H1 | H1].
  + (* two bytes *)
    assert (HS2 : length (skipn (Z.to_nat i) bs) = 2%nat) by lia.
    destruct (skipn (Z.to_nat i) bs) as [|x0 [|x1 [|x2 r]]] eqn:ES; cbn [length] in HS2; try lia.
    cbn [firstn b64_enc]. cbn [nth] in N0, N1. rewrite <- N0, <- N1.
    replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (crt5_nth_big bs (Z.to_nat (i + 2))) by lia. rewrite Zdiv_0_l, Z.add_0_r. reflexivity.
  + (* one byte *)
    assert (HS1 : length (skipn (Z.to_nat i) bs) = 1%nat) by lia.
    destruct (skipn (Z.to_nat i) bs) as [|x0 [|x1 r]] eqn:ES; cbn [length] in HS1; try lia.
    cbn [firstn b64_enc]. cbn [nth] in N0. rewrite <- N0.
    replace (i + 1 <? l) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (crt5_nth_big bs (Z.to_nat (i + 1))) by lia. rewrite Zdiv_0_l, Z.add_0_r. reflexivity.
Qed.

Lemma crt5_quad_enc : forall (bs : list Z) (l i : Z),
  Z.of_nat (length bs) = l -> 0 <= i < l -> i mod 3 = 0 ->
  b64_enc (skipn (Z.to_nat i) bs) = crt5_quad bs l i ++ b64_enc (skipn (Z.to_nat i + 3) bs).
Proof.
intros bs l i HL Hi Hm.
assert (HS : Z.of_nat (length (skipn (Z.to_nat i) bs)) = l - i) by (rewrite length_skipn; lia).
assert (HSK : skipn (Z.to_nat i + 3) bs = skipn 3 (skipn (Z.to_nat i) bs))
  by (rewrite skipn_skipn; f_equal; lia).
assert (N0 : nth 0 (skipn (Z.to_nat i) bs) 0 = nth (Z.to_nat i) bs 0)
  by (rewrite crt5_nth_skipn; f_equal; lia).
assert (N1 : nth 1 (skipn (Z.to_nat i) bs) 0 = nth (Z.to_nat (i + 1)) bs 0)
  by (rewrite crt5_nth_skipn; f_equal; lia).
assert (N2 : nth 2 (skipn (Z.to_nat i) bs) 0 = nth (Z.to_nat (i + 2)) bs 0)
  by (rewrite crt5_nth_skipn; f_equal; lia).
unfold crt5_quad. rewrite HSK.
destruct (skipn (Z.to_nat i) bs) as [|x0 [|x1 [|x2 r]]] eqn:ES; cbn [length] in HS;
  cbn [nth] in N0, N1, N2.
- lia.
- rewrite <- N0. cbn [skipn b64_enc].
  replace (i + 1 <? l) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (crt5_nth_big bs (Z.to_nat (i + 1))) by lia. rewrite Zdiv_0_l, Z.add_0_r. reflexivity.
- rewrite <- N0, <- N1. cbn [skipn b64_enc].
  replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (crt5_nth_big bs (Z.to_nat (i + 2))) by lia. rewrite Zdiv_0_l, Z.add_0_r. reflexivity.
- rewrite <- N0, <- N1, <- N2. cbn [skipn b64_enc].
  replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.
Lemma crt5_enc_split : forall (bs : list Z) (l i : Z),
  Z.of_nat (length bs) = l -> 0 <= i <= l -> i mod 3 = 0 ->
  b64_enc bs = b64_enc (firstn (Z.to_nat i) bs) ++ b64_enc (skipn (Z.to_nat i) bs).
Proof.
intros bs l i HL Hi Hm. rewrite <- (firstn_skipn (Z.to_nat i) bs) at 1.
rewrite (CRTL.b64_enc_app3 (Z.to_nat (i / 3))) by (rewrite firstn_length_le by lia; lia).
reflexivity.
Qed.
Lemma crt5_pre_len : forall (bs : list Z) (l i : Z),
  Z.of_nat (length bs) = l -> 0 <= i <= l -> i mod 3 = 0 ->
  Z.of_nat (length (b64_enc (firstn (Z.to_nat i) bs))) = i / 3 * 4.
Proof.
intros bs l i HL Hi Hm. rewrite CRTL.enc_len_Z, firstn_length_le by lia.
rewrite Z2Nat.id by lia. Z.div_mod_to_equations. lia.
Qed.
Lemma crt5_pre_nth : forall (bs : list Z) (l i : Z) (j : nat),
  Z.of_nat (length bs) = l -> 0 <= i <= l -> i mod 3 = 0 -> (Z.of_nat j < i / 3 * 4) ->
  nth j (b64_enc (firstn (Z.to_nat i) bs)) 0 = nth j (b64_enc bs) 0.
Proof.
intros bs l i j HL Hi Hm Hj.
rewrite <- (firstn_skipn (Z.to_nat i) bs) at 2.
rewrite (CRTL.b64_enc_app3 (Z.to_nat (i / 3))) by (rewrite firstn_length_le by lia; lia).
rewrite app_nth1; [reflexivity|].
pose proof (crt5_pre_len bs l i HL Hi Hm) as HPL. lia.
Qed.

Lemma crt5_quad_nth : forall (bs : list Z) (l i : Z) (j : nat),
  Z.of_nat (length bs) = l -> 0 <= i < l -> i mod 3 = 0 -> (j < 4)%nat ->
  nth (Z.to_nat (i / 3 * 4) + j) (b64_enc bs) 0 = nth j (crt5_quad bs l i) 0.
Proof.
intros bs l i j HL Hi Hm Hj.
rewrite (crt5_enc_split bs l i HL ltac:(lia) Hm).
rewrite app_nth2 by (pose proof (crt5_pre_len bs l i HL ltac:(lia) Hm); lia).
rewrite (crt5_quad_enc bs l i HL Hi Hm).
rewrite app_nth1 by (pose proof (crt5_pre_len bs l i HL ltac:(lia) Hm); unfold crt5_quad; cbn [length]; lia).
f_equal. pose proof (crt5_pre_len bs l i HL ltac:(lia) Hm) as HP. lia.
Qed.
Lemma crt5_quad_len : forall (bs : list Z) (l i : Z), length (crt5_quad bs l i) = 4%nat.
Proof. intros. unfold crt5_quad. reflexivity. Qed.


(* ================= U of the shapes the loop computes ================= *)
Lemma crt5_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply zcanon_id. unfold M64. exact Hz. Qed.
Lemma crt5_U_off : forall E n x c, ew E n = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  U E (SOff n c) = x + c.
Proof.
intros E n x c Hn Hx Hc. rewrite U_SOff, Hn, unsigned_lit_small by exact Hx.
apply zcanon_id. unfold M64. exact Hc.
Qed.
Lemma crt5_U_srl : forall E v k, 0 <= k < 64 -> U E (SAlu ALU_SRL v (SLit k)) = Z.shiftr (U E v) k.
Proof.
intros E v k Hk. rewrite U_SAlu. cbn [zalu_raw].
rewrite (crt5_U_lit E k ltac:(lia)).
rewrite (CRTL.vD k ltac:(lia)), (Z.mod_small k 64) by lia.
pose proof (U_range E v) as Hv. unfold M64 in Hv.
rewrite Z.shiftr_div_pow2 by lia. apply zcanon_id. unfold M64.
assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
assert (H1 : 1 <= 2 ^ k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ (U E v)); [apply Z.div_le_upper_bound; [lia | nia] | lia].
Qed.
Lemma crt5_U_sll : forall E v k, 0 <= k < 64 -> U E (SAlu ALU_SLL v (SLit k)) = Z.shiftl (U E v) k mod 2 ^ 64.
Proof.
intros E v k Hk. rewrite U_SAlu. cbn [zalu_raw].
rewrite (crt5_U_lit E k ltac:(lia)).
rewrite (CRTL.vD k ltac:(lia)), (Z.mod_small k 64) by lia. reflexivity.
Qed.
Lemma crt5_U_or : forall E a b, 0 <= Z.lor (U E a) (U E b) < 2 ^ 64 ->
  U E (SAlu ALU_OR a b) = Z.lor (U E a) (U E b).
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. exact H. Qed.
Lemma crt5_U_and : forall E a b, 0 <= Z.land (U E a) (U E b) < 2 ^ 64 ->
  U E (SAlu ALU_AND a b) = Z.land (U E a) (U E b).
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. exact H. Qed.

(* the five shapes: c0 >> 2, (c0 mod 4) * 16 | c1 >> 4, (c1 mod 16) * 4, that | c2 >> 6, c2 mod 64 *)
Lemma crt5_sh2 : forall E n x, ew E n = w64 x -> 0 <= x < 256 ->
  U E (SAlu ALU_SRL (SOff n 0) (SLit 2)) = x / 4.
Proof.
intros E n x Hn Hx. rewrite (crt5_U_srl E _ 2 ltac:(lia)).
rewrite (crt5_U_off E n x 0 Hn ltac:(lia) ltac:(lia)), Z.add_0_r.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma crt5_sh62 : forall E n x, ew E n = w64 x -> 0 <= x < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 62)) (SLit 58)) = x mod 4 * 16.
Proof.
intros E n x Hn Hx. rewrite (crt5_U_srl E _ 58 ltac:(lia)), (crt5_U_sll E _ 62 ltac:(lia)).
rewrite (crt5_U_off E n x 0 Hn ltac:(lia) ltac:(lia)), Z.add_0_r.
change (2 ^ 64) with 18446744073709551616. apply CRTL.sh62. exact Hx.
Qed.
Lemma crt5_sh60 : forall E n x, ew E n = w64 x -> 0 <= x < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 60)) (SLit 58)) = x mod 16 * 4.
Proof.
intros E n x Hn Hx. rewrite (crt5_U_srl E _ 58 ltac:(lia)), (crt5_U_sll E _ 60 ltac:(lia)).
rewrite (crt5_U_off E n x 0 Hn ltac:(lia) ltac:(lia)), Z.add_0_r.
change (2 ^ 64) with 18446744073709551616. apply CRTL.sh60. exact Hx.
Qed.
Lemma crt5_or1 : forall E n m x y, ew E n = w64 x -> ew E m = w64 y -> 0 <= x < 256 -> 0 <= y < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SRL (SOff m 0) (SLit 4)) (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 62)) (SLit 58)))
  = x mod 4 * 16 + y / 16.
Proof.
intros E n m x y Hn Hm Hx Hy.
assert (HA : U E (SAlu ALU_SRL (SOff m 0) (SLit 4)) = y / 16).
{ rewrite (crt5_U_srl E _ 4 ltac:(lia)), (crt5_U_off E m y 0 Hm ltac:(lia) ltac:(lia)), Z.add_0_r.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
assert (HB : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 62)) (SLit 58)) = x mod 4 * 16)
  by (apply crt5_sh62; assumption).
rewrite crt5_U_or by (rewrite HA, HB; rewrite (CRTL.lor_p (y / 16) (x mod 4) 4 16)
  by (try reflexivity; Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia).
rewrite HA, HB. rewrite (CRTL.lor_p (y / 16) (x mod 4) 4 16)
  by (try reflexivity; Z.div_mod_to_equations; lia). lia.
Qed.
Lemma crt5_or2 : forall E m p y z, ew E m = w64 y -> ew E p = w64 z -> 0 <= y < 256 -> 0 <= z < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SRL (SOff p 0) (SLit 6)) (SAlu ALU_SRL (SAlu ALU_SLL (SOff m 0) (SLit 60)) (SLit 58)))
  = y mod 16 * 4 + z / 64.
Proof.
intros E m p y z Hm Hp Hy Hz.
assert (HA : U E (SAlu ALU_SRL (SOff p 0) (SLit 6)) = z / 64).
{ rewrite (crt5_U_srl E _ 6 ltac:(lia)), (crt5_U_off E p z 0 Hp ltac:(lia) ltac:(lia)), Z.add_0_r.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
assert (HB : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff m 0) (SLit 60)) (SLit 58)) = y mod 16 * 4)
  by (apply crt5_sh60; assumption).
rewrite crt5_U_or by (rewrite HA, HB; rewrite (CRTL.lor_p (z / 64) (y mod 16) 2 4)
  by (try reflexivity; Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia).
rewrite HA, HB. rewrite (CRTL.lor_p (z / 64) (y mod 16) 2 4)
  by (try reflexivity; Z.div_mod_to_equations; lia). lia.
Qed.
Lemma crt5_and63 : forall E p z, ew E p = w64 z -> 0 <= z < 256 ->
  U E (SAlu ALU_AND (SOff p 0) (SLit 63)) = z mod 64.
Proof.
intros E p z Hp Hz.
assert (HA : U E (SOff p 0) = z) by (rewrite (crt5_U_off E p z 0 Hp ltac:(lia) ltac:(lia)); lia).
rewrite crt5_U_and; rewrite HA, (crt5_U_lit E 63 ltac:(lia)), (CRTL.vD z ltac:(lia)); [reflexivity | lia].
Qed.

(* ================= the symbolic states of the walk =================
   atoms (B; A's + 1): 51 l, 52 bd, 53 i, 54 q = want + 4 * (i / 3), 55 bd + i, 56 57 58 the three body bytes,
   59 the current character's value, 60 that value rounded down to a multiple of 4 (0x81f54's t5),
   65 ra, 66 a0, 67 a1, 68 a2, 69 s6, 70 s8, 71 s9, 72 s7, 73 s11, 74 t3, 75 t5, 76 the shadow base,
   77 bd + 1 (a5), 78 i + 2 (a2), 79 i + 1 (s11), 80 / 81 the exit's q + 4 / a3, 82 ~bd (a4). Every atom below 51 is
   the caller's (B's crt_E pins 32 .. 50) and the walk never touches it (crt5_P), so the boundary env survives the
   loop. A register of a re-key target may not carry a non-zero offset on a re-keyed atom (YL09 reg_reabs_ok), which
   is why bd + 1, i + 1 and i + 2 have atoms of their own, and why the re-keys into D1 / E1 keep atom 54 (s6 = q + 1 /
   q + 2 there, crt5_PQ); the ALIAS of 0x81e2c's `add s7, a5, a3` is what keeps the body loads resolvable (the
   engine's address normalisation, YP0e alias_lin_lookup). *)
(* YCbq.v asan_consts: 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000; the states need a literal bound *)
Definition CRT5_CEIL : Z := 140737479966720.
(* B's crt_E ends at atom 50 (En, crt_extra's nineteenth), so the walk's own atoms start at 51 (A: 50); every atom
   number of the A walk is A's + 1, plus atom 82 for a4 = ~bd *)
Definition crt5_P (n : nat) : bool := Nat.ltb n 51.
Definition crt5_Bx : sv := SOff 76 0.
Definition crt5_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the destination window of the trip, narrowed after each character so that what is written stays put *)
Definition crt5_want (lo : Z) : YP09.region := YP09.mkRegion (Some 54%nat) lo 4 lo 4 [].
Definition crt5_SHw (lo : Z) : list shent := [mkSHE 54 lo 4].
Definition crt5_body (nb : Z) : YP09.region :=
  YP09.mkRegion (Some 55%nat) 0 nb 0 0
    (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (56 + j) 0))) (seq 0 (Z.to_nat nb))).
Definition crt5_SHH (nb : Z) : list shent := [mkSHE 55 0 nb; mkSHE 54 0 4].
(* B: a4 = ~bd (atom 82) is the bound of the UBSan overflow tests 0x81e10 `bltu a4, a3`, 0x81e3c `bgeu a3, a4`,
   0x81e68 `bltu a4, a2`; its range lets the engine decide them *)
Definition crt5_base : list (nat * afact) :=
  [(76%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (51%nat, mkAF 1 3145728 0); (52%nat, mkAF 4096 CRT5_CEIL 0);
   (53%nat, mkAF 0 3145728 0); (54%nat, mkAF 4096 CRT5_CEIL 0);
   (82%nat, mkAF (2 ^ 64 - 1 - CRT5_CEIL) (2 ^ 64 - 1 - 4096) 0)].
Definition crt5_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 52 0) (SOff 53 0), SOff 55 0);
   (SAlu ALU_ADD (SOff 77 0) (SOff 53 0), SOff 55 1)].
Definition crt5_eq62 : list acond := [mkAC BC_EQ (SOff 59 0) (SLit 62)].
Definition crt5_h1 (b : bool) : acond :=
  if b then mkAC BC_LTU (SOff 79 0) (SOff 51 0) else mkAC BC_GEU (SOff 79 0) (SOff 51 0).
Definition crt5_h2 (b : bool) : acond :=
  if b then mkAC BC_LTU (SOff 78 0) (SOff 51 0) else mkAC BC_GEU (SOff 78 0) (SOff 51 0).
Definition crt5_more (b : bool) : acond :=
  if b then mkAC BC_LTU (SOff 53 3) (SOff 51 0) else mkAC BC_GEU (SOff 53 3) (SOff 51 0).

(* B's registers (MEASURED, crt.B.s 0x81e10 .. 0x81fd4): a3 = i, s3 = the shadow-test cursor q, t6 = the store base q
   (0x81e14 `mv t6, s6`), s6 = the store cursor (c0 at 0x81e30, then q + 1 .. q + 3), a5 = bd + 1, a4 = ~bd, a7 = -1,
   s4 = l, s5 = bd, s2 = SHADOW_OFF, s10 = SF; the alphabet constants a6 = 103, t0 = 25, t1 = 51, t2 = 61, t4 = 207
   (A: a5 a6 a7 t0 t2; A's t1 = 62 and t3 = 247 are immediates of B's body, 0x81eb8 / 0x81ea8).
   The registers a state does not need are carried at fixed atoms: ra 65, a0 66, a1 67, a2 68, s6 69, s8 70, s9 71,
   s7 72, s11 73, t3 74, t5 75 (s8 / s9 are passive: no B loop instruction writes them). *)
(* ---- the head, 0x81e18 ---- *)
Definition crt5_regsH : list sv :=
  [SLit 0; SOff 65 0; SOff 2 0; SOff 3 0; SOff 4 0;
   SLit 25; SLit 51; SLit 61; SOff 8 0; SOff 9 0;
   SOff 66 0; SOff 67 0; SOff 68 0; SOff 53 0; SOff 82 0;
   SOff 77 0; SLit 103; SLit 18446744073709551615;
   SOff 76 0; SOff 54 0; SOff 51 0; SOff 52 0; SOff 69 0;
   SOff 72 0; SOff 70 0; SOff 71 0; SOff 26 0; SOff 73 0;
   SOff 74 0; SLit 207; SOff 75 0; SOff 54 0].
Definition crt5_atomsH : list (nat * afact) :=
  crt5_base ++ [(55%nat, mkAF 4096 CRT5_CEIL 0); (77%nat, mkAF 4096 CRT5_CEIL 0);
                (56%nat, mkAF 0 255 0); (57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0)].
Definition crt5_condsH (nb : Z) : list acond :=
  if nb =? 3 then [mkAC BC_LTU (SOff 53 1) (SOff 51 0); mkAC BC_LTU (SOff 53 2) (SOff 51 0)]
  else if nb =? 2 then [mkAC BC_LTU (SOff 53 1) (SOff 51 0); mkAC BC_GEU (SOff 53 2) (SOff 51 0)]
  else [mkAC BC_GEU (SOff 53 1) (SOff 51 0); mkAC BC_GEU (SOff 53 2) (SOff 51 0)].
(* the boundary form (atoms only: a re-key installs no cond and no alias) and the running form *)
Definition crt5_factsH0 : facts := mkFacts crt5_atomsH [] [].
Definition crt5_factsH (nb : Z) : facts := mkFacts crt5_atomsH (crt5_condsH nb) crt5_alias.
Definition crt5_ssH (nb : Z) (G : facts) : sstate :=
  mkSS 0x81e18 crt5_regsH [crt5_body nb; crt5_want 0] None G.

(* ---- B, 0x81e8c (A 0x81d7c): the three bytes are read (s6 = c0, ra = c1, s7 = c2), the first character's class is
   still open; a2 = i + 2, s11 = i + 1 ---- *)
Definition crt5_regsB : list sv :=
  [SLit 0; SOff 57 0; SOff 2 0; SOff 3 0; SOff 4 0;
   SLit 25; SLit 51; SLit 61; SOff 8 0; SOff 9 0;
   SOff 66 0; SOff 67 0; SOff 78 0; SOff 53 0; SOff 82 0;
   SOff 77 0; SLit 103; SLit 18446744073709551615;
   SOff 76 0; SOff 54 0; SOff 51 0; SOff 52 0; SOff 56 0;
   SOff 58 0; SOff 70 0; SOff 71 0; SOff 26 0; SOff 79 0;
   SOff 74 0; SLit 207; SOff 75 0; SOff 54 0].
Definition crt5_atomsB (lo hi : Z) : list (nat * afact) :=
  crt5_base ++ [(56%nat, mkAF lo hi 0); (57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0)].
Definition crt5_factsB (lo hi : Z) : facts :=
  mkFacts (crt5_atomsB lo hi)
          (if lo =? 248 then [mkAC BC_EQ (SAlu ALU_SRL (SOff 56 0) (SLit 2)) (SLit 62)] else []) [].
Definition crt5_ssB (G : facts) : sstate := mkSS 0x81e8c crt5_regsB [crt5_want 0] None G.

(* ---- C, 0x81ef4 (A 0x81dd8): the second character's value is the atom 59, in t5 (A: s10) ---- *)
Definition crt5_regsC : list sv :=
  [SLit 0; SOff 57 0; SOff 2 0; SOff 3 0; SOff 4 0;
   SLit 25; SLit 51; SLit 61; SOff 8 0; SOff 9 0;
   SOff 66 0; SOff 67 0; SOff 78 0; SOff 53 0; SOff 82 0;
   SOff 77 0; SLit 103; SLit 18446744073709551615;
   SOff 76 0; SOff 54 0; SOff 51 0; SOff 52 0; SOff 69 0;
   SOff 58 0; SOff 70 0; SOff 71 0; SOff 26 0; SOff 79 0;
   SOff 74 0; SLit 207; SOff 59 0; SOff 54 0].
Definition crt5_atomsC (lo hi : Z) : list (nat * afact) :=
  crt5_base ++ [(57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0); (59%nat, mkAF lo hi 0)].
Definition crt5_factsC (lo hi : Z) (h1 : bool) : facts :=
  mkFacts (crt5_atomsC lo hi)
          ((if lo =? 62 then crt5_eq62 else []) ++
           (if h1 then [crt5_h1 true] else [crt5_h1 false; crt5_h2 false; crt5_more false])) [].
Definition crt5_factsC0 : facts := mkFacts (crt5_atomsC 0 63) [] [].
Definition crt5_ssC (G : facts) : sstate := mkSS 0x81ef4 crt5_regsC [crt5_want 1] None G.

(* ---- D1, 0x81f60 (A 0x81e38): the third character's value is 59 (a1), its multiple of 4 is 60 (t5); the store
   cursor s6 is q + 1, the run's own SOff 54 1 (re-keyed with crt5_PQ, which keeps atom 54) ---- *)
Definition crt5_regsD1 : list sv :=
  [SLit 0; SOff 65 0; SOff 2 0; SOff 3 0; SOff 4 0;
   SLit 25; SLit 51; SLit 61; SOff 8 0; SOff 9 0;
   SOff 66 0; SOff 59 0; SOff 78 0; SOff 53 0; SOff 82 0;
   SOff 77 0; SLit 103; SLit 18446744073709551615;
   SOff 76 0; SOff 54 0; SOff 51 0; SOff 52 0; SOff 54 1;
   SOff 58 0; SOff 70 0; SOff 71 0; SOff 26 0; SOff 73 0;
   SOff 74 0; SLit 207; SOff 60 0; SOff 54 0].
Definition crt5_atomsD1 (lo hi tlo thi : Z) : list (nat * afact) :=
  crt5_base ++ [(58%nat, mkAF 0 255 0); (59%nat, mkAF lo hi 0); (60%nat, mkAF tlo thi 0)].
Definition crt5_factsD1 (lo hi tlo thi : Z) (h2 : bool) : facts :=
  mkFacts (crt5_atomsD1 lo hi tlo thi)
          ((if lo =? 62 then crt5_eq62 else []) ++
           (if h2 then [crt5_h2 true] else [crt5_h2 false; crt5_more false])) [].
Definition crt5_factsD10 : facts := mkFacts (crt5_atomsD1 0 63 0 63) [] [].
Definition crt5_ssD1 (G : facts) : sstate := mkSS 0x81f60 crt5_regsD1 [crt5_want 2] None G.

(* ---- E1, 0x81f98 (A 0x81e68): the fourth character's value is 59 (a1); s6 = q + 2 ---- *)
Definition crt5_regsE1 : list sv :=
  [SLit 0; SOff 65 0; SOff 2 0; SOff 3 0; SOff 4 0;
   SLit 25; SLit 51; SLit 61; SOff 8 0; SOff 9 0;
   SOff 66 0; SOff 59 0; SOff 78 0; SOff 53 0; SOff 82 0;
   SOff 77 0; SLit 103; SLit 18446744073709551615;
   SOff 76 0; SOff 54 0; SOff 51 0; SOff 52 0; SOff 54 2;
   SOff 58 0; SOff 70 0; SOff 71 0; SOff 26 0; SOff 73 0;
   SOff 74 0; SLit 207; SOff 75 0; SOff 54 0].
Definition crt5_atomsE1 (lo hi : Z) : list (nat * afact) := crt5_base ++ [(59%nat, mkAF lo hi 0)].
Definition crt5_factsE1 (lo hi : Z) (more : bool) : facts :=
  mkFacts (crt5_atomsE1 lo hi) ((if lo =? 62 then crt5_eq62 else []) ++ [crt5_more more]) [].
Definition crt5_factsE10 : facts := mkFacts (crt5_atomsE1 0 63) [] [].
Definition crt5_ssE1 (G : facts) : sstate := mkSS 0x81f98 crt5_regsE1 [crt5_want 3] None G.

(* ---- the state the walk hands back at 0x82098 (after 0x82094 `addi a0, t6, 4`, before the three slot reloads
   0x82098 .. 0x820a0, which crt5_seg5 runs from the boundary's slot region): registers only, no region, atoms only.
   a0 = s3 = s6 = q + 4 (80), a3 = i + 3 (81), t6 = q (54) ---- *)
Definition crt5_regsOut : list sv :=
  [SLit 0; SOff 65 0; SOff 2 0; SOff 3 0; SOff 4 0;
   SLit 25; SLit 51; SLit 61; SOff 8 0; SOff 9 0;
   SOff 80 0; SOff 67 0; SOff 68 0; SOff 81 0; SOff 82 0;
   SOff 77 0; SLit 103; SLit 18446744073709551615;
   SOff 76 0; SOff 80 0; SOff 51 0; SOff 52 0; SOff 80 0;
   SOff 72 0; SOff 70 0; SOff 71 0; SOff 26 0; SOff 73 0;
   SOff 74 0; SLit 207; SOff 75 0; SOff 54 0].
Definition crt5_factsOut : facts :=
  mkFacts [(76%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (51%nat, mkAF 1 3145728 0);
           (52%nat, mkAF 4096 CRT5_CEIL 0); (80%nat, mkAF 4096 CRT5_CEIL 0);
           (81%nat, mkAF 0 3145731 0)] [] [].
Definition crt5_ssOut : sstate := mkSS 0x82098 crt5_regsOut [] None crt5_factsOut.

(* ---- the thirty-two registers, to decide the walk's kept-register list ---- *)
Lemma crt5_bv5_cases : forall r : bv 5,
  r = Z_to_bv 5 0 \/ r = Z_to_bv 5 1 \/ r = Z_to_bv 5 2 \/ r = Z_to_bv 5 3 \/ r = Z_to_bv 5 4 \/ r = Z_to_bv 5 5 \/ r = Z_to_bv 5 6 \/ r = Z_to_bv 5 7 \/ r = Z_to_bv 5 8 \/ r = Z_to_bv 5 9 \/ r = Z_to_bv 5 10 \/ r = Z_to_bv 5 11 \/ r = Z_to_bv 5 12 \/ r = Z_to_bv 5 13 \/ r = Z_to_bv 5 14 \/ r = Z_to_bv 5 15 \/ r = Z_to_bv 5 16 \/ r = Z_to_bv 5 17 \/ r = Z_to_bv 5 18 \/ r = Z_to_bv 5 19 \/ r = Z_to_bv 5 20 \/ r = Z_to_bv 5 21 \/ r = Z_to_bv 5 22 \/ r = Z_to_bv 5 23 \/ r = Z_to_bv 5 24 \/ r = Z_to_bv 5 25 \/ r = Z_to_bv 5 26 \/ r = Z_to_bv 5 27 \/ r = Z_to_bv 5 28 \/ r = Z_to_bv 5 29 \/ r = Z_to_bv 5 30 \/ r = Z_to_bv 5 31.
Proof.
intros r. pose proof (u5_range r) as Hr.
assert (H : forall k : Z, 0 <= k < 32 -> bv_unsigned r = k -> r = Z_to_bv 5 k).
{ intros k Hk Hv. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hv. }
destruct (Z.eq_dec (bv_unsigned r) 0) as [E0|?]; [left; exact (H 0 ltac:(lia) E0)|].
destruct (Z.eq_dec (bv_unsigned r) 1) as [E1|?]; [do 1 right; left; exact (H 1 ltac:(lia) E1)|].
destruct (Z.eq_dec (bv_unsigned r) 2) as [E2|?]; [do 2 right; left; exact (H 2 ltac:(lia) E2)|].
destruct (Z.eq_dec (bv_unsigned r) 3) as [E3|?]; [do 3 right; left; exact (H 3 ltac:(lia) E3)|].
destruct (Z.eq_dec (bv_unsigned r) 4) as [E4|?]; [do 4 right; left; exact (H 4 ltac:(lia) E4)|].
destruct (Z.eq_dec (bv_unsigned r) 5) as [E5|?]; [do 5 right; left; exact (H 5 ltac:(lia) E5)|].
destruct (Z.eq_dec (bv_unsigned r) 6) as [E6|?]; [do 6 right; left; exact (H 6 ltac:(lia) E6)|].
destruct (Z.eq_dec (bv_unsigned r) 7) as [E7|?]; [do 7 right; left; exact (H 7 ltac:(lia) E7)|].
destruct (Z.eq_dec (bv_unsigned r) 8) as [E8|?]; [do 8 right; left; exact (H 8 ltac:(lia) E8)|].
destruct (Z.eq_dec (bv_unsigned r) 9) as [E9|?]; [do 9 right; left; exact (H 9 ltac:(lia) E9)|].
destruct (Z.eq_dec (bv_unsigned r) 10) as [E10|?]; [do 10 right; left; exact (H 10 ltac:(lia) E10)|].
destruct (Z.eq_dec (bv_unsigned r) 11) as [E11|?]; [do 11 right; left; exact (H 11 ltac:(lia) E11)|].
destruct (Z.eq_dec (bv_unsigned r) 12) as [E12|?]; [do 12 right; left; exact (H 12 ltac:(lia) E12)|].
destruct (Z.eq_dec (bv_unsigned r) 13) as [E13|?]; [do 13 right; left; exact (H 13 ltac:(lia) E13)|].
destruct (Z.eq_dec (bv_unsigned r) 14) as [E14|?]; [do 14 right; left; exact (H 14 ltac:(lia) E14)|].
destruct (Z.eq_dec (bv_unsigned r) 15) as [E15|?]; [do 15 right; left; exact (H 15 ltac:(lia) E15)|].
destruct (Z.eq_dec (bv_unsigned r) 16) as [E16|?]; [do 16 right; left; exact (H 16 ltac:(lia) E16)|].
destruct (Z.eq_dec (bv_unsigned r) 17) as [E17|?]; [do 17 right; left; exact (H 17 ltac:(lia) E17)|].
destruct (Z.eq_dec (bv_unsigned r) 18) as [E18|?]; [do 18 right; left; exact (H 18 ltac:(lia) E18)|].
destruct (Z.eq_dec (bv_unsigned r) 19) as [E19|?]; [do 19 right; left; exact (H 19 ltac:(lia) E19)|].
destruct (Z.eq_dec (bv_unsigned r) 20) as [E20|?]; [do 20 right; left; exact (H 20 ltac:(lia) E20)|].
destruct (Z.eq_dec (bv_unsigned r) 21) as [E21|?]; [do 21 right; left; exact (H 21 ltac:(lia) E21)|].
destruct (Z.eq_dec (bv_unsigned r) 22) as [E22|?]; [do 22 right; left; exact (H 22 ltac:(lia) E22)|].
destruct (Z.eq_dec (bv_unsigned r) 23) as [E23|?]; [do 23 right; left; exact (H 23 ltac:(lia) E23)|].
destruct (Z.eq_dec (bv_unsigned r) 24) as [E24|?]; [do 24 right; left; exact (H 24 ltac:(lia) E24)|].
destruct (Z.eq_dec (bv_unsigned r) 25) as [E25|?]; [do 25 right; left; exact (H 25 ltac:(lia) E25)|].
destruct (Z.eq_dec (bv_unsigned r) 26) as [E26|?]; [do 26 right; left; exact (H 26 ltac:(lia) E26)|].
destruct (Z.eq_dec (bv_unsigned r) 27) as [E27|?]; [do 27 right; left; exact (H 27 ltac:(lia) E27)|].
destruct (Z.eq_dec (bv_unsigned r) 28) as [E28|?]; [do 28 right; left; exact (H 28 ltac:(lia) E28)|].
destruct (Z.eq_dec (bv_unsigned r) 29) as [E29|?]; [do 29 right; left; exact (H 29 ltac:(lia) E29)|].
destruct (Z.eq_dec (bv_unsigned r) 30) as [E30|?]; [do 30 right; left; exact (H 30 ltac:(lia) E30)|].
destruct (Z.eq_dec (bv_unsigned r) 31) as [E31|?]; [do 31 right; exact (H 31 ltac:(lia) E31)|].
lia.
Qed.

(* ================= the walk ================= *)
Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable W : world tfibsegs.
(* the journal the loop keeps: it makes no call and allocates nothing, so every component is fixed *)
Variables (STK sp0 : Z) (FP : list (Z * Z)) (lyA : alayout) (SA : astate) (W0 : world tfibsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (Up : list (Z * Z)) (kj : Z).
(* the body at bd, its length l, the destination want of En + 1 bytes *)
Variables (bd want l En : Z) (bs : list Z).
Hypothesis HLEN : Z.of_nat (length bs) = l.
Hypothesis HLB : 1 <= l <= 3145728.
Hypothesis HEN : En = (l + 2) / 3 * 4.
Hypothesis HBD : 4096 <= bd /\ bd + l <= alloc_ceiling.
Hypothesis HWT : 4096 <= want /\ want + En + 1 <= alloc_ceiling.
Hypothesis HDJ : want + En + 1 <= bd \/ bd + l <= want.
Hypothesis HSHD : forall x, bd <= x < bd + l -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Hypothesis HSHW : forall x, want <= x < want + En + 1 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Hypothesis HAWR : forall a, want <= a < want + En + 1 ->
  awr_byte tfibsegs B STK sp0 FP (ablocks B lyA SA) (ablocks B lyc Sc) lyc own (frames SA) a.

(* what the loop keeps of memory *)
Definition crt5_memf (m : word -> option byte) : Prop :=
  garr8 tfibsegs (mrestrict (w_H W) m) bd bs /\
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF bd l /\
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF want (En + 1) /\
  (forall a, want <= a < want + En + 1 -> writable_at tfibsegs (mrestrict (w_H W) m) a).
(* the first n characters of the encoding are at want *)
Definition crt5_out (m : word -> option byte) (n : nat) : Prop :=
  forall j, (j < n)%nat -> val_mem tfibsegs (mrestrict (w_H W) m) (want + Z.of_nat j) 1 (nth j (b64_enc bs) 0).
Definition crt5_JR (m : word -> option byte) (mdc : Model) : Prop :=
  ajournal tfibsegs B STK sp0 FP lyA SA W0 mem0 md0 own lyc Sc W (unpoison Up m) mdc kj /\
  ARU tfibsegs B lyc Sc Up W m mdc.
(* the atoms every state of the walk holds; regs0 is the register file at the loop's entry. B: the frame-shadow
   register is s10 = x26 (A: s3 = x19); a4 = ~bd is pinned by value at atom 82 (A's 68 held the passive s6 = En,
   which B keeps in slot 0x28); the passive s8 / s9 are carried at 70 / 71 *)
Definition crt5_EA (E : env) (regs0 : bvmap 5 word) (i q : Z) : Prop :=
  ew E 51 = Z_to_bv 64 l /\ ew E 52 = Z_to_bv 64 bd /\ ew E 53 = Z_to_bv 64 i /\
  ew E 54 = Z_to_bv 64 q /\ ew E 55 = Z_to_bv 64 (bd + i) /\ ew E 76 = Z_to_bv 64 SHADOW_OFF /\
  ew E 2 = getr regs0 2%bv /\ ew E 3 = getr regs0 3%bv /\ ew E 4 = getr regs0 4%bv /\
  ew E 8 = getr regs0 8%bv /\ ew E 9 = getr regs0 9%bv /\ ew E 26 = getr regs0 26%bv /\
  ew E 82 = Z_to_bv 64 (2 ^ 64 - 1 - bd) /\ ew E 70 = getr regs0 24%bv /\ ew E 71 = getr regs0 25%bv.

(* the caller's part of crt5_EA: the atoms the walk never re-keys, and the two passive registers *)
Definition crt5_EA_low (E : env) (regs0 : bvmap 5 word) : Prop :=
  ew E 2 = YK11.getr regs0 2%bv /\ ew E 3 = YK11.getr regs0 3%bv /\ ew E 4 = YK11.getr regs0 4%bv /\
  ew E 8 = YK11.getr regs0 8%bv /\ ew E 9 = YK11.getr regs0 9%bv /\ ew E 26 = YK11.getr regs0 26%bv /\
  ew E 70 = YK11.getr regs0 24%bv /\ ew E 71 = YK11.getr regs0 25%bv.
(* ---- arithmetic of the trip counter ---- *)
Lemma crt5_ceil : alloc_ceiling <= CRT5_CEIL.
Proof. pose proof asan_consts as ((_ & H) & _). unfold CRT5_CEIL. lia. Qed.
Lemma crt5_q_room : forall i, 0 <= i < l -> i mod 3 = 0 -> i / 3 * 4 + 4 <= En.
Proof. intros i Hi Hm. rewrite HEN. Z.div_mod_to_equations. lia. Qed.
Lemma crt5_en_pos : 4 <= En.
Proof. rewrite HEN. Z.div_mod_to_equations. lia. Qed.

(* ---- memory kept across a write inside [want, want + En + 1) ---- *)
Lemma crt5_mbyte_keep : forall (m m' : word -> option byte) (P : Z -> Prop) a,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a < 2 ^ 64 -> ~ P a ->
  mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a.
Proof.
intros m m' P a Hk Ha HP. unfold mbyte, mrestrict. rewrite (Hk (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact HP.
Qed.
Lemma crt5_aview_keep : forall (m m' : word -> option byte) (P : Z -> Prop) a,
  (forall x : word, ~ P (bv_unsigned x) -> m' x = m x) -> 0 <= a < 2 ^ 64 -> ~ P a ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Proof.
intros m m' P a Hk Ha HP. unfold aview. rewrite (crt5_mbyte_keep m m' P a Hk Ha HP). reflexivity.
Qed.
Lemma crt5_memf_keep : forall (m m' : word -> option byte) (lo hi : Z),
  crt5_memf m -> want <= lo -> hi <= want + En + 1 ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> crt5_memf m'.
Proof.
intros m m' lo hi (HG & HRB & HRW & HWr) Hlo Hhi Hk Hgr.
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
pose proof crt5_en_pos. pose proof crt5_ceil.
assert (SH : forall x, 0 <= x < 2 ^ 47 ->
  aview tfibsegs (w_H W) m' (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx.
  assert (Hy : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 17592186044416)
    by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply (crt5_aview_keep m m' (fun a => lo <= a < hi) _ Hk); [unfold SHADOW_OFF in *; lia|].
  cbv beta. intros Hc. apply (HSHW (shadow_of_addr SHADOW_OFF x)); [lia | exact Hy]. }
split; [|split; [|split]].
- intros j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr]. intros kk Hkk.
  rewrite <- (Hv kk Hkk). apply (crt5_mbyte_keep m m' (fun a => lo <= a < hi) _ Hk); cbv beta.
  + destruct HBD. lia.
  + destruct HBD. destruct HWT. destruct HDJ as [HD1 | HD2]; lia.
- intros x Hx. destruct (HRB x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite SH; [exact Hs | destruct HBD; lia].
- intros x Hx. destruct (HRW x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite SH; [exact Hs | destruct HWT; lia].
- intros a Ha. apply (writable_at_grows _ _ _ _ Hgr). apply HWr. exact Ha.
Qed.
Lemma crt5_out_keep : forall (m m' : word -> option byte) (n : nat) (lo hi : Z),
  crt5_out m n -> want + Z.of_nat n <= lo -> Z.of_nat n <= En ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) -> crt5_out m' n.
Proof.
intros m m' n lo hi HO Hlo Hn Hk j Hj kk Hkk.
pose proof (HO j Hj kk Hkk) as Hv. rewrite <- Hv.
pose proof crt5_en_pos. destruct HWT. destruct HBD.
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
apply (crt5_mbyte_keep m m' (fun a => lo <= a < hi) _ Hk).
- cbv beta. lia.
- cbv beta. lia.
Qed.

(* ---- the shadow entries of the two blocks the trip touches ---- *)
Lemma crt5_U_atom : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> U E (SOff n 0) = x.
Proof. intros E n x Hn Hx. rewrite (crt5_U_off E n x 0 Hn Hx ltac:(lia)). lia. Qed.
Lemma crt5_shok_w : forall E m q lo,
  crt5_memf m -> ew E 76 = Z_to_bv 64 SHADOW_OFF -> ew E 54 = Z_to_bv 64 q ->
  0 <= lo <= 4 -> want <= q -> q + 4 <= want + En ->
  sh_ok tfibsegs crt5_Bx (crt5_SHw lo) E (mrestrict (w_H W) m).
Proof.
intros E m q lo (_ & _ & HRW & _) H76 H54 Hlo Hq1 Hq2.
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _). destruct HWT as [HW1 HW2].
assert (HB : U E crt5_Bx = SHADOW_OFF)
  by (unfold crt5_Bx; apply (crt5_U_atom E 76 SHADOW_OFF H76); unfold SHADOW_OFF; lia).
assert (HQ : U E (SOff 54 0) = q) by (apply (crt5_U_atom E 54 q H54); lia).
unfold sh_ok, crt5_SHw. constructor; [|constructor].
eapply (shent_ok_of_range tfibsegs (w_H W) m E crt5_Bx 54 want (En + 1) q lo 4 HRW HB HQ
  ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. apply HSHW. lia.
Qed.
Lemma crt5_shok_H : forall E m q i nb,
  crt5_memf m -> ew E 76 = Z_to_bv 64 SHADOW_OFF -> ew E 54 = Z_to_bv 64 q ->
  ew E 55 = Z_to_bv 64 (bd + i) -> 0 <= i -> i + nb <= l -> 1 <= nb <= 3 ->
  want <= q -> q + 4 <= want + En ->
  sh_ok tfibsegs crt5_Bx (crt5_SHH nb) E (mrestrict (w_H W) m).
Proof.
intros E m q i nb HM H76 H54 H55 Hi Hin Hnb Hq1 Hq2.
pose proof HM as (_ & HRB & _ & _).
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _). destruct HBD as [HD1 HD2].
assert (HB : U E crt5_Bx = SHADOW_OFF)
  by (unfold crt5_Bx; apply (crt5_U_atom E 76 SHADOW_OFF H76); unfold SHADOW_OFF; lia).
assert (HP : U E (SOff 55 0) = bd + i) by (apply (crt5_U_atom E 55 (bd + i) H55); lia).
unfold sh_ok, crt5_SHH. constructor.
- eapply (shent_ok_of_range tfibsegs (w_H W) m E crt5_Bx 55 bd l (bd + i) 0 nb HRB HB HP
    ltac:(lia) ltac:(lia)).
  intros x Hx. cbn [Z.min Z.max] in Hx. rewrite Z.max_r in Hx by lia. apply HSHD. lia.
- pose proof (crt5_shok_w E m q 0 HM H76 H54 ltac:(lia) Hq1 Hq2) as HS.
  unfold sh_ok, crt5_SHw in HS. exact HS.
Qed.

(* ---- the write window of a trip is inside the destination block ---- *)
Lemma crt5_awr_w : forall E q lo,
  ew E 54 = Z_to_bv 64 q -> want <= q -> q + 4 <= want + En -> 0 <= lo <= 4 ->
  awr_ok tfibsegs B E [crt5_want lo] STK sp0 FP (ablocks B lyA SA) (ablocks B lyc Sc) lyc own (frames SA).
Proof.
intros E q lo H54 Hq1 Hq2 Hlo.
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _). destruct HWT as [HW1 HW2].
eapply (awr_ok_cons_gen tfibsegs B E (crt5_want lo) [] STK sp0 FP (ablocks B lyA SA) (ablocks B lyc Sc)
  lyc own (frames SA) 54 q);
  first
  [ lazymatch goal with |- YP09.r_base _ = Some _ => solve [reflexivity] end
  | lazymatch goal with |- bv_unsigned _ = _ => solve [rewrite H54; apply unsigned_lit_small; lia] end
  | lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => solve [apply awr_ok_nil] end
  | lazymatch goal with |- forall _, _ =>
      solve [unfold crt5_want; cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HAWR; lia] end ].
Qed.
Lemma crt5_awr_H : forall E q nb,
  ew E 54 = Z_to_bv 64 q -> want <= q -> q + 4 <= want + En ->
  awr_ok tfibsegs B E [crt5_body nb; crt5_want 0] STK sp0 FP (ablocks B lyA SA) (ablocks B lyc Sc) lyc own
    (frames SA).
Proof.
intros E q nb H54 Hq1 Hq2. apply awr_ok_cons_ro; [unfold crt5_body; cbn; lia|].
exact (crt5_awr_w E q 0 H54 Hq1 Hq2 ltac:(lia)).
Qed.

(* ---- one byte of a region, as the machine holds it ---- *)
Lemma crt5_zbv8_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_mod. lia.
Qed.
Lemma crt5_le_byte1 : forall v, le_byte v 1 0 = v mod 256.
Proof.
intros v. unfold le_byte.
rewrite Z.shiftr_div_pow2 by (cbn [Z.of_nat]; lia).
replace (2 ^ (8 * Z.of_nat 0)) with 1 by (cbn [Z.of_nat]; reflexivity).
replace (2 ^ (8 * Z.of_nat 1)) with 256 by (cbn [Z.of_nat]; reflexivity).
rewrite Z.div_1_r. apply Z.mod_mod. lia.
Qed.
Lemma crt5_chunk_byte : forall E (m : word -> option byte) n b cs lo hi wlo whi od e,
  region_ok tfibsegs E (mrestrict (w_H W) m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs ->
  val_mem tfibsegs (mrestrict (w_H W) m) (b + od) 1 (U E e mod 256).
Proof.
intros E m n b cs lo hi wlo whi od e (_ & _ & _ & Hcs) Hn Hin.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (bb & Hcb & Hmb).
cbn [cbyte YP09.c_off YP09.c_val byte_of_word] in Hcb. rewrite ?Z.mul_0_r, ?Z.shiftr_0_r in Hcb.
injection Hcb as <-. intros kk Hkk.
assert (kk = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
cbn [YP09.c_off] in Hmb. rewrite ?Z.add_0_r in Hmb. rewrite Hmb.
rewrite crt5_le_byte1. rewrite Z.mod_mod by lia. rewrite crt5_zbv8_mod. reflexivity.
Qed.

(* ---- the regions of the states ---- *)
Lemma crt5_region_want : forall E m q lo,
  crt5_memf m -> ew E 54 = Z_to_bv 64 q -> want <= q -> q + 4 <= want + En -> 0 <= lo <= 4 ->
  region_ok tfibsegs E (mrestrict (w_H W) m) (crt5_want lo).
Proof.
intros E m q lo (_ & _ & _ & HWr) H54 Hq1 Hq2 Hlo.
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _). destruct HWT as [HW1 HW2].
unfold region_ok, crt5_want. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H54, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply HWr; lia | constructor].
Qed.
Lemma crt5_chunk_body : forall E m i (j : nat),
  garr8 tfibsegs (mrestrict (w_H W) m) bd bs -> ew E 55 = Z_to_bv 64 (bd + i) ->
  ew E (56 + j)%nat = Z_to_bv 64 (nth (Z.to_nat i + j) bs 0) ->
  0 <= i -> (Z.to_nat i + j < length bs)%nat ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W) m) (bd + i)
    (YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (56 + j) 0))).
Proof.
intros E m i j HG H55 Hj Hi Hlt.
destruct (HG (Z.to_nat i + j)%nat Hlt) as [Hv Hr].
apply (chunk_ok_val tfibsegs E (mrestrict (w_H W) m) (bd + i) (Z.of_nat j) 1 (SOff (56 + j) 0)
  (nth (Z.to_nat i + j) bs 0)).
- cbn [sv_denot]. rewrite Hj, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
- cbn. lia.
- cbn. lia.
- cbn [N.to_nat]. replace (bd + i + Z.of_nat j) with (bd + Z.of_nat (Z.to_nat i + j)) by lia.
  exact Hv.
Qed.

(* ---- reading a register of a state, and the facts a state installs ---- *)
Lemma crt5_regv : forall E ss (ms : machine_state) (r : bv 5) n (v : word),
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  ew E n = v -> getr (ms_regs ms) r = v.
Proof.
intros E ss ms r n v HS Hr Hn.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS), Hr, fsw_SOff0. exact Hn.
Qed.
Lemma crt5_regv_off : forall E ss (ms : machine_state) (r : bv 5) n c v,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff n c ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  getr (ms_regs ms) r = Z_to_bv 64 (v + c).
Proof.
intros E ss ms r n c v HS Hr Hn Hv Hvc.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS), Hr.
apply bv_eq. change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
rewrite (crt5_U_off E n v c Hn Hv Hvc), unsigned_lit_small by lia. reflexivity.
Qed.
Lemma crt5_regv_offw : forall E ss (ms : machine_state) (r : bv 5) n c v w,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff n c ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> v + c = w ->
  getr (ms_regs ms) r = Z_to_bv 64 w.
Proof.
intros E ss ms r n c v w HS Hr Hn Hv Hvc <-. exact (crt5_regv_off E ss ms r n c v HS Hr Hn Hv Hvc).
Qed.
Lemma crt5_regv_U : forall E ss (ms : machine_state) (r : bv 5) e v,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = e ->
  U E e = v -> 0 <= v < 2 ^ 64 -> getr (ms_regs ms) r = Z_to_bv 64 v.
Proof.
intros E ss ms r e v HS Hr Hv Hb.
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms r HS), Hr.
apply bv_eq. change (bv_unsigned (sv_denot E e)) with (U E e). rewrite Hv, unsigned_lit_small by lia.
reflexivity.
Qed.
Lemma crt5_regv_lit : forall E ss (ms : machine_state) (r : bv 5) z,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SLit z -> 0 <= z < 2 ^ 64 ->
  getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros. apply (fsw_reg_lit (w_H W) E ss ms r z); assumption. Qed.
Lemma crt5_ext : forall E (K : nat) ws n, (n < K)%nat -> ew (extK E K ws) n = ew E n.
Proof. intros E K ws n H. exact (proj1 (env_agree_extK E K ws) n H). Qed.
Lemma crt5_env_agree : forall E vs, env_agree_pd crt5_P PT E (havoc E 51 vs).
Proof.
intros E vs. split; [|intros d _; reflexivity].
intros n Hn. unfold crt5_P in Hn. apply Nat.ltb_lt in Hn. apply ew_havoc_old. exact Hn.
Qed.
(* the branch facts a state carries: an unsigned comparison of two atom offsets *)
Lemma crt5_cond_ltu : forall E n c m x y,
  ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  0 <= y < 2 ^ 64 -> x + c < y -> acond_ok E (mkAC BC_LTU (SOff n c) (SOff m 0)).
Proof.
intros E n c m x y Hn Hm Hx Hxc Hy Hlt. unfold acond_ok. cbn [ac_c ac_a ac_b].
cbn [branch_taken]. unfold bv_ltu.
change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
change (bv_unsigned (sv_denot E (SOff m 0))) with (U E (SOff m 0)).
rewrite (crt5_U_off E n x c Hn Hx Hxc), (crt5_U_atom E m y Hm Hy).
apply Z.ltb_lt. lia.
Qed.
Lemma crt5_cond_geu : forall E n c m x y,
  ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  0 <= y < 2 ^ 64 -> y <= x + c -> acond_ok E (mkAC BC_GEU (SOff n c) (SOff m 0)).
Proof.
intros E n c m x y Hn Hm Hx Hxc Hy Hge. unfold acond_ok. cbn [ac_c ac_a ac_b].
cbn [branch_taken]. unfold bv_ltu.
change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
change (bv_unsigned (sv_denot E (SOff m 0))) with (U E (SOff m 0)).
rewrite (crt5_U_off E n x c Hn Hx Hxc), (crt5_U_atom E m y Hm Hy).
apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma crt5_alias_ok : forall E i,
  ew E 52 = Z_to_bv 64 bd -> ew E 53 = Z_to_bv 64 i -> ew E 55 = Z_to_bv 64 (bd + i) ->
  ew E 77 = Z_to_bv 64 (bd + 1) -> 0 <= i -> i < l ->
  alias_ok E crt5_alias.
Proof.
intros E i H52 H53 H55 H77 Hi0 Hil.
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _). destruct HBD as [HD1 HD2].
split; [|split; [|exact I]].
- apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (crt5_U_atom E 52 bd H52 ltac:(lia)), (crt5_U_atom E 53 i H53 ltac:(lia)),
    (crt5_U_atom E 55 (bd + i) H55 ltac:(lia)).
  apply zcanon_id. unfold M64. lia.
- apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (crt5_U_atom E 77 (bd + 1) H77 ltac:(lia)), (crt5_U_atom E 53 i H53 ltac:(lia)),
    (crt5_U_off E 55 (bd + i) 1 H55 ltac:(lia) ltac:(lia)).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the re-key: the env of the next canonical state, and its three obligation sets ---- *)
Lemma crt5_ew_ewset : forall E k v n, (n < k)%nat -> ew (ewset E k v) n = ew E n.
Proof. intros E k v n H. cbn [ew ewset]. destruct (Nat.eqb_spec n k); [lia | reflexivity]. Qed.
(* the values of atoms 51 .. 82 at a boundary: the loop's own numbers, then the registers the walk carries
   (B: ra a0 a1 a2 s6 s8 s9 s7 s11 t3 t5 at 65 .. 75), then the pinned values (B: ~bd at 82, a4's UBSan bound) *)
Definition crt5_vs (ms : machine_state) (i q c0 c1 c2 v tv : Z) : list word :=
  [Z_to_bv 64 l; Z_to_bv 64 bd; Z_to_bv 64 i; Z_to_bv 64 q; Z_to_bv 64 (bd + i);
   Z_to_bv 64 c0; Z_to_bv 64 c1; Z_to_bv 64 c2; Z_to_bv 64 v; Z_to_bv 64 tv;
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   YK11.getr (ms_regs ms) 1%bv; YK11.getr (ms_regs ms) 10%bv; YK11.getr (ms_regs ms) 11%bv;
   YK11.getr (ms_regs ms) 12%bv; YK11.getr (ms_regs ms) 22%bv; YK11.getr (ms_regs ms) 24%bv;
   YK11.getr (ms_regs ms) 25%bv; YK11.getr (ms_regs ms) 23%bv; YK11.getr (ms_regs ms) 27%bv;
   YK11.getr (ms_regs ms) 28%bv; YK11.getr (ms_regs ms) 30%bv;
   Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (bd + 1); Z_to_bv 64 (i + 2); Z_to_bv 64 (i + 1);
   Z_to_bv 64 (q + 4); Z_to_bv 64 (i + 3); Z_to_bv 64 (2 ^ 64 - 1 - bd)].
Lemma crt5_rekey : forall E2 ss2 (ms2 : machine_state) regs' rs' G' vs,
  st_ok tfibsegs E2 ss2 (restrict (w_H W) ms2) ->
  reabs_check crt5_P ss2 regs' G' = true ->
  Forall (fun rj : bv 5 * nat => ew (havoc E2 51 vs) (snd rj) = YK11.getr (ms_regs ms2) (fst rj))
    (reabs_obl crt5_P regs') ->
  Forall (fun nf : nat * afact => afact_ok (havoc E2 51 vs) (fst nf) (snd nf)) (fact_obls crt5_P G') ->
  mem_ok tfibsegs (havoc E2 51 vs) (mrestrict (w_H W) (ms_mem ms2)) rs' ->
  st_ok tfibsegs (havoc E2 51 vs) (mkSS (ss_pc ss2) regs' rs' None G') (restrict (w_H W) ms2).
Proof.
intros E2 ss2 ms2 regs' rs' G' vs HS Hck Hobl Hfo HM.
exact (st_ok_reabs tfibsegs crt5_P E2 (havoc E2 51 vs) ss2 (restrict (w_H W) ms2) regs' rs' G'
  HS (crt5_env_agree E2 vs) Hck Hobl Hfo HM).
Qed.
(* B only: the re-keys into D1 / E1 keep the destination atom 54 (q), since there s6 = q + 1 / q + 2 is the run's own
   SOff 54 k (B's store cursor, 0x81f2c `addi s6, t6, 1` ..; A stores through t4 with immediate offsets) and a re-key
   target may hold an offset only of a kept atom (YL09.reg_reabs_ok) *)
Definition crt5_PQ (n : nat) : bool := Nat.ltb n 51 || Nat.eqb n 54.
Lemma crt5_env_agreeQ : forall E vs, nth 3 vs (ew E 54) = ew E 54 -> env_agree_pd crt5_PQ PT E (havoc E 51 vs).
Proof.
intros E vs H54. split; [|intros d _; reflexivity].
intros n Hn. unfold crt5_PQ in Hn. apply Bool.orb_true_iff in Hn as [Hn|Hn].
- apply Nat.ltb_lt in Hn. apply ew_havoc_old. exact Hn.
- apply Nat.eqb_eq in Hn. subst n. unfold havoc. cbn [ew].
  destruct (Nat.ltb_spec 54 51) as [Hc|Hc]; [lia|]. exact H54.
Qed.
Lemma crt5_rekeyQ : forall E2 ss2 (ms2 : machine_state) regs' rs' G' vs,
  nth 3 vs (ew E2 54) = ew E2 54 ->
  st_ok tfibsegs E2 ss2 (restrict (w_H W) ms2) ->
  reabs_check crt5_PQ ss2 regs' G' = true ->
  Forall (fun rj : bv 5 * nat => ew (havoc E2 51 vs) (snd rj) = YK11.getr (ms_regs ms2) (fst rj))
    (reabs_obl crt5_PQ regs') ->
  Forall (fun nf : nat * afact => afact_ok (havoc E2 51 vs) (fst nf) (snd nf)) (fact_obls crt5_PQ G') ->
  mem_ok tfibsegs (havoc E2 51 vs) (mrestrict (w_H W) (ms_mem ms2)) rs' ->
  st_ok tfibsegs (havoc E2 51 vs) (mkSS (ss_pc ss2) regs' rs' None G') (restrict (w_H W) ms2).
Proof.
intros E2 ss2 ms2 regs' rs' G' vs H54 HS Hck Hobl Hfo HM.
exact (st_ok_reabs tfibsegs crt5_PQ E2 (havoc E2 51 vs) ss2 (restrict (w_H W) ms2) regs' rs' G'
  HS (crt5_env_agreeQ E2 vs H54) Hck Hobl Hfo HM).
Qed.
(* every register obligation is either a carried register (by computation) or one of the walk's numbers *)
Ltac crt5_obl :=
  apply Forall_forall; let rj := fresh "rj" in let Hin := fresh "Hin" in
  intros rj Hin; vm_compute in Hin;
  repeat (destruct Hin as [<-|Hin]; [cbn [fst snd]; first [reflexivity | symmetry; assumption]|]);
  destruct Hin.
Ltac crt5_fobl A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A76 A77 A82 :=
  apply Forall_forall; let nf := fresh "nf" in let Hin := fresh "Hin" in
  intros nf Hin; vm_compute in Hin;
  repeat (destruct Hin as [<-|Hin];
    [cbn [fst snd]; unfold afact_ok; cbn [af_lo af_hi af_al2];
     rewrite ?A51, ?A52, ?A53, ?A54, ?A55, ?A56, ?A57, ?A58, ?A59, ?A60, ?A76, ?A77, ?A82;
     rewrite ?Z.pow_0_r, ?Z.mod_1_r;
     rewrite unsigned_lit_small by (unfold SHADOW_OFF, CRT5_CEIL in *; lia);
     unfold SHADOW_OFF, CRT5_CEIL in *; lia |]);
  destruct Hin.

(* register readers. Kit rule: vm_compute only ever runs on a CLOSED goal - the register's symbolic value is computed
   first (eval on a closed term), its equation asserted closed, and the reading lemma applied with `exact`. *)
Ltac crt5_rv HS H :=
  lazymatch goal with |- YK11.getr (ms_regs ?ms) ?r = ?v =>
  lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
  lazymatch type of H with ew _ ?n = _ =>
    let sv := eval vm_compute in (sr_get (ss_regs ss) r) in
    lazymatch sv with SOff ?m 0 =>
      constr_eq m n;
      let Hr := fresh "Hr" in
      assert (Hr : sr_get (ss_regs ss) r = SOff n 0) by (vm_compute; reflexivity);
      exact (crt5_regv Ex ss ms r n v HS Hr ltac:(rewrite !crt5_ew_ewset by lia; exact H))
    end end end end.
Ltac crt5_rvo HS H :=
  lazymatch goal with |- YK11.getr (ms_regs ?ms) ?r = Z_to_bv 64 ?w =>
  lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
  lazymatch type of H with ew _ ?n = Z_to_bv 64 ?v =>
    let sv := eval vm_compute in (sr_get (ss_regs ss) r) in
    lazymatch sv with SOff ?m ?c =>
      constr_eq m n;
      let Hr := fresh "Hr" in
      assert (Hr : sr_get (ss_regs ss) r = SOff n c) by (vm_compute; reflexivity);
      exact (crt5_regv_offw Ex ss ms r n c v w HS Hr ltac:(rewrite !crt5_ew_ewset by lia; exact H)
               ltac:(lia) ltac:(lia) ltac:(lia))
    end end end end.
Ltac crt5_rvl HS :=
  lazymatch goal with |- YK11.getr (ms_regs ?ms) ?r = Z_to_bv 64 ?w =>
  lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
    let sv := eval vm_compute in (sr_get (ss_regs ss) r) in
    lazymatch sv with SLit _ =>
      let Hr := fresh "Hr" in
      assert (Hr : sr_get (ss_regs ss) r = SLit w) by (vm_compute; reflexivity);
      exact (crt5_regv_lit Ex ss ms r w HS Hr ltac:(lia))
    end end end.

(* ---- the register picture a boundary state hands on ---- *)
Definition crt5_mregs (ms : machine_state) (regs0 : bvmap 5 word) (i q c0 c1 c2 : Z) : Prop :=
  YK11.getr (ms_regs ms) 20%bv = Z_to_bv 64 l /\ YK11.getr (ms_regs ms) 21%bv = Z_to_bv 64 bd /\
  YK11.getr (ms_regs ms) 13%bv = Z_to_bv 64 i /\ YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 31%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 15%bv = Z_to_bv 64 (bd + 1) /\
  YK11.getr (ms_regs ms) 12%bv = Z_to_bv 64 (i + 2) /\
  YK11.getr (ms_regs ms) 27%bv = Z_to_bv 64 (i + 1) /\
  YK11.getr (ms_regs ms) 22%bv = Z_to_bv 64 c0 /\ YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 c1 /\
  YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 c2 /\
  YK11.getr (ms_regs ms) 14%bv = Z_to_bv 64 (2 ^ 64 - 1 - bd) /\
  YK11.getr (ms_regs ms) 24%bv = YK11.getr regs0 24%bv /\
  YK11.getr (ms_regs ms) 25%bv = YK11.getr regs0 25%bv.
Ltac crt5_regs_tac HS A51 A52 A53 A54 A76 A77 A56 A57 A58 A82 A70 A71 A78 A79 :=
  repeat split;
  first [ assumption | crt5_rv HS A51 | crt5_rv HS A52 | crt5_rv HS A53 | crt5_rv HS A54 | crt5_rv HS A76
        | crt5_rv HS A77 | crt5_rv HS A56 | crt5_rv HS A57 | crt5_rv HS A58
        | crt5_rv HS A82 | crt5_rv HS A70 | crt5_rv HS A71 | crt5_rv HS A78 | crt5_rv HS A79
        | crt5_rvo HS A53 | crt5_rvo HS A54 | crt5_rvl HS ].

(* ---- what the B boundary hands to the next phase ---- *)
Definition crt5_KB (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (i q c0 c1 c2 : Z)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall (E' : env) (ms' : machine_state) (mdc' : Model),
    st_ok tfibsegs E' (crt5_ssB (crt5_factsB 0 255)) (restrict (w_H W) ms') ->
    (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
    crt5_EA E' regs0 i q -> ew E' 77 = Z_to_bv 64 (bd + 1) ->
    ew E' 78 = Z_to_bv 64 (i + 2) -> ew E' 79 = Z_to_bv 64 (i + 1) ->
    ew E' 56 = Z_to_bv 64 c0 -> ew E' 57 = Z_to_bv 64 c1 -> ew E' 58 = Z_to_bv 64 c2 ->
    crt5_memf (ms_mem ms') -> crt5_out (ms_mem ms') (Z.to_nat (i / 3 * 4)) ->
    crt5_JR (ms_mem ms') mdc' ->
    (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms' x = ms_mem ms x) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr tfibsegs W (mkCfg ms' mdc') Q.
Lemma crt5_toB : forall (regs0 : bvmap 5 word) (E E1 : env) (ss1 : sstate) (ms1 ms : machine_state)
    (mdc1 : Model) (i q c0 c1 c2 : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 ->
  crt5_KB regs0 E ms i q c0 c1 c2 Q ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 ->
  st_ok tfibsegs E1 ss1 (restrict (w_H W) ms1) -> ss_pc ss1 = 0x81e8c ->
  reabs_check crt5_P ss1 crt5_regsB (crt5_factsB 0 255) = true ->
  crt5_mregs ms1 regs0 i q c0 c1 c2 ->
  (forall n, (n < 51)%nat -> ew E1 n = ew E n) ->
  crt5_EA E regs0 i q ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4)) -> crt5_JR (ms_mem ms1) mdc1 ->
  (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms1 x = ms_mem ms x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) ->
  SRr tfibsegs W (mkCfg ms1 mdc1) Q.
Proof.
intros regs0 E E1 ss1 ms1 ms mdc1 i q c0 c1 c2 Q Hi0 Hil Hm3 Hq K Hb0 Hb1 Hb2 HS Hpc Hck HR Hag HEA HM HO
  HJR Hkeep HG.
destruct HR as (R20 & R21 & R13 & R19 & R31 & R18 & R15 & R12 & R27 & R22 & R1 & R23 & R14 & R24 & R25).
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
assert (HM1 : crt5_memf (ms_mem ms1))
  by (apply (crt5_memf_keep (ms_mem ms) (ms_mem ms1) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
assert (HO1 : crt5_out (ms_mem ms1) (Z.to_nat (i / 3 * 4)))
  by (apply (crt5_out_keep (ms_mem ms) (ms_mem ms1) _ q (q + 4) HO ltac:(lia) ltac:(lia) Hkeep)).
assert (A51 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 51 = Z_to_bv 64 l) by reflexivity.
assert (A52 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 52 = Z_to_bv 64 bd) by reflexivity.
assert (A53 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 53 = Z_to_bv 64 i) by reflexivity.
assert (A54 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 54 = Z_to_bv 64 q) by reflexivity.
assert (A55 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 55 = Z_to_bv 64 (bd + i)) by reflexivity.
assert (A56 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 56 = Z_to_bv 64 c0) by reflexivity.
assert (A57 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 57 = Z_to_bv 64 c1) by reflexivity.
assert (A58 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 58 = Z_to_bv 64 c2) by reflexivity.
assert (A59 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 59 = Z_to_bv 64 0) by reflexivity.
assert (A60 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 60 = Z_to_bv 64 0) by reflexivity.
assert (A76 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 76 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (A77 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 77 = Z_to_bv 64 (bd + 1)) by reflexivity.
assert (A78 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 78 = Z_to_bv 64 (i + 2)) by reflexivity.
assert (A79 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 79 = Z_to_bv 64 (i + 1)) by reflexivity.
assert (A82 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 82 = Z_to_bv 64 (2 ^ 64 - 1 - bd)) by reflexivity.
pose proof (crt5_rekey E1 ss1 ms1 crt5_regsB [crt5_want 0] (crt5_factsB 0 255)
  (crt5_vs ms1 i q c0 c1 c2 0 0) HS Hck ltac:(crt5_obl)
  ltac:(crt5_fobl A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A76 A77 A82)
  ltac:(split; [vm_compute; reflexivity|];
        split; [constructor; [apply (crt5_region_want _ (ms_mem ms1) q 0 HM1 A54 Hq1 Hq2 ltac:(lia))
                             | constructor]
               | cbn [pairwise_disjoint all_disjoint]; tauto])) as HS3.
rewrite Hpc in HS3.
apply (K _ ms1 _ HS3);
  [ intros n Hn; rewrite ew_havoc_old by lia; apply Hag; lia
  | unfold crt5_EA; repeat split;
      first [ exact A51 | exact A52 | exact A53 | exact A54 | exact A55 | exact A76
            | exact A82 | exact R24 | exact R25
            | rewrite ew_havoc_old by lia; rewrite Hag by lia; assumption ]
  | exact A77 | exact A78 | exact A79 | exact A56 | exact A57 | exact A58
  | exact HM1 | exact HO1 | exact HJR | exact Hkeep | exact HG ].
Qed.

(* ---- an atom fact from the atom's value ---- *)
Lemma crt5_afacts : forall E (n : nat) (lo hi v : Z),
  ew E n = Z_to_bv 64 v -> lo <= v <= hi -> 0 <= v < 2 ^ 64 -> afact_ok E n (mkAF lo hi 0).
Proof.
intros E n lo hi v Hn Hv Hv64. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hn, unsigned_lit_small by exact Hv64. rewrite Z.pow_0_r, Z.mod_1_r.
split; [lia|]. split; [reflexivity | lia].
Qed.
Ltac crt5_atok A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A76 A77 :=
  cbn [atoms_ok f_atoms app crt5_base crt5_atomsH crt5_atomsB crt5_atomsC crt5_atomsD1 crt5_atomsE1
       crt5_factsH crt5_factsH0 crt5_factsB crt5_factsC crt5_factsC0 crt5_factsD1 crt5_factsD10
       crt5_factsE1 crt5_factsE10];
  repeat match goal with |- _ /\ _ => split end; try exact I;
  (eapply crt5_afacts;
    [ first [exact A51 | exact A52 | exact A53 | exact A54 | exact A55 | exact A56 | exact A57
            | exact A58 | exact A59 | exact A60 | exact A76 | exact A77 | eassumption]
    | unfold SHADOW_OFF, CRT5_CEIL in *; lia | unfold SHADOW_OFF, CRT5_CEIL in *; lia ]).
(* ---- the character the walk stores, against the released b64c ---- *)
Lemma crt5_U_addlit : forall E a k x, U E a = x -> 0 <= x -> 0 <= k -> x + k < 2 ^ 64 ->
  U E (SAlu ALU_ADD a (SLit k)) = x + k.
Proof.
intros E a k x Hx H0 Hk Hs. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, (crt5_U_lit E k ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma crt5_b64cA : forall v, 0 <= v <= 25 -> (v + 65) mod 256 = b64c v.
Proof. intros v Hv. unfold b64c. rewrite (proj2 (Z.ltb_lt v 26)) by lia. rewrite Z.mod_small by lia. lia. Qed.
Lemma crt5_b64cB : forall v, 26 <= v <= 51 -> (v + 71) mod 256 = b64c v.
Proof.
intros v Hv. unfold b64c. rewrite (proj2 (Z.ltb_ge v 26)) by lia. rewrite (proj2 (Z.ltb_lt v 52)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma crt5_b64cC : forall v, 52 <= v <= 61 -> (v + 252) mod 256 = b64c v.
Proof.
intros v Hv. unfold b64c. rewrite (proj2 (Z.ltb_ge v 26)) by lia. rewrite (proj2 (Z.ltb_ge v 52)) by lia.
rewrite (proj2 (Z.ltb_lt v 62)) by lia.
replace (v + 252) with (v - 4 + 1 * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma crt5_b64cD : 43 mod 256 = b64c 62.
Proof. reflexivity. Qed.
Lemma crt5_b64cE : 47 mod 256 = b64c 63.
Proof. reflexivity. Qed.

(* the trip writes only inside the destination window: outside it the memory is the run's own *)
Lemma crt5_keepH : forall E (m1 m2 : word -> option byte) q nb G,
  frame_of E (ss_mem (crt5_ssH nb G)) m1 m2 -> ew E 54 = Z_to_bv 64 q -> 0 <= q -> q + 4 <= 2 ^ 64 ->
  forall x : word, ~ (q <= bv_unsigned x < q + 4) -> m2 x = m1 x.
Proof.
intros E m1 m2 q nb G HFr E54 Hq0 Hq4 x Hx. apply HFr. intros (r & Hin & Hw).
cbn [ss_mem crt5_ssH In] in Hin. destruct Hin as [<-|[<-|[]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val crt5_body crt5_want] in Hw;
  [lia | rewrite E54, unsigned_lit_small in Hw by lia; lia].
Qed.
Lemma crt5_keep1 : forall E (m1 m2 : word -> option byte) q lo,
  frame_of E [crt5_want lo] m1 m2 -> ew E 54 = Z_to_bv 64 q -> 0 <= q -> q + 4 <= 2 ^ 64 -> 0 <= lo ->
  forall x : word, ~ (q + lo <= bv_unsigned x < q + 4) -> m2 x = m1 x.
Proof.
intros E m1 m2 q lo HFr E54 Hq0 Hq4 Hlo x Hx. apply HFr. intros (r & Hin & Hw).
cbn [In] in Hin. destruct Hin as [<-|[]].
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val crt5_want] in Hw.
rewrite E54, unsigned_lit_small in Hw by lia. lia.
Qed.

(* ================= phase H: 0x81e18 -> 0x81e8c, the three body bytes are read ================= *)
Lemma crt5_phH : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
  (i q nb : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> nb = Z.min 3 (l - i) ->
  st_ok tfibsegs E (crt5_ssH nb crt5_factsH0) (restrict (w_H W) ms) ->
  crt5_EA E regs0 i q -> ew E 77 = Z_to_bv 64 (bd + 1) ->
  ew E 56 = Z_to_bv 64 (nth (Z.to_nat i) bs 0) ->
  ew E 57 = Z_to_bv 64 (nth (Z.to_nat (i + 1)) bs 0) ->
  ew E 58 = Z_to_bv 64 (nth (Z.to_nat (i + 2)) bs 0) ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4)) -> crt5_JR (ms_mem ms) mdc ->
  crt5_KB regs0 E ms i q (nth (Z.to_nat i) bs 0) (nth (Z.to_nat (i + 1)) bs 0)
    (nth (Z.to_nat (i + 2)) bs 0) Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i q nb Q Hi0 Hil Hm3 Hq Hnb HS HEA H77 H56 H57 H58 HM HO HJR K.
pose proof HEA as HEAc.
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
destruct HJR as [HJ HARU].
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
assert (Hbyt : forall j, 0 <= nth j bs 0 < 256).
{ intros j. destruct (Nat.lt_ge_cases j (length bs)) as [Hj | Hj].
  - destruct HM as (HG0 & _). exact (proj2 (HG0 j Hj)).
  - rewrite crt5_nth_big by lia. lia. }
assert (HF : facts_ok E (crt5_factsH nb)).
{ pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0). unfold crt5_ssH, crt5_factsH0 in HG0.
  cbn [ss_facts] in HG0. destruct HG0 as (HA & _ & _).
  split; [exact HA|]. split; [|exact (crt5_alias_ok E i E52 E53 E55 H77 Hi0 Hil)].
  unfold crt5_factsH, crt5_condsH. cbn [f_conds].
  assert (Hnb3 : nb = 3 \/ nb = 2 \/ nb = 1) by lia.
  destruct Hnb3 as [-> | [-> | ->]]; cbn [Z.eqb Pos.eqb]; split; try split; try exact I.
  - exact (crt5_cond_ltu E 53 1 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (crt5_cond_ltu E 53 2 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (crt5_cond_ltu E 53 1 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (crt5_cond_geu E 53 2 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (crt5_cond_geu E 53 1 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact (crt5_cond_geu E 53 2 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (HS1 : st_ok tfibsegs E (crt5_ssH nb (crt5_factsH nb)) (restrict (w_H W) ms))
  by (apply (st_ok_facts tfibsegs E (crt5_ssH nb crt5_factsH0) _ (crt5_factsH nb) HS HF)).
pose proof (crt5_shok_H E (ms_mem ms) q i nb HM E76 E54 E55 Hi0 ltac:(lia) ltac:(lia) Hq1 Hq2) as SHOK.
assert (Hnb3 : nb = 3 \/ nb = 2 \/ nb = 1) by lia.
destruct Hnb3 as [Hnbv | [Hnbv | Hnbv]]; rewrite Hnbv in HS1, SHOK.
- fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81e8c.
  { apply (crt5_awr_H E q 3 E54 Hq1 Hq2). }
  pose proof (crt5_keepH E _ _ q 3 (crt5_factsH 3) HF0 E54 ltac:(lia) ltac:(lia)) as Hkeep.
  refine (crt5_toB regs0 E _ _ _ ms _ i q _ _ _ Q Hi0 Hil Hm3 Hq K _ _ _ HS1 _ _ _ _ HEAc HM HO
    (conj HJ HARU) Hkeep HG).
  + first [apply Hbyt | lia].
  + first [apply Hbyt | lia].
  + first [apply Hbyt | lia].
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H56 H57 H58 E82 E70 E71 E53 E53.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (Hz2 : nth (Z.to_nat (i + 2)) bs 0 = 0) by (apply crt5_nth_big; lia).
  rewrite Hz2 in H58, K.
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81e8c.
  { apply (crt5_awr_H E q 2 E54 Hq1 Hq2). }
  pose proof (crt5_keepH E _ _ q 2 (crt5_factsH 2) HF0 E54 ltac:(lia) ltac:(lia)) as Hkeep.
  refine (crt5_toB regs0 E _ _ _ ms _ i q _ _ _ Q Hi0 Hil Hm3 Hq K _ _ _ HS1 _ _ _ _ HEAc HM HO
    (conj HJ HARU) Hkeep HG).
  + first [apply Hbyt | lia].
  + first [apply Hbyt | lia].
  + first [apply Hbyt | lia].
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H56 H57 H58 E82 E70 E71 E53 E53.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (Hz1 : nth (Z.to_nat (i + 1)) bs 0 = 0) by (apply crt5_nth_big; lia).
  assert (Hz2 : nth (Z.to_nat (i + 2)) bs 0 = 0) by (apply crt5_nth_big; lia).
  rewrite Hz1 in H57, K. rewrite Hz2 in H58, K.
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81e8c.
  { apply (crt5_awr_H E q 1 E54 Hq1 Hq2). }
  pose proof (crt5_keepH E _ _ q 1 (crt5_factsH 1) HF0 E54 ltac:(lia) ltac:(lia)) as Hkeep.
  refine (crt5_toB regs0 E _ _ _ ms _ i q _ _ _ Q Hi0 Hil Hm3 Hq K _ _ _ HS1 _ _ _ _ HEAc HM HO
    (conj HJ HARU) Hkeep HG).
  + first [apply Hbyt | lia].
  + first [apply Hbyt | lia].
  + first [apply Hbyt | lia].
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H56 H57 H58 E82 E70 E71 E53 E53.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
Qed.

(* ================= phase B: 0x81e8c -> 0x81ef4, the first character is written ================= *)
Definition crt5_KC (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (i q c1 c2 v1 : Z)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall (E' : env) (ms' : machine_state) (mdc' : Model),
    st_ok tfibsegs E' (crt5_ssC crt5_factsC0) (restrict (w_H W) ms') ->
    (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
    crt5_EA E' regs0 i q -> ew E' 77 = Z_to_bv 64 (bd + 1) ->
    ew E' 78 = Z_to_bv 64 (i + 2) -> ew E' 79 = Z_to_bv 64 (i + 1) ->
    ew E' 57 = Z_to_bv 64 c1 -> ew E' 58 = Z_to_bv 64 c2 -> ew E' 59 = Z_to_bv 64 v1 ->
    crt5_memf (ms_mem ms') -> crt5_out (ms_mem ms') (Z.to_nat (i / 3 * 4) + 1) ->
    crt5_JR (ms_mem ms') mdc' ->
    (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms' x = ms_mem ms x) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr tfibsegs W (mkCfg ms' mdc') Q.
(* a character the engine stored, read back from the destination region of the state it reached *)
Lemma crt5_byte_at : forall E ss (ms : machine_state) q lo cs od e,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 54%nat) lo 4 lo 4 cs) ->
  In (YP09.mkChunk od (CVal 1 e)) cs -> ew E 54 = Z_to_bv 64 q -> 0 <= q < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (q + od) 1 (U E e mod 256).
Proof.
intros E ss ms q lo cs od e HS Hnth Hin H54 Hq.
pose proof (fsw_region_nth E ss (restrict (w_H W) ms) 0 _ HS Hnth) as HR.
cbn [ms_mem restrict] in HR.
apply (crt5_chunk_byte E (ms_mem ms) 54 q cs lo 4 lo 4 od e HR
  ltac:(rewrite H54; apply unsigned_lit_small; lia) Hin).
Qed.
Lemma crt5_byte0 : forall E ss (ms : machine_state) q e,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 54%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 1 e)]) ->
  ew E 54 = Z_to_bv 64 q -> 0 <= q < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) q 1 (U E e mod 256).
Proof.
intros E ss ms q e HS Hnth H54 Hq.
pose proof (crt5_byte_at E ss ms q 0 _ 0 e HS Hnth ltac:(cbn [In]; left; reflexivity) H54 Hq) as H.
rewrite Z.add_0_r in H. exact H.
Qed.
(* the character of a value the state carries as an atom with an offset *)
Lemma crt5_chr_off : forall E (n : nat) v k,
  ew E n = Z_to_bv 64 v -> 0 <= v <= 63 ->
  ((k = 65 /\ v <= 25) \/ (k = 71 /\ 26 <= v <= 51) \/ (k = 252 /\ 52 <= v <= 61)) ->
  U E (SOff n k) mod 256 = b64c v.
Proof.
intros E n v k Hn Hv Hk.
rewrite (crt5_U_off E n v k Hn ltac:(lia) ltac:(destruct Hk as [(->&_)|[(->&_)|(->&_)]]; lia)).
destruct Hk as [(-> & Hb)|[(-> & Hb)|(-> & Hb)]].
- apply crt5_b64cA. lia.
- apply crt5_b64cB. lia.
- apply crt5_b64cC. lia.
Qed.
Lemma crt5_out_step : forall (m : word -> option byte) (i q v : Z) (j : nat),
  0 <= i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> (j < 4)%nat ->
  crt5_out m (Z.to_nat (i / 3 * 4) + j) ->
  val_mem tfibsegs (mrestrict (w_H W) m) (q + Z.of_nat j) 1 v ->
  v = nth j (crt5_quad bs l i) 0 ->
  crt5_out m (Z.to_nat (i / 3 * 4) + S j).
Proof.
intros m i q v j Hi Hm3 Hq Hj HO Hv Heq jj Hjj.
destruct (Nat.eq_dec jj (Z.to_nat (i / 3 * 4) + j)) as [-> | Hne]; [|apply HO; lia].
rewrite (crt5_quad_nth bs l i j HLEN Hi Hm3 Hj), <- Heq.
replace (want + Z.of_nat (Z.to_nat (i / 3 * 4) + j)) with (q + Z.of_nat j) by (subst q; lia).
exact Hv.
Qed.

(* the character b64_char leaves for a value whose class the state carries *)
Lemma crt5_chr : forall E (n : nat) v k,
  ew E n = Z_to_bv 64 v -> 0 <= v <= 63 ->
  ((k = 65 /\ v <= 25) \/ (k = 71 /\ 26 <= v <= 51) \/ (k = 252 /\ 52 <= v <= 61)) ->
  U E (SAlu ALU_ADD (SOff n 0) (SLit k)) mod 256 = b64c v.
Proof.
intros E n v k Hn Hv Hk.
rewrite (crt5_U_addlit E (SOff n 0) k v (crt5_U_atom E n v Hn ltac:(lia)) ltac:(lia)
  ltac:(destruct Hk as [(->&_)|[(->&_)|(->&_)]]; lia) ltac:(destruct Hk as [(->&_)|[(->&_)|(->&_)]]; lia)).
destruct Hk as [(-> & Hb)|[(-> & Hb)|(-> & Hb)]].
- apply crt5_b64cA. lia.
- apply crt5_b64cB. lia.
- apply crt5_b64cC. lia.
Qed.
Lemma crt5_chr_sh : forall E c0 k,
  ew E 56 = Z_to_bv 64 c0 -> 0 <= c0 < 256 ->
  ((k = 65 /\ c0 <= 103) \/ (k = 71 /\ 104 <= c0 <= 207) \/ (k = 252 /\ 208 <= c0 <= 247)) ->
  U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 56 0) (SLit 2)) (SLit k)) mod 256 = b64c (c0 / 4).
Proof.
intros E c0 k Hn Hc Hk.
assert (Hs : U E (SAlu ALU_SRL (SOff 56 0) (SLit 2)) = c0 / 4) by (apply (crt5_sh2 E 56 c0 Hn Hc)).
rewrite (crt5_U_addlit E _ k (c0 / 4) Hs ltac:(Z.div_mod_to_equations; lia)
  ltac:(destruct Hk as [(->&_)|[(->&_)|(->&_)]]; lia)
  ltac:(destruct Hk as [(->&_)|[(->&_)|(->&_)]]; Z.div_mod_to_equations; lia)).
destruct Hk as [(-> & Hb)|[(-> & Hb)|(-> & Hb)]].
- apply crt5_b64cA. Z.div_mod_to_equations. lia.
- apply crt5_b64cB. Z.div_mod_to_equations. lia.
- apply crt5_b64cC. Z.div_mod_to_equations. lia.
Qed.

(* ---- the C boundary (B 0x81ef4): the second character's value is in t5 (A: s10) ---- *)
Definition crt5_mregsC (ms : machine_state) (regs0 : bvmap 5 word) (i q v1 c1 c2 : Z) : Prop :=
  YK11.getr (ms_regs ms) 20%bv = Z_to_bv 64 l /\ YK11.getr (ms_regs ms) 21%bv = Z_to_bv 64 bd /\
  YK11.getr (ms_regs ms) 13%bv = Z_to_bv 64 i /\ YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 31%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 15%bv = Z_to_bv 64 (bd + 1) /\
  YK11.getr (ms_regs ms) 12%bv = Z_to_bv 64 (i + 2) /\
  YK11.getr (ms_regs ms) 27%bv = Z_to_bv 64 (i + 1) /\
  YK11.getr (ms_regs ms) 30%bv = Z_to_bv 64 v1 /\ YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 c1 /\
  YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 c2 /\
  YK11.getr (ms_regs ms) 14%bv = Z_to_bv 64 (2 ^ 64 - 1 - bd) /\
  YK11.getr (ms_regs ms) 24%bv = YK11.getr regs0 24%bv /\
  YK11.getr (ms_regs ms) 25%bv = YK11.getr regs0 25%bv.
(* ---- the re-key from the first character's state to the second's ---- *)
Lemma crt5_toC : forall (regs0 : bvmap 5 word) (E E1 : env) (ss1 : sstate) (ms1 ms : machine_state)
    (mdc1 : Model) (i q c1 c2 v1 : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 ->
  crt5_KC regs0 E ms i q c1 c2 v1 Q ->
  0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= v1 <= 63 ->
  st_ok tfibsegs E1 ss1 (restrict (w_H W) ms1) -> ss_pc ss1 = 0x81ef4 ->
  reabs_check crt5_P ss1 crt5_regsC crt5_factsC0 = true ->
  crt5_mregsC ms1 regs0 i q v1 c1 c2 ->
  (forall n, (n < 51)%nat -> ew E1 n = ew E n) ->
  crt5_EA E regs0 i q ->
  crt5_memf (ms_mem ms1) -> crt5_out (ms_mem ms1) (Z.to_nat (i / 3 * 4) + 1) ->
  crt5_JR (ms_mem ms1) mdc1 ->
  (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms1 x = ms_mem ms x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) ->
  SRr tfibsegs W (mkCfg ms1 mdc1) Q.
Proof.
intros regs0 E E1 ss1 ms1 ms mdc1 i q c1 c2 v1 Q Hi0 Hil Hm3 Hq K Hb1 Hb2 Hbv HS Hpc Hck HR Hag HEA
  HM1 HO1 HJR Hkeep HG.
destruct HR as (R20 & R21 & R13 & R19 & R31 & R18 & R15 & R12 & R27 & R30 & R1 & R23 & R14 & R24 & R25).
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
assert (A51 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 51 = Z_to_bv 64 l) by reflexivity.
assert (A52 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 52 = Z_to_bv 64 bd) by reflexivity.
assert (A53 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 53 = Z_to_bv 64 i) by reflexivity.
assert (A54 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 54 = Z_to_bv 64 q) by reflexivity.
assert (A55 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 55 = Z_to_bv 64 (bd + i)) by reflexivity.
assert (A56 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 56 = Z_to_bv 64 0) by reflexivity.
assert (A57 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 57 = Z_to_bv 64 c1) by reflexivity.
assert (A58 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 58 = Z_to_bv 64 c2) by reflexivity.
assert (A59 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 59 = Z_to_bv 64 v1) by reflexivity.
assert (A60 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 60 = Z_to_bv 64 0) by reflexivity.
assert (A76 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 76 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (A77 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 77 = Z_to_bv 64 (bd + 1)) by reflexivity.
assert (A78 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 78 = Z_to_bv 64 (i + 2)) by reflexivity.
assert (A79 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 79 = Z_to_bv 64 (i + 1)) by reflexivity.
assert (A82 : ew (havoc E1 51 (crt5_vs ms1 i q 0 c1 c2 v1 0)) 82 = Z_to_bv 64 (2 ^ 64 - 1 - bd)) by reflexivity.
pose proof (crt5_rekey E1 ss1 ms1 crt5_regsC [crt5_want 1] crt5_factsC0
  (crt5_vs ms1 i q 0 c1 c2 v1 0) HS Hck ltac:(crt5_obl)
  ltac:(crt5_fobl A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A76 A77 A82)
  ltac:(split; [vm_compute; reflexivity|];
        split; [constructor; [apply (crt5_region_want _ (ms_mem ms1) q 1 HM1 A54 Hq1 Hq2 ltac:(lia))
                             | constructor]
               | cbn [pairwise_disjoint all_disjoint]; tauto])) as HS3.
rewrite Hpc in HS3.
apply (K _ ms1 _ HS3);
  [ intros n Hn; rewrite ew_havoc_old by lia; apply Hag; lia
  | unfold crt5_EA; repeat split;
      first [ exact A51 | exact A52 | exact A53 | exact A54 | exact A55 | exact A76
            | exact A82 | exact R24 | exact R25
            | rewrite ew_havoc_old by lia; rewrite Hag by lia; assumption ]
  | exact A77 | exact A78 | exact A79 | exact A57 | exact A58 | exact A59
  | exact HM1 | exact HO1 | exact HJR | exact Hkeep | exact HG ].
Qed.

(* ---- the D1 boundary: the third character's value and its multiple of 4 ---- *)
Definition crt5_mregsD (ms : machine_state) (regs0 : bvmap 5 word) (i q v tv c2 : Z) : Prop :=
  YK11.getr (ms_regs ms) 20%bv = Z_to_bv 64 l /\ YK11.getr (ms_regs ms) 21%bv = Z_to_bv 64 bd /\
  YK11.getr (ms_regs ms) 13%bv = Z_to_bv 64 i /\ YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 31%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 15%bv = Z_to_bv 64 (bd + 1) /\
  YK11.getr (ms_regs ms) 12%bv = Z_to_bv 64 (i + 2) /\
  YK11.getr (ms_regs ms) 11%bv = Z_to_bv 64 v /\ YK11.getr (ms_regs ms) 30%bv = Z_to_bv 64 tv /\
  YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 c2 /\
  YK11.getr (ms_regs ms) 14%bv = Z_to_bv 64 (2 ^ 64 - 1 - bd) /\
  YK11.getr (ms_regs ms) 24%bv = YK11.getr regs0 24%bv /\
  YK11.getr (ms_regs ms) 25%bv = YK11.getr regs0 25%bv.
Definition crt5_KD (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (i q c2 v2 tv : Z)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall (E' : env) (ms' : machine_state) (mdc' : Model),
    st_ok tfibsegs E' (crt5_ssD1 crt5_factsD10) (restrict (w_H W) ms') ->
    (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
    crt5_EA E' regs0 i q -> ew E' 77 = Z_to_bv 64 (bd + 1) ->
    ew E' 78 = Z_to_bv 64 (i + 2) -> ew E' 79 = Z_to_bv 64 (i + 1) ->
    ew E' 58 = Z_to_bv 64 c2 -> ew E' 59 = Z_to_bv 64 v2 -> ew E' 60 = Z_to_bv 64 tv ->
    crt5_memf (ms_mem ms') -> crt5_out (ms_mem ms') (Z.to_nat (i / 3 * 4) + 2) ->
    crt5_JR (ms_mem ms') mdc' ->
    (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms' x = ms_mem ms x) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr tfibsegs W (mkCfg ms' mdc') Q.
Lemma crt5_toD1 : forall (regs0 : bvmap 5 word) (E E1 : env) (ss1 : sstate) (ms1 ms : machine_state)
    (mdc1 : Model) (i q c2 v2 tv : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 ->
  crt5_KD regs0 E ms i q c2 v2 tv Q ->
  0 <= c2 < 256 -> 0 <= v2 <= 63 -> 0 <= tv <= 63 ->
  st_ok tfibsegs E1 ss1 (restrict (w_H W) ms1) -> ss_pc ss1 = 0x81f60 ->
  reabs_check crt5_PQ ss1 crt5_regsD1 crt5_factsD10 = true ->
  crt5_mregsD ms1 regs0 i q v2 tv c2 ->
  (forall n, (n < 51)%nat \/ n = 54%nat -> ew E1 n = ew E n) ->
  crt5_EA E regs0 i q ->
  crt5_memf (ms_mem ms1) -> crt5_out (ms_mem ms1) (Z.to_nat (i / 3 * 4) + 2) ->
  crt5_JR (ms_mem ms1) mdc1 ->
  (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms1 x = ms_mem ms x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) ->
  SRr tfibsegs W (mkCfg ms1 mdc1) Q.
Proof.
intros regs0 E E1 ss1 ms1 ms mdc1 i q c2 v2 tv Q Hi0 Hil Hm3 Hq K Hb2 Hbv Hbt HS Hpc Hck HR Hag HEA
  HM1 HO1 HJR Hkeep HG.
destruct HR as (R20 & R21 & R13 & R19 & R31 & R18 & R15 & R12 & R11 & R30 & R23 & R14 & R24 & R25).
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
assert (A51 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 51 = Z_to_bv 64 l) by reflexivity.
assert (A52 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 52 = Z_to_bv 64 bd) by reflexivity.
assert (A53 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 53 = Z_to_bv 64 i) by reflexivity.
assert (A54 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 54 = Z_to_bv 64 q) by reflexivity.
assert (A55 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 55 = Z_to_bv 64 (bd + i)) by reflexivity.
assert (A56 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 56 = Z_to_bv 64 0) by reflexivity.
assert (A57 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 57 = Z_to_bv 64 0) by reflexivity.
assert (A58 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 58 = Z_to_bv 64 c2) by reflexivity.
assert (A59 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 59 = Z_to_bv 64 v2) by reflexivity.
assert (A60 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 60 = Z_to_bv 64 tv) by reflexivity.
assert (A76 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 76 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (A77 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 77 = Z_to_bv 64 (bd + 1)) by reflexivity.
assert (A78 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 78 = Z_to_bv 64 (i + 2)) by reflexivity.
assert (A79 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 79 = Z_to_bv 64 (i + 1)) by reflexivity.
assert (A82 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v2 tv)) 82 = Z_to_bv 64 (2 ^ 64 - 1 - bd)) by reflexivity.
assert (H54Q : nth 3 (crt5_vs ms1 i q 0 0 c2 v2 tv) (ew E1 54) = ew E1 54)
  by (cbn [crt5_vs nth]; rewrite (Hag 54%nat ltac:(lia)); symmetry; exact E54).
pose proof (crt5_rekeyQ E1 ss1 ms1 crt5_regsD1 [crt5_want 2] crt5_factsD10
  (crt5_vs ms1 i q 0 0 c2 v2 tv) H54Q HS Hck ltac:(crt5_obl)
  ltac:(crt5_fobl A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A76 A77 A82)
  ltac:(split; [vm_compute; reflexivity|];
        split; [constructor; [apply (crt5_region_want _ (ms_mem ms1) q 2 HM1 A54 Hq1 Hq2 ltac:(lia))
                             | constructor]
               | cbn [pairwise_disjoint all_disjoint]; tauto])) as HS3.
rewrite Hpc in HS3.
apply (K _ ms1 _ HS3);
  [ intros n Hn; rewrite ew_havoc_old by lia; apply Hag; lia
  | unfold crt5_EA; repeat split;
      first [ exact A51 | exact A52 | exact A53 | exact A54 | exact A55 | exact A76
            | exact A82 | exact R24 | exact R25
            | rewrite ew_havoc_old by lia; rewrite Hag by lia; assumption ]
  | exact A77 | exact A78 | exact A79 | exact A58 | exact A59 | exact A60
  | exact HM1 | exact HO1 | exact HJR | exact Hkeep | exact HG ].
Qed.

(* ---- the E1 boundary: the fourth character's value ---- *)
Definition crt5_mregsE (ms : machine_state) (regs0 : bvmap 5 word) (i q v c2 : Z) : Prop :=
  YK11.getr (ms_regs ms) 20%bv = Z_to_bv 64 l /\ YK11.getr (ms_regs ms) 21%bv = Z_to_bv 64 bd /\
  YK11.getr (ms_regs ms) 13%bv = Z_to_bv 64 i /\ YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 31%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 15%bv = Z_to_bv 64 (bd + 1) /\
  YK11.getr (ms_regs ms) 12%bv = Z_to_bv 64 (i + 2) /\
  YK11.getr (ms_regs ms) 11%bv = Z_to_bv 64 v /\
  YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 c2 /\
  YK11.getr (ms_regs ms) 14%bv = Z_to_bv 64 (2 ^ 64 - 1 - bd) /\
  YK11.getr (ms_regs ms) 24%bv = YK11.getr regs0 24%bv /\
  YK11.getr (ms_regs ms) 25%bv = YK11.getr regs0 25%bv.
Definition crt5_KE (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (i q c2 v3 : Z)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall (E' : env) (ms' : machine_state) (mdc' : Model),
    st_ok tfibsegs E' (crt5_ssE1 crt5_factsE10) (restrict (w_H W) ms') ->
    (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
    crt5_EA E' regs0 i q -> ew E' 77 = Z_to_bv 64 (bd + 1) ->
    ew E' 78 = Z_to_bv 64 (i + 2) -> ew E' 79 = Z_to_bv 64 (i + 1) ->
    ew E' 58 = Z_to_bv 64 c2 -> ew E' 59 = Z_to_bv 64 v3 ->
    crt5_memf (ms_mem ms') -> crt5_out (ms_mem ms') (Z.to_nat (i / 3 * 4) + 3) ->
    crt5_JR (ms_mem ms') mdc' ->
    (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms' x = ms_mem ms x) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr tfibsegs W (mkCfg ms' mdc') Q.
Lemma crt5_toE1 : forall (regs0 : bvmap 5 word) (E E1 : env) (ss1 : sstate) (ms1 ms : machine_state)
    (mdc1 : Model) (i q c2 v3 : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 ->
  crt5_KE regs0 E ms i q c2 v3 Q ->
  0 <= c2 < 256 -> 0 <= v3 <= 63 ->
  st_ok tfibsegs E1 ss1 (restrict (w_H W) ms1) -> ss_pc ss1 = 0x81f98 ->
  reabs_check crt5_PQ ss1 crt5_regsE1 crt5_factsE10 = true ->
  crt5_mregsE ms1 regs0 i q v3 c2 ->
  (forall n, (n < 51)%nat \/ n = 54%nat -> ew E1 n = ew E n) ->
  crt5_EA E regs0 i q ->
  crt5_memf (ms_mem ms1) -> crt5_out (ms_mem ms1) (Z.to_nat (i / 3 * 4) + 3) ->
  crt5_JR (ms_mem ms1) mdc1 ->
  (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms1 x = ms_mem ms x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) ->
  SRr tfibsegs W (mkCfg ms1 mdc1) Q.
Proof.
intros regs0 E E1 ss1 ms1 ms mdc1 i q c2 v3 Q Hi0 Hil Hm3 Hq K Hb2 Hbv HS Hpc Hck HR Hag HEA
  HM1 HO1 HJR Hkeep HG.
destruct HR as (R20 & R21 & R13 & R19 & R31 & R18 & R15 & R12 & R11 & R23 & R14 & R24 & R25).
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
assert (A51 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 51 = Z_to_bv 64 l) by reflexivity.
assert (A52 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 52 = Z_to_bv 64 bd) by reflexivity.
assert (A53 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 53 = Z_to_bv 64 i) by reflexivity.
assert (A54 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 54 = Z_to_bv 64 q) by reflexivity.
assert (A55 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 55 = Z_to_bv 64 (bd + i)) by reflexivity.
assert (A56 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 56 = Z_to_bv 64 0) by reflexivity.
assert (A57 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 57 = Z_to_bv 64 0) by reflexivity.
assert (A58 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 58 = Z_to_bv 64 c2) by reflexivity.
assert (A59 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 59 = Z_to_bv 64 v3) by reflexivity.
assert (A60 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 60 = Z_to_bv 64 0) by reflexivity.
assert (A76 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 76 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (A77 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 77 = Z_to_bv 64 (bd + 1)) by reflexivity.
assert (A78 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 78 = Z_to_bv 64 (i + 2)) by reflexivity.
assert (A79 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 79 = Z_to_bv 64 (i + 1)) by reflexivity.
assert (A82 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 c2 v3 0)) 82 = Z_to_bv 64 (2 ^ 64 - 1 - bd)) by reflexivity.
assert (H54Q : nth 3 (crt5_vs ms1 i q 0 0 c2 v3 0) (ew E1 54) = ew E1 54)
  by (cbn [crt5_vs nth]; rewrite (Hag 54%nat ltac:(lia)); symmetry; exact E54).
pose proof (crt5_rekeyQ E1 ss1 ms1 crt5_regsE1 [crt5_want 3] crt5_factsE10
  (crt5_vs ms1 i q 0 0 c2 v3 0) H54Q HS Hck ltac:(crt5_obl)
  ltac:(crt5_fobl A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A76 A77 A82)
  ltac:(split; [vm_compute; reflexivity|];
        split; [constructor; [apply (crt5_region_want _ (ms_mem ms1) q 3 HM1 A54 Hq1 Hq2 ltac:(lia))
                             | constructor]
               | cbn [pairwise_disjoint all_disjoint]; tauto])) as HS3.
rewrite Hpc in HS3.
apply (K _ ms1 _ HS3);
  [ intros n Hn; rewrite ew_havoc_old by lia; apply Hag; lia
  | unfold crt5_EA; repeat split;
      first [ exact A51 | exact A52 | exact A53 | exact A54 | exact A55 | exact A76
            | exact A82 | exact R24 | exact R25
            | rewrite ew_havoc_old by lia; rewrite Hag by lia; assumption ]
  | exact A77 | exact A78 | exact A79 | exact A58 | exact A59
  | exact HM1 | exact HO1 | exact HJR | exact Hkeep | exact HG ].
Qed.

(* ---- the head boundary: the trip's own state at 0x81e18, re-keyed for the next trip ---- *)
Lemma crt5_region_body : forall E (m : word -> option byte) i nb,
  garr8 tfibsegs (mrestrict (w_H W) m) bd bs ->
  ew E 55 = Z_to_bv 64 (bd + i) ->
  ew E 56 = Z_to_bv 64 (nth (Z.to_nat i) bs 0) ->
  ew E 57 = Z_to_bv 64 (nth (Z.to_nat (i + 1)) bs 0) ->
  ew E 58 = Z_to_bv 64 (nth (Z.to_nat (i + 2)) bs 0) ->
  0 <= i -> i + nb <= l -> 1 <= nb <= 3 ->
  region_ok tfibsegs E (mrestrict (w_H W) m) (crt5_body nb).
Proof.
intros E m i nb HG H55 H56 H57 H58 Hi0 Hin Hnb.
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _). destruct HBD as [HD1 HD2].
unfold region_ok, crt5_body. cbv zeta.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H55, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
assert (Hnb3 : nb = 3 \/ nb = 2 \/ nb = 1) by lia.
assert (C0 : ew E (56 + 0)%nat = Z_to_bv 64 (nth (Z.to_nat i + 0) bs 0))
  by (rewrite Nat.add_0_r, Nat.add_0_r; exact H56).
assert (C1 : ew E (56 + 1)%nat = Z_to_bv 64 (nth (Z.to_nat i + 1) bs 0))
  by (replace (Z.to_nat i + 1)%nat with (Z.to_nat (i + 1)) by lia; exact H57).
assert (C2 : ew E (56 + 2)%nat = Z_to_bv 64 (nth (Z.to_nat i + 2) bs 0))
  by (replace (Z.to_nat i + 2)%nat with (Z.to_nat (i + 2)) by lia; exact H58).
destruct Hnb3 as [-> | [-> | ->]];
  [ replace (Z.to_nat 3) with 3%nat by reflexivity
  | replace (Z.to_nat 2) with 2%nat by reflexivity
  | replace (Z.to_nat 1) with 1%nat by reflexivity ];
  cbn [seq map].
- apply Forall_cons; [exact (crt5_chunk_body E m i 0 HG H55 C0 Hi0 ltac:(lia))|].
  apply Forall_cons; [exact (crt5_chunk_body E m i 1 HG H55 C1 Hi0 ltac:(lia))|].
  apply Forall_cons; [exact (crt5_chunk_body E m i 2 HG H55 C2 Hi0 ltac:(lia))|].
  apply Forall_nil.
- apply Forall_cons; [exact (crt5_chunk_body E m i 0 HG H55 C0 Hi0 ltac:(lia))|].
  apply Forall_cons; [exact (crt5_chunk_body E m i 1 HG H55 C1 Hi0 ltac:(lia))|].
  apply Forall_nil.
- apply Forall_cons; [exact (crt5_chunk_body E m i 0 HG H55 C0 Hi0 ltac:(lia))|].
  apply Forall_nil.
Qed.

Definition crt5_mregsH (ms : machine_state) (regs0 : bvmap 5 word) (i q : Z) : Prop :=
  YK11.getr (ms_regs ms) 20%bv = Z_to_bv 64 l /\ YK11.getr (ms_regs ms) 21%bv = Z_to_bv 64 bd /\
  YK11.getr (ms_regs ms) 13%bv = Z_to_bv 64 i /\ YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 31%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 15%bv = Z_to_bv 64 (bd + 1) /\
  YK11.getr (ms_regs ms) 14%bv = Z_to_bv 64 (2 ^ 64 - 1 - bd) /\
  YK11.getr (ms_regs ms) 24%bv = YK11.getr regs0 24%bv /\
  YK11.getr (ms_regs ms) 25%bv = YK11.getr regs0 25%bv.
(* what the walk holds at a head, as one predicate: the induction's invariant *)
Definition crt5_head_at (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model) (i : Z) : Prop :=
  st_ok tfibsegs E (crt5_ssH (Z.min 3 (l - i)) crt5_factsH0) (restrict (w_H W) ms) /\
  crt5_EA E regs0 i (want + i / 3 * 4) /\ ew E 77 = Z_to_bv 64 (bd + 1) /\
  ew E 56 = Z_to_bv 64 (nth (Z.to_nat i) bs 0) /\
  ew E 57 = Z_to_bv 64 (nth (Z.to_nat (i + 1)) bs 0) /\
  ew E 58 = Z_to_bv 64 (nth (Z.to_nat (i + 2)) bs 0) /\
  crt5_memf (ms_mem ms) /\ crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4)) /\ crt5_JR (ms_mem ms) mdc /\
  0 <= i /\ i < l /\ i mod 3 = 0.
Lemma crt5_toHead : forall (regs0 : bvmap 5 word) (E E1 : env) (ss1 : sstate) (ms1 : machine_state)
    (mdc1 : Model) (i q nb : Z),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> nb = Z.min 3 (l - i) ->
  st_ok tfibsegs E1 ss1 (restrict (w_H W) ms1) -> ss_pc ss1 = 0x81e18 ->
  reabs_check crt5_P ss1 crt5_regsH crt5_factsH0 = true ->
  crt5_mregsH ms1 regs0 i q ->
  (forall n, (n < 51)%nat -> ew E1 n = ew E n) ->
  crt5_EA_low E regs0 ->
  crt5_memf (ms_mem ms1) -> crt5_out (ms_mem ms1) (Z.to_nat (i / 3 * 4)) ->
  crt5_JR (ms_mem ms1) mdc1 ->
  exists E', crt5_head_at regs0 E' ms1 mdc1 i /\ (forall n, (n < 51)%nat -> ew E' n = ew E n).
Proof.
intros regs0 E E1 ss1 ms1 mdc1 i q nb Hi0 Hil Hm3 Hq Hnb HS Hpc Hck HR Hag HEAl HM1 HO1 HJR.
assert (Hnb3 : nb = 3 \/ nb = 2 \/ nb = 1) by lia.
destruct HR as (R20 & R21 & R13 & R19 & R31 & R18 & R15 & R14 & R24 & R25).
destruct HEAl as (Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E70 & E71).
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
assert (Hbyt : forall j, 0 <= nth j bs 0 < 256).
{ intros j. destruct (Nat.lt_ge_cases j (length bs)) as [Hj | Hj].
  - destruct HM1 as (HG0 & _). exact (proj2 (HG0 j Hj)).
  - rewrite crt5_nth_big by lia. lia. }
assert (Hb0 : 0 <= nth (Z.to_nat i) bs 0 < 256) by apply Hbyt.
assert (Hb1 : 0 <= nth (Z.to_nat (i + 1)) bs 0 < 256) by apply Hbyt.
assert (Hb2 : 0 <= nth (Z.to_nat (i + 2)) bs 0 < 256) by apply Hbyt.
set (c0 := nth (Z.to_nat i) bs 0) in *. set (c1 := nth (Z.to_nat (i + 1)) bs 0) in *.
set (c2 := nth (Z.to_nat (i + 2)) bs 0) in *.
assert (A51 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 51 = Z_to_bv 64 l) by reflexivity.
assert (A52 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 52 = Z_to_bv 64 bd) by reflexivity.
assert (A53 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 53 = Z_to_bv 64 i) by reflexivity.
assert (A54 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 54 = Z_to_bv 64 q) by reflexivity.
assert (A55 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 55 = Z_to_bv 64 (bd + i)) by reflexivity.
assert (A56 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 56 = Z_to_bv 64 c0) by reflexivity.
assert (A57 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 57 = Z_to_bv 64 c1) by reflexivity.
assert (A58 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 58 = Z_to_bv 64 c2) by reflexivity.
assert (A59 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 59 = Z_to_bv 64 0) by reflexivity.
assert (A60 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 60 = Z_to_bv 64 0) by reflexivity.
assert (A76 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 76 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (A77 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 77 = Z_to_bv 64 (bd + 1)) by reflexivity.
assert (A82 : ew (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)) 82 = Z_to_bv 64 (2 ^ 64 - 1 - bd)) by reflexivity.
pose proof (crt5_rekey E1 ss1 ms1 crt5_regsH [crt5_body nb; crt5_want 0] crt5_factsH0
  (crt5_vs ms1 i q c0 c1 c2 0 0) HS Hck ltac:(crt5_obl)
  ltac:(crt5_fobl A51 A52 A53 A54 A55 A56 A57 A58 A59 A60 A76 A77 A82)
  ltac:(split; [destruct Hnb3 as [-> | [-> | ->]]; vm_compute; reflexivity|];
        split;
        [ apply Forall_cons;
          [ apply (crt5_region_body _ (ms_mem ms1) i nb (proj1 HM1) A55 A56 A57 A58
                     ltac:(lia) ltac:(lia) ltac:(lia))
          | apply Forall_cons;
            [ apply (crt5_region_want _ (ms_mem ms1) q 0 HM1 A54 Hq1 Hq2 ltac:(lia)) | apply Forall_nil ] ]
        | cbn [pairwise_disjoint all_disjoint];
          split; [split; [|exact I] | split; [exact I | exact I]];
          unfold extent_disjoint, crt5_body, crt5_want;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite A55, A54, !unsigned_lit_small by lia;
          destruct HDJ as [HJ1 | HJ2]; [right | left]; lia ])) as HS3.
rewrite Hpc in HS3.
exists (havoc E1 51 (crt5_vs ms1 i q c0 c1 c2 0 0)).
split; [|intros n Hn; rewrite ew_havoc_old by lia; apply Hag; lia].
unfold crt5_head_at. rewrite <- Hnb. split; [exact HS3|].
split; [ unfold crt5_EA; repeat split;
         first [ exact A51 | exact A52 | exact A53 | rewrite A54; rewrite Hq; reflexivity | exact A55
               | exact A76 | exact A82 | exact R24 | exact R25
               | rewrite ew_havoc_old by lia; rewrite Hag by lia; assumption ] |].
split; [exact A77|]. split; [exact A56|]. split; [exact A57|]. split; [exact A58|].
split; [exact HM1|]. split; [exact HO1|]. split; [exact HJR|].
repeat split; assumption.
Qed.

(* ---- the exit boundary 0x82098: registers only, no region ---- *)
Definition crt5_mregsO (ms : machine_state) (regs0 : bvmap 5 word) (i q : Z) : Prop :=
  YK11.getr (ms_regs ms) 20%bv = Z_to_bv 64 l /\ YK11.getr (ms_regs ms) 21%bv = Z_to_bv 64 bd /\
  YK11.getr (ms_regs ms) 13%bv = Z_to_bv 64 (i + 3) /\
  YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 (q + 4) /\
  YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 (q + 4) /\
  YK11.getr (ms_regs ms) 22%bv = Z_to_bv 64 (q + 4) /\
  YK11.getr (ms_regs ms) 31%bv = Z_to_bv 64 q /\
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 15%bv = Z_to_bv 64 (bd + 1) /\
  YK11.getr (ms_regs ms) 14%bv = Z_to_bv 64 (2 ^ 64 - 1 - bd) /\
  YK11.getr (ms_regs ms) 24%bv = YK11.getr regs0 24%bv /\
  YK11.getr (ms_regs ms) 25%bv = YK11.getr regs0 25%bv.
(* what the loop hands to the next segment at 0x82098 (B: a0 = s3 = s6 = q + 4 after `addi a0, t6, 4` 0x82094;
   t6 = q, the last group's store base; A: a0 = a2 = q + 4, t4 = q) *)
Definition crt5_exit_at (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model) (i q : Z) : Prop :=
  st_ok tfibsegs E crt5_ssOut (restrict (w_H W) ms) /\ crt5_EA_low E regs0 /\
  ew E 76 = Z_to_bv 64 SHADOW_OFF /\ ew E 51 = Z_to_bv 64 l /\ ew E 52 = Z_to_bv 64 bd /\
  ew E 77 = Z_to_bv 64 (bd + 1) /\ ew E 80 = Z_to_bv 64 (q + 4) /\ ew E 81 = Z_to_bv 64 (i + 3) /\
  ew E 54 = Z_to_bv 64 q /\
  crt5_memf (ms_mem ms) /\ crt5_out (ms_mem ms) (Z.to_nat En) /\ crt5_JR (ms_mem ms) mdc /\
  crt5_mregsO ms regs0 i q /\ 0 <= i /\ i < l /\ i mod 3 = 0 /\ l <= i + 3 /\ q = want + i / 3 * 4.
Definition crt5_KX (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (i q : Z)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall (E' : env) (ms' : machine_state) (mdc' : Model),
    crt5_exit_at regs0 E' ms' mdc' i q ->
    (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
    (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms' x = ms_mem ms x) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr tfibsegs W (mkCfg ms' mdc') Q.
Lemma crt5_toOut : forall (regs0 : bvmap 5 word) (E E1 : env) (ss1 : sstate) (ms1 : machine_state)
    (mdc1 : Model) (i q : Z),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> l <= i + 3 ->
  st_ok tfibsegs E1 ss1 (restrict (w_H W) ms1) -> ss_pc ss1 = 0x82098 ->
  reabs_check crt5_P ss1 crt5_regsOut crt5_factsOut = true ->
  crt5_mregsO ms1 regs0 i q ->
  (forall n, (n < 51)%nat -> ew E1 n = ew E n) ->
  crt5_EA_low E regs0 ->
  crt5_memf (ms_mem ms1) -> crt5_out (ms_mem ms1) (Z.to_nat (i / 3 * 4) + 4) ->
  crt5_JR (ms_mem ms1) mdc1 ->
  exists E', crt5_exit_at regs0 E' ms1 mdc1 i q /\ (forall n, (n < 51)%nat -> ew E' n = ew E n).
Proof.
intros regs0 E E1 ss1 ms1 mdc1 i q Hi0 Hil Hm3 Hq Hlast HS Hpc Hck HR Hag HEAl HM1 HO1 HJR.
pose proof HR as HRc.
destruct HR as (R20 & R21 & R13 & R10 & R19 & R22 & R31 & R18 & R15 & R14 & R24 & R25).
destruct HEAl as (Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E70 & E71).
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
assert (HEnd : q + 4 = want + En) by (subst q; rewrite HEN; Z.div_mod_to_equations; lia).
assert (A51 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 51 = Z_to_bv 64 l) by reflexivity.
assert (A52 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 52 = Z_to_bv 64 bd) by reflexivity.
assert (A53 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 53 = Z_to_bv 64 i) by reflexivity.
assert (A54 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 54 = Z_to_bv 64 q) by reflexivity.
assert (A55 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 55 = Z_to_bv 64 (bd + i)) by reflexivity.
assert (A56 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 56 = Z_to_bv 64 0) by reflexivity.
assert (A57 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 57 = Z_to_bv 64 0) by reflexivity.
assert (A58 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 58 = Z_to_bv 64 0) by reflexivity.
assert (A59 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 59 = Z_to_bv 64 0) by reflexivity.
assert (A60 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 60 = Z_to_bv 64 0) by reflexivity.
assert (A76 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 76 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (A77 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 77 = Z_to_bv 64 (bd + 1)) by reflexivity.
assert (A80 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 80 = Z_to_bv 64 (q + 4)) by reflexivity.
assert (A81 : ew (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)) 81 = Z_to_bv 64 (i + 3)) by reflexivity.
pose proof (crt5_rekey E1 ss1 ms1 crt5_regsOut [] crt5_factsOut
  (crt5_vs ms1 i q 0 0 0 0 0) HS Hck ltac:(crt5_obl)
  ltac:(apply Forall_forall; intros nf Hin; vm_compute in Hin;
        repeat (destruct Hin as [<-|Hin];
          [cbn [fst snd]; unfold afact_ok; cbn [af_lo af_hi af_al2];
           rewrite ?A51, ?A52, ?A76, ?A80, ?A81;
           rewrite ?Z.pow_0_r, ?Z.mod_1_r;
           rewrite unsigned_lit_small by (unfold SHADOW_OFF, CRT5_CEIL in *; lia);
           unfold SHADOW_OFF, CRT5_CEIL in *; lia |]);
        destruct Hin)
  ltac:(split; [vm_compute; reflexivity|]; split; [apply Forall_nil | exact I])) as HS3.
rewrite Hpc in HS3.
exists (havoc E1 51 (crt5_vs ms1 i q 0 0 0 0 0)).
split; [|intros n Hn; rewrite ew_havoc_old by lia; apply Hag; lia].
unfold crt5_exit_at. split; [exact HS3|].
split; [ unfold crt5_EA_low; repeat split;
         first [ exact R24 | exact R25
               | rewrite ew_havoc_old by lia; rewrite Hag by lia; assumption ] |].
split; [exact A76|]. split; [exact A51|]. split; [exact A52|]. split; [exact A77|].
split; [exact A80|]. split; [exact A81|]. split; [exact A54|].
split; [exact HM1|].
split; [ replace (Z.to_nat En) with (Z.to_nat (i / 3 * 4) + 4)%nat
           by (rewrite HEN; Z.div_mod_to_equations; lia); exact HO1 |].
split; [exact HJR|].
split; [exact HRc|]. repeat split; assumption.
Qed.

(* ---- a trip that ends on the back edge: the walk is at the next head ---- *)
Definition crt5_KH (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (i q : Z)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall (E' : env) (ms' : machine_state) (mdc' : Model),
    crt5_head_at regs0 E' ms' mdc' (i + 3) ->
    (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
    (forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem ms' x = ms_mem ms x) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr tfibsegs W (mkCfg ms' mdc') Q.
Lemma crt5_phE_more : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
  (i q c2 v3 : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> i + 2 < l -> i + 3 < l ->
  crt5_KH regs0 E ms i q Q ->
  c2 = nth (Z.to_nat (i + 2)) bs 0 -> v3 = c2 mod 64 -> 0 <= c2 < 256 ->
  st_ok tfibsegs E (crt5_ssE1 crt5_factsE10) (restrict (w_H W) ms) ->
  crt5_EA E regs0 i q -> ew E 77 = Z_to_bv 64 (bd + 1) ->
  ew E 78 = Z_to_bv 64 (i + 2) -> ew E 79 = Z_to_bv 64 (i + 1) ->
  ew E 58 = Z_to_bv 64 c2 -> ew E 59 = Z_to_bv 64 v3 ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4) + 3) -> crt5_JR (ms_mem ms) mdc ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i q c2 v3 Q Hi0 Hil Hm3 Hq Hi2 Hi3 K Hc2 Hv3 Hb2 HS HEA H77 H78 H79 H58 H59
  HM HO HJR.
pose proof HEA as HEAc.
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
destruct HJR as [HJ HARU].
pose proof asan_consts as ((Hc1b & Hc2b) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
pose proof (crt5_shok_w E (ms_mem ms) q 3 HM E76 E54 ltac:(lia) Hq1 Hq2) as SHOK.
assert (Hbv : 0 <= v3 <= 63) by (subst v3; Z.div_mod_to_equations; lia).
assert (Hcls : (0 <= v3 <= 25) \/ (26 <= v3 <= 51) \/ (52 <= v3 <= 61) \/ (v3 = 62) \/ (v3 = 63)) by lia.
destruct Hcls as [Hcl | [Hcl | [Hcl | [Hcl | Hcl]]]].
- assert (HFE : facts_ok E (crt5_factsE1 0 25 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 app]. split; [|exact I].
       exact (crt5_cond_ltu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 0 25 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81e18.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { rewrite <- (crt5_chr_off _ 59 v3 65 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  assert (HO4 : crt5_out (ms_mem msN) (Z.to_nat ((i + 3) / 3 * 4)))
    by (replace (Z.to_nat ((i + 3) / 3 * 4)) with (Z.to_nat (i / 3 * 4) + 4)%nat
          by (Z.div_mod_to_equations; lia); exact HO1).
  destruct (crt5_toHead regs0 E _ _ msN _ (i + 3) (q + 4) (Z.min 3 (l - (i + 3)))
    ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)
    ltac:(subst q; Z.div_mod_to_equations; lia) eq_refl HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO4 (conj HJ HARU)) as (E' & HHead & Hag').
  exact (K E' msN _ HHead Hag' Hkeep HG).
- assert (HFE : facts_ok E (crt5_factsE1 26 51 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 app]. split; [|exact I].
       exact (crt5_cond_ltu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 26 51 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81e18.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { rewrite <- (crt5_chr_off _ 59 v3 71 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  assert (HO4 : crt5_out (ms_mem msN) (Z.to_nat ((i + 3) / 3 * 4)))
    by (replace (Z.to_nat ((i + 3) / 3 * 4)) with (Z.to_nat (i / 3 * 4) + 4)%nat
          by (Z.div_mod_to_equations; lia); exact HO1).
  destruct (crt5_toHead regs0 E _ _ msN _ (i + 3) (q + 4) (Z.min 3 (l - (i + 3)))
    ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)
    ltac:(subst q; Z.div_mod_to_equations; lia) eq_refl HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO4 (conj HJ HARU)) as (E' & HHead & Hag').
  exact (K E' msN _ HHead Hag' Hkeep HG).
- assert (HFE : facts_ok E (crt5_factsE1 52 61 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 app]. split; [|exact I].
       exact (crt5_cond_ltu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 52 61 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81e18.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { rewrite <- (crt5_chr_off _ 59 v3 252 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  assert (HO4 : crt5_out (ms_mem msN) (Z.to_nat ((i + 3) / 3 * 4)))
    by (replace (Z.to_nat ((i + 3) / 3 * 4)) with (Z.to_nat (i / 3 * 4) + 4)%nat
          by (Z.div_mod_to_equations; lia); exact HO1).
  destruct (crt5_toHead regs0 E _ _ msN _ (i + 3) (q + 4) (Z.min 3 (l - (i + 3)))
    ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)
    ltac:(subst q; Z.div_mod_to_equations; lia) eq_refl HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO4 (conj HJ HARU)) as (E' & HHead & Hag').
  exact (K E' msN _ HHead Hag' Hkeep HG).
- assert (HFE : facts_ok E (crt5_factsE1 62 62 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 crt5_eq62 app]. split; [|split; [|exact I]].
       - unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
         assert (Hd : sv_denot E (SOff 59 0) = sv_denot E (SLit 62)).
         { apply U_inj. rewrite (crt5_U_atom E 59 v3 H59 ltac:(lia)), (crt5_U_lit E 62 ltac:(lia)). lia. }
         rewrite Hd. apply bv_eqb_refl.
       - exact (crt5_cond_ltu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 62 62 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81e18.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 43) mod 256 = b64c v3) by
         (rewrite (crt5_U_lit e 43 ltac:(lia)); replace v3 with 62 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  assert (HO4 : crt5_out (ms_mem msN) (Z.to_nat ((i + 3) / 3 * 4)))
    by (replace (Z.to_nat ((i + 3) / 3 * 4)) with (Z.to_nat (i / 3 * 4) + 4)%nat
          by (Z.div_mod_to_equations; lia); exact HO1).
  destruct (crt5_toHead regs0 E _ _ msN _ (i + 3) (q + 4) (Z.min 3 (l - (i + 3)))
    ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)
    ltac:(subst q; Z.div_mod_to_equations; lia) eq_refl HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO4 (conj HJ HARU)) as (E' & HHead & Hag').
  exact (K E' msN _ HHead Hag' Hkeep HG).
- assert (HFE : facts_ok E (crt5_factsE1 63 63 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 app]. split; [|exact I].
       exact (crt5_cond_ltu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 63 63 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81e18.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 47) mod 256 = b64c v3) by
         (rewrite (crt5_U_lit e 47 ltac:(lia)); replace v3 with 63 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  assert (HO4 : crt5_out (ms_mem msN) (Z.to_nat ((i + 3) / 3 * 4)))
    by (replace (Z.to_nat ((i + 3) / 3 * 4)) with (Z.to_nat (i / 3 * 4) + 4)%nat
          by (Z.div_mod_to_equations; lia); exact HO1).
  destruct (crt5_toHead regs0 E _ _ msN _ (i + 3) (q + 4) (Z.min 3 (l - (i + 3)))
    ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)
    ltac:(subst q; Z.div_mod_to_equations; lia) eq_refl HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO4 (conj HJ HARU)) as (E' & HHead & Hag').
  exact (K E' msN _ HHead Hag' Hkeep HG).
Qed.

Lemma crt5_phE_last : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
  (i q c2 v3 : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> i + 2 < l -> l <= i + 3 ->
  crt5_KX regs0 E ms i q Q ->
  c2 = nth (Z.to_nat (i + 2)) bs 0 -> v3 = c2 mod 64 -> 0 <= c2 < 256 ->
  st_ok tfibsegs E (crt5_ssE1 crt5_factsE10) (restrict (w_H W) ms) ->
  crt5_EA E regs0 i q -> ew E 77 = Z_to_bv 64 (bd + 1) ->
  ew E 78 = Z_to_bv 64 (i + 2) -> ew E 79 = Z_to_bv 64 (i + 1) ->
  ew E 58 = Z_to_bv 64 c2 -> ew E 59 = Z_to_bv 64 v3 ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4) + 3) -> crt5_JR (ms_mem ms) mdc ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i q c2 v3 Q Hi0 Hil Hm3 Hq Hi2 Hi3 K Hc2 Hv3 Hb2 HS HEA H77 H78 H79 H58 H59
  HM HO HJR.
pose proof HEA as HEAc.
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
destruct HJR as [HJ HARU].
pose proof asan_consts as ((Hc1b & Hc2b) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
pose proof (crt5_shok_w E (ms_mem ms) q 3 HM E76 E54 ltac:(lia) Hq1 Hq2) as SHOK.
assert (Hbv : 0 <= v3 <= 63) by (subst v3; Z.div_mod_to_equations; lia).
assert (Hcls : (0 <= v3 <= 25) \/ (26 <= v3 <= 51) \/ (52 <= v3 <= 61) \/ (v3 = 62) \/ (v3 = 63)) by lia.
destruct Hcls as [Hcl | [Hcl | [Hcl | [Hcl | Hcl]]]].
- assert (HFE : facts_ok E (crt5_factsE1 0 25 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 app]. split; [|exact I].
       exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 0 25 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { rewrite <- (crt5_chr_off _ 59 v3 65 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO1 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFE : facts_ok E (crt5_factsE1 26 51 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 app]. split; [|exact I].
       exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 26 51 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { rewrite <- (crt5_chr_off _ 59 v3 71 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO1 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFE : facts_ok E (crt5_factsE1 52 61 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 app]. split; [|exact I].
       exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 52 61 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { rewrite <- (crt5_chr_off _ 59 v3 252 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO1 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFE : facts_ok E (crt5_factsE1 62 62 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 crt5_eq62 app]. split; [|split; [|exact I]].
       - unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
         assert (Hd : sv_denot E (SOff 59 0) = sv_denot E (SLit 62)).
         { apply U_inj. rewrite (crt5_U_atom E 59 v3 H59 ltac:(lia)), (crt5_U_lit E 62 ltac:(lia)). lia. }
         rewrite Hd. apply bv_eqb_refl.
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 62 62 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 43) mod 256 = b64c v3) by
         (rewrite (crt5_U_lit e 43 ltac:(lia)); replace v3 with 62 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO1 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFE : facts_ok E (crt5_factsE1 63 63 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsE1 app]. split; [|exact I].
       exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsE1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssE1 (crt5_factsE1 63 63 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssE1 crt5_factsE10) _ _ HS HFE)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 3 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep3 : forall x : word, ~ (q + 3 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 3 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep3; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 3) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep3)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v3) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 (b64c v3)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 47) mod 256 = b64c v3) by
         (rewrite (crt5_U_lit e 47 ltac:(lia)); replace v3 with 63 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 3 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v3) 3 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv3, Hc2; reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO1 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
Qed.

Lemma crt5_phD_out : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
  (i q c1 c2 v2 tv : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> i + 1 < l -> l <= i + 2 ->
  crt5_KX regs0 E ms i q Q ->
  c1 = nth (Z.to_nat (i + 1)) bs 0 -> c2 = nth (Z.to_nat (i + 2)) bs 0 ->
  v2 = c1 mod 16 * 4 + c2 / 64 -> tv = c1 mod 16 * 4 ->
  0 <= c1 < 256 -> 0 <= c2 < 256 ->
  st_ok tfibsegs E (crt5_ssD1 crt5_factsD10) (restrict (w_H W) ms) ->
  crt5_EA E regs0 i q -> ew E 77 = Z_to_bv 64 (bd + 1) ->
  ew E 78 = Z_to_bv 64 (i + 2) -> ew E 79 = Z_to_bv 64 (i + 1) ->
  ew E 58 = Z_to_bv 64 c2 -> ew E 59 = Z_to_bv 64 v2 -> ew E 60 = Z_to_bv 64 tv ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4) + 2) -> crt5_JR (ms_mem ms) mdc ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i q c1 c2 v2 tv Q Hi0 Hil Hm3 Hq Hi1 Hi2 K Hc1 Hc2 Hv2 Htv Hb1 Hb2 HS HEA H77
  H78 H79 H58 H59 H60 HM HO HJR.
pose proof HEA as HEAc.
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
destruct HJR as [HJ HARU].
pose proof asan_consts as ((Hc1b & Hc2b) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
pose proof (crt5_shok_w E (ms_mem ms) q 2 HM E76 E54 ltac:(lia) Hq1 Hq2) as SHOK.
assert (Hbv : 0 <= v2 <= 63) by (subst v2; Z.div_mod_to_equations; lia).
assert (Hbt : 0 <= tv <= 63) by (subst tv; Z.div_mod_to_equations; lia).
assert (Hcls : (0 <= v2 <= 25) \/ (26 <= v2 <= 51) \/ (52 <= v2 <= 61) \/ (v2 = 62) \/ (v2 = 63)) by lia.
destruct Hcls as [Hcl | [Hcl | [Hcl | [Hcl | Hcl]]]].
- assert (HFD : facts_ok E (crt5_factsD1 0 25 0 63 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 app]. split; [|split; [|exact I]].
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 0 25 0 63 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { rewrite <- (crt5_chr_off _ 59 v2 65 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 2 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO2 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFD : facts_ok E (crt5_factsD1 26 51 0 51 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 app]. split; [|split; [|exact I]].
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 26 51 0 51 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { rewrite <- (crt5_chr_off _ 59 v2 71 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 2 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO2 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFD : facts_ok E (crt5_factsD1 52 61 52 63 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 app]. split; [|split; [|exact I]].
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 52 61 52 63 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { rewrite <- (crt5_chr_off _ 59 v2 252 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 2 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO2 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFD : facts_ok E (crt5_factsD1 62 62 52 63 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 crt5_eq62 app]. split; [|split; [|split; [|exact I]]].
       - unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
         assert (Hd : sv_denot E (SOff 59 0) = sv_denot E (SLit 62)).
         { apply U_inj. rewrite (crt5_U_atom E 59 v2 H59 ltac:(lia)), (crt5_U_lit E 62 ltac:(lia)). lia. }
         rewrite Hd. apply bv_eqb_refl.
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 62 62 52 63 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 43) mod 256 = b64c v2) by
         (rewrite (crt5_U_lit e 43 ltac:(lia)); replace v2 with 62 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 2 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO2 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFD : facts_ok E (crt5_factsD1 63 63 52 63 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 app]. split; [|split; [|exact I]].
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 63 63 52 63 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 47) mod 256 = b64c v2) by
         (rewrite (crt5_U_lit e 47 ltac:(lia)); replace v2 with 63 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 2 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO2 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
Qed.

Lemma crt5_phC_in : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
  (i q c1 c2 v1 : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> i + 1 < l ->
  crt5_KD regs0 E ms i q c2 (c1 mod 16 * 4 + c2 / 64) (c1 mod 16 * 4) Q ->
  c1 = nth (Z.to_nat (i + 1)) bs 0 -> v1 = nth (Z.to_nat i) bs 0 mod 4 * 16 + c1 / 16 ->
  0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= v1 <= 63 ->
  st_ok tfibsegs E (crt5_ssC crt5_factsC0) (restrict (w_H W) ms) ->
  crt5_EA E regs0 i q -> ew E 77 = Z_to_bv 64 (bd + 1) ->
  ew E 78 = Z_to_bv 64 (i + 2) -> ew E 79 = Z_to_bv 64 (i + 1) ->
  ew E 57 = Z_to_bv 64 c1 -> ew E 58 = Z_to_bv 64 c2 -> ew E 59 = Z_to_bv 64 v1 ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4) + 1) -> crt5_JR (ms_mem ms) mdc ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i q c1 c2 v1 Q Hi0 Hil Hm3 Hq Hi1 K Hc1 Hv1 Hb1 Hb2 Hbv HS HEA H77 H78 H79
  H57 H58 H59 HM HO HJR.
pose proof HEA as HEAc.
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
destruct HJR as [HJ HARU].
pose proof asan_consts as ((Hc1b & Hc2b) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
pose proof (crt5_shok_w E (ms_mem ms) q 1 HM E76 E54 ltac:(lia) Hq1 Hq2) as SHOK.
assert (Hcls : (0 <= v1 <= 25) \/ (26 <= v1 <= 51) \/ (52 <= v1 <= 61) \/ (v1 = 62) \/ (v1 = 63)) by lia.
destruct Hcls as [Hcl | [Hcl | [Hcl | [Hcl | Hcl]]]].
- assert (HFC : facts_ok E (crt5_factsC 0 25 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC app]. split; [|exact I].
       exact (crt5_cond_ltu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 0 25 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f60.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c1 mod 16 * 4 + c2 / 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or2 e 57 58 c1 c2 HeC1 HeC2 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c1 mod 16 * 4)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_sh60 e 57 c1 HeC1 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { rewrite <- (crt5_chr_off _ 59 v1 65 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  refine (crt5_toD1 regs0 E _ _ _ ms _ i q c2 _ _ Q Hi0 Hil Hm3 Hq K Hb2 _ _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFC : facts_ok E (crt5_factsC 26 51 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC app]. split; [|exact I].
       exact (crt5_cond_ltu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 26 51 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f60.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c1 mod 16 * 4 + c2 / 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or2 e 57 58 c1 c2 HeC1 HeC2 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c1 mod 16 * 4)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_sh60 e 57 c1 HeC1 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { rewrite <- (crt5_chr_off _ 59 v1 71 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  refine (crt5_toD1 regs0 E _ _ _ ms _ i q c2 _ _ Q Hi0 Hil Hm3 Hq K Hb2 _ _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFC : facts_ok E (crt5_factsC 52 61 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC app]. split; [|exact I].
       exact (crt5_cond_ltu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 52 61 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f60.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c1 mod 16 * 4 + c2 / 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or2 e 57 58 c1 c2 HeC1 HeC2 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c1 mod 16 * 4)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_sh60 e 57 c1 HeC1 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { rewrite <- (crt5_chr_off _ 59 v1 252 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  refine (crt5_toD1 regs0 E _ _ _ ms _ i q c2 _ _ Q Hi0 Hil Hm3 Hq K Hb2 _ _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFC : facts_ok E (crt5_factsC 62 62 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC crt5_eq62 app]. split; [|split; [|exact I]].
       - unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
         assert (Hd : sv_denot E (SOff 59 0) = sv_denot E (SLit 62)).
         { apply U_inj. rewrite (crt5_U_atom E 59 v1 H59 ltac:(lia)), (crt5_U_lit E 62 ltac:(lia)). lia. }
         rewrite Hd. apply bv_eqb_refl.
       - exact (crt5_cond_ltu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 62 62 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f60.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c1 mod 16 * 4 + c2 / 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or2 e 57 58 c1 c2 HeC1 HeC2 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c1 mod 16 * 4)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_sh60 e 57 c1 HeC1 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 43) mod 256 = b64c v1) by
         (rewrite (crt5_U_lit e 43 ltac:(lia)); replace v1 with 62 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  refine (crt5_toD1 regs0 E _ _ _ ms _ i q c2 _ _ Q Hi0 Hil Hm3 Hq K Hb2 _ _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFC : facts_ok E (crt5_factsC 63 63 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC app]. split; [|exact I].
       exact (crt5_cond_ltu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 63 63 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f60.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c1 mod 16 * 4 + c2 / 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or2 e 57 58 c1 c2 HeC1 HeC2 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c1 mod 16 * 4)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_sh60 e 57 c1 HeC1 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 47) mod 256 = b64c v1) by
         (rewrite (crt5_U_lit e 47 ltac:(lia)); replace v1 with 63 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  refine (crt5_toD1 regs0 E _ _ _ ms _ i q c2 _ _ Q Hi0 Hil Hm3 Hq K Hb2 _ _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
Qed.

Lemma crt5_phD_in : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
  (i q c1 c2 v2 tv : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> i + 1 < l -> i + 2 < l ->
  crt5_KE regs0 E ms i q c2 (c2 mod 64) Q ->
  c1 = nth (Z.to_nat (i + 1)) bs 0 -> c2 = nth (Z.to_nat (i + 2)) bs 0 ->
  v2 = c1 mod 16 * 4 + c2 / 64 -> tv = c1 mod 16 * 4 ->
  0 <= c1 < 256 -> 0 <= c2 < 256 ->
  st_ok tfibsegs E (crt5_ssD1 crt5_factsD10) (restrict (w_H W) ms) ->
  crt5_EA E regs0 i q -> ew E 77 = Z_to_bv 64 (bd + 1) ->
  ew E 78 = Z_to_bv 64 (i + 2) -> ew E 79 = Z_to_bv 64 (i + 1) ->
  ew E 58 = Z_to_bv 64 c2 -> ew E 59 = Z_to_bv 64 v2 -> ew E 60 = Z_to_bv 64 tv ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4) + 2) -> crt5_JR (ms_mem ms) mdc ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i q c1 c2 v2 tv Q Hi0 Hil Hm3 Hq Hi1 Hi2 K Hc1 Hc2 Hv2 Htv Hb1 Hb2 HS HEA H77
  H78 H79 H58 H59 H60 HM HO HJR.
pose proof HEA as HEAc.
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
destruct HJR as [HJ HARU].
pose proof asan_consts as ((Hc1b & Hc2b) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
pose proof (crt5_shok_w E (ms_mem ms) q 2 HM E76 E54 ltac:(lia) Hq1 Hq2) as SHOK.
assert (Hbv : 0 <= v2 <= 63) by (subst v2; Z.div_mod_to_equations; lia).
assert (Hbt : 0 <= tv <= 63) by (subst tv; Z.div_mod_to_equations; lia).
assert (Hcls : (0 <= v2 <= 25) \/ (26 <= v2 <= 51) \/ (52 <= v2 <= 61) \/ (v2 = 62) \/ (v2 = 63)) by lia.
destruct Hcls as [Hcl | [Hcl | [Hcl | [Hcl | Hcl]]]].
- assert (HFD : facts_ok E (crt5_factsD1 0 25 0 63 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 app]. split; [|exact I].
       exact (crt5_cond_ltu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 0 25 0 63 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f98.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c2 mod 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_and63 e 58 c2 HeC2 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { rewrite <- (crt5_chr_off _ 59 v2 65 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  refine (crt5_toE1 regs0 E _ _ _ ms _ i q c2 _ Q Hi0 Hil Hm3 Hq K Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFD : facts_ok E (crt5_factsD1 26 51 0 51 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 app]. split; [|exact I].
       exact (crt5_cond_ltu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 26 51 0 51 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f98.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c2 mod 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_and63 e 58 c2 HeC2 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { rewrite <- (crt5_chr_off _ 59 v2 71 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  refine (crt5_toE1 regs0 E _ _ _ ms _ i q c2 _ Q Hi0 Hil Hm3 Hq K Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFD : facts_ok E (crt5_factsD1 52 61 52 63 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 app]. split; [|exact I].
       exact (crt5_cond_ltu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 52 61 52 63 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f98.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c2 mod 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_and63 e 58 c2 HeC2 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { rewrite <- (crt5_chr_off _ 59 v2 252 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  refine (crt5_toE1 regs0 E _ _ _ ms _ i q c2 _ Q Hi0 Hil Hm3 Hq K Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFD : facts_ok E (crt5_factsD1 62 62 52 63 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 crt5_eq62 app]. split; [|split; [|exact I]].
       - unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
         assert (Hd : sv_denot E (SOff 59 0) = sv_denot E (SLit 62)).
         { apply U_inj. rewrite (crt5_U_atom E 59 v2 H59 ltac:(lia)), (crt5_U_lit E 62 ltac:(lia)). lia. }
         rewrite Hd. apply bv_eqb_refl.
       - exact (crt5_cond_ltu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 62 62 52 63 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f98.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c2 mod 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_and63 e 58 c2 HeC2 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 43) mod 256 = b64c v2) by
         (rewrite (crt5_U_lit e 43 ltac:(lia)); replace v2 with 62 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  refine (crt5_toE1 regs0 E _ _ _ ms _ i q c2 _ Q Hi0 Hil Hm3 Hq K Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFD : facts_ok E (crt5_factsD1 63 63 52 63 true)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H58 H58 H58 H59 H60 E76 H77|]. split.
     { cbn [f_conds crt5_factsD1 app]. split; [|exact I].
       exact (crt5_cond_ltu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsD1]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssD1 (crt5_factsD1 63 63 52 63 true)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssD1 crt5_factsD10) _ _ HS HFD)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81f98.
  { apply (crt5_awr_w E q 2 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep2 : forall x : word, ~ (q + 2 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 2 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep2; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 2) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep2)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC2 : ew e 58 = Z_to_bv 64 c2) by (rewrite !crt5_ew_ewset by lia; exact H58);
    assert (HeV : ew e 59 = Z_to_bv 64 v2) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R11 : YK11.getr (ms_regs msN) 11%bv = Z_to_bv 64 (c2 mod 64)) by
      (eapply (crt5_regv_U e _ _ 11%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_and63 e 58 c2 HeC2 ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 (b64c v2)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 47) mod 256 = b64c v2) by
         (rewrite (crt5_U_lit e 47 ltac:(lia)); replace v2 with 63 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 2 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v2) 2 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with true by (symmetry; apply Z.ltb_lt; lia);
             rewrite Hv2, Hc1, Hc2; reflexivity)). }
  refine (crt5_toE1 regs0 E _ _ _ ms _ i q c2 _ Q Hi0 Hil Hm3 Hq K Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H58 H58 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
Qed.

Lemma crt5_phC_out : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
  (i q c1 c2 v1 : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 -> l <= i + 1 ->
  crt5_KX regs0 E ms i q Q ->
  c1 = nth (Z.to_nat (i + 1)) bs 0 -> v1 = nth (Z.to_nat i) bs 0 mod 4 * 16 + c1 / 16 ->
  0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= v1 <= 63 ->
  st_ok tfibsegs E (crt5_ssC crt5_factsC0) (restrict (w_H W) ms) ->
  crt5_EA E regs0 i q -> ew E 77 = Z_to_bv 64 (bd + 1) ->
  ew E 78 = Z_to_bv 64 (i + 2) -> ew E 79 = Z_to_bv 64 (i + 1) ->
  ew E 57 = Z_to_bv 64 c1 -> ew E 58 = Z_to_bv 64 c2 -> ew E 59 = Z_to_bv 64 v1 ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4) + 1) -> crt5_JR (ms_mem ms) mdc ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i q c1 c2 v1 Q Hi0 Hil Hm3 Hq Hi1 K Hc1 Hv1 Hb1 Hb2 Hbv HS HEA H77 H78 H79
  H57 H58 H59 HM HO HJR.
pose proof HEA as HEAc.
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
destruct HJR as [HJ HARU].
pose proof asan_consts as ((Hc1b & Hc2b) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
pose proof (crt5_shok_w E (ms_mem ms) q 1 HM E76 E54 ltac:(lia) Hq1 Hq2) as SHOK.
assert (Hcls : (0 <= v1 <= 25) \/ (26 <= v1 <= 51) \/ (52 <= v1 <= 61) \/ (v1 = 62) \/ (v1 = 63)) by lia.
destruct Hcls as [Hcl | [Hcl | [Hcl | [Hcl | Hcl]]]].
- assert (HFC : facts_ok E (crt5_factsC 0 25 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC app]. split; [|split; [|split; [|exact I]]].
       - exact (crt5_cond_geu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 0 25 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { rewrite <- (crt5_chr_off _ 59 v1 65 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl2 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl2.
     refine (crt5_byte_at _ _ _ q 1 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 1 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q 61 2 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hp2)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  assert (HO3 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO2
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO3 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFC : facts_ok E (crt5_factsC 26 51 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC app]. split; [|split; [|split; [|exact I]]].
       - exact (crt5_cond_geu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 26 51 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { rewrite <- (crt5_chr_off _ 59 v1 71 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl2 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl2.
     refine (crt5_byte_at _ _ _ q 1 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 1 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q 61 2 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hp2)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  assert (HO3 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO2
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO3 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFC : facts_ok E (crt5_factsC 52 61 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC app]. split; [|split; [|split; [|exact I]]].
       - exact (crt5_cond_geu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 52 61 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { rewrite <- (crt5_chr_off _ 59 v1 252 HeV ltac:(lia)
       ltac:(first [left; split; [reflexivity | lia]
                   | right; left; split; [reflexivity | lia]
                   | right; right; split; [reflexivity | lia]])).
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl2 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl2.
     refine (crt5_byte_at _ _ _ q 1 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 1 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q 61 2 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hp2)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  assert (HO3 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO2
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO3 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFC : facts_ok E (crt5_factsC 62 62 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC crt5_eq62 app]. split; [|split; [|split; [|split; [|exact I]]]].
       - unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
         assert (Hd : sv_denot E (SOff 59 0) = sv_denot E (SLit 62)).
         { apply U_inj. rewrite (crt5_U_atom E 59 v1 H59 ltac:(lia)), (crt5_U_lit E 62 ltac:(lia)). lia. }
         rewrite Hd. apply bv_eqb_refl.
       - exact (crt5_cond_geu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 62 62 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 43) mod 256 = b64c v1) by
         (rewrite (crt5_U_lit e 43 ltac:(lia)); replace v1 with 62 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl2 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl2.
     refine (crt5_byte_at _ _ _ q 1 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 1 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q 61 2 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hp2)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  assert (HO3 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO2
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO3 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
- assert (HFC : facts_ok E (crt5_factsC 63 63 false)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H57 H57 H58 H59 H59 E76 H77|]. split.
     { cbn [f_conds crt5_factsC app]. split; [|split; [|split; [|exact I]]].
       - exact (crt5_cond_geu E 79 0 51 (i + 1) l H79 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 78 0 51 (i + 2) l H78 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
       - exact (crt5_cond_geu E 53 3 51 i l E53 E51 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
     cbn [f_alias crt5_factsC]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssC (crt5_factsC 63 63 false)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssC crt5_factsC0) _ _ HS HFC)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x82098.
  { apply (crt5_awr_w E q 1 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep1 : forall x : word, ~ (q + 1 <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (exact (crt5_keep1 E _ _ q 1 HF E54 ltac:(lia) ltac:(lia) ltac:(lia))).
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply Hkeep1; lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ (q + 1) (q + 4) HO ltac:(lia) ltac:(lia) Hkeep1)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeV : ew e 59 = Z_to_bv 64 v1) by (rewrite !crt5_ew_ewset by lia; exact H59);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 1) 1 (b64c v1)).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hlit : U e (SLit 47) mod 256 = b64c v1) by
         (rewrite (crt5_U_lit e 47 ltac:(lia)); replace v1 with 63 by lia; reflexivity) end.
     rewrite <- Hlit.
     refine (crt5_byte_at _ _ _ q 1 _ 1 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp2 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 2) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl2 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl2.
     refine (crt5_byte_at _ _ _ q 1 _ 2 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (Hp3 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) (q + 3) 1 61).
  { match goal with HSx : st_ok _ ?e _ _ |- _ =>
       assert (Hl3 : U e (SLit 61) mod 256 = 61) by (rewrite (crt5_U_lit e 61 ltac:(lia)); reflexivity) end.
     rewrite <- Hl3.
     refine (crt5_byte_at _ _ _ q 1 _ 3 _ HS1 _ _ HeQ _);
       first [ solve [lia]
             | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end
             | lazymatch goal with |- In _ _ => solve [cbn [In]; tauto] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 2)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c v1) 1 ltac:(lia) Hm3 Hq ltac:(lia) HO0
       ltac:(replace (q + Z.of_nat 1) with (q + 1) by lia; exact Hby)
       ltac:(unfold crt5_quad; cbn [nth]; rewrite Hv1, Hc1; reflexivity)). }
  assert (HO2 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 3)).
  { apply (crt5_out_step (ms_mem msN) i q 61 2 ltac:(lia) Hm3 Hq ltac:(lia) HO1
       ltac:(replace (q + Z.of_nat 2) with (q + 2) by lia; exact Hp2)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 1 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  assert (HO3 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 4)).
  { apply (crt5_out_step (ms_mem msN) i q 61 3 ltac:(lia) Hm3 Hq ltac:(lia) HO2
       ltac:(replace (q + Z.of_nat 3) with (q + 3) by lia; exact Hp3)
       ltac:(unfold crt5_quad; cbn [nth];
             replace (i + 2 <? l) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity)). }
  destruct (crt5_toOut regs0 E _ _ msN _ i q ltac:(lia) ltac:(lia) Hm3 Hq ltac:(lia) HS1
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H57 H57 H58 E82 E70 E71 H78 H79)
    ltac:(intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity)
    ltac:(unfold crt5_EA_low; repeat split; assumption)
    HM1 HO3 (conj HJ HARU)) as (E' & HX & Hag').
  exact (K E' msN _ HX Hag' Hkeep HG).
Qed.

Lemma crt5_phB : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
  (i q c0 c1 c2 : Z) (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 -> q = want + i / 3 * 4 ->
  crt5_KC regs0 E ms i q c1 c2 (c0 mod 4 * 16 + c1 / 16) Q ->
  c0 = nth (Z.to_nat i) bs 0 -> 0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 ->
  st_ok tfibsegs E (crt5_ssB (crt5_factsB 0 255)) (restrict (w_H W) ms) ->
  crt5_EA E regs0 i q -> ew E 77 = Z_to_bv 64 (bd + 1) ->
  ew E 78 = Z_to_bv 64 (i + 2) -> ew E 79 = Z_to_bv 64 (i + 1) ->
  ew E 56 = Z_to_bv 64 c0 -> ew E 57 = Z_to_bv 64 c1 -> ew E 58 = Z_to_bv 64 c2 ->
  crt5_memf (ms_mem ms) -> crt5_out (ms_mem ms) (Z.to_nat (i / 3 * 4)) -> crt5_JR (ms_mem ms) mdc ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i q c0 c1 c2 Q Hi0 Hil Hm3 Hq K Hc0 Hb0 Hb1 Hb2 HS HEA H77 H78 H79 H56 H57 H58
  HM HO HJR.
pose proof HEA as HEAc.
destruct HEA as (E51 & E52 & E53 & E54 & E55 & E76 & Ea2 & Ea3 & Ea4 & Ea8 & Ea9 & Ea26 & E82 & E70 & E71).
destruct HJR as [HJ HARU].
pose proof asan_consts as ((Hc1 & Hc2) & _ & _ & _ & _).
destruct HBD as [HD1 HD2]. destruct HWT as [HW1 HW2]. pose proof crt5_en_pos as HEp.
assert (Hq1 : want <= q) by (subst q; Z.div_mod_to_equations; lia).
assert (Hq2 : q + 4 <= want + En) by (subst q; pose proof (crt5_q_room i ltac:(lia) Hm3); lia).
pose proof (crt5_shok_w E (ms_mem ms) q 0 HM E76 E54 ltac:(lia) Hq1 Hq2) as SHOK.
assert (Hv56 : forall EE : env, ew EE 59 = Z_to_bv 64 (c0 mod 4 * 16 + c1 / 16) ->
  ew EE 59 = Z_to_bv 64 (c0 mod 4 * 16 + c1 / 16)) by (intros EE HH; exact HH).
assert (Hcls : (0 <= c0 <= 103) \/ (104 <= c0 <= 207) \/ (208 <= c0 <= 247) \/ (248 <= c0 <= 251)
               \/ (252 <= c0 <= 255)) by lia.
destruct Hcls as [Hcl | [Hcl | [Hcl | [Hcl | Hcl]]]].
- assert (HFB : facts_ok E (crt5_factsB 0 103)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H56 H57 H58 H56 H56 E76 H77|]. split.
    { cbn [f_conds crt5_factsB]. exact I. }
    cbn [f_alias crt5_factsB]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssB (crt5_factsB 0 103)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssB (crt5_factsB 0 255)) _ _ HS HFB)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81ef4.
  { apply (crt5_awr_w E q 0 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply (crt5_keep1 E _ _ q 0 HF E54 ltac:(lia) ltac:(lia) ltac:(lia)); lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4)))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ q (q + 4) HO ltac:(lia) ltac:(lia) Hkeep)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC0 : ew e 56 = Z_to_bv 64 c0) by (rewrite !crt5_ew_ewset by lia; exact H56);
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c0 mod 4 * 16 + c1 / 16)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or1 e 56 57 c0 c1 HeC0 HeC1 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) q 1 (b64c (c0 / 4))).
  { rewrite <- (crt5_chr_sh _ c0 65 HeC0 ltac:(lia)
        ltac:(first [left; split; [reflexivity | lia]
                    | right; left; split; [reflexivity | lia]
                    | right; right; split; [reflexivity | lia]])).
    refine (crt5_byte0 _ _ _ q _ HS1 _ HeQ _);
      first [ solve [lia] | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c (c0 / 4)) 0 ltac:(lia) Hm3 Hq ltac:(lia)
      ltac:(rewrite Nat.add_0_r; exact HO0)
      ltac:(replace (q + Z.of_nat 0) with q by lia; exact Hby)
      ltac:(unfold crt5_quad; cbn [nth]; rewrite Hc0; reflexivity)). }
  refine (crt5_toC regs0 E _ _ _ ms _ i q c1 c2 _ Q Hi0 Hil Hm3 Hq K Hb1 Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H56 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFB : facts_ok E (crt5_factsB 104 207)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H56 H57 H58 H56 H56 E76 H77|]. split.
    { cbn [f_conds crt5_factsB]. exact I. }
    cbn [f_alias crt5_factsB]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssB (crt5_factsB 104 207)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssB (crt5_factsB 0 255)) _ _ HS HFB)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81ef4.
  { apply (crt5_awr_w E q 0 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply (crt5_keep1 E _ _ q 0 HF E54 ltac:(lia) ltac:(lia) ltac:(lia)); lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4)))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ q (q + 4) HO ltac:(lia) ltac:(lia) Hkeep)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC0 : ew e 56 = Z_to_bv 64 c0) by (rewrite !crt5_ew_ewset by lia; exact H56);
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c0 mod 4 * 16 + c1 / 16)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or1 e 56 57 c0 c1 HeC0 HeC1 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) q 1 (b64c (c0 / 4))).
  { rewrite <- (crt5_chr_sh _ c0 71 HeC0 ltac:(lia)
        ltac:(first [left; split; [reflexivity | lia]
                    | right; left; split; [reflexivity | lia]
                    | right; right; split; [reflexivity | lia]])).
    refine (crt5_byte0 _ _ _ q _ HS1 _ HeQ _);
      first [ solve [lia] | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c (c0 / 4)) 0 ltac:(lia) Hm3 Hq ltac:(lia)
      ltac:(rewrite Nat.add_0_r; exact HO0)
      ltac:(replace (q + Z.of_nat 0) with q by lia; exact Hby)
      ltac:(unfold crt5_quad; cbn [nth]; rewrite Hc0; reflexivity)). }
  refine (crt5_toC regs0 E _ _ _ ms _ i q c1 c2 _ Q Hi0 Hil Hm3 Hq K Hb1 Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H56 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFB : facts_ok E (crt5_factsB 208 247)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H56 H57 H58 H56 H56 E76 H77|]. split.
    { cbn [f_conds crt5_factsB]. exact I. }
    cbn [f_alias crt5_factsB]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssB (crt5_factsB 208 247)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssB (crt5_factsB 0 255)) _ _ HS HFB)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81ef4.
  { apply (crt5_awr_w E q 0 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply (crt5_keep1 E _ _ q 0 HF E54 ltac:(lia) ltac:(lia) ltac:(lia)); lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4)))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ q (q + 4) HO ltac:(lia) ltac:(lia) Hkeep)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC0 : ew e 56 = Z_to_bv 64 c0) by (rewrite !crt5_ew_ewset by lia; exact H56);
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c0 mod 4 * 16 + c1 / 16)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or1 e 56 57 c0 c1 HeC0 HeC1 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) q 1 (b64c (c0 / 4))).
  { rewrite <- (crt5_chr_sh _ c0 252 HeC0 ltac:(lia)
        ltac:(first [left; split; [reflexivity | lia]
                    | right; left; split; [reflexivity | lia]
                    | right; right; split; [reflexivity | lia]])).
    refine (crt5_byte0 _ _ _ q _ HS1 _ HeQ _);
      first [ solve [lia] | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c (c0 / 4)) 0 ltac:(lia) Hm3 Hq ltac:(lia)
      ltac:(rewrite Nat.add_0_r; exact HO0)
      ltac:(replace (q + Z.of_nat 0) with q by lia; exact Hby)
      ltac:(unfold crt5_quad; cbn [nth]; rewrite Hc0; reflexivity)). }
  refine (crt5_toC regs0 E _ _ _ ms _ i q c1 c2 _ Q Hi0 Hil Hm3 Hq K Hb1 Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H56 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFB : facts_ok E (crt5_factsB 248 251)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H56 H57 H58 H56 H56 E76 H77|]. split.
    { cbn [f_conds crt5_factsB]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
      assert (Hd : sv_denot E (SAlu ALU_SRL (SOff 56 0) (SLit 2)) = sv_denot E (SLit 62)).
      { apply U_inj. rewrite (crt5_sh2 E 56 c0 H56 ltac:(lia)), (crt5_U_lit E 62 ltac:(lia)).
        Z.div_mod_to_equations. lia. }
      rewrite Hd. apply bv_eqb_refl. }
    cbn [f_alias crt5_factsB]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssB (crt5_factsB 248 251)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssB (crt5_factsB 0 255)) _ _ HS HFB)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81ef4.
  { apply (crt5_awr_w E q 0 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply (crt5_keep1 E _ _ q 0 HF E54 ltac:(lia) ltac:(lia) ltac:(lia)); lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4)))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ q (q + 4) HO ltac:(lia) ltac:(lia) Hkeep)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC0 : ew e 56 = Z_to_bv 64 c0) by (rewrite !crt5_ew_ewset by lia; exact H56);
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c0 mod 4 * 16 + c1 / 16)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or1 e 56 57 c0 c1 HeC0 HeC1 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]);
    assert (Hlit : U e (SLit 43) mod 256 = b64c (c0 / 4)) by
      (rewrite (crt5_U_lit e 43 ltac:(lia));
       replace (c0 / 4) with 62 by (Z.div_mod_to_equations; lia); reflexivity) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) q 1 (b64c (c0 / 4))).
  { rewrite <- Hlit.
     refine (crt5_byte0 _ _ _ q _ HS1 _ HeQ _);
      first [ solve [lia] | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c (c0 / 4)) 0 ltac:(lia) Hm3 Hq ltac:(lia)
      ltac:(rewrite Nat.add_0_r; exact HO0)
      ltac:(replace (q + Z.of_nat 0) with q by lia; exact Hby)
      ltac:(unfold crt5_quad; cbn [nth]; rewrite Hc0; reflexivity)). }
  refine (crt5_toC regs0 E _ _ _ ms _ i q c1 c2 _ Q Hi0 Hil Hm3 Hq K Hb1 Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H56 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
- assert (HFB : facts_ok E (crt5_factsB 252 255)).
  { split; [crt5_atok E51 E52 E53 E54 E55 H56 H57 H58 H56 H56 E76 H77|]. split.
    { cbn [f_conds crt5_factsB]. exact I. }
    cbn [f_alias crt5_factsB]. exact I. }
  assert (HS1 : st_ok tfibsegs E (crt5_ssB (crt5_factsB 252 255)) (restrict (w_H W) ms))
    by (apply (st_ok_facts tfibsegs E (crt5_ssB (crt5_factsB 0 255)) _ _ HS HFB)).
  fsw_aj_run_to_tokU crt_tbl_ok HS1 HJ HARU SHOK crt5_Bspan 0x81ef4.
  { apply (crt5_awr_w E q 0 E54 Hq1 Hq2 ltac:(lia)). }
  match goal with |- SRr _ _ (mkCfg ?m _) _ => set (msN := m) in * end.
  assert (Hkeep : forall x : word, ~ (q <= bv_unsigned x < q + 4) -> ms_mem msN x = ms_mem ms x)
    by (intros x Hx; apply (crt5_keep1 E _ _ q 0 HF E54 ltac:(lia) ltac:(lia) ltac:(lia)); lia).
  assert (HM1 : crt5_memf (ms_mem msN))
    by (apply (crt5_memf_keep (ms_mem ms) (ms_mem msN) q (q + 4) HM Hq1 ltac:(lia) Hkeep HG)).
  assert (HO0 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4)))
    by (apply (crt5_out_keep (ms_mem ms) (ms_mem msN) _ q (q + 4) HO ltac:(lia) ltac:(lia) Hkeep)).
  match goal with HSx : st_ok _ ?e _ _ |- _ =>
    assert (HeC0 : ew e 56 = Z_to_bv 64 c0) by (rewrite !crt5_ew_ewset by lia; exact H56);
    assert (HeC1 : ew e 57 = Z_to_bv 64 c1) by (rewrite !crt5_ew_ewset by lia; exact H57);
    assert (HeQ : ew e 54 = Z_to_bv 64 q) by (rewrite !crt5_ew_ewset by lia; exact E54);
    assert (R30 : YK11.getr (ms_regs msN) 30%bv = Z_to_bv 64 (c0 mod 4 * 16 + c1 / 16)) by
      (eapply (crt5_regv_U e _ _ 30%bv _ _ HS1);
       [ vm_compute; reflexivity
       | apply (crt5_or1 e 56 57 c0 c1 HeC0 HeC1 ltac:(lia) ltac:(lia))
       | Z.div_mod_to_equations; lia ]);
    assert (Hlit : U e (SLit 47) mod 256 = b64c (c0 / 4)) by
      (rewrite (crt5_U_lit e 47 ltac:(lia));
       replace (c0 / 4) with 63 by (Z.div_mod_to_equations; lia); reflexivity) end.
  assert (Hby : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msN)) q 1 (b64c (c0 / 4))).
  { rewrite <- Hlit.
     refine (crt5_byte0 _ _ _ q _ HS1 _ HeQ _);
      first [ solve [lia] | lazymatch goal with |- nth_error _ _ = _ => solve [vm_compute; reflexivity] end ]. }
  assert (HO1 : crt5_out (ms_mem msN) (Z.to_nat (i / 3 * 4) + 1)).
  { apply (crt5_out_step (ms_mem msN) i q (b64c (c0 / 4)) 0 ltac:(lia) Hm3 Hq ltac:(lia)
      ltac:(rewrite Nat.add_0_r; exact HO0)
      ltac:(replace (q + Z.of_nat 0) with q by lia; exact Hby)
      ltac:(unfold crt5_quad; cbn [nth]; rewrite Hc0; reflexivity)). }
  refine (crt5_toC regs0 E _ _ _ ms _ i q c1 c2 _ Q Hi0 Hil Hm3 Hq K Hb1 Hb2 _ HS1 _ _ _ _ HEAc
    HM1 HO1 (conj HJ HARU) Hkeep HG).
  + Z.div_mod_to_equations; lia.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + crt5_regs_tac HS1 E51 E52 E53 E54 E76 H77 H56 H57 H58 E82 E70 E71 H78 H79.
  + intros n Hn; rewrite !crt5_ew_ewset by lia; reflexivity.
Qed.
Lemma crt5_ag_trans : forall (E0 E1 E2 : env),
  (forall n, (n < 51)%nat -> ew E1 n = ew E0 n) -> (forall n, (n < 51)%nat -> ew E2 n = ew E1 n) ->
  forall n, (n < 51)%nat -> ew E2 n = ew E0 n.
Proof. intros E0 E1 E2 H1 H2 n Hn. rewrite (H2 n Hn). exact (H1 n Hn). Qed.

(* ================= one trip of the loop: head -> head, or head -> exit ================= *)
Lemma crt5_keep_trans : forall (m0 m1 m2 : word -> option byte) (a b : Z),
  (forall x : word, ~ (a <= bv_unsigned x < b) -> m1 x = m0 x) ->
  (forall x : word, ~ (a <= bv_unsigned x < b) -> m2 x = m1 x) ->
  forall x : word, ~ (a <= bv_unsigned x < b) -> m2 x = m0 x.
Proof. intros m0 m1 m2 a b H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.
Lemma crt5_trip : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model) (i : Z)
    (Q : world tfibsegs -> config -> Prop),
  0 <= i -> i < l -> i mod 3 = 0 ->
  crt5_head_at regs0 E ms mdc i ->
  crt5_KH regs0 E ms i (want + i / 3 * 4) Q ->
  crt5_KX regs0 E ms i (want + i / 3 * 4) Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc i Q Hi0 Hil Hm3 HH KH KX.
destruct HH as (HS & HEA & H77 & H56 & H57 & H58 & HM & HO & HJR & _ & _ & _).
assert (Hbyt : forall j, 0 <= nth j bs 0 < 256).
{ intros j. destruct (Nat.lt_ge_cases j (length bs)) as [Hj | Hj].
  - destruct HM as (HG0 & _). exact (proj2 (HG0 j Hj)).
  - rewrite crt5_nth_big by lia. lia. }
apply (crt5_phH regs0 E ms mdc i (want + i / 3 * 4) (Z.min 3 (l - i)) Q Hi0 Hil Hm3 eq_refl eq_refl
  HS HEA H77 H56 H57 H58 HM HO HJR).
intros EB msB mdcB HSB HagB HEAB H76B H77B H78B H55B H56B H57B HMB HOB HJRB HkB HgB.
apply (crt5_phB regs0 EB msB mdcB i (want + i / 3 * 4) (nth (Z.to_nat i) bs 0)
  (nth (Z.to_nat (i + 1)) bs 0) (nth (Z.to_nat (i + 2)) bs 0) Q Hi0 Hil Hm3 eq_refl);
  [ | reflexivity | apply Hbyt | apply Hbyt | apply Hbyt | exact HSB | exact HEAB | exact H76B
  | exact H77B | exact H78B | exact H55B | exact H56B | exact H57B | exact HMB | exact HOB | exact HJRB ].
intros EC msC mdcC HSC HagC HEAC H76C H77C H78C H56C H57C H58C HMC HOC HJRC HkC HgC.
pose proof (crt5_keep_trans _ _ _ _ _ HkB HkC) as HkC'.
  pose proof (crt5_ag_trans _ _ _ HagB HagC) as HagC'.
pose proof (mem_grows_trans _ _ _ HgB HgC) as HgC'.
destruct (Z_lt_ge_dec (i + 1) l) as [Hi1 | Hi1].
- (* at least two bytes in this trip *)
  apply (crt5_phC_in regs0 EC msC mdcC i (want + i / 3 * 4) (nth (Z.to_nat (i + 1)) bs 0)
    (nth (Z.to_nat (i + 2)) bs 0) (nth (Z.to_nat i) bs 0 mod 4 * 16 + nth (Z.to_nat (i + 1)) bs 0 / 16)
    Q Hi0 Hil Hm3 eq_refl Hi1);
    [ | reflexivity | reflexivity | apply Hbyt | apply Hbyt
    | pose proof (Hbyt (Z.to_nat i)); pose proof (Hbyt (Z.to_nat (i + 1))); Z.div_mod_to_equations; lia
    | exact HSC | exact HEAC | exact H76C | exact H77C | exact H78C | exact H56C | exact H57C
    | exact H58C | exact HMC | exact HOC | exact HJRC ].
  intros ED msD mdcD HSD HagD HEAD H76D H77D H78D H57D H58D H59D HMD HOD HJRD HkD HgD.
  pose proof (crt5_keep_trans _ _ _ _ _ HkC' HkD) as HkD'.
  pose proof (crt5_ag_trans _ _ _ HagC' HagD) as HagD'.
  pose proof (mem_grows_trans _ _ _ HgC' HgD) as HgD'.
  destruct (Z_lt_ge_dec (i + 2) l) as [Hi2 | Hi2].
  + (* three bytes *)
    apply (crt5_phD_in regs0 ED msD mdcD i (want + i / 3 * 4) (nth (Z.to_nat (i + 1)) bs 0)
      (nth (Z.to_nat (i + 2)) bs 0) (nth (Z.to_nat (i + 1)) bs 0 mod 16 * 4 + nth (Z.to_nat (i + 2)) bs 0 / 64)
      (nth (Z.to_nat (i + 1)) bs 0 mod 16 * 4) Q Hi0 Hil Hm3 eq_refl Hi1 Hi2);
      [ | reflexivity | reflexivity | reflexivity | reflexivity | apply Hbyt | apply Hbyt
      | exact HSD | exact HEAD | exact H76D | exact H77D | exact H78D | exact H57D | exact H58D
      | exact H59D | exact HMD | exact HOD | exact HJRD ].
    intros EE msE mdcE HSE HagE HEAE H76E H77E H78E H57E H58E HME HOE HJRE HkE HgE.
    pose proof (crt5_keep_trans _ _ _ _ _ HkD' HkE) as HkE'.
    pose proof (crt5_ag_trans _ _ _ HagD' HagE) as HagE'.
    pose proof (mem_grows_trans _ _ _ HgD' HgE) as HgE'.
    destruct (Z_lt_ge_dec (i + 3) l) as [Hi3 | Hi3].
    * apply (crt5_phE_more regs0 EE msE mdcE i (want + i / 3 * 4) (nth (Z.to_nat (i + 2)) bs 0)
        (nth (Z.to_nat (i + 2)) bs 0 mod 64) Q Hi0 Hil Hm3 eq_refl Hi2 Hi3);
        [ | reflexivity | reflexivity | apply Hbyt | exact HSE | exact HEAE | exact H76E | exact H77E
        | exact H78E | exact H57E | exact H58E | exact HME | exact HOE | exact HJRE ].
      intros E' ms' mdc' HHead Hag' Hk' Hg'.
      exact (KH E' ms' mdc' HHead (crt5_ag_trans _ _ _ HagE' Hag')
               (crt5_keep_trans _ _ _ _ _ HkE' Hk') (mem_grows_trans _ _ _ HgE' Hg')).
    * apply (crt5_phE_last regs0 EE msE mdcE i (want + i / 3 * 4) (nth (Z.to_nat (i + 2)) bs 0)
        (nth (Z.to_nat (i + 2)) bs 0 mod 64) Q Hi0 Hil Hm3 eq_refl Hi2 ltac:(lia));
        [ | reflexivity | reflexivity | apply Hbyt | exact HSE | exact HEAE | exact H76E | exact H77E
        | exact H78E | exact H57E | exact H58E | exact HME | exact HOE | exact HJRE ].
      intros E' ms' mdc' HX Hag' Hk' Hg'.
      exact (KX E' ms' mdc' HX (crt5_ag_trans _ _ _ HagE' Hag')
               (crt5_keep_trans _ _ _ _ _ HkE' Hk') (mem_grows_trans _ _ _ HgE' Hg')).
  + (* exactly two bytes *)
    apply (crt5_phD_out regs0 ED msD mdcD i (want + i / 3 * 4) (nth (Z.to_nat (i + 1)) bs 0)
      (nth (Z.to_nat (i + 2)) bs 0) (nth (Z.to_nat (i + 1)) bs 0 mod 16 * 4 + nth (Z.to_nat (i + 2)) bs 0 / 64)
      (nth (Z.to_nat (i + 1)) bs 0 mod 16 * 4) Q Hi0 Hil Hm3 eq_refl Hi1 ltac:(lia));
      [ | reflexivity | reflexivity | reflexivity | reflexivity | apply Hbyt | apply Hbyt
      | exact HSD | exact HEAD | exact H76D | exact H77D | exact H78D | exact H57D | exact H58D
      | exact H59D | exact HMD | exact HOD | exact HJRD ].
    intros E' ms' mdc' HX Hag' Hk' Hg'.
    exact (KX E' ms' mdc' HX (crt5_ag_trans _ _ _ HagD' Hag')
             (crt5_keep_trans _ _ _ _ _ HkD' Hk') (mem_grows_trans _ _ _ HgD' Hg')).
- (* exactly one byte *)
  apply (crt5_phC_out regs0 EC msC mdcC i (want + i / 3 * 4) (nth (Z.to_nat (i + 1)) bs 0)
    (nth (Z.to_nat (i + 2)) bs 0) (nth (Z.to_nat i) bs 0 mod 4 * 16 + nth (Z.to_nat (i + 1)) bs 0 / 16)
    Q Hi0 Hil Hm3 eq_refl ltac:(lia));
    [ | reflexivity | reflexivity | apply Hbyt | apply Hbyt
    | pose proof (Hbyt (Z.to_nat i)); pose proof (Hbyt (Z.to_nat (i + 1))); Z.div_mod_to_equations; lia
    | exact HSC | exact HEAC | exact H76C | exact H77C | exact H78C | exact H56C | exact H57C
    | exact H58C | exact HMC | exact HOC | exact HJRC ].
  intros E' ms' mdc' HX Hag' Hk' Hg'.
  exact (KX E' ms' mdc' HX (crt5_ag_trans _ _ _ HagC' Hag')
           (crt5_keep_trans _ _ _ _ _ HkC' Hk') (mem_grows_trans _ _ _ HgC' Hg')).
Qed.

(* ================= the loop: induction on the trips that remain ================= *)
Lemma crt5_keep_widen : forall (m0 m1 m2 : word -> option byte) (a b c : Z),
  a <= b -> b <= c ->
  (forall x : word, ~ (a <= bv_unsigned x < b) -> m1 x = m0 x) ->
  (forall x : word, ~ (b <= bv_unsigned x < c) -> m2 x = m1 x) ->
  forall x : word, ~ (a <= bv_unsigned x < c) -> m2 x = m0 x.
Proof.
intros m0 m1 m2 a b c Hab Hbc H1 H2 x Hx.
rewrite (H2 x ltac:(lia)). exact (H1 x ltac:(lia)).
Qed.
Definition crt5_KL (regs0 : bvmap 5 word) (E0 : env) (ms0 : machine_state)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall (E' : env) (ms' : machine_state) (mdc' : Model) (i' q' : Z),
    crt5_exit_at regs0 E' ms' mdc' i' q' ->
    (forall n, (n < 51)%nat -> ew E' n = ew E0 n) ->
    (forall x : word, ~ (want <= bv_unsigned x < want + En) -> ms_mem ms' x = ms_mem ms0 x) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr tfibsegs W (mkCfg ms' mdc') Q.
Lemma crt5_loop : forall (n : nat) (regs0 : bvmap 5 word) (E0 E : env) (ms ms0 : machine_state)
    (mdc : Model) (i : Z) (Q : world tfibsegs -> config -> Prop),
  (Z.to_nat (l - i) <= n)%nat -> 0 <= i -> i < l -> i mod 3 = 0 ->
  crt5_head_at regs0 E ms mdc i ->
  (forall n, (n < 51)%nat -> ew E n = ew E0 n) ->
  (forall x : word, ~ (want <= bv_unsigned x < want + i / 3 * 4) -> ms_mem ms x = ms_mem ms0 x) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms)) ->
  crt5_KL regs0 E0 ms0 Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
induction n as [|n IH]; intros regs0 E0 E ms ms0 mdc i Q Hn Hi0 Hil Hm3 HH Hag Hk Hg KL.
- lia.
- pose proof (crt5_q_room i ltac:(lia) Hm3) as Hroom.
  apply (crt5_trip regs0 E ms mdc i Q Hi0 Hil Hm3 HH).
  + (* back edge: one more trip *)
    intros E' ms' mdc' HHead Hag' Hk' Hg'.
    pose proof HHead as HH'.
    destruct HH' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hi0' & Hil' & Hm3').
    apply (IH regs0 E0 E' ms' ms0 mdc' (i + 3) Q ltac:(lia) Hi0' Hil' Hm3' HHead
             (crt5_ag_trans _ _ _ Hag Hag')).
    * replace (want + (i + 3) / 3 * 4) with (want + i / 3 * 4 + 4) by (Z.div_mod_to_equations; lia).
      exact (crt5_keep_widen _ _ _ want (want + i / 3 * 4) (want + i / 3 * 4 + 4)
               ltac:(Z.div_mod_to_equations; lia) ltac:(lia) Hk Hk').
    * exact (mem_grows_trans _ _ _ Hg Hg').
    * exact KL.
  + (* the trip ends the loop *)
    intros E' ms' mdc' HX Hag' Hk' Hg'.
    pose proof HX as HXc.
    destruct HX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlast & _).
    apply (KL E' ms' mdc' i (want + i / 3 * 4) HXc (crt5_ag_trans _ _ _ Hag Hag'));
      [ | exact (mem_grows_trans _ _ _ Hg Hg') ].
    replace (want + En) with (want + i / 3 * 4 + 4) by (rewrite HEN; Z.div_mod_to_equations; lia).
    exact (crt5_keep_widen _ _ _ want (want + i / 3 * 4) (want + i / 3 * 4 + 4)
             ltac:(Z.div_mod_to_equations; lia) ltac:(lia) Hk Hk').
Qed.
(* the whole loop, from its head at i = 0 *)
Lemma crt5_loop_run : forall (regs0 : bvmap 5 word) (E : env) (ms : machine_state) (mdc : Model)
    (Q : world tfibsegs -> config -> Prop),
  crt5_head_at regs0 E ms mdc 0 -> crt5_KL regs0 E ms Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros regs0 E ms mdc Q HH KL.
apply (crt5_loop (Z.to_nat l) regs0 E E ms ms mdc 0 Q ltac:(lia) ltac:(lia) ltac:(lia)
         ltac:(reflexivity) HH ltac:(intros n Hn; reflexivity)).
- intros x Hx. reflexivity.
- apply mem_grows_refl.
- exact KL.
Qed.

End Walk.

(* ================= the segment: crt_INV_81d0c -> crt_INV_81f58 ================= *)
Section Seg5.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* the state the walk hands the loop at 0x81e18: the four regions every loop boundary carries (B: the s1 slots
   crt_cs1L, crt_cs1e plus the loop path's spills 0x28 := En and 0x38 := F, 0x81ddc / 0x81de0), and the loop's own
   register shape *)
Definition crt5_ssIn : sstate :=
  mkSS 0x81e18 crt5_regsH (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF) None
    (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5);
              (47%nat, mkAF 4096 (2 ^ 47) 5)] [] []).



(* ---- the entry re-key: the chain's boundary state crt_ss_ret 0x81e18 (every register an atom) becomes the loop's
   own state crt5_ssIn. The register picture differs in two ways: the literal registers (B: x5 x6 x7 x16 x17 x29, the
   alphabet constants and a7 = -1), whose values crt_INV_81d0c pins, and the walk's own atoms from 51 on. The regions
   and the atom facts of the two states are the same term. ---- *)
(* the values of atoms 51 .. 82 at the loop's entry: the loop's own numbers at i = 0, then the registers the walk
   carries (same layout as crt5_vs), then bd + 1 and ~bd *)
Definition crt5_vsIn (cx : crt_cx) (E : env) : list word :=
  [Z_to_bv 64 (Z.of_nat (length (c_bs cx))); Z_to_bv 64 (c_bd cx); Z_to_bv 64 0; Z_to_bv 64 (c_want cx);
   Z_to_bv 64 (c_bd cx);
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   ew E 1; ew E 10; ew E 11; ew E 12; ew E 22; ew E 24; ew E 25; ew E 23; ew E 27; ew E 28; ew E 30;
   Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (c_bd cx + 1); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
   Z_to_bv 64 (2 ^ 64 - 1 - c_bd cx)].
Lemma crt5_ewIn_lo : forall cx E n, (n < 51)%nat -> ew (havoc E 51 (crt5_vsIn cx E)) n = ew E n.
Proof. intros cx E n Hn. apply ew_havoc_old. exact Hn. Qed.
Lemma crt5_ewIn_hi : forall cx E n, (51 <= n)%nat ->
  ew (havoc E 51 (crt5_vsIn cx E)) n = nth (n - 51) (crt5_vsIn cx E) (ew E n).
Proof.
intros cx E n Hn. unfold havoc. cbn [ew].
destruct (Nat.ltb_spec n 51) as [Hc|Hc]; [lia|reflexivity].
Qed.

Definition crt5_ssEntry : sstate := crt_ss_ret 0x81e18 crt_cs1L crt_csF.

(* the two ways a register of the loop's state reads the same as at the boundary: the same symbolic value, or one
   of the walk's own atoms (>= 51), whose value the vector pins *)
Lemma crt5_in_same : forall cx E (r : bv 5) (v : sv),
  sr_get crt5_regsH r = v -> sr_get (ss_regs crt5_ssEntry) r = v ->
  sv_denot (havoc E 51 (crt5_vsIn cx E)) (sr_get crt5_regsH r)
    = sv_denot (havoc E 51 (crt5_vsIn cx E)) (sr_get (ss_regs crt5_ssEntry) r).
Proof. intros cx E r v H1 H2. rewrite H1, H2. reflexivity. Qed.
Lemma crt5_in_hi : forall cx E (W3 : world tfibsegs) (ms3 : machine_state) (r : bv 5) (m n : nat),
  sr_get crt5_regsH r = SOff m 0 -> (51 <= m)%nat ->
  sr_get (ss_regs crt5_ssEntry) r = SOff n 0 -> (n < 51)%nat ->
  nth (m - 51) (crt5_vsIn cx E) (ew E m) = YK11.getr (ms_regs ms3) r ->
  st_ok tfibsegs E crt5_ssEntry (restrict (w_H W3) ms3) ->
  sv_denot (havoc E 51 (crt5_vsIn cx E)) (sr_get crt5_regsH r)
    = sv_denot (havoc E 51 (crt5_vsIn cx E)) (sr_get (ss_regs crt5_ssEntry) r).
Proof.
intros cx E W3 ms3 r m n H1 Hm H2 Hn Hv HS.
rewrite H1, H2. cbn [sv_denot]. rewrite !Z.add_0_r, !lit_of_word.
rewrite crt5_ewIn_hi by exact Hm. rewrite crt5_ewIn_lo by exact Hn.
rewrite Hv. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt5_ssEntry ms3 r HS), H2, fsw_SOff0.
reflexivity.
Qed.
Lemma crt5_in_lit : forall cx E (W3 : world tfibsegs) (ms3 : machine_state) (r : bv 5) (z : Z) (n : nat),
  st_ok tfibsegs E crt5_ssEntry (restrict (w_H W3) ms3) ->
  sr_get crt5_regsH r = SLit z -> sr_get (ss_regs crt5_ssEntry) r = SOff n 0 -> (n < 51)%nat ->
  YK11.getr (ms_regs ms3) r = Z_to_bv 64 z ->
  sv_denot (havoc E 51 (crt5_vsIn cx E)) (sr_get crt5_regsH r)
    = sv_denot (havoc E 51 (crt5_vsIn cx E)) (sr_get (ss_regs crt5_ssEntry) r).
Proof.
intros cx E W3 ms3 r z n HS H1 H2 Hn Hr.
rewrite H1, H2. cbn [sv_denot]. rewrite Z.add_0_r, lit_of_word.
rewrite crt5_ewIn_lo by exact Hn.
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt5_ssEntry ms3 r HS), H2, fsw_SOff0 in Hr.
rewrite Hr. reflexivity.
Qed.

Lemma crt5_toIn : forall (cx : crt_cx) (E : env) (W3 : world tfibsegs) (ms3 : machine_state) k ly3 S3 U3 md3,
  crt_INV_81d0c B cx E k ly3 S3 U3 W3 ms3 md3 ->
  st_ok tfibsegs E crt5_ssEntry (restrict (w_H W3) ms3) ->
  st_ok tfibsegs (havoc E 51 (crt5_vsIn cx E)) crt5_ssIn (restrict (w_H W3) ms3).
Proof.
intros cx E W3 ms3 k ly3 S3 U3 md3 HINV HS.
destruct HINV as (R19 & R22 & R31 & R13 & R15 & R20 & R21 & R18 & R14 & R17 & R16 & R5 & R6 & R7 & R29 & HMEM).
assert (Ea : forall (r : bv 5) (n : nat), sr_get (ss_regs crt5_ssEntry) r = SOff n 0 ->
          ew E n = YK11.getr (ms_regs ms3) r).
{ intros r n Hr. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt5_ssEntry ms3 r HS), Hr, fsw_SOff0.
  reflexivity. }
pose proof (st_ok_agree tfibsegs 51%nat E (havoc E 51 (crt5_vsIn cx E)) crt5_ssEntry _ HS
              (env_agree_havoc E 51 (crt5_vsIn cx E)) ltac:(vm_compute; reflexivity)) as HS1.
apply (st_ok_regs tfibsegs (havoc E 51 (crt5_vsIn cx E)) crt5_ssEntry _ crt5_regsH HS1).
intros r. destruct (crt5_bv5_cases r) as
  [Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|
   [Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|Er]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  subst r.
- exact (crt5_in_same cx E (Z_to_bv 5 0) _ ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 1) 65%nat 1%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 1) 1%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_same cx E (Z_to_bv 5 2) _ ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)).
- exact (crt5_in_same cx E (Z_to_bv 5 3) _ ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)).
- exact (crt5_in_same cx E (Z_to_bv 5 4) _ ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)).
- exact (crt5_in_lit cx E W3 ms3 (Z_to_bv 5 5) 25 5%nat HS ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(lia) R5).
- exact (crt5_in_lit cx E W3 ms3 (Z_to_bv 5 6) 51 6%nat HS ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(lia) R6).
- exact (crt5_in_lit cx E W3 ms3 (Z_to_bv 5 7) 61 7%nat HS ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(lia) R7).
- exact (crt5_in_same cx E (Z_to_bv 5 8) _ ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)).
- exact (crt5_in_same cx E (Z_to_bv 5 9) _ ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 10) 66%nat 10%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 10) 10%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 11) 67%nat 11%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 11) 11%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 12) 68%nat 12%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 12) 12%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 13) 53%nat 13%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; symmetry; exact R13) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 14) 82%nat 14%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; symmetry; exact R14) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 15) 77%nat 15%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; symmetry; exact R15) HS).
- exact (crt5_in_lit cx E W3 ms3 (Z_to_bv 5 16) 103 16%nat HS ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(lia) R16).
- exact (crt5_in_lit cx E W3 ms3 (Z_to_bv 5 17) 18446744073709551615 17%nat HS ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(lia) R17).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 18) 76%nat 18%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; symmetry; exact R18) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 19) 54%nat 19%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; symmetry; exact R19) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 20) 51%nat 20%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; symmetry; exact R20) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 21) 52%nat 21%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; symmetry; exact R21) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 22) 69%nat 22%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 22) 22%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 23) 72%nat 23%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 23) 23%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 24) 70%nat 24%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 24) 24%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 25) 71%nat 25%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 25) 25%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_same cx E (Z_to_bv 5 26) _ ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity)).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 27) 73%nat 27%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 27) 27%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 28) 74%nat 28%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 28) 28%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_lit cx E W3 ms3 (Z_to_bv 5 29) 207 29%nat HS ltac:(vm_compute; reflexivity)
           ltac:(vm_compute; reflexivity) ltac:(lia) R29).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 30) 75%nat 30%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; exact (Ea (Z_to_bv 5 30) 30%nat ltac:(vm_compute; reflexivity))) HS).
- exact (crt5_in_hi cx E W3 ms3 (Z_to_bv 5 31) 54%nat 31%nat ltac:(vm_compute; reflexivity)
           ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia)
           ltac:(cbn [crt5_vsIn nth Nat.sub]; symmetry; exact R31) HS).
Qed.

(* the four ways a register the loop does not write keeps its value across the loop *)
Lemma crt5_lit_keep : forall (W3 : world tfibsegs) (E E' : env) (ms3 ms' : machine_state) (r : bv 5) (z : Z),
  st_ok tfibsegs E crt5_ssIn (restrict (w_H W3) ms3) ->
  st_ok tfibsegs E' crt5_ssOut (restrict (w_H W3) ms') ->
  sr_get (ss_regs crt5_ssOut) r = SLit z -> sr_get (ss_regs crt5_ssIn) r = SLit z ->
  YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r.
Proof.
intros W3 E E' ms3 ms' r z HSin HSout H1 H2.
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E' crt5_ssOut ms' r HSout), H1.
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt5_ssIn ms3 r HSin), H2.
reflexivity.
Qed.
Lemma crt5_atom_keep : forall (W3 : world tfibsegs) (E E' : env) (ms3 ms' : machine_state) (r : bv 5) (n : nat),
  st_ok tfibsegs E crt5_ssIn (restrict (w_H W3) ms3) ->
  st_ok tfibsegs E' crt5_ssOut (restrict (w_H W3) ms') ->
  sr_get (ss_regs crt5_ssOut) r = SOff n 0 -> sr_get (ss_regs crt5_ssIn) r = SOff n 0 ->
  ew E' n = ew E n ->
  YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r.
Proof.
intros W3 E E' ms3 ms' r n HSin HSout H1 H2 Hn.
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E' crt5_ssOut ms' r HSout), H1, fsw_SOff0.
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt5_ssIn ms3 r HSin), H2, fsw_SOff0.
exact Hn.
Qed.
Lemma crt5_pin_keep : forall (W3 : world tfibsegs) (E' : env) (ms3 ms' : machine_state) (r : bv 5) (n : nat)
    (v : word),
  st_ok tfibsegs E' crt5_ssOut (restrict (w_H W3) ms') ->
  sr_get (ss_regs crt5_ssOut) r = SOff n 0 -> ew E' n = v -> YK11.getr (ms_regs ms3) r = v ->
  YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r.
Proof.
intros W3 E' ms3 ms' r n v HSout H1 Hn Hr.
rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E' crt5_ssOut ms' r HSout), H1, fsw_SOff0, Hn.
symmetry. exact Hr.
Qed.

(* the registers the loop does not write keep their value: each is a literal, one of crt_E's atoms (kept by
   every re-key), or one of the walk's atoms whose value the exit state pins (B: a4 = ~bd at 82, a5 = bd + 1 at 77,
   the passive s8 / s9 at 70 / 71) *)
Lemma crt5_kept_regs : forall (W3 : world tfibsegs) (E E' : env) (ms3 ms' : machine_state) (bd l : Z),
  st_ok tfibsegs E crt5_ssIn (restrict (w_H W3) ms3) ->
  st_ok tfibsegs E' crt5_ssOut (restrict (w_H W3) ms') ->
  (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
  ew E' 51 = Z_to_bv 64 l -> ew E' 52 = Z_to_bv 64 bd -> ew E' 76 = Z_to_bv 64 SHADOW_OFF ->
  ew E' 77 = Z_to_bv 64 (bd + 1) -> ew E' 82 = Z_to_bv 64 (2 ^ 64 - 1 - bd) ->
  ew E' 70 = YK11.getr (ms_regs ms3) 24%bv -> ew E' 71 = YK11.getr (ms_regs ms3) 25%bv ->
  YK11.getr (ms_regs ms3) 20%bv = Z_to_bv 64 l -> YK11.getr (ms_regs ms3) 21%bv = Z_to_bv 64 bd ->
  YK11.getr (ms_regs ms3) 18%bv = Z_to_bv 64 SHADOW_OFF ->
  YK11.getr (ms_regs ms3) 15%bv = Z_to_bv 64 (bd + 1) ->
  YK11.getr (ms_regs ms3) 14%bv = Z_to_bv 64 (2 ^ 64 - 1 - bd) ->
  forall r : bv 5, ~ In r crt5_clob -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r.
Proof.
intros W3 E E' ms3 ms' bd l HSin HSout Hag A51 A52 A76 A77 A82 A70 A71 R20 R21 R18 R15 R14 r Hr.
destruct (crt5_bv5_cases r) as
  [Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|
   [Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|Er]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  subst r.
- exact (crt5_lit_keep W3 E E' ms3 ms' (Z_to_bv 5 0) 0 HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
- exfalso; apply Hr; cbn [In crt5_clob]; left; apply bv_eq; vm_compute; reflexivity.
- exact (crt5_atom_keep W3 E E' ms3 ms' (Z_to_bv 5 2) 2%nat HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (Hag 2%nat ltac:(lia))).
- exact (crt5_atom_keep W3 E E' ms3 ms' (Z_to_bv 5 3) 3%nat HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (Hag 3%nat ltac:(lia))).
- exact (crt5_atom_keep W3 E E' ms3 ms' (Z_to_bv 5 4) 4%nat HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (Hag 4%nat ltac:(lia))).
- exact (crt5_lit_keep W3 E E' ms3 ms' (Z_to_bv 5 5) 25 HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
- exact (crt5_lit_keep W3 E E' ms3 ms' (Z_to_bv 5 6) 51 HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
- exact (crt5_lit_keep W3 E E' ms3 ms' (Z_to_bv 5 7) 61 HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
- exact (crt5_atom_keep W3 E E' ms3 ms' (Z_to_bv 5 8) 8%nat HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (Hag 8%nat ltac:(lia))).
- exact (crt5_atom_keep W3 E E' ms3 ms' (Z_to_bv 5 9) 9%nat HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (Hag 9%nat ltac:(lia))).
- exfalso; apply Hr; cbn [In crt5_clob]; do 1 right; left; apply bv_eq; vm_compute; reflexivity.
- exfalso; apply Hr; cbn [In crt5_clob]; do 2 right; left; apply bv_eq; vm_compute; reflexivity.
- exfalso; apply Hr; cbn [In crt5_clob]; do 3 right; left; apply bv_eq; vm_compute; reflexivity.
- exfalso; apply Hr; cbn [In crt5_clob]; do 4 right; left; apply bv_eq; vm_compute; reflexivity.
- exact (crt5_pin_keep W3 E' ms3 ms' (Z_to_bv 5 14) 82%nat _ HSout
    ltac:(vm_compute; reflexivity) A82 R14).
- exact (crt5_pin_keep W3 E' ms3 ms' (Z_to_bv 5 15) 77%nat _ HSout
    ltac:(vm_compute; reflexivity) A77 R15).
- exact (crt5_lit_keep W3 E E' ms3 ms' (Z_to_bv 5 16) 103 HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
- exact (crt5_lit_keep W3 E E' ms3 ms' (Z_to_bv 5 17) 18446744073709551615 HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
- exact (crt5_pin_keep W3 E' ms3 ms' (Z_to_bv 5 18) 76%nat _ HSout
    ltac:(vm_compute; reflexivity) A76 R18).
- exfalso; apply Hr; cbn [In crt5_clob]; do 5 right; left; apply bv_eq; vm_compute; reflexivity.
- exact (crt5_pin_keep W3 E' ms3 ms' (Z_to_bv 5 20) 51%nat _ HSout
    ltac:(vm_compute; reflexivity) A51 R20).
- exact (crt5_pin_keep W3 E' ms3 ms' (Z_to_bv 5 21) 52%nat _ HSout
    ltac:(vm_compute; reflexivity) A52 R21).
- exfalso; apply Hr; cbn [In crt5_clob]; do 6 right; left; apply bv_eq; vm_compute; reflexivity.
- exfalso; apply Hr; cbn [In crt5_clob]; do 7 right; left; apply bv_eq; vm_compute; reflexivity.
- exact (crt5_pin_keep W3 E' ms3 ms' (Z_to_bv 5 24) 70%nat _ HSout
    ltac:(vm_compute; reflexivity) A70 eq_refl).
- exact (crt5_pin_keep W3 E' ms3 ms' (Z_to_bv 5 25) 71%nat _ HSout
    ltac:(vm_compute; reflexivity) A71 eq_refl).
- exact (crt5_atom_keep W3 E E' ms3 ms' (Z_to_bv 5 26) 26%nat HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (Hag 26%nat ltac:(lia))).
- exfalso; apply Hr; cbn [In crt5_clob]; do 8 right; left; apply bv_eq; vm_compute; reflexivity.
- exfalso; apply Hr; cbn [In crt5_clob]; do 9 right; left; apply bv_eq; vm_compute; reflexivity.
- exact (crt5_lit_keep W3 E E' ms3 ms' (Z_to_bv 5 29) 207 HSin HSout
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
- exfalso; apply Hr; cbn [In crt5_clob]; do 10 right; left; apply bv_eq; vm_compute; reflexivity.
- exfalso; apply Hr; cbn [In crt5_clob]; do 11 right; left; apply bv_eq; vm_compute; reflexivity.
Qed.


(* STK_check_round_trip is at least the function's probe window; never COMPUTE it (a Theorem Labs lane 07:3xZ) *)
Lemma crt5_stk_ge : 223 <= STK_check_round_trip.
Proof.
unfold STK_check_round_trip. etransitivity; [|apply Z.le_max_l].
unfold PROBE_check_round_trip, PROBE_PAGE. lia.
Qed.
Lemma crt5_sp1_bounds : forall cx, spZ (c_regs cx) - 223 <= crt_sp1 cx <= spZ (c_regs cx) - 192.
Proof. intros cx. unfold crt_sp1. Z.div_mod_to_equations. lia. Qed.

(* a region of the boundary state survives the loop: its bytes are outside the loop's write window and
   writable_at only grows *)
Lemma crt5_region_keep : forall (W3 : world tfibsegs) (E : env) (m m' : word -> option byte)
    (r : YP09.region) (lo hi : Z),
  region_ok tfibsegs E (mrestrict (w_H W3) m) r ->
  mem_grows (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  (forall o, YP09.r_lo r <= o < YP09.r_hi r ->
     ~ (lo <= base_val E (YP09.r_base r) + o < hi)) ->
  regions_wf [r] = true ->
  region_ok tfibsegs E (mrestrict (w_H W3) m') r.
Proof.
intros W3 E m m' r lo hi (HB1 & HB2 & HW & HC) Hgr Hk Hout Hwf.
split; [exact HB1|]. split; [exact HB2|].
split; [intros o Ho; apply (writable_at_grows _ _ _ _ Hgr); exact (HW o Ho)|].
apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) HC c Hc) as Hck.
cbn [regions_wf region_wf] in Hwf. rewrite Bool.andb_true_r in Hwf.
apply Bool.andb_true_iff in Hwf as [_ Hall].
pose proof (proj1 (forallb_forall _ _) Hall c Hc) as Hin.
unfold chunk_inside in Hin. apply Bool.andb_true_iff in Hin as [Hin0 Hlen].
apply Bool.andb_true_iff in Hin0 as [Hlo Hhi].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hlen.
intros i Hi. destruct (Hck i Hi) as (b & Hcb & Hmb).
exists b. split; [exact Hcb|]. rewrite <- Hmb.
apply (crt5_mbyte_keep W3 m m' (fun a => lo <= a < hi)); [exact Hk| |].
- lia.
- cbv beta. intros Hcon. apply (Hout (YP09.c_off c + i) ltac:(lia)). lia.
Qed.

(* the four regions of the boundary state are outside the loop's write window *)
Lemma crt5_out_window : forall (cx : crt_cx) ly3 S3 (W3 : world tfibsegs) (mem : word -> option byte) (a : Z),
  crt_l5_mem B cx ly3 S3 W3 mem ->
  HState.in_window (spZ (c_regs cx)) STK_check_round_trip a ->
  ~ (c_want cx <= a < c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4).
Proof.
intros cx ly3 S3 W3 mem a HM Hw Hc.
unfold crt_l5_mem in HM. cbv zeta in HM.
destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HST).
exact (HST a ltac:(lia) Hw).
Qed.
Lemma crt5_out_shadow : forall (cx : crt_cx) ly3 S3 (W3 : world tfibsegs) (mem : word -> option byte) (a : Z),
  crt_l5_mem B cx ly3 S3 W3 mem ->
  SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 ->
  ~ (c_want cx <= a < c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4).
Proof.
intros cx ly3 S3 W3 mem a HM Hw Hc.
unfold crt_l5_mem in HM. cbv zeta in HM.
destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSW & _).
exact (HSW a ltac:(lia) Hw).
Qed.
Lemma crt5_out_frame : forall (cx : crt_cx) ly3 S3 (W3 : world tfibsegs) (mem : word -> option byte) (a : Z),
  crt_l5_mem B cx ly3 S3 W3 mem ->
  crt_F cx <= a < crt_F cx + fs_frame_bytes 3 ->
  ~ (c_want cx <= a < c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4).
Proof.
intros cx ly3 S3 W3 mem a HM Hw Hc.
unfold crt_l5_mem in HM. cbv zeta in HM.
destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFR).
lia.
Qed.

(* ---- the exit re-key: the walk's own exit state becomes a boundary state (B: crt_ss_ret 0x82098 crt_cs1L, before the
   reloads; A: crt_ss_ret 0x81f58) ---- *)
Definition crt5_P0 (n : nat) : bool := Nat.leb 32 n && Nat.ltb n 51.
Definition crt5_vsR (ms' : machine_state) : list word :=
  [YK11.getr (ms_regs ms') (Z_to_bv 5 0);
   YK11.getr (ms_regs ms') (Z_to_bv 5 1);
   YK11.getr (ms_regs ms') (Z_to_bv 5 2);
   YK11.getr (ms_regs ms') (Z_to_bv 5 3);
   YK11.getr (ms_regs ms') (Z_to_bv 5 4);
   YK11.getr (ms_regs ms') (Z_to_bv 5 5);
   YK11.getr (ms_regs ms') (Z_to_bv 5 6);
   YK11.getr (ms_regs ms') (Z_to_bv 5 7);
   YK11.getr (ms_regs ms') (Z_to_bv 5 8);
   YK11.getr (ms_regs ms') (Z_to_bv 5 9);
   YK11.getr (ms_regs ms') (Z_to_bv 5 10);
   YK11.getr (ms_regs ms') (Z_to_bv 5 11);
   YK11.getr (ms_regs ms') (Z_to_bv 5 12);
   YK11.getr (ms_regs ms') (Z_to_bv 5 13);
   YK11.getr (ms_regs ms') (Z_to_bv 5 14);
   YK11.getr (ms_regs ms') (Z_to_bv 5 15);
   YK11.getr (ms_regs ms') (Z_to_bv 5 16);
   YK11.getr (ms_regs ms') (Z_to_bv 5 17);
   YK11.getr (ms_regs ms') (Z_to_bv 5 18);
   YK11.getr (ms_regs ms') (Z_to_bv 5 19);
   YK11.getr (ms_regs ms') (Z_to_bv 5 20);
   YK11.getr (ms_regs ms') (Z_to_bv 5 21);
   YK11.getr (ms_regs ms') (Z_to_bv 5 22);
   YK11.getr (ms_regs ms') (Z_to_bv 5 23);
   YK11.getr (ms_regs ms') (Z_to_bv 5 24);
   YK11.getr (ms_regs ms') (Z_to_bv 5 25);
   YK11.getr (ms_regs ms') (Z_to_bv 5 26);
   YK11.getr (ms_regs ms') (Z_to_bv 5 27);
   YK11.getr (ms_regs ms') (Z_to_bv 5 28);
   YK11.getr (ms_regs ms') (Z_to_bv 5 29);
   YK11.getr (ms_regs ms') (Z_to_bv 5 30);
   YK11.getr (ms_regs ms') (Z_to_bv 5 31)].
Lemma crt5_nth_big_w : forall (l : list word) (n : nat) (d : word), (length l <= n)%nat -> nth n l d = d.
Proof.
induction l as [|x l IH]; intros [|n] d H; cbn [nth length] in *; try lia; try reflexivity.
apply IH. lia.
Qed.
Lemma crt5_ew_vsR_lo : forall (E' : env) (ms' : machine_state) (n : nat),
  (n < 32)%nat -> ew (havoc E' 0 (crt5_vsR ms')) n = nth n (crt5_vsR ms') (ew E' n).
Proof.
intros E' ms' n Hn. unfold havoc. cbn [ew].
destruct (Nat.ltb_spec n 0) as [Hc|Hc]; [lia|]. rewrite Nat.sub_0_r. reflexivity.
Qed.
Lemma crt5_ew_vsR_hi : forall (E' : env) (ms' : machine_state) (n : nat),
  (32 <= n)%nat -> ew (havoc E' 0 (crt5_vsR ms')) n = ew E' n.
Proof.
intros E' ms' n Hn. unfold havoc. cbn [ew].
destruct (Nat.ltb_spec n 0) as [Hc|Hc]; [lia|]. rewrite Nat.sub_0_r.
apply crt5_nth_big_w. unfold crt5_vsR. cbn [length]. lia.
Qed.

(* the atoms the four boundary regions read: the three stack / frame bases and crt_E's extra atoms *)
Definition crt5_Pr (n : nat) : bool :=
  Nat.eqb n 8 || Nat.eqb n 9 || Nat.eqb n 26 || (Nat.leb 32 n && Nat.ltb n 51).
Lemma crt5_toRet : forall (cx : crt_cx) (E E' : env) (ms3 ms' : machine_state) ly3 S3 (W3 : world tfibsegs),
  st_ok tfibsegs E crt5_ssIn (restrict (w_H W3) ms3) ->
  st_ok tfibsegs E' crt5_ssOut (restrict (w_H W3) ms') ->
  (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
  (forall r : bv 5, ~ In r crt5_clob -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r) ->
  crt_E cx E -> crt_l5_mem B cx ly3 S3 W3 (ms_mem ms3) ->
  (forall x : word, ~ (c_want cx <= bv_unsigned x <
                       c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) ->
     ms_mem ms' x = ms_mem ms3 x) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms')) ->
  env_agree_pd crt5_Pr (fun _ : nat => false) E (havoc E' 0 (crt5_vsR ms')).
Proof.
intros cx E E' ms3 ms' ly3 S3 W3 HSin HSout Hag Hkr HE HM Hkeep Hgr.
split; [|intros d Hd; discriminate Hd].
intros n Hn. unfold crt5_Pr in Hn.
assert (Hhi : (32 <= n)%nat -> ew (havoc E' 0 (crt5_vsR ms')) n = ew E n)
  by (intros H32; rewrite crt5_ew_vsR_hi by lia; apply Hag;
      apply Bool.orb_true_iff in Hn as [Hn|Hn];
      [ apply Bool.orb_true_iff in Hn as [Hn|Hn];
        [ apply Bool.orb_true_iff in Hn as [Hn|Hn]; apply Nat.eqb_eq in Hn; lia
        | apply Nat.eqb_eq in Hn; lia ]
      | apply Bool.andb_true_iff in Hn as [_ Hn]; apply Nat.ltb_lt in Hn; lia ]).
destruct (Nat.leb_spec 32 n) as [H32|H32]; [exact (Hhi H32)|].
apply Bool.orb_true_iff in Hn as [Hn|Hn];
  [ apply Bool.orb_true_iff in Hn as [Hn|Hn];
    [ apply Bool.orb_true_iff in Hn as [Hn|Hn]; apply Nat.eqb_eq in Hn; subst n
    | apply Nat.eqb_eq in Hn; subst n ]
  | apply Bool.andb_true_iff in Hn as [Hn _];
    first [discriminate Hn | (apply Nat.leb_le in Hn; exfalso; lia)] ].
- rewrite crt5_ew_vsR_lo by lia. unfold crt5_vsR. cbn [nth].
  rewrite (Hkr (Z_to_bv 5 8) ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc];
      [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]); exact Hc)).
  exact (crt5_regv W3 E crt5_ssIn ms3 (Z_to_bv 5 8) 8%nat (ew E 8%nat) HSin
           ltac:(vm_compute; reflexivity) eq_refl).
- rewrite crt5_ew_vsR_lo by lia. unfold crt5_vsR. cbn [nth].
  rewrite (Hkr (Z_to_bv 5 9) ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc];
      [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]); exact Hc)).
  exact (crt5_regv W3 E crt5_ssIn ms3 (Z_to_bv 5 9) 9%nat (ew E 9%nat) HSin
           ltac:(vm_compute; reflexivity) eq_refl).
- rewrite crt5_ew_vsR_lo by lia. unfold crt5_vsR. cbn [nth].
  rewrite (Hkr (Z_to_bv 5 26) ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc];
      [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]); exact Hc)).
  exact (crt5_regv W3 E crt5_ssIn ms3 (Z_to_bv 5 26) 26%nat (ew E 26%nat) HSin
           ltac:(vm_compute; reflexivity) eq_refl).
Qed.

Lemma crt5_seg5_core : forall (cx : crt_cx) (E : env) (k : Z) ly3 S3 (U3 : list (Z * Z))
    (W3 : world tfibsegs) (ms3 : machine_state) md3 (Q : world tfibsegs -> config -> Prop),
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  crt_INV_81d0c B cx E k ly3 S3 U3 W3 ms3 md3 ->
  st_ok tfibsegs E crt5_ssIn (restrict (w_H W3) ms3) ->
  (forall (E' : env) (ms' : machine_state) (md' : Model) (i' q' : Z),
     crt5_exit_at SK B W3 STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 k (c_bd cx) (c_want cx)
       (Z.of_nat (length (c_bs cx))) ((Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) (c_bs cx)
       (ms_regs ms3) E' ms' md' i' q' ->
     (forall n, (n < 51)%nat -> ew E' n = ew E n) ->
     (forall x : word, ~ (c_want cx <= bv_unsigned x <
                          c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) ->
        ms_mem ms' x = ms_mem ms3 x) ->
     mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms')) ->
     SRr tfibsegs W3 (mkCfg ms' md') Q) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) Q.
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 Q HJ HARU HINV HS KX.
destruct HINV as (R19 & R22 & R31 & R13 & R15 & R20 & R21 & R18 & R14 & R17 & R16 & R5 & R6 & R7 & R29 & HMEM).
pose proof HMEM as HMEMc. unfold crt_l5_mem in HMEM. cbv zeta in HMEM.
(* the walk's own section variables, read off cx *)
set (bd := c_bd cx) in *. set (want := c_want cx) in *.
set (l := Z.of_nat (length (c_bs cx))) in *. set (En := (l + 2) / 3 * 4) in *.
(* the head state at i = 0 *)
assert (HEAl : crt5_EA_low E (ms_regs ms3)).
{ unfold crt5_EA_low. repeat split;
  match goal with |- ew E ?n = YK11.getr (ms_regs ms3) ?r =>
    symmetry; exact (crt5_regv W3 E crt5_ssIn ms3 r n (ew E n) HS ltac:(vm_compute; reflexivity) eq_refl)
  end. }
destruct (crt5_toHead SK B W3 STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx)
  (c_W cx) (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 k bd want l En (c_bs cx)
  eq_refl ltac:(tauto) eq_refl ltac:(split; tauto) ltac:(split; tauto) ltac:(tauto)
  (ms_regs ms3) E E crt5_ssIn ms3 md3 0 want (Z.min 3 (l - 0))
  ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(rewrite Zdiv_0_l; lia) eq_refl HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(unfold crt5_mregsH; repeat split; assumption)
  ltac:(intros n Hn; reflexivity) HEAl
  ltac:(unfold crt5_memf; split; [|split; [|split]]; tauto)
  ltac:(intros j Hj; rewrite Zdiv_0_l in Hj; cbn in Hj; lia)
  ltac:(split; [exact HJ | exact HARU])) as (E0 & HHead & Hag0).
apply (crt5_loop_run SK B W3 STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx)
  (c_W cx) (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 k bd want l En (c_bs cx)
  eq_refl ltac:(tauto) eq_refl ltac:(split; tauto) ltac:(split; tauto) ltac:(tauto)
  ltac:(tauto) ltac:(tauto) ltac:(tauto)
  (ms_regs ms3) E0 ms3 md3 Q HHead).
intros E' ms' mdc' i' q' HX Hag' Hk' Hg'.
exact (KX E' ms' mdc' i' q' HX (fun n Hn => eq_trans (Hag' n Hn) (Hag0 n Hn)) Hk' Hg').
Qed.
(* ================= the chain form: crt_from 0x820a4 -> crt_from 0x81e18, frame-generic in R ================= *)
(* the exit env: every register of the boundary state is an atom, so it is the machine's own register file, with
   crt_E's nineteen extras unchanged (B: atoms 32 .. 50; the shape L7's crt_l7_seg uses) *)
Lemma crt5_ret_Pr : forall (E : env) (cx : crt_cx) (ms3 ms' : machine_state),
  crt_E cx E -> (forall r : bv 5, ~ In r crt5_clob -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r) ->
  (forall (r : bv 5) (n : nat), sr_get (ss_regs crt5_ssEntry) r = SOff n 0 ->
     ew E n = YK11.getr (ms_regs ms3) r) ->
  env_agree_on crt5_Pr E (Ereg (ms_regs ms') (crt_extra cx)).
Proof.
intros E cx ms3 ms' HE Hkr Ea.
intros n Hn. unfold crt5_Pr in Hn.
apply Bool.orb_true_iff in Hn as [Hn|Hn];
  [ apply Bool.orb_true_iff in Hn as [Hn|Hn];
    [ apply Bool.orb_true_iff in Hn as [Hn|Hn]; apply Nat.eqb_eq in Hn; subst n
    | apply Nat.eqb_eq in Hn; subst n ]
  | apply Bool.andb_true_iff in Hn as (Hn1 & Hn2); apply Nat.leb_le in Hn1; apply Nat.ltb_lt in Hn2 ].
- rewrite (ew_Ereg_nat (ms_regs ms') _ 8 8%bv eq_refl).
  rewrite (Hkr 8%bv ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc]; [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]);
    exact Hc)).
  symmetry. exact (Ea 8%bv 8%nat ltac:(vm_compute; reflexivity)).
- rewrite (ew_Ereg_nat (ms_regs ms') _ 9 9%bv eq_refl).
  rewrite (Hkr 9%bv ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc]; [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]);
    exact Hc)).
  symmetry. exact (Ea 9%bv 9%nat ltac:(vm_compute; reflexivity)).
- rewrite (ew_Ereg_nat (ms_regs ms') _ 26 26%bv eq_refl).
  rewrite (Hkr 26%bv ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc]; [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]);
    exact Hc)).
  symmetry. exact (Ea 26%bv 26%nat ltac:(vm_compute; reflexivity)).
- replace n with (32 + (n - 32))%nat by lia.
  rewrite ew_Ereg_extra. symmetry.
  exact (crt_E_extra cx E (n - 32)%nat HE ltac:(unfold crt_nextra; lia)).
Qed.

(* the four regions of the boundary state lie outside the loop's write window [want, want + En) *)
Lemma crt5_regions_out : forall (cx : crt_cx) (E : env) ly3 S3 (W3 : world tfibsegs) (ms3 : machine_state)
    U3 md3 k r o,
  crt_E cx E -> crt_l5_mem B cx ly3 S3 W3 (ms_mem ms3) ->
  crt_J SK B cx ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k -> ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  In r (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF) ->
  YP09.r_lo r <= o < YP09.r_hi r ->
  ~ (c_want cx <= base_val E (YP09.r_base r) + o <
     c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4).
Proof.
intros cx E ly3 S3 W3 ms3 U3 md3 k r o HE HM HJ HARU Hfr Hin Ho.
pose proof HE as (EE2 & _ & _ & EE8 & EE9 & EE26 & _).
pose proof (crt_E_F cx E HE) as EE47.
pose proof (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfr)
  as (_ & F4096 & Fceil & _ & FS1 & FS2).
pose proof alloc_ceiling_val as HAC.
pose proof crt5_stk_ge as HSTK.
pose proof (crt5_sp1_bounds cx) as (HP1 & HP2).
assert (EE47u : bv_unsigned (ew E 47) = crt_F cx)
  by (rewrite EE47; apply unsigned_lit_small; lia).
cbn [In crt_ret_regions] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
  cbn [crt_s0_region fs_ret_s0_region crt_slot_region crt_frame_region crt_shadow_region
       YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ho |- *.
- rewrite EE8. apply (crt5_out_window cx ly3 S3 W3 (ms_mem ms3)); [exact HM|].
  unfold HState.in_window. lia.
- rewrite EE9. apply (crt5_out_window cx ly3 S3 W3 (ms_mem ms3)); [exact HM|].
  unfold HState.in_window. lia.
- rewrite EE47u. apply (crt5_out_frame cx ly3 S3 W3 (ms_mem ms3)); [exact HM|]. lia.
- rewrite EE26. apply (crt5_out_shadow cx ly3 S3 W3 (ms_mem ms3)); [exact HM|].
  rewrite crt_frame3 in Ho. change (512 / 8) with 64 in Ho.
  change (2 ^ 44) with 17592186044416.
  unfold SHADOW_OFF. unfold kLowMemEnd in FS1. unfold kHighShadowEnd in FS2. lia.
Qed.

(* the last trip writes the last quad: q + 4 = want + En *)
Lemma crt5_En_last : forall l i q want, 0 <= i -> i < l -> i mod 3 = 0 -> l <= i + 3 -> q = want + i / 3 * 4 ->
  q + 4 = want + (l + 2) / 3 * 4.
Proof. intros l i q want H0 H1 H2 H3 ->. Z.div_mod_to_equations. lia. Qed.
Lemma crt5_En_nonneg : forall l, 0 <= l -> 0 <= (l + 2) / 3 * 4.
Proof. intros l Hl. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia]. Qed.

(* ---- the exit's three slot reloads (B only; A's loop exit 0x81f54 `addi a0, t4, 4` reaches its join 0x81f58
   directly): 0x82098 `ld s3, 0x38(s1)`, 0x8209c `ld s6, 0x10(s1)`, 0x820a0 `ld s11, 0x28(s1)`, run from the boundary
   at 0x82098 (a0 = q + 4 already, 0x82094) over the s1 slots crt_cs1L (the loop path's spills 0x38 := F and
   0x28 := En) as a READ-ONLY region, so the run's frame keeps all of memory, to the join 0x820a4 ---- *)
Definition crt5_slot_ro : YP09.region := YP09.mkRegion (Some 9%nat) 0x10 0x58 0 0 crt_cs1L.
Definition crt5_ssX : sstate :=
  mkSS 0x82098 (ss_regs (crt_ss_ret 0x82098 crt_cs1L crt_csF)) [crt5_slot_ro] None
    (ss_facts (crt_ss_ret 0x82098 crt_cs1L crt_csF)).
Definition crt5_ssY : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL 0x820a4 crt5_ssX).
Lemma crt5_runXY : sym_run_toN tfibsegs crt_tbl FUEL 0x820a4 crt5_ssX = (crt5_ssY, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crt5_ssY_shape :
  ss_pc crt5_ssY = 0x820a4 /\ ss_resv crt5_ssY = None /\
  map (fun q => sr_get (ss_regs crt5_ssY) q) [10; 18; 19; 22; 27]%bv =
    [SOff 10 0; SOff 18 0; SOff 47 0; SOff 47 0; SOff 50 0].
Proof. repeat split; vm_compute; reflexivity. Qed.
(* the reloads write a0 s3 s6 s11 only, all in crt5_clob *)
Lemma crt5_ssY_regs : forall r : bv 5, ~ In r crt5_clob ->
  sr_get (ss_regs crt5_ssY) r = sr_get (ss_regs crt5_ssX) r.
Proof.
intros r Hr. destruct (crt5_bv5_cases r) as
  [Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|
   [Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|[Er|Er]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  subst r;
  first [ vm_compute; reflexivity
        | exfalso; apply Hr; cbn [In crt5_clob];
          repeat (first [ left; solve [apply bv_eq; vm_compute; reflexivity] | right ]) ].
Qed.
Lemma crt5_awr_ro : forall cx E ly3 S3,
  awr_ok tfibsegs B E [crt5_slot_ro] STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)).
Proof.
intros cx E ly3 S3 a (r & Hin & Hr). exfalso.
destruct Hin as [<-|[]]. cbn [crt5_slot_ro YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.
Lemma crt5_frame_ro : forall E (m m' : word -> option byte), frame_of E [crt5_slot_ro] m m' -> m' = m.
Proof.
intros E m m' HF. apply functional_extensionality. intros x. apply HF.
intros (r & Hin & Hw). destruct Hin as [<-|[]]. cbn [crt5_slot_ro YP09.r_wlo YP09.r_whi] in Hw. lia.
Qed.
(* the exit env of a machine whose registers outside crt5_clob are the entry's is a crt_E env *)
Lemma crt5_E_exit : forall (E : env) (cx : crt_cx) (ms3 ms' : machine_state),
  crt_E cx E -> (forall r : bv 5, ~ In r crt5_clob -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r) ->
  (forall (r : bv 5) (n : nat), sr_get (ss_regs crt5_ssEntry) r = SOff n 0 ->
     ew E n = YK11.getr (ms_regs ms3) r) ->
  env_agree_on crt5_Pr E (Ereg (ms_regs ms') (crt_extra cx)) /\ crt_E cx (Ereg (ms_regs ms') (crt_extra cx)).
Proof.
intros E cx ms3 ms' HE Hkr Ea.
assert (HAGE : env_agree_on crt5_Pr E (Ereg (ms_regs ms') (crt_extra cx))) by (apply (crt5_ret_Pr E cx ms3 ms'); assumption).
split; [exact HAGE|].
pose proof HE as (C2 & C3 & C4 & C8 & C9 & C26 & CX).
split; [|split; [|split; [|split; [|split; [|split]]]]].
- rewrite (ew_Ereg_nat (ms_regs ms') (crt_extra cx) 2 2%bv eq_refl).
  rewrite (Hkr 2%bv ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc]; [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]);
    exact Hc)).
  rewrite <- (Ea 2%bv 2%nat ltac:(vm_compute; reflexivity)). exact C2.
- rewrite (ew_Ereg_nat (ms_regs ms') (crt_extra cx) 3 3%bv eq_refl).
  rewrite (Hkr 3%bv ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc]; [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]);
    exact Hc)).
  rewrite <- (Ea 3%bv 3%nat ltac:(vm_compute; reflexivity)). exact C3.
- rewrite (ew_Ereg_nat (ms_regs ms') (crt_extra cx) 4 4%bv eq_refl).
  rewrite (Hkr 4%bv ltac:(cbn [In crt5_clob]; intros Hc;
    repeat (destruct Hc as [Hc|Hc]; [apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate|]);
    exact Hc)).
  rewrite <- (Ea 4%bv 4%nat ltac:(vm_compute; reflexivity)). exact C4.
- rewrite (HAGE 8%nat eq_refl). exact C8.
- rewrite (HAGE 9%nat eq_refl). exact C9.
- rewrite (HAGE 26%nat eq_refl). exact C26.
- intros j Hj. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* ---- lane L5: the segment lemma, frame-generic in R (the walk's design, a Theorem Labs lane 05:2xZ). The boundary states
   are B's: crt_ss_ret 0x81e18 crt_cs1L crt_csF at the loop head (crtA_from_entry's loop-arm premise) and
   crt_ss_ret 0x820a4 crt_cs1e crt_csF at the join (A23's a23_seg6 start), all registers atoms ---- *)
Theorem crt5_seg5 : forall R : crt_inv,
  crt5_stable R ->
  crt_from SK B (crt_ss_ret 0x820a4 crt_cs1e crt_csF)
    (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
       crt_INV_81f58 B cx E k ly3 S3 U3 W3 ms3 md3 /\ R cx E k ly3 S3 U3 W3 ms3 md3) ->
  crt_from SK B (crt_ss_ret 0x81e18 crt_cs1L crt_csF)
    (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
       crt_INV_81d0c B cx E k ly3 S3 U3 W3 ms3 md3 /\ R cx E k ly3 S3 U3 W3 ms3 md3).
Proof.
intros R HST HNEXT cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFR (HINV & HR) HS.
pose proof HFR as (Hfr & Hfr2 & Hflag).
pose proof asan_consts as ((AC1 & AC2) & _ & _ & _ & _).
pose proof alloc_ceiling_val as HAC.
pose proof crt5_stk_ge as HSTK.
(* the machine's registers at the entry, read off the boundary state's atoms *)
assert (Ea : forall (r : bv 5) (n : nat), sr_get (ss_regs crt5_ssEntry) r = SOff n 0 ->
          ew E n = YK11.getr (ms_regs ms3) r).
{ intros r n Hr. rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E crt5_ssEntry ms3 r HS), Hr, fsw_SOff0.
  reflexivity. }
pose proof HINV as HINVc.
destruct HINVc as (R19 & R22 & R31 & R13 & R15 & R20 & R21 & R18 & R14 & R17 & R16 & R5 & R6 & R7 & R29 & HMEM).
(* the entry re-key: the loop's own state, under the walk's env *)
pose proof (crt5_toIn cx E W3 ms3 k ly3 S3 U3 md3 HINV HS) as HSin.
set (E1 := havoc E 51 (crt5_vsIn cx E)) in HSin.
assert (Hag1 : forall n, (n < 51)%nat -> ew E1 n = ew E n) by (intros n Hn; apply crt5_ewIn_lo; exact Hn).
(* the boundary state's regions and facts, at the entry *)
assert (HMO : mem_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3))
                (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF))
  by exact (st_ok_mem_ok tfibsegs E crt5_ssEntry _ HS).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & HFACTS).
(* run the loop *)
apply (crt5_seg5_core cx E1 k ly3 S3 U3 W3 ms3 md3 _ HJ HARU HINV HSin).
intros E' ms' md' i' q' HX Hag' Hk' Hgr.
(* the loop's whole transition, as crt5_stable reads it *)
pose proof HX as (HSout & HEAl' & X76 & X51 & X52 & X77 & X80 & X81 & X54 & HMF' & HOUT' & HJR' & HMO' &
                  Hi0 & Hil & Him & Hle & Hq).
destruct HEAl' as (L2 & L3 & L4 & L8 & L9 & L26 & L70 & L71).
pose proof HMO' as (O20 & O21 & O13 & O10 & O19 & O22 & O31 & O18 & O15 & O14 & O24 & O25).
assert (Hag'E : forall n, (n < 51)%nat -> ew E' n = ew E n)
  by (intros n Hn; rewrite (Hag' n Hn); apply Hag1; exact Hn).
assert (X82 : ew E' 82 = Z_to_bv 64 (2 ^ 64 - 1 - c_bd cx)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E' crt5_ssOut ms' 14%bv HSout) in O14.
  change (sr_get (ss_regs crt5_ssOut) 14%bv) with (SOff 82 0) in O14. rewrite fsw_SOff0 in O14. exact O14. }
assert (Hkr : forall r : bv 5, ~ In r crt5_clob -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms3) r).
{ exact (crt5_kept_regs W3 E1 E' ms3 ms' (c_bd cx) (Z.of_nat (length (c_bs cx))) HSin HSout Hag'
           X51 X52 X76 X77 X82 L70 L71 R20 R21 R18 R15 R14). }
(* the exit env at 0x82098: the machine's registers, with crt_E's extras *)
destruct (crt5_E_exit E cx ms3 ms' HE Hkr Ea) as (HAGE & HE2).
pose proof HMEM as HMEMk.
destruct HMEMk as (MG & MRAb & MRAw & MWR & MAWR & (ML1 & ML2) & MBD1 & MBD2 & MWT1 & MWT2 & MDJ & MSHb &
                   MSHw & MFRd & MWIN).
(* the four boundary regions, carried across the loop's write window, then read under the exit env *)
assert (HMOE : mem_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms'))
                 (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF)).
{ destruct HMO as (Hwf & Hrok & Hpd). rewrite Forall_forall in Hrok.
  split; [exact Hwf|]. split; [|exact Hpd].
  apply Forall_forall. intros r Hin.
  apply (crt5_region_keep W3 E (ms_mem ms3) (ms_mem ms') r (c_want cx)
           (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4));
    [ exact (Hrok r Hin) | exact Hgr | exact Hk'
    | intros o Ho;
      exact (crt5_regions_out cx E ly3 S3 W3 ms3 U3 md3 k r o HE HMEM HJ HARU Hfr Hin Ho)
    | cbn [In crt_ret_regions] in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity ]. }
assert (HMA : mem_atoms_in crt5_Pr (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF) = true)
  by (vm_compute; reflexivity).
pose proof (mem_ok_agree_on tfibsegs crt5_Pr E (Ereg (ms_regs ms') (crt_extra cx))
              (mrestrict (w_H W3) (ms_mem ms')) (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF)
              HAGE HMA HMOE) as HMO2.
assert (HFA : facts_atoms_in crt5_Pr (ss_facts crt5_ssEntry) = true) by (vm_compute; reflexivity).
pose proof (facts_ok_agree_on crt5_Pr E (Ereg (ms_regs ms') (crt_extra cx)) (ss_facts crt5_ssEntry)
              HAGE HFA HFACTS) as HFACTS2.
(* the boundary state at 0x82098, the loop's exit *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W3) E' crt5_ssOut ms' HSout eq_refl) as Hms.
assert (HSret98 : st_ok tfibsegs (Ereg (ms_regs ms') (crt_extra cx)) (crt_ss_ret 0x82098 crt_cs1L crt_csF)
                  (restrict (w_H W3) ms')).
{ rewrite Hms. rewrite restrict_mkst_fx. cbn [ms_regs ms_mem mkst].
  destruct HMO2 as (W2 & RK2 & PD2).
  apply (entry_st_ok_full tfibsegs); [apply regs_ok_Ereg | exact W2 | exact RK2 | exact PD2 | exact HFACTS2]. }
(* the trip count at the exit: the last trip writes the last quad, so q' + 4 = want + En *)
pose proof (crt5_En_last (Z.of_nat (length (c_bs cx))) i' q' (c_want cx) Hi0 Hil Him Hle Hq) as HEn.
pose proof (CRTL.enc_len_Z (c_bs cx)) as HLEN.
assert (HBOK : bytes_ok (c_bs cx)).
{ apply Forall_forall. intros x Hx.
  destruct (In_nth (c_bs cx) x 0 Hx) as (j & Hj & <-). exact (proj2 (MG j Hj)). }
pose proof (b64_enc_ok (c_bs cx) HBOK) as HEOK.
pose proof (crt5_En_nonneg (Z.of_nat (length (c_bs cx))) (Nat2Z.is_nonneg _)) as HEnpos.
(* the three slot reloads 0x82098 .. 0x820a0, over the read-only slot region: memory does not move *)
assert (HSX : st_ok tfibsegs (Ereg (ms_regs ms') (crt_extra cx)) crt5_ssX (restrict (w_H W3) ms')).
{ refine (st_ok_submem tfibsegs _ (crt_ss_ret 0x82098 crt_cs1L crt_csF) _ [crt5_slot_ro] HSret98 _
            ltac:(vm_compute; reflexivity)).
  change (ss_mem (crt_ss_ret 0x82098 crt_cs1L crt_csF)) with (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF).
  cbn [crt_ret_regions].
  apply submem_drop. apply submem_keep; [|apply submem_nil].
  unfold subregion, crt5_slot_ro, crt_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc. exact Hc. }
destruct HJR' as (HJ2 & HARU2).
eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 FUEL 0x820a4 (Ereg (ms_regs ms') (crt_extra cx)) crt5_ssX
          crt5_ssY RS_running ms' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HSX crt5_runXY I HARU2 HJ2
          (crt5_awr_ro cx (Ereg (ms_regs ms') (crt_extra cx)) ly3 S3)).
intros ms'' mat HSY HJY HARUY HFY _ _.
set (mdY := with_vm_backing (m_vm_lazy md') mat md') in *.
pose proof (crt5_frame_ro _ _ _ HFY) as HMEQ.
destruct crt5_ssY_shape as (HpcY & HresY & _).
assert (Y10 : sr_get (ss_regs crt5_ssY) 10%bv = SOff 10 0) by (vm_compute; reflexivity).
assert (Y18 : sr_get (ss_regs crt5_ssY) 18%bv = SOff 18 0) by (vm_compute; reflexivity).
assert (Y19 : sr_get (ss_regs crt5_ssY) 19%bv = SOff 47 0) by (vm_compute; reflexivity).
assert (Y22 : sr_get (ss_regs crt5_ssY) 22%bv = SOff 47 0) by (vm_compute; reflexivity).
assert (Y27 : sr_get (ss_regs crt5_ssY) 27%bv = SOff 50 0) by (vm_compute; reflexivity).
(* the registers the reloads keep, and the machine's registers outside crt5_clob across the whole segment *)
assert (Hkr2 : forall r : bv 5, ~ In r crt5_clob -> YK11.getr (ms_regs ms'') r = YK11.getr (ms_regs ms') r).
{ intros r Hr.
  rewrite (st_ok_restrict_reg tfibsegs (w_H W3) _ crt5_ssY ms'' r HSY), (crt5_ssY_regs r Hr).
  rewrite (st_ok_restrict_reg tfibsegs (w_H W3) _ (crt_ss_ret 0x82098 crt_cs1L crt_csF) ms' r HSret98).
  reflexivity. }
assert (Hkr3 : forall r : bv 5, ~ In r crt5_clob -> YK11.getr (ms_regs ms'') r = YK11.getr (ms_regs ms3) r)
  by (intros r Hr; rewrite (Hkr2 r Hr); exact (Hkr r Hr)).
destruct (crt5_E_exit E cx ms3 ms'' HE Hkr3 Ea) as (HAGE3 & HE3).
(* the boundary state at the join 0x820a4: the same regions on the same memory, under the env of the machine
   after the reloads; the slots narrowed to crt_cs1e *)
pose proof (mem_ok_agree_on tfibsegs crt5_Pr E (Ereg (ms_regs ms'') (crt_extra cx))
              (mrestrict (w_H W3) (ms_mem ms')) (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF)
              HAGE3 HMA HMOE) as HMO3.
pose proof (facts_ok_agree_on crt5_Pr E (Ereg (ms_regs ms'') (crt_extra cx)) (ss_facts crt5_ssEntry)
              HAGE3 HFA HFACTS) as HFACTS3.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W3) _ crt5_ssY ms'' HSY HresY) as HmsY.
rewrite HpcY in HmsY.
assert (HSretL : st_ok tfibsegs (Ereg (ms_regs ms'') (crt_extra cx)) (crt_ss_ret 0x820a4 crt_cs1L crt_csF)
                   (restrict (w_H W3) ms'')).
{ rewrite HmsY. rewrite restrict_mkst_fx. cbn [ms_regs ms_mem mkst]. rewrite HMEQ.
  destruct HMO3 as (W2 & RK2 & PD2).
  apply (entry_st_ok_full tfibsegs); [apply regs_ok_Ereg | exact W2 | exact RK2 | exact PD2 | exact HFACTS3]. }
assert (HSret : st_ok tfibsegs (Ereg (ms_regs ms'') (crt_extra cx)) (crt_ss_ret 0x820a4 crt_cs1e crt_csF)
                  (restrict (w_H W3) ms'')).
{ refine (st_ok_submem tfibsegs _ (crt_ss_ret 0x820a4 crt_cs1L crt_csF) _
            (crt_s0_region :: crt_ret_regions crt_cs1e crt_csF) HSretL _ ltac:(vm_compute; reflexivity)).
  change (ss_mem (crt_ss_ret 0x820a4 crt_cs1L crt_csF)) with (crt_s0_region :: crt_ret_regions crt_cs1L crt_csF).
  cbn [crt_ret_regions].
  apply submem_keep; [apply subregion_refl|]. apply submem_keep; [|apply submem_keep; [apply subregion_refl|]].
  - unfold subregion, crt_slot_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia|].
    intros c Hc. cbn [crt_cs1e crt_cs1L In] in Hc |- *. tauto.
  - apply submem_keep; [apply subregion_refl | apply submem_nil]. }
(* the frame's flag word is outside the loop's window, and the reloads keep memory, so crt_frame_ok crosses *)
assert (HFR2 : crt_frame_ok cx S3 W3 ms'').
{ split; [exact Hfr|]. split; [exact Hfr2|]. rewrite HMEQ.
  pose proof (crt_F_facts SK B cx ly3 S3 U3 W3 (ms_mem ms3) md3 k HJ HARU Hfr) as (_ & F4096 & Fceil & _ & _ & _).
  rewrite <- Hflag. apply rdword_ext. intros i Hi. unfold aview. f_equal.
  apply (crt5_mbyte_keep W3 (ms_mem ms3) (ms_mem ms')
           (fun a => c_want cx <= a < c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4));
    [ exact Hk' | rewrite crt_frame3; clear - F4096 Fceil HAC Hi; lia | ].
  cbv beta. apply (crt5_out_frame cx ly3 S3 W3 (ms_mem ms3));
    [exact HMEM | rewrite crt_frame3; clear - Hi; lia]. }
(* the registers at the join, read off the run's state *)
assert (HE2' := HE2).
assert (V10 : ew (Ereg (ms_regs ms') (crt_extra cx)) 10 = Z_to_bv 64 (q' + 4))
  by (rewrite (ew_Ereg_nat (ms_regs ms') (crt_extra cx) 10 10%bv eq_refl); exact O10).
assert (V18 : ew (Ereg (ms_regs ms') (crt_extra cx)) 18 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat (ms_regs ms') (crt_extra cx) 18 18%bv eq_refl); exact O18).
assert (V47 : ew (Ereg (ms_regs ms') (crt_extra cx)) 47 = Z_to_bv 64 (crt_F cx)) by exact (crt_E_F cx _ HE2).
assert (V50 : ew (Ereg (ms_regs ms') (crt_extra cx)) 50 = Z_to_bv 64 (crt_En cx))
  by exact (crt_E_extra cx _ 18 HE2 ltac:(unfold crt_nextra; lia)).
assert (G10 : YK11.getr (ms_regs ms'') 10%bv = Z_to_bv 64 (c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4)).
{ rewrite <- HEn. exact (crt5_regv W3 _ crt5_ssY ms'' 10%bv 10 _ HSY Y10 V10). }
assert (G18 : YK11.getr (ms_regs ms'') 18%bv = Z_to_bv 64 SHADOW_OFF)
  by exact (crt5_regv W3 _ crt5_ssY ms'' 18%bv 18 _ HSY Y18 V18).
assert (G19 : YK11.getr (ms_regs ms'') 19%bv = Z_to_bv 64 (crt_F cx))
  by exact (crt5_regv W3 _ crt5_ssY ms'' 19%bv 47 _ HSY Y19 V47).
assert (G22 : YK11.getr (ms_regs ms'') 22%bv = Z_to_bv 64 (crt_F cx))
  by exact (crt5_regv W3 _ crt5_ssY ms'' 22%bv 47 _ HSY Y22 V47).
assert (G27 : YK11.getr (ms_regs ms'') 27%bv = Z_to_bv 64 (crt_En cx))
  by exact (crt5_regv W3 _ crt5_ssY ms'' 27%bv 50 _ HSY Y27 V50).
(* the exit invariant *)
assert (HI58 : crt_INV_81f58 B cx (Ereg (ms_regs ms'') (crt_extra cx)) k ly3 S3 U3 W3 ms'' mdY).
{ unfold crt_INV_81f58. cbv zeta. rewrite HMEQ.
  split; [exact G10|].
  split; [exact G18|].
  split; [exact G27|].
  split; [exact G22|].
  split; [exact G19|].
  split.
  { intros j Hj. split.
    - apply HOUT'. apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact HEnpos. rewrite <- HLEN.
      apply Nat2Z.inj_lt. exact Hj.
    - unfold bytes_ok in HEOK. rewrite Forall_forall in HEOK. apply HEOK. apply nth_In. exact Hj. }
  split; [exact MWT1|]. split; [exact MWT2|]. split; [exact MSHw|]. split; [exact MWIN|].
  split; [exact MFRd|].
  split; [intros x Hx; apply (proj1 (proj2 (proj2 HMF'))); clear - Hx; lia|].
  split; [apply (proj2 (proj2 (proj2 HMF'))); clear - HEnpos; lia|].
  apply MAWR. clear - HEnpos; lia. }
(* R crosses the segment by its stability: the loop and the reloads write registers of crt5_clob only, memory only
   in the loop's window *)
assert (HR2 : R cx (Ereg (ms_regs ms'') (crt_extra cx)) k ly3 S3 U3 W3 ms'' mdY).
{ apply (HST cx E (Ereg (ms_regs ms'') (crt_extra cx)) k ly3 S3 U3 W3 ms3 ms'' md3 mdY);
    [ intros n (Hn1 & Hn2); apply HAGE3; unfold crt5_Pr; apply Bool.orb_true_iff; right;
      apply Bool.andb_true_iff; split; [apply Nat.leb_le; exact Hn1 | apply Nat.ltb_lt; exact Hn2]
    | exact Hkr3 | rewrite HMEQ; exact Hk' | rewrite HMEQ; exact Hgr | exact HR ]. }
exact (HNEXT cx (Ereg (ms_regs ms'') (crt_extra cx)) k ly3 S3 U3 W3 ms'' mdY
         HB HE3 HJY HARUY HFR2 (conj HI58 HR2) HSret).
Qed.

End Seg5.

Print Assumptions crt5_seg5.
