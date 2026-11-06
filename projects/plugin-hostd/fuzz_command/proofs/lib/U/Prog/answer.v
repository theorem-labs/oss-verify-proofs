(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths, module names and numbers changed; 505 of its 555 lines of code are new or changed and 1016 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/sup_resp.v, with its addresses and numbers changed; 1050 of its 1225 lines of code are new or changed and 380 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c mix_call_c RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma an_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma an_eqb_zxb : forall (b : byte) z, 0 <= z < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 z) = Z.eqb (bv_unsigned b) z.
Proof. intros b z Hz. pose proof (an_byte_range b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma an_skipn_nth : forall {X} (l rest : list X) n r, skipn n l = r :: rest -> nth_error l n = Some r.
Proof.
  intros X l. induction l as [|y l IH]; intros rest n r H; destruct n; cbn in *; try discriminate.
  - inversion H; reflexivity.
  - eapply IH. exact H.
Qed.

Lemma an_read1 : forall m a (T : list byte) i b, bytes_at rsegs m a T -> nth_error T i = Some b ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i + 0)) 1 = Some [b].
Proof.
  intros m a T i b HB E. rewrite <- Z.add_assoc.
  assert (Hi : (i < length T)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite (bytes_at_read rsegs m a T (Z.of_nat i + 0) 1 HB) by lia.
  rewrite Z.add_0_r, Nat2Z.id.
  destruct (skipn i T) as [|c r] eqn:Es.
  - exfalso. apply (f_equal (@length _)) in Es. rewrite length_skipn in Es. cbn in Es. lia.
  - rewrite (an_skipn_nth T r i c Es) in E. injection E as <-. reflexivity.
Qed.

Lemma an_eqb_lit64 : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma an_signed_lit : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

Lemma anu_ne_m1 : forall z, 0 <= z < 2 ^ 64 - 1 -> negb (bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 (-1))) = true.
Proof.
  intros z Hz. unfold bv_eqb. rewrite (unsigned_lit z) by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by (vm_compute; reflexivity).
  apply negb_true_iff. apply Z.eqb_neq. lia.
Qed.

Lemma anu_eqb_nz0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma anu_not : forall z, 0 <= z < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 z)) 18446744073709551615) = Z_to_bv 64 (18446744073709551615 - z).
Proof. intros z Hz. f_equal. rewrite unsigned_lit by lia. apply zb_lxor_ones. lia. Qed.

Section Loop.
Variables (r1 r2 r3 r4 r7 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
  (F : bvmap 5 word) (fc : bv 32) (sh buf : Z) (x : list byte) (m0 : word -> option byte).
Hypothesis X0 : no0 x.
Hypothesis XL : Z.of_nat (length x) <= LMAX.
Hypothesis FIT : Z.of_nat (length (inst x)) <= 4095.
Hypothesis SHB : 1 <= sh.
Hypothesis SEP : sh + Z.of_nat (length x) + 1 <= buf.
Hypothesis BUFB : buf + 4096 < 2 ^ 63.
Hypothesis SPB : bv_unsigned r2 + 8 = buf.

Definition lst (w5 w6 w8 w10 w11 w12 w17 : word) (pc : Z) (m : word -> option byte) : machine_state :=
  MS (mkR r1 r2 r3 r4 w5 w6 r7 w8 r9 w10 w11 w12 (Z_to_bv 64 60) (Z_to_bv 64 (18446744073709551615 - buf))
          (Z_to_bv 64 (-1)) (Z_to_bv 64 62) w17
          r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition linv (m : word -> option byte) (out rest : list byte) : Prop :=
  bytes_at rsegs m sh (x ++ [Z_to_bv 8 0]) /\ wr_at rsegs m buf 4096 /\ bytes_at rsegs m buf out /\
  bytes_at rsegs m (buf + Z.of_nat (length out)) rest /\ (length out + length rest = 4096)%nat /\
  munch [(buf, buf + 4096)] m0 m /\ wmono rsegs m0 m.

Lemma an_swrap : forall z, 0 <= z < 2 ^ 31 -> Z_to_bv 64 (bv_swrap 32 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). Z.div_mod_to_equations. lia.
Qed.

Lemma anu_ltu_nb : forall z, 0 <= z <= 4096 -> bv_ltu (Z_to_bv 64 (18446744073709551615 - buf)) (Z_to_bv 64 z) = false.
Proof using SHB SEP BUFB.
  intros z Hz. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

Lemma linv_store : forall m out r0 rest' v, linv m out (r0 :: rest') ->
  linv (write_to_mem m (Z_to_bv 64 (buf + Z.of_nat (length out))) [v]) (out ++ [v]) rest'.
Proof.
  intros m out r0 rest' v (HX & HW & HO & HR & HLen & HM & HWM).
  pose proof (bytes_at_bound _ _ _ _ HO) as OB. pose proof (bytes_at_bound _ _ _ _ HX) as XB.
  pose proof (wr_at_bound_like := HW). destruct HW as (W1 & W2 & W3).
  cbn [length] in HLen.
  change (Z_to_bv 64 (buf + Z.of_nat (length out))) with (wa (buf + Z.of_nat (length out))).
  assert (L1 : Z.of_nat (length [v]) = 1) by reflexivity.
  replace (r0 :: rest') with ([r0] ++ rest') in HR by reflexivity. apply bytes_at_app in HR as [_ HR2].
  cbn [length] in HR2.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply bytes_at_write_other; [exact HX | lia | try rewrite L1; lia | try rewrite L1; rewrite length_app in XB |- *; cbn [length] in XB |- *; lia].
  - apply wr_at_write. exact wr_at_bound_like.
  - apply bytes_at_app. split.
    + apply bytes_at_write_other; [exact HO | lia | try rewrite L1; lia | try rewrite L1; lia].
    + apply bytes_at_write_same; try rewrite L1; lia.
  - rewrite length_app. cbn [length]. replace (buf + Z.of_nat (length out + 1)) with (buf + Z.of_nat (length out) + 1) by lia.
    apply bytes_at_write_other; [exact HR2 | lia | try rewrite L1; lia | try rewrite L1; lia].
  - rewrite length_app. cbn [length]. lia.
  - apply munch_write; [exact HM | lia | try rewrite L1; lia | cbn [inside]; left; try rewrite L1; lia].
  - apply wmono_write. exact HWM.
Qed.

Lemma an_write : forall (w5 w6 w8 w12 w17 : word) (v : byte) out r0 rest' m (P : machine_state -> Prop),
  le1 w17 = [v] -> linv m out (r0 :: rest') -> Z.of_nat (length out) + 1 <= 4095 ->
  (forall w5' w6' m', linv m' (out ++ [v]) rest' ->
     evt rsegs P (lst w5' w6' w8 (Z_to_bv 64 (Z.of_nat (length out) + 1)) (Z_to_bv 64 buf) w12 w17 0x163ec m')) ->
  evt rsegs P (lst w5 w6 w8 (Z_to_bv 64 (Z.of_nat (length out))) (Z_to_bv 64 buf) w12 w17 0x163d0 m).
Proof.
  intros w5 w6 w8 w12 w17 v out r0 rest' m P Hv HL Ho K.
  pose proof HL as (HX & HW & HO & HR & HLen & HM & HWM).
  unfold lst. step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length out) + 1)) by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace ((Z.of_nat (length out) + 1) / 2 ^ 12) with 0 by (symmetry; apply Z.div_small; lia).
  if_false. step.
  rewrite (anu_ltu_nb (Z.of_nat (length out))) by lia. cbv iota.
  step.
  assert (HS : store_ok rsegs m (Z_to_bv 64 (buf + Z.of_nat (length out))) 1 = true)
    by exact (wr_at_store_ok rsegs m buf 4096 (Z.of_nat (length out)) 1 HW ltac:(lia) ltac:(lia)).
  step. rewrite Hv.
  pose proof (linv_store m out r0 rest' v HL) as HL'.
  match goal with |- context [write_to_mem m ?a [v]] =>
    replace a with (Z_to_bv 64 (buf + Z.of_nat (length out))) by (apply bv_eq; rewrite ?unsigned_lit_wrap; f_equal; lia) end.
  set (m' := write_to_mem m _ [v]) in HL' |- *. clearbody m'.
  step. apply K. exact HL'.
Qed.

Lemma an_loop : forall xr j d out rest w5 w6 w8 w10 w12 w17 m (P : machine_state -> Prop),
  skipn j x = xr -> (j <= length x)%nat -> w8 = Z_to_bv 64 (sh + Z.of_nat j - 1) ->
  w10 = Z_to_bv 64 (Z.of_nat (length out)) -> w12 = Z_to_bv 64 (Z.of_nat d) -> (d <= j)%nat ->
  out ++ inst_go d xr = inst x -> linv m out rest ->
  (forall w5' w6' w10' w11' w12' w17' m' rest', linv m' (inst x ++ [Z_to_bv 8 0]) rest' ->
     evt rsegs P (lst w5' w6' (Z_to_bv 64 (sh + Z.of_nat (length x) - 1)) w10' w11' w12' w17' 0x16410 m')) ->
  evt rsegs P (lst w5 w6 w8 w10 (Z_to_bv 64 buf) w12 w17 0x16390 m).
Proof.
  induction xr as [|c xr IH]; intros j d out rest w5 w6 w8 w10 w12 w17 m P Hs Hjx E8 E10 E12 Hd Hinv HL K.
  - pose proof HL as (HX & HW & HO & HR & HLen & HM & HWM).
    assert (Hj : j = length x).
    { apply (f_equal (@length _)) in Hs. rewrite length_skipn in Hs. cbn in Hs. lia. }
    assert (RD : ov_read_bytes rsegs m (wa (sh + Z.of_nat j + 0)) 1 = Some [Z_to_bv 8 0]).
    { apply (an_read1 m sh (x ++ [Z_to_bv 8 0]) j). exact HX. rewrite nth_error_app2 by lia.
      rewrite Hj, Nat.sub_diag. reflexivity. }
    assert (HO' : out = inst x) by (rewrite <- Hinv; cbn; rewrite app_nil_r; reflexivity).
    assert (LO : Z.of_nat (length out) <= 4095) by (rewrite HO'; exact FIT).
    destruct rest as [|r0 rest']; [cbn [length] in HLen; lia|].
    subst w8 w10 w12. unfold lst. step. step. if_false. step. if_true.
    step. rewrite (anu_ltu_nb (Z.of_nat (length out))) by lia. cbv iota.
    step. step. step.
    assert (HS : store_ok rsegs m (Z_to_bv 64 (bv_unsigned r2 + 8 + Z.of_nat (length out))) 1 = true).
    { rewrite SPB. exact (wr_at_store_ok rsegs m buf 4096 (Z.of_nat (length out)) 1 HW ltac:(lia) ltac:(lia)). }
    step.
    replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
    rewrite SPB.
    pose proof (linv_store m out r0 rest' (Z_to_bv 8 0) HL) as HL'.
    set (m' := write_to_mem m _ [Z_to_bv 8 0]) in HL' |- *. clearbody m'.
    step.
    rewrite bv_lts_zero_r. rewrite (unsigned_lit (Z.of_nat (length out))) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
    replace (2 ^ 63 <=? Z.of_nat (length out) * 2 ^ 32) with false by (symmetry; apply Z.leb_gt; lia).
    cbn iota. subst j. rewrite HO' in HL'. eapply K. exact HL'.
  - pose proof HL as (HX & HW & HO & HR & HLen & HM & HWM).
    assert (Hjl : (j < length x)%nat).
    { apply (f_equal (@length _)) in Hs. rewrite length_skipn in Hs. cbn in Hs. lia. }
    assert (Hs' : skipn (S j) x = xr).
    { revert Hs. clear. revert j. induction x as [|y l IHl]; intros j H; destruct j; cbn in *; try discriminate.
      - injection H as _ ->. reflexivity.
      - apply IHl. exact H. }
    assert (Ec : nth_error x j = Some c) by exact (an_skipn_nth x xr j c Hs).
    assert (RD : ov_read_bytes rsegs m (wa (sh + Z.of_nat j + 0)) 1 = Some [c]).
    { apply (an_read1 m sh (x ++ [Z_to_bv 8 0]) j). exact HX. rewrite nth_error_app1 by lia. exact Ec. }
    assert (ZC : bv_unsigned (zxb c) = bv_unsigned c) by (unfold zxb; apply unsigned_lit; pose proof (an_byte_range c); lia).
    assert (CN0 : bv_unsigned c <> 0).
    { intros E. apply X0. assert (Ec0 : c = Z_to_bv 8 0) by (apply bv_eq; rewrite E; reflexivity).
      rewrite <- Ec0. exact (nth_error_In x j Ec). }
    assert (ZD : bv_unsigned (Z_to_bv 64 (Z.of_nat d)) = Z.of_nat d) by (apply unsigned_lit; lia).
    assert (SD : bv_signed (Z_to_bv 64 (Z.of_nat d)) = Z.of_nat d) by (apply an_signed_lit; unfold LMAX in XL; lia).
    assert (SD1 : bv_signed (Z_to_bv 64 (Z.of_nat d + 1)) = Z.of_nat d + 1) by (apply an_signed_lit; unfold LMAX in XL; lia).
    assert (S0 : bv_signed (Z_to_bv 64 0) = 0) by reflexivity.
    assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (LXI : (length (inst x) <= length x)%nat) by apply inst_length.
    assert (TAIL : forall d' out' rest' w5' w6' w10' w12' w17' m',
       w10' = Z_to_bv 64 (Z.of_nat (length out')) -> w12' = Z_to_bv 64 (Z.of_nat d') -> (d' <= S j)%nat ->
       out' ++ inst_go d' xr = inst x -> linv m' out' rest' ->
       evt rsegs P (lst w5' w6' (Z_to_bv 64 (sh + Z.of_nat j - 1)) w10' (Z_to_bv 64 buf) w12' w17' 0x163ec m')).
    { intros d' out' rest' w5' w6' w10' w12' w17' m' E10' E12' Hd' Hinv' HL'.
      unfold lst. step. step.
      rewrite (anu_ne_m1 (sh + Z.of_nat j - 1 + 1)) by (unfold LMAX in XL; lia). cbv iota.
      eapply (IH (S j) d' out' rest'); [exact Hs' | lia | | exact E10' | exact E12' | exact Hd' | exact Hinv' | exact HL' | exact K].
      f_equal. lia. }
    assert (OUTB : forall b xs, out ++ b :: xs = inst x -> Z.of_nat (length out) + 1 <= 4095 /\ rest <> []).
    { intros b xs E. apply (f_equal (@length _)) in E. rewrite length_app in E. cbn [length] in E.
      split; [lia|]. intros ->. cbn [length] in HLen. lia. }
    subst w8 w10 w12. unfold lst. step. step.
    rewrite an_eqb_zxb by lia.
    destruct (Z.eqb_spec (bv_unsigned c) 60) as [C60|C60]; cbn [negb].
    + step. rewrite ZD. rewrite an_swrap by (unfold LMAX in XL; lia).
      step. if_false. step. destruct d as [|d'].
      * if_true. step. step.
        cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_eq _ _) C60) in Hinv.
        destruct (OUTB _ _ Hinv) as [Ob Rne]. destruct rest as [|r0 rest']; [congruence|].
        eapply (an_write _ _ _ _ (Z_to_bv 64 49) (Z_to_bv 8 49) out r0 rest' m P); [reflexivity | exact HL | exact Ob |].
        intros w5' w6' m' HL'.
        eapply (TAIL 1%nat (out ++ [Z_to_bv 8 49]) rest'); [ | reflexivity | lia | | exact HL'].
        -- f_equal. rewrite length_app. cbn [length]. lia.
        -- rewrite <- app_assoc. exact Hinv.
      * if_false. step. step.
        cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_eq _ _) C60) in Hinv.
        eapply (TAIL (S (S d')) out rest); [reflexivity | | lia | exact Hinv | exact HL].
        f_equal. lia.
    + step. if_false. step.
      rewrite an_eqb_zxb by lia.
      destruct (Z.eqb_spec (bv_unsigned c) 62) as [C62|C62]; cbn [negb].
      * step. destruct d as [|d'].
        -- if_true. step. if_true.
           cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_neq _ _) C60) in Hinv.
           destruct (OUTB _ _ Hinv) as [Ob Rne]. destruct rest as [|r0 rest']; [congruence|].
           eapply (an_write _ _ _ _ (zxb c) c out r0 rest' m P); [apply le1_zxb | exact HL | exact Ob |].
           intros w5' w6' m' HL'.
           eapply (TAIL 0%nat (out ++ [c]) rest'); [ | reflexivity | lia | | exact HL'].
           ++ f_equal. rewrite length_app. cbn [length]. lia.
           ++ rewrite <- app_assoc. exact Hinv.
        -- if_false. step. step.
           cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_neq _ _) C60), (proj2 (Z.eqb_eq _ _) C62) in Hinv.
           eapply (TAIL d' out rest); [reflexivity | | lia | exact Hinv | exact HL].
           rewrite unsigned_lit by lia. rewrite an_swrap by (unfold LMAX in XL; lia). f_equal. lia.
      * step. destruct d as [|d'].
        -- if_true.
           cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_neq _ _) C60) in Hinv.
           destruct (OUTB _ _ Hinv) as [Ob Rne]. destruct rest as [|r0 rest']; [congruence|].
           eapply (an_write _ _ _ _ (zxb c) c out r0 rest' m P); [apply le1_zxb | exact HL | exact Ob |].
           intros w5' w6' m' HL'.
           eapply (TAIL 0%nat (out ++ [c]) rest'); [ | reflexivity | lia | | exact HL'].
           ++ f_equal. rewrite length_app. cbn [length]. lia.
           ++ rewrite <- app_assoc. exact Hinv.
        -- if_false. step.
           cbn [inst_go] in Hinv. rewrite (proj2 (Z.eqb_neq _ _) C60), (proj2 (Z.eqb_neq _ _) C62) in Hinv.
           eapply (TAIL (S d') out rest); [reflexivity | reflexivity | lia | exact Hinv | exact HL].
Qed.

End Loop.

Lemma an_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa (a + 0)) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  f_equal.
Qed.

Lemma an_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma an_eqb_ne0 : forall z, -2^31 <= z < 2^31 -> z <> 0 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof.
  intros z Hz N. unfold bv_eqb. rewrite !unsigned_lit_wrap. apply Z.eqb_neq. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.

Definition an_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo : Z) (t : list byte) (h : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x16418) (Z_to_bv 64 (bv_unsigned sp + -4128)) gp tp t0 t1 t2 s0' (Z_to_bv 64 0x33ff0)
                  (Z_to_bv 64 (bv_unsigned sp + -4120)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x16284) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp); (0x343d8, 0x343e0)] m m' /\ wmono rsegs m m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ length slack = (4095 - length t)%nat
    /\ bytes_at rsegs m' (bv_unsigned sp + -4120) (t ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells rsegs m' (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra]
    /\ bytes_at rsegs m' 0x343d8 (le8 (Z_to_bv 64 h)).

Lemma an_run_resp : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo rf code h : Z) (canary : word),
  -2^31 <= rf < 2^31 -> rf <> 0 -> -2^31 <= code < 2^31 ->
  bytes_at rsegs m 0x34028 (le4 (Z_to_bv 64 rf)) -> bytes_at rsegs m 0x3402c (le4 (Z_to_bv 64 code)) ->
  bytes_at rsegs m 0x343d8 (le8 (Z_to_bv 64 h)) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 4128 + SNPRINTF_K <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bv_unsigned sp < 2^63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> bv_unsigned sp <= TASK_SIZE ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (an_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (resp code) h m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo rf code h canary RF RF0 HC HRF HCD HST ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 24%nat ST.
  rename FR into FRS.
  apply (rw_cells_split_CB rsegs _ _ [] 24%nat junk [] [8; 8; 8]%nat) in FRS; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRS.
  carve_frame 4096%nat ST.
  rename FR into FRB.
  carve_frame 8%nat ST.
  clear FR.
  do 9 step.
  match goal with H : bytes_at rsegs ?mm 0x34028 _ |- _ => pose proof (an_rd4 mm _ _ H) as RD1 end.
  step. rewrite an_sx32 by lia.
  step. first [if_false | if_false_by (an_eqb_ne0 rf RF RF0)].
  match goal with H : bytes_at rsegs ?mm 0x3402c _ |- _ => pose proof (an_rd4 mm _ _ H) as RD2 end.
  step. rewrite an_sx32 by lia.
  do 5 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
  pose proof (resp_len code HC) as RL.
  pose proof (rw_cells_bound _ _ _ _ FRB) as FBB. cbn [cells_size csize Nat.add] in FBB.
  assert (BJ : bytes_at rsegs mS (bv_unsigned sp + -4120) junk0).
  { destruct FRB as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary RESP_FMT RESP_PS
              [AInt code] (RESP_HEAD ++ pf_dec code) junk0).
    - rewrite unsigned_lit by lia. apply resp_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, RESP_FMT. cbn [length]. lia.
    - exact resp_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HC | apply lit_mod32].
    - exact (resp_text code).
    - rewrite !unsigned_lit by lia. try replace (bv_unsigned sp + -4128 + 8) with (bv_unsigned sp + -4120) by lia. exact FRB.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact MI.
    - exact (task_mem_munch1 m mS lo (bv_unsigned sp) TM MU HTS).
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & mP
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  try replace (bv_unsigned sp + -4128 + 8) with (bv_unsigned sp + -4120) in MU2, BT by lia.
  change (Z.to_nat (4096 - 1)) with 4095%nat in BT, MU2.
  rewrite (firstn_all2 (n := 4095%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 0x16354)) with (Z_to_bv 64 0x16354) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (JL : length junk0 = 4096%nat) by (destruct FRB as [[[HJ _] _] _]; exact HJ).
  assert (FRS2 : rw_cells rsegs mP (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport rsegs _ mS mP _ _ FRS MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | split; [lia | exact I]]. }
  assert (HST2 : bytes_at rsegs mP 0x343d8 (le8 (Z_to_bv 64 h))).
  { apply (bytes_at_transport rsegs _ mS mP _ _ HST MU2). cbn [disjoint_from]. rewrite ?length_le8.
    split; [lia | split; [lia | exact I]]. }
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (RESP_HEAD ++ pf_dec code))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs mP (bv_unsigned sp + -4120 + Z.of_nat (S (length (RESP_HEAD ++ pf_dec code))))
                   (skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)).
  { apply (bytes_at_transport rsegs _ mS mP _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes ((RESP_HEAD ++ pf_dec code) ++ [0]) = resp code ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (RESP_HEAD ++ pf_dec code)) with
      (pf_bytes (RESP_HEAD ++ pf_dec code)). rewrite pf_resp by exact HC. reflexivity. }
  assert (LR : length (resp code) = length (RESP_HEAD ++ pf_dec code)).
  { rewrite <- (pf_resp code HC). unfold pf_bytes. apply length_map. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs mP (bv_unsigned sp + -4120)
                  (resp code ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)).
  { replace (resp code ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0) with
      ((resp code ++ [Z_to_bv 8 0]) ++ skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, LR. cbn [length].
    replace (Z.of_nat (length (RESP_HEAD ++ pf_dec code) + 1))
      with (Z.of_nat (S (length (RESP_HEAD ++ pf_dec code)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FRB.
  do 3 step.
  apply evt_done. unfold an_mid.
  do 18 eexists. exists (skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0). split; [reflexivity|].
  split.
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros y (Hy1 & Hy2 & _). split; [lia | exact I].
    - eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros y (Hy1 & Hy2 & _).
      split; [lia | split; [lia | exact I]]. }
  split; [eapply wmono_trans; eassumption|].
  split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, LR; lia|].
  split; [exact BUF|]. split; [exact FRS2 | exact HST2].
Qed.

Lemma an_run_tail : forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F Fc : bvmap 5 word) fc (m mc : word -> option byte) (lo sh h : Z) (x junk : list byte) (s0o s1o rao : word),
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length (inst x)) <= 4095 ->
  1 <= sh -> sh + Z.of_nat (length x) + 1 <= bv_unsigned sp + -4120 -> bv_unsigned sp < 2 ^ 63 ->
  lo + 4128 <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bytes_at rsegs mc sh (x ++ [Z_to_bv 8 0]) ->
  rw_cells rsegs mc (bv_unsigned sp + -4120) [CB 4096%nat junk] ->
  rw_cells rsegs mc (bv_unsigned sp + -24) [C8 s1o; C8 s0o; C8 rao] ->
  munch [(lo, bv_unsigned sp); (0x343d8, 0x343e0)] m mc -> wmono rsegs m mc ->
  bytes_at rsegs mc 0x343d8 (le8 (Z_to_bv 64 h)) ->
  frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
  evt rsegs (an_mid rao sp gp tp s0o s1o s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (inst x) h m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -4128)) gp tp t0 t1 t2 (Z_to_bv 64 sh) (Z_to_bv 64 0x33ff0)
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x1636c) fc None mc (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F Fc fc m mc lo sh h x junk s0o s1o rao X0 XL FIT SHB SEP S63 LO IE HX FRB FRS MU WM HS FRM FK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (JL : length junk = 4096%nat) by (destruct FRB as [[[HJ _] _] _]; exact HJ).
  assert (JB : bytes_at rsegs mc (bv_unsigned sp + -4120) junk).
  { destruct FRB as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (HW : wr_at rsegs mc (bv_unsigned sp + -4120) 4096).
  { destruct FRB as [_ Hw]. change (Z.of_nat (cells_size [CB 4096%nat junk])) with 4096 in Hw. exact Hw. }
  assert (BN : bytes_at rsegs mc (bv_unsigned sp + -4120) [] /\
               bytes_at rsegs mc (bv_unsigned sp + -4120 + Z.of_nat (length (@nil byte))) junk).
  { apply bytes_at_app. exact JB. }
  step. rewrite (anu_eqb_nz0 sh) by lia. cbv iota.
  do 8 step.
  rewrite anu_not by (rewrite ?unsigned_lit by lia; lia).
  eapply an_loop with (x := x) (sh := sh) (m0 := mc) (j := 0%nat) (d := 0%nat) (out := @nil byte) (rest := junk) (xr := x).
  all: try (first [ assumption | reflexivity | (f_equal; lia) | lia | (rewrite unsigned_lit by lia; lia)
                  | (unfold linv; split; [exact HX|]; split; [exact HW|]; split; [exact (proj1 BN)|];
                     split; [exact (proj2 BN)|]; split; [cbn [length]; lia|];
                     split; [apply munch_refl | apply wmono_refl]) ]).
  { intros w5' w6' w10' w11' w12' w17' m' rest' HL'.
    destruct HL' as (HX' & HW' & HO' & HR' & HLen' & HM' & HWM').
    unfold lst.
    do 2 step.
    apply evt_done. unfold an_mid.
    do 18 eexists. exists rest'. split; [reflexivity|].
    split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact HM'].
      unfold sub_fp. cbn [outside]. intros y (Hy1 & Hy2 & _). split; [lia | exact I]. }
    split; [eapply wmono_trans; eassumption|].
    split; [exact FRM|]. split; [exact FK|].
    split; [rewrite length_app in HLen'; cbn [length] in HLen'; lia|].
    split.
    { replace (inst x ++ Z_to_bv 8 0 :: rest') with ((inst x ++ [Z_to_bv 8 0]) ++ rest')
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact HO' | exact HR']. }
    split.
    { apply (rw_cells_transport rsegs _ mc m' _ _ FRS HM' HWM'). cbn [disjoint_from cells_size csize Nat.add].
      split; [lia | exact I]. }
    apply (bytes_at_transport rsegs _ mc m' _ _ HS HM'). cbn [disjoint_from]. rewrite ?length_le8.
    split; [lia | exact I]. }
Qed.

Lemma an_eqb0 : forall w : word, bv_unsigned w = 0 -> bv_eqb w (Z_to_bv 64 0) = true.
Proof. intros w H. unfold bv_eqb. rewrite H. reflexivity. Qed.

Lemma an_run_nochg : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo sh h : Z) (x : list byte),
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length (inst x)) <= 4095 ->
  1 <= sh -> sh + Z.of_nat (length x) + 1 <= bv_unsigned sp + -4120 -> bv_unsigned sp < 2 ^ 63 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 4128 <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bytes_at rsegs m sh (x ++ [Z_to_bv 8 0]) ->
  bytes_at rsegs m 0x34028 (le4 (Z_to_bv 64 0)) -> bytes_at rsegs m 0x343d8 (le8 (Z_to_bv 64 h)) ->
  bv_unsigned a2 = 0 -> frm0 fc ->
  evt rsegs (an_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (inst x) h m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 sh) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sh h x X0 XL FIT SHB SEP S63 ST LO IE HX HRF HS A2 FRM.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(lo, bv_unsigned sp); (0x343d8, 0x343e0)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 24%nat ST.
  rename FR into FRS.
  apply (rw_cells_split_CB rsegs _ _ [] 24%nat junk [] [8; 8; 8]%nat) in FRS; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRS.
  carve_frame 4096%nat ST.
  rename FR into FRB.
  carve_frame 8%nat ST.
  clear FR.
  do 9 step.
  match goal with H : bytes_at rsegs ?mm 0x34028 _ |- _ => pose proof (an_rd4 mm _ _ H) as RD1 end.
  step. try (rewrite an_sx32 by lia).
  step. try if_true.
  step. first [if_true | if_true_by (an_eqb0 a2 A2)].
  eapply an_run_tail.
  all: first [eassumption | lia | (intros; reflexivity)].
Qed.

Lemma an_run_ret : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (s0v s1v rav : word),
  rw_cells rsegs m (bv_unsigned sp + 4104) [C8 s1v; C8 s0v; C8 rav] -> bv_unsigned sp + 4128 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 4128)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc rav) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16418) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s0v s1v rav FR HB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 7 step. apply evt_done. reflexivity.
Qed.

Lemma an_eqb_nz : forall w : word, bv_unsigned w <> 0 -> bv_eqb w (Z_to_bv 64 0) = false.
Proof. intros w H. unfold bv_eqb. rewrite unsigned_lit by lia. apply Z.eqb_neq. exact H. Qed.

Lemma an_run_chg : mix_call_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo sh h c fn : Z) (x : list byte)
    (args : list (word * list byte)),
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length (inst x)) <= 4095 ->
  1 <= sh -> sh + Z.of_nat (length x) + 1 <= lo ->
  sh + Z.of_nat (length x) + 1 <= 0x343d8 \/ 0x343e0 <= sh -> bv_unsigned sp < 2 ^ 63 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 4128 + MIX_CALL_FRAME <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  mem_inv rsegs m ->
  bytes_at rsegs m sh (x ++ [Z_to_bv 8 0]) ->
  bytes_at rsegs m 0x34028 (le4 (Z_to_bv 64 0)) ->
  rw_cells rsegs m 0x343d8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  bv_unsigned a2 <> 0 -> frm0 fc ->
  -2 ^ 31 <= fn < 2 ^ 31 -> (length args <= 6)%nat ->
  bytes_at rsegs m c (le4 (Z_to_bv 64 fn) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  1 <= c -> c mod 8 = 0 -> c + 56 <= 0x343d8 ->
  (forall m', munch [(lo, bv_unsigned sp); (0x343d8, 0x343e0)] m m' ->
     forall k p, nth_error args k = Some p ->
       mc_arg m' (bv_unsigned sp - 4128 - MIX_CALL_FRAME) (bv_unsigned sp - 4128) c k p) ->
  evt rsegs (an_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (inst x) (mixcall h fn (map snd args)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 sh) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo sh h c fn x args X0 XL FIT SHB SEP SST S63 ST LO IE MI HX HRF HS Hh A2 FRM Hfn LA EF C0 CM8 C1 HARG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold MIX_CALL_FRAME in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (0x343d8, 0x343e0)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (HX0 : True /\ bytes_at rsegs m sh (x ++ [Z_to_bv 8 0])) by (split; [exact I | exact HX]).
  carve_frame 24%nat ST.
  rename FR into FRS.
  apply (rw_cells_split_CB rsegs _ _ [] 24%nat junk [] [8; 8; 8]%nat) in FRS; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FRS.
  carve_frame 4096%nat ST.
  rename FR into FRB.
  carve_frame 8%nat ST.
  clear FR.
  do 9 step.
  match goal with H : bytes_at rsegs ?mm 0x34028 _ |- _ => pose proof (an_rd4 mm _ _ H) as RD1 end.
  step. try (rewrite an_sx32 by lia).
  step. try if_true.
  step. first [if_false | if_false_by (an_eqb_nz a2 A2)].
  do 3 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
  eapply evt_cut.
  { eapply (MIX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo fn args).
    - exact MI.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. try unfold MIX_CALL_FRAME. lia.
    - exact Hfn.
    - exact LA.
    - rewrite unsigned_lit by lia. exact EF.
    - rewrite !unsigned_lit by lia. try unfold MIX_CALL_FRAME. left. lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite unsigned_lit by lia. exact CM8.
    - intros k p Hk. rewrite !unsigned_lit by lia. try unfold MIX_CALL_FRAME.
      try replace (bv_unsigned sp + -4128 - 96) with (bv_unsigned sp - 4128 - 96) by lia.
      try replace (bv_unsigned sp + -4128) with (bv_unsigned sp - 4128) by lia.
      exact (HARG mS MU k p Hk).
    - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
      apply ro_bytes_b_sound. vm_compute. reflexivity.
    - rewrite unsigned_lit by lia. unfold FNV_B0_ADDR. try unfold MIX_CALL_FRAME. left. lia. }
  intros ms' PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & mP
    & -> & MU2 & WM2 & MI2 & ST2).
  rewrite !unsigned_lit in MU2, ST2 by lia. try unfold MIX_CALL_FRAME in MU2.
  rewrite (unsigned_lit h) by lia.
  replace (ret_pc (Z_to_bv 64 0x16368)) with (Z_to_bv 64 0x16368) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (FRS2 : rw_cells rsegs mP (bv_unsigned sp + -24) [C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport rsegs _ mS mP _ _ FRS MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (FRB2 : rw_cells rsegs mP (bv_unsigned sp + -4120) [CB 4096%nat junk0]).
  { apply (rw_cells_transport rsegs _ mS mP _ _ FRB MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (HS2 : rw_cells rsegs mP 0x343d8 [C8 (Z_to_bv 64 h)]).
  { apply (rw_cells_transport rsegs _ mS mP _ _ HS MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (HX2 : bytes_at rsegs mP sh (x ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transport rsegs _ mS mP _ _ HX MU2). cbn [disjoint_from]. rewrite length_app. cbn [length].
    repeat split; lia. }
  assert (MU3 : munch [(lo, bv_unsigned sp); (0x343d8, 0x343e0)] m mP).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside].
    intros y (Hy1 & Hy2 & _). split; [lia | exact I]. }
  assert (WM3 : wmono rsegs m mP) by (eapply wmono_trans; eassumption).
  clear FRS FRB HS HX MU2 WM2 MU WM.
  step.
  match goal with H : rw_cells rsegs ?mm 0x343d8 [C8 ?v] |- _ =>
    assert (HS3 : bytes_at rsegs mm 0x343d8 (le8 v))
      by (destruct H as [[_ Hb] _]; cbn [cells_bytes cbytes] in Hb; rewrite ?app_nil_r in Hb; exact Hb) end.
  match goal with H : munch [(lo, _); _] m ?mm |- _ =>
    assert (HX3 : bytes_at rsegs mm sh (x ++ [Z_to_bv 8 0]))
      by (apply (bytes_at_transport rsegs _ m mm _ _ (proj2 HX0) H); cbn [disjoint_from];
          rewrite length_app; cbn [length]; repeat split; lia) end.
  eapply an_run_tail.
  all: first [eassumption | lia | (intros; reflexivity)].
Qed.

Lemma an_run_pre : snprintf_contract -> mix_call_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo rf code h c sh fn : Z) (x : list byte)
    (args : list (word * list byte)) (canary : word),
  -2 ^ 31 <= rf < 2 ^ 31 -> bytes_at rsegs m 0x34028 (le4 (Z_to_bv 64 rf)) ->
  rw_cells rsegs m 0x343d8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 4128 + SNPRINTF_K <= bv_unsigned sp ->
  lo + 4128 + MIX_CALL_FRAME <= bv_unsigned sp -> 2 ^ 21 <= lo -> bv_unsigned sp < 2 ^ 63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> bv_unsigned sp <= TASK_SIZE ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  (rf <> 0 -> -2 ^ 31 <= code < 2 ^ 31 /\ bytes_at rsegs m 0x3402c (le4 (Z_to_bv 64 code))) ->
  (rf = 0 -> no0 x /\ Z.of_nat (length x) <= LMAX /\ Z.of_nat (length (inst x)) <= 4095 /\
     1 <= sh /\ sh + Z.of_nat (length x) + 1 <= lo /\
     (sh + Z.of_nat (length x) + 1 <= 0x343d8 \/ 0x343e0 <= sh) /\ bytes_at rsegs m sh (x ++ [Z_to_bv 8 0])) ->
  (rf = 0 -> bv_unsigned a2 <> 0 ->
     -2 ^ 31 <= fn < 2 ^ 31 /\ (length args <= 6)%nat /\
     bytes_at rsegs m c (le4 (Z_to_bv 64 fn) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) /\
     1 <= c /\ c mod 8 = 0 /\ c + 56 <= 0x343d8 /\
     (forall m', munch [(lo, bv_unsigned sp); (0x343d8, 0x343e0)] m m' ->
        forall k p, nth_error args k = Some p ->
          mc_arg m' (bv_unsigned sp - 4128 - MIX_CALL_FRAME) (bv_unsigned sp - 4128) c k p)) ->
  evt rsegs (an_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo
               (if rf =? 0 then inst x else resp code)
               (if (rf =? 0) && negb (bv_unsigned a2 =? 0) then mixcall h fn (map snd args) else h) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 sh) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs)).
Proof.
  intros SNP MIX ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo rf code h c sh fn x args canary RF HRF HS Hh ST LO1 LO2 IE S63 FRM MI TM HTS GG GW HR HX HC.
  assert (HSb : bytes_at rsegs m 0x343d8 (le8 (Z_to_bv 64 h))).
  { destruct HS as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite ?app_nil_r in Hb. exact Hb. }
  unfold SNPRINTF_K, MIX_CALL_FRAME in *.
  destruct (Z.eqb_spec rf 0) as [R0|R0].
  - subst rf. cbn [andb].
    destruct (HX eq_refl) as (X0 & XL & FIT & SHB & SEP & SST & HXb).
    destruct (Z.eqb_spec (bv_unsigned a2) 0) as [A0|A0]; cbn [negb].
    + eapply an_run_nochg; first [eassumption | lia].
    + destruct (HC eq_refl A0) as (Hfn & LA & EF & C0 & CM8 & C1 & HARG).
      eapply (an_run_chg MIX); first [eassumption | lia | exact HARG].
  - destruct (HR R0) as (HCd & HCb). cbn [andb].
    eapply (an_run_resp SNP) with (rf := rf) (canary := canary); first [eassumption | lia | (unfold SNPRINTF_K; lia)].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecAnsB RecGlue
  hand_back_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require RecStep hand_back.
Local Open Scope Z_scope.

Lemma anu_cells_rebytes : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf' | rewrite Eb; exact Hb]|].
  rewrite Es. exact Hw.
Qed.

Lemma anu_rc_cell8 : forall m a v, GLOB_LO <= a -> a + 8 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le8 v) -> rw_cells rsegs m a [C8 v].
Proof.
  intros m a v H1 H2 H. apply (anu_cells_rebytes _ _ [CB (length (le8 v)) (le8 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le8; lia | exact H].
  - cbn. split; exact I.
  - reflexivity.
  - cbn [cells_size csize]. rewrite length_le8. reflexivity.
Qed.


Lemma an_cells : forall L A mem R O, g_rec_rep rsegs L A mem R O ->
  bytes_at rsegs mem 0x34028 (le4 (Z_to_bv 64 (r_refuse R))) /\
  bytes_at rsegs mem 0x3402c (le4 (Z_to_bv 64 (r_code R))) /\
  rw_cells rsegs mem 0x343d8 [C8 (Z_to_bv 64 (r_state R))] /\
  -2 ^ 31 <= r_refuse R < 2 ^ 31 /\ -2 ^ 31 <= r_code R < 2 ^ 31 /\ 0 <= r_state R < 2 ^ 64.
Proof.
  intros L A mem R O GR.
  destruct GR as (Q & HRep & HO).
  destruct HRep as (HS & HC & HA & HP & HX & HW).
  destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  split; [replace 0x34028 with (G_REC + OFF_REFUSE) by (unfold G_REC, OFF_REFUSE; lia); exact X1|].
  split; [replace 0x3402c with (G_REC + OFF_CODE) by (unfold G_REC, OFF_CODE; lia); exact X2|].
  split.
  { apply anu_rc_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x343d8 with (G_REC + OFF_STATE) by (unfold G_REC, OFF_STATE; lia). exact X4. }
  split; [exact X6|]. split; [exact X7 | exact X9].
Qed.

Lemma an_shape : forall mem sh x, ans_shape rsegs mem sh x -> 0 <= sh < 2 ^ 63 ->
  no0 x /\ Z.of_nat (length x) <= LMAX /\ Z.of_nat (length (inst x)) <= 4095 /\
  sh + Z.of_nat (length x) + 1 <= 2 ^ 20 /\
  (sh + Z.of_nat (length x) + 1 <= 0x343d8 \/ 0x343e0 <= sh) /\ bytes_at rsegs mem sh (x ++ [Z_to_bv 8 0]).
Proof.
  intros mem sh x (HB & X0 & XL & FT & RO) Hsh.
  unfold fits, PHD_LINE_MAX in FT. unfold LMAX in XL.
  assert (HI : sh + Z.of_nat (length x) < 2 ^ 20).
  { destruct (Z.lt_ge_cases (sh + Z.of_nat (length x)) (2 ^ 20)) as [H|H]; [exact H|].
    pose proof (RO (Z.of_nat (length x)) ltac:(lia)) as E. rewrite ro_addr_hi in E by lia. discriminate. }
  assert (HG : sh + Z.of_nat (length x) + 1 <= 0x343d8 \/ 0x343e0 <= sh).
  { destruct (Z.le_gt_cases (sh + Z.of_nat (length x) + 1) 0x343d8) as [H|H]; [left; exact H|].
    destruct (Z.le_gt_cases 0x343e0 sh) as [H2|H2]; [right; exact H2|]. exfalso.
    set (i := Z.max 0 (0x343d8 - sh)).
    pose proof (RO i ltac:(unfold i; lia)) as E.
    assert (G : ro_addr rsegs (wa (sh + i)) = false) by (apply glob_ro_false; unfold i, GLOB_LO, GLOB_N; lia).
    unfold wa in G. first [rewrite G in E; discriminate | cbv [wa] in G; congruence]. }
  split; [exact X0|]. split; [unfold LMAX; exact XL|]. split; [lia|]. split; [lia|]. split; [exact HG | exact HB].
Qed.

Lemma an_inst_go_no0 : forall s d, no0 s -> no0 (inst_go d s).
Proof.
  unfold no0. induction s as [|b s IH]; intros d H; cbn [inst_go]; [intro F; exact F|].
  assert (Hs : ~ In (Z_to_bv 8 0) s) by (intro F; apply H; right; exact F).
  assert (Hb : b <> Z_to_bv 8 0) by (intro E; apply H; left; exact E).
  destruct d as [|d'].
  - destruct (bv_unsigned b =? 60).
    + intros [E|F]; [exact (no0_nz [Z_to_bv 8 49] ltac:(vm_compute; reflexivity) (or_introl E)) | exact (IH 1%nat Hs F)].
    + intros [E|F]; [exact (Hb E) | exact (IH O Hs F)].
  - destruct (bv_unsigned b =? 60); [exact (IH _ Hs)|].
    destruct (bv_unsigned b =? 62); exact (IH _ Hs).
Qed.

Lemma an_combine_snd : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H |- *; try discriminate; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

Lemma an_nth_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) k a b,
  nth_error (combine l1 l2) k = Some (a, b) -> nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|k] a b H; cbn in H; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH l2 k a b H).
Qed.

Lemma an_pad_le : forall e c a, e <= c -> a < e + (- e) mod 8 -> a < 8 * ((c + 7) / 8).
Proof.
  intros e c a H1 H2.
  pose proof (Z.div_mod (- e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)).
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma an_rw_cj : forall m a cs, ro_agree rsegs m -> GLOB_LO <= a ->
  a + Z.of_nat (cells_size cs) <= GLOB_LO + Z.of_nat GLOB_N -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize_cj rsegs m) a cs.
Proof.
  intros m a cs RA H1 H2 H. apply (rw_cells_transfer rsegs m); [exact H|].
  intros i Hi.
  assert (NE : normalize_cj rsegs m (wa (a + i)) = m (wa (a + i))).
  { unfold normalize_cj. rewrite (MemNorm.cj_drop_false_intro rsegs (wa (a + i))); [reflexivity | apply glob_ro_false; lia |].
    right. unfold wa. rewrite unsigned_lit by (unfold GLOB_LO, GLOB_N in *; lia). unfold TASK_SIZE, GLOB_LO, GLOB_N in *. lia. }
  unfold wa in NE. unfold mbyte, writable_at, wview, mrd. rewrite NE. split; [reflexivity | tauto].
Qed.

Lemma an_low_same : forall mem m' lo sp a, ro_agree rsegs mem ->
  munch [(lo, sp); (0x343d8, 0x343e0)] (normalize_cj rsegs mem) m' ->
  0 <= a < lo -> lo <= TASK_SIZE -> ~ (0x343d8 <= a < 0x343e0) ->
  mbyte rsegs m' a = mbyte rsegs mem a.
Proof.
  intros mem m' lo sp a RA MU Ha HT Hn. unfold TASK_SIZE in HT.
  rewrite (munch_mbyte _ _ _ _ _ MU) by (first [lia | cbn; split; [lia | split; [lia | exact I]]]).
  unfold mbyte. apply (mrd_normalize_cj rsegs mem _ RA). right. right. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
Qed.

Ltac an_pres X5 X1 G4 R1 :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X5 eq_refl); simp_regs;
    transitivity (getr R1 (Z_to_bv 5 k)); [exact (G4 k ltac:(unfold callee_saved; lia))|];
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X1 eq_refl); simp_regs; reflexivity
  end.

Lemma an_set_state_same : forall R, set_state R (r_state R) = R.
Proof. intros R. destruct R. reflexivity. Qed.

Section AH.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GUARDG : ms_guard B = 0x54730.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis REC_IMG : forall a, rec_area a -> in_img B a /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis REC_NO : forall L A mem md a, aa_MR API L A mem md -> rec_area a -> ~ owned B L A a.
Hypothesis SNP : snprintf_contract.
Hypothesis HB : forall fx' : YK11.FPState, @hand_back_contract fx' rc B API.
Hypothesis MIX : mix_call_contract.

Lemma an_mc_arg : forall L A mem md c k q n s lo hi lo' sp' m',
  aa_MR API L A mem md -> ro_agree rsegs mem ->
  (forall q0 k0 a, In (q0, k0) (blocks L A) -> q0 + k0 <= a < 8 * ((q0 + k0 + 7) / 8) -> present mem a) ->
  bytes_at rsegs mem (c + CALL_OFF_ARGS + 8 * Z.of_nat k) (le8 (Z_to_bv 64 q)) ->
  In (q, n) (blocks L A) -> Z.of_nat (length s) + 1 <= n ->
  bytes_at rsegs mem q (s ++ [Z_to_bv 8 0]) -> no0 s -> Z.of_nat (length s) <= LMAX ->
  alloc_ceiling <= lo -> alloc_ceiling <= lo' -> 0x343e0 <= lo' -> lo' <= TASK_SIZE -> 0 <= c ->
  c + CALL_OFF_ARGS + 8 * Z.of_nat k + 8 <= 0x343d8 ->
  (forall i, 0 <= i < n -> ~ rec_area (q + i)) ->
  munch [(lo', sp'); (0x343d8, 0x343e0)] (normalize_cj rsegs mem) m' ->
  mc_arg m' lo hi c k (Z_to_bv 64 q, s).
Proof.
  intros L A mem md c k q n s lo hi lo' sp' m' HM RA PAD BP Hb Hn BS N0 LX HLO HLO' HLO2 HT C0 HC NRA MU.
  unfold CALL_OFF_ARGS in BP, HC.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_value as ACV.
  pose proof Hb as Hb0.
  unfold blocks in Hb. apply in_map_iff in Hb as ([u n'] & Eu & Hu). cbn in Eu. injection Eu as E0 E2. subst n'.
  assert (E1 : ptr_addr L u = q) by (rewrite <- E0; reflexivity). clear E0.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  destruct (mr_blocks B _ LAWS L A mem md u n 0 HM Hu ltac:(lia)) as (_ & HQ1 & HQ2 & _). rewrite E1 in HQ1, HQ2.
  pose proof (Z.mod_pos_bound (- (q + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hpad.
  assert (CE : forall a, a < q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 ->
            a < alloc_ceiling).
  { intros a Ha. pose proof (an_pad_le (q + Z.of_nat (length s) + 1) (q + n) a ltac:(lia) Ha) as X.
    pose proof (Z.div_mod (q + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)). destruct ACV as (_ & ACM). lia. }
  destruct (hand_back.hb_bytes_pad rsegs mem q (s ++ [Z_to_bv 8 0])
              (Z.to_nat ((- (q + Z.of_nat (length s) + 1)) mod 8)) BS) as (sl & LS & BS2).
  - rewrite length_app. cbn [length].
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
  - intros j Hj. rewrite length_app. cbn [length].
    destruct (Z_lt_le_dec (q + Z.of_nat (length s + 1) + Z.of_nat j) (q + n)) as [Hl|Hl].
    + destruct (mr_blocks B _ LAWS L A mem md u n (Z.of_nat (length s + 1) + Z.of_nat j) HM Hu ltac:(lia))
        as (Hp & _).
      rewrite E1 in Hp. destruct Hp as [bb E]. unfold mbyte.
      replace (q + Z.of_nat (length s + 1) + Z.of_nat j) with (q + (Z.of_nat (length s + 1) + Z.of_nat j)) by ring.
      rewrite E. discriminate.
    + destruct (PAD q n (q + Z.of_nat (length s + 1) + Z.of_nat j) Hb0) as [bb E].
      * split; [exact Hl|]. apply (an_pad_le (q + Z.of_nat (length s) + 1) (q + n)); lia.
      * unfold mbyte. rewrite E. discriminate.
  - assert (LSZ : Z.of_nat (length sl) = (- (q + Z.of_nat (length s) + 1)) mod 8)
      by (rewrite LS, Z2Nat.id by lia; reflexivity).
    assert (NW : forall a, q <= a < q + Z.of_nat (length s) + 1 + Z.of_nat (length sl) ->
              0 <= a < lo' /\ ~ (0x343d8 <= a < 0x343e0)).
    { intros a Ha. pose proof (CE a ltac:(lia)) as Ca. split; [lia|]. intros Hw.
      destruct (Z_lt_le_dec a (q + n)) as [Hl|Hl].
      - apply (NRA (a - q)); [lia|]. replace (q + (a - q)) with a by ring.
        unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia.
      - apply (NRA (n - 1)); [lia|]. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia. }
    unfold mc_arg. cbn [fst snd]. rewrite unsigned_lit by lia.
    split.
    { apply (bytes_at_transfer _ mem); [exact BP|]. intros i Hi.
      replace (Z.of_nat (length (le8 (Z_to_bv 64 q)))) with 8 in Hi by reflexivity.
      apply (an_low_same mem m' lo' sp'); [exact RA | exact MU | lia | exact HT | lia]. }
    split; [exact N0|]. split; [exact LX|].
    pose proof (mr_blocks_range B _ LAWS L A mem md u n HM Hu) as RG. rewrite E1 in RG.
    split; [lia|]. split; [lia|].
    exists sl. rewrite <- app_assoc in BS2. cbn [app] in BS2.
    split.
    { apply (bytes_at_transfer _ mem); [exact BS2|]. intros i Hi.
      rewrite length_app in Hi. cbn [length] in Hi.
      destruct (NW (q + i) ltac:(lia)) as [N1 N2].
      apply (an_low_same mem m' lo' sp'); [exact RA | exact MU | exact N1 | exact HT | exact N2]. }
    rewrite LSZ. split; [lia|]. left.
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
Qed.

Theorem answer_holds : answer_contract B API.
Proof using SEGS ERRNO_LOW GOTG GUARDG AX CTX REC_IMG REC_NO SNP HB MIX.
  unfold answer_contract, answer_ret.
  intros L A regs mem md R O c sh e x chg b PRE A10 A11 CHG REP SHP ENT FZ F18 RES ROOM RA.
  destruct PRE as [PRE HTS].
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  assert (KV : ANSWER_K = 12384) by reflexivity.
  assert (HBK : HAND_BACK_K = 8256) by reflexivity.
  rewrite KV in PRE |- *.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  change (getr regs 12) with (reg_get regs 12) in CHG.
  rewrite SEGS in RA, HWS, HERR, F18, REP, SHP.
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb0] _]. cbn [cells_bytes cbytes] in Hb0. rewrite app_nil_r in Hb0. exact Hb0. }
  assert (GWb : bytes_at rsegs mem snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb0] _]. cbn [cells_bytes cbytes] in Hb0. rewrite app_nil_r in Hb0. exact Hb0. }
  assert (ST0 : stk rsegs (normalize_cj rsegs mem) (bv_unsigned sp - 12384) (bv_unsigned sp))
    by (apply stk_normalize_cj; [lia | exact HTS | intros a Ha; apply HWS; lia]).
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GUARD (Mem.le8 canary) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  destruct (an_cells L A mem R O REP) as (CR & CC & CS & RFR & RCR & RSR).
  pose proof (bytes_at_normalize_cj_low rsegs mem 0x34028 (le4 (Z_to_bv 64 (r_refuse R))) RA
    ltac:(rewrite length_le4; unfold TASK_SIZE; lia) CR) as CRn.
  pose proof (bytes_at_normalize_cj_low rsegs mem 0x3402c (le4 (Z_to_bv 64 (r_code R))) RA
    ltac:(rewrite length_le4; unfold TASK_SIZE; lia) CC) as CCn.
  pose proof (an_rw_cj mem 0x343d8 [C8 (Z_to_bv 64 (r_state R))] RA ltac:(unfold GLOB_LO; lia)
    ltac:(cbn; unfold GLOB_LO, GLOB_N; lia) CS) as CSn.
  assert (XF : r_refuse R = 0 -> no0 x /\ Z.of_nat (length x) <= LMAX /\ Z.of_nat (length (inst x)) <= 4095 /\
      sh + Z.of_nat (length x) + 1 <= 2 ^ 20 /\ (sh + Z.of_nat (length x) + 1 <= 0x343d8 \/ 0x343e0 <= sh) /\
      bytes_at rsegs mem sh (x ++ [Z_to_bv 8 0]) /\ 1 <= sh).
  { intros R0. pose proof (SHP R0) as SS. pose proof SS as (SB & _ & _ & _ & SRO).
    pose proof (bytes_at_bound _ _ _ _ SB) as BB. rewrite length_app in BB. cbn [length] in BB.
    assert (S63 : sh < 2 ^ 63).
    { destruct (Z.lt_ge_cases sh (2 ^ 20)) as [H|H]; [lia|].
      pose proof (SRO 0 ltac:(lia)) as E. rewrite Z.add_0_r in E. rewrite ro_addr_hi in E by lia. discriminate. }
    destruct (an_shape mem sh x SS ltac:(lia)) as (X1 & X2 & X3 & X4 & X5 & X6).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. destruct (Z.eq_dec sh 0) as [E0|E0]; [|lia]. exfalso.
    pose proof (SRO 0 ltac:(lia)) as E. rewrite E0 in E. vm_compute in E. discriminate. }
  assert (EP : exists P, r_refuse R = 0 -> chg = true ->
      call_at rsegs (blocks L A) mem c e P /\ 1 <= c /\ c mod 8 = 0 /\ c + 56 <= 0x343d8 /\
      Forall (fun s => Z.of_nat (length s) <= LMAX) (snd e)).
  { destruct (Z.eq_dec (r_refuse R) 0) as [R0|R0]; [|exists []; intros H; contradiction].
    destruct chg; [|exists []; intros _ H; discriminate].
    destruct (ENT R0 eq_refl) as [EN _].
    pose proof REP as (Q & (_ & GC & _) & _).
    destruct GC as (CL & CQ & _ & CI & CS0 & CSL).
    destruct EN as [(k & Ek & ->)|(-> & ->)].
    - assert (Hk : (k < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ek; discriminate).
      destruct (nth_error (l_calls Q) k) as [P|] eqn:EPk; [|apply nth_error_None in EPk; lia].
      destruct (CI k e P Ek EPk) as (CA & CF).
      exists P. intros _ _. split; [exact CA|].
      unfold G_REC, OFF_CALLS, CALL_SIZE. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia | exact CF].
    - exists (l_spill Q). intros _ _. split; [exact CS0|]. unfold REC_SC. split; [lia|]. split; [reflexivity|]. split; [lia | exact CSL]. }
  destruct EP as (P & HP).
  assert (TF : no0 (if r_refuse R =? 0 then inst x else resp (r_code R)) /\
               (length (if (r_refuse R =? 0)%Z then inst x else resp (r_code R)) <= 4095)%nat).
  { destruct (Z.eqb_spec (r_refuse R) 0) as [R0|R0]; cbv iota.
    - destruct (XF R0) as (X1 & _ & X3 & _). split; [unfold inst; apply an_inst_go_no0; exact X1 | lia].
    - pose proof (resp_length (r_code R) RCR). split; [apply resp_no0 | lia]. }
  assert (EA : rec_answer R e x chg = hand_back (if r_refuse R =? 0 then (if chg then rec_mix R e else R) else R)
                 (if r_refuse R =? 0 then inst x else resp (r_code R)))
    by (unfold rec_answer; destruct (r_refuse R =? 0); reflexivity).
  assert (ET : snd (rec_answer R e x chg) = if r_refuse R =? 0 then inst x else resp (r_code R))
    by (rewrite rec_answer_text; reflexivity).
  set (args := combine (map (fun pn => Z_to_bv 64 (fst pn)) P) (snd e)).
  set (tm := if r_refuse R =? 0 then inst x else resp (r_code R)) in *.
  set (R' := if r_refuse R =? 0 then (if chg then rec_mix R e else R) else R) in *.
  set (h' := if (r_refuse R =? 0) && negb (bv_unsigned (reg_get regs 12) =? 0)
             then mixcall (r_state R) (fst e) (map snd args) else r_state R).
  destruct TF as (T0 & TL).
  assert (ER : set_state R h' = R').
  { unfold h', R'. destruct (Z.eqb_spec (r_refuse R) 0) as [R0|R0].
    - destruct (Z.eqb_spec (bv_unsigned (reg_get regs 12)) 0) as [Z0|Z0].
      + assert (CF : chg = false)
          by (rewrite CHG; first [reflexivity | apply negb_false_iff; apply Z.eqb_eq; exact Z0]).
        rewrite CF. exact (an_set_state_same R).
      + assert (CT : chg = true)
          by (rewrite CHG; first [reflexivity | apply negb_true_iff; apply Z.eqb_neq; exact Z0]). rewrite CT.
        destruct (HP R0 CT) as ((_ & _ & CLP & _) & _).
        unfold rec_mix, args. rewrite an_combine_snd; [reflexivity|]. rewrite length_map. exact CLP.
    - exact (an_set_state_same R). }
  assert (HR' : 0 <= h' < 2 ^ 64).
  { unfold h'. destruct ((r_refuse R =? 0) && negb (bv_unsigned (reg_get regs 12) =? 0));
      [apply mixcall_range; exact RSR | exact RSR]. }
  assert (ET2 : snd (hand_back R' tm) = tm) by (rewrite <- EA; exact ET).
  rewrite ET in ROOM |- *. rewrite EA.
  assert (BRNG : forall q k, In (q, k) (blocks L A) -> 4096 <= q /\ q + k <= alloc_ceiling).
  { intros q k Hq. unfold blocks in Hq. apply in_map_iff in Hq as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
    exact (mr_blocks_range B _ LAWS L A mem md p k' HMR Hp). }
  assert (BNR : forall q k i, In (q, k) (blocks L A) -> 0 <= i < k -> ~ rec_area (q + i)).
  { intros q k i Hq Hi. unfold blocks in Hq. apply in_map_iff in Hq as ([pq kq] & Eq & Uq). cbn [fst snd] in Eq.
    injection Eq as <- <-.
    pose proof (ax_blocks_img AX L A mem md pq kq i HMR Uq Hi) as NI.
    intros Hra. exact (NI (proj1 (REC_IMG _ Hra))). }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 c) by exact A10. rewrite R10.
    assert (R11 : reg_get regs 11 = Z_to_bv 64 sh) by exact A11. rewrite R11.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    apply (an_run_pre SNP MIX) with (lo := bv_unsigned sp - 12384) (rf := r_refuse R) (code := r_code R)
      (h := r_state R) (fn := fst e) (args := args) (canary := canary) (x := x);
      [exact RFR | exact CRn | exact CSn | exact RSR | exact ST0 | unfold SNPRINTF_K; lia | unfold MIX_CALL_FRAME; lia
      | lia | lia | exact FZ
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mem)) | exact HTS
      | exact GGn | exact GWn | | | ].
    - intros _. split; [exact RCR | exact CCn].
    - intros R0. destruct (XF R0) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X7|]. split; [lia|].
      split; [exact X5|].
      apply bytes_at_normalize_cj_low; [exact RA | rewrite length_app; cbn [length]; unfold TASK_SIZE; lia | exact X6].
    - intros R0 A2.
      assert (CT : chg = true) by (rewrite CHG; apply negb_true_iff; apply Z.eqb_neq; exact A2).
      destruct (HP R0 CT) as (CA & C0 & CM8 & C1 & CF).
      destruct CA as (CF0 & CL6 & CLP & CFN & CNA & CND & CKA).
      assert (LP : length (map (fun pn => Z_to_bv 64 (fst pn)) P) = length (snd e)) by (rewrite length_map; exact CLP).
      assert (LA : length args = length (snd e)) by (unfold args; rewrite length_combine, LP; lia).
      split; [unfold REC_FN_COUNT in CF0; lia|].
      split; [rewrite LA; exact CL6|].
      split.
      { apply bytes_at_normalize_cj_low; [exact RA | rewrite length_app, !length_le4; unfold TASK_SIZE; lia |].
        apply bytes_at_app. split.
        - unfold CALL_OFF_FN in CFN. rewrite Z.add_0_r in CFN. exact CFN.
        - rewrite LA. replace (c + Z.of_nat (length (le4 (Z_to_bv 64 (fst e))))) with (c + CALL_OFF_NARGS)
            by (rewrite length_le4; unfold CALL_OFF_NARGS; reflexivity). exact CNA. }
      split; [lia|]. split; [exact CM8|]. split; [exact C1|].
      intros m' MU k [w s] Hk. destruct (an_nth_combine _ _ _ _ k w s Hk) as (Hw & Hs).
      rewrite nth_error_map in Hw. destruct (nth_error P k) as [pn|] eqn:EPn; cbn in Hw; [|discriminate].
      injection Hw as <-.
      destruct (CKA k s pn Hs EPn) as (BP & PNZ & PIN & PSZ & PBS & PN0).
      assert (Kk : (k < length (snd e))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
      destruct pn as [q n]. cbn [fst snd] in BP, PNZ, PIN, PSZ, PBS.
      apply (an_mc_arg L A mem md c k q n s _ _ (bv_unsigned sp - 12384) (bv_unsigned sp) m');
        [exact HMR | exact RA | exact (proj2 (ENT R0 CT)) | exact BP | exact PIN | lia | exact PBS | exact PN0
        | rewrite Forall_forall in CF; apply CF; exact (nth_error_In _ _ Hs)
        | unfold MIX_CALL_FRAME; lia | lia | lia | unfold TASK_SIZE in *; lia | lia | unfold CALL_OFF_ARGS; lia
        | | exact MU].
      intros i Hi. exact (BNR q n i PIN Hi). }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & s0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1n
    & slack & -> & MU1n & WM1n & FRM1 & FK1 & SL & BUF1n & FRS1n & HS1n).
  fold tm in SL, BUF1n.
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (rw_cells_rel_cj rsegs _ _ _ _ MR1r FRS1n) as FRS1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r BUF1n) as BUF1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r HS1n) as HS1.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  clear MU1n WM1n FRS1n BUF1n HS1n EQ1 MR1r.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16418) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -4128))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (bv_unsigned sp + -4120))
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 4128) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 12384 <= a < bv_unsigned sp) ->
            ~ (0x343d8 <= a < 0x343e0) -> outside [(bv_unsigned sp - 12384, bv_unsigned sp); (0x343d8, 0x343e0)] a)
    by (intros a _ H1 H2; cbn; split; [exact H1 | split; [exact H2 | exact I]]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUTW; [lia | lia |]].
      intro Hw. apply (REC_NO _ _ _ _ a HMR); [unfold rec_area, G_REC, REC_SIZE; lia | exact Ho].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUTW; [lia | lia |] | exact Hp].
      intro Hw. apply (REC_NO _ _ _ _ a HMR); [unfold rec_area, G_REC, REC_SIZE; lia | exact Ho].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & _).
      assert (Hb : In (ptr_addr L p, n) (blocks L A))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A) (p, n) Hin)).
      pose proof (BRNG _ _ Hb) as RG. pose proof (BNR _ _ i Hb Hi) as NR.
      eapply munch_present; [exact MU1 | lia | apply OUTW; [lia | lia |] | exact Hp].
      intro Hw. apply NR. unfold rec_area, G_REC, REC_SIZE. lia.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  assert (REP1 : g_rec_rep rsegs L A m1 R' O).
  { rewrite <- ER. unfold g_rec_rep in REP |- *.
    apply (RecStep.rec_rep_set_state rsegs G_REC REC_SC L A mem m1 R O h' REP HR').
    - replace (G_REC + OFF_STATE) with 0x343d8 by (unfold G_REC, OFF_STATE; lia). exact HS1.
    - intros a Ha N. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, OFF_STATE in Ha, N.
      apply (munch_mbyte rsegs _ mem m1 a MU1); [lia|]. apply OUTW; lia.
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros p k i Hin Hi. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) as Hb.
      pose proof (BRNG _ _ Hb) as RG. pose proof (BNR p k i Hb Hi) as NR.
      apply (munch_mbyte rsegs _ mem m1 _ MU1); [lia|]. apply OUTW; [lia | lia |].
      intro Hw. apply NR. unfold rec_area, G_REC, REC_SIZE. lia. }
  rewrite <- SEGS.
  eapply SR_bind.
  { eapply (HB (mkFP F1 fc1) L A R1 m1 md (bv_unsigned sp - 4120) tm slack R' O b).
    - rewrite HBK. split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
      split; [rewrite SP1; replace (bv_unsigned sp - 4128) with (bv_unsigned sp + (-258) * 16) by ring;
              rewrite Z.mod_add by lia; exact HAL|].
      split; [rewrite SP1; lia|].
      split; [rewrite SP1; lia|].
      split; [intros a Ha; rewrite SP1 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
      split; [rewrite E1_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
      intros HI. specialize (HAUX HI). rewrite SP1.
      destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
      exists av, ar.
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
        assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
        destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUTW; [lia | lia |]].
        intro Hw. apply (REC_NO _ _ _ _ (ms_libc B + 8 + Z.of_nat k) HMR); [unfold rec_area, G_REC, REC_SIZE; lia | exact SO]. }
      split.
      { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
        split; [lia | apply OUTW; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUTW; lia]. }
      split.
      { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUTW; lia]. }
      lia.
    - rewrite E1_10. reflexivity.
    - rewrite SEGS. replace (bv_unsigned sp - 4120) with (bv_unsigned sp + -4120) by lia. exact BUF1.
    - exact T0.
    - unfold LMAX. lia.
    - rewrite SL. pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)) as DM. rewrite HAL in DM.
      pose proof (Z.mod_pos_bound (- (bv_unsigned sp - 4120 + Z.of_nat (length tm) + 1)) 8 ltac:(lia)) as MB.
      pose proof (Z.div_mod (- (bv_unsigned sp - 4120 + Z.of_nat (length tm) + 1)) 8 ltac:(lia)) as DM2.
      lia.
    - right. rewrite SP1. lia.
    - left. rewrite SP1. lia.
    - rewrite SEGS. exact REP1.
    - intros [q k] Hin. pose proof (BRNG q k (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin)).
      unfold iv_apart. cbn [fst snd]. rewrite length_app. cbn [length]. lia.
    - exact RES.
    - exact ROOM.
    - rewrite SEGS. exact RA1. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p1 & p2 & old & O2 & -> & OLD & POST2 & A0' & P12 & AL1 & AL2 & FR1
    & FR2 & BLK & KEPT & UB & REP2 & OREL & ONO & BIND & BP1 & BP2 & BS & RA2 & GK2 & INIT2 & REG2 & GR2 & RES2).
  destruct POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HP2 & HVM2 & HFR2 & HBLKS2 & HSCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (c1 & c2 & COLD & CIFF & NP1 & NP2).
  rewrite ET2 in BP2.
  set (n := Z.of_nat (length tm) + 1) in *.
  assert (G2 : forall r, callee_saved r -> reg_get R2 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (HP2 r Hr). unfold getr.
    assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 5) with 32. unfold callee_saved in Hr. rewrite Z.mod_small by lia.
      change (bv_unsigned 0) with 0. lia. }
    rewrite NZ. reflexivity. }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -4128))
    by exact (eq_trans (G2 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (DOM : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     (forall q k, In (q, k) (blocks L A) -> ~ (q <= a < q + k)) /\ ~ (p1 <= a < p1 + n) /\ ~ (p2 <= a < p2 + n)).
  { intros a Ha. split; [|split].
    - intros q k Hq Hin. unfold blocks in Hq. apply in_map_iff in Hq as ([pq kq] & Eq & Uq). cbn [fst snd] in Eq.
      injection Eq as <- <-.
      pose proof (mr_blocks_range B _ LAWS L A mem md pq kq HMR Uq).
      pose proof (ax_blocks_img AX L A mem md pq kq (a - ptr_addr L pq) HMR Uq ltac:(lia)) as NI.
      replace (ptr_addr L pq + (a - ptr_addr L pq)) with a in NI by ring.
      destruct Ha as [Ha|Ha]; [lia | exact (NI Ha)].
    - intros Hin. destruct FR1 as (F1a & F1b & F1c). pose proof (F1c (a - p1) ltac:(lia)) as NI.
      replace (p1 + (a - p1)) with a in NI by ring. destruct Ha as [Ha|Ha]; [lia | exact (NI Ha)].
    - intros Hin. destruct FR2 as (F2a & F2b & F2c). pose proof (F2c (a - p2) ltac:(lia)) as NI.
      replace (p2 + (a - p2)) with a in NI by ring. destruct Ha as [Ha|Ha]; [lia | exact (NI Ha)]. }
  assert (HF12 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 12384 <= a < bv_unsigned sp - 4128) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. destruct (DOM a (or_introl Ha)) as (D1 & D2 & D3).
    apply HFR2; [left; exact Ha | intro Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho); lia
      | intro Ho; destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho); lia
      | unfold scratch_k; rewrite SP1, HBK; intros [H|H]; lia |].
    intros [H|[(k & Hk & H)|[H|H]]];
      [unfold G_REC, OFF_ANSWER in H; lia | exact (D1 old k Hk H) | apply D2; unfold n; lia | apply D3; unfold n; lia]. }
  assert (FRS2 : rw_cells rsegs m2 (bv_unsigned sp + -24) [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FRS1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF12 (bv_unsigned sp + -24 + i) ltac:(lia) ltac:(lia)) as [E12 W12].
    split; [exact E12 | tauto]. }
  assert (GK : forall i, 0 <= i < 8 ->
     mbyte (ms_segs B) m2 (ms_got_guard B + i) = mbyte (ms_segs B) mem (ms_got_guard B + i)).
  { intros i Hi. rewrite (GK2 i Hi). rewrite GOTG.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUTW; lia]. }
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite E1_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. rewrite E2_2.
    eapply an_run_ret with (s0v := reg_get regs 8) (s1v := reg_get regs 9) (rav := reg_get regs 1).
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp + -4128 + 4104) with (bv_unsigned sp + -24) by ring.
      exact FRS2.
    - rewrite unsigned_lit by lia. lia. }
  intros ms5 (can5 & Q5 & EQ5). subst can5.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ5) as (R5 & -> & X5). clear EQ5.
  rewrite <- SEGS.
  apply SR_ret. cbv beta zeta.
  exists (mkFP F1 fc1), L2, A2, R5, m2, md2, p1, p2, old, O2.
  split; [rewrite RP; reflexivity|].
  split.
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split.
  { apply (bytes_at_transfer _ m1); [exact OLD|]. intros i Hi. rewrite Mem.length_le8 in Hi.
    symmetry. apply (munch_mbyte _ _ _ _ _ MU1); [unfold G_REC, OFF_ANSWER; lia|].
    apply OUTW; unfold G_REC, OFF_ANSWER; lia. }
  split.
  { unfold call_post_rec.
    split; [exact HMR2|]. split; [exact HWF2|]. split; [exact HBD2|].
    split; [exact HLE2|].
    split; [exact HSTAB2|].
    split.
    { intros r Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
      destruct C as [C|C].
      { subst r. rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X5 eq_refl). simp_regs.
        rewrite unsigned_lit by lia. replace (bv_unsigned sp + -4128 + 4128) with (bv_unsigned sp) by ring.
        exact (Z_to_bv_lit_self sp). }
      destruct C as [C|C]; [subst r; an_pres X5 X1 G2 R1|].
      destruct C as [C|C]; [subst r; an_pres X5 X1 G2 R1|].
      destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ (Z_to_bv 5 8) X5 eq_refl); simp_regs; reflexivity|].
      destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ (Z_to_bv 5 9) X5 eq_refl); simp_regs; reflexivity|].
      repeat (destruct C as [C|C]; [subst r; an_pres X5 X1 G2 R1|]).
      subst r. an_pres X5 X1 G2 R1. }
    split; [exact HVM2|].
    split.
    { intros a Hd N1 N2 NS NE. unfold scratch_k, spZ in NS. change (getr regs 2) with sp in NS.
      unfold ans_writes in NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct Hd as [Hd|Hd]; [lia | pose proof (in_img_low B SEGS a Hd); lia]).
      destruct (DOM a Hd) as (D1 & D2 & D3).
      assert (OW : outside [(bv_unsigned sp - 12384, bv_unsigned sp); (0x343d8, 0x343e0)] a).
      { apply OUTW; [lia | intro H; apply NS; left; exact H | intro H; apply NE; right; unfold G_REC, OFF_STATE; lia]. }
      assert (E01 : mbyte (ms_segs B) m1 a = mbyte (ms_segs B) mem a)
        by (apply (munch_mbyte _ _ _ _ _ MU1); [lia | exact OW]).
      assert (W01 : writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m1 a)
        by (apply (munch_writable _ _ _ _ _ MU1); [lia | exact OW]).
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFR2; [exact Hd | exact N1 | exact N2
          | unfold scratch_k; rewrite SP1, HBK; intros [H|H]; [apply NS; left; lia | apply NS; right; exact H] |].
        intros [H|[(k & Hk & H)|[H|H]]];
          [apply NE; left; exact H | exact (D1 old k Hk H) | apply D2; unfold n; lia | apply D3; unfold n; lia]. }
      destruct H12 as [E12 W12].
      split; [rewrite E12, E01; reflexivity | tauto]. }
    split.
    { intros p k i H1 H2 Hne Hi.
      rewrite (HBLKS2 p k i H1 H2 Hne Hi).
      assert (Hb : In (ptr_addr L p, k) (blocks L A))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A) (p, k) H1)).
      pose proof (BRNG _ _ Hb) as RG. pose proof (BNR _ _ i Hb Hi) as NR.
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUTW; [lia | lia |]].
      intro Hw. apply NR. unfold rec_area, G_REC, REC_SIZE. lia. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 4128)) as [D1|D1].
    - apply HSCR2. unfold scratch_k. rewrite SP1, HBK. left. lia.
    - apply (proj2 (HF12 a ltac:(lia) ltac:(lia))). rewrite SEGS. apply WM1. apply HWS. lia. }
  split.
  { rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. exact A0'. }
  split; [exact P12|]. split; [exact AL1|]. split; [exact AL2|]. split; [exact FR1|]. split; [exact FR2|].
  split.
  { exists c1, c2. split; [exact COLD|]. split; [exact CIFF|]. split; [exact NP1 | exact NP2]. }
  split.
  { intros a k i Hin Hne Hi.
    rewrite (KEPT a k i Hin Hne Hi).
    pose proof (BRNG _ _ Hin) as RG. pose proof (BNR _ _ i Hin Hi) as NR.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUTW; [lia | lia |]].
    intro Hw. apply NR. unfold rec_area, G_REC, REC_SIZE. lia. }
  split; [exact UB|].
  split; [first [exact REP2 | rewrite SEGS in REP2 |- *; exact REP2]|].
  split; [exact OREL|]. split; [exact ONO|]. split; [exact BIND|].
  split; [exact BP1|]. split; [exact BP2|].
  split; [exact RA2|].
  split.
  { rewrite SEGS. destruct (ax_statics AX L2 A2 m2 md2 HMR2) as (_ & (g & Hg & HGW) & _).
    apply (f18_words_after mem m2 g F18); [| exact Hg | rewrite SEGS, GUARDG in HGW; exact HGW].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK i Hi). }
  split; [exact GK|].
  split; [exact INIT2|].
  split; [exact REG2|].
  split; [exact GR2 | exact RES2].
Qed.

End AH.
