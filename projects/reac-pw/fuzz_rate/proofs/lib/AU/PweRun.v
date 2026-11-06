(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (pa_int7's chain: the entry state, the run, the kept-byte and kept-register steps, the call through the runtime's intrinsic law, and the fresh entry state after it) and proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 (ck_leaf, the `ret` leaf into the caller's post); the composition is pod_write_ent's own -- four runs, two runtime calls and the leaf -- and the byte lemmas of the two put32s are new. *)
(* proves function pod_write_ent

   The composition of pod_write_ent's walk on reac-pw/fuzz_rate's image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address is measured on its unstripped
   twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the four engine runs of
   lib/AU/PweStates.v, entered by the four lemmas of lib/AU/PweWalk.v, the two runtime calls through the kit's
   intrinsic law, and the `ret` leaf into lib/AU/PweSpec.v's pod_write_ent_specX.

   THE ROUTE
     R0  0x83cc4 -> 0x83cf4   the prologue's five stores into [sp - 48, sp), the alignment test of e, and the two
                              8-byte loads that fetch the runtime's shadow offset through the image's GOT cell.
     R1  0x83cf4 -> 0x518b8   the two put32s at pp + len and pp + len + 4 under their guards and checks, the len
                              cell's two updates, and the `jal` of the runtime copy.
     the copy            __asan_memcpy(pp + len + 8, e + 8, size), through PweKit.pwe_intrin_at at OCpy.
     R2  0x83e94 -> 0x51d54   the len cell's update to len + 8 + size, the pad, and the `jal` of the runtime fill.
     the fill            __asan_memset(pp + len + 8 + size, 0, pad8 size), through pwe_intrin_at at OSet.
     R3  0x83edc -> 0x83f08   the len cell's update to len + n, the epilogue's five loads, and `ret`.

   WHAT THE PIECES GIVE. Each run keeps every byte outside the zone its write windows lie in (PweKit.pwe_kept_run),
   so the bytes outside [sp - T_pwe_STK, sp) and outside pwe_E pp len e are as at the call; that is the post's own
   memory clause, and PweWalk.pwe_shadow_kept turns it into the post's shadow clause, from which
   PweWalk.pwe_ra_kept_of_shadow gives the two "still marked usable" clauses. The bytes of the post's byte list come
   from the two put32s (read out of the run's own region at pp + len, by pwr_body_word below), from the copy's
   view equality on the body and from the fill's zero bytes, assembled by PweWalk.pwe_post_bytes. The len cell is
   read out of R3's len region. The registers the caller keeps are the five the prologue saved and restored, and
   the ones no run and neither call writes. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YG0q.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import PweSpec PweMem PweKit PweStates PweWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= arithmetic of the two put32s' bytes ======================= *)
(* two values that agree on their low byte give the same byte *)
Lemma pwr_bv8_mod : forall a b, a mod 256 = b mod 256 -> Z_to_bv 8 a = Z_to_bv 8 b.
Proof.
intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. exact H.
Qed.

(* a narrower modulus sees through a wider one *)
Lemma pwr_mod_pow : forall x a b, 0 <= b <= a -> (x mod 2 ^ a) mod 2 ^ b = x mod 2 ^ b.
Proof.
intros x a b (Hb & Hba).
assert (Hpb : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
assert (Hpa : 0 < 2 ^ (a - b)) by (apply Z.pow_pos_nonneg; lia).
assert (Hsplit : 2 ^ a = 2 ^ (a - b) * 2 ^ b)
  by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
assert (Hc : 0 < 2 ^ (a - b) * 2 ^ b) by (apply Z.mul_pos_pos; lia).
rewrite Hsplit.
rewrite (Z.div_mod x (2 ^ (a - b) * 2 ^ b)) at 2 by lia.
replace (2 ^ (a - b) * 2 ^ b * (x / (2 ^ (a - b) * 2 ^ b)))
  with ((2 ^ (a - b) * (x / (2 ^ (a - b) * 2 ^ b))) * 2 ^ b) by ring.
rewrite Z.add_comm, Z_mod_plus_full. reflexivity.
Qed.

(* the engine's logical shift right by a small literal *)
Lemma pwr_u_srl : forall E a s, 0 <= s < 64 -> Z.land s 63 = s ->
U E (SAlu ALU_SRL a (SLit s)) = (Z.shiftr (U E a) s) mod 2 ^ 64.
Proof.
intros E a s Hs Hl. rewrite U_SAlu, (U_lit E s) by lia.
cbn [zalu_raw]. rewrite Hl. unfold zcanon, M64. reflexivity.
Qed.

(* the engine's 32-bit sign extension *)
Lemma pwr_u_sext32 : forall E a, U E (SExt true 32 a) = (bv_swrap 32 (U E a mod 2 ^ 32)) mod 2 ^ 64.
Proof.
intros E a. rewrite U_SExt. change (2 ^ Z.of_N 32) with (2 ^ 32). unfold zcanon, M64. reflexivity.
Qed.

(* a 32-bit value, sign-extended and canonised, is itself or itself plus 2^64 - 2^32 *)
Lemma pwr_swrap32_m64 : forall t, 0 <= t < 2 ^ 32 ->
bv_swrap 32 t mod 2 ^ 64 = t \/ bv_swrap 32 t mod 2 ^ 64 = t + (2 ^ 64 - 2 ^ 32).
Proof.
intros t Ht.
assert (H32 : 2 ^ 32 = 4294967296) by reflexivity.
assert (H64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
assert (Hm : bv_modulus 32 = 4294967296) by reflexivity.
assert (Hh : bv_half_modulus 32 = 2147483648) by reflexivity.
unfold bv_swrap, bv_wrap. rewrite Hm, Hh, H64, H32.
destruct (Z_lt_le_dec t 2147483648) as [Hl | Hl].
- left. rewrite (Z.mod_small (t + 2147483648) 4294967296) by lia.
  replace (t + 2147483648 - 2147483648) with t by lia.
  apply Z.mod_small. lia.
- right.
  assert (Hq : (t + 2147483648) mod 4294967296 = t + 2147483648 + -1 * 4294967296).
  { rewrite <- (Z_mod_plus_full (t + 2147483648) (-1) 4294967296).
    apply Z.mod_small. lia. }
  rewrite Hq.
  replace (t + 2147483648 + -1 * 4294967296 - 2147483648) with (t - 4294967296) by lia.
  rewrite <- (Z_mod_plus_full (t - 4294967296) 1 18446744073709551616).
  rewrite (Z.mod_small (t - 4294967296 + 1 * 18446744073709551616) 18446744073709551616) by lia.
  lia.
Qed.

(* byte 0 of the type word: the `lw` sign-extends, which the low byte does not see *)
Lemma pwr_type_byte0 : forall E a t, U E a = t -> 0 <= t < 2 ^ 32 ->
U E (SExt true 32 a) mod 256 = t mod 256.
Proof.
intros E a t Ha Ht.
rewrite pwr_u_sext32, Ha, (Z.mod_small t (2 ^ 32)) by lia.
change 256 with (2 ^ 8).
assert (Hd : 2 ^ 64 - 2 ^ 32 = (2 ^ 56 - 2 ^ 24) * 2 ^ 8) by (vm_compute; reflexivity).
destruct (pwr_swrap32_m64 t Ht) as [HX | HX]; rewrite HX; [reflexivity|].
rewrite Hd, Z_mod_plus_full. reflexivity.
Qed.

(* bytes 1 .. 3 of the type word *)
Lemma pwr_type_byte : forall E a t s, U E a = t -> 0 <= t < 2 ^ 32 -> 0 <= s -> s + 8 <= 32 ->
Z.land s 63 = s ->
U E (SAlu ALU_SRL (SExt true 32 a) (SLit s)) mod 256 = (t / 2 ^ s) mod 256.
Proof.
intros E a t s Ha Ht Hs Hs32 Hl.
rewrite (pwr_u_srl E (SExt true 32 a) s ltac:(cbv beta; lia) Hl).
rewrite pwr_u_sext32, Ha, (Z.mod_small t (2 ^ 32)) by lia.
change 256 with (2 ^ 8).
rewrite (pwr_mod_pow _ 64 8) by lia.
rewrite Z.shiftr_div_pow2 by lia.
assert (Hps : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
destruct (pwr_swrap32_m64 t Ht) as [HX | HX]; rewrite HX; [reflexivity|].
assert (Hm : 2 ^ 64 - 2 ^ 32 = (2 ^ (24 - s) * (2 ^ 32 - 1) * 2 ^ 8) * 2 ^ s).
{ replace (2 ^ (24 - s) * (2 ^ 32 - 1) * 2 ^ 8 * 2 ^ s)
    with ((2 ^ (24 - s) * 2 ^ 8 * 2 ^ s) * (2 ^ 32 - 1)) by ring.
  rewrite <- !Z.pow_add_r by lia.
  replace (24 - s + 8 + s) with 32 by lia.
  vm_compute. reflexivity. }
rewrite Hm. rewrite Z.div_add by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

(* bytes 1 .. 3 of the size word: no sign extension, the value is already 32-bit *)
Lemma pwr_plain_byte : forall E a t s, U E a = t -> 0 <= t -> 0 <= s < 64 -> Z.land s 63 = s ->
U E (SAlu ALU_SRL a (SLit s)) mod 256 = (t / 2 ^ s) mod 256.
Proof.
intros E a t s Ha Ht Hs Hl.
rewrite (pwr_u_srl E a s Hs Hl), Ha, Z.shiftr_div_pow2 by lia.
change 256 with (2 ^ 8). apply pwr_mod_pow. lia.
Qed.

(* the four bytes of a 32-bit little-endian word *)
Lemma pwr_le4 : forall v, 0 <= v < 2 ^ 32 ->
YO0f.le_byte v 4 0 = v mod 256 /\ YO0f.le_byte v 4 1 = (v / 2 ^ 8) mod 256 /\
YO0f.le_byte v 4 2 = (v / 2 ^ 16) mod 256 /\ YO0f.le_byte v 4 3 = (v / 2 ^ 24) mod 256.
Proof.
intros v Hv. unfold YO0f.le_byte.
change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 0) with 1. rewrite Z.div_1_r.
repeat split.
Qed.

Section s.
Variable segs : list Segment.

(* one byte of a one-byte chunk of a region *)
Lemma pwr_chunk_byte : forall E m n b cs lo hi wlo whi od e,
region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs ->
mbyte segs m (b + od) = Some (Z_to_bv 8 (U E e)).
Proof.
intros E m n b cs lo hi wlo whi od e (_ & _ & _ & Hcs) Hn Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck.
cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. rewrite Z.add_0_r in Hb2.
rewrite Hb2. f_equal. injection Hb1 as Hb1. rewrite <- Hb1.
unfold byte_of_word, U. reflexivity.
Qed.

(* four one-byte chunks are a 32-bit little-endian value *)
Lemma pwr_val4 : forall m a v (b0 b1 b2 b3 : Z),
0 <= v < 2 ^ 32 ->
b0 mod 256 = v mod 256 -> b1 mod 256 = (v / 2 ^ 8) mod 256 ->
b2 mod 256 = (v / 2 ^ 16) mod 256 -> b3 mod 256 = (v / 2 ^ 24) mod 256 ->
mbyte segs m a = Some (Z_to_bv 8 b0) ->
mbyte segs m (a + 1) = Some (Z_to_bv 8 b1) ->
mbyte segs m (a + 2) = Some (Z_to_bv 8 b2) ->
mbyte segs m (a + 3) = Some (Z_to_bv 8 b3) ->
val_mem segs m a 4 v.
Proof.
intros m a v b0 b1 b2 b3 Hv H0 H1 H2 H3 M0 M1 M2 M3.
destruct (pwr_le4 v Hv) as (L0 & L1 & L2 & L3).
intros kk Hk.
assert (Hc : (kk = 0 \/ kk = 1 \/ kk = 2 \/ kk = 3)%nat) by lia.
destruct Hc as [-> | [-> | [-> | ->]]].
- change (Z.of_nat 0) with 0. rewrite Z.add_0_r, M0, L0. f_equal.
  apply pwr_bv8_mod. rewrite H0, Z.mod_mod by lia. reflexivity.
- change (Z.of_nat 1) with 1. rewrite M1, L1. f_equal.
  apply pwr_bv8_mod. rewrite H1, Z.mod_mod by lia. reflexivity.
- change (Z.of_nat 2) with 2. rewrite M2, L2. f_equal.
  apply pwr_bv8_mod. rewrite H2, Z.mod_mod by lia. reflexivity.
- change (Z.of_nat 3) with 3. rewrite M3, L3. f_equal.
  apply pwr_bv8_mod. rewrite H3, Z.mod_mod by lia. reflexivity.
Qed.
End s.

(* ======================= memory that only grows ======================= *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a byte that could be read before a write can be read after it *)
Lemma pwr_aview_grows : forall segs (H : word -> bool) m m' a,
mem_grows (mrestrict H m) (mrestrict H m') ->
aview segs H m a <> None -> aview segs H m' a <> None.
Proof.
intros segs H m m' a Hg Ha. unfold aview, mbyte in *.
destruct (mrestrict H m' (Z_to_bv 64 a)) as [b|] eqn:E'; [cbn [option_map]; discriminate|].
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E.
- exfalso. apply (Hg (Z_to_bv 64 a)); [rewrite E; discriminate | rewrite E'; reflexivity].
- exact Ha.
Qed.
(* the intrinsic's "every byte present stays present" is mem_grows *)
Lemma pwr_grows_of_apres : forall (H : word -> bool) m m',
(forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *.
destruct (H x) eqn:EH; [exfalso; exact (Hx eq_refl)|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
destruct (Hp (bv_unsigned x)) as [_ [b' Hb']].
- split; [rewrite Z_to_bv_bv_unsigned; exact EH | exists b; rewrite Z_to_bv_bv_unsigned; exact Em].
- rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.
(* a shadow hull is readable after a write that only adds bytes *)
Lemma pwr_hull_grows : forall segs (H : word -> bool) m m' x n,
mem_grows (mrestrict H m) (mrestrict H m') ->
shadow_hull_vis (aview segs H m) x n -> shadow_hull_vis (aview segs H m') x n.
Proof.
intros segs H m m' x n Hg Hh s Hs. apply (pwr_aview_grows segs H m m' s Hg). exact (Hh s Hs).
Qed.
(* an atom's own value *)
Lemma pwr_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq.
change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)).
rewrite U_SOff, Z.add_0_r. apply zcanon_id.
pose proof (u64_range (ew E n)) as H. unfold M64. lia.
Qed.
(* the hull of a sub-range is inside the hull of the range *)
Lemma pwr_hull_sub : forall (rd : reader) a n a' n',
shadow_hull_vis rd a n -> 0 <= a -> a <= a' -> 0 < n' -> a' + n' <= a + n ->
shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' Hh Ha0 H1 H2 H3 s Hs. apply Hh.
unfold shadow_addr in *.
assert (Hi1 : a / 8 <= a' / 8) by (apply Z.div_le_mono; lia).
assert (Hi2 : (a' + n' - 1) / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (D1 : (SHADOW_OFF + a / 8) / 8 <= (SHADOW_OFF + a' / 8) / 8) by (apply Z.div_le_mono; lia).
assert (D2 : (SHADOW_OFF + (a' + n' - 1) / 8) / 8 <= (SHADOW_OFF + (a + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; lia).
lia.
Qed.
End g.

(* a difference of two 16-aligned addresses is 16-aligned *)
Lemma pwr_mod16_sub : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. rewrite (Z.div_mod a 16) by lia. rewrite (Z.div_mod b 16) by lia.
rewrite Ha, Hb, !Z.add_0_r.
replace (16 * (a / 16) - 16 * (b / 16)) with ((a / 16 - b / 16) * 16) by ring.
apply Z.mod_mul. lia.
Qed.

(* The registers the walk does not claim: the two calls' caller-saved set, and the five the prologue saves and the
   epilogue restores (sp, s0, s1, s2, s3), whose kept values the leaf reads out of the save slot instead. *)
Definition pwr_clobA : list (bv 5) :=
[1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 28; 29; 30; 31]%bv.
Lemma pwr_notinA : forall r : bv 5, existsb (fun c => bv_eqb c r) pwr_clobA = false -> ~ In r pwr_clobA.
Proof.
intros r H Hin. assert (Ht : existsb (fun c => bv_eqb c r) pwr_clobA = true).
{ apply existsb_exists. exists r. split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]. }
rewrite H in Ht. discriminate Ht.
Qed.
Lemma pwr_clob_sub : forall r : bv 5, ~ In r pwr_clobA -> ~ In r pwe_clob.
Proof. intros r H Hin. apply H. cbv [pwr_clobA pwe_clob In] in *. tauto. Qed.
Ltac pwr_keep_reg KR :=
apply KR; [let Hz := fresh "Hz" in intro Hz; vm_compute in Hz; discriminate Hz
          | apply pwr_notinA; vm_compute; reflexivity].
(* a callee-saved register that a runtime call keeps *)
Ltac pwr_call_keep HP :=
apply (pwe_pres _ _ _ HP);
[ let Hz := fresh "Hz" in intro Hz; vm_compute in Hz; discriminate Hz
| apply pwe_notin; vm_compute; reflexivity ].
(* the machine state at the end of a run, written with the pc the next entry state names *)
Ltac pwr_shape pc :=
idtac; lazymatch goal with
| HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) |- _ =>
  let H := fresh "Hshape" in
  assert (H : ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom rsegs));
  [ rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl) at 1;
    repeat f_equal; vm_compute; reflexivity
  | rewrite H at 1; clear H ]
end.
(* carry an "every byte outside the zone is as it was" fact across the run that has just finished *)
Ltac pwr_upd K name :=
idtac; match goal with
| HFr : frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
  pose proof (pwe_kept_run _ E rs H _ m1 m2 K HFr ltac:(pwe_kwr)) as name
end.
(* the same fact, started at the run's own entry memory *)
Ltac pwr_new Zn name :=
idtac; match goal with
| HFr : frame_of ?E ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
  pose proof (pwe_kept_run Zn E rs H m1 m1 m2 ltac:(intros; reflexivity) HFr ltac:(pwe_kwr)) as name
end.
(* extend the running mem_grows by the run that has just finished *)
Ltac pwr_grow :=
idtac; match goal with
| MG : mem_grows ?A ?Bm |- _ =>
  match goal with
  | HG : mem_grows ?Bm ?C |- _ =>
    let X := fresh "MGn" in pose proof (mem_grows_trans _ _ _ MG HG) as X; clear MG; rename X into MG
  end
end.

(* ======================= the walk ======================= *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HBgot : as_got_shadow B = PWE_GOT.
Hypothesis HBcell : as_shadow_cell B = PWE_CELL.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy PWE_MEMCPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet PWE_MEMSET.

Theorem pwe_B_walk : pod_write_ent_specX rsegs B MT PWE_A.
Proof using MTL LAWS HBgot HBcell AMEMCPY AMEMSET.
unfold pod_write_ent_specX, pw_pre.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pp q len e
(HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev)
H10 H11 Hpp0 Hpp8 Hpp63 Hppam Hppra Hpphull Hawr Hppsp Vlen Hlen0 Hlen8 Hcap
Hq0 Hq8 Hqam Hblen Hszle Htyr Hent Hqra Hqhull Hsep Hqsp.
(* ---- the numbers the walk needs, from the contract's premises and the journal ---- *)
pose proof pwe_wx as Hwx. pose proof pwe_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (P32 : 2 ^ 32 = 4294967296) by reflexivity.
assert (P46 : 2 ^ 46 = 70368744177664) by reflexivity.
assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
assert (P63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HOL : Layout.OFF_LEN = 16384) by reflexivity.
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
assert (HEN : Layout.ENT_SIZE = 104) by reflexivity.
assert (HBM : Layout.POD_BUF_MAX = 16384) by reflexivity.
unfold T_pwe_STK in *.
assert (Hsz : 0 <= Model.e_size e <= 96) by lia.
pose proof (pwm_pad8_range (Model.e_size e)) as Hpad.
assert (Hn8 : pwe_len e = 8 + Model.e_size e + Model.pad8 (Model.e_size e))
  by (unfold pwe_len; apply pwm_enc_len; [exact Hblen | lia]).
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hceilsp : alloc_ceiling <= spZ regs - (48 + ESTACK)) by lia.
assert (Hppam' := Hppam). assert (Hqam' := Hqam).
cbv [amem_range kLowMemEnd kHighMemBeg kHighMemEnd] in Hppam', Hqam'.
assert (Hpp47 : pp + 19744 <= 2 ^ 47) by lia.
assert (Hq47 : q + 104 <= 2 ^ 47) by lia.
(* the image's GOT cell and the runtime's shadow-offset cell *)
destruct ((al_const _ _ LAWS) lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBcell in Kcell. rewrite HBgot, HBcell in Kgot.
(* ---- R0's entry state ---- *)
set (E0 := Ereg regs (pwe_extra [])).
assert (B2 : bv_unsigned (ew E0 2) = spZ regs)
  by (subst E0; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (HR0 : regs_ok E0 sr_atoms regs) by (subst E0; apply regs_ok_Ereg).
assert (E10 : ew E0 10 = Z_to_bv 64 pp)
  by (subst E0; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E0 11 = Z_to_bv 64 q)
  by (subst E0; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF) by (subst E0; reflexivity).
assert (E2 : ew E0 2 = Z_to_bv 64 (spZ regs))
  by (subst E0; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); unfold spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (E1' : ew E0 1 = Z_to_bv 64 (bv_unsigned (getr regs 1)))
  by (subst E0; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity).
assert (E8' : ew E0 8 = Z_to_bv 64 (bv_unsigned (getr regs 8)))
  by (subst E0; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity).
assert (E9' : ew E0 9 = Z_to_bv 64 (bv_unsigned (getr regs 9)))
  by (subst E0; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity).
assert (E18' : ew E0 18 = Z_to_bv 64 (bv_unsigned (getr regs 18)))
  by (subst E0; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity).
assert (E19' : ew E0 19 = Z_to_bv 64 (bv_unsigned (getr regs 19)))
  by (subst E0; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), Z_to_bv_bv_unsigned; reflexivity).
assert (HS : st_ok rsegs E0 ss_p0 (restrict (w_H W) (mkst regs (Z_to_bv 64 PWE_A) memc (seg_rom rsegs)))).
{ subst E0. apply (pwe_entry0 W regs memc q H11 Hq0 ltac:(cbv beta; lia) Hq8 Hsp46 Hal16
    ltac:(intros a Ha; apply Hpres; lia) Kgot Kcell). }
assert (SHOK : sh_ok rsegs PWE_Bx [] E0 (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((spZ regs - (48 + ESTACK) <= a < spZ regs) \/
     (pp + len <= a < pp + len + pwe_len e \/ pp + Layout.OFF_LEN <= a < pp + Layout.OFF_LEN + 8)) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
assert (MG : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
clearbody E0.
unfold cfg_at. change (w64 PWE_A) with (Z_to_bv 64 PWE_A).
(* ---- R0: 0x83cc4 -> 0x83cf4 ---- *)
pwe_run PWE_P1.
pwr_upd KE KEn. clear KE. rename KEn into KE.
pwr_new (fun a => spZ regs - 48 <= a < spZ regs) KN.
pwr_grow.
pwe_reg HS (2%bv : bv 5) RA2. pwe_reg HS (9%bv : bv 5) RA9.
pwe_reg HS (11%bv : bv 5) RA11. pwe_reg HS (15%bv : bv 5) RA15.
assert (KR0 : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pwr_clobA -> getr (ms_regs ms) r = getr regs r)
  by exact (pwe_regs_kept E0 _ ms regs sr_atoms (w_H W) pwr_clobA HS HR0 ltac:(vm_compute; reflexivity)).
assert (SP1 : spZ (ms_regs ms) = spZ regs - 48).
{ unfold spZ at 1. rewrite RA2, (pwe_soff E0 2 (spZ regs) (-48) E2), unsigned_lit_small by lia. lia. }
(* the five values the prologue stored into the save slot *)
pwe_regn HS 0%nat RgS.
pose proof (pwe_field E0 _ 2 (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) RgS B2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite (pwe_soff E0 1 _ 0 E1'), Z.add_0_r; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range) ltac:(cbn; lia)) as Vra1.
pose proof (pwe_field E0 _ 2 (spZ regs) _ _ _ _ _ (-16) 8 (SOff 8 0) (bv_unsigned (getr regs 8)) RgS B2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite (pwe_soff E0 8 _ 0 E8'), Z.add_0_r; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range) ltac:(cbn; lia)) as Vs01.
pose proof (pwe_field E0 _ 2 (spZ regs) _ _ _ _ _ (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) RgS B2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite (pwe_soff E0 9 _ 0 E9'), Z.add_0_r; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range) ltac:(cbn; lia)) as Vs11.
pose proof (pwe_field E0 _ 2 (spZ regs) _ _ _ _ _ (-32) 8 (SOff 18 0) (bv_unsigned (getr regs 18)) RgS B2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite (pwe_soff E0 18 _ 0 E18'), Z.add_0_r; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range) ltac:(cbn; lia)) as Vs21.
pose proof (pwe_field E0 _ 2 (spZ regs) _ _ _ _ _ (-40) 8 (SOff 19 0) (bv_unsigned (getr regs 19)) RgS B2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite (pwe_soff E0 19 _ 0 E19'), Z.add_0_r; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply u64_range) ltac:(cbn; lia)) as Vs31.
change (N.to_nat 8) with 8%nat in Vra1, Vs01, Vs11, Vs21, Vs31.
(* the shadow bytes, and so the two usable ranges, as at the call *)
assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - (48 + ESTACK) <= a < spZ regs) ->
  ~ pwe_E pp len e a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hx Hy. apply KE; [exact Ha | intros [Hc | Hc]; [exact (Hx Hc) | exact (Hy Hc)]]. }
assert (SH1 : forall x, 0 <= x < kHighMemEnd ->
  aview rsegs (w_H W) (ms_mem ms) (shadow_addr x) = aview rsegs (w_H W) memc (shadow_addr x))
  by exact (pwe_shadow_kept W W memc (ms_mem ms) (spZ regs) (48 + ESTACK) pp len e KE' Hceilsp Hlen0 Hcap Hppam Hpp0).
assert (RApp1 : range_addressable (aview rsegs (w_H W) (ms_mem ms)) SHADOW_OFF pp Layout.PP_SIZE)
  by exact (pwe_ra_kept_of_shadow W W memc (ms_mem ms) pp Layout.PP_SIZE SH1 Hppam Hpp0 ltac:(cbv beta; lia) Hppra).
assert (RAq1 : range_addressable (aview rsegs (w_H W) (ms_mem ms)) SHADOW_OFF q Layout.ENT_SIZE)
  by exact (pwe_ra_kept_of_shadow W W memc (ms_mem ms) q Layout.ENT_SIZE SH1 Hqam Hq0 ltac:(cbv beta; lia) Hqra).
(* e's bytes and the len cell at R1's entry *)
assert (Hent1 : garr8 rsegs (mrestrict (w_H W) (ms_mem ms)) q
  (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e))).
{ apply (pwm_garr8_kept rsegs (w_H W) (w_H W) memc (ms_mem ms) q _ Hent).
  intros x Hx. rewrite pwm_ent_len in Hx by lia. apply KE; lia. }
assert (Vlen1 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (pp + 16384) 8 len).
{ apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) memc (ms_mem ms) _ 8 _ Vlen).
  intros x Hx. apply KN; lia. }
assert (Vty1 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) q 4 (Model.e_type e))
  by exact (pwm_ent_type rsegs _ q e Hent1 Htyr).
assert (Vsz1 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (q + 4) 4 (Model.e_size e))
  by exact (pwm_ent_size rsegs _ q e Hent1 ltac:(cbv beta; lia)).
assert (Hpres1 : forall a, pp + len <= a < pp + len + 8 \/ pp + 16384 <= a < pp + 16392 ->
  apresent (w_H W) (ms_mem ms) a).
{ intros a Ha.
  refine (proj1 (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hawr a _))).
  cbv [pwe_E]. lia. }
(* ---- R1: 0x83cf4 -> 0x518b8, the copy's entry ---- *)
set (E1 := Ereg (ms_regs ms) (pwe_extra [len; Model.e_size e; Model.e_type e; pp + len])).
assert (F2 : bv_unsigned (ew E1 2) = spZ regs - 48)
  by (subst E1; rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); exact SP1).
assert (F9 : ew E1 9 = Z_to_bv 64 pp)
  by (subst E1; rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl), RA9,
      (pwe_soff E0 10 pp 0 E10), Z.add_0_r; reflexivity).
assert (F11 : ew E1 11 = Z_to_bv 64 q)
  by (subst E1; rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl), RA11,
      (pwe_soff E0 11 q 0 E11), Z.add_0_r; reflexivity).
assert (F15 : getr (ms_regs ms) 15 = w64 SHADOW_OFF)
  by (rewrite RA15, (pwe_soff E0 32 SHADOW_OFF 0 E32), Z.add_0_r; reflexivity).
assert (F32 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by (subst E1; reflexivity).
assert (F33 : ew E1 33 = Z_to_bv 64 len) by (subst E1; reflexivity).
assert (F34 : ew E1 34 = Z_to_bv 64 (Model.e_size e)) by (subst E1; reflexivity).
assert (F35 : ew E1 35 = Z_to_bv 64 (Model.e_type e)) by (subst E1; reflexivity).
assert (F36 : ew E1 36 = Z_to_bv 64 (pp + len)) by (subst E1; reflexivity).
assert (HR1 : regs_ok E1 p1_regs (ms_regs ms)).
{ unfold p1_regs. apply regs_ok_override; [subst E1; apply regs_ok_Ereg | |].
  - intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
  - cbn [sv_denot]. rewrite F32, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact F15. }
pwr_shape PWE_P1.
clear HS SHOK.
assert (HS : st_ok rsegs E1 ss_p1
  (restrict (w_H W) (mkst (ms_regs ms) (Z_to_bv 64 PWE_P1) (ms_mem ms) (seg_rom rsegs)))).
{ subst E1. apply (pwe_entry1 W (ms_regs ms) (ms_mem ms) pp q len (Model.e_size e) (Model.e_type e)
    ltac:(rewrite RA9, (pwe_soff E0 10 pp 0 E10), Z.add_0_r; reflexivity)
    ltac:(rewrite RA11, (pwe_soff E0 11 q 0 E11), Z.add_0_r; reflexivity)
    F15 ltac:(cbv beta; lia) ltac:(rewrite SP1; apply pwr_mod16_sub; [exact Hal16 | reflexivity])
    Hpp0 Hpp8 Hpp47 Hq0 Hq8 Hq47 Hlen0 Hlen8 ltac:(cbv beta; lia) Hsz Htyr Vlen1 Vty1 Vsz1 Hpres1 ltac:(cbv beta; lia)). }
assert (SHOK : sh_ok rsegs PWE_Bx p1_SH E1 (mrestrict (w_H W) (ms_mem ms)))
  by exact (pwe_sh1 W (ms_mem ms) E1 pp q len F32 F9 F11 F36 Hpp0 Hpp47 ltac:(rewrite <- HPP; exact Hppam)
      Hq0 Hq47 ltac:(rewrite <- HEN; exact Hqam) Hlen0 ltac:(cbv beta; lia) ltac:(rewrite <- HPP; exact RApp1)
      ltac:(rewrite <- HEN; exact RAq1)).
assert (F9u : bv_unsigned (ew E1 9) = pp) by (rewrite F9; apply unsigned_lit_small; lia).
assert (F36u : bv_unsigned (ew E1 36) = pp + len) by (rewrite F36; apply unsigned_lit_small; lia).
clearbody E1.
(* R1 writes the len cell and the eight bytes at pp + len; both are the caller's to write *)
pwe_run_awr ltac:(
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly1 ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly1 ow) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat pp);
  [ reflexivity | exact F9u
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; cbv [pwe_E]; lia | ];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 36%nat (pp + len));
  [ reflexivity | exact F36u
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; cbv [pwe_E]; lia
  | apply awr_ok_nil ]) PWE_MEMCPY.
(* ---- the state at the copy's entry ---- *)
lazymatch goal with HS : st_ok _ ?E _ _ |- _ => remember E as EC eqn:HEC end.
assert (HAG : env_agree 37 E1 EC).
{ split; [intros n Hn | ]; rewrite HEC; [repeat (rewrite ew_ewset_other by lia) | ]; reflexivity. }
assert (G32 : ew EC 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (proj1 HAG 32%nat ltac:(cbv beta; lia)); exact F32).
assert (G33 : ew EC 33 = Z_to_bv 64 len) by (rewrite (proj1 HAG 33%nat ltac:(cbv beta; lia)); exact F33).
assert (G34 : ew EC 34 = Z_to_bv 64 (Model.e_size e)) by (rewrite (proj1 HAG 34%nat ltac:(cbv beta; lia)); exact F34).
assert (G35 : ew EC 35 = Z_to_bv 64 (Model.e_type e)) by (rewrite (proj1 HAG 35%nat ltac:(cbv beta; lia)); exact F35).
assert (G36 : ew EC 36 = Z_to_bv 64 (pp + len)) by (rewrite (proj1 HAG 36%nat ltac:(cbv beta; lia)); exact F36).
assert (G9 : ew EC 9 = Z_to_bv 64 pp) by (rewrite (proj1 HAG 9%nat ltac:(cbv beta; lia)); exact F9).
assert (G11 : ew EC 11 = Z_to_bv 64 q) by (rewrite (proj1 HAG 11%nat ltac:(cbv beta; lia)); exact F11).
assert (G2 : bv_unsigned (ew EC 2) = spZ regs - 48) by (rewrite (proj1 HAG 2%nat ltac:(cbv beta; lia)); exact F2).
assert (G36u : bv_unsigned (ew EC 36) = pp + len) by (rewrite G36; apply unsigned_lit_small; lia).
assert (G9u : bv_unsigned (ew EC 9) = pp) by (rewrite G9; apply unsigned_lit_small; lia).
pwr_upd KE KEn. clear KE. rename KEn into KE.
pwr_new (fun a => (pp + 16384 <= a < pp + 16392) \/ (pp + len <= a < pp + len + 8)) S1.
pwr_grow.
assert (HR1' : regs_ok EC p1_regs (ms_regs ms))
  by exact (regs_ok_agree 37 E1 EC p1_regs (ms_regs ms) HAG ltac:(vm_compute; reflexivity) HR1).
pose proof (pwe_regs_kept EC _ _ (ms_regs ms) p1_regs (w_H W) pwr_clobA HS HR1'
  ltac:(vm_compute; reflexivity)) as KR1.
pwe_reg HS (1%bv : bv 5) RB1. pwe_reg HS (2%bv : bv 5) RB2.
pwe_reg HS (10%bv : bv 5) RB10. pwe_reg HS (11%bv : bv 5) RB11. pwe_reg HS (12%bv : bv 5) RB12.
pwe_reg HS (8%bv : bv 5) RB8. pwe_reg HS (9%bv : bv 5) RB9.
pwe_reg HS (18%bv : bv 5) RB18. pwe_reg HS (19%bv : bv 5) RB19.
(* the len cell after the two put32s *)
pwe_regn HS 0%nat RgL1.
pose proof (pwe_field EC _ 9 pp _ _ _ _ _ 16384 8 (SOff 33 8) (len + 8) RgL1 G9u
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite (pwe_soff EC 33 len 8 G33); reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as VL1.
change (N.to_nat 8) with 8%nat in VL1.
(* the two words the put32s wrote, read out of the run's own region at pp + len *)
pwe_regn HS 2%nat RgB.
assert (Vsz2 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms0)) (pp + len) 4 (Model.e_size e)).
{ apply (pwr_val4 rsegs _ (pp + len) (Model.e_size e) (U EC (SOff 34 0)) (U EC (SAlu ALU_SRL (SOff 34 0) (SLit 8)))
    (U EC (SAlu ALU_SRL (SOff 34 0) (SLit 16))) (U EC (SAlu ALU_SRL (SOff 34 0) (SLit 24)))
    ltac:(cbv beta; lia)
    ltac:(rewrite (U_atom EC 34 (Model.e_size e) G34) by lia; reflexivity)
    ltac:(apply (pwr_plain_byte EC _ (Model.e_size e) 8);
          [apply (U_atom EC 34 (Model.e_size e) G34); lia | lia | lia | reflexivity])
    ltac:(apply (pwr_plain_byte EC _ (Model.e_size e) 16);
          [apply (U_atom EC 34 (Model.e_size e) G34); lia | lia | lia | reflexivity])
    ltac:(apply (pwr_plain_byte EC _ (Model.e_size e) 24);
          [apply (U_atom EC 34 (Model.e_size e) G34); lia | lia | lia | reflexivity])).
  - replace (pp + len) with (pp + len + 0) by lia.
    exact (pwr_chunk_byte rsegs EC _ 36 (pp + len) _ _ _ _ _ 0 _ RgB G36u
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
  - exact (pwr_chunk_byte rsegs EC _ 36 (pp + len) _ _ _ _ _ 1 _ RgB G36u
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
  - exact (pwr_chunk_byte rsegs EC _ 36 (pp + len) _ _ _ _ _ 2 _ RgB G36u
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
  - exact (pwr_chunk_byte rsegs EC _ 36 (pp + len) _ _ _ _ _ 3 _ RgB G36u
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
assert (Vty2 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms0)) (pp + len + 4) 4 (Model.e_type e)).
{ apply (pwr_val4 rsegs _ (pp + len + 4) (Model.e_type e) (U EC (SExt true 32 (SOff 35 0)))
    (U EC (SAlu ALU_SRL (SExt true 32 (SOff 35 0)) (SLit 8)))
    (U EC (SAlu ALU_SRL (SExt true 32 (SOff 35 0)) (SLit 16)))
    (U EC (SAlu ALU_SRL (SExt true 32 (SOff 35 0)) (SLit 24)))
    Htyr
    ltac:(apply (pwr_type_byte0 EC _ (Model.e_type e));
          [apply (U_atom EC 35 (Model.e_type e) G35); lia | exact Htyr])
    ltac:(apply (pwr_type_byte EC _ (Model.e_type e) 8);
          [apply (U_atom EC 35 (Model.e_type e) G35); lia | exact Htyr | lia | lia | reflexivity])
    ltac:(apply (pwr_type_byte EC _ (Model.e_type e) 16);
          [apply (U_atom EC 35 (Model.e_type e) G35); lia | exact Htyr | lia | lia | reflexivity])
    ltac:(apply (pwr_type_byte EC _ (Model.e_type e) 24);
          [apply (U_atom EC 35 (Model.e_type e) G35); lia | exact Htyr | lia | lia | reflexivity])).
  - exact (pwr_chunk_byte rsegs EC _ 36 (pp + len) _ _ _ _ _ 4 _ RgB G36u
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
  - replace (pp + len + 4 + 1) with (pp + len + 5) by lia.
    exact (pwr_chunk_byte rsegs EC _ 36 (pp + len) _ _ _ _ _ 5 _ RgB G36u
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
  - replace (pp + len + 4 + 2) with (pp + len + 6) by lia.
    exact (pwr_chunk_byte rsegs EC _ 36 (pp + len) _ _ _ _ _ 6 _ RgB G36u
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))).
  - replace (pp + len + 4 + 3) with (pp + len + 7) by lia.
    exact (pwr_chunk_byte rsegs EC _ 36 (pp + len) _ _ _ _ _ 7 _ RgB G36u
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). }
(* ---- the copy: __asan_memcpy(pp + len + 8, e + 8, size) ---- *)
assert (SP2 : spZ (ms_regs ms0) = spZ regs - 48)
  by (unfold spZ at 1; rewrite RB2, pwr_soff0; exact G2).
assert (K3a : getr (ms_regs ms) 3 = getr regs 3) by pwr_keep_reg KR0.
assert (K4a : getr (ms_regs ms) 4 = getr regs 4) by pwr_keep_reg KR0.
assert (K3b : getr (ms_regs ms0) 3 = getr (ms_regs ms) 3) by pwr_keep_reg KR1.
assert (K4b : getr (ms_regs ms0) 4 = getr (ms_regs ms) 4) by pwr_keep_reg KR1.
assert (KE2' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - (48 + ESTACK) <= a < spZ regs) ->
  ~ pwe_E pp len e a -> aview rsegs (w_H W) (ms_mem ms0) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hx Hy. apply KE; [exact Ha | intros [Hc | Hc]; [exact (Hx Hc) | exact (Hy Hc)]]. }
assert (SH2 : forall x, 0 <= x < kHighMemEnd ->
  aview rsegs (w_H W) (ms_mem ms0) (shadow_addr x) = aview rsegs (w_H W) memc (shadow_addr x))
  by exact (pwe_shadow_kept W W memc (ms_mem ms0) (spZ regs) (48 + ESTACK) pp len e KE2'
      Hceilsp Hlen0 Hcap Hppam Hpp0).
assert (RApp2 : range_addressable (aview rsegs (w_H W) (ms_mem ms0)) SHADOW_OFF pp Layout.PP_SIZE)
  by exact (pwe_ra_kept_of_shadow W W memc (ms_mem ms0) pp Layout.PP_SIZE SH2 Hppam Hpp0 ltac:(cbv beta; lia) Hppra).
assert (RAq2 : range_addressable (aview rsegs (w_H W) (ms_mem ms0)) SHADOW_OFF q Layout.ENT_SIZE)
  by exact (pwe_ra_kept_of_shadow W W memc (ms_mem ms0) q Layout.ENT_SIZE SH2 Hqam Hq0 ltac:(cbv beta; lia) Hqra).
assert (Hent2 : garr8 rsegs (mrestrict (w_H W) (ms_mem ms0)) q
  (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e))).
{ apply (pwm_garr8_kept rsegs (w_H W) (w_H W) memc (ms_mem ms0) q _ Hent).
  intros x Hx. rewrite pwm_ent_len in Hx by lia. apply KE; lia. }
pwr_shape PWE_MEMCPY.
eapply SRr_bind.
{ eapply (pwe_intrin_at B LAWS OCpy PWE_MEMCPY AMEMCPY) with (d := pp + len + 8) (x := q + 8)
    (n := Model.e_size e) (o := spZ regs - 48 - sp0) (raw := Z_to_bv 64 PWE_RA1).
  - exact HJ.
  - rewrite RB10, (pwe_soff EC 36 (pp + len) 8 G36). reflexivity.
  - rewrite RB11, (pwe_soff EC 11 q 8 G11). reflexivity.
  - rewrite RB12, (pwe_soff EC 34 (Model.e_size e) 0 G34), Z.add_0_r. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite SP2. lia.
  - apply pwr_mod16_sub; [apply pwr_mod16_sub; [exact Hal16 | reflexivity] | exact Hsp0al].
  - lia.
  - lia.
  - rewrite K3b, K3a. exact Hgp.
  - rewrite K4b, K4a. exact Htp.
  - rewrite RB1. reflexivity.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split; [apply Hawr; cbv [pwe_E]; lia | lia].
  - apply (pwe_amem_sub pp Layout.PP_SIZE); [exact Hppam | lia | lia | lia].
  - eapply range_addressable_sub; [exact RApp2 | lia | lia].
  - intros Hn0. apply (pwr_hull_grows rsegs (w_H W) memc (ms_mem ms0) _ _ MG).
    apply (pwr_hull_sub (aview rsegs (w_H W) memc) pp Layout.PP_SIZE); [exact Hpphull | lia | lia | lia | lia].
  - split; [lia|]. split; [lia|].
    split; [apply (pwe_src_ok W (ms_regs ms0) (ms_mem ms0) (q + 8) (Model.e_size e)
        (map (fun x : byte => bv_unsigned x) (Model.e_body e))
        (pwm_ent_body rsegs _ q e Hent2 Hblen ltac:(cbv beta; lia)) ltac:(rewrite length_map; exact Hblen)
        ltac:(intros aa Haa; rewrite SP2; lia))|].
    split; [lia|].
    split; [apply (pwe_amem_sub q Layout.ENT_SIZE); [exact Hqam | lia | lia | lia]|].
    split; [eapply range_addressable_sub; [exact RAq2 | lia | lia]|].
    intros Hn0. apply (pwr_hull_grows rsegs (w_H W) memc (ms_mem ms0) _ _ MG).
    apply (pwr_hull_sub (aview rsegs (w_H W) memc) q Layout.ENT_SIZE);
    [exact Hqhull | lia | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & HP2 & H10b & Heff & Hfr2 & Hpres2).
clear HJ. rename HJ2 into HJ.
(* ---- R2: 0x83e94 -> 0x51d54, the fill's entry ---- *)
assert (D2 : getr regs2 2 = getr (ms_regs ms0) 2) by pwr_call_keep HP2.
assert (D3 : getr regs2 3 = getr (ms_regs ms0) 3) by pwr_call_keep HP2.
assert (D4 : getr regs2 4 = getr (ms_regs ms0) 4) by pwr_call_keep HP2.
assert (D8 : getr regs2 8 = getr (ms_regs ms0) 8) by pwr_call_keep HP2.
assert (D9 : getr regs2 9 = getr (ms_regs ms0) 9) by pwr_call_keep HP2.
assert (D18 : getr regs2 18 = getr (ms_regs ms0) 18) by pwr_call_keep HP2.
assert (D19 : getr regs2 19 = getr (ms_regs ms0) 19) by pwr_call_keep HP2.
assert (SP3 : spZ regs2 = spZ regs - 48) by (unfold spZ at 1; rewrite D2; exact SP2).
assert (R2_9 : getr regs2 9 = w64 pp) by (rewrite D9, RB9, pwr_soff0; exact G9).
assert (R2_8 : getr regs2 8 = w64 (pp + 16384))
  by (rewrite D8, RB8, (pwe_soff EC 9 pp 16384 G9); reflexivity).
assert (R2_18 : getr regs2 18 = w64 (Model.e_size e))
  by (rewrite D18, RB18, (pwe_soff EC 34 (Model.e_size e) 0 G34), Z.add_0_r; reflexivity).
assert (Xsh3 := pwe_sh3_denot EC pp G9 G32 ltac:(cbv beta; lia) ltac:(cbv beta; lia)). cbv [pwe_sh3] in Xsh3.
assert (R2_19 : getr regs2 19 = w64 (shadow_addr (pp + 16384)))
  by (rewrite D19, RB19, Xsh3; reflexivity).
assert (KEc : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((spZ regs - (48 + ESTACK) <= a < spZ regs) \/
     (pp + len <= a < pp + len + pwe_len e \/ pp + Layout.OFF_LEN <= a < pp + Layout.OFF_LEN + 8)) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hz. rewrite (Hfr2 a Ha ltac:(cbv beta; lia) ltac:(cbv beta; lia)). apply KE; [exact Ha | exact Hz]. }
assert (KEq : forall i, 0 <= i < Model.e_size e ->
  aview rsegs (w_H W) (ms_mem ms0) (q + 8 + i) = aview rsegs (w_H W) memc (q + 8 + i))
  by (intros i Hi; apply KE; lia).
clear KE. rename KEc into KE.
assert (MGc := mem_grows_trans _ _ _ MG (pwr_grows_of_apres (w_H W) (ms_mem ms0) mem2 Hpres2)).
clear MG. rename MGc into MG.
assert (SH3 : forall x, 0 <= x < kHighMemEnd ->
  aview rsegs (w_H W) mem2 (shadow_addr x) = aview rsegs (w_H W) memc (shadow_addr x))
  by exact (pwe_shadow_kept W W memc mem2 (spZ regs) (48 + ESTACK) pp len e
      ltac:(intros a Ha Hx Hy; apply KE;
            [exact Ha | intros [Hc | Hc]; [exact (Hx Hc) | exact (Hy Hc)]])
      Hceilsp Hlen0 Hcap Hppam Hpp0).
assert (RApp3 : range_addressable (aview rsegs (w_H W) mem2) SHADOW_OFF pp Layout.PP_SIZE)
  by exact (pwe_ra_kept_of_shadow W W memc mem2 pp Layout.PP_SIZE SH3 Hppam Hpp0 ltac:(cbv beta; lia) Hppra).
assert (VL2 : val_mem rsegs (mrestrict (w_H W) mem2) (pp + 16384) 8 (len + 8)).
{ apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms0) mem2 _ 8 _ VL1).
  intros xx Hxx. apply Hfr2; lia. }
assert (HprL2 : forall a, pp + 16384 <= a < pp + 16392 -> apresent (w_H W) mem2 a).
{ intros a Ha.
  refine (proj1 (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hawr a _))).
  cbv [pwe_E]. lia. }
set (EB := Ereg regs2 (pwe_extra [len; Model.e_size e])).
assert (H9' : ew EB 9 = Z_to_bv 64 pp)
  by (subst EB; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R2_9).
assert (H32' : ew EB 32 = Z_to_bv 64 SHADOW_OFF) by (subst EB; reflexivity).
assert (H33' : ew EB 33 = Z_to_bv 64 len) by (subst EB; reflexivity).
assert (H34' : ew EB 34 = Z_to_bv 64 (Model.e_size e)) by (subst EB; reflexivity).
assert (H2' : bv_unsigned (ew EB 2) = spZ regs - 48)
  by (subst EB; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact SP3).
assert (H9u : bv_unsigned (ew EB 9) = pp) by (rewrite H9'; apply unsigned_lit_small; lia).
assert (HR2 : regs_ok EB p2_regs regs2).
{ unfold p2_regs. apply regs_ok_override; [apply regs_ok_override; [apply regs_ok_override;
    [subst EB; apply regs_ok_Ereg | | ] | | ] | | ];
  try (intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  - rewrite (pwe_soff EB 9 pp 16384 H9'). symmetry. exact R2_8.
  - rewrite (pwe_sh3_denot EB pp H9' H32') by lia. symmetry. exact R2_19.
  - rewrite (pwe_soff EB 34 (Model.e_size e) 0 H34'), Z.add_0_r. symmetry. exact R2_18. }
clear HS SHOK.
assert (HS : st_ok rsegs EB ss_p2 (restrict (w_H W) (mkst regs2 (Z_to_bv 64 PWE_P2) mem2 (seg_rom rsegs)))).
{ subst EB. apply (pwe_entry2 W regs2 mem2 pp len (Model.e_size e) R2_9 R2_8 R2_18 R2_19
    ltac:(cbv beta; lia) ltac:(rewrite SP3; apply pwr_mod16_sub; [exact Hal16 | reflexivity])
    Hpp0 Hpp8 Hpp47 Hlen0 Hlen8 ltac:(cbv beta; lia) Hsz VL2 HprL2). }
assert (SHOK : sh_ok rsegs PWE_Bx p2_SH EB (mrestrict (w_H W) mem2))
  by exact (pwe_shblk W mem2 EB pp p2_SH eq_refl H32' H9' Hpp0 Hpp47
      ltac:(rewrite <- HPP; exact Hppam) ltac:(rewrite <- HPP; exact RApp3)).
clearbody EB.
pwe_run_awr ltac:(
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly1 ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly1 ow) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat pp);
  [ reflexivity | exact H9u
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; cbv [pwe_E]; lia
  | apply awr_ok_nil ]) PWE_MEMSET.
(* ---- the state at the fill's entry ---- *)
pwr_upd KE KEn. clear KE. rename KEn into KE.
pwr_new (fun a => pp + 16384 <= a < pp + 16392) S3.
pwr_grow.
pose proof (pwe_regs_kept EB _ _ regs2 p2_regs (w_H W) pwr_clobA HS HR2
  ltac:(vm_compute; reflexivity)) as KR2.
pwe_reg HS (1%bv : bv 5) RC1. pwe_reg HS (2%bv : bv 5) RC2.
pwe_reg HS (10%bv : bv 5) RC10. pwe_reg HS (11%bv : bv 5) RC11. pwe_reg HS (12%bv : bv 5) RC12.
pwe_reg HS (8%bv : bv 5) RC8. pwe_reg HS (9%bv : bv 5) RC9.
pwe_reg HS (18%bv : bv 5) RC18. pwe_reg HS (19%bv : bv 5) RC19.
pwe_regn HS 0%nat RgL2.
pose proof (pwe_field EB _ 9 pp _ _ _ _ _ 16384 8 pwe_tot (len + 8 + Model.e_size e) RgL2 H9u
  ltac:(cbv [pwe_tot]; cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite denot_lit_U; f_equal; unfold pwe_tot; rewrite U_SAlu; cbn [zalu_raw];
        rewrite (U_atom_off EB 33 len 8 H33') by lia;
        rewrite (U_atom_off EB 34 (Model.e_size e) 0 H34') by lia;
        rewrite Z.add_0_r; apply zcanon_id; unfold M64; lia)
  ltac:(cbn; lia) ltac:(cbn; lia)) as VL3.
change (N.to_nat 8) with 8%nat in VL3.
assert (SP4 : spZ (ms_regs ms1) = spZ regs - 48)
  by (unfold spZ at 1; rewrite RC2, pwr_soff0; exact H2').
assert (Xpad : U EB pwe_pad = Model.pad8 (Model.e_size e))
  by (apply (pwe_pad_val EB len (Model.e_size e) H33' H34'); lia).
assert (Xpad' := Xpad). cbv [pwe_pad] in Xpad'.
assert (U10 : U EB (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 8) (SOff 33 0)) (SOff 34 0))
  = pp + len + 8 + Model.e_size e).
{ rewrite !U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off EB 9 pp 8 H9') by lia.
  rewrite (U_atom_off EB 33 len 0 H33') by lia.
  rewrite (U_atom_off EB 34 (Model.e_size e) 0 H34') by lia.
  rewrite (zcanon_id (pp + 8 + (len + 0))) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia. }
assert (R3_10 : getr (ms_regs ms1) 10 = w64 (pp + len + 8 + Model.e_size e))
  by (rewrite RC10; unfold w64; rewrite denot_lit_U, U10; reflexivity).
assert (R3_12 : getr (ms_regs ms1) 12 = w64 (Model.pad8 (Model.e_size e))).
{ rewrite RC12. unfold w64. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_lit EB 0) by lia.
  rewrite Xpad', Z.add_0_r. apply zcanon_id. unfold M64. lia. }
assert (SH4 : forall x, 0 <= x < kHighMemEnd ->
  aview rsegs (w_H W) (ms_mem ms1) (shadow_addr x) = aview rsegs (w_H W) memc (shadow_addr x))
  by exact (pwe_shadow_kept W W memc (ms_mem ms1) (spZ regs) (48 + ESTACK) pp len e
      ltac:(intros a Ha Hx Hy; apply KE;
            [exact Ha | intros [Hc | Hc]; [exact (Hx Hc) | exact (Hy Hc)]])
      Hceilsp Hlen0 Hcap Hppam Hpp0).
assert (RApp4 : range_addressable (aview rsegs (w_H W) (ms_mem ms1)) SHADOW_OFF pp Layout.PP_SIZE)
  by exact (pwe_ra_kept_of_shadow W W memc (ms_mem ms1) pp Layout.PP_SIZE SH4 Hppam Hpp0 ltac:(cbv beta; lia) Hppra).
(* ---- the fill: __asan_memset(pp + len + 8 + size, 0, pad8 size) ---- *)
pwr_shape PWE_MEMSET.
eapply SRr_bind.
{ eapply (pwe_intrin_at B LAWS OSet PWE_MEMSET AMEMSET) with (d := pp + len + 8 + Model.e_size e)
    (x := 0) (n := Model.pad8 (Model.e_size e)) (o := spZ regs - 48 - sp0) (raw := Z_to_bv 64 PWE_RA2).
  - exact HJ.
  - exact R3_10.
  - rewrite RC11. reflexivity.
  - exact R3_12.
  - lia.
  - lia.
  - lia.
  - rewrite SP4. lia.
  - apply pwr_mod16_sub; [apply pwr_mod16_sub; [exact Hal16 | reflexivity] | exact Hsp0al].
  - lia.
  - lia.
  - rewrite (KR2 (3%bv : bv 5) ltac:(intro Hz; vm_compute in Hz; discriminate Hz)
      ltac:(apply pwr_notinA; vm_compute; reflexivity)), D3, K3b, K3a. exact Hgp.
  - rewrite (KR2 (4%bv : bv 5) ltac:(intro Hz; vm_compute in Hz; discriminate Hz)
      ltac:(apply pwr_notinA; vm_compute; reflexivity)), D4, K4b, K4a. exact Htp.
  - rewrite RC1. reflexivity.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split; [apply Hawr; cbv [pwe_E]; lia | lia].
  - apply (pwe_amem_sub pp Layout.PP_SIZE); [exact Hppam | lia | lia | lia].
  - eapply range_addressable_sub; [exact RApp4 | lia | lia].
  - intros Hn0. apply (pwr_hull_grows rsegs (w_H W) memc (ms_mem ms1) _ _ MG).
    apply (pwr_hull_sub (aview rsegs (w_H W) memc) pp Layout.PP_SIZE);
    [exact Hpphull | lia | lia | lia | lia].
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem4 & md4 & -> & HJ4 & Hio4 & HP4 & H10c & Heff4 & Hfr4 & Hpres4).
clear HJ. rename HJ4 into HJ.
(* ---- R3: 0x83edc -> 0x83f08, the `ret` ---- *)
assert (F2b : getr regs3 2 = getr (ms_regs ms1) 2) by pwr_call_keep HP4.
assert (F3b : getr regs3 3 = getr (ms_regs ms1) 3) by pwr_call_keep HP4.
assert (F4b : getr regs3 4 = getr (ms_regs ms1) 4) by pwr_call_keep HP4.
assert (F8b : getr regs3 8 = getr (ms_regs ms1) 8) by pwr_call_keep HP4.
assert (F9b : getr regs3 9 = getr (ms_regs ms1) 9) by pwr_call_keep HP4.
assert (F18b : getr regs3 18 = getr (ms_regs ms1) 18) by pwr_call_keep HP4.
assert (F19b : getr regs3 19 = getr (ms_regs ms1) 19) by pwr_call_keep HP4.
assert (SP5 : spZ regs3 = spZ regs - 48) by (unfold spZ at 1; rewrite F2b; exact SP4).
assert (Xsh3b := pwe_sh3_denot EB pp H9' H32' ltac:(cbv beta; lia) ltac:(cbv beta; lia)). cbv [pwe_sh3] in Xsh3b.
assert (R4_9 : getr regs3 9 = w64 pp) by (rewrite F9b, RC9, pwr_soff0; exact H9').
assert (R4_8 : getr regs3 8 = w64 (pp + 16384))
  by (rewrite F8b, RC8, (pwe_soff EB 9 pp 16384 H9'); reflexivity).
assert (R4_18 : getr regs3 18 = w64 (Model.pad8 (Model.e_size e))).
{ rewrite F18b, RC18. unfold w64. rewrite denot_lit_U, Xpad'. reflexivity. }
assert (R4_19 : getr regs3 19 = w64 (shadow_addr (pp + 16384)))
  by (rewrite F19b, RC19, Xsh3b; reflexivity).
assert (KEd : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((spZ regs - (48 + ESTACK) <= a < spZ regs) \/
     (pp + len <= a < pp + len + pwe_len e \/ pp + Layout.OFF_LEN <= a < pp + Layout.OFF_LEN + 8)) ->
  aview rsegs (w_H W) mem4 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hz. rewrite (Hfr4 a Ha ltac:(cbv beta; lia) ltac:(cbv beta; lia)). apply KE; [exact Ha | exact Hz]. }
clear KE. rename KEd into KE.
assert (MGd := mem_grows_trans _ _ _ MG (pwr_grows_of_apres (w_H W) (ms_mem ms1) mem4 Hpres4)).
clear MG. rename MGd into MG.
assert (KSS : forall a, spZ regs - 48 <= a < spZ regs ->
  aview rsegs (w_H W) mem4 a = aview rsegs (w_H W) (ms_mem ms) a).
{ intros a Ha.
  rewrite (Hfr4 a ltac:(cbv beta; lia) ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (S3 a ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (Hfr2 a ltac:(cbv beta; lia) ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (S1 a ltac:(cbv beta; lia) ltac:(cbv beta; lia)). reflexivity. }
assert (VL4 : val_mem rsegs (mrestrict (w_H W) mem4) (pp + 16384) 8 (len + 8 + Model.e_size e)).
{ apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms1) mem4 _ 8 _ VL3).
  intros xx Hxx. apply Hfr4; lia. }
assert (HprL4 : forall a, pp + 16384 <= a < pp + 16392 -> apresent (w_H W) mem4 a).
{ intros a Ha.
  refine (proj1 (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hawr a _))).
  cbv [pwe_E]. lia. }
set (E3 := Ereg regs3 (pwe_extra [len; Model.e_size e; bv_unsigned (getr regs 1);
  bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18);
  bv_unsigned (getr regs 19)])).
assert (I9 : ew E3 9 = Z_to_bv 64 pp)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 9 9%bv eq_refl); exact R4_9).
assert (I32 : ew E3 32 = Z_to_bv 64 SHADOW_OFF) by (subst E3; reflexivity).
assert (I9u : bv_unsigned (ew E3 9) = pp) by (rewrite I9; apply unsigned_lit_small; lia).
assert (I2 : bv_unsigned (ew E3 2) = spZ regs - 48)
  by (subst E3; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl); exact SP5).
assert (I35 : ew E3 35 = getr regs 1)
  by (transitivity (Z_to_bv 64 (bv_unsigned (getr regs 1)));
      [subst E3; reflexivity | apply Z_to_bv_bv_unsigned]).
assert (I36 : ew E3 36 = getr regs 8)
  by (transitivity (Z_to_bv 64 (bv_unsigned (getr regs 8)));
      [subst E3; reflexivity | apply Z_to_bv_bv_unsigned]).
assert (I37 : ew E3 37 = getr regs 9)
  by (transitivity (Z_to_bv 64 (bv_unsigned (getr regs 9)));
      [subst E3; reflexivity | apply Z_to_bv_bv_unsigned]).
assert (I38 : ew E3 38 = getr regs 18)
  by (transitivity (Z_to_bv 64 (bv_unsigned (getr regs 18)));
      [subst E3; reflexivity | apply Z_to_bv_bv_unsigned]).
assert (I39 : ew E3 39 = getr regs 19)
  by (transitivity (Z_to_bv 64 (bv_unsigned (getr regs 19)));
      [subst E3; reflexivity | apply Z_to_bv_bv_unsigned]).
assert (I33 : ew E3 33 = Z_to_bv 64 len) by (subst E3; reflexivity).
assert (I34 : ew E3 34 = Z_to_bv 64 (Model.e_size e)) by (subst E3; reflexivity).
assert (I2' : ew E3 2 = Z_to_bv 64 (spZ regs - 48))
  by (rewrite <- I2; symmetry; apply Z_to_bv_bv_unsigned).
assert (Xpad3 : U E3 pwe_pad = Model.pad8 (Model.e_size e))
  by (apply (pwe_pad_val E3 len (Model.e_size e) I33 I34); lia).
assert (Xtot3 : U E3 pwe_tot = len + 8 + Model.e_size e).
{ unfold pwe_tot. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E3 33 len 8 I33) by lia.
  rewrite (U_atom_off E3 34 (Model.e_size e) 0 I34) by lia.
  rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
assert (HR3 : regs_ok E3 p3_regs regs3).
{ unfold p3_regs. apply regs_ok_override; [apply regs_ok_override; [apply regs_ok_override;
    [subst E3; apply regs_ok_Ereg | | ] | | ] | | ];
  try (intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  - rewrite (pwe_soff E3 9 pp 16384 I9). symmetry. exact R4_8.
  - rewrite (pwe_sh3_denot E3 pp I9 I32) by lia. symmetry. exact R4_19.
  - rewrite denot_lit_U, Xpad3. symmetry. exact R4_18. }
clear HS SHOK.
assert (HS : st_ok rsegs E3 ss_p3
  (restrict (w_H W) (mkst regs3 (Z_to_bv 64 PWE_P3) mem4 (seg_rom rsegs)))).
{ subst E3. apply (pwe_entry3 W regs3 mem4 pp len (Model.e_size e)
    (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
    (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19))
    R4_9 R4_8 R4_18 R4_19 ltac:(cbv beta; lia)
    ltac:(rewrite SP5; apply pwr_mod16_sub; [exact Hal16 | reflexivity])
    Hpp0 Hpp8 Hpp47 ltac:(rewrite SP5; lia) Hlen0 Hlen8 ltac:(cbv beta; lia) Hsz
    (u64_range (getr regs 1)) (u64_range (getr regs 8)) (u64_range (getr regs 9))
    (u64_range (getr regs 18)) (u64_range (getr regs 19))
    VL4
    ltac:(replace (spZ regs3 + 40) with (spZ regs + -8) by lia;
          apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem4 _ 8 _ Vra1);
          intros xx Hxx; apply KSS; lia)
    ltac:(replace (spZ regs3 + 32) with (spZ regs + -16) by lia;
          apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem4 _ 8 _ Vs01);
          intros xx Hxx; apply KSS; lia)
    ltac:(replace (spZ regs3 + 24) with (spZ regs + -24) by lia;
          apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem4 _ 8 _ Vs11);
          intros xx Hxx; apply KSS; lia)
    ltac:(replace (spZ regs3 + 16) with (spZ regs + -32) by lia;
          apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem4 _ 8 _ Vs21);
          intros xx Hxx; apply KSS; lia)
    ltac:(replace (spZ regs3 + 8) with (spZ regs + -40) by lia;
          apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms) mem4 _ 8 _ Vs31);
          intros xx Hxx; apply KSS; lia)
    HprL4). }
assert (SH5 : forall x, 0 <= x < kHighMemEnd ->
  aview rsegs (w_H W) mem4 (shadow_addr x) = aview rsegs (w_H W) memc (shadow_addr x))
  by exact (pwe_shadow_kept W W memc mem4 (spZ regs) (48 + ESTACK) pp len e
      ltac:(intros a Ha Hx Hy; apply KE;
            [exact Ha | intros [Hc | Hc]; [exact (Hx Hc) | exact (Hy Hc)]])
      Hceilsp Hlen0 Hcap Hppam Hpp0).
assert (RApp5 : range_addressable (aview rsegs (w_H W) mem4) SHADOW_OFF pp Layout.PP_SIZE)
  by exact (pwe_ra_kept_of_shadow W W memc mem4 pp Layout.PP_SIZE SH5 Hppam Hpp0 ltac:(cbv beta; lia) Hppra).
assert (SHOK : sh_ok rsegs PWE_Bx p3_SH E3 (mrestrict (w_H W) mem4))
  by exact (pwe_shblk W mem4 E3 pp p3_SH eq_refl I32 I9 Hpp0 Hpp47
      ltac:(rewrite <- HPP; exact Hppam) ltac:(rewrite <- HPP; exact RApp5)).
clearbody E3.
pwe_run_awr ltac:(
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly1 ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly1 ow) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat pp);
  [ reflexivity | exact I9u
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply Hawr; cbv [pwe_E]; lia
  | apply awr_ok_nil ]) PWE_RET.
(* ---- the `ret` leaf ---- *)
pwr_upd KE KEn. clear KE. rename KEn into KE.
pwr_new (fun a => pp + 16384 <= a < pp + 16392) S5.
pose proof (pwe_regs_kept E3 _ _ regs3 p3_regs (w_H W) pwr_clobA HS HR3
  ltac:(vm_compute; reflexivity)) as KR3.
pwe_reg HS (1%bv : bv 5) RD1. pwe_reg HS (2%bv : bv 5) RD2.
pwe_reg HS (8%bv : bv 5) RD8. pwe_reg HS (9%bv : bv 5) RD9.
pwe_reg HS (18%bv : bv 5) RD18. pwe_reg HS (19%bv : bv 5) RD19.
pwe_regn HS 1%nat RgL3.
pose proof (pwe_field E3 _ 9 pp _ _ _ _ _ 16384 8 (SAlu ALU_ADD pwe_tot pwe_pad) (len + pwe_len e)
  RgL3 I9u
  ltac:(cbv [pwe_tot pwe_pad]; cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw];
        rewrite Xtot3, Xpad3; rewrite zcanon_id by (unfold M64; lia); lia)
  ltac:(cbn; lia) ltac:(cbn; lia)) as VLF.
change (N.to_nat 8) with 8%nat in VLF.
assert (KALL : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r pwr_clobA ->
  getr (ms_regs ms2) r = getr regs r).
{ intros r Hr0 Hn.
  rewrite (KR3 r Hr0 Hn), (pwe_pres _ _ r HP4 Hr0 (pwr_clob_sub r Hn)),
    (KR2 r Hr0 Hn), (pwe_pres _ _ r HP2 Hr0 (pwr_clob_sub r Hn)), (KR1 r Hr0 Hn).
  exact (KR0 r Hr0 Hn). }
assert (KW : forall a, pp + len <= a < pp + len + 8 ->
  aview rsegs (w_H W) (ms_mem ms2) a = aview rsegs (w_H W) (ms_mem ms0) a).
{ intros a Ha.
  rewrite (S5 a ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (Hfr4 a ltac:(cbv beta; lia) ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (S3 a ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (Hfr2 a ltac:(cbv beta; lia) ltac:(cbv beta; lia) ltac:(cbv beta; lia)). reflexivity. }
assert (Vszf : val_mem rsegs (mrestrict (w_H W) (ms_mem ms2)) (pp + len) 4 (Model.e_size e)).
{ apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms0) (ms_mem ms2) _ 4 _ Vsz2).
  intros xx Hxx. apply KW. lia. }
assert (Vtyf : val_mem rsegs (mrestrict (w_H W) (ms_mem ms2)) (pp + len + 4) 4 (Model.e_type e)).
{ apply (pwm_val_mem_kept rsegs (w_H W) (w_H W) (ms_mem ms0) (ms_mem ms2) _ 4 _ Vty2).
  intros xx Hxx. apply KW. lia. }
assert (Hbodyf : forall i, 0 <= i < Model.e_size e ->
  aview rsegs (w_H W) (ms_mem ms2) (pp + len + 8 + i) = aview rsegs (w_H W) memc (q + 8 + i)).
{ intros i Hi.
  rewrite (S5 (pp + len + 8 + i) ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (Hfr4 (pp + len + 8 + i) ltac:(cbv beta; lia) ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (S3 (pp + len + 8 + i) ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (Heff i ltac:(cbv beta; lia)). apply KEq. lia. }
assert (Hpadf : forall i, 0 <= i < Model.pad8 (Model.e_size e) ->
  mbyte rsegs (mrestrict (w_H W) (ms_mem ms2)) (pp + len + 8 + Model.e_size e + i) =
  Some (Z_to_bv 8 0)).
{ intros i Hi. apply pwm_aview_mbyte.
  rewrite (S5 (pp + len + 8 + Model.e_size e + i) ltac:(cbv beta; lia) ltac:(cbv beta; lia)).
  rewrite (Heff4 i ltac:(cbv beta; lia)). reflexivity. }
assert (SHF : forall x, 0 <= x < kHighMemEnd ->
  aview rsegs (w_H W) (ms_mem ms2) (shadow_addr x) = aview rsegs (w_H W) memc (shadow_addr x))
  by exact (pwe_shadow_kept W W memc (ms_mem ms2) (spZ regs) (48 + ESTACK) pp len e
      ltac:(intros a Ha Hx Hy; apply KE;
            [exact Ha | intros [Hc | Hc]; [exact (Hx Hc) | exact (Hy Hc)]])
      Hceilsp Hlen0 Hcap Hppam Hpp0).
eapply (SRr_ret_at rsegs pwe_tbl pwe_tbl_ok pwe_wx W E3);
  [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. red. eexists. exists lyc, Sc, (ms_regs ms2), (ms_mem ms2). eexists.
split; [rewrite RD1, pwr_soff0, I35, Hra; reflexivity|].
split; [reflexivity|].
split; [eapply (ajournal_materialize rsegs B LAWS); try exact Hsegs; exact HJ|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  try pwr_keep_reg KALL.
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite RD2, (pwe_soff E3 2 (spZ regs - 48) 48 I2').
    replace (spZ regs - 48 + 48) with (spZ regs) by lia.
    unfold spZ. apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite RD8, pwr_soff0, I36. reflexivity.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite RD9, pwr_soff0, I37. reflexivity.
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite RD18, pwr_soff0, I38. reflexivity.
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite RD19, pwr_soff0, I39. reflexivity. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [ let rec kio := first [ apply same_io_refl
                              | eapply same_io_trans; [| apply same_io_wvb_pwe]; kio
                              | eapply same_io_trans; [| exact Hio4]; kio
                              | eapply same_io_trans; [| exact Hio2]; kio ] in kio |].
split; [apply mo_le_refl; exact MTL|].
split; [intros a Ha Hx Hy; apply KE;
        [exact Ha | intros [Hc | Hc]; [exact (Hx Hc) | exact (Hy Hc)]]|].
split.
{ apply (pwe_post_bytes (w_H W) (w_H W) memc (ms_mem ms2) pp q len e Hblen Hsz Htyr Hent
    Vszf Vtyf Hbodyf Hpadf). }
split; [rewrite HOL; exact VLF|].
split; [exact SHF|].
split.
- exact (pwe_ra_kept_of_shadow W W memc (ms_mem ms2) pp Layout.PP_SIZE SHF Hppam Hpp0
    ltac:(cbv beta; lia) Hppra).
- exact (pwe_ra_kept_of_shadow W W memc (ms_mem ms2) q Layout.ENT_SIZE SHF Hqam Hq0
    ltac:(cbv beta; lia) Hqra).
Qed.
End d.
End b.

Print Assumptions pwe_B_walk.
About pwe_B_walk.

(* The runtime invariant's laws are a kernel theorem (YG0q.AR_laws_ok), so the walk's open hypotheses are the
   meter's laws, the image's two symbol-record cells and the two runtime callees' laws. *)
Corollary pod_write_ent_B : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}
  (B : asyms) (MT : ameter_ops),
  ameter_laws MT -> as_got_shadow B = PWE_GOT -> as_shadow_cell B = PWE_CELL ->
  aintrin_realizes rsegs B OCpy PWE_MEMCPY -> aintrin_realizes rsegs B OSet PWE_MEMSET ->
  pod_write_ent_specX rsegs B MT PWE_A.
Proof.
intros fx rc SK B MT MTL HBgot HBcell AMEMCPY AMEMSET.
exact (@pwe_B_walk fx rc SK B MT MTL (YG0q.AR_laws_ok rsegs B) HBgot HBcell AMEMCPY AMEMSET).
Qed.
Print Assumptions pod_write_ent_B.
About pod_write_ent_B.
