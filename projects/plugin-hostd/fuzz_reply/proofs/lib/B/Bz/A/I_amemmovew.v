(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/I_memcpyw.v, with its module paths, module names, addresses and numbers changed; 252 of its 509 lines of code are new or changed and 282 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_pcap/lib/A/Bz/A/I_amemmovew.v
   (commit eabce720039), the __asan_memmove walk, with its module paths changed and its code
   addresses moved from fuzz_pcap.asan's __asan_memmove (0x51c50) to fuzz_reply.asan's (0x52e04) in the lib/A source (of
   that source: the 220 words differ only in auipc/ld/jal relocations, so each pc keeps its offset, +0x11b4), and from
   there to fuzz_reply.asan-ubsan's (0x52e5c: each pc at +0x58 from its fuzz_reply.asan twin, +0x120c from pcap's).
   pcap's I_memcpyw.icells and I_amemcpy.stk_after_copy are restated here (amm_cells at fuzz_reply.asan-ubsan's cells;
   stk_after_copy unchanged) instead of importing the two memcpy walks. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/Bz/A/I_amemmovew.v at commit 8fe76247f18, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (32 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10-30: comments only: the inherited comments made true of this image-B file (addresses,
   offsets and loads named as fuzz_reply.asan-ubsan's); the inherited fuzz_pcap -> fuzz_reply.asan claims are kept and
   marked as about the lib/A source. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck D_kit X_atexit I_imemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u32arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u64arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8ro segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.

(* The runtime cells this walk reads (pcap took them from I_memcpyw.icells, less REAL(memcpy)'s slot, which
   __asan_memmove never reads): the GOT slot of __asan_shadow_memory_dynamic_address (0x9df50) and the cell it names
   (0xa6638, the shadow offset), and the GOT slot of asan's replace_intrin_cached flag (0x9eab8) and the flag byte
   (0xa7319, 1 after start-up).  In the lib/A source the addresses were paired with fuzz_pcap.asan's by the instruction
   that loads them (pcap 0x51c80 / 0x51cac against fuzz_reply.asan 0x52e34 / 0x52e60); in fuzz_reply.asan-ubsan those
   loads are at 0x52e8c / 0x52eb8 (__asan_memmove+0x30 / +0x5c). *)
Definition amm_cells (m : mem) : Prop :=
  ro_cells asegs m 0x9df50 [C8 (Z_to_bv 64 0xa6638)]
  /\ ro_cells asegs m 0x9eab8 [C8 (Z_to_bv 64 0xa7319)]
  /\ ro_cells asegs m 0xa6638 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ ro_cells asegs m 0xa7319 [C1 (Z_to_bv 8 1)].

(* pcap's I_amemcpy.v:52-68, unchanged. *)
Lemma stk_after_copy : forall m m' lo hi a n (bs : list byte),
  stk asegs m lo hi -> munch [(a, a + n)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' a [CB (Z.to_nat n) bs] -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi a n bs (H0 & H1 & H) MU WM ((Hwf & B0 & B1 & B) & _).
  split; [exact H0|]. split; [exact H1|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)]. split; [exact (WM _ Hw)|].
  assert (Ex : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia).
  cbn [cells_bytes cbytes cells_wf cell_wf] in Hwf, B0, B1, B. rewrite app_nil_r in B1, B. destruct Hwf as [Hl _].
  destruct (Z_lt_le_dec x a) as [L|L]; [| destruct (Z_lt_le_dec x (a + n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite Ex. cbn [outside]. split; [lia| exact I].
  - assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
    specialize (B (Z.to_nat (x - a)) Hi). rewrite Z2Nat.id in B by lia. replace (a + (x - a)) with x in B by lia.
    destruct (nth_error bs (Z.to_nat (x - a))) as [c|] eqn:E; [exists c; exact B|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite Ex. cbn [outside]. split; [lia| exact I].
Qed.

Definition amemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d : Z) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + Z.of_nat (length src)); (bv_unsigned sp - 2224, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' d [CB (length src) src].

Lemma amemmove_prologue : forall (sp : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo sp -> lo <= sp - 2224 -> kHighShadowEnd < lo -> sp < 2^63 ->
  amm_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (junk : list byte) (a3' : word),
      ms' = MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) s1
                    a0 a1 a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x52e98) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2144, sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' (sp + -2144) [CB 2080 junk]
      /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52e5c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH (G2 & G1 & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2144, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  carve_frame 64%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  zidle_beginz sp 2144%Z MUz1 WMz1.
  zhide.
  do 10 lstep.
  zidle_end MUz1 WMz1.
  do 5 astep.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRs|]. split; [exact FR| exact ST].
Qed.

Lemma amemmove_src_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a5' a6' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 e) (Z_to_bv 64 e) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x530b4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 c) (Z_to_bv 64 e) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x530a4) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    zhide.
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section SrcRIP.
Hypothesis RIP : rip_stmt.

Lemma amemmove_src_rip : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 < n -> d + n < 2^63 -> s + n < 2^63 ->
  acc asegs m s n -> rng_ok s n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1'
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7' s2' s3 s4' s5'
                    s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x52ef0) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x530bc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  zhide.
  do 6 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 4 lstep. lstep. if_true.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma amemmove_src : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 <= n -> d + n < 2^63 -> s + n < 2^63 ->
  chk_ok m s n -> m2s_cells m -> amm_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1'
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7' s2' (Z_to_bv 64 (n + -65)) s4' s5'
                    s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x52ef0) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52e98) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN (AC & QW & RO) M2S (G2 & G1 & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  zhide.
  do 4 lstep. rewrite (lxor_ones64 s) by lia.
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - s)) = 18446744073709551615 - s) by (apply unsigned_lit; lia).
  if_false.
  lstep. lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (amemmove_src_rip sp d s n); try assumption; lia.
  - subst n. if_true. lstep. if_false. lstep.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + s ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((s / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (s + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((s + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (s + n + -1) with (s + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (s + n + -1) / 8) with ((s + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + s / 8) with (s / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m s n AC ltac:(lia) S0) as SB. unfold shad, SHB in SB.
      destruct (SB ((s + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (amemmove_src_rip sp d s n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (amemmove_src_loop (Z.to_nat ((s + n + -1) / 8 + 2147450880 - (s / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a5' & a6' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 19 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (amemmove_src_rip sp d s n); try assumption; lia.
    + apply evt_done. do 19 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

End SrcRIP.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma amemmove_dst_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a5' a6' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 e) (Z_to_bv 64 e) a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x53158) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 c) (Z_to_bv 64 e) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x53148) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section DstRIP.
Hypothesis RIP : rip_stmt.

Lemma amemmove_dst_rip : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 < n -> d + n < 2^63 -> s + n < 2^63 ->
  acc asegs m d n -> rng_ok d n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s5' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1'
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7' s2' s3' s4 s5'
                    s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x52f3c) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x53160) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO N0) as (RIM & N40).
  do 5 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  do 4 lstep. lstep. if_true.
  apply evt_done. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma amemmove_dst : forall (sp d s n : Z) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - 2224 -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= d -> 0 <= s -> 0 <= n -> d + n < 2^63 -> s + n < 2^63 ->
  chk_ok m d n -> m2s_cells m -> amm_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a3' a4' a5' a6' a7' s2' s3' s5' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1'
                    (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3' a4' a5' a6' a7' s2' s3' s4 s5'
                    s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x52f3c) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 (n + -65)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52ef0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 S0 N0 DN SN (AC & QW & RO) M2S (G2 & G1 & SHC & RI) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 d) by lia.
  assert (EUnd : bv_unsigned (Z_to_bv 64 (18446744073709551615 - d)) = 18446744073709551615 - d) by (apply unsigned_lit; lia).
  if_false.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL]; [| destruct (Z.eq_dec n 0) as [Z0|NZ]].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    if_true. lstep. if_true.
    apply (amemmove_dst_rip sp d s n); try assumption; lia.
  - subst n. if_true. lstep. if_false. lstep.
    apply evt_done. do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + d ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((d / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (d + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((d + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (d + n + -1) with (d + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (d + n + -1) / 8) with ((d + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + d / 8) with (d / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m d n AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((d + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (amemmove_dst_rip sp d s n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (amemmove_dst_loop (Z.to_nat ((d + n + -1) / 8 + 2147450880 - (d / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a5' & a6' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 18 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (amemmove_dst_rip sp d s n); try assumption; lia.
    + apply evt_done. do 18 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

End DstRIP.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Theorem amemmove_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s : Z) (src junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length src)) ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2224 -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= d -> 0 <= s -> d + Z.of_nat (length src) <= 2^47 -> s + Z.of_nat (length src) <= 2^47 ->
  (Z.of_nat (length src) = 0 \/ s + Z.of_nat (length src) <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= s) ->
  (Z.of_nat (length src) = 0 \/ d + Z.of_nat (length src) <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= d) ->
  bytes_at asegs m s src -> rw_cells asegs m d [CB (length src) junk] ->
  chk_ok m s (Z.of_nat (length src)) -> chk_ok m d (Z.of_nat (length src)) -> m2s_cells m -> amm_cells m -> mem_inv asegs m ->
  evt asegs (amemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52e5c) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> -> ST LO LOLO SPH D0 S0 DH SH SEPS SEPD SRC DST CS CD M2S IC MI.
  unfold kHighShadowEnd in *.
  set (n := Z.of_nat (length src)) in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(d, d + n); (usp - 2224, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(usp - 2224, usp)] m) as MUf.
  pose proof IC as (G2 & G1 & SHC & RI).
  assert (SRC0 : keep (bytes_at asegs m s src)) by exact SRC. clear SRC.
  assert (DST0 : keep (rw_cells asegs m d [CB (length src) junk])) by exact DST. clear DST.
  assert (N0 : 0 <= n) by lia.
  assert (N40 : n <= 2^40).
  { destruct (Z.eq_dec n 0) as [E|NE]; [lia|]. destruct CS as (_ & _ & RO). destruct (RO ltac:(lia)) as (_ & HN). exact HN. }
  assert (RS : n = 0 \/ s + n <= 0x7fff8000 \/ 0x10007fff8000 <= s).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (RD : n = 0 \/ d + n <= 0x7fff8000 \/ 0x10007fff8000 <= d).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (OFF : forall p, chk_ok m p n -> 0 <= p -> p + n <= 2^47 ->
            forall m', munch [(d, d + n); (usp - 2224, usp)] m m' -> chk_ok m' p n).
  { intros p CP P0 P1 m' MU'. apply (chk_ok_agree m m' p n CP P0 P1). apply (agree_of_munch _ _ _ _ MU'). intros x Hx.
    cbn [outside]. split; [lia| split; [lia| exact I]]. }
  call (amemmove_prologue usp); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact IC| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (OFF s CS S0 SH mm MU) as CS1; pose proof (OFF d CD D0 DH mm MU) as CD1 end.
  assert (IC1 : amm_cells x) by (split; [exact G2| split; [exact G1| split; [exact SHC| exact RI]]]).
  assert (M2S1 : m2s_cells x).
  { destruct M2S as (M1 & M2 & M3). split; [| split].
    - apply (rw_cells_agree asegs m x _ _ M1); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia.
    - apply (rw_cells_agree asegs m x _ _ M2); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia.
    - apply (rw_cells_agree asegs m x _ _ M3); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia. }
  call (amemmove_src RIP usp d s n); [exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
        | exact CS1| exact M2S1| exact IC1| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST2 end.
  clear CS1 CD1 IC1 M2S1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (OFF d CD D0 DH mm MU) as CD2;
    assert (IC2 : amm_cells mm) by (split; [exact G2| split; [exact G1| split; [exact SHC| exact RI]]]);
    assert (M2S2 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia ])
  end.
  call (amemmove_dst RIP usp d s n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
        | exact CD2| exact M2S2| exact IC2| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST3 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SRC : bytes_at asegs mm s src)
      by (unfold keep in SRC0; apply (bytes_at_agree asegs m mm _ _ SRC0); apply (agree_of_munch _ _ _ _ MUf); intros y Hy;
          cbn [outside]; fold n in Hy; (split; [lia| exact I]));
    assert (DST : rw_cells asegs mm d [CB (length src) junk])
      by (unfold keep in DST0; apply (rw_cells_agree asegs m mm _ _ DST0); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy;
          cbn [outside]; cbn [cells_size csize] in Hy; rewrite Nat.add_0_r in Hy; fold n in Hy; (split; [lia| exact I]))
  end.
  clear CD2 IC2 M2S2 MUf SRC0 DST0.
  lstep.
  destruct (Z.eq_dec n 0) as [NZ0|NNZ].
  - eapply evt_cut.
    { eapply imemmove_spec with (xs := src) (junk := junk);
        [ reflexivity| reflexivity| reflexivity| lia| lia| lia
        | unfold n; rewrite Nat2Z.id; reflexivity| exact SRC
        | unfold n; rewrite Nat2Z.id; exact DST| assumption]. }
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
    rewrite NZ0, Z.add_0_r in MUc.
    lazymatch type of MUc with munch _ ?m1 ?m2 =>
      assert (MUe : munch [] m1 m2) by (eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia);
      clear MUc; transport_after_call asegs m1 m2 MUe WMc; clear MUe WMc end.
    replace (ret_pc (Z_to_bv 64 0x52f40)) with (Z_to_bv 64 0x52f40) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 10 lstep.
    release_frame FR ST3 (usp + -64). release_frame FRs ST3 usp.
    lstep.
    unfold amemmove_post. sys_finish.
    + rewrite (unsigned_lit usp) by lia.
      eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite (unsigned_lit usp) by lia. assumption.
    + lazymatch goal with H : rw_cells asegs _ d [CB _ src] |- _ => unfold n in H; rewrite Nat2Z.id in H; exact H end.
  - eapply evt_cut.
    { eapply imemmove_spec with (xs := src) (junk := junk);
        [ reflexivity| reflexivity| reflexivity| lia| lia| lia
        | unfold n; rewrite Nat2Z.id; reflexivity| exact SRC
        | unfold n; rewrite Nat2Z.id; exact DST| assumption]. }
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
    lazymatch type of MUc with munch _ ?m1 ?m2 =>
      assert (ST4 : stk asegs m2 lo (usp + -2144))
        by (exact (stk_after_copy m1 m2 lo (usp + -2144) d n src ST3 MUc WMc PO));
      clear ST3; rename ST4 into ST3;
      transport_after_call asegs m1 m2 MUc WMc; clear MUc WMc end.
    replace (ret_pc (Z_to_bv 64 0x52f40)) with (Z_to_bv 64 0x52f40) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 10 lstep.
    release_frame FR ST3 (usp + -64). release_frame FRs ST3 usp.
    lstep.
    unfold amemmove_post. sys_finish.
    + rewrite (unsigned_lit usp) by lia.
      eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite (unsigned_lit usp) by lia. assumption.
    + lazymatch goal with H : rw_cells asegs _ d [CB _ src] |- _ => unfold n in H; rewrite Nat2Z.id in H; exact H end.
Qed.

End WithRIP.
