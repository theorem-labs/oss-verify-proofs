(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit AF_atexit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition SHOFF : Z := 0x7fff8000.
Definition shd (a : Z) : Z := SHOFF + Z.shiftr a 3.
Definition shn (l : Z) : Z := Z.shiftr l 3.

End CANSEC1.
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

Section CANSEC2. Context {rc : runConstT}.
Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Definition mdtor_rt (m : mem) : Prop :=
     rw_cells bsegs m 0x998b8 [C8 (Z_to_bv 64 0x1315a0)]
  /\ rw_cells bsegs m 0x998c8 [C8 (Z_to_bv 64 0x133628); C8 (Z_to_bv 64 0x9f2f8); C8 (Z_to_bv 64 0xa1af8);
                                C8 (Z_to_bv 64 0xa27e8); C8 (Z_to_bv 64 0xa27f0); C8 (Z_to_bv 64 0xa27e0)]
  /\ rw_cells bsegs m 0x998f8 [C8 (Z_to_bv 64 0x9b738)]
  /\ rw_cells bsegs m 0x9b730 [C8 (Z_to_bv 64 0x92c08); C8 (Z_to_bv 64 0x9300c)]
  /\ rw_cells bsegs m 0xa1af8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0xa27d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xa135c [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x1336a0 [C8 (Z_to_bv 64 18446744073709551615)]
  /\ rw_cells bsegs m 0x9f310 [C4 (Z_to_bv 64 1)].

Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0x998b8 \/ (0x99900 <= lo /\ hi <= 0x9b730) \/ (0x9b740 <= lo /\ hi <= 0x9f310) \/ (0x9f314 <= lo /\ hi <= 0xa135c)
   \/ (0xa135d <= lo /\ hi <= 0xa1af8) \/ (0xa1b00 <= lo /\ hi <= 0xa27d8) \/ (0xa27da <= lo /\ hi <= 0x1336a0) \/ 0x1336a8 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0x998b8 <= A /\ A + n <= 0x99900) \/ (0x9b730 <= A /\ A + n <= 0x9b740) \/ (0x9f310 <= A /\ A + n <= 0x9f314)
              \/ (0xa135c <= A /\ A + n <= 0xa135d) \/ (0xa1af8 <= A /\ A + n <= 0xa1b00) \/ (0xa27d8 <= A /\ A + n <= 0xa27da)
              \/ (0x1336a0 <= A /\ A + n <= 0x1336a8)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

Definition poison_low_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sb sl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma poison_low_spec : forall RNG (sb sl : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> KHIGH <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  mdtor_rt m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x5f7000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF bsegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x537dc) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  unfold KHIGH in KH. pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x800cd000 /\ 0 < shn size).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  carve_frame 64%nat ST.
  do 8 hstep.
  hstep. if_true.
  zstep. hstep. if_cases K1; zify_cond K1.
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 hstep.
  do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  zstep. hstep. if_cases K8; zify_cond K8.
  { exfalso. apply K8. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  do 2 zstep.
  hstep. if_cases K9; zify_cond K9. 2:{ exfalso. lia. }
  do 3 hstep.
  hstep. if_cases K10; zify_cond K10; [exfalso; lia|].
  do 5 zstep.
  assert (E1 : Z.land (Z.shiftr (addr + size + -8) 3 + 1) 18446744073709551615 - Z.shiftr addr 3 = shn size).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
    rewrite Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr addr 3) with (shd addr).
  hstep. if_false.
  do 3 hstep.
  hstep. if_cases KT; zify_cond KT.
  2:{ exfalso. lia. }
  do 3 hstep. do 8 hstep.
  hstep.
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold poison_low_post. destruct_exs PO.
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  do 16 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros xq Hxq. cbn in Hxq |- *. tauto. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  split. 2: exact DST2.
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR'.
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST'.
  eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end. exact FR'.
Qed.

Definition unreg_one_post (spv d sb sl se : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x401cc) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x133628) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1b1ca) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9b738) s8 (Z_to_bv 64 0x9f2f8)
                  (Z_to_bv 64 0xa1af8) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x401cc) fc None m' (seg_rom bsegs)
    /\ munch [(sb, se)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma unreg_one_spec : forall RNG (sb sl se : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv bsegs m -> mdtor_rt m ->
  rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 (swr mod 256))] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 65536 -> 0x10000 <= beg -> beg + swr <= 0x5f7000 ->
  0x10000 <= d -> d + 64 <= 0x5f7000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr -> se = sb + sl ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF bsegs RNG (unreg_one_post spv d sb sl se gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x133628) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b1ca) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x9b738) s8 (Z_to_bv 64 0x9f2f8)
             (Z_to_bv 64 0xa1af8) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x401e4) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> -> DST RIMG RSH.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 8192).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  do 7 hstep.
  hstep. if_false.
  hstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  hstep. if_true.
  hstep. if_false.
  do 2 hstep. do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  zstep. hstep. if_cases K3; zify_cond K3.
  { exfalso. apply K3. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  hstep. zstep. rewrite (unsigned_lit8 (swr mod 256)) by (apply Z.mod_pos_bound; lia). hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear -SL. Z.div_mod_to_equations. lia. }
  do 6 hstep. hstep. if_false.
  do 3 hstep. do 5 zstep. hstep. do 3 zstep.
  assert (E1 : Z.land (2147450880 + Z.shiftr (beg + swr + -8) 3 + 1) 18446744073709551615 - Z.land (2147450880 + Z.shiftr beg 3) 18446744073709551615
               = shn swr).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
    rewrite !Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr beg 3) with (shd beg).
  hstep. if_cases KT; zify_cond KT. 2:{ exfalso. lia. }
  do 3 hstep.
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold unreg_one_post. destruct_exs PO.
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  cbn [ret_pc reg_get].
  replace (ret_pc (Z_to_bv 64 0x401cc)) with (Z_to_bv 64 0x401cc : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed.

Definition gdesc (m : mem) (d beg sz swr nm md odr : Z) : Prop :=
     rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 (swr mod 256))].

Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells bsegs m 0x9a550 [C8 (Z_to_bv 64 0x9e180); C8 (Z_to_bv 64 0x9e440)]
  /\ rw_cells bsegs m 0x9e440 [C8 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0x9f3b0 [C8 (Z_to_bv 64 0)]
  /\ gdesc m 0x9e180 0x20d20 0xd 0x20 0x1bfaf 0x20cdb (2^64 - 1)
  /\ gdesc m 0x9e1c0 0x20d40 0x17 0x40 0x1f793 0x20cdb (2^64 - 1)
  /\ gdesc m 0x9e200 0x20d80 0xd 0x20 0x1e6fa 0x20cdb (2^64 - 1)
  /\ gdesc m 0x9e240 0x20da0 0x49 0x80 0x2046f 0x20cdb (2^64 - 1)
  /\ gdesc m 0x9e280 0x20e20 0x45 0x80 0x1476e 0x20cdb (2^64 - 1)
  /\ gdesc m 0x9e2c0 0x20ea0 0x47 0x80 0x136f4 0x20cdb (2^64 - 1)
  /\ gdesc m 0x9e300 0x20f20 0x11 0x40 0x1cf53 0x20cdb (2^64 - 1)
  /\ gdesc m 0x9e340 0x20f60 0x55 0x80 0x1872c 0x20cdb (2^64 - 1)
  /\ gdesc m 0x9e380 0x20fe0 0x400 0x500 0x1580c 0x22980 (2^64 - 1)
  /\ gdesc m 0x9e3c0 0x214e0 0x1000 0x1400 0x18733 0x22980 (2^64 - 1)
  /\ gdesc m 0x9e400 0x228e0 0x80 0xa0 0x15eb3 0x22980 (2^64 - 1)
  /\ (exists j, rw_cells bsegs m 0x7fffc1a4 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc1a8 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc1b0 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc1b4 [CB 16 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc1c4 [CB 16 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc1d4 [CB 16 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc1e4 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc1ec [CB 16 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc1fc [CB 160 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc29c [CB 640 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc51c [CB 20 j])
  /\ (exists j, rw_cells bsegs m 0x8000bc30 [CB 88 j]).

Local Ltac tr_one MU WM D H :=
  lazymatch type of H with
  | _ /\ _ => let Ha := fresh "Ha" in let Hb := fresh "Hb" in destruct H as [Ha Hb]; split; [tr_one MU WM D Ha | tr_one MU WM D Hb]
  | exists _, _ => let j := fresh "j" in let Hj := fresh "Hj" in destruct H as [j Hj]; exists j; tr_one MU WM D Hj
  | _ => eapply rw_cells_transport; [exact H | exact MU | exact WM | apply D; cbn; lia]
  end.

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800141a0 -> 0x5f4d04 <= A \/ (0x9e491 <= A /\ A + n <= 0x5f4ae0) \/ A + n <= 0x9e490 ->
              disjoint_from (AEXIT_W1 sp) A n).
  { intros A n Hn HA HO. unfold AEXIT_W1, MDTOR_DEPTH. cbn. lia. }
  unfold mdtor_pre, gdesc in *.
  destruct P as (RT & P).
  assert (RT' : mdtor_rt m').
  { eapply mdtor_rt_frame; [exact RT | exact MU | exact WM | ]. unfold AEXIT_W1, MDTOR_DEPTH.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  refine (conj RT' _). clear RT RT'.
  tr_one MU WM D P.
Qed.

End CANSEC2.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac hstep ::= zstep; fix_lit_store.
Ltac rt_split := unfold mdtor_rt; repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Ltac lit_nat := repeat match goal with H : rw_cells _ _ _ [CB (Z.to_nat (Zpos ?p)) _] |- _ =>
                  let v := eval vm_compute in (Z.to_nat (Zpos p)) in change (Z.to_nat (Zpos p)) with v in H; move H at top end.
Ltac lit_addr := repeat match goal with H : rw_cells _ _ (Zpos ?a + Zpos ?b) _ |- _ =>
                  let v := eval vm_compute in (Zpos a + Zpos b) in change (Zpos a + Zpos b) with v in H end.
Ltac lit_rng := repeat match goal with H : rng _ _ (Zpos ?a - Zpos ?b) |- _ =>
                  let v := eval vm_compute in (Zpos a - Zpos b) in change (Zpos a - Zpos b) with v in H end.
Ltac side RIMG RSTK KH :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RSTK | lia] ]
  | |- rng_aimg _ => exact RIMG
  | |- rw_cells _ _ (?a + ?b) _ => let v := eval vm_compute in (a + b) in change (a + b) with v; hyp_by_addr
  | |- rw_cells _ _ _ _ => hyp_by_addr
  | |- mdtor_rt _ => rt_split
  | |- mem_inv _ _ => hyp_by_addr
  | |- stk _ _ _ _ => hyp_by_addr
  | |- @eq _ _ _ => reflexivity
  | |- Z.lt (shn _) _ => vm_compute; reflexivity
  | |- _ => first [exact KH | lia]
  end.

Local Ltac clear_at a := try (match goal with H : rw_cells _ _ a _ |- _ => clear H end).
Definition parked (P : Prop) : Prop := P.
Local Ltac park H := lazymatch type of H with ?T => change T with (parked T) in H end.
Local Ltac unpark H MU WM DISJ :=
  unfold parked in H;
  lazymatch type of H with
  | rw_cells ?segs ?m0 ?a ?cs =>
      lazymatch type of MU with
      | munch ?W m0 ?m1 => apply (rw_cells_transport segs W m0 m1 a cs) in H; [ | exact MU | exact WM | apply DISJ; cbn; lia ]
      end
  end.
Section CANSEC3. Context {rc : runConstT}.
Theorem module_dtor_proof : module_dtor_stmt mdtor_pre.
Proof.
  unfold module_dtor_stmt. intros until lo. intros HPRE ST LO KH MI RSTK RIMG RW.
  pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold mdtor_pre, gdesc in P.
  destruct P as (RT & GSS & FLG & MTX & (D0 & B0) & (D1 & B1) & (D2 & B2) & (D3 & B3) & (D4 & B4) & (D5 & B5) & (D6 & B6) & (D7 & B7) & (D8 & B8) & (D9 & B9) & (D10 & B10) & [j0 S0] & [j1 S1] & [j2 S2] & [j3 S3] & [j4 S4] & [j5 S5] & [j6 S6] & [j7 S7] & [j8 S8] & [j9 S9] & [j10 S10] & [j11 S11]).
  lit_addr.
  change (2^64 - 1) with 18446744073709551615 in D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10.
  park D0; park B0. park D1; park B1. park D2; park B2. park D3; park B3. park D4; park B4. park D5; park B5. park D6; park B6. park D7; park B7. park D8; park B8. park D9; park B9. park D10; park B10.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  unfold MDTOR_W in RW.
  repeat lazymatch type of RW with Forall _ (_ :: _) =>
    let H := fresh "RW" in pose proof (Forall_inv RW) as H; cbn [fst snd] in H; apply Forall_inv_tail in RW end.
  lit_rng.
  pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9e440, 0x9e448); (0x9f3b0, 0x9f3b8); (0x7fffc1a4, 0x7fffc1fc); (0x7fffc1fc, 0x7fffc530); (0x8000bc30, 0x8000bc88)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (DISJ : forall A n, 0 <= n -> 0x9e180 <= A -> A + n <= 0x9e440 -> disjoint_from [(bv_unsigned sp - 1024, bv_unsigned sp); (0x9e440, 0x9e448); (0x9f3b0, 0x9f3b8); (0x7fffc1a4, 0x7fffc1fc); (0x7fffc1fc, 0x7fffc530); (0x8000bc30, 0x8000bc88)]%Z A n).
  { intros A n Hn HA HB. cbn [disjoint_from fst snd]. repeat split; lia. }
  assert (RSF : rng RNG (bv_unsigned sp + -272) 272) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.
  sort_lits. move S0 at top. move S1 at top. move S2 at top. move S3 at top. move S4 at top. move S5 at top. move S6 at top. move S7 at top. move S8 at top. move S9 at top. move S10 at top. move S11 at top.
  carve_frame 16%nat ST.
  do 9 hstep.
  carve_frame 16%nat ST.
  do 3 hstep. astep. hstep. hstep. astep. do 2 hstep. astep. do 4 hstep.
  carve_frame 176%nat ST.
  do 14 hstep.
  do 5 hstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep.
  steps_to 0x400d0%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.
  hstep. hstep. astep.
  steps_to 0x401e4%Z.
  unpark D0 MU WM DISJ; unpark B0 MU WM DISJ. move D0 after REAL. move B0 after D0.
  assert (RX : rng RNG 0x7fffc1a4 4) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc1a4 4 0x7fffc1a8). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1a4.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e180; clear_at 0x9e190.
  unpark D1 MU WM DISJ; unpark B1 MU WM DISJ. move D1 after REAL. move B1 after D1.
  assert (RX : rng RNG 0x7fffc1a8 8) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc1a8 8 0x7fffc1b0). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1a8.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e1c0; clear_at 0x9e1d0.
  unpark D2 MU WM DISJ; unpark B2 MU WM DISJ. move D2 after REAL. move B2 after D2.
  assert (RX : rng RNG 0x7fffc1b0 4) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc1b0 4 0x7fffc1b4). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1b0.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e200; clear_at 0x9e210.
  unpark D3 MU WM DISJ; unpark B3 MU WM DISJ. move D3 after REAL. move B3 after D3.
  assert (RX : rng RNG 0x7fffc1b4 16) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc1b4 16 0x7fffc1c4). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1b4.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e240; clear_at 0x9e250.
  unpark D4 MU WM DISJ; unpark B4 MU WM DISJ. move D4 after REAL. move B4 after D4.
  assert (RX : rng RNG 0x7fffc1c4 16) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc1c4 16 0x7fffc1d4). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1c4.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e280; clear_at 0x9e290.
  unpark D5 MU WM DISJ; unpark B5 MU WM DISJ. move D5 after REAL. move B5 after D5.
  assert (RX : rng RNG 0x7fffc1d4 16) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc1d4 16 0x7fffc1e4). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1d4.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e2c0; clear_at 0x9e2d0.
  unpark D6 MU WM DISJ; unpark B6 MU WM DISJ. move D6 after REAL. move B6 after D6.
  assert (RX : rng RNG 0x7fffc1e4 8) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc1e4 8 0x7fffc1ec). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1e4.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e300; clear_at 0x9e310.
  unpark D7 MU WM DISJ; unpark B7 MU WM DISJ. move D7 after REAL. move B7 after D7.
  assert (RX : rng RNG 0x7fffc1ec 16) by (apply (rng_sub' _ _ _ _ _ RW2); lia).
  call (unreg_one_spec RNG 0x7fffc1ec 16 0x7fffc1fc). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1ec.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e340; clear_at 0x9e350.
  unpark D8 MU WM DISJ; unpark B8 MU WM DISJ. move D8 after REAL. move B8 after D8.
  assert (RX : rng RNG 0x7fffc1fc 160) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc1fc 160 0x7fffc29c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc1fc.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e380; clear_at 0x9e390.
  unpark D9 MU WM DISJ; unpark B9 MU WM DISJ. move D9 after REAL. move B9 after D9.
  assert (RX : rng RNG 0x7fffc29c 640) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc29c 640 0x7fffc51c). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc29c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e3c0; clear_at 0x9e3d0.
  unpark D10 MU WM DISJ; unpark B10 MU WM DISJ. move D10 after REAL. move B10 after D10.
  assert (RX : rng RNG 0x7fffc51c 20) by (apply (rng_sub' _ _ _ _ _ RW3); lia).
  call (unreg_one_spec RNG 0x7fffc51c 20 0x7fffc530). all: side RIMG RSTK KH. clear RX. clear_at 0x7fffc51c.
  lit_nat. hstep. hstep. astep. hstep. hstep. astep. clear_at 0x9e400; clear_at 0x9e410.
  steps_to 0x40400%Z. hstep.
  move RW4 at bottom.
  call_sp (poison_low_spec RNG 0x8000bc30 88). all: side RIMG RSTK KH. clear RW4.
  lit_nat.
  steps_to 0x40440%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.
  steps_to 0x40698%Z.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -32) end.
  hstep. hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16) end.
  hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  hstep.
  unfold module_dtor_post. sys_finish.
Qed.

Section Closed.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Definition aexit_spec_closed (FOE : funcs_on_exit_specA_stmt) :=
    aexit_spec get_so set_so mdtor_pre module_dtor_proof mdtor_pre_frame FOE
               (F_stdio_exit.stdio_exit_proof get_so set_so get_set set_set set_get).
End Closed.
End CANSEC3.
