(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition SHOFF : Z := 0x7fff8000.
Definition shd (a : Z) : Z := SHOFF + Z.shiftr a 3.
Definition shn (l : Z) : Z := Z.shiftr l 3.

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Lemma unsigned_lit8m : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_rt (m : mem) : Prop :=
     rw_cells bsegs m 0xcb980 [C8 (Z_to_bv 64 0x163da0)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcb990 [C8 (Z_to_bv 64 0x165e28); C8 (Z_to_bv 64 0xd1af8); C8 (Z_to_bv 64 0xd42f8);
                                C8 (Z_to_bv 64 0xd4fe8); C8 (Z_to_bv 64 0xd4ff0); C8 (Z_to_bv 64 0xd4fe0)]  (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcb9c0 [C8 (Z_to_bv 64 0xcd850)]                                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xcd848 [C8 (Z_to_bv 64 0xc4ccc); C8 (Z_to_bv 64 0xc50d0)]              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd42f8 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd4fd8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd3b5c [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x165ea0 [C8 (Z_to_bv 64 0xffffffffffffffff)]                                         (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd1b10 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0xcb980 \/ (0xcb9c8 <= lo /\ hi <= 0xcd848) \/ (0xcd858 <= lo /\ hi <= 0xd1b10) \/ (0xd1b14 <= lo /\ hi <= 0xd3b5c)
   \/ (0xd3b5d <= lo /\ hi <= 0xd42f8) \/ (0xd4300 <= lo /\ hi <= 0xd4fd8) \/ (0xd4fda <= lo /\ hi <= 0x165ea0) \/ 0x165ea8 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0xcb980 <= A /\ A + n <= 0xcb9c8) \/ (0xcd848 <= A /\ A + n <= 0xcd858) \/ (0xd1b10 <= A /\ A + n <= 0xd1b14)
              \/ (0xd3b5c <= A /\ A + n <= 0xd3b5d) \/ (0xd42f8 <= A /\ A + n <= 0xd4300) \/ (0xd4fd8 <= A /\ A + n <= 0xd4fda)
              \/ (0x165ea0 <= A /\ A + n <= 0x165ea8)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x629000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF bsegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x55e0c) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  unfold KHIGH in KH. pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x800cd000 /\ 0 < shn size).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  carve_frame 64%nat ST.
  do 8 hstep.                                          (* [comment removed for export] *)
  hstep. if_true.                                      (* [comment removed for export] *)
  zstep. hstep. if_cases K1; zify_cond K1.              (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 hstep.                                          (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K8; zify_cond K8.
  { exfalso. apply K8. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  do 2 zstep.                                          (* [comment removed for export] *)
  hstep. if_cases K9; zify_cond K9. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases K10; zify_cond K10; [exfalso; lia|]. (* [comment removed for export] *)
  do 5 zstep.                                          (* [comment removed for export] *)
  assert (E1 : Z.land (Z.shiftr (addr + size + -8) 3 + 1) 18446744073709551615 - Z.shiftr addr 3 = shn size).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
    rewrite Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr addr 3) with (shd addr).
  hstep. if_false.                                     (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases KT; zify_cond KT.                    (* [comment removed for export] *)
  2:{ exfalso. lia. }
  do 3 hstep. do 8 hstep.                              (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_one_post (spv d sb sl : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x41db0) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x165e28) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1b4e4) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xcd850) s8 (Z_to_bv 64 0xd1af8)
                  (Z_to_bv 64 0xd42f8) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41db0) fc None m' (seg_rom bsegs)
    /\ munch [(sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma unreg_one_spec : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv bsegs m -> mdtor_rt m ->
  rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 swr)] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 4096 -> 0x10000 <= beg -> beg + swr <= 0x629000 ->
  0x10000 <= d -> d + 64 <= 0x629000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF bsegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x165e28) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b4e4) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xcd850) s8 (Z_to_bv 64 0xd1af8)
             (Z_to_bv 64 0xd42f8) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41dc8) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 512).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  do 7 hstep.
  hstep. if_false.                                     (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  hstep. if_true.                                      (* [comment removed for export] *)
  hstep. if_false.                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 2 hstep. do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K3; zify_cond K3.
  { exfalso. apply K3. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  hstep. zstep. rewrite (unsigned_lit8m swr). hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear - SL. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  do 6 hstep. hstep. if_false.
  (* [comment removed for export] *)
  do 3 hstep. do 5 zstep. hstep. do 3 zstep.
  assert (E1 : Z.land (2147450880 + Z.shiftr (beg + swr + -8) 3 + 1) 18446744073709551615 - Z.land (2147450880 + Z.shiftr beg 3) 18446744073709551615
               = shn swr).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. change 18446744073709551615 with (Z.ones 64).
    rewrite !Z.land_ones by lia. change (2 ^ 64) with 18446744073709551616. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr beg 3) with (shd beg).
  hstep. if_cases KT; zify_cond KT. 2:{ exfalso. lia. }  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold unreg_one_post. destruct_exs PO.
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  cbn [ret_pc reg_get].
  replace (ret_pc (Z_to_bv 64 0x41db0)) with (Z_to_bv 64 0x41db0 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gdesc (m : mem) (d beg sz swr nm md odr : Z) : Prop :=
     rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 swr)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AGLOBALS : list (Z * Z * Z * Z * Z) := [
  (0x21100, 36, 96, 0x1c2ce, 0x21160);
  (0x211a0, 7, 32, 0x2084a, 0x21160);
  (0x211c0, 1, 32, 0x1482e, 0x21160);
  (0x211e0, 29, 64, 0x137a6, 0x21160);
  (0x21220, 54, 96, 0x1d282, 0x21160);
  (0x21280, 128, 160, 0x1cbfc, 0x21680);
  (0x21320, 32, 64, 0x12412, 0x21680);
  (0x21360, 212, 256, 0x2034a, 0x21680);
  (0x21460, 53, 96, 0x1f2c5, 0x21680);
  (0x214c0, 144, 192, 0x10b1d, 0x21680);
  (0x21580, 36, 96, 0x1cc04, 0x21680);
  (0x215e0, 12, 32, 0x13d86, 0x21680);
  (0x21600, 32, 64, 0x158e9, 0x21680);
  (0x21640, 32, 64, 0x15f99, 0x21680);
  (0x216e0, 144, 192, 0x10b1d, 0x22220);
  (0x217a0, 36, 96, 0x1cc04, 0x22220);
  (0x21800, 520, 672, 0x1fb50, 0x22220);
  (0x21aa0, 128, 160, 0x1cbfc, 0x22220);
  (0x21b40, 32, 64, 0x12412, 0x22220);
  (0x21b80, 264, 352, 0x20352, 0x22220);
  (0x21ce0, 212, 256, 0x2034a, 0x22220);
  (0x21de0, 53, 96, 0x1f2c5, 0x22220);
  (0x21e40, 520, 672, 0x1899f, 0x22220);
  (0x220e0, 128, 160, 0x17773, 0x22220);
  (0x22180, 8, 32, 0x14835, 0x22220);
  (0x221a0, 32, 64, 0x1e01a, 0x22220);
  (0x221e0, 32, 64, 0x18f6a, 0x22220);
  (0x22300, 256, 320, 0x1a07d, 0x22460);
  (0x22440, 8, 32, 0x14835, 0x22460);
  (0x224e0, 128, 160, 0x17773, 0x225a0);
  (0x22580, 8, 32, 0x14835, 0x225a0);
  (0x22620, 36, 96, 0x1c2ce, 0x225dc);
  (0x22680, 13, 32, 0x1eaaf, 0x225dc);
  (0x226a0, 1, 32, 0x2084a, 0x225dc);
  (0x226c0, 36, 96, 0x1c2ce, 0x22720);
  (0x22760, 6, 32, 0x2084a, 0x22720);
  (0x22780, 1, 32, 0x1482e, 0x22720);
  (0x606980, 8, 32, 0x1bb38, 0x21160)]%Z.
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint gdescs (m : mem) (d : Z) (G : list (Z * Z * Z * Z * Z)) : Prop :=
  match G with
  | [] => True
  | (b, sz, swr, nm, md) :: G' => gdesc m d b sz swr nm md (2^64 - 1) /\ gdescs m (d + 64) G'
  end.

(* [comment removed for export] *)
Fixpoint gsorted (lo hi : Z) (G : list (Z * Z * Z * Z * Z)) : Prop :=
  match G with
  | [] => True
  | (b, sz, swr, nm, md) :: G' =>
      lo <= shd b /\ shd b + shn swr <= hi /\ b mod 8 = 0 /\ swr mod 8 = 0 /\ 0 < swr < 4096 /\ 0x10000 <= b /\ b + swr <= 0x629000
      /\ gsorted (shd b + shn swr) hi G'
  end.

(* [comment removed for export] *)
Fixpoint gshads (m : mem) (G : list (Z * Z * Z * Z * Z)) : Prop :=
  match G with
  | [] => True
  | (b, sz, swr, nm, md) :: G' => (exists j, rw_cells bsegs m (shd b) [CB (Z.to_nat (shn swr)) j]) /\ gshads m G'
  end.

Fixpoint gsortedb (lo hi : Z) (G : list (Z * Z * Z * Z * Z)) : bool :=
  match G with
  | [] => true
  | (b, sz, swr, nm, md) :: G' =>
      (lo <=? shd b) && (shd b + shn swr <=? hi) && (b mod 8 =? 0) && (swr mod 8 =? 0) && (0 <? swr) && (swr <? 4096)
      && (0x10000 <=? b) && (b + swr <=? 0x629000) && gsortedb (shd b + shn swr) hi G'
  end.

Lemma gsortedb_ok : forall G lo hi, gsortedb lo hi G = true -> gsorted lo hi G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros lo hi H; cbn [gsortedb gsorted] in *; [exact I|].
  repeat rewrite andb_true_iff in H. destruct H as [[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9].
  apply Z.leb_le in H1, H2, H7, H8. apply Z.eqb_eq in H3, H4. apply Z.ltb_lt in H5, H6.
  repeat split; try assumption; try lia. apply IH. exact H9.
Qed.

(* [comment removed for export] *)
Fixpoint ghull (W : list (Z * Z)) (G : list (Z * Z * Z * Z * Z)) : Prop :=
  match G with
  | [] => True
  | (b, sz, swr, nm, md) :: G' => (exists iv, In iv W /\ fst iv <= shd b /\ shd b + shn swr <= snd iv) /\ ghull W G'
  end.
Fixpoint ghullb (W : list (Z * Z)) (G : list (Z * Z * Z * Z * Z)) : bool :=
  match G with
  | [] => true
  | (b, sz, swr, nm, md) :: G' => existsb (fun iv => (fst iv <=? shd b) && (shd b + shn swr <=? snd iv)) W && ghullb W G'
  end.
Lemma ghullb_ok : forall W G, ghullb W G = true -> ghull W G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros H; cbn [ghullb ghull] in *; [exact I|].
  apply andb_true_iff in H. destruct H as [H1 H2]. split; [| apply IH; exact H2].
  apply existsb_exists in H1. destruct H1 as (iv & IN & H1). apply andb_true_iff in H1. destruct H1 as [A B].
  apply Z.leb_le in A, B. exists iv. split; [exact IN|]. split; assumption.
Qed.
Lemma outside_In : forall (W : list (Z * Z)) x iv, outside W x -> In iv W -> ~ (fst iv <= x < snd iv).
Proof.
  induction W as [|[lo0 hi0] W IH]; intros x iv HO IN; [destruct IN|]. cbn [outside] in HO. destruct HO as [H1 H2].
  destruct IN as [<- | IN]; [exact H1| apply IH; assumption].
Qed.
Lemma munch_in_W : forall (W : list (Z * Z)) iv a b m m', munch [(a, b)] m m' -> In iv W -> fst iv <= a -> b <= snd iv -> munch W m m'.
Proof.
  intros W iv a b m m' MU IN L H x HO. apply MU. cbn [outside]. split; [| exact I].
  pose proof (outside_In W _ iv HO IN). lia.
Qed.
Lemma AGLOBALS_hull : ghull [(0x7fffc220, 0x7fffc4f4); (0x800b8d30, 0x800b8d34)] AGLOBALS.
Proof. apply ghullb_ok. vm_compute. reflexivity. Qed.

Lemma AGLOBALS_sorted : gsorted 0x7fffc220 0x800b8d34 AGLOBALS.
Proof. apply gsortedb_ok. vm_compute. reflexivity. Qed.

Lemma AGLOBALS_length : Z.of_nat (length AGLOBALS) = 38.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cb_sub : forall m a (k : nat) j a' n', rw_cells bsegs m a [CB k j] -> a <= a' -> 0 <= n' -> a' + n' <= a + Z.of_nat k ->
  exists j', rw_cells bsegs m a' [CB (Z.to_nat n') j'].
Proof.
  intros m a k j a' n' [[WF [A0 [AL BY]]] [W0 [W1 W]]] H1 H2 H3.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize] in *. destruct WF as [LJ _]. rewrite app_nil_r in *. rewrite Nat.add_0_r in *.
  exists (firstn (Z.to_nat n') (skipn (Z.to_nat (a' - a)) j)).
  assert (LEN : length (firstn (Z.to_nat n') (skipn (Z.to_nat (a' - a)) j)) = Z.to_nat n').
  { rewrite length_firstn, length_skipn. lia. }
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact LEN| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite LEN; lia|].
    intros i Hi. rewrite LEN in Hi.
    rewrite nth_error_firstn. replace (Nat.ltb i (Z.to_nat n')) with true by (symmetry; apply Nat.ltb_lt; exact Hi). rewrite nth_error_skipn.
    replace (a' + Z.of_nat i) with (a + Z.of_nat (Z.to_nat (a' - a) + i)) by lia. apply BY. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
    replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
Qed.

Lemma gshads_of_hull : forall G lo hi m a (k : nat) j, rw_cells bsegs m a [CB k j] -> a <= lo -> hi <= a + Z.of_nat k ->
  gsorted lo hi G -> gshads m G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros lo hi m a k j C H1 H2 S; cbn [gshads gsorted] in *; [exact I|].
  destruct S as (L1 & L2 & _ & _ & SW & _ & _ & S).
  assert (N0 : 0 <= shn swr) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  split.
  - eapply cb_sub; [exact C| lia| exact N0| lia].
  - eapply IH; [exact C| | exact H2| exact S]. lia.
Qed.

Lemma gshads_of_hull2 : forall G lo hi m a1 (k1 : nat) j1 a2 (k2 : nat) j2,
  rw_cells bsegs m a1 [CB k1 j1] -> rw_cells bsegs m a2 [CB k2 j2] ->
  gsorted lo hi G -> ghull [(a1, a1 + Z.of_nat k1); (a2, a2 + Z.of_nat k2)] G -> gshads m G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros lo hi m a1 k1 j1 a2 k2 j2 C1 C2 S H; cbn [gshads gsorted ghull] in *; [exact I|].
  destruct S as (L1 & L2 & _ & _ & SW & _ & _ & S). destruct H as [(iv & IN & LO & HI) H].
  assert (N0 : 0 <= shn swr) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  split.
  - destruct IN as [<- | [<- | []]]; cbn [fst snd] in LO, HI;
      [eapply cb_sub; [exact C1| lia| exact N0| lia] | eapply cb_sub; [exact C2| lia| exact N0| lia]].
  - eapply IH; [exact C1| exact C2| exact S| exact H].
Qed.

Lemma gdescs_transport : forall G W m m' d, gdescs m d G -> munch W m m' -> wmono bsegs m m' ->
  (forall A n, d <= A -> 0 <= n -> A + n <= d + 64 * Z.of_nat (length G) -> disjoint_from W A n) -> gdescs m' d G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros W m m' d HG MU WM HD; cbn [gdescs length] in *; [exact I|].
  destruct HG as [[D1 D2] HG]. split; [split|].
  - eapply rw_cells_transport; [exact D1| exact MU| exact WM| apply HD; cbn [cells_size csize Nat.add]; lia].
  - eapply rw_cells_transport; [exact D2| exact MU| exact WM| apply HD; cbn [cells_size csize Nat.add]; lia].
  - eapply IH; [exact HG| exact MU| exact WM|]. intros A n H1 H2 H3. apply HD; lia.
Qed.

Lemma gshads_transport : forall G W m m' lo hi, gshads m G -> gsorted lo hi G -> munch W m m' -> wmono bsegs m m' ->
  (forall A n, lo <= A -> 0 <= n -> A + n <= hi -> disjoint_from W A n) -> gshads m' G.
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros W m m' lo hi HG S MU WM HD; cbn [gshads gsorted] in *; [exact I|].
  destruct HG as [[j C] HG]. destruct S as (L1 & L2 & _ & _ & SW & _ & _ & S).
  assert (N0 : 0 <= shn swr) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  split.
  - exists j. eapply rw_cells_transport; [exact C| exact MU| exact WM|]. apply HD; [lia| lia|]. cbn [cells_size csize].
    rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
  - eapply IH; [exact HG| exact S| exact MU| exact WM|]. intros A n H1 H2 H3. apply HD; [lia| lia| exact H3].
Qed.

(* [comment removed for export] *)
Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells bsegs m 0xcc658 [C8 (Z_to_bv 64 0xd02a0); C8 (Z_to_bv 64 0xd0c20)]     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd0c40 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xd1bb0 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ gdescs m 0xd02a0 AGLOBALS                                                        (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x7fffc220 [CB 724 j])          (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x800b8d30 [CB 4 j])            (* [comment removed for export] *)
  /\ (exists j, rw_cells bsegs m 0x80012054 [CB 304 j]).         (* [comment removed for export] *)

Lemma mdtor_pre_frame : forall sp m m',
  mdtor_pre m -> KHIGH <= sp - 48 - MDTOR_DEPTH -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> mdtor_pre m'.
Proof.
  intros sp m m' P KH MU WM. unfold KHIGH, MDTOR_DEPTH in KH.
  assert (D : forall A n, 0 <= n -> A + n <= 0x800cd000 -> 0x627524 <= A \/ (0xd0c91 <= A /\ A + n <= 0x627300) \/ A + n <= 0xd0c90 ->
              disjoint_from (AEXIT_W1 sp) A n).
  { intros A n Hn HA HO. unfold AEXIT_W1, MDTOR_DEPTH. cbn. lia. }
  unfold mdtor_pre in *.
  destruct P as (RT & G1 & G2 & G3 & GD & [j1 S1] & [j1b S1b] & [j2 S2]).
  assert (RT' : mdtor_rt m').
  { eapply mdtor_rt_frame; [exact RT | exact MU | exact WM | ]. unfold AEXIT_W1, MDTOR_DEPTH.
    repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
  refine (conj RT' _).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - eapply rw_cells_transport; [exact G1 | exact MU | exact WM | apply D; cbn; lia].
  - eapply rw_cells_transport; [exact G2 | exact MU | exact WM | apply D; cbn; lia].
  - eapply rw_cells_transport; [exact G3 | exact MU | exact WM | apply D; cbn; lia].
  - eapply gdescs_transport; [exact GD | exact MU | exact WM |]. rewrite AGLOBALS_length. intros A n H1 H2 H3. apply D; lia.
  - exists j1. eapply rw_cells_transport; [exact S1 | exact MU | exact WM | apply D; cbn; lia].
  - exists j1b. eapply rw_cells_transport; [exact S1b | exact MU | exact WM | apply D; cbn; lia].
  - exists j2. eapply rw_cells_transport; [exact S2 | exact MU | exact WM | apply D; cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC2.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac rt_split := unfold mdtor_rt; repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Ltac lit_nat := repeat match goal with H : rw_cells _ _ _ [CB (Z.to_nat (Zpos ?p)) _] |- _ =>
                  let v := eval vm_compute in (Z.to_nat (Zpos p)) in change (Z.to_nat (Zpos p)) with v in H; move H at top end.
Ltac lit_addr := repeat match goal with H : rw_cells _ _ (Zpos ?a + Zpos ?b) _ |- _ =>
                  let v := eval vm_compute in (Zpos a + Zpos b) in change (Zpos a + Zpos b) with v in H end.
Ltac lit_rng := repeat match goal with H : rng _ _ (Zpos ?a - Zpos ?b) |- _ =>
                  let v := eval vm_compute in (Zpos a - Zpos b) in change (Zpos a - Zpos b) with v in H end.
(* [comment removed for export] *)
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hstepS := sort_lits; zstep; fix_lit_store.
Ltac astepS := hstepS; try (first [if_true | if_false]).

Section CANSEC2b. Context {rc : runConstT}.
Lemma munch_hull : forall lo hi a b m m', munch [(a, b)] m m' -> lo <= a -> b <= hi -> munch [(lo, hi)] m m'.
Proof.
  intros lo hi a b m m' M H1 H2. eapply munch_weaken; [| exact M]. unfold sub_fp. intros x Hx. cbn [outside] in *.
  destruct Hx as [Hx _]. split; [lia| exact I].
Qed.

Lemma munch_hull2 : forall lo hi a b m m1 m', munch [(lo, a)] m m1 -> munch [(b, hi)] m1 m' -> lo <= b -> a <= hi -> munch [(lo, hi)] m m'.
Proof.
  intros lo hi a b m m1 m' M1 M2 H H'. eapply munch_trans; [eapply munch_weaken; [| exact M1] | eapply munch_weaken; [| exact M2]];
    unfold sub_fp; intros x Hx; cbn [outside] in *; destruct Hx as [Hx _]; split; try exact I; lia.
Qed.

Lemma unreg_loop : forall G RNG (W : list (Z * Z)) (lo hi d spv : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  G <> [] ->
  mem_inv bsegs m -> mdtor_rt m -> gdescs m d G -> gshads m G -> gsorted lo hi G -> ghull W G ->
  0x10000 <= d -> d + 64 * Z.of_nat (length G) <= 0x629000 -> 0x7fffa000 <= lo -> hi <= 0x800cd000 -> 0 <= spv < 2^64 ->
  rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) W ->
  evtF bsegs RNG (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR ra' (Z_to_bv 64 spv) gp tp t0' t1' t2' s0' (Z_to_bv 64 0x165e28) a0' a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 2) (Z_to_bv 64 0x1b4e4) (Z_to_bv 64 (d + 64 * Z.of_nat (length G))) s5 s6 (Z_to_bv 64 0xcd850) s8
                    (Z_to_bv 64 0xd1af8) (Z_to_bv 64 0xd42f8) (Z_to_bv 64 0) t3' t4' t5' t6')
               F (Z_to_bv 64 0x41fcc) fc None m' (seg_rom bsegs)
      /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x165e28) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b4e4) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xcd850) s8 (Z_to_bv 64 0xd1af8)
             (Z_to_bv 64 0xd42f8) (Z_to_bv 64 (Z.of_nat (length G))) t3 t4 t5 t6)
        F (Z_to_bv 64 0x41dc8) fc None m (seg_rom bsegs)).
Proof.
  induction G as [|[[[[b sz] swr] nm] md] G IH]; intros until m; intros NE MI RT HD HS HSO HHU D0 D1 LO HI SPV RIMG RH; [congruence|].
  clear NE. cbn [gdescs gshads length] in *. pose proof HSO as HSO'. cbn [gsorted] in HSO'.
  cbn [ghull] in HHU. destruct HHU as [(iv & IVIN & IVLO & IVHI) HHU].
  destruct HD as [[DC DB] HD]. destruct HS as [[j SH] HS]. destruct HSO' as (L1 & L2 & AL & SL & SW & BL & BH & HSO').
  rewrite Nat2Z.inj_succ in D1 |- *.
  pose proof (Zle_0_nat (length G)) as LG.
  assert (N0 : 0 < shn swr < 512) by (unfold shn; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (SB : 0x7fffa000 <= shd b) by lia.
  assert (RX : rng RNG (shd b) (shn swr)) by (eapply rng_sub'; [exact (proj1 (Forall_forall _ _) RH iv IVIN)| lia]).
  change (2^64 - 1) with 18446744073709551615 in DC.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (unreg_one_spec RNG (shd b) (shn swr)); first [exact MI | exact RT | exact DC | exact DB | exact SH | exact RIMG | exact RX
                                                        | reflexivity | lia]. }
  intros ms1 PO1. unfold unreg_one_post in PO1.
  destruct PO1 as (t0' & t1' & t2' & s0' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & _).
  (* [comment removed for export] *)
  assert (DJ : forall A n, 0 <= n -> A + n <= 0x629000 -> disjoint_from [(shd b, shd b + shn swr)] A n).
  { intros A n Hn HA. cbn [disjoint_from]. split; [left; lia| exact I]. }
  pose proof (rw_cells_transport bsegs _ _ _ _ _ DC MU1 WM1 ltac:(apply DJ; cbn [cells_size csize Nat.add]; lia)) as DC1.
  assert (RT1 : mdtor_rt m1).
  { eapply mdtor_rt_frame; [exact RT| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil]. cbn [rt_clear]. lia. }
  assert (HD1 : gdescs m1 (d + 64) G).
  { eapply gdescs_transport; [exact HD| exact MU1| exact WM1|]. intros A n H1 H2 H3. apply DJ; lia. }
  assert (HS1 : gshads m1 G).
  { eapply gshads_transport; [exact HS| exact HSO'| exact MU1| exact WM1|]. intros A n H1 H2 H3. cbn [disjoint_from]. split; [right; lia| exact I]. }
  clear DC DB SH HD HS RT MI.
  pose proof RT1 as RT1'. destruct RT1' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  (* [comment removed for export] *)
  hstepS. hstepS. astepS. hstepS. hstepS. hstepS.
  if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    destruct G as [|g G]; [| cbn [length] in K; rewrite Nat2Z.inj_succ in K; lia].
    apply evtF_done. cbn [length]. do 18 eexists.
    split; [reflexivity|].
    split; [eapply (munch_in_W W iv); [exact MU1| exact IVIN| lia| lia]|]. split; [exact WM1| exact MI1].
  - (* [comment removed for export] *)
    destruct G as [|g G]; [cbn [length] in K; lia|].
    set (G' := g :: G) in *.
    (* [comment removed for export] *)
    match goal with |- context [Z_to_bv 64 (Z.succ (Z.of_nat (length G')) + ?c)] =>
      replace (Z_to_bv 64 (Z.succ (Z.of_nat (length G')) + c)) with (Z_to_bv 64 (Z.of_nat (length G'))) by (f_equal; lia) end.
    eapply evtF_mono.
    { eapply (IH RNG W (shd b + shn swr) hi (d + 64)); first [ discriminate | exact MI1 | exact RT1 | exact HD1 | exact HS1 | exact HSO'
                                                          | exact HHU | exact RIMG | exact RH | lia ]. }
    cbv beta. intros ms' (ra' & t0'' & t1'' & t2'' & s0'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m' & -> & MU2 & WM2 & MI2).
    exists ra', t0'', t1'', t2'', s0'', a0'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m'.
    split; [ match goal with |- context [Z_to_bv 64 (d + 64 * Z.succ (Z.of_nat (length G')))] =>
               replace (d + 64 * Z.succ (Z.of_nat (length G'))) with (d + 64 + 64 * Z.of_nat (length G')) by lia end;
             reflexivity |].
    split; [eapply munch_trans; [eapply (munch_in_W W iv); [exact MU1| exact IVIN| lia| lia] | exact MU2]|].
    split; [eapply wmono_trans; [exact WM1| exact WM2]| exact MI2].
Qed.
End CANSEC2b.

(* [comment removed for export] *)
Ltac hstep ::= zstep; fix_lit_store.

Section CANSEC3. Context {rc : runConstT}.
Theorem module_dtor_proof : module_dtor_stmt mdtor_pre.
Proof.
  unfold module_dtor_stmt. intros until lo. intros HPRE ST LO KH MI RSTK RIMG RW.
  pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold mdtor_pre in P.
  destruct P as (RT & GSS & FLG & MTX & GD & [j1 S1] & [j1b S1b] & [j2 S2]).
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  (* [comment removed for export] *)
  unfold MDTOR_W in RW.
  assert (RWH : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) [(0x7fffc220, 0x7fffc4f4); (0x800b8d30, 0x800b8d34)])
    by (inversion RW as [|? ? _ R1]; inversion R1 as [|? ? _ R2]; inversion R2 as [|? ? A3 R3]; inversion R3 as [|? ? A4 _];
        constructor; [exact A3| constructor; [exact A4| constructor]]).
  repeat lazymatch type of RW with Forall _ (_ :: _) =>
    let H := fresh "RW" in pose proof (Forall_inv RW) as H; cbn [fst snd] in H; apply Forall_inv_tail in RW end.
  lit_rng.
  pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0xd0c40, 0xd0c48); (0xd1bb0, 0xd1bb8);
              (0x7fffc220, 0x7fffc4f4); (0x800b8d30, 0x800b8d34); (0x80012054, 0x80012184)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  assert (RSF : rng RNG (bv_unsigned sp + -272) 272) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.
  sort_lits. move S1 at top. move S1b at top. move S2 at top.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 9 hstep.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 hstep. astep. hstep. hstep. astep. do 2 hstep. astep. do 4 hstep.
  (* [comment removed for export] *)
  carve_frame 176%nat ST.
  do 14 hstep.
  do 5 hstep.                                          (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  steps_to 0x41cb4%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  hstep. hstep. astep.
  steps_to 0x41dc8%Z.
  (* [comment removed for export] *)
  lazymatch goal with M : munch _ m ?mc, W : wmono _ m ?mc |- _ =>
    assert (GD' : gdescs mc 0xd02a0 AGLOBALS)
      by (eapply gdescs_transport; [exact GD| exact M| exact W| rewrite AGLOBALS_length; intros A n H1 H2 H3; cbn [disjoint_from]; lia]) end.
  assert (HS : gshads _ AGLOBALS) by (eapply (gshads_of_hull2 AGLOBALS 0x7fffc220 0x800b8d34); [exact S1| exact S1b| exact AGLOBALS_sorted| exact AGLOBALS_hull]).
  replace (Z_to_bv 64 38) with (Z_to_bv 64 (Z.of_nat (length AGLOBALS))) by reflexivity.
  move RW2 at bottom. move RW3 at bottom.
  call (unreg_loop AGLOBALS RNG [(0x7fffc220, 0x7fffc4f4); (0x800b8d30, 0x800b8d34)] 0x7fffc220 0x800b8d34 0xd02a0).
  all: first [ unfold AGLOBALS; discriminate | exact GD' | exact HS | exact AGLOBALS_sorted | exact AGLOBALS_hull | exact RWH | rewrite AGLOBALS_length; lia | side RIMG RSTK KH ].
  clear RW2 RW3 RWH GD GD' HS.
  rewrite AGLOBALS_length.
  (* [comment removed for export] *)
  do 6 hstep. hstep.
  move RW4 at bottom.
  call_sp (poison_low_spec RNG 0x80012054 304). all: side RIMG RSTK KH. clear RW4.
  lit_nat.
  (* [comment removed for export] *)
  steps_to 0x42024%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.                                               (* [comment removed for export] *)
  steps_to 0x4227c%Z.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -32) end.
  hstep. hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16) end.
  hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  hstep.
  unfold module_dtor_post. sys_finish.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Closed.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Definition aexit_spec_closed :=
    aexit_spec get_so set_so mdtor_pre module_dtor_proof mdtor_pre_frame
               (F_stdio_exit.stdio_exit_proof get_so set_so get_set set_set set_get).
End Closed.
End CANSEC3.