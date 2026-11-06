(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF F_memset.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
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
  repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
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
     rw_cells asegs m 0xd14f8 [C8 (Z_to_bv 64 0x169560)]
  /\ rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8); C8 (Z_to_bv 64 0xd72b8); C8 (Z_to_bv 64 0xd9ab8);
                                C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a0)]
  /\ rw_cells asegs m 0xd1538 [C8 (Z_to_bv 64 0xd3428)]
  /\ rw_cells asegs m 0xd3420 [C8 (Z_to_bv 64 0xc74a0); C8 (Z_to_bv 64 0xc78a4)]
  /\ rw_cells asegs m 0xd9ab8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xda798 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xd931c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x16b660 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ rw_cells asegs m 0xd72d0 [C4 (Z_to_bv 64 1)].

Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0xd14f8 \/ (0xd1540 <= lo /\ hi <= 0xd3420) \/ (0xd3430 <= lo /\ hi <= 0xd72d0) \/ (0xd72d4 <= lo /\ hi <= 0xd931c)
   \/ (0xd931d <= lo /\ hi <= 0xd9ab8) \/ (0xd9ac0 <= lo /\ hi <= 0xda798) \/ (0xda79a <= lo /\ hi <= 0x16b660) \/ 0x16b668 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono asegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0xd14f8 <= A /\ A + n <= 0xd1540) \/ (0xd3420 <= A /\ A + n <= 0xd3430) \/ (0xd72d0 <= A /\ A + n <= 0xd72d4)
              \/ (0xd931c <= A /\ A + n <= 0xd931d) \/ (0xd9ab8 <= A /\ A + n <= 0xd9ac0) \/ (0xda798 <= A /\ A + n <= 0xda79a)
              \/ (0x16b660 <= A /\ A + n <= 0x16b668)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

Definition poison_low_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sb sl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sb, sb + sl)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma poison_low_spec : forall RNG (sb sl : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (addr size lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> KHIGH <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  mdtor_rt m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x62f000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells asegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF asegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5f738) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  unfold KHIGH in KH. pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
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
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR'.
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST'.
  eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end. exact FR'.
Qed.

Definition unreg_one_post (spv d sb sl : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x4afe4) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x16b5e8) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1c69e) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xd3428) s8 (Z_to_bv 64 0xd72b8)
                  (Z_to_bv 64 0xd9ab8) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x4afe4) fc None m' (seg_rom asegs)
    /\ munch [(sb, sb + sl)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma unreg_one_spec : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv asegs m -> mdtor_rt m ->
  rw_cells asegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells asegs m (d + 16) [C1 (Z_to_bv 8 swr)] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 256 -> 0x10000 <= beg -> beg + swr <= 0x62f000 ->
  0x10000 <= d -> d + 64 <= 0x62f000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells asegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF asegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x16b5e8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1c69e) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xd3428) s8 (Z_to_bv 64 0xd72b8)
             (Z_to_bv 64 0xd9ab8) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4affc) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 32).
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
  hstep. zstep. rewrite (unsigned_lit8 swr) by lia. hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }

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
  replace (ret_pc (Z_to_bv 64 0x4afe4)) with (Z_to_bv 64 0x4afe4 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed.

Definition gdesc (m : mem) (d beg sz swr nm md odr : Z) : Prop :=
     rw_cells asegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells asegs m (d + 16) [C1 (Z_to_bv 8 swr)].

Definition unregg_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells asegs m 0xd7370 [C8 (Z_to_bv 64 0)]
  /\ gdesc m 0xd5e90 0x22c60 0x7 0x20 0x1d5fc 0x23360 (2^64 - 1)
  /\ gdesc m 0xd5ed0 0x22c80 0x13 0x40 0x200f6 0x23360 (2^64 - 1)
  /\ gdesc m 0xd5f10 0x22d00 0xb 0x20 0x22280 0x23360 (2^64 - 1)
  /\ gdesc m 0xd5f50 0x22d20 0x43 0x80 0x14d08 0x23360 (2^64 - 1)
  /\ gdesc m 0xd5f90 0x22da0 0x8 0x20 0x10b15 0x23360 (2^64 - 1)
  /\ gdesc m 0xd5fd0 0x22dc0 0x70 0xa0 0x13b21 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6010 0x22e60 0xf 0x20 0x13b8f 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6050 0x22e80 0x53 0x80 0x1e6cf 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6090 0x22f00 0xa 0x20 0x16fce 0x23360 (2^64 - 1)
  /\ gdesc m 0xd60d0 0x22f20 0x12 0x40 0x19749 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6110 0x22fa0 0x14 0x40 0x17013 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6150 0x23020 0x14 0x40 0x21450 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6190 0x230a0 0x12 0x40 0x1b127 0x23360 (2^64 - 1)
  /\ gdesc m 0xd61d0 0x23120 0xc 0x20 0x21458 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6210 0x23160 0xa 0x20 0x14d0f 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6250 0x23180 0x12 0x40 0x1f61b 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6290 0x23200 0xa 0x20 0x19e64 0x23360 (2^64 - 1)
  /\ gdesc m 0xd62d0 0x23220 0x12 0x40 0x1d601 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6310 0x232a0 0x10 0x20 0x1a923 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6350 0x232c0 0x45 0x80 0x1cd55 0x23360 (2^64 - 1)
  /\ gdesc m 0xd6390 0x23340 0x6 0x20 0x20aa7 0x23360 (2^64 - 1)
  /\ (exists j, rw_cells asegs m 0x7fffc58c [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc590 [CB 8 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5a0 [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5a4 [CB 16 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5b4 [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5b8 [CB 20 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5cc [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5d0 [CB 16 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5e0 [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5e4 [CB 8 j])
  /\ (exists j, rw_cells asegs m 0x7fffc5f4 [CB 8 j])
  /\ (exists j, rw_cells asegs m 0x7fffc604 [CB 8 j])
  /\ (exists j, rw_cells asegs m 0x7fffc614 [CB 8 j])
  /\ (exists j, rw_cells asegs m 0x7fffc624 [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc62c [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc630 [CB 8 j])
  /\ (exists j, rw_cells asegs m 0x7fffc640 [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc644 [CB 8 j])
  /\ (exists j, rw_cells asegs m 0x7fffc654 [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x7fffc658 [CB 16 j])
  /\ (exists j, rw_cells asegs m 0x7fffc668 [CB 4 j])
  /\ (exists j, rw_cells asegs m 0x80012bd2 [CB 168 j]).

Definition MDTOR_DEPTH : Z := 1024.
Definition MDTOR_W : list (Z * Z) := [(0xd7370, 0xd7378); (0x7fffc58c, 0x7fffc66c); (0x80012bd2, 0x80012c80)]%Z.

Definition unregg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (0xd7370, 0xd7378); (0x7fffc58c, 0x7fffc66c); (0x80012bd2, 0x80012c80)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xd7370 [C8 (Z_to_bv 64 0)]

    /\ rw_cells asegs m' 0x7fffc58c [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc590 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x7fffc5a0 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc5a4 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' 0x7fffc5b4 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc5b8 [CB 20 (repeat (Z_to_bv 8 0) 20)]
    /\ rw_cells asegs m' 0x7fffc5cc [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc5d0 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' 0x7fffc5e0 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc5e4 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x7fffc5f4 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x7fffc604 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x7fffc614 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x7fffc624 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc62c [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc630 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x7fffc640 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc644 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells asegs m' 0x7fffc654 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x7fffc658 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells asegs m' 0x7fffc668 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells asegs m' 0x80012bd2 [CB 168 (repeat (Z_to_bv 8 0) 168)].

Definition unregg_stmt (PRE : mem -> Prop) : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (KHIGH <= lo) ->
    mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    a0 = Z_to_bv 64 0xd5e90 -> a1 = Z_to_bv 64 21 ->
    evtF asegs RNG (unregg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x4ae40) fc None m (seg_rom asegs)).

End CANSEC2.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

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

Section CANSEC3. Context {rc : runConstT}.
Theorem unregg_proof : unregg_stmt unregg_pre.
Proof.
  unfold unregg_stmt. intros until lo. intros HPRE ST LO KH MI RSTK RIMG RW -> ->.
  pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold unregg_pre, gdesc in P.
  destruct P as (RT & MTX & (D0 & B0) & (D1 & B1) & (D2 & B2) & (D3 & B3) & (D4 & B4) & (D5 & B5) & (D6 & B6) & (D7 & B7) & (D8 & B8) & (D9 & B9) & (D10 & B10) & (D11 & B11) & (D12 & B12) & (D13 & B13) & (D14 & B14) & (D15 & B15) & (D16 & B16) & (D17 & B17) & (D18 & B18) & (D19 & B19) & (D20 & B20) & [j0 S0] & [j1 S1] & [j2 S2] & [j3 S3] & [j4 S4] & [j5 S5] & [j6 S6] & [j7 S7] & [j8 S8] & [j9 S9] & [j10 S10] & [j11 S11] & [j12 S12] & [j13 S13] & [j14 S14] & [j15 S15] & [j16 S16] & [j17 S17] & [j18 S18] & [j19 S19] & [j20 S20] & [jA SA]).
  lit_addr.
  change (2^64 - 1) with 18446744073709551615 in D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).

  unfold MDTOR_W in RW.
  repeat lazymatch type of RW with Forall _ (_ :: _) =>
    let H := fresh "RW" in pose proof (Forall_inv RW) as H; cbn [fst snd] in H; apply Forall_inv_tail in RW end.
  lit_rng.
  pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0xd7370, 0xd7378); (0x7fffc58c, 0x7fffc66c); (0x80012bd2, 0x80012c80)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RSF : rng RNG (bv_unsigned sp + -240) 240) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.

  move PGC at bottom. move GOT at bottom. move GOT80 at bottom. move REAL at bottom. move D0 at bottom. move B0 at bottom. move D1 at bottom. move B1 at bottom. move D2 at bottom. move B2 at bottom. move D3 at bottom. move B3 at bottom. move D4 at bottom. move B4 at bottom. move D5 at bottom. move B5 at bottom. move D6 at bottom. move B6 at bottom. move D7 at bottom. move B7 at bottom. move D8 at bottom. move B8 at bottom. move D9 at bottom. move B9 at bottom. move D10 at bottom. move B10 at bottom. move D11 at bottom. move B11 at bottom. move D12 at bottom. move B12 at bottom. move D13 at bottom. move B13 at bottom. move D14 at bottom. move B14 at bottom. move D15 at bottom. move B15 at bottom. move D16 at bottom. move B16 at bottom. move D17 at bottom. move B17 at bottom. move D18 at bottom. move B18 at bottom. move D19 at bottom. move B19 at bottom. move D20 at bottom. move B20 at bottom. move RGL at bottom. move MTX at bottom. move CANP at bottom. move SHB at bottom. move INI at bottom. move THR at bottom.
  move S0 at top. move S1 at top. move S2 at top. move S3 at top. move S4 at top. move S5 at top. move S6 at top. move S7 at top. move S8 at top. move S9 at top. move S10 at top. move S11 at top. move S12 at top. move S13 at top. move S14 at top. move S15 at top. move S16 at top. move S17 at top. move S18 at top. move S19 at top. move S20 at top. move SA at top.

  carve_frame 176%nat ST.
  do 14 hstep.
  do 5 hstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep.

  steps_to 0x4aee8%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.
  hstep. hstep. astep.
  steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc58c 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc58c 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc590 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc590 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5a0 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5a0 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5a4 16) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5a4 16). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5b4 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5b4 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5b8 20) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5b8 20). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5cc 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5cc 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5d0 16) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5d0 16). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5e0 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5e0 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5e4 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5e4 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc5f4 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5f4 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc604 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc604 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc614 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc614 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc624 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc624 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc62c 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc62c 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc630 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc630 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc640 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc640 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc644 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc644 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc654 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc654 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc658 16) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc658 16). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4affc%Z.

  assert (RX : rng RNG 0x7fffc668 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc668 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x5f738%Z.
  move RW2 at bottom.
  call_sp (poison_low_spec RNG 0x80012bd2 168). all: side RIMG RSTK KH. clear RW2.
  lit_nat.

  steps_to 0x4b258%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.
  steps_to 0x4b30c%Z.
  hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -176) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  unfold unregg_post. sys_finish.
  all: try hyp_by_addr.
Qed.
End CANSEC3.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.F_fmt_fp_lib.
Import F_syscalls.TwinB StdioFiles.TwinB Stdio_kit.TwinB MonadF.TwinB F_memset.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StrwF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

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
     rw_cells bsegs m 0xd3610 [C8 (Z_to_bv 64 0x16b720)]
  /\ rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8); C8 (Z_to_bv 64 0xd9478); C8 (Z_to_bv 64 0xdbc78);
                                C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc960)]
  /\ rw_cells bsegs m 0xd3650 [C8 (Z_to_bv 64 0xd5540)]
  /\ rw_cells bsegs m 0xd5538 [C8 (Z_to_bv 64 0xc95bc); C8 (Z_to_bv 64 0xc99c0)]
  /\ rw_cells bsegs m 0xdbc78 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0xdc958 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xdb4dc [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x16d820 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ rw_cells bsegs m 0xd9490 [C4 (Z_to_bv 64 1)].

Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0xd3610 \/ (0xd3658 <= lo /\ hi <= 0xd5538) \/ (0xd5548 <= lo /\ hi <= 0xd9490) \/ (0xd9494 <= lo /\ hi <= 0xdb4dc)
   \/ (0xdb4dd <= lo /\ hi <= 0xdbc78) \/ (0xdbc80 <= lo /\ hi <= 0xdc958) \/ (0xdc95a <= lo /\ hi <= 0x16d820) \/ 0x16d828 <= lo).

Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono bsegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0xd3610 <= A /\ A + n <= 0xd3658) \/ (0xd5538 <= A /\ A + n <= 0xd5548) \/ (0xd9490 <= A /\ A + n <= 0xd9494)
              \/ (0xdb4dc <= A /\ A + n <= 0xdb4dd) \/ (0xdbc78 <= A /\ A + n <= 0xdbc80) \/ (0xdc958 <= A /\ A + n <= 0xdc95a)
              \/ (0x16d820 <= A /\ A + n <= 0x16d828)) -> disjoint_from W A n).
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
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x631000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF bsegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x600c8) fc None m (seg_rom bsegs)).
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

Definition unreg_one_post (spv d sb sl : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x4b974) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x16d7a8) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1c731) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xd5540) s8 (Z_to_bv 64 0xd9478)
                  (Z_to_bv 64 0xdbc78) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x4b974) fc None m' (seg_rom bsegs)
    /\ munch [(sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma unreg_one_spec : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv bsegs m -> mdtor_rt m ->
  rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 swr)] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 256 -> 0x10000 <= beg -> beg + swr <= 0x631000 ->
  0x10000 <= d -> d + 64 <= 0x631000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF bsegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x16d7a8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1c731) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xd5540) s8 (Z_to_bv 64 0xd9478)
             (Z_to_bv 64 0xdbc78) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4b98c) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 32).
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
  hstep. zstep. rewrite (unsigned_lit8 swr) by lia. hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }

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
  replace (ret_pc (Z_to_bv 64 0x4b974)) with (Z_to_bv 64 0x4b974 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed.

Definition gdesc (m : mem) (d beg sz swr nm md odr : Z) : Prop :=
     rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
                         C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)]
  /\ rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 swr)].

Definition unregg_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells bsegs m 0xd9530 [C8 (Z_to_bv 64 0)]
  /\ gdesc m 0xd7fb0 0x22d00 0x7 0x20 0x1d6da 0x23500 (2^64 - 1)
  /\ gdesc m 0xd7ff0 0x22d20 0x13 0x40 0x1b1ba 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8030 0x22da0 0xb 0x20 0x14307 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8070 0x22dc0 0x43 0x80 0x13bf7 0x23500 (2^64 - 1)
  /\ gdesc m 0xd80b0 0x22e40 0x8 0x20 0x10b1d 0x23500 (2^64 - 1)
  /\ gdesc m 0xd80f0 0x22e60 0x70 0xa0 0x13bff 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8130 0x22f00 0xf 0x20 0x17935 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8170 0x22f20 0x53 0x80 0x10b86 0x23500 (2^64 - 1)
  /\ gdesc m 0xd81b0 0x22fa0 0xa 0x20 0x1703f 0x23500 (2^64 - 1)
  /\ gdesc m 0xd81f0 0x22fc0 0x12 0x40 0x18b85 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8230 0x23040 0x29 0x60 0x10b8e 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8270 0x230a0 0x4f 0x80 0x13c6d 0x23500 (2^64 - 1)
  /\ gdesc m 0xd82b0 0x23120 0xc 0x20 0x1a8f6 0x23500 (2^64 - 1)
  /\ gdesc m 0xd82f0 0x23140 0x14 0x40 0x12618 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8330 0x231c0 0x14 0x40 0x1430f 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8370 0x23240 0x12 0x40 0x18b8d 0x23500 (2^64 - 1)
  /\ gdesc m 0xd83b0 0x232c0 0xc 0x20 0x1cdd6 0x23500 (2^64 - 1)
  /\ gdesc m 0xd83f0 0x23300 0xa 0x20 0x14e06 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8430 0x23320 0x12 0x40 0x18b95 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8470 0x233a0 0xa 0x20 0x19e22 0x23500 (2^64 - 1)
  /\ gdesc m 0xd84b0 0x233c0 0x12 0x40 0x1158d 0x23500 (2^64 - 1)
  /\ gdesc m 0xd84f0 0x23440 0x10 0x20 0x14e4b 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8530 0x23460 0x45 0x80 0x11595 0x23500 (2^64 - 1)
  /\ gdesc m 0xd8570 0x234e0 0x6 0x20 0x20b55 0x23500 (2^64 - 1)
  /\ (exists j, rw_cells bsegs m 0x7fffc5a0 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5a4 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5b4 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5b8 [CB 16 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5c8 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5cc [CB 20 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5e0 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5e4 [CB 16 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5f4 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc5f8 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc608 [CB 12 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc614 [CB 16 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc624 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc628 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc638 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc648 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc658 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc660 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc664 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc674 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc678 [CB 8 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc688 [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc68c [CB 16 j])
  /\ (exists j, rw_cells bsegs m 0x7fffc69c [CB 4 j])
  /\ (exists j, rw_cells bsegs m 0x80012ff6 [CB 192 j]).

Definition MDTOR_DEPTH : Z := 1024.
Definition MDTOR_W : list (Z * Z) := [(0xd9530, 0xd9538); (0x7fffc5a0, 0x7fffc6a0); (0x80012ff6, 0x800130b8)]%Z.

Definition unregg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (0xd9530, 0xd9538); (0x7fffc5a0, 0x7fffc6a0); (0x80012ff6, 0x800130b8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0xd9530 [C8 (Z_to_bv 64 0)]

    /\ rw_cells bsegs m' 0x7fffc5a0 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc5a4 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells bsegs m' 0x7fffc5b4 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc5b8 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells bsegs m' 0x7fffc5c8 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc5cc [CB 20 (repeat (Z_to_bv 8 0) 20)]
    /\ rw_cells bsegs m' 0x7fffc5e0 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc5e4 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells bsegs m' 0x7fffc5f4 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc5f8 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells bsegs m' 0x7fffc608 [CB 12 (repeat (Z_to_bv 8 0) 12)]
    /\ rw_cells bsegs m' 0x7fffc614 [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells bsegs m' 0x7fffc624 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc628 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells bsegs m' 0x7fffc638 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells bsegs m' 0x7fffc648 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells bsegs m' 0x7fffc658 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc660 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc664 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells bsegs m' 0x7fffc674 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc678 [CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells bsegs m' 0x7fffc688 [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x7fffc68c [CB 16 (repeat (Z_to_bv 8 0) 16)]
    /\ rw_cells bsegs m' 0x7fffc69c [CB 4 (repeat (Z_to_bv 8 0) 4)]
    /\ rw_cells bsegs m' 0x80012ff6 [CB 192 (repeat (Z_to_bv 8 0) 192)].

Definition unregg_stmt (PRE : mem -> Prop) : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    PRE m ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (KHIGH <= lo) ->
    mem_inv bsegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    a0 = Z_to_bv 64 0xd7fb0 -> a1 = Z_to_bv 64 24 ->
    evtF bsegs RNG (unregg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x4b7d0) fc None m (seg_rom bsegs)).

End CANSEC2.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

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

Section CANSEC3. Context {rc : runConstT}.
Theorem unregg_proof : unregg_stmt unregg_pre.
Proof.
  unfold unregg_stmt. intros until lo. intros HPRE ST LO KH MI RSTK RIMG RW -> ->.
  pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold unregg_pre, gdesc in P.
  destruct P as (RT & MTX & (D0 & B0) & (D1 & B1) & (D2 & B2) & (D3 & B3) & (D4 & B4) & (D5 & B5) & (D6 & B6) & (D7 & B7) & (D8 & B8) & (D9 & B9) & (D10 & B10) & (D11 & B11) & (D12 & B12) & (D13 & B13) & (D14 & B14) & (D15 & B15) & (D16 & B16) & (D17 & B17) & (D18 & B18) & (D19 & B19) & (D20 & B20) & (D21 & B21) & (D22 & B22) & (D23 & B23) & [j0 S0] & [j1 S1] & [j2 S2] & [j3 S3] & [j4 S4] & [j5 S5] & [j6 S6] & [j7 S7] & [j8 S8] & [j9 S9] & [j10 S10] & [j11 S11] & [j12 S12] & [j13 S13] & [j14 S14] & [j15 S15] & [j16 S16] & [j17 S17] & [j18 S18] & [j19 S19] & [j20 S20] & [j21 S21] & [j22 S22] & [j23 S23] & [jA SA]).
  lit_addr.
  change (2^64 - 1) with 18446744073709551615 in D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22, D23.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).

  unfold MDTOR_W in RW.
  repeat lazymatch type of RW with Forall _ (_ :: _) =>
    let H := fresh "RW" in pose proof (Forall_inv RW) as H; cbn [fst snd] in H; apply Forall_inv_tail in RW end.
  lit_rng.
  pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0xd9530, 0xd9538); (0x7fffc5a0, 0x7fffc6a0); (0x80012ff6, 0x800130b8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (RSF : rng RNG (bv_unsigned sp + -240) 240) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.

  move PGC at bottom. move GOT at bottom. move GOT80 at bottom. move REAL at bottom. move D0 at bottom. move B0 at bottom. move D1 at bottom. move B1 at bottom. move D2 at bottom. move B2 at bottom. move D3 at bottom. move B3 at bottom. move D4 at bottom. move B4 at bottom. move D5 at bottom. move B5 at bottom. move D6 at bottom. move B6 at bottom. move D7 at bottom. move B7 at bottom. move D8 at bottom. move B8 at bottom. move D9 at bottom. move B9 at bottom. move D10 at bottom. move B10 at bottom. move D11 at bottom. move B11 at bottom. move D12 at bottom. move B12 at bottom. move D13 at bottom. move B13 at bottom. move D14 at bottom. move B14 at bottom. move D15 at bottom. move B15 at bottom. move D16 at bottom. move B16 at bottom. move D17 at bottom. move B17 at bottom. move D18 at bottom. move B18 at bottom. move D19 at bottom. move B19 at bottom. move D20 at bottom. move B20 at bottom. move D21 at bottom. move B21 at bottom. move D22 at bottom. move B22 at bottom. move D23 at bottom. move B23 at bottom. move RGL at bottom. move MTX at bottom. move CANP at bottom. move SHB at bottom. move INI at bottom. move THR at bottom.
  move S0 at top. move S1 at top. move S2 at top. move S3 at top. move S4 at top. move S5 at top. move S6 at top. move S7 at top. move S8 at top. move S9 at top. move S10 at top. move S11 at top. move S12 at top. move S13 at top. move S14 at top. move S15 at top. move S16 at top. move S17 at top. move S18 at top. move S19 at top. move S20 at top. move S21 at top. move S22 at top. move S23 at top. move SA at top.

  carve_frame 176%nat ST.
  do 14 hstep.
  do 5 hstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep.

  steps_to 0x4b878%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.
  hstep. hstep. astep.
  steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5a0 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5a0 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5a4 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5a4 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5b4 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5b4 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5b8 16) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5b8 16). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5c8 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5c8 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5cc 20) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5cc 20). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5e0 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5e0 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5e4 16) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5e4 16). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5f4 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5f4 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc5f8 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc5f8 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc608 12) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc608 12). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc614 16) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc614 16). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc624 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc624 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc628 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc628 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc638 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc638 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc648 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc648 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc658 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc658 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc660 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc660 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc664 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc664 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc674 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc674 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc678 8) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc678 8). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc688 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc688 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc68c 16) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc68c 16). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x4b98c%Z.

  assert (RX : rng RNG 0x7fffc69c 4) by (apply (rng_sub' _ _ _ _ _ RW1); lia).
  call (unreg_one_spec RNG 0x7fffc69c 4). all: side RIMG RSTK KH. clear RX.
  lit_nat. steps_to 0x600c8%Z.
  move RW2 at bottom.
  call_sp (poison_low_spec RNG 0x80012ff6 192). all: side RIMG RSTK KH. clear RW2.
  lit_nat.

  steps_to 0x4bbe8%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.
  steps_to 0x4bc9c%Z.
  hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -176) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  unfold unregg_post. sys_finish.
  all: try hyp_by_addr.
Qed.
End CANSEC3.
End TwinB.
