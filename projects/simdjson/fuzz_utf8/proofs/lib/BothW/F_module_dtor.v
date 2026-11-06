(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF F_memset AExit F_stdio_exit F_module_dtor_pre.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Section CANSEC2. Context {rc : runConstT}.
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
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x6d2000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF bsegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x82898) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  unfold KHIGH in KH. pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x80100000 /\ 0 < shn size).
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
    ms' = MS (mkR (Z_to_bv 64 0x68be0) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x20cba8) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1cc67) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x174060) s8 (Z_to_bv 64 0x178878)
                  (Z_to_bv 64 0x17b078) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x68be0) fc None m' (seg_rom bsegs)
    /\ munch [(sb, sb + sl)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Lemma unreg_one_spec : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv bsegs m -> mdtor_rt m ->
  rw_cells bsegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells bsegs m (d + 16) [C1 (Z_to_bv 8 (swr mod 256))] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 65536 -> 0x10000 <= beg -> beg + swr <= 0x6d2000 ->
  0x10000 <= d -> d + 64 <= 0x6d2000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF bsegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x20cba8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cc67) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x174060) s8 (Z_to_bv 64 0x178878)
             (Z_to_bv 64 0x17b078) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x68bf8) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x80100000 /\ 0 < shn swr < 8192).
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
  hstep. zstep. rewrite (unsigned_lit8 (swr mod 256)) by (Z.div_mod_to_equations; lia). hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear -SL SWR. Z.div_mod_to_equations. lia. }
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
  replace (ret_pc (Z_to_bv 64 0x68be0)) with (Z_to_bv 64 0x68be0 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed.

End CANSEC2.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Ltac hstep ::= zstep; fix_lit_store.

Section CANSEC3. Context {rc : runConstT}.

Definition iter_post (spv d n : Z) (W : list (Z * Z)) (gp tp s5 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x20cba8) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1cc67) (Z_to_bv 64 (d + 64)) s5 s6 (Z_to_bv 64 0x174060) s8 (Z_to_bv 64 0x178878)
                  (Z_to_bv 64 0x17b078) (Z_to_bv 64 (n - 1)) t3 t4 t5 t6)
             F (Z_to_bv 64 (if n =? 1 then 0x68dfc else 0x68bf8)) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

Lemma iter_plain : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d n beg sz swr nm md : Z) (junk : list byte),
  mem_inv bsegs m -> mdtor_rt m ->
  gdesc m d beg sz swr nm md 18446744073709551615 ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 65536 -> 0x10000 <= beg -> beg + swr <= 0x6d2000 ->
  0x10000 <= d -> d + 64 <= 0x6d2000 -> 0 <= spv < 2^64 -> 0 < n < 65536 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF bsegs RNG (iter_post spv d n [(sb, sb + sl)] gp tp s5 s6 s8 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x20cba8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cc67) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x174060) s8 (Z_to_bv 64 0x178878)
             (Z_to_bv 64 0x17b078) (Z_to_bv 64 n) t3 t4 t5 t6)
        F (Z_to_bv 64 0x68bf8) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI RT [D DB] AL SL SWR LOW HIE DLO DHI SPV NR -> -> DST RIMG RSH.
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x80100000 /\ 0 < shn swr < 8192).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  call (unreg_one_spec RNG (shd beg) (shn swr)).
  1-15: first [ eassumption | reflexivity | lia | idtac ].
  hstep. zstep. astep. zstep. zstep. hstep.
  replace (n + -1) with (n - 1) by lia.
  assert (E : bv_eqb (Z_to_bv 64 (n - 1)) (Z_to_bv 64 0) = (n =? 1)).
  { rewrite bv_eqb_Z, !unsigned_lit by lia. destruct (Z.eqb_spec n 1); lia. }
  rewrite E. clear E.
  replace (if n =? 1 then Z_to_bv 64 429564 else Z_to_bv 64 429048) with (Z_to_bv 64 (if n =? 1 then 0x68dfc else 0x68bf8) : word) by (destruct (n =? 1); reflexivity).
  unfold iter_post. sys_finish.
Qed.

Lemma iter_odr : forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d n beg sz swr nm md odr : Z) (junk : list byte) (ob : byte),
  mem_inv bsegs m -> mdtor_rt m ->
  gdesc m d beg sz swr nm md odr ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 65536 -> 0x10000 <= beg -> beg + swr <= 0x6d2000 ->
  0x10000 <= d -> d + 64 <= odr -> odr < 0x6d2000 -> 0 <= spv < 2^64 -> 0 < n < 65536 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells bsegs m sb [CB (Z.to_nat sl) junk] ->
  rw_cells bsegs m odr [C1 ob] ->
  rng_aimg RNG -> rng RNG sb sl -> rng RNG odr 1 ->
  evtF bsegs RNG (iter_post spv d n [(sb, sb + sl); (odr, odr + 1)] gp tp s5 s6 s8 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x20cba8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cc67) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x174060) s8 (Z_to_bv 64 0x178878)
             (Z_to_bv 64 0x17b078) (Z_to_bv 64 n) t3 t4 t5 t6)
        F (Z_to_bv 64 0x68bf8) fc None m (seg_rom bsegs)).
Proof.
  intros until ob. intros MI RT [D DB] AL SL SWR LOW HIE DLO DHI OHI SPV NR -> -> DST OD RIMG RSH ROD.
  pose proof (munch_refl [(shd beg, shd beg + shn swr); (odr, odr + 1)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x80100000 /\ 0 < shn swr < 8192).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  call (unreg_one_spec RNG (shd beg) (shn swr)).
  1-15: first [ eassumption | reflexivity | lia | idtac ].
  hstep. zstep. hstep. if_cases K; zify_cond K. 2:{ exfalso. lia. }
  hstep. zstep. zstep. hstep.
  replace (n + -1) with (n - 1) by lia.
  assert (E : bv_eqb (Z_to_bv 64 (n - 1)) (Z_to_bv 64 0) = (n =? 1)).
  { rewrite bv_eqb_Z, !unsigned_lit by lia. destruct (Z.eqb_spec n 1); lia. }
  rewrite E. clear E. unfold iter_post.
  destruct (Z.eqb_spec n 1) as [N1|N1]; cbn [negb].
  - hstep. sys_finish.
  - sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation G := (Z * Z * Z * Z * Z * Z * Z)%type.
Definition MD_M64 : Z := 18446744073709551615.
Definition g_d (g : G) : Z := let '(d, beg, sz, swr, nm, md, odr) := g in d.
(* [comment removed for export] *)
Definition g_W (g : G) : list (Z * Z) :=
  let '(d, beg, sz, swr, nm, md, odr) := g in
  (shd beg, shd beg + shn swr) :: (if odr =? MD_M64 then [] else [(odr, odr + 1)]).
(* [comment removed for export] *)
Definition g_ivs (g : G) : list (Z * Z) := let '(d, beg, sz, swr, nm, md, odr) := g in (d, d + 64) :: g_W g.
Definition g_P (m : mem) (g : G) : Prop :=
  let '(d, beg, sz, swr, nm, md, odr) := g in
  gdesc m d beg sz swr nm md odr
  /\ (exists j, rw_cells bsegs m (shd beg) [CB (Z.to_nat (shn swr)) j])
  /\ (odr = MD_M64 \/ exists b, rw_cells bsegs m odr [C1 b]).
Definition g_R (RNG : footprint) (g : G) : Prop :=
  let '(d, beg, sz, swr, nm, md, odr) := g in rng RNG (shd beg) (shn swr) /\ (odr = MD_M64 \/ rng RNG odr 1).
Definition g_okb (g : G) : bool :=
  let '(d, beg, sz, swr, nm, md, odr) := g in
  (beg mod 8 =? 0) && (swr mod 8 =? 0) && (0 <? swr) && (swr <? 65536) && (0x10000 <=? beg) && (beg + swr <=? 0x6d2000)
  && (0x10000 <=? d) && (d + 64 <=? 0x6d2000) && ((odr =? MD_M64) || ((d + 64 <=? odr) && (odr <? 0x6d2000))).
Definition disj_iv (w iv : Z * Z) : bool := (snd iv <=? fst w) || (snd w <=? fst iv).
Definition sepb (g g' : G) : bool := forallb (fun iv => forallb (fun w => disj_iv w iv) (g_W g)) (g_ivs g').
Fixpoint gs_okb (d : Z) (gs : list G) : bool :=
  match gs with [] => true | g :: tl => (g_d g =? d) && g_okb g && forallb (sepb g) tl && gs_okb (d + 64) tl end.

Lemma disj_all : forall (W : list (Z * Z)) lo hi, forallb (fun w => disj_iv w (lo, hi)) W = true ->
  forall A n, lo <= A -> A + n <= hi -> disjoint_from W A n.
Proof.
  induction W as [|[wl wh] W IH]; cbn [forallb disjoint_from]; intros lo hi H A n H1 H2; [exact I|].
  apply andb_prop in H as [Ha Hb]. unfold disj_iv in Ha. cbn [fst snd] in Ha. split; [| eapply IH; eauto].
  destruct (Z.leb_spec0 hi wl); destruct (Z.leb_spec0 wh lo); cbn in Ha; try discriminate; lia.
Qed.

Lemma shn_nonneg : forall l, 0 <= l -> 0 <= shn l.
Proof. intros l Hl. unfold shn. apply Z.shiftr_nonneg. exact Hl. Qed.

Definition md_iv_clear (W : list (Z * Z)) (iv : Z * Z) : Prop := forall A n, fst iv <= A -> A + n <= snd iv -> disjoint_from W A n.

Lemma g_P_transport_gen : forall W m m' g,
  Forall (md_iv_clear W) (g_ivs g) -> g_okb g = true ->
  munch W m m' -> wmono bsegs m m' -> g_P m g -> g_P m' g.
Proof.
  intros W m m' [[[[[[d beg] sz] swr] nm] md] odr] HS HK MU WM HG. unfold g_P in HG |- *. destruct HG as ([D DB] & [j SH] & OD).
  unfold g_okb in HK. repeat (apply andb_prop in HK as [HK ?X]).
  cbn [g_ivs g_W] in HS. pose proof (Forall_inv HS) as H1. apply Forall_inv_tail in HS. pose proof (Forall_inv HS) as H2. apply Forall_inv_tail in HS.
  unfold md_iv_clear in H1, H2. cbn [fst snd] in H1, H2.
  assert (SWR : 0 < swr) by (apply Z.ltb_lt; assumption).
  pose proof (shn_nonneg swr ltac:(lia)) as SN.
  split; [split|split].
  - eapply rw_cells_transport; [exact D | exact MU | exact WM |]. apply H1; cbn; lia.
  - eapply rw_cells_transport; [exact DB | exact MU | exact WM |]. apply H1; cbn; lia.
  - exists j. eapply rw_cells_transport; [exact SH | exact MU | exact WM |]. apply H2; [lia | cbn [cells_size csize]; lia].
  - destruct (Z.eqb_spec odr MD_M64) as [E|NE]; [left; exact E|].
    destruct OD as [OD|[b OD]]; [left; exact OD| right]. exists b.
    pose proof (Forall_inv HS) as H3. unfold md_iv_clear in H3. cbn [fst snd] in H3.
    eapply rw_cells_transport; [exact OD | exact MU | exact WM |]. apply H3; cbn; lia.
Qed.

Lemma g_P_transport : forall W m m' g,
  forallb (fun iv => forallb (fun w => disj_iv w iv) W) (g_ivs g) = true -> g_okb g = true ->
  munch W m m' -> wmono bsegs m m' -> g_P m g -> g_P m' g.
Proof.
  intros W m m' g HS. apply g_P_transport_gen. apply Forall_forall. intros [l h] Hiv. rewrite forallb_forall in HS.
  intros A n H1 H2. eapply disj_all; [exact (HS _ Hiv) | exact H1 | exact H2].
Qed.

(* [comment removed for export] *)
Definition lowb (HI : Z) (c : Z * Z) (g : G) : bool := forallb (fun iv => (snd iv <=? HI) && disj_iv c iv) (g_ivs g).
Lemma lowb_clear : forall HI c a b g, lowb HI c g = true -> HI <= a -> Forall (md_iv_clear [(a, b); c]) (g_ivs g).
Proof.
  intros HI [c1 c2] a b g H Ha. apply Forall_forall. intros [l h] Hiv. unfold lowb in H. rewrite forallb_forall in H.
  specialize (H _ Hiv). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. unfold disj_iv in H2. cbn [fst snd] in *.
  intros A n HA Hn. cbn [disjoint_from fst snd]. 
  cbn [fst snd] in HA, Hn. destruct (Z.leb_spec0 h c1); destruct (Z.leb_spec0 c2 l); cbn in H2; try discriminate; lia.
Qed.

Lemma sub_fp_app_l : forall (W1 W2 Wc : list (Z * Z)), sub_fp (W1 ++ W2) Wc -> sub_fp W1 Wc.
Proof.
  intros W1 W2 Wc H x Hx. specialize (H x Hx). clear Hx. induction W1 as [|[lo hi] W1 IH]; cbn in *; [exact I|]. tauto.
Qed.
Lemma sub_fp_app_r : forall (W1 W2 Wc : list (Z * Z)), sub_fp (W1 ++ W2) Wc -> sub_fp W2 Wc.
Proof.
  intros W1 W2 Wc H x Hx. specialize (H x Hx). clear Hx. induction W1 as [|[lo hi] W1 IH]; cbn in *; [exact H|]. tauto.
Qed.

Lemma gs_okb_all : forall gs d, gs_okb d gs = true -> forall g, In g gs -> g_okb g = true.
Proof.
  induction gs as [|g0 tl IH]; intros d OK g Hg; [destruct Hg|]. cbn [gs_okb] in OK.
  apply andb_prop in OK as [OK OKT]. apply andb_prop in OK as [OK SEP]. apply andb_prop in OK as [DE GK].
  destruct Hg as [<-|Hg]; [exact GK| exact (IH _ OKT g Hg)].
Qed.

Definition loop_post (spv : Z) (W : list (Z * Z)) (gp tp s5 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s7 s9 s10 s11 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x68dfc) fc None m' (seg_rom bsegs)
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'.

Lemma unreg_loop : forall RNG (Wc : list (Z * Z)) (gp tp s5 s6 s8 : word) (F : bvmap 5 word) fc (spv : Z),
  0 <= spv < 2^64 -> rng_aimg RNG ->
  forall (gs : list G) (d n : Z),
  gs_okb d gs = true -> gs <> [] -> n = Z.of_nat (length gs) -> n < 65536 ->
  Forall (g_R RNG) gs -> Forall rt_clear (flat_map g_W gs) -> sub_fp (flat_map g_W gs) Wc ->
  forall (m : mem) (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  mem_inv bsegs m -> mdtor_rt m -> Forall (g_P m) gs ->
  evtF bsegs RNG (loop_post spv Wc gp tp s5 s6 s8 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x20cba8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cc67) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x174060) s8 (Z_to_bv 64 0x178878)
             (Z_to_bv 64 0x17b078) (Z_to_bv 64 n) t3 t4 t5 t6)
        F (Z_to_bv 64 0x68bf8) fc None m (seg_rom bsegs)).
Proof.
  intros RNG Wc gp tp s5 s6 s8 F fc spv SPV RIMG gs.
  induction gs as [|g tl IH]; intros d n OK NE EN NB HR HC HW m ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI RT HP; [congruence|].
  cbn [gs_okb] in OK. apply andb_prop in OK as [OK OKT]. apply andb_prop in OK as [OK SEP]. apply andb_prop in OK as [DE GK].
  apply Z.eqb_eq in DE.
  pose proof (Forall_inv HP) as P0. pose proof (Forall_inv_tail HP) as PT.
  pose proof (Forall_inv HR) as R0. pose proof (Forall_inv_tail HR) as RT'.
  cbn [flat_map] in HC, HW. apply Forall_app in HC as [HC0 HCT].
  pose proof (sub_fp_app_l _ _ _ HW) as HW0. pose proof (sub_fp_app_r _ _ _ HW) as HWT.
  cbn [length] in EN. rewrite Nat2Z.inj_succ in EN.
  pose proof GK as GK'.
  destruct g as [[[[[[d0 beg] sz] swr] nm] md] odr]. cbn [g_d] in DE. subst d0.
  unfold g_okb in GK. repeat (apply andb_prop in GK as [GK ?X]).
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
  destruct P0 as (GD & [j SH] & OD). destruct R0 as [RS RO].
  (* [comment removed for export] *)
  eapply evtF_cut with (P := iter_post spv d n (g_W (d, beg, sz, swr, nm, md, odr)) gp tp s5 s6 s8 F fc m).
  { cbn [g_W]. destruct (Z.eqb_spec odr MD_M64) as [E|NEo].
    - subst odr. eapply iter_plain; try eassumption; try reflexivity; lia.
    - destruct OD as [OD|[b OD]]; [contradiction|]. destruct RO as [RO|RO]; [contradiction|].
      match goal with H : (_ || _) = true |- _ => apply orb_prop in H as [H|H]; [first [discriminate H | apply Z.eqb_eq in H; contradiction]|];
        apply andb_prop in H as [XO1 XO2]; apply Z.leb_le in XO1; apply Z.ltb_lt in XO2 end.
      eapply iter_odr; try eassumption; try reflexivity; lia. }
  intros ms' PO. unfold iter_post in PO. destruct_exs PO. destruct PO as (-> & MU1 & WM1 & MI1).
  assert (RT1 : mdtor_rt x16) by (eapply mdtor_rt_frame; [exact RT | exact MU1 | exact WM1 | exact HC0]).
  destruct tl as [|g' tl'].
  - (* [comment removed for export] *)
    cbn [length] in EN. replace (n =? 1) with true by (symmetry; apply Z.eqb_eq; lia).
    apply evtF_done. unfold loop_post. do 26 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [exact HW0 | exact MU1]|]. split; [exact WM1 | exact MI1].
  - replace (n =? 1) with false by (symmetry; apply Z.eqb_neq; cbn [length] in EN; lia).
    eapply evtF_mono.
    { eapply (IH (d + 64) (n - 1)); try eassumption; try (intro; discriminate); try lia.
      apply Forall_forall. intros g1 Hg1. rewrite Forall_forall in PT. rewrite forallb_forall in SEP.
      eapply g_P_transport; [exact (SEP g1 Hg1) | exact (gs_okb_all _ _ OKT g1 Hg1) | exact MU1 | exact WM1 | exact (PT g1 Hg1)]. }
    intros ms' PO. unfold loop_post in PO |- *. destruct_exs PO. destruct PO as (-> & MU2 & WM2 & MI2).
    do 26 eexists. split; [reflexivity|].
    split; [eapply munch_trans; [eapply munch_weaken; [exact HW0 | exact MU1] | exact MU2]|].
    split; [eapply wmono_trans; [exact WM1 | exact WM2] | exact MI2].
Qed.

(* [comment removed for export] *)
Lemma unreg_loop_c : forall RNG (Wc : list (Z * Z)) (gs : list G) (d n : Z) (gp tp s5 s6 s8 : word) (F : bvmap 5 word) fc (spv : Z)
    (m : mem) (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  0 <= spv < 2^64 -> rng_aimg RNG ->
  gs_okb d gs = true -> gs <> [] -> n = Z.of_nat (length gs) -> n < 65536 ->
  Forall (g_R RNG) gs -> Forall rt_clear (flat_map g_W gs) -> sub_fp (flat_map g_W gs) Wc ->
  mem_inv bsegs m -> mdtor_rt m -> Forall (g_P m) gs ->
  evtF bsegs RNG (loop_post spv Wc gp tp s5 s6 s8 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x20cba8) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1cc67) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x174060) s8 (Z_to_bv 64 0x178878)
             (Z_to_bv 64 0x17b078) (Z_to_bv 64 n) t3 t4 t5 t6)
        F (Z_to_bv 64 0x68bf8) fc None m (seg_rom bsegs)).
Proof. intros. eapply unreg_loop; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition g_sh (g : G) : Z * Z := let '(d, beg, sz, swr, nm, md, odr) := g in (shd beg, shn swr).
Definition g_odr_inb (OD : list Z) (g : G) : bool := let '(d, beg, sz, swr, nm, md, odr) := g in (odr =? MD_M64) || existsb (Z.eqb odr) OD.

Lemma pre_g_P : forall m (GL : list G) (OD : list Z) (SH : list (Z * Z)),
  SH = map g_sh GL -> forallb (g_odr_inb OD) GL = true ->
  Forall (gdesc_t m) GL -> Forall (fun o => exists b, rw_cells bsegs m o [C1 b]) OD ->
  Forall (fun p => exists j, rw_cells bsegs m (fst p) [CB (Z.to_nat (snd p)) j]) SH ->
  Forall (g_P m) GL.
Proof.
  intros m GL OD SH -> HO HD HOD HSH. rewrite Forall_map in HSH. rewrite forallb_forall in HO.
  rewrite Forall_forall in HD, HOD, HSH |- *. intros g Hg.
  specialize (HO g Hg). specialize (HD g Hg). specialize (HSH g Hg).
  destruct g as [[[[[[d beg] sz] swr] nm] md] odr]. cbn [g_sh fst snd gdesc_t g_odr_inb] in *. unfold g_P.
  split; [exact HD|]. split; [exact HSH|].
  apply orb_prop in HO as [HO|HO]; [left; apply Z.eqb_eq; exact HO| right].
  apply existsb_exists in HO as (o & Ho & E). apply Z.eqb_eq in E. subst o. exact (HOD _ Ho).
Qed.

Definition covb (W : list (Z * Z)) (lo len : Z) : bool := existsb (fun c => (fst c <=? lo) && (lo + len <=? snd c)) W.
Lemma rng_cov : forall RNG (W : list (Z * Z)), Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) W ->
  forall lo len, covb W lo len = true -> rng RNG lo len.
Proof.
  intros RNG W HW lo len H. apply existsb_exists in H as ([cl ch] & Hc & E). rewrite Forall_forall in HW. specialize (HW _ Hc).
  cbn [fst snd] in *. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  eapply rng_sub'; [exact HW| lia].
Qed.
Definition g_covb (W : list (Z * Z)) (g : G) : bool :=
  let '(d, beg, sz, swr, nm, md, odr) := g in covb W (shd beg) (shn swr) && ((odr =? MD_M64) || covb W odr 1).
Lemma g_R_all : forall RNG (W : list (Z * Z)) (GL : list G), Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) W ->
  forallb (g_covb W) GL = true -> Forall (g_R RNG) GL.
Proof.
  intros RNG W GL HW H. rewrite forallb_forall in H. apply Forall_forall. intros g Hg. specialize (H g Hg).
  destruct g as [[[[[[d beg] sz] swr] nm] md] odr]. cbn [g_covb] in H. unfold g_R. apply andb_prop in H as [H1 H2].
  split; [eapply rng_cov; eassumption|]. apply orb_prop in H2 as [H2|H2]; [left; apply Z.eqb_eq; exact H2| right; eapply rng_cov; eassumption].
Qed.

Lemma outside_in : forall (W : list (Z * Z)) x c, outside W x -> In c W -> ~ (fst c <= x < snd c).
Proof.
  induction W as [|[l h] W IH]; cbn [outside In]; intros x c HO Hc; [destruct Hc|].
  destruct HO as [H1 H2]. destruct Hc as [<-|Hc]; [exact H1| exact (IH _ _ H2 Hc)].
Qed.
Lemma sub_fp_cov : forall (W Wc : list (Z * Z)),
  forallb (fun iv => existsb (fun c => (fst c <=? fst iv) && (snd iv <=? snd c)) Wc) W = true -> sub_fp W Wc.
Proof.
  intros W Wc H x Hx. induction W as [|[l h] W IH]; cbn [outside]; [exact I|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. split; [| exact (IH H2)].
  apply existsb_exists in H1 as (c & Hc & E). apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. cbn [fst snd] in *.
  pose proof (outside_in _ _ _ Hx Hc). lia.
Qed.

Lemma g_P_low_all : forall HI c a b m m' (GL : list G) d,
  gs_okb d GL = true -> forallb (lowb HI c) GL = true -> HI <= a ->
  munch [(a, b); c] m m' -> wmono bsegs m m' -> Forall (g_P m) GL -> Forall (g_P m') GL.
Proof.
  intros HI c a b m m' GL d OK HL Ha MU WM HP. rewrite forallb_forall in HL. rewrite Forall_forall in HP |- *. intros g Hg.
  eapply g_P_transport_gen; [eapply lowb_clear; [exact (HL g Hg) | exact Ha] | exact (gs_okb_all _ _ OK g Hg) | exact MU | exact WM | exact (HP g Hg)].
Qed.
End CANSEC3.

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

Section CANSEC4. Context {rc : runConstT}.
Theorem module_dtor_proof : module_dtor_stmt mdtor_pre.
Proof.
  unfold module_dtor_stmt. intros until lo. intros HPRE ST LO KH MI RSTK RIMG RW.
  pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold mdtor_pre in P.
  destruct P as (RT & GSS & FLG & MTX & GDS & ODS & SHS & [j5 S5]).
  unfold GARR_SH in S5.
  pose proof RT as RT'. destruct RT' as (PGC & GOT & GOT80 & REAL & SHB & INI & CANP & THR & RGL).
  (* [comment removed for export] *)
  pose proof RW as RW0.
  unfold MDTOR_W in RW.
  repeat lazymatch type of RW with Forall _ (_ :: _) =>
    let H := fresh "RW" in pose proof (Forall_inv RW) as H; cbn [fst snd] in H; apply Forall_inv_tail in RW end.
  lit_rng.
  pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp); (0x178930, 0x178938)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (RSF : rng RNG (bv_unsigned sp + -272) 272) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.
  sort_lits.
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
  steps_to 0x68ae4%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.                                  (* [comment removed for export] *)
  hstep. hstep. astep.
  steps_to 0x68bf8%Z.
  (* [comment removed for export] *)
  assert (GOK : gs_okb 0x176f10 GLOBALS = true) by (vm_compute; reflexivity).
  assert (GP0 : Forall (g_P m) GLOBALS)
    by (apply (pre_g_P m GLOBALS GODRS GSHADOWS); [vm_compute; reflexivity | vm_compute; reflexivity | exact GDS | exact ODS | exact SHS]).
  clear GDS ODS SHS.
  match type of MU with munch _ _ ?mc =>
    assert (GP1 : Forall (g_P mc) GLOBALS)
      by (eapply (g_P_low_all KHIGH (0x178930, 0x178938) (bv_unsigned sp - 1024) (bv_unsigned sp)); [exact GOK | vm_compute; reflexivity | unfold KHIGH; lia | exact MU | exact WM | exact GP0]);
    assert (MU' : munch ((bv_unsigned sp - 1024, bv_unsigned sp) :: MDTOR_W) m mc)
      by (eapply munch_weaken; [| exact MU]; unfold MDTOR_W; intros xq Hxq; cbn [outside] in Hxq |- *; tauto)
  end.
  clear MU GP0. rename MU' into MU. unfold MDTOR_W in MU.
  (* [comment removed for export] *)
  let wc := eval vm_compute in (firstn 4 (skipn 2 MDTOR_W)) in call (unreg_loop_c RNG wc GLOBALS).
  all: lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- gs_okb _ _ = true => exact GOK
       | |- GLOBALS <> [] => unfold GLOBALS; intro; discriminate
       | |- @eq Z _ _ => vm_compute; reflexivity
       | |- Forall (g_R _) _ => apply (g_R_all RNG MDTOR_W GLOBALS RW0); vm_compute; reflexivity
       | |- Forall rt_clear _ =>
           let l := eval vm_compute in (flat_map g_W GLOBALS) in
           replace (flat_map g_W GLOBALS) with l by (vm_compute; reflexivity);
           repeat (apply Forall_cons; [unfold rt_clear; lia|]); apply Forall_nil
       | |- sub_fp _ _ => apply sub_fp_cov; vm_compute; reflexivity
       | |- mem_inv _ _ => hyp_by_addr
       | |- mdtor_rt _ => rt_split
       | |- Forall (g_P _) _ => exact GP1
       | |- _ => lia
       end.
  clear GP1 GOK.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 6 hstep. hstep.
  move RW7 at bottom.
  let a := eval vm_compute in GARR_SH in
  let n := eval vm_compute in (8 * Z.of_nat (length GLOBALS)) in
  call_sp (poison_low_spec RNG a n). all: side RIMG RSTK KH. clear RW7.
  lit_nat.
  (* [comment removed for export] *)
  steps_to 0x68e54%Z.

  amo_step. astep. amo_step. astep. astep.
  astep.                                               (* [comment removed for export] *)
  steps_to 0x690ac%Z.
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
End CANSEC4.
