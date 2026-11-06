(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep SysMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import PEnv LJ F_memset.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition poison_entry : Z := 0x59818.

Definition pgup (x : Z) : Z := ((x + 4096 - 1) / 4096) * 4096.
Definition pgdn (x : Z) : Z := (x / 4096) * 4096.

Definition poison_remap (addr size v : Z) : option (Z * Z) := None.

Definition poison_tree (addr size v : Z) : itree nodeL (exc unit) :=
  match poison_remap addr size v with None => Ret (Ok tt) | Some (pb, pe) => t_remap pb (pe - pb) end.

Definition poison_H (addr size v : Z) (H : word -> bool) : word -> bool :=
  match poison_remap addr size v with None => H | Some (pb, pe) => unhide_range pb pe H end.

Lemma poison_remap_memset : forall addr size v, size mod 8 = 0 -> 0 <= size ->
  (v <> 0 \/ size < 8 * 65536) -> poison_remap addr size v = None.
Proof. reflexivity. Qed.

Definition poison_range (addr size : Z) : Prop :=
  (0 <= addr /\ addr < 0x7fff8000 /\ 0 <= addr + size - 8 /\ addr + size - 8 < 0x7fff8000)
  \/ (0x10007fff8000 <= addr /\ addr < 2^47 /\ 0x10007fff8000 <= addr + size - 8 /\ addr + size - 8 < 2^47).

Lemma poison_range_of_app_mem : forall addr size, 8 <= size -> app_mem addr size -> poison_range addr size.
Proof. intros addr size S8 AM. unfold app_mem in AM. unfold poison_range. lia. Qed.

Section P.
Context {HC : HasCeiling}.
Variable E : penv.
Variables (ra gp tp x5 x6 x7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (q lo addr size v : Z) (m : word -> option byte).
Hypothesis MI : mem_inv asegs m.
Hypothesis QB : 0x10007fff8000 <= lo /\ lo <= q - 64 /\ q <= 2^47.
Hypothesis AB : addr mod 8 = 0 /\ size mod 8 = 0 /\ 0 <= size /\ poison_range addr size /\ 0 <= v < 256.

Notation W := [(q - 64, q); (sh addr, sh addr + size / 8)].

Definition poison_post : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'
    /\ rw_cells asegs m' (sh addr) [CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 v) (Z.to_nat (size / 8)))].

Notation PST pc mm x9 x11 x12 x13 x14 x15 x16 x17 y5 y6 y7 y28 y29 y30 y31 :=
  (MS (mkR ra (wz (q + -64)) gp tp y5 y6 y7 s0 x9 (wz addr) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
      F (wz pc) fc None mm (seg_rom asegs)) (only parsing).
Notation FRAME mm junk8 := (rw_cells asegs mm (q + -64) [CB 8 junk8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) (only parsing).

Definition at948 (Q : machine_state -> Prop) : Prop :=
  forall (m0 : word -> option byte) (junk8 : list byte) x13 x14 x15 x16 x17 y5 y6 y7 y28 y29 y30 y31,
    poison_env E m0 -> FRAME m0 junk8 -> stk asegs m0 lo (q + -64) ->
    munch [(q - 64, q)] m m0 -> wmono asegs m m0 -> mem_inv asegs m0 ->
    evt asegs Q (PST 0x59a9c m0 (wz SHADOW_OFF) (wz (addr + size - 8)) (wz v) x13 x14 x15 x16 x17 y5 y6 y7 y28 y29 y30 y31).

#[using="QB AB"] Lemma poison_tail2 : forall Q, at948 Q -> forall (m0 : word -> option byte) (junk8 : list byte) x13 x15 x16 x17 y5 y6 y7 y28 y29 y30 y31,
  poison_env E m0 -> FRAME m0 junk8 -> stk asegs m0 lo (q + -64) ->
  munch [(q - 64, q)] m m0 -> wmono asegs m m0 -> mem_inv asegs m0 ->
  evt asegs Q (PST 0x59a48 m0 (wz SHADOW_OFF) (wz size) (wz v) x13 (wz (SHADOW_OFF - 1)) x15 x16 x17 y5 y6 y7 y28 y29 y30 y31).
Proof.
  intros Q K. intros until y31. intros PE FR ST MU WM MI0. pose proof QB as (LO & LOQ & QHI). pose proof AB as (AL & SL & S8 & AM & VB).
  unfold poison_range in AM. unfold SHADOW_OFF. pose proof PE as PE0. pe_split PE.
  zstep. zstep. if_cases K0; zify_cond K0.
  { exfalso. change 7 with (Z.ones 3) in K0. rewrite Z.land_ones in K0 by lia. change (2^3) with 8 in K0. lia. }
  zstep. zstep.
  zstep. if_cases K1; zify_cond K1.
  -   eapply K; eassumption.
  - do 7 zstep.
    zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
    do 5 zstep.
    zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
    eapply K; eassumption.
Qed.

#[using="QB AB"] Lemma poison_tail1 : forall Q, at948 Q -> forall (m0 : word -> option byte) (junk8 : list byte) x9 x13 x14 x15 x16 x17 y5 y6 y7 y28 y29 y30 y31,
  poison_env E m0 -> FRAME m0 junk8 -> stk asegs m0 lo (q + -64) ->
  munch [(q - 64, q)] m m0 -> wmono asegs m m0 -> mem_inv asegs m0 ->
  evt asegs Q (PST 0x5984c m0 x9 (wz size) (wz v) x13 x14 x15 x16 x17 y5 y6 y7 y28 y29 y30 y31).
Proof.
  intros Q K. intros until y31. intros PE FR ST MU WM MI0. pose proof QB as (LO & LOQ & QHI). pose proof AB as (AL & SL & S8 & AM & VB).
  unfold poison_range in AM. unfold SHADOW_OFF in *. pose proof PE as PE0. pe_split PE.
  zstep. zstep. if_cases K0; zify_cond K0.
  { exfalso. change 7 with (Z.ones 3) in K0. rewrite Z.land_ones in K0 by lia. change (2^3) with 8 in K0. lia. }
  do 3 zstep.
  do 4 zstep.
  replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879 in *
    by (vm_compute; reflexivity).
  zstep. if_cases K1; zify_cond K1.
  -   eapply poison_tail2; eassumption.
  - do 6 zstep.
    zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
    do 5 zstep.
    zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    zstep. if_cases K4; zify_cond K4; [| exfalso; lia].

    do 3 zstep. zstep. if_cases K5; zify_cond K5; [exfalso; lia|]. zstep. if_cases K6; zify_cond K6; [| exfalso; lia].
    eapply poison_tail2; eassumption.
Qed.

#[using="MI QB AB"] Lemma poison_head : forall Q, at948 Q -> forall (a3 a4 a5 a6 a7 : word),
  poison_env E m -> stk asegs m lo q ->
  evt asegs Q
      (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz poison_entry) fc None m (seg_rom asegs)).
Proof.
  intros Q K a3 a4 a5 a6 a7 PE ST. unfold poison_entry. pose proof QB as (LO & LOQ & QHI). pose proof AB as (AL & SL & S8 & AM & VB).
  unfold poison_range in AM. pose proof PE as PE0. pe_split PE.
  pose proof (munch_refl [(q - 64, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 64%nat ST.
  do 8 zstep.
  assert (PE1 : poison_env E m0) by pe_join.
  zstep. if_cases KV; zify_cond KV.
  -   eapply poison_tail1; try eassumption.
  - do 3 zstep.   zstep. if_false. eapply poison_tail1; try eassumption.
Qed.

#[using="size"] Lemma sh_beg_eq : SHADOW_OFF + addr ≫ 3 = sh addr.
Proof. unfold sh. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
#[using="v AB"] Lemma sh_end_eq : (addr + size - 8) ≫ 3 + 1 = addr / 8 + size / 8.
Proof.
  pose proof AB as (AL & SL & S8 & AM & VB). unfold poison_range in AM.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; nia.
Qed.
#[using="v AB"] Lemma sh_len_eq : ((addr + size - 8) ≫ 3 + 1) mod 18446744073709551616 - addr ≫ 3 = size / 8.
Proof.
  pose proof AB as (AL & SL & S8 & AM & VB). unfold poison_range in AM.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; nia). Z.div_mod_to_equations; nia.
Qed.

#[using="QB AB"] Lemma poison_memset_whole : forall (m0 : word -> option byte) (junk8 junk : list byte) x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 y5 y7 y28 y29 y30 y31,
  poison_env E m0 -> FRAME m0 junk8 -> stk asegs m0 lo (q + -64) ->
  munch W m m0 -> wmono asegs m m0 -> mem_inv asegs m0 ->
  rw_cells asegs m0 (sh addr) [CB (Z.to_nat (size / 8)) junk] ->
  bv_unsigned x11 mod 256 = v ->
  evt asegs poison_post
    (MS (mkR ra (wz (q + -64)) gp tp y5 (wz 0xa221c) y7 (wz (size / 8)) x9 (wz (sh addr)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (wz 0x59b90) fc None m0 (seg_rom asegs)).
Proof.
  intros until y31. intros PE FR ST MU WM MI0 SH XV. pose proof QB as (LO & LOQ & QHI). pose proof AB as (AL & SL & S8 & AM & VB).
  unfold poison_range in AM. unfold sh, SHADOW_OFF in *. pe_split PE.
  pose proof (unsigned_lit (addr / 8 + 2147450880) ltac:(lia)) as US. pose proof (unsigned_lit (size / 8) ltac:(lia)) as UL.
  do 10 zstep.
  release_frame FR ST q.
  call (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk); [rewrite US, UL; exact SH| assumption|].
  unfold poison_post, sh, SHADOW_OFF; finish; [pe_join|].
  lazymatch goal with P : rw_cells asegs _ (bv_unsigned _) _ |- _ => rewrite US, UL, XV in P; exact P end.
Qed.

#[using="QB AB"] Lemma poison_tail3 : forall junk,
  rw_cells asegs m (sh addr) [CB (Z.to_nat (size / 8)) junk] ->
  at948 poison_post.
Proof.
  intros junk SH. unfold at948. intros until y31. intros PE FR ST MU WM MI0. pose proof QB as (LO & LOQ & QHI). pose proof AB as (AL & SL & S8 & AM & VB).
  unfold poison_range in AM. pose proof PE as PE0. pe_split PE.
  apply (rw_cells_transport asegs [(q - 64, q)] m m0) in SH; [| exact MU| exact WM| unfold sh, SHADOW_OFF; cbn [disjoint_from]; simpl_sizes; lia].
  apply (munch_weaken [(q - 64, q)] W) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
  do 4 zstep.   if_false.
  do 5 zstep.
  rewrite sh_beg_eq, sh_len_eq.
  zstep.   if_cases KV; zify_cond KV.
  -   do 2 zstep.   eapply poison_memset_whole; try eassumption. rewrite unsigned_lit by lia. apply Z.mod_small. lia.
  -   do 4 zstep.
    if_cases KS; zify_cond KS; [| exfalso; clear - KS AM S8; Z.div_mod_to_equations; nia].
    do 2 zstep. eapply poison_memset_whole; try eassumption. rewrite unsigned_lit by lia. subst v. reflexivity.
Qed.

#[using="MI QB AB"] Lemma poison_shadow_spec_all : forall (a3 a4 a5 a6 a7 : word) (junk : list byte),
  poison_env E m -> stk asegs m lo q ->
  rw_cells asegs m (sh addr) [CB (Z.to_nat (size / 8)) junk] ->
  evt asegs poison_post
      (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz poison_entry) fc None m (seg_rom asegs)).
Proof. intros a3 a4 a5 a6 a7 junk PE ST SH. eapply poison_head; [exact (poison_tail3 junk SH)| exact PE| exact ST]. Qed.

#[using="MI QB AB"] Lemma poison_shadow_spec : forall (a3 a4 a5 a6 a7 : word) (junk : list byte),
  poison_env E m -> stk asegs m lo q ->
  (v <> 0 \/ size < 8 * 65536) ->
  rw_cells asegs m (sh addr) [CB (Z.to_nat (size / 8)) junk] ->
  evt asegs poison_post
      (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz poison_entry) fc None m (seg_rom asegs)).
Proof. intros a3 a4 a5 a6 a7 junk PE ST _ SH. exact (poison_shadow_spec_all a3 a4 a5 a6 a7 junk PE ST SH). Qed.

Section PA.
Variable H : word -> bool.
Hypothesis LOQ2 : lo <= q - 592.

Notation WA := [(q - 592, q); (sh addr, sh addr + size / 8)].

Definition poison_postA : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = poison_H addr size v H
    /\ munch WA m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'
    /\ rw_cells asegs m' (sh addr) [CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 v) (Z.to_nat (size / 8)))].

#[using="Type"] Lemma rw_cells_CB3 : forall (mm : word -> option byte) A n1 n2 n3 (b : byte),
  rw_cells asegs mm A [CB n1 (repeat b n1)] ->
  rw_cells asegs mm (A + Z.of_nat n1) [CB n2 (repeat b n2)] ->
  rw_cells asegs mm (A + Z.of_nat n1 + Z.of_nat n2) [CB n3 (repeat b n3)] ->
  rw_cells asegs mm A [CB (n1 + n2 + n3)%nat (repeat b (n1 + n2 + n3)%nat)].
Proof.
  intros mm A n1 n2 n3 b R1 R2 R3.
  pose proof (rw_cells_put3 asegs mm A [CB n1 (repeat b n1)] [CB n2 (repeat b n2)] [CB n3 (repeat b n3)]) as P.
  cbn [cells_size csize app] in P. rewrite !Nat.add_0_r in P. specialize (P R1 R2 R3).
  pose proof (rw_cells_merge asegs mm A [] [CB n1 (repeat b n1); CB n2 (repeat b n2); CB n3 (repeat b n3)] [] P) as M.
  cbn [cells_size csize cells_bytes cbytes app] in M. rewrite app_nil_r, Nat.add_0_r, <- !repeat_app, Nat.add_assoc in M. exact M.
Qed.

#[using="addr size"] Lemma rw_cells_CB0_nil : forall (mm : word -> option byte) A j, rw_cells asegs mm A [CB 0 j] -> j = [].
Proof. intros mm A j [[[W _] _] _]. cbn in W. destruct j; [reflexivity| cbn in W; lia]. Qed.

#[using="addr size"] Lemma pgup_ge x : x <= pgup x. Proof. unfold pgup. Z.div_mod_to_equations. nia. Qed.
#[using="addr size"] Lemma pgup_lt x : pgup x < x + 4096. Proof. unfold pgup. Z.div_mod_to_equations. nia. Qed.
#[using="addr size"] Lemma pgdn_le x : pgdn x <= x. Proof. unfold pgdn. Z.div_mod_to_equations. nia. Qed.
#[using="addr size"] Lemma pgdn_gt x : x - 4096 < pgdn x. Proof. unfold pgdn. Z.div_mod_to_equations. nia. Qed.
#[using="Type"] Lemma pgup_mod x : pgup x mod 4096 = 0. Proof. unfold pgup. apply Z_mod_mult. Qed.
#[using="Type"] Lemma pgdn_mod x : pgdn x mod 4096 = 0. Proof. unfold pgdn. apply Z_mod_mult. Qed.
#[using="Type"] Lemma pg_diff_mod x y : (pgdn y - pgup x) mod 4096 = 0.
Proof. unfold pgup, pgdn. rewrite <- Z.mul_sub_distr_r. apply Z_mod_mult. Qed.
#[using="addr size"] Lemma land_pgup x : 0 <= x -> x + 4096 < 2^64 -> Z.land (x + 4096 + -1) 18446744073709547520 = pgup x.
Proof. intros. rewrite land_m4096 by lia. unfold pgup. Z.div_mod_to_equations. nia. Qed.
#[using="addr size"] Lemma land_pgdn x : 0 <= x < 2^64 -> Z.land x 18446744073709547520 = pgdn x.
Proof. intros. rewrite land_m4096 by lia. unfold pgdn. Z.div_mod_to_equations. nia. Qed.

#[using="v AB"] Lemma sh_range : 0x7fff8000 <= sh addr /\ sh addr + size / 8 <= 0x10007fff8000.
Proof. pose proof AB as (AL & SL & S8 & AM & VB). unfold poison_range in AM. unfold sh, SHADOW_OFF. split; Z.div_mod_to_equations; nia. Qed.

Notation PB := (pgup (sh addr)).
Notation PE := (pgdn (sh addr + size / 8)).

#[using="QB AB LOQ2"] Lemma poison_memset_wholeA : forall (m0 : word -> option byte) (junk8 junk : list byte) x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 y5 y7 y28 y29 y30 y31,
  poison_remap addr size v = None ->
  poison_env E m0 -> FRAME m0 junk8 -> stk asegs m0 lo (q + -64) ->
  munch WA m m0 -> wmono asegs m m0 -> mem_inv asegs m0 ->
  rw_cells asegs m0 (sh addr) [CB (Z.to_nat (size / 8)) junk] ->
  bv_unsigned x11 mod 256 = v ->
  evt asegs (lzk H (Ret (Ok tt)) poison_postA)
    (MS (mkR ra (wz (q + -64)) gp tp y5 (wz 0xa221c) y7 (wz (size / 8)) x9 (wz (sh addr)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
        F (wz 0x59b90) fc None m0 (seg_rom asegs)).
Proof.
  intros until y31. intros PR PE FR ST MU WM MI0 SH XV. pose proof QB as (LO & LOQ & QHI). pose proof AB as (AL & SL & S8 & AM & VB).
  unfold poison_range in AM. pose proof sh_range as SR. pe_split PE.
  pose proof (unsigned_lit (sh addr) ltac:(lia)) as US. pose proof (unsigned_lit (size / 8) ltac:(lia)) as UL.
  do 10 zstep.
  release_frame FR ST q.
  call (memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ junk); [rewrite US, UL; exact SH| assumption|].
  lazymatch goal with P : rw_cells asegs _ (bv_unsigned _) _ |- _ => rewrite US, UL, XV in P end.
  lz_ret. unfold poison_postA, poison_H. rewrite PR. finish. reflexivity. pe_join.
Qed.

#[using="QB AB LOQ2"] Lemma poison_948A : forall junk,
  rw_cells asegs m (sh addr) [CB (Z.to_nat (size / 8)) junk] ->
  at948 (lzk H (poison_tree addr size v) poison_postA).
Proof.
  intros junk SH. unfold at948. intros until y31. intros PE FR ST MU WM MI0. pose proof QB as (LO & LOQ & QHI). pose proof AB as (AL & SL & S8 & AM & VB).
  unfold poison_range in AM. pose proof sh_range as SR. pose proof PE as PE0. pe_split PE.
  apply (rw_cells_transport asegs [(q - 64, q)] m m0) in SH; [| exact MU| exact WM| unfold sh, SHADOW_OFF; cbn [disjoint_from]; simpl_sizes; lia].
  apply (munch_weaken [(q - 64, q)] WA) in MU; [| unfold sub_fp; cbn [outside]; intros; lia].
  do 4 zstep.   if_false.
  do 5 zstep.
  rewrite sh_len_eq, sh_beg_eq.
  zstep.   if_cases KV; zify_cond KV.
  -   do 2 zstep. unfold poison_tree, poison_remap.
    eapply poison_memset_wholeA; try eassumption; [reflexivity|]. rewrite unsigned_lit by lia. apply Z.mod_small. lia.
  -   do 4 zstep.
    if_cases KS; zify_cond KS; [| exfalso; clear - KS AM S8; Z.div_mod_to_equations; nia].
    do 2 zstep. unfold poison_tree, poison_remap.
    eapply poison_memset_wholeA; try eassumption; [reflexivity|]. rewrite unsigned_lit by lia. subst v. reflexivity.
Qed.

#[using="MI QB AB LOQ2"] Lemma poison_shadow_specA : forall (a3 a4 a5 a6 a7 : word) (junk : list byte),
  mclean H m -> poison_env E m -> stk asegs m lo q ->
  rw_cells asegs m (sh addr) [CB (Z.to_nat (size / 8)) junk] ->
  implA H (poison_tree addr size v) poison_postA
      (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz addr) (wz size) (wz v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz poison_entry) fc None m (seg_rom asegs)).
Proof. intros a3 a4 a5 a6 a7 junk C PE ST SH. lz_go. eapply poison_head; [exact (poison_948A junk SH)| exact PE| exact ST]. Qed.
End PA.
End P.
