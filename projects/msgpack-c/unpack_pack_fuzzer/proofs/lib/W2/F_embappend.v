(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ABytes AFrameD RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammapz. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aunmap F_adepot1 F_aintal F_irt.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.W2 Require Import F_mmapordie F_embrealloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation EMBA_STACK := 448 (only parsing).
Notation AEMBz := 0xd9328 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition emb_append_entry := 0x60de8.

Ltac emb_lock ST :=
  carve_frame 96%nat ST;
  do 12 step;
  do 5 step;
  step; zstep; zstep; zstep; zstep;
  step;
  zstep; zstep; zstep; zstep; zstep; zstep; zstep;
  zstep; step; if_lit;
  zstep; zstep;
  amo_step;
  step; if_lit;
  amo_step;
  step; if_lit;
  step; if_lit.

Ltac emb_unlock :=
  step;
  do 4 step; zstep; zstep; zstep;
  step;
  zstep; zstep; zstep; step; zstep;
  step;
  zstep; zstep; step; if_lit;
  zstep; step; if_lit;
  zstep; zstep; zstep; zstep; zstep; zstep; zstep;
  step; if_lit;
  amo_step;
  step; if_lit;
  amo_step;
  step; if_lit;
  step; if_lit;
  step; if_lit;
  do 13 step.

Definition emb_fit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo d cap sz len : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d, d + cap)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0xd9328 [C8 (Z_to_bv 64 0xd9348)]
    /\ rw_cells asegs m' 0xd9338 [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' 0xd9348 [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 (sz + len))]
    /\ junk_at m' d cap.

Lemma emb_fit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo d cap sz TXT : Z) (str : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBA_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 TXT ->
  bytes_at asegs m TXT (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str ->
  bv_unsigned sp <= TXT -> TXT + Z.of_nat (length str) + 1 < 2^63 -> (1 <= length str <= 400)%nat ->
  rw_cells asegs m 0xd9328 [C8 (Z_to_bv 64 0xd9348)] ->
  rw_cells asegs m 0xd9338 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd9348 [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 sz)] ->
  junk_at m d cap -> AIMG_HI <= d -> d + cap <= ATOP -> 0 <= sz -> sz + Z.of_nat (length str) <= cap ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d cap -> rng RNG TXT (Z.of_nat (length str) + 1) ->
  evtF asegs RNG (emb_fit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo d cap sz (Z.of_nat (length str)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_append_entry) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros ST CEIL LO MI -> TXTB NOZ TXTLO TXTHI LEN PTR MTX VEC OLD DLO DHI SZ0 FIT RA RIMG RSTK ROLD RTXT.
  unfold AIMG_HI, emb_append_entry in *. word_range sp SPR. pose proof atop_range as ATR.
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).

  destruct (junk_split m d sz (cap - sz) ltac:(replace (sz + (cap - sz)) with cap by (clear; lia); exact OLD) SZ0 ltac:(clear -FIT LENR; lia)) as [J1 J23].
  destruct (junk_split m (d + sz) len (cap - sz - len) ltac:(replace (len + (cap - sz - len)) with (cap - sz) by (clear; lia); exact J23) ltac:(clear -LENR; lia) ltac:(clear -FIT; lia)) as [J2 J3].
  clear OLD J23. destruct J1 as [j1 J1]. destruct J2 as [j2 J2]. destruct J3 as [j3 J3].
  pose proof (munch_refl [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d, d + cap)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  emb_lock ST.
  step. step. if_lit.
  step.
  step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (TXTc : bytes_at asegs mc (bv_unsigned (Z_to_bv 64 TXT)) (str ++ Z_to_bv 8 0 :: [])) by (rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); assumption) end.
  call istrlen_spec; [ eassumption | exact TXTc | exact NOZ | rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); exact RTXT | ].
  fold len. clear TXTc.
  step. step.
  step. zstep.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 LEN SZ0 FIT DHI ATR. subst len. lia. }
  step.
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 LEN SZ0 FIT DHI ATR. subst len. lia. }
  step. zstep. zstep. step.
  setreg 12 (Z_to_bv 64 len) ltac:(f_equal; clear -LENR SZ0 DHI ATR FIT; lia).
  step.
  call (F_aintal.imemset_spec (d + sz) len); [reflexivity| reflexivity| reflexivity| clear -DLO SZ0; lia| clear -LENR; lia| clear -DHI FIT ATR; lia| exact J2| assumption|].
  step.
  step. step. zstep. step. step.
  step.
  match goal with H : rw_cells asegs _ (d + sz) [CB (Z.to_nat len) ?zz] |- _ =>
    replace (Z.to_nat len) with (length str) in H by (subst len; rewrite Nat2Z.id; reflexivity); rename H into DSTc end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply (imemcpy_specZ RNG) with (src := str) (rest := [Z_to_bv 8 0]);
      [ eassumption | eassumption | exact DSTc | reflexivity
      | rewrite length_app; cbn [length]; fold len; clear -TXTLO CEIL LO DHI FIT LENR SPR; lia
      | fold len; clear -DHI FIT ATR LENR SZ0; lia
      | rewrite length_app; cbn [length]; fold len; clear -TXTHI; lia
      | fold len; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact RTXT|]; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact ROLD|]; clear -SZ0 FIT LENR; lia ]
    | post_call asegs mc ]
  end.
  emb_unlock.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold emb_fit_post.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact PTR|]. split; [exact MTX|].
  split. { replace (sz + len) with (len + sz) by (clear; lia). exact VEC. }
  replace cap with (sz + (cap - sz)) by (clear; lia). apply junk_merge; [exists j1; exact J1| | exact SZ0| clear -FIT LENR; lia].
  replace (cap - sz) with (len + (cap - sz - len)) by (clear; lia). apply junk_merge; [| exists j3; exact J3| clear -LENR; lia| clear -FIT; lia].
  exists str. replace (Z.to_nat len) with (length str) by (subst len; rewrite Nat2Z.id; reflexivity). exact POST.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition emb_first_post (RNG : footprint) (sp : word) (lo a len : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + 65536 <= ATOP
  /\ munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (a, a + 65536)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' 0xd9328 [C8 (Z_to_bv 64 0xd9348)]
  /\ rw_cells asegs m' 0xd9338 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' 0xd9348 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 65536); C8 (Z_to_bv 64 len)]
  /\ junk_at m' a 65536
  /\ rng RNG' a 65536 /\ rng RNG' (shad a) (shlen 65536)
  /\ rmap_cells m'.

Lemma emb_first_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo TXT : Z) (str : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBA_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 TXT ->
  bytes_at asegs m TXT (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str ->
  bv_unsigned sp <= TXT -> TXT + Z.of_nat (length str) + 1 < 2^63 -> (1 <= length str <= 400)%nat ->
  rw_cells asegs m 0xd9328 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd9338 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd9348 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  4096 <= bv_unsigned ra ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG TXT (Z.of_nat (length str) + 1) ->
  (forall a, FRESH a = true -> 0 < a -> a + 65536 <= ATOP -> AIMG_HI <= a) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + 65536 <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> emb_first_post RNG sp lo a (Z.of_nat (length str)) m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 65536 3 34) (adec_mmap ATOP 65536 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_append_entry) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros ST CEIL LO MI -> TXTB NOZ TXTLO TXTHI LEN PTR MTX VEC RA RC RIMG RSTK RTXT FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI, emb_append_entry in *. word_range sp SPR. pose proof atop_range as ATR.
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  pose proof (munch_refl [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  emb_lock ST.
  step. step. if_lit.
  zstep. step. step. step. step.
  step. step.
  step.
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (emb_realloc0_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm 65536 65536 lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => unfold rmap_cells; repeat (split; [assumption|]); assumption
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ _ => eassumption
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO; lia).
  all: try reflexivity.
  { intros a HFR A0 ACE. exact (FROK a HFR A0 ACE). }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }

  intros a RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & VEC2 & ZCH & RCH & RSCH & RC2).
  pose proof (FROK a HFR A0 ACE) as DLO.
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  assert (MUA : munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (a, a + 65536)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  assert (WMA : wmono asegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  clear MU WM.
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO DLO A0 ACE; lia).
  xport PTR MU2 WM2 ltac:(clear -SPR CEIL LO DLO A0 ACE; lia).
  xport MTX MU2 WM2 ltac:(clear -SPR CEIL LO DLO A0 ACE; lia).
  eapply bytes_at_transport in TXTB; [| exact MU2 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; fold len; clear -SPR CEIL LO DLO A0 ACE TXTLO LENR; lia].
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RTXT.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2).
  clear MU2 WM2 VEC.

  remember 0 as sz eqn:SZE in VEC2. assert (SZ0 : 0 <= sz) by (subst sz; clear; lia).
  set (d := a) in *. set (cap := 65536) in VEC2.
  assert (DHI : d + cap <= ATOP) by (subst d cap; exact ACE).
  assert (FIT : sz + len <= cap) by (subst sz cap; clear -LENR; lia).
  assert (ROLD : rng RNG' d cap) by (subst d cap; exact RCH).
  change (rw_cells asegs m2 a [CB (Z.to_nat 65536) (repeat (Z_to_bv 8 0) (Z.to_nat 65536))]) with (fill_at m2 d cap 0) in ZCH.
  apply fill_is_junk in ZCH.
  destruct (junk_split m2 d sz (cap - sz) ltac:(replace (sz + (cap - sz)) with cap by (clear; lia); exact ZCH) SZ0 ltac:(clear -FIT LENR; lia)) as [J1 J23].
  destruct (junk_split m2 (d + sz) len (cap - sz - len) ltac:(replace (len + (cap - sz - len)) with (cap - sz) by (clear; lia); exact J23) ltac:(clear -LENR; lia) ltac:(clear -FIT; lia)) as [J2 J3].
  clear ZCH J23. destruct J1 as [j1 J1]. destruct J2 as [j2 J2]. destruct J3 as [j3 J3].
  rename VEC2 into VEC. rename MUA into MU. rename WMA into WM. rename ST2 into STX.
  iprefix.
  replace (ret_pc (Z_to_bv 64 397084)) with (Z_to_bv 64 397084 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step.
  step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (TXTc : bytes_at asegs mc (bv_unsigned (Z_to_bv 64 TXT)) (str ++ Z_to_bv 8 0 :: [])) by (rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); assumption) end.
  call istrlen_spec; [ eassumption | exact TXTc | exact NOZ | rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); exact RTXT | ].
  fold len. clear TXTc.
  step. step.
  step. zstep.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 LENR SZ0 FIT DHI ATR. lia. }
  step.
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 LENR SZ0 FIT DHI ATR. subst cap. lia. }
  step. zstep. zstep. step.
  setreg 12 (Z_to_bv 64 len) ltac:(f_equal; clear -LENR SZ0 DHI ATR FIT; lia).
  step.
  call (F_aintal.imemset_spec (d + sz) len); [reflexivity| reflexivity| reflexivity| clear -DLO SZ0; lia| clear -LENR; lia| clear -DHI FIT ATR; lia| exact J2| assumption|].
  step.
  step. step. zstep. step. step.
  step.
  match goal with H : rw_cells asegs _ (d + sz) [CB (Z.to_nat len) ?zz] |- _ =>
    replace (Z.to_nat len) with (length str) in H by (subst len; rewrite Nat2Z.id; reflexivity); rename H into DSTc end.
  lazymatch goal with |- evtF _ _ ?RR (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply imemcpy_specZ with (src := str) (rest := [Z_to_bv 8 0]);
      [ eassumption | eassumption | exact DSTc | reflexivity
      | rewrite length_app; cbn [length]; fold len; clear -TXTLO CEIL LO DHI FIT LENR SPR; lia
      | fold len; clear -DHI FIT ATR LENR SZ0; lia
      | rewrite length_app; cbn [length]; fold len; clear -TXTHI; lia
      | fold len; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact RTXT|]; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact ROLD|]; clear -SZ0 FIT LENR; lia ]
    | post_call asegs mc ]
  end.
  emb_unlock.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -96) _ |- _ => release_frame FRM STX (bv_unsigned sp) end.
  apply evtF_done. eapply KONT; [exact HFR|].
  unfold emb_first_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STX|]. split; [exact PTR|]. split; [exact MTX|].
  split. { replace (Z_to_bv 64 len) with (Z_to_bv 64 (len + sz)) by (f_equal; subst sz; clear; lia). exact VEC. }
  split. { replace 65536 with (sz + (cap - sz)) by (subst sz cap; clear; lia). apply junk_merge; [exists j1; exact J1| | exact SZ0| clear -FIT LENR; lia].
           replace (cap - sz) with (len + (cap - sz - len)) by (clear; lia). apply junk_merge; [| exists j3; exact J3| clear -LENR; lia| clear -FIT; lia].
           exists str. replace (Z.to_nat len) with (length str) by (subst len; rewrite Nat2Z.id; reflexivity). assumption. }
  split; [exact RCH|]. split; [exact RSCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition emb_grow_post (RNG : footprint) (sp : word) (lo d0 cap0 sz len a ncap : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + ncap <= ATOP
  /\ munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d0, d0 + cap0); (a, a + ncap)]%Z m m' /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' 0xd9328 [C8 (Z_to_bv 64 0xd9348)]
  /\ rw_cells asegs m' 0xd9338 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m' 0xd9348 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ncap); C8 (Z_to_bv 64 (sz + len))]
  /\ junk_at m' a ncap
  /\ rng RNG' a ncap
  /\ rmap_cells m'.

Lemma emb_grow_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo d0 cap0 sz TXT ncap : Z) (str : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBA_STACK ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 TXT ->
  bytes_at asegs m TXT (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str ->
  bv_unsigned sp <= TXT -> TXT + Z.of_nat (length str) + 1 < 2^63 -> (1 <= length str <= 400)%nat ->
  rw_cells asegs m 0xd9328 [C8 (Z_to_bv 64 0xd9348)] ->
  rw_cells asegs m 0xd9338 [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0xd9348 [C8 (Z_to_bv 64 d0); C8 (Z_to_bv 64 cap0); C8 (Z_to_bv 64 sz)] ->
  junk_at m d0 cap0 -> AIMG_HI <= d0 -> d0 + cap0 <= ATOP -> 0 < cap0 -> cap0 mod 4096 = 0 -> cap0 < 2^38 ->
  1 <= sz -> sz <= cap0 -> cap0 < sz + Z.of_nat (length str) ->
  ncap = (sz + Z.of_nat (length str) + 4095) / 4096 * 4096 ->
  4096 <= bv_unsigned ra ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d0 cap0 -> rng RNG TXT (Z.of_nat (length str) + 1) ->
  (forall a, FRESH a = true -> 0 < a -> a + ncap <= ATOP -> AIMG_HI <= a /\ (a + ncap <= d0 \/ d0 + cap0 <= a)) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ncap <= ATOP -> fp_le RNG RNG' ->
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a, FRESH a = true -> K a = ebind (enode (NMunmap d0 cap0) (adec_munmap d0 cap0)) (K2 a)) ->
  (forall a RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> emb_grow_post RNG sp lo d0 cap0 sz (Z.of_nat (length str)) a ncap m RNG' m' ->
      implS asegs RNG' (K2 a 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ncap 3 34) (adec_mmap ATOP ncap 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_append_entry) fc None m (seg_rom asegs)).
Proof.
  intros until str. intros ST CEIL LO MI -> TXTB NOZ TXTLO TXTHI LEN PTR MTX VEC OLD D0LO D0HI C0POS C0AL C0HI SZ1 SZC NOFIT NCAP RA RC RIMG RSTK ROLD0 RTXT FROK UNR SHAPE KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI, emb_append_entry in *. word_range sp SPR. pose proof atop_range as ATR.
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  assert (NC : ncap mod 4096 = 0 /\ sz + len <= ncap /\ ncap < sz + len + 4096) by (rewrite NCAP; clear -SZ1 LENR; Z.div_mod_to_equations; lia).
  destruct NC as (NCM & NCL & NCH).
  destruct OLD as [junk OLD].
  pose proof (munch_refl [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  iprefix.
  emb_lock ST.
  step. step. if_lit.
  assert (SZ0 : 0 <= sz) by (clear -SZ1; lia).
  step.
  step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (TXTc : bytes_at asegs mc (bv_unsigned (Z_to_bv 64 TXT)) (str ++ Z_to_bv 8 0 :: [])) by (rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); assumption) end.
  call istrlen_spec; [ eassumption | exact TXTc | exact NOZ | rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); exact RTXT | ].
  fold len. clear TXTc.
  step. step.
  step. zstep.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 LENR SZ1 SZC D0HI ATR. lia. }
  step.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 LENR SZ1 SZC NOFIT D0HI ATR C0HI. lia. }
  step. step.
  step.
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (emb_realloc1_spec RNG K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm d0 cap0 sz (len + sz) ncap lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => unfold rmap_cells; repeat (split; [assumption|]); assumption
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ _ => eassumption
       | |- junk_at _ _ _ => eexists; eassumption
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       | |- rng _ _ _ => exact ROLD0
       | |- _ = _ / _ * _ => rewrite NCAP; f_equal; f_equal; clear; lia
       end.
  all: try (unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO D0LO D0HI C0POS C0AL C0HI SZ1 SZC LENR; lia).
  { intros a HFR A0 ACE. exact (FROK a HFR A0 ACE). }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }
  { exact SHAPE. }

  intros a RNG' m3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & AAL & A0 & ACE & MU2 & MI2 & ST2 & VEC2 & JNK & RCH & RC2).
  destruct (FROK a HFR A0 ACE) as [DLO ADJ].
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  assert (MUA : munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d0, d0 + cap0); (a, a + ncap)]%Z m m3).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  clear MU WM.
  eapply cells_frameD in FR; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply cells_frameD in PTR; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply cells_frameD in MTX; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply bytes_at_transport in TXTB; [| exact MU2 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; fold len; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI TXTLO LENR; lia].
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RTXT.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2).
  clear MU2 VEC OLD.
  set (d := a) in *. set (cap := ncap) in VEC2, JNK.
  assert (DHI : d + cap <= ATOP) by (subst d cap; exact ACE).
  assert (FIT : sz + len <= cap) by (subst cap; exact NCL).
  assert (ROLD : rng RNG' d cap) by (subst d cap; exact RCH).
  destruct (junk_split m3 d sz (cap - sz) ltac:(replace (sz + (cap - sz)) with cap by (clear; lia); exact JNK) SZ0 ltac:(clear -FIT LENR; lia)) as [J1 J23].
  destruct (junk_split m3 (d + sz) len (cap - sz - len) ltac:(replace (len + (cap - sz - len)) with (cap - sz) by (clear; lia); exact J23) ltac:(clear -LENR; lia) ltac:(clear -FIT; lia)) as [J2 J3].
  clear JNK J23. destruct J1 as [j1 J1]. destruct J2 as [j2 J2]. destruct J3 as [j3 J3].
  rename VEC2 into VEC. rename MUA into MU. rename ST2 into STX.
  iprefix.
  replace (ret_pc (Z_to_bv 64 397136)) with (Z_to_bv 64 397136 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step.
  step. zstep. zstep. step.
  setreg 12 (Z_to_bv 64 len) ltac:(f_equal; clear -LENR SZ0 DHI ATR FIT; lia).
  step.
  call (F_aintal.imemset_spec (d + sz) len); [reflexivity| reflexivity| reflexivity| clear -DLO SZ0; lia| clear -LENR; lia| clear -DHI FIT ATR; lia| exact J2| assumption|].
  step.
  step. step. zstep. step. step.
  step.
  match goal with H : rw_cells asegs _ (d + sz) [CB (Z.to_nat len) ?zz] |- _ =>
    replace (Z.to_nat len) with (length str) in H by (subst len; rewrite Nat2Z.id; reflexivity); rename H into DSTc end.
  lazymatch goal with |- evtF _ _ ?RR (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply imemcpy_specZ with (src := str) (rest := [Z_to_bv 8 0]);
      [ eassumption | eassumption | exact DSTc | reflexivity
      | rewrite length_app; cbn [length]; fold len; clear -TXTLO CEIL LO DHI FIT LENR SPR; lia
      | fold len; clear -DHI FIT ATR LENR SZ0; lia
      | rewrite length_app; cbn [length]; fold len; clear -TXTHI; lia
      | fold len; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact RTXT|]; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact ROLD|]; clear -SZ0 FIT LENR; lia ]
    | post_call asegs mc ]
  end.
  emb_unlock.
  lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -96) _ |- _ => release_frame FRM STX (bv_unsigned sp) end.
  apply evtF_done. eapply KONT; [exact HFR|].
  unfold emb_grow_post.
  split; [exact FPLE|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MU|]. split; [assumption|]. split; [exact STX|]. split; [exact PTR|]. split; [exact MTX|].
  split. { replace (sz + len) with (len + sz) by (clear; lia). exact VEC. }
  split. { replace ncap with (sz + (cap - sz)) by (subst cap; clear; lia). apply junk_merge; [exists j1; exact J1| | exact SZ0| clear -FIT LENR; lia].
           replace (cap - sz) with (len + (cap - sz - len)) by (clear; lia). apply junk_merge; [| exists j3; exact J3| clear -LENR; lia| clear -FIT; lia].
           exists str. replace (Z.to_nat len) with (length str) by (subst len; rewrite Nat2Z.id; reflexivity). assumption. }
  split; [exact RCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB ARepKit.TwinB ABytes.TwinB AFrameD.TwinB RT_stubs.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammapz. Import F_aunmap.TwinB F_adepot1.TwinB F_aintal.TwinB F_irt.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import F_mmapordie.TwinB F_embrealloc.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation EMBA_STACK := 448 (only parsing).
Notation AEMBz := 0xdb4e8 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition emb_append_entry := 0x61778.

Ltac emb_lock ST :=
  carve_frame 96%nat ST;
  do 12 step;
  do 5 step;
  step; zstep; zstep; zstep; zstep;
  step;
  zstep; zstep; zstep; zstep; zstep; zstep; zstep;
  zstep; step; if_lit;
  zstep; zstep;
  amo_step;
  step; if_lit;
  amo_step;
  step; if_lit;
  step; if_lit.

Ltac emb_unlock :=
  step;
  do 4 step; zstep; zstep; zstep;
  step;
  zstep; zstep; zstep; step; zstep;
  step;
  zstep; zstep; step; if_lit;
  zstep; step; if_lit;
  zstep; zstep; zstep; zstep; zstep; zstep; zstep;
  step; if_lit;
  amo_step;
  step; if_lit;
  amo_step;
  step; if_lit;
  step; if_lit;
  step; if_lit;
  do 13 step.

Definition emb_fit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo d cap sz len : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d, d + cap)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)]
    /\ rw_cells bsegs m' 0xdb4f8 [C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0xdb508 [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 (sz + len))]
    /\ junk_at m' d cap.

Lemma emb_fit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo d cap sz TXT : Z) (str : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBA_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 TXT ->
  bytes_at bsegs m TXT (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str ->
  bv_unsigned sp <= TXT -> TXT + Z.of_nat (length str) + 1 < 2^63 -> (1 <= length str <= 400)%nat ->
  rw_cells bsegs m 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)] ->
  rw_cells bsegs m 0xdb4f8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xdb508 [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 sz)] ->
  junk_at m d cap -> AIMG_HI <= d -> d + cap <= ATOP -> 0 <= sz -> sz + Z.of_nat (length str) <= cap ->
  4096 <= bv_unsigned ra ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d cap -> rng RNG TXT (Z.of_nat (length str) + 1) ->
  evtF bsegs RNG (emb_fit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo d cap sz (Z.of_nat (length str)) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_append_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until str. intros ST CEIL LO MI -> TXTB NOZ TXTLO TXTHI LEN PTR MTX VEC OLD DLO DHI SZ0 FIT RA RIMG RSTK ROLD RTXT.
  unfold AIMG_HI, emb_append_entry in *. word_range sp SPR. pose proof atop_range as ATR.
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).

  destruct (junk_split m d sz (cap - sz) ltac:(replace (sz + (cap - sz)) with cap by (clear; lia); exact OLD) SZ0 ltac:(clear -FIT LENR; lia)) as [J1 J23].
  destruct (junk_split m (d + sz) len (cap - sz - len) ltac:(replace (len + (cap - sz - len)) with (cap - sz) by (clear; lia); exact J23) ltac:(clear -LENR; lia) ltac:(clear -FIT; lia)) as [J2 J3].
  clear OLD J23. destruct J1 as [j1 J1]. destruct J2 as [j2 J2]. destruct J3 as [j3 J3].
  pose proof (munch_refl [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d, d + cap)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  emb_lock ST.
  step. step. if_lit.
  step.
  step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (TXTc : bytes_at bsegs mc (bv_unsigned (Z_to_bv 64 TXT)) (str ++ Z_to_bv 8 0 :: [])) by (rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); assumption) end.
  call istrlen_spec; [ eassumption | exact TXTc | exact NOZ | rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); exact RTXT | ].
  fold len. clear TXTc.
  step. step.
  step. zstep.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 LEN SZ0 FIT DHI ATR. subst len. lia. }
  step.
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 LEN SZ0 FIT DHI ATR. subst len. lia. }
  step. zstep. zstep. step.
  setreg 12 (Z_to_bv 64 len) ltac:(f_equal; clear -LENR SZ0 DHI ATR FIT; lia).
  step.
  call (F_aintal.TwinB.imemset_spec (d + sz) len); [reflexivity| reflexivity| reflexivity| clear -DLO SZ0; lia| clear -LENR; lia| clear -DHI FIT ATR; lia| exact J2| assumption|].
  step.
  step. step. zstep. step. step.
  step.
  match goal with H : rw_cells bsegs _ (d + sz) [CB (Z.to_nat len) ?zz] |- _ =>
    replace (Z.to_nat len) with (length str) in H by (subst len; rewrite Nat2Z.id; reflexivity); rename H into DSTc end.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply (imemcpy_specZ RNG) with (src := str) (rest := [Z_to_bv 8 0]);
      [ eassumption | eassumption | exact DSTc | reflexivity
      | rewrite length_app; cbn [length]; fold len; clear -TXTLO CEIL LO DHI FIT LENR SPR; lia
      | fold len; clear -DHI FIT ATR LENR SZ0; lia
      | rewrite length_app; cbn [length]; fold len; clear -TXTHI; lia
      | fold len; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact RTXT|]; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact ROLD|]; clear -SZ0 FIT LENR; lia ]
    | post_call bsegs mc ]
  end.
  emb_unlock.
  release_frame FR ST (bv_unsigned sp).
  apply evtF_done. unfold emb_fit_post.
  do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact PTR|]. split; [exact MTX|].
  split. { replace (sz + len) with (len + sz) by (clear; lia). exact VEC. }
  replace cap with (sz + (cap - sz)) by (clear; lia). apply junk_merge; [exists j1; exact J1| | exact SZ0| clear -FIT LENR; lia].
  replace (cap - sz) with (len + (cap - sz - len)) by (clear; lia). apply junk_merge; [| exists j3; exact J3| clear -LENR; lia| clear -FIT; lia].
  exists str. replace (Z.to_nat len) with (length str) by (subst len; rewrite Nat2Z.id; reflexivity). exact POST.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition emb_first_post (RNG : footprint) (sp : word) (lo a len : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + 65536 <= ATOP
  /\ munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (a, a + 65536)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)]
  /\ rw_cells bsegs m' 0xdb4f8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' 0xdb508 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 65536); C8 (Z_to_bv 64 len)]
  /\ junk_at m' a 65536
  /\ rng RNG' a 65536 /\ rng RNG' (shad a) (shlen 65536)
  /\ rmap_cells m'.

Lemma emb_first_spec : forall RNG {R} (K : Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo TXT : Z) (str : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBA_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 TXT ->
  bytes_at bsegs m TXT (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str ->
  bv_unsigned sp <= TXT -> TXT + Z.of_nat (length str) + 1 < 2^63 -> (1 <= length str <= 400)%nat ->
  rw_cells bsegs m 0xdb4e8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xdb4f8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xdb508 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  4096 <= bv_unsigned ra ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG TXT (Z.of_nat (length str) + 1) ->
  (forall a, FRESH a = true -> 0 < a -> a + 65536 <= ATOP -> AIMG_HI <= a) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + 65536 <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> emb_first_post RNG sp lo a (Z.of_nat (length str)) m RNG' m' ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 65536 3 34) (adec_mmap ATOP 65536 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_append_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until str. intros ST CEIL LO MI -> TXTB NOZ TXTLO TXTHI LEN PTR MTX VEC RA RC RIMG RSTK RTXT FROK UNR KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI, emb_append_entry in *. word_range sp SPR. pose proof atop_range as ATR.
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  pose proof (munch_refl [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  emb_lock ST.
  step. step. if_lit.
  zstep. step. step. step. step.
  step. step.
  step.
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (emb_realloc0_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm 65536 65536 lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => unfold rmap_cells; repeat (split; [assumption|]); assumption
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ _ => eassumption
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO; lia).
  all: try reflexivity.
  { intros a HFR A0 ACE. exact (FROK a HFR A0 ACE). }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }

  intros a RNG' m2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & VEC2 & ZCH & RCH & RSCH & RC2).
  pose proof (FROK a HFR A0 ACE) as DLO.
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  assert (MUA : munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (a, a + 65536)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  assert (WMA : wmono bsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  clear MU WM.
  xport FR MU2 WM2 ltac:(clear -SPR CEIL LO DLO A0 ACE; lia).
  xport PTR MU2 WM2 ltac:(clear -SPR CEIL LO DLO A0 ACE; lia).
  xport MTX MU2 WM2 ltac:(clear -SPR CEIL LO DLO A0 ACE; lia).
  eapply bytes_at_transport in TXTB; [| exact MU2 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; fold len; clear -SPR CEIL LO DLO A0 ACE TXTLO LENR; lia].
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RTXT.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2).
  clear MU2 WM2 VEC.

  remember 0 as sz eqn:SZE in VEC2. assert (SZ0 : 0 <= sz) by (subst sz; clear; lia).
  set (d := a) in *. set (cap := 65536) in VEC2.
  assert (DHI : d + cap <= ATOP) by (subst d cap; exact ACE).
  assert (FIT : sz + len <= cap) by (subst sz cap; clear -LENR; lia).
  assert (ROLD : rng RNG' d cap) by (subst d cap; exact RCH).
  change (rw_cells bsegs m2 a [CB (Z.to_nat 65536) (repeat (Z_to_bv 8 0) (Z.to_nat 65536))]) with (fill_at m2 d cap 0) in ZCH.
  apply fill_is_junk in ZCH.
  destruct (junk_split m2 d sz (cap - sz) ltac:(replace (sz + (cap - sz)) with cap by (clear; lia); exact ZCH) SZ0 ltac:(clear -FIT LENR; lia)) as [J1 J23].
  destruct (junk_split m2 (d + sz) len (cap - sz - len) ltac:(replace (len + (cap - sz - len)) with (cap - sz) by (clear; lia); exact J23) ltac:(clear -LENR; lia) ltac:(clear -FIT; lia)) as [J2 J3].
  clear ZCH J23. destruct J1 as [j1 J1]. destruct J2 as [j2 J2]. destruct J3 as [j3 J3].
  rename VEC2 into VEC. rename MUA into MU. rename WMA into WM. rename ST2 into STX.
  iprefix.
  replace (ret_pc (Z_to_bv 64 399532)) with (Z_to_bv 64 399532 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step.
  step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (TXTc : bytes_at bsegs mc (bv_unsigned (Z_to_bv 64 TXT)) (str ++ Z_to_bv 8 0 :: [])) by (rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); assumption) end.
  call istrlen_spec; [ eassumption | exact TXTc | exact NOZ | rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); exact RTXT | ].
  fold len. clear TXTc.
  step. step.
  step. zstep.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 LENR SZ0 FIT DHI ATR. lia. }
  step.
  step. if_cases K1; zify_cond K1. 2: { exfalso. clear -K1 LENR SZ0 FIT DHI ATR. subst cap. lia. }
  step. zstep. zstep. step.
  setreg 12 (Z_to_bv 64 len) ltac:(f_equal; clear -LENR SZ0 DHI ATR FIT; lia).
  step.
  call (F_aintal.TwinB.imemset_spec (d + sz) len); [reflexivity| reflexivity| reflexivity| clear -DLO SZ0; lia| clear -LENR; lia| clear -DHI FIT ATR; lia| exact J2| assumption|].
  step.
  step. step. zstep. step. step.
  step.
  match goal with H : rw_cells bsegs _ (d + sz) [CB (Z.to_nat len) ?zz] |- _ =>
    replace (Z.to_nat len) with (length str) in H by (subst len; rewrite Nat2Z.id; reflexivity); rename H into DSTc end.
  lazymatch goal with |- evtF _ _ ?RR (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply imemcpy_specZ with (src := str) (rest := [Z_to_bv 8 0]);
      [ eassumption | eassumption | exact DSTc | reflexivity
      | rewrite length_app; cbn [length]; fold len; clear -TXTLO CEIL LO DHI FIT LENR SPR; lia
      | fold len; clear -DHI FIT ATR LENR SZ0; lia
      | rewrite length_app; cbn [length]; fold len; clear -TXTHI; lia
      | fold len; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact RTXT|]; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact ROLD|]; clear -SZ0 FIT LENR; lia ]
    | post_call bsegs mc ]
  end.
  emb_unlock.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -96) _ |- _ => release_frame FRM STX (bv_unsigned sp) end.
  apply evtF_done. eapply KONT; [exact HFR|].
  unfold emb_first_post.
  split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STX|]. split; [exact PTR|]. split; [exact MTX|].
  split. { replace (Z_to_bv 64 len) with (Z_to_bv 64 (len + sz)) by (f_equal; subst sz; clear; lia). exact VEC. }
  split. { replace 65536 with (sz + (cap - sz)) by (subst sz cap; clear; lia). apply junk_merge; [exists j1; exact J1| | exact SZ0| clear -FIT LENR; lia].
           replace (cap - sz) with (len + (cap - sz - len)) by (clear; lia). apply junk_merge; [| exists j3; exact J3| clear -LENR; lia| clear -FIT; lia].
           exists str. replace (Z.to_nat len) with (length str) by (subst len; rewrite Nat2Z.id; reflexivity). assumption. }
  split; [exact RCH|]. split; [exact RSCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.

Definition emb_grow_post (RNG : footprint) (sp : word) (lo d0 cap0 sz len a ncap : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'
  /\ a mod 4096 = 0 /\ 0 < a /\ a + ncap <= ATOP
  /\ munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d0, d0 + cap0); (a, a + ncap)]%Z m m' /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)]
  /\ rw_cells bsegs m' 0xdb4f8 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' 0xdb508 [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ncap); C8 (Z_to_bv 64 (sz + len))]
  /\ junk_at m' a ncap
  /\ rng RNG' a ncap
  /\ rmap_cells m'.

Lemma emb_grow_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R)) (Q : R -> footprint -> machine_state -> Prop)
    (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo d0 cap0 sz TXT ncap : Z) (str : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - EMBA_STACK ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 TXT ->
  bytes_at bsegs m TXT (str ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0) str ->
  bv_unsigned sp <= TXT -> TXT + Z.of_nat (length str) + 1 < 2^63 -> (1 <= length str <= 400)%nat ->
  rw_cells bsegs m 0xdb4e8 [C8 (Z_to_bv 64 0xdb508)] ->
  rw_cells bsegs m 0xdb4f8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xdb508 [C8 (Z_to_bv 64 d0); C8 (Z_to_bv 64 cap0); C8 (Z_to_bv 64 sz)] ->
  junk_at m d0 cap0 -> AIMG_HI <= d0 -> d0 + cap0 <= ATOP -> 0 < cap0 -> cap0 mod 4096 = 0 -> cap0 < 2^38 ->
  1 <= sz -> sz <= cap0 -> cap0 < sz + Z.of_nat (length str) ->
  ncap = (sz + Z.of_nat (length str) + 4095) / 4096 * 4096 ->
  4096 <= bv_unsigned ra ->
  rmap_cells m ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG d0 cap0 -> rng RNG TXT (Z.of_nat (length str) + 1) ->
  (forall a, FRESH a = true -> 0 < a -> a + ncap <= ATOP -> AIMG_HI <= a /\ (a + ncap <= d0 \/ d0 + cap0 <= a)) ->
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ncap <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a, FRESH a = true -> K a = ebind (enode (NMunmap d0 cap0) (adec_munmap d0 cap0)) (K2 a)) ->
  (forall a RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> emb_grow_post RNG sp lo d0 cap0 sz (Z.of_nat (length str)) a ncap m RNG' m' ->
      implS bsegs RNG' (K2 a 0) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ncap 3 34) (adec_mmap ATOP ncap 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 emb_append_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until str. intros ST CEIL LO MI -> TXTB NOZ TXTLO TXTHI LEN PTR MTX VEC OLD D0LO D0HI C0POS C0AL C0HI SZ1 SZC NOFIT NCAP RA RC RIMG RSTK ROLD0 RTXT FROK UNR SHAPE KONT.
  pose proof RC as RC0. destruct RC0 as (GPG & PGSZ & GOT & DPM & MLIM).
  unfold AIMG_HI, emb_append_entry in *. word_range sp SPR. pose proof atop_range as ATR.
  set (len := Z.of_nat (length str)) in *.
  assert (LENR : 1 <= len <= 400) by (subst len; clear -LEN; lia).
  assert (NC : ncap mod 4096 = 0 /\ sz + len <= ncap /\ ncap < sz + len + 4096) by (rewrite NCAP; clear -SZ1 LENR; Z.div_mod_to_equations; lia).
  destruct NC as (NCM & NCL & NCH).
  destruct OLD as [junk OLD].
  pose proof (munch_refl [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  emb_lock ST.
  step. step. if_lit.
  assert (SZ0 : 0 <= sz) by (clear -SZ1; lia).
  step.
  step.
  step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (TXTc : bytes_at bsegs mc (bv_unsigned (Z_to_bv 64 TXT)) (str ++ Z_to_bv 8 0 :: [])) by (rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); assumption) end.
  call istrlen_spec; [ eassumption | exact TXTc | exact NOZ | rewrite unsigned_lit by (clear -TXTLO TXTHI SPR; lia); exact RTXT | ].
  fold len. clear TXTc.
  step. step.
  step. zstep.
  step. if_cases K0; zify_cond K0. { exfalso. clear -K0 LENR SZ1 SZC D0HI ATR. lia. }
  step.
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 LENR SZ1 SZC NOFIT D0HI ATR C0HI. lia. }
  step. step.
  step.
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (emb_realloc1_spec RNG K K2 Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm d0 cap0 sz (len + sz) ncap lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => unfold rmap_cells; repeat (split; [assumption|]); assumption
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ _ => eassumption
       | |- junk_at _ _ _ => eexists; eassumption
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       | |- rng _ _ _ => exact ROLD0
       | |- _ = _ / _ * _ => rewrite NCAP; f_equal; f_equal; clear; lia
       end.
  all: try (unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO D0LO D0HI C0POS C0AL C0HI SZ1 SZC LENR; lia).
  { intros a HFR A0 ACE. exact (FROK a HFR A0 ACE). }
  { intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }
  { exact SHAPE. }

  intros a RNG' m3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & AAL & A0 & ACE & MU2 & MI2 & ST2 & VEC2 & JNK & RCH & RC2).
  destruct (FROK a HFR A0 ACE) as [DLO ADJ].
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  assert (MUA : munch [(bv_unsigned sp - EMBA_STACK, bv_unsigned sp); (AEMBz, AEMBz + 56); (d0, d0 + cap0); (a, a + ncap)]%Z m m3).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  clear MU WM.
  eapply cells_frameD in FR; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply cells_frameD in PTR; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply cells_frameD in MTX; [| exact MU2 | cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd length]; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI; lia].
  eapply bytes_at_transport in TXTB; [| exact MU2 | cbn [disjoint_from fst snd]; rewrite length_app; cbn [length]; fold len; clear -SPR CEIL LO DLO A0 ACE D0LO D0HI TXTLO LENR; lia].
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RTXT.
  destruct RC2 as (GPG2 & PGSZ2 & GOT2 & DPM2 & MLIM2).
  clear MU2 VEC OLD.
  set (d := a) in *. set (cap := ncap) in VEC2, JNK.
  assert (DHI : d + cap <= ATOP) by (subst d cap; exact ACE).
  assert (FIT : sz + len <= cap) by (subst cap; exact NCL).
  assert (ROLD : rng RNG' d cap) by (subst d cap; exact RCH).
  destruct (junk_split m3 d sz (cap - sz) ltac:(replace (sz + (cap - sz)) with cap by (clear; lia); exact JNK) SZ0 ltac:(clear -FIT LENR; lia)) as [J1 J23].
  destruct (junk_split m3 (d + sz) len (cap - sz - len) ltac:(replace (len + (cap - sz - len)) with (cap - sz) by (clear; lia); exact J23) ltac:(clear -LENR; lia) ltac:(clear -FIT; lia)) as [J2 J3].
  clear JNK J23. destruct J1 as [j1 J1]. destruct J2 as [j2 J2]. destruct J3 as [j3 J3].
  rename VEC2 into VEC. rename MUA into MU. rename ST2 into STX.
  iprefix.
  replace (ret_pc (Z_to_bv 64 399584)) with (Z_to_bv 64 399584 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step.
  step. zstep. zstep. step.
  setreg 12 (Z_to_bv 64 len) ltac:(f_equal; clear -LENR SZ0 DHI ATR FIT; lia).
  step.
  call (F_aintal.TwinB.imemset_spec (d + sz) len); [reflexivity| reflexivity| reflexivity| clear -DLO SZ0; lia| clear -LENR; lia| clear -DHI FIT ATR; lia| exact J2| assumption|].
  step.
  step. step. zstep. step. step.
  step.
  match goal with H : rw_cells bsegs _ (d + sz) [CB (Z.to_nat len) ?zz] |- _ =>
    replace (Z.to_nat len) with (length str) in H by (subst len; rewrite Nat2Z.id; reflexivity); rename H into DSTc end.
  lazymatch goal with |- evtF _ _ ?RR (MS _ _ _ _ _ ?mc _) =>
    eapply evtF_cut;
    [ eapply imemcpy_specZ with (src := str) (rest := [Z_to_bv 8 0]);
      [ eassumption | eassumption | exact DSTc | reflexivity
      | rewrite length_app; cbn [length]; fold len; clear -TXTLO CEIL LO DHI FIT LENR SPR; lia
      | fold len; clear -DHI FIT ATR LENR SZ0; lia
      | rewrite length_app; cbn [length]; fold len; clear -TXTHI; lia
      | fold len; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact RTXT|]; clear -LENR; lia
      | fold len; eapply rng_sub'; [exact ROLD|]; clear -SZ0 FIT LENR; lia ]
    | post_call bsegs mc ]
  end.
  emb_unlock.
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -96) _ |- _ => release_frame FRM STX (bv_unsigned sp) end.
  apply evtF_done. eapply KONT; [exact HFR|].
  unfold emb_grow_post.
  split; [exact FPLE|]. split; [exact AAL|]. split; [exact A0|]. split; [exact ACE|].
  split; [exact MU|]. split; [assumption|]. split; [exact STX|]. split; [exact PTR|]. split; [exact MTX|].
  split. { replace (sz + len) with (len + sz) by (clear; lia). exact VEC. }
  split. { replace ncap with (sz + (cap - sz)) by (subst cap; clear; lia). apply junk_merge; [exists j1; exact J1| | exact SZ0| clear -FIT LENR; lia].
           replace (cap - sz) with (len + (cap - sz - len)) by (clear; lia). apply junk_merge; [| exists j3; exact J3| clear -LENR; lia| clear -FIT; lia].
           exists str. replace (Z.to_nat len) with (length str) by (subst len; rewrite Nat2Z.id; reflexivity). assumption. }
  split; [exact RCH|].
  unfold rmap_cells. repeat (split; [assumption|]). assumption.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed.
End CANSEC2.
End TwinB.
