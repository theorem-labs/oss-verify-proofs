(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module paths, module names, addresses and numbers changed; 357 of its 406 lines of code are new or changed and 881 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P3F.v, with its module names, addresses and numbers changed; 194 of its 272 lines of code are new or changed and 328 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R3.v r3_evt (:229) at a working branch 3803efccea0
     (blob 6ae9be99eebcf5082cecf82db91f8b7f17f617e5);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r3_evt calls reac_identity_init (0x87de8) at 0x81688, so it is split at that call and has no
     single _of_F. r3_pre_F re-runs R3.v:271-275 (0x81640 li a0,4; 0x81644 li a1,6; the fifteen `sb`
     0x81648 .. 0x81680; 0x81684 ld a0,144(s1); 0x81688 jal) and stops AT the callee entry, with the facts
     R3.v:276-294 derives there (asan_cells, shadow_rw, addressable) in its post; r3_post_F re-runs
     R3.v:310-349 (the return point 0x8168c = the run's end cut: the ret_pc normalisation and the
     munch / wmono / bytes_at transport), its premises being the callee post facts r3_evt uses there.
     No _F steps through the callee, and no callee contract is stated here.
   Bridge input only: no top, no W_cutfree_ok, no cut-free twin, no LSCPS join.
   rule 24: no function proved. *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; writer of record a Theorem Labs lane, lane (internal path); consumer a Theorem Labs lane's
   W1 seg_R3): r3_pre_F_on and r3_post_F_on carry the proofs; r3_pre_F and r3_post_F keep their statements, as
   corollaries.
   r3_pre_F_on: the premise `shadow_rw m` is DROPPED.  Measured from the stretch's proof: the fifteen shadow stores
   into [Sh + 254, Sh + 291) take store_ok from the rw_cells premise at Sh + 254 (rng RNG (Sh + 254) 37), the reload
   [Ab + 144, Ab + 152) reads through the ro_cells premise (rng RNG (Ab + 144) 8), and the stretch loads no shadow
   byte; `shadow_rw m` only rebuilt the post's `shadow_rw m1`.  The post's r3_mid becomes r3_mid_on (r3_mid without
   its conjunct `shadow_rw m1`) and the transport `forall P, shadow_rw_on P m -> shadow_rw_on P m1` (every region:
   the written shadow bytes are present in m1).
   r3_post_F_on: the stretch has no instruction, so it reads and stores no shadow byte.  Its shadow premises, the
   conjunct `shadow_rw m1` of r3_mid and the callee-post fact `shadow_rw m'`, are DROPPED (they only rebuilt the post's
   `shadow_rw m'`): it takes r3_mid_on.  The post's r3_Q becomes r3_Q_on, whose conjunct `shadow_rw m'` is replaced by
   `forall P, shadow_rw_on P m2 -> shadow_rw_on P m'`, m2 the memory at the return point 0x8168c (the stretch's start,
   the memory of the dropped premise). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R3.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn.
(* Last: StepF's step / finish (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* R3.v's one-byte store hook, on the evtF goal (pilot fix (2)): `sb r,o(s3)` writes le1 r; the engine
   records it in the shadow cells once it is a byte list. *)
Local Ltac r3F_fix :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      rewrite (R3.r3_le1_lit z) by lia; mem_after_store
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (R3.r3_le1 v); mem_after_store
  | _ => idtac
  end.
Local Ltac r3F_sb := step; r3F_fix.

(* The state at the reac_identity_init entry: the run's own facts about the memory it has written. *)
Definition r3_mid (m m1 : word -> option byte) (Sh idp lo spv : Z) (idb : list byte) : Prop :=
  munch [(Sh + 254, Sh + 291)] m m1 /\ wmono rsegs m m1 /\
  mem_inv rsegs m1 /\ stk rsegs m1 lo spv /\ asan_cells m1 /\ shadow_rw m1 /\
  addressable m1 idp 38 /\ rw_cells rsegs m1 idp [CB 38 idb] /\
  bytes_at rsegs m1 (Sh + 254) [Z_to_bv 8 4] /\
  bytes_at rsegs m1 (Sh + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
  bytes_at rsegs m1 (Sh + 282) (repeat (Z_to_bv 8 0) 9).

(* The post of the R3 run (R3.v:242-251). *)
Definition r3_Q (sp gp tp s0 s1 s2 s3 s7 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (spv Sh idp lo : Z) : machine_state -> Prop :=
  fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
    ms' = MS R F (Z_to_bv 64 0x8168c) fc None m' (seg_rom rsegs) /\
    getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
    getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
    munch [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)] m m' /\ wmono rsegs m m' /\
    mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\ shadow_rw m' /\
    rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
    bytes_at rsegs m' (Sh + 254) [Z_to_bv 8 4] /\
    bytes_at rsegs m' (Sh + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
    bytes_at rsegs m' (Sh + 282) (repeat (Z_to_bv 8 0) 9).

(* ---- route (C): r3_mid / r3_Q without the universal shadow_rw ---- *)

(* r3_mid without its conjunct `shadow_rw m1`. *)
Definition r3_mid_on (m m1 : word -> option byte) (Sh idp lo spv : Z) (idb : list byte) : Prop :=
  munch [(Sh + 254, Sh + 291)] m m1 /\ wmono rsegs m m1 /\
  mem_inv rsegs m1 /\ stk rsegs m1 lo spv /\ asan_cells m1 /\
  addressable m1 idp 38 /\ rw_cells rsegs m1 idp [CB 38 idb] /\
  bytes_at rsegs m1 (Sh + 254) [Z_to_bv 8 4] /\
  bytes_at rsegs m1 (Sh + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
  bytes_at rsegs m1 (Sh + 282) (repeat (Z_to_bv 8 0) 9).

Lemma r3_mid_on_of_mid : forall (m m1 : word -> option byte) (Sh idp lo spv : Z) (idb : list byte),
  r3_mid m m1 Sh idp lo spv idb -> r3_mid_on m m1 Sh idp lo spv idb.
Proof.
  intros m m1 Sh idp lo spv idb MID. unfold r3_mid in MID. unfold r3_mid_on.
  destruct MID as (MU & WM & MI & ST & AC & _ & K).
  exact (conj MU (conj WM (conj MI (conj ST (conj AC K))))).
Qed.

Lemma r3_mid_of_on : forall (m m1 : word -> option byte) (Sh idp lo spv : Z) (idb : list byte),
  shadow_rw m1 -> r3_mid_on m m1 Sh idp lo spv idb -> r3_mid m m1 Sh idp lo spv idb.
Proof.
  intros m m1 Sh idp lo spv idb HSW MID. unfold r3_mid_on in MID. unfold r3_mid.
  destruct MID as (MU & WM & MI & ST & AC & K).
  exact (conj MU (conj WM (conj MI (conj ST (conj AC (conj HSW K)))))).
Qed.

(* r3_Q with its conjunct `shadow_rw m'` replaced by the transport from m2, the memory at the return point. *)
Definition r3_Q_on (sp gp tp s0 s1 s2 s3 s7 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m m2 : word -> option byte) (spv Sh idp lo : Z) : machine_state -> Prop :=
  fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
    ms' = MS R F (Z_to_bv 64 0x8168c) fc None m' (seg_rom rsegs) /\
    getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
    getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
    munch [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)] m m' /\ wmono rsegs m m' /\
    mem_inv rsegs m' /\ stk rsegs m' lo spv /\ asan_cells m' /\
    (forall P, B.ShadowRwOn.shadow_rw_on P m2 -> B.ShadowRwOn.shadow_rw_on P m') /\
    rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] /\
    bytes_at rsegs m' (Sh + 254) [Z_to_bv 8 4] /\
    bytes_at rsegs m' (Sh + 272) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] /\
    bytes_at rsegs m' (Sh + 282) (repeat (Z_to_bv 8 0) 9).

Lemma r3_Q_of_on : forall (sp gp tp s0 s1 s2 s3 s7 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m m2 : word -> option byte) (spv Sh idp lo : Z),
  shadow_rw m2 -> forall ms',
  r3_Q_on sp gp tp s0 s1 s2 s3 s7 s9 s10 F fc m m2 spv Sh idp lo ms' ->
  r3_Q sp gp tp s0 s1 s2 s3 s7 s9 s10 F fc m spv Sh idp lo ms'.
Proof.
  intros sp gp tp s0 s1 s2 s3 s7 s9 s10 F fc m m2 spv Sh idp lo HSW ms' PO.
  unfold r3_Q_on in PO. unfold r3_Q.
  destruct PO as (R & m' & E & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G23 & G25 & G26 & MU & WM & MI & ST & AC &
                  SW & K).
  exists R, m'.
  do 16 (split; [assumption|]).
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m' (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m2 HSW)))|].
  exact K.
Qed.

(* R3.r3_shadow_rw under a region guard P: a munch whose written shadow bytes are present after it keeps every
   shadow_rw_on region. *)
Lemma r3_srw_on_munch : forall (P : Z -> Prop) W m m', B.ShadowRwOn.shadow_rw_on P m -> munch W m m' ->
  wmono rsegs m m' -> (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' HS MU WM H a Hp Ha. destruct (HS a Hp Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* ---- the pre-call stretch 0x81640 .. 0x81688, route (C): no shadow premise; the post transports every
   shadow_rw_on region.  Accesses: the fifteen one-byte shadow stores inside the 37-byte block [s3 + 254, s3 + 291)
   (at +254, +272 .. +276 and +282 .. +290) and the 8-byte reload of the identity buffer base at [s1 + 144]. *)
Lemma r3_pre_F_on : forall (RNG : footprint)
  (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab idp lo : Z) (xs idb : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 152 <= 2 ^ 64 ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp -> idp mod 8 = 0 -> shadow_addr idp = Sh + 272 ->
    (forall a, idp <= a <= idp + 38 -> app_mem a) ->
    (idp + 38 <= spv - 2224 \/ spv <= idp) ->
    length xs = 37%nat -> rw_cells rsegs m (Sh + 254) (map C1 xs) ->
    rw_cells rsegs m idp [CB 38 idb] -> ro_cells rsegs m (Ab + 144) [C8 (Z_to_bv 64 idp)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m ->
    rng RNG (Sh + 254) 37 -> rng RNG (Ab + 144) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x8168c) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 idp) (Z_to_bv 64 6) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x87de8) fc None m1 (seg_rom rsegs) /\
         r3_mid_on m m1 Sh idp lo spv idb /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1))
      (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81640) fc None m (seg_rom rsegs)).
Proof.
  intros RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab idp lo xs idb -> -> -> HSrt HSlo HHM HLO HAE HSA HA64 HSid Hidrt Hid8 Hshid Hidapp Hsep
    Hxs CH RWid RO144 HMI ST HAC Gsh Gid.
  do 37 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (rw_cells_bound rsegs m (Sh + 254) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  pose proof (rw_cells_bound rsegs m idp _ RWid) as Hidb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hidb.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  pose proof (Hidapp (idp + 38) ltac:(lia)) as Hidhi.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hidhi.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (munch_refl [(Sh + 254, Sh + 291)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  r3F_sb. r3F_sb. r3F_sb. r3F_sb. r3F_sb.
  r3F_sb. r3F_sb. r3F_sb. r3F_sb. r3F_sb.
  r3F_sb. r3F_sb. r3F_sb. r3F_sb. r3F_sb.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1).
  { intros P HP. apply (r3_srw_on_munch P _ m m1 HP MU WM). intros a Ha.
    pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    destruct (Z_le_gt_dec (Sh + 254) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 291)) as [H2|H2]|].
    - right. apply (R3.r3_ba_rd m1 (Sh + 254) _ a HbC). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I]. }
  pose proof (R3.r3_ba_sub _ _ _ 0 1 HbC ltac:(cbn [length]; lia)) as B0.
  pose proof (R3.r3_ba_sub _ _ _ 18 5 HbC ltac:(cbn [length]; lia)) as B18.
  pose proof (R3.r3_ba_sub _ _ _ 28 9 HbC ltac:(cbn [length]; lia)) as B28.
  cbn [firstn skipn] in B0, B18, B28.
  replace (Sh + 254 + Z.of_nat 0) with (Sh + 254) in B0 by lia.
  replace (Sh + 254 + Z.of_nat 18) with (Sh + 272) in B18 by lia.
  replace (Sh + 254 + Z.of_nat 28) with (Sh + 282) in B28 by lia.
  assert (HA1 : addressable m1 idp 38).
  { apply R3.r3_id_addr; [lia | exact Hid8 | unfold APPMEM_END; lia | intros i Hi; apply Hidapp; lia |].
    rewrite Hshid. exact B18. }
  apply evtF_done. cbn beta.
  exists m1. split; [reflexivity|].
  split; [|exact HSW1].
  unfold r3_mid_on.
  split; [exact MU|]. split; [exact WM|]. split; [exact HMI|]. split; [exact ST|].
  split; [exact HAC1|]. split; [exact HA1|]. split; [exact RWid|].
  split; [exact B0|]. split; [exact B18 | exact B28].
Qed.

(* ---- the pre-call stretch 0x81640 .. 0x81688, stopping at the reac_identity_init entry 0x87de8 ----
   Accesses: the fifteen one-byte shadow stores inside the 37-byte block [s3 + 254, s3 + 291) (at
   +254, +272 .. +276 and +282 .. +290) and the 8-byte reload of the identity buffer base at [s1 + 144]. *)
Lemma r3_pre_F : forall (RNG : footprint)
  (rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab idp lo : Z) (xs idb : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2224 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 152 <= 2 ^ 64 ->
    (Sh + 392 <= idp \/ idp + 38 <= Sh) -> RT_HI <= idp -> idp mod 8 = 0 -> shadow_addr idp = Sh + 272 ->
    (forall a, idp <= a <= idp + 38 -> app_mem a) ->
    (idp + 38 <= spv - 2224 \/ spv <= idp) ->
    length xs = 37%nat -> rw_cells rsegs m (Sh + 254) (map C1 xs) ->
    rw_cells rsegs m idp [CB 38 idb] -> ro_cells rsegs m (Ab + 144) [C8 (Z_to_bv 64 idp)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    rng RNG (Sh + 254) 37 -> rng RNG (Ab + 144) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x8168c) sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 idp) (Z_to_bv 64 6) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x87de8) fc None m1 (seg_rom rsegs) /\
         r3_mid m m1 Sh idp lo spv idb)
      (MS (mkR rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81640) fc None m (seg_rom rsegs)).
Proof.
  intros RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab idp lo xs idb Hsp Hs3 Hs1 HSrt HSlo HHM HLO HAE HSA HA64 HSid Hidrt Hid8 Hshid Hidapp Hsep
    Hxs CH RWid RO144 HMI ST HAC HSW Gsh Gid.
  refine (evtF_mono rsegs RNG _ _ _
            (r3_pre_F_on RNG rra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m spv Sh Ab idp lo xs idb Hsp Hs3 Hs1 HSrt HSlo HHM HLO HAE HSA HA64 HSid Hidrt Hid8
               Hshid Hidapp Hsep Hxs CH RWid RO144 HMI ST HAC Gsh Gid) _).
  intros ms' (m1 & E & MID & TR). exists m1. split; [exact E|].
  exact (r3_mid_of_on m m1 Sh idp lo spv idb
           (B.ShadowRwOn.shadow_rw_of_on_all m1 (TR _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))) MID).
Qed.

(* ---- the post-call stretch, route (C): the return point 0x8168c is the run's end cut; no shadow premise, the post
   transports every shadow_rw_on region from the memory at the return point ----
   The premises are the facts of the reac_identity_init post that r3_evt uses at that point, plus the
   pre-call facts (r3_mid_on) it composes them with. *)
Lemma r3_post_F_on : forall (RNG : footprint)
  (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m m1 m' : word -> option byte) (spv Sh idp lo : Z) (idb : list byte),
    Sh + 392 <= lo -> lo + 2224 <= spv -> (Sh + 392 <= idp \/ idp + 38 <= Sh) ->
    r3_mid_on m m1 Sh idp lo spv idb ->
    munch [(spv - 2224, spv); (idp, idp + 38)] m1 m' -> wmono rsegs m1 m' ->
    mem_inv rsegs m' -> stk rsegs m' lo spv -> asan_cells m' ->
    rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] ->
    evtF rsegs RNG (r3_Q_on sp gp tp s0 s1 s2 s3 s7 s9 s10 F fc m m' spv Sh idp lo)
      (MS (mkR (Z_to_bv 64 0x8168c) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (ret_pc (Z_to_bv 64 0x8168c)) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m1 m' spv Sh idp lo idb HSlo HLO HSid MID MU2 WM2 MI2 ST2 AC2 HZ.
  destruct MID as (MU & WM & _ & _ & _ & _ & _ & B0 & B18 & B28).
  assert (Hsub : sub_fp [(spv - 2224, spv); (idp, idp + 38)]
                   [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  assert (Hsub1 : sub_fp [(Sh + 254, Sh + 291)]
                   [(Sh + 254, Sh + 291); (spv - 2224, spv); (idp, idp + 38)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m' (munch_weaken _ _ m m1 Hsub1 MU)
                (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  assert (Hdj : forall k n, 0 <= k -> k + n <= 37 ->
            disjoint_from [(spv - 2224, spv); (idp, idp + 38)] (Sh + 254 + k) n).
  { intros k n Hk Hkn. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B0 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 254) with (Sh + 254 + 0) by lia; apply Hdj; lia)) as B0'.
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B18 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 272) with (Sh + 254 + 18) by lia; apply Hdj; lia)) as B18'.
  pose proof (bytes_at_transport rsegs [(spv - 2224, spv); (idp, idp + 38)] m1 m' _ _ B28 MU2
    ltac:(cbn [length repeat Z.of_nat Pos.of_succ_nat Pos.succ];
          replace (Sh + 282) with (Sh + 254 + 28) by lia; apply Hdj; lia)) as B28'.
  replace (ret_pc (Z_to_bv 64 0x8168c)) with (Z_to_bv 64 0x8168c)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evtF_done. unfold r3_Q_on. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
  split; [exact MI2|]. split; [exact ST2|]. split; [exact AC2|]. split; [intros P HP; exact HP|].
  split; [exact HZ|]. split; [exact B0'|]. split; [exact B18' | exact B28'].
Qed.

(* ---- the post-call stretch: the return point 0x8168c is the run's end cut ----
   The premises are the facts of the reac_identity_init post that r3_evt uses at that point, plus the
   pre-call facts (r3_mid) it composes them with. *)
Lemma r3_post_F : forall (RNG : footprint)
  (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m m1 m' : word -> option byte) (spv Sh idp lo : Z) (idb : list byte),
    Sh + 392 <= lo -> lo + 2224 <= spv -> (Sh + 392 <= idp \/ idp + 38 <= Sh) ->
    r3_mid m m1 Sh idp lo spv idb ->
    munch [(spv - 2224, spv); (idp, idp + 38)] m1 m' -> wmono rsegs m1 m' ->
    mem_inv rsegs m' -> stk rsegs m' lo spv -> asan_cells m' -> shadow_rw m' ->
    rw_cells rsegs m' idp [CB 38 (repeat (Z_to_bv 8 0) 38)] ->
    evtF rsegs RNG (r3_Q sp gp tp s0 s1 s2 s3 s7 s9 s10 F fc m spv Sh idp lo)
      (MS (mkR (Z_to_bv 64 0x8168c) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (ret_pc (Z_to_bv 64 0x8168c)) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m1 m' spv Sh idp lo idb HSlo HLO HSid MID MU2 WM2 MI2 ST2 AC2 SW2 HZ.
  refine (evtF_mono rsegs RNG _ _ _
            (r3_post_F_on RNG sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m m1 m' spv Sh idp lo idb HSlo HLO HSid
               (r3_mid_on_of_mid m m1 Sh idp lo spv idb MID) MU2 WM2 MI2 ST2 AC2 HZ) _).
  exact (r3_Q_of_on sp gp tp s0 s1 s2 s3 s7 s9 s10 F fc m m' spv Sh idp lo SW2).
Qed.
