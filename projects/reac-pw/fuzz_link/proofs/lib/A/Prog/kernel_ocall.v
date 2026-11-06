(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v; 369 of its 424 lines of code are new or changed and 431 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's OWN-CALLEE STEP. A call, from a cut of kernel's walk (kat, F live), of a
   function whose contract is an `aleaf_rd` with kernel's two own callees' write set and Post (nl_error_c.v,
   attr_text_c.v: the struct nl_w at a0 = w2, its n only grows), and the cut rebuilt at the return address.

   - `kat_ocall`: the cut after the call, from the cut before it and the callee's apost (its akept over w2 and its
     window [s1 - K, s1), the registers it preserves, the same frames, the blocks up to order). Every byte the cut
     names keeps its view: the saved words, the spill slots and the cursor by akept's stack clause, F's header, flag
     word and shadow by its frame clause, the read set (cursor, g_nl, long_alias) by akept_akb_gx; the presence of F
     and of its shadow from their views (off the image), w2's from the callee's Post (`ko_present_of_view`).
   - `kn_ocall`: the call itself (SRr_bind with the contract on kernel's journal at ((8, fpos) :: own); apre from the
     cut) and the return (kat_ocall, and w2's fields from the Post). Used at nl_error +0x1b7c (kernel_k12.v) and at
     attr_text +0xb40 / +0xdc8 (the attribute lanes).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkCall PcapRelro kernel_kit kernel_entry kernel_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the write set and the Post of kernel's own callees (nl_error_c.v, attr_text_c.v) *)
Definition kn_wawr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(aarg regs 0, aarg regs 0 + NW_SIZE)].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis KI : KernImg pa_segs B.

Definition kn_wpost (regs : bvmap 5 word) (m : word -> option byte) (regs' : bvmap 5 word)
    (m' : word -> option byte) : Prop :=
  forall bs, anlw_at SEGS m (aarg regs 0) bs ->
    exists bs', anlw_at SEGS m' (aarg regs 0) bs' /\ nlw_wf bs' /\ nw_n bs <= nw_n bs'.

(* ---- small facts ---- *)

Lemma ko_present_of_view : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H m a <> None -> apresent H m a.
Proof.
  intros H m a Ha Hn Hv. unfold aview, mbyte, mrestrict in Hv. unfold apresent.
  destruct (H (Z_to_bv 64 a)) eqn:EH.
  - rewrite (seg_rom_none SEGS a Ha Hn) in Hv. exfalso. apply Hv. reflexivity.
  - destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    + split; [reflexivity | exists b; reflexivity].
    + rewrite (seg_rom_none SEGS a Ha Hn) in Hv. exfalso. apply Hv. reflexivity.
Qed.

Lemma ko_view_of_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview SEGS H m a <> None.
Proof.
  intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

Lemma ko_set_fs : forall f f' (S : astate), set_fs f (set_fs f' S) = set_fs f S.
Proof. intros f f' S. destruct S. reflexivity. Qed.

Lemma ko_regs0 : forall cx (ms3 ms4 : machine_state),
  aregs_preserved (ms_regs ms3) (ms_regs ms4) -> kregs0 cx ms3 -> kregs0 cx ms4.
Proof.
  intros cx ms3 ms4 HP (R2 & R9 & R8 & R3 & R4 & R18 & R20). unfold kregs0.
  split; [rewrite <- R2; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- R9; exact (HP 9 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- R8; exact (HP 8 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- R3; exact (HP 3 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- R4; exact (HP 4 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- R18; exact (HP 18 ltac:(unfold acallee_saved; lia))|].
  rewrite <- R20; exact (HP 20 ltac:(unfold acallee_saved; lia)).
Qed.

Lemma ko_regs_eq : forall (ms3 ms4 : machine_state) rl rl',
  aregs_preserved (ms_regs ms3) (ms_regs ms4) -> incl rl' rl ->
  Forall (fun rv => acallee_saved (Z.of_nat (fst rv))) rl' -> kregs_eq ms3 rl -> kregs_eq ms4 rl'.
Proof.
  intros ms3 ms4 rl rl' HP Hinc Hcs Heq. unfold kregs_eq in *. rewrite Forall_forall in *.
  intros rv Hin. rewrite (HP _ (Hcs rv Hin)). exact (Heq rv (Hinc rv Hin)).
Qed.

(* ---- THE CUT AFTER AN OWN CALLEE ---- *)
Section o.
Variable cx : kcx.
Variables fpos k2 K pc ret adv : Z.
Variables (ly3 ly4 : alayout) (S3 S4 : astate) (W3 W4 : world SEGS) (ms3 ms4 : machine_state) (md3 md4 : Model).
Variables (rl rl' : list (nat * Z)) (sl : list (Z * Z)) (sh : list Z) (g : option Z).
Hypothesis HB : kbase SK B cx.
Hypothesis HJ3 : ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
  (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.
Hypothesis HF3 : frames S3 = (KN_CID, fpos) :: frames (k_Sc cx).
Hypothesis HK : kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3.
Hypothesis HKm : kms ret ms4.
Hypothesis HP : aregs_preserved (ms_regs ms3) (ms_regs ms4).
Hypothesis Hrl : incl rl' rl.
Hypothesis Hcs : Forall (fun rv => acallee_saved (Z.of_nat (fst rv))) rl'.
Hypothesis HKP : 0 <= K <= ksp1 cx - (ksp cx - KERNEL_AK).
Hypothesis HAK : akept SEGS B ly3 S3 W3 (ms_mem ms3) W4 (ms_mem ms4) (ksp1 cx - K) (ksp1 cx)
  (fun a => kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE).
Hypothesis HS4 : S4 = set_fs (st_fs S4) S3.
Hypothesis Hperm4 : Permutation (ablocks B ly4 S4) (ablocks B ly3 S3).
Hypothesis HF4 : frames S4 = frames S3.
Hypothesis Hfds : m_fds md4 = m_fds md3.
Hypothesis Hfs : m_fs md4 = m_fs md3.
Hypothesis Hw2 : forall a, kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE -> aview SEGS (w_H W4) (ms_mem ms4) a <> None.
Hypothesis Hsl : kslots_okb sl = true.
Hypothesis Hsh : (length sh <= 0x448)%nat.

Lemma ko_HK : kms pc ms3 /\ kregs0 cx ms3 /\ kregs_eq ms3 rl /\ ksaved cx W3 ms3 /\ kframe cx fpos true W3 ms3 /\
  kshadow cx fpos W3 ms3 sh /\ kslots_eq cx W3 ms3 sl /\ kjbk B cx fpos k2 ly3 S3 md3 /\ kkept B cx fpos W3 ms3 /\
  kcursor cx W3 ms3 adv /\ kgnl_at cx W3 ms3 g /\ kla_at W3 ms3.
Proof. exact HK. Qed.

Lemma ko_KJ : kjbk B cx fpos k2 ly3 S3 md3.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ko_HK)))))))). Qed.

Lemma ko_geo : alloc_ceiling + KERNEL_AK <= ksp cx /\ ksp cx <= 2 ^ 47 /\
  ksp cx - 368 <= ksp1 cx <= ksp cx - 352 /\ ksp1 cx mod 32 = 0 /\
  4096 <= kF cx fpos /\ kF cx fpos + 16384 <= alloc_ceiling /\
  (forall a, kF cx fpos <= a < kF cx fpos + 16384 -> ~ in_img SEGS a).
Proof.
  destruct (kn_sp SK B cx HB) as (S1 & S2 & _ & (S4' & S5) & S6 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 ko_KJ) as (F1 & F2 & _ & _ & _ & F6 & _).
  change (fs_frame_bytes KN_CID) with 16384 in F2, F6.
  repeat split; try lia; exact F6.
Qed.

Lemma ko_fa : forall c p, frame_addr ly3 c p = frame_addr (k_lyc cx) c p.
Proof.
  intros c p. pose proof HB as ((HJ0 & _) & _).
  rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c p HJ3)).
  rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c p HJ0)).
  reflexivity.
Qed.

Lemma ko_row : ly_stk_lo ly3 = ly_stk_lo (k_lyc cx) /\ ly_stk_hi ly3 = ly_stk_hi (k_lyc cx).
Proof.
  pose proof HB as ((HJ0 & _) & _).
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (A1 & A2).
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as (B1 & B2).
  split; congruence.
Qed.

Lemma ko_Fapp : kF cx fpos + 16384 <= kLowShadowBeg \/ kHighMemBeg <= kF cx fpos.
Proof. destruct (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB ko_KJ) as (_ & _ & _ & H). exact H. Qed.

(* the w2 range is inside F *)
Lemma ko_w2_F : forall a, kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE -> kF cx fpos <= a < kF cx fpos + 16384.
Proof. intros a Ha. unfold kW2, KN_W2, NW_SIZE in Ha. lia. Qed.

(* a read-set byte keeps its view across the call *)
Lemma ko_ard_keep : forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a ->
  aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
  intros a Ha.
  pose proof HB as (_ & HRD & _).
  destruct (kn_rd_facts SK B LAWS cx fpos k2 ly3 S3 md3 a HB ko_KJ Ha) as (Hab & _ & Hfs').
  destruct ko_row as (R1 & R2).
  pose proof ko_KJ as (_ & _ & J3 & _).
  assert (Hakb : akb SEGS B ly3 S3 (ksp1 cx - K) (ksp1 cx) a).
  { apply (akb_sub SEGS B (k_lyc cx) (k_Sc cx) ly3 S3 (ksp cx - KERNEL_AK) (ksp cx) (ksp1 cx - K) (ksp1 cx) a
      (HRD a Ha)); [lia | pose proof ko_geo; lia | exact R1 | exact R2 | | | intros c p; exact (ko_fa c p)].
    - intros b m Hin. exact (Permutation_in _ (Permutation_sym J3) Hin).
    - intros c q Hin. rewrite HF3. right. exact Hin. }
  apply (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ3 HAK Hakb).
  intros Hw. apply Hfs'. unfold kn_fside, in_zr, frame_rng. cbn [fst snd]. left.
  pose proof (ko_w2_F a Hw). change (fs_frame_bytes KN_CID) with 16384. unfold kF in *. lia.
Qed.

(* a byte of F's range or of F's shadow range keeps its view across the call, unless in w2 *)
Lemma ko_F_keep : forall a,
  (kF cx fpos <= a < kF cx fpos + 16384 \/ kFSH cx fpos <= a < kFSH cx fpos + 2048) ->
  ~ (kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE) ->
  aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
  intros a Ha Hw. destruct HAK as (_ & _ & _ & K4 & _).
  apply (K4 KN_CID fpos a); [rewrite HF3; left; reflexivity | | exact Hw].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite (ko_fa KN_CID fpos). change (fs_frame_bytes KN_CID) with 16384.
  change (16384 / 8) with 2048. unfold kFSH, kF, shadow_addr in *. exact Ha.
Qed.

(* a stack byte at or above s1 keeps its view across the call *)
Lemma ko_stack_keep : forall a, ksp1 cx <= a < 2 ^ 64 ->
  aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a.
Proof.
  intros a Ha. destruct HAK as (K1 & _). pose proof ko_geo as (G1 & _ & G3 & _ & _ & G6 & _).
  apply K1; [lia | lia | unfold kW2, KN_W2, NW_SIZE; lia].
Qed.

Theorem kat_ocall : kat B cx fpos ret rl' sl sh true adv g k2 ly4 S4 W4 ms4 md4.
Proof.
  destruct ko_HK as (Km & Kr0 & Kreq & Ksv & Kfr & Ksh & Ksl & KJ & (Kak & Kro) & Kcur & Kgnl & Kla).
  pose proof ko_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  unfold kat.
  split; [exact HKm|].
  split; [exact (ko_regs0 cx ms3 ms4 HP Kr0)|].
  split; [exact (ko_regs_eq ms3 ms4 rl rl' HP Hrl Hcs Kreq)|].
  split.
  (* ksaved *)
  { destruct Ksv as (Sv1 & Sv2). split.
    - rewrite (kk_rdword_agree (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) (ms_mem ms4))); [exact Sv1|].
      intros i Hi. apply ko_stack_keep. lia.
    - intros j Hj. rewrite (kk_rdword_agree (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) (ms_mem ms4)));
        [exact (Sv2 j Hj)|].
      intros i Hi. apply ko_stack_keep. lia. }
  split.
  (* kframe *)
  { unfold kframe in Kfr |- *. destruct Kfr as (Fr1 & Fr2 & Fr3 & Fr4 & Fr5 & Fr6).
    change (fs_frame_bytes KN_CID) with 16384 in *.
    change (16384 / 8) with 2048 in *.
    assert (FK : forall a, kF cx fpos <= a < kF cx fpos + 24 \/ kF cx fpos + 16376 <= a < kF cx fpos + 16384 ->
      aview SEGS (w_H W4) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply ko_F_keep; [left; lia | unfold kW2, KN_W2, NW_SIZE; lia]. }
    split; [rewrite (kk_rdword_agree (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) (ms_mem ms4)));
            [exact Fr1 | intros i Hi; apply FK; lia]|].
    split; [rewrite (kk_rdword_agree (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) (ms_mem ms4)));
            [exact Fr2 | intros i Hi; apply FK; lia]|].
    split; [rewrite (kk_rdword_agree (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) (ms_mem ms4)));
            [exact Fr3 | intros i Hi; apply FK; lia]|].
    split; [rewrite (kk_rdword_agree (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) (ms_mem ms4)));
            [exact Fr4 | intros i Hi; apply FK; lia]|].
    split.
    - intros a Ha. apply ko_present_of_view; [lia | exact (G7 a Ha) |].
      destruct (Z_lt_le_dec a (kW2 cx fpos)) as [Hl|Hl];
        [|destruct (Z_lt_le_dec a (kW2 cx fpos + NW_SIZE)) as [Hh|Hh]].
      + rewrite (ko_F_keep a ltac:(left; lia) ltac:(lia)). exact (ko_view_of_present _ _ _ (Fr5 a Ha)).
      + exact (Hw2 a ltac:(lia)).
      + rewrite (ko_F_keep a ltac:(left; lia) ltac:(lia)). exact (ko_view_of_present _ _ _ (Fr5 a Ha)).
    - intros a Ha. apply ko_present_of_view.
      + unfold kFSH, shadow_of_addr, SHADOW_OFF in Ha. pose proof asan_consts as ((C1a & C1b) & _). split; lia.
      + intros Himg. pose proof (pa_segs_low a Himg) as Hlow. unfold kFSH, shadow_of_addr, SHADOW_OFF in Ha.
        unfold kLowMemEnd in Hlow. lia.
      + pose proof ko_Fapp as HFa.
        rewrite (ko_F_keep a ltac:(right; exact Ha)) by (unfold kFSH, shadow_of_addr, kW2, KN_W2, NW_SIZE in *;
          unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia).
        exact (ko_view_of_present _ _ _ (Fr6 a Ha)). }
  split.
  (* kshadow *)
  { intros i Hi. pose proof ko_Fapp as HFa. rewrite (ko_F_keep (kFSH cx fpos + Z.of_nat i)).
    - exact (Ksh i Hi).
    - right. lia.
    - unfold kFSH, shadow_of_addr, kW2, KN_W2, NW_SIZE in *.
      unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  split.
  (* kslots_eq *)
  { unfold kslots_eq in *. rewrite Forall_forall in *. intros ov Hin.
    pose proof (kslots_okb_spec sl Hsl ov Hin) as Hb.
    rewrite (kk_rdword_agree (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) (ms_mem ms4)));
      [exact (Ksl ov Hin)|].
    intros i Hi. apply ko_stack_keep. lia. }
  split.
  (* kjbk *)
  { destruct KJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7). unfold kjbk.
    split; [exact J1|].
    split; [rewrite HS4 at 1; rewrite J2 at 1; rewrite ko_set_fs; reflexivity|].
    split; [exact (Permutation_trans Hperm4 J3)|].
    split; [exact J4|]. split; [exact J5|].
    split; [rewrite Hfds; exact J6 | rewrite Hfs; exact J7]. }
  split.
  (* kkept *)
  { split.
    - destruct ko_row as (R1 & R2). pose proof KJ as (_ & _ & J3 & _).
      apply (akept_trans_ly SK SEGS B LAWS pa_segs_low (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) ly3 S3 W3
        (ms_mem ms3) W4 (ms_mem ms4) (ksp cx - KERNEL_AK) (ksp cx) (ksp1 cx - K) (ksp1 cx)
        (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a) (fun a => kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE)
        (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a)).
      + lia.
      + lia.
      + exact Kak.
      + exact HAK.
      + lia.
      + lia.
      + intros b m Hin. exact (Permutation_in _ (Permutation_sym J3) Hin).
      + intros f Hin. rewrite HF3. right. exact Hin.
      + intros c p. exact (ko_fa c p).
      + intros a Ha. exact Ha.
      + intros a Ha. right. unfold aside_rng, in_zr, frame_rng. cbn [fst snd]. left.
        change (fs_frame_bytes KN_CID) with 16384. pose proof (ko_w2_F a Ha). unfold kF in *. lia.
    - intros a Hro Hno Her.
      assert (Himg : in_img SEGS a).
      { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] |].
        exact (ke_relro_img _ _ KI a Hr). }
      destruct HAK as (_ & _ & K3 & _).
      rewrite (K3 a Himg Hno Her).
      + exact (Kro a Hro Hno Her).
      + intros Hw. exact (G7 a (ko_w2_F a Hw) Himg). }
  split.
  (* kcursor *)
  { destruct Kcur as (C1 & C2 & C3 & C4).
    assert (CUR : forall i, 0 <= i < 16 ->
      aview SEGS (w_H W4) (ms_mem ms4) (ka0 cx + i) = aview SEGS (w_H W3) (ms_mem ms3) (ka0 cx + i))
      by (intros i Hi; apply ko_ard_keep; left; unfold ka0 in *; lia).
    split; [exact C1|]. split; [|split].
    - apply (val_mem_moved SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) (ka0 cx) (ka0 cx) 8 (k_wp cx + adv));
        [|exact C2]. intros i Hi. apply CUR. cbn in Hi. lia.
    - apply (val_mem_moved SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) (ka0 cx + 8) (ka0 cx + 8) 8
        (k_wn cx - adv)); [|exact C3].
      intros i Hi. cbn in Hi. replace (ka0 cx + 8 + i) with (ka0 cx + (8 + i)) by lia. apply CUR. lia.
    - intros i Hi.
      destruct (kn_ard_bound SK B LAWS cx (ka0 cx + i) HB ltac:(left; unfold ka0 in *; lia)) as (Hb & _).
      apply (kn_wr_keep (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) (ka0 cx + i)); [lia | exact (C4 i Hi) | |].
      + apply CUR. exact Hi.
      + pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWRO) & _).
        apply HWRO. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
        split; [cbn; right; right; left; reflexivity | cbn; unfold ka0 in *; lia]. }
  split.
  (* kgnl_at *)
  { assert (GW : forall kbs3, Z.of_nat (length kbs3) = NK_SIZE ->
      anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs3 -> anlk_at SEGS (rdW W4 (ms_mem ms4)) LA_G_NL kbs3).
    { intros kbs3 Hl ((Ha & Hw) & Hl'). split; [split|exact Hl'].
      - apply (kk_abytes_keep SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) LA_G_NL kbs3); [|exact Ha].
        intros i Hi. apply ko_ard_keep. right; right; left. rewrite Hl in Hi. lia.
      - intros i Hi. rewrite Hl in Hi.
        apply (writable_at_of_wseg SEGS _ LA_G_NL NK_SIZE); [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE; lia
          | exact (ki_gnl_wseg _ _ KI) | lia]. }
    destruct g as [j|]; cbn [kgnl_at] in Kgnl |- *.
    - destruct Kgnl as (kbs3 & Ha & Hk). exists kbs3. split; [|exact Hk].
      exact (GW kbs3 (proj2 Ha) Ha).
    - exact (GW (k_kbs cx) (proj2 Kgnl) Kgnl). }
  (* kla_at *)
  { destruct Kla as (la3 & (Hb & Hw) & Hl). exists la3. split; [|exact Hl]. split.
    - apply (kk_abytes_keep SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4) LA_LONG_ALIAS (la3 ++ [zb 0]));
        [|exact Hb].
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply ko_ard_keep.
      repeat (first [left; unfold LONG_ALIAS_SIZE; lia | right]).
    - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      apply (writable_at_of_wseg SEGS _ LA_LONG_ALIAS LONG_ALIAS_SIZE); [unfold LA_LONG_ALIAS; lia
        | unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE; lia | exact (ki_la_wseg _ _ KI) | unfold LONG_ALIAS_SIZE; lia]. }
Qed.
End o.

(* the exception set of an akept may be enlarged *)
Lemma ko_akept_mono : forall ly S W m W' m' lo hi (E E' : Z -> Prop), (forall a, E a -> E' a) ->
  akept SEGS B ly S W m W' m' lo hi E -> akept SEGS B ly S W m W' m' lo hi E'.
Proof.
  intros ly S W m W' m' lo hi E E' Hs (K1 & K2 & K3 & K4 & K5 & K6).
  split; [intros a H1 H2 Hn; apply (K1 a H1 H2); intros He; exact (Hn (Hs a He))|].
  split; [intros b mm i H1 H2 Hn; apply (K2 b mm i H1 H2); intros He; exact (Hn (Hs _ He))|].
  split; [intros a H1 H2 H3 Hn; apply (K3 a H1 H2 H3); intros He; exact (Hn (Hs a He))|].
  split; [intros c q a H1 H2 Hn; apply (K4 c q a H1 H2); intros He; exact (Hn (Hs a He))|].
  split; [exact K5 | exact K6].
Qed.

(* nl_error's side room: kernel's own (class 1) is unchanged by F (class 8) *)
Lemma kn_side_room1 : forall cx fpos S3, kbase SK B cx -> frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  aside_room S3 [(1, 1)].
Proof.
  intros cx fpos S3 HB HF3. pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hroom & _) & _).
  unfold aside_room, KERNEL_SIDE in *. apply Forall_inv_tail in Hroom. apply Forall_inv in Hroom.
  constructor; [|constructor]. cbn [fst snd] in *. rewrite HF3.
  replace (count_cid 1 ((KN_CID, fpos) :: frames (k_Sc cx))) with (count_cid 1 (frames (k_Sc cx))) by reflexivity.
  exact Hroom.
Qed.

(* THE OWN-CALLEE STEP: a call from a cut of kernel's walk of a function with an `aleaf_rd` contract whose write set
   is w2 and whose Post keeps w2 a struct nl_w whose n only grows (nl_error, attr_text); the walk continues at the
   return address with the cut rebuilt (registers rl' kept), w2's new fields n' >= n. *)
Theorem kn_ocall : forall (pcE K : Z) SIDE Pre Rd POST cx fpos k2 ly3 S3 W3 ms3 md3 pc ret rl rl' sl sh adv g n f,
  aleaf_rd SK SEGS PCAP_RLO PCAP_RHI B pcE K 0 SIDE Pre Rd kn_wawr kn_wpost ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
    (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  kat B cx fpos pc rl sl sh true adv g k2 ly3 S3 W3 ms3 md3 ->
  kw_at W3 ms3 (kW2 cx fpos) n f ->
  BASE + kpc pc = pcE ->
  0 <= K <= ksp1 cx - (ksp cx - KERNEL_AK) ->
  aside_room S3 SIDE ->
  getr (ms_regs ms3) 1 = w64 (BASE + kpc ret) -> 0 <= kpc ret < 2 ^ 40 -> kpc ret mod 2 = 0 ->
  getr (ms_regs ms3) 10 = w64 (kW2 cx fpos) ->
  Pre (ms_regs ms3) (rdW W3 (ms_mem ms3)) ->
  (forall a, Rd (ms_regs ms3) (rdW W3 (ms_mem ms3)) a -> akb SEGS B ly3 S3 (ksp1 cx - K) (ksp1 cx) a) ->
  incl rl' rl -> Forall (fun rv => acallee_saved (Z.of_nat (fst rv))) rl' ->
  kslots_okb sl = true -> (length sh <= 0x448)%nat ->
  (forall ly4 S4 W4 ms4 md4 n' f',
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
       (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly4 S4 W4 (ms_mem ms4) md4 k2 ->
     frames S4 = (KN_CID, fpos) :: frames (k_Sc cx) ->
     kat B cx fpos ret rl' sl sh true adv g k2 ly4 S4 W4 ms4 md4 -> kw_at W4 ms4 (kW2 cx fpos) n' f' -> n <= n' ->
     SRr SEGS W4 (mkCfg ms4 md4) (POST cx)) ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros pcE K SIDE Pre Rd POST cx fpos k2 ly3 S3 W3 ms3 md3 pc ret rl rl' sl sh adv g n f
    HC HB HJ3 HF3 HK Hkw Hpc HKP Hroom Hra Hret1 Hret2 Ha0 HPre HRd Hrl Hcs Hsl Hsh HCONT.
  pose proof HK as (Km & Kr0 & Kreq & Ksv & Kfr & Ksh & Ksl & KJ & (Kak & Kro) & Kcur & Kgnl & Kla).
  pose proof Km as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & (S4' & S5') & S6 & S7 & S8 & _).
  pose proof (kn_sp1 SK B cx HB) as (_ & _ & SP46 & _).
  destruct (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB KJ) as (F1 & F2 & _ & _).
  pose proof HB as ((HJ0 & HGok & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hev & _) & _).
  pose proof Kr0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  assert (Hsp : spZ (ms_regs ms3) = ksp1 cx).
  { unfold spZ. transitivity (bv_unsigned (w64 (ksp1 cx))); [f_equal; exact R2|].
    unfold w64. apply unsigned_lit_small. lia. }
  assert (Ha0' : aarg (ms_regs ms3) 0 = kW2 cx fpos).
  { unfold aarg, argZ. transitivity (bv_unsigned (getr (ms_regs ms3) 10)); [reflexivity|].
    rewrite Ha0. unfold w64. apply unsigned_lit_small. unfold kW2, KN_W2. lia. }
  rewrite (kn_ms_shape ms3 (BASE + kpc pc) M1 M2 M3 M4 M5 M6). rewrite Hpc.
  eapply SRr_bind.
  { apply (HC (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx)
      (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 (ms_regs ms3)).
    - unfold apre.
      split; [exact HJ3|]. split; [exact HGok|]. split; [exact Kro|].
      split; [rewrite Hra; apply ret_ok_codeptr_v; [exact Hret1 | exact Hret2]|].
      split; [unfold raZ; rewrite Hra; unfold w64; rewrite (lv_text LV); unfold link_text;
              rewrite unsigned_lit_small by lia; lia|].
      split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
      split; [rewrite Hsp; pose proof (kn_sp1 SK B cx HB) as (_ & HM & _); lia|].
      split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
      split; [pose proof KJ as (J1 & _); rewrite J1; exact Hev|].
      split; [exact Hroom|].
      split.
      + intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha. rewrite Ha0' in Ha.
        apply (ajw_frame B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) ly3 S3
          ((KN_CID, fpos) :: k_own cx) KN_CID fpos a); [left; reflexivity | | ].
        * rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos HJ3)).
          rewrite <- (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos HJ0)).
          change (fs_frame_bytes KN_CID) with 16384. unfold kW2, KN_W2, NW_SIZE, kF in *. lia.
        * unfold kW2, KN_W2, NW_SIZE, kF in *. lia.
      + intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha. rewrite Ha0' in Ha.
        apply (kX_not_ro SK B LAWS cx fpos k2 ly3 S3 md3 a HB KJ). unfold kX_in. right; left.
        change (fs_frame_bytes KN_CID) with 16384. unfold kW2, KN_W2, NW_SIZE in Ha. lia.
    - intros a Ha. rewrite Hsp. exact (HRd a Ha).
    - exact HPre. }
  cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HF4 & Hfds & Hfs & HAK4 & _ &
    (HS4 & Hperm4 & HPost)).
  rewrite Z.add_0_r in HJ4. rewrite Hsp in HAK4.
  assert (HAK' : akept SEGS B ly3 S3 W3 (ms_mem ms3) W4 mem4 (ksp1 cx - K) (ksp1 cx)
    (fun a => kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE)).
  { refine (ko_akept_mono ly3 S3 W3 (ms_mem ms3) W4 mem4 (ksp1 cx - K) (ksp1 cx) _ _ _ HAK4).
    intros a (r & Hr & Ha). destruct Hr as [<- | []].
    cbn [fst snd] in Ha. rewrite Ha0' in Ha. exact Ha. }
  destruct (anlw_of_nlw_fields SEGS _ _ _ _ Hkw) as (bs & Hbs & Hwf & Hn & Hf).
  unfold kn_wpost in HPost. rewrite Ha0' in HPost. destruct (HPost bs Hbs) as (bs' & Hbs' & Hwf' & Hle).
  set (ms4 := mkst regs4 (getr (ms_regs ms3) 1) mem4 (seg_rom SEGS)).
  assert (Hw2 : forall a, kW2 cx fpos <= a < kW2 cx fpos + NW_SIZE -> aview SEGS (w_H W4) (ms_mem ms4) a <> None).
  { intros a Ha. pose proof Hbs' as ((Hab & _) & Hlen). destruct Hab as (_ & _ & Hab).
    pose proof (Hab (Z.to_nat (a - kW2 cx fpos)) ltac:(rewrite <- (Nat2Z.id (length bs')), Hlen; lia)) as Hm.
    rewrite Z2Nat.id in Hm by lia. replace (kW2 cx fpos + (a - kW2 cx fpos)) with a in Hm by lia.
    unfold aview. cbn [ms_mem ms4 mkst]. rewrite Hm.
    destruct (nth_error bs' (Z.to_nat (a - kW2 cx fpos))) eqn:En; [discriminate|].
    apply nth_error_None in En. rewrite <- (Nat2Z.id (length bs')), Hlen in En. lia. }
  assert (HKm : kms ret ms4).
  { unfold kms, ms4. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
    rewrite Hra. repeat split; reflexivity. }
  apply (HCONT ly4 S4 W4 ms4 md4 (nw_n bs') (nw_full bs')).
  - exact HJ4.
  - rewrite HF4. exact HF3.
  - eapply kat_ocall; try eassumption.
  - exact (nlw_fields_of_anlw SEGS _ _ _ Hbs' Hwf').
  - rewrite <- Hn. exact Hle.
Qed.

End b.
End a.

Print Assumptions kat_ocall.
Print Assumptions kn_ocall.
