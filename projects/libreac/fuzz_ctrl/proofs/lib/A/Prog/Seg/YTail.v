(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1441 of its 1505 lines of code are new or changed and 947 lines of the source are left out. *)
(* A Theorem Labs lane of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A, libreac v1.9.0): the release tail 0x82b80-0x82bf0
   (v1.8 0x82ac0-0x82b30). seg_Y3, seg_Y2, seg_Y1 and seg_Jrel are S_Y3, S_Y2, S_Y1 and S_Jrel of Seg/Slot.v, over
   the official v1.9 cuts of SlotInv.v (Inv_A82bb0, Inv_A82bac, Inv_A82b9c, Inv_Jrel; v1.8 Inv_A82af0, Inv_A82aec,
   Inv_A82adc, Inv_Jrel, renamed by v190-cutnames-A.tsv (a working note, not in this delivery)). The v1.9 tail is the v1.8 one moved
   by +0xc0 with two immediates renumbered: the frame size 3040 -> 3136 (0x82b94 `addiw a1,a0,-0x3c0`) and the
   frame shadow length 380 -> 392 (0x82ba4 `li a1,0x188`). The two release calls go through their in-tree
   contracts, whose constants are still v1.8 on the DRAFT v1.9 base: frame_release_6 / __asan_stack_free_6
   (asan_stack_free_c.ASAN_STACK_FREE_6 = 0x3dbd4, v1.9 0x3dbf4) and meta_fill_00 / __asan_set_shadow_00
   (asan_set_shadow_c.ASAN_SET_SHADOW_00 = 0x54ec8, v1.9 0x54ee8); this file names the v1.9 call targets. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_free_c asan_set_shadow_c asan_stack_malloc_c asan_set_shadow memset.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Sf6.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_free_c.
Module SS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadow_c.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The W^X fact evt_normalize needs, proved here on image A's own segments (rsegs, Img0.v:3), by the same proof as
   BzBridge.v:37 wx_apart_asan. It replaces PFrameAPI.wx_apart_rsegs: PFrameAPI carries PLAIN-build values
   (pframe_asan's ms_malloc / ms_free ...; auditor a Theorem Labs lane, 2026-10-28 22:18Z) and was dropped from the unit as an
   orphan, so this ASan file must not depend on it. Do not re-add the Require. *)
Lemma ytail_wx_apart : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section YTail.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Let API := APIf rc.

(* The Lib-evt -> SR bridge (as F18's sl_run_lib: this lane's Y3 epilogue is a Lib.Exec.evt run). *)
Lemma sl_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

Lemma rd8 : forall m A w, bytes_at rsegs m A (le8 w) -> ov_read_bytes rsegs m (wa A) 8 = Some (le8 w).
Proof.
  intros m A w H.
  pose proof (bytes_at_ov_read rsegs m A (le8 w) 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH.
Qed.

(* ---- The allocator laws this file takes apart, each in exactly one place. The generated Contract.v grows a law only
   by appending conjuncts, at every nesting level, so no proof below destructs a law's conclusion itself: it uses
   one of these lemmas, whose statement is fixed here and whose proof is the one place to re-fit. *)
Lemma yt_law_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH HS HW.
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH HS HW)
    as (H1 & H2 & H3 & H4).
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma yt_law_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Hw Hr HS HW HOK.
  destruct (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md FS
              HAH Hw Hr HS HW HOK) as (H1 & H2 & H3 & H4).
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma yt_law_mat_le : forall H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md') /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md md' Hmat.
  destruct (AC.a_laws_mat_le _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md md' Hmat)
    as (H1 & _ & H3 & _).
  exact (conj H1 H3).
Qed.

(* a_laws_blocks: a live block ends at or below stklo, and each of its bytes is app memory outside the FakeStack. *)
Lemma yt_law_blocks : forall H mem md q k,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (q, k) H ->
  q + k <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, q <= a < q + k -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md q k HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md q k HAH Hin)
    as (_ & _ & Hend & _ & Hall).
  split; [exact Hend|]. intros a Ha.
  destruct (Hall a Ha) as (Happ & _ & _ & _ & Hnfs). exact (conj Happ Hnfs).
Qed.

Lemma yt_law_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ FS mod 4096 = 0 /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw Hr.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hr)
    as (H1 & H2 & H3 & H4).
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* a_laws_fs_state, its first clause: the FakeStack at tp is a_fs_ok. *)
Lemma yt_law_fs_ok : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hr.
  destruct (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hr)
    as (Hok & _).
  exact Hok.
Qed.

(* a_fs_ok, its first clause: every FakeStack byte is writable and present. *)
Lemma yt_fs_ok_cells : forall mem FS, AC.a_fs_ok mem FS ->
  forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b.
Proof. intros mem FS (H1 & _). exact H1. Qed.

(* ENT, read in one place (it grows by appended conjuncts too): the entry sp is S and the entry tp is the as_tp word. *)
Lemma yt_ent_regs : forall g hb mem md, ENT APIf g hb mem md ->
  AC.aspZ (g_regs g) = g_S g /\ getr (g_regs g) 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS).
Proof. intros g hb mem md (Hsp & Htp & _). exact (conj Hsp Htp). Qed.

(* Y3's run: 0x82bb0 li a0,0; addi sp,s0,-416; ld ra / s0-s11 from [sp+408 .. sp+312] = [S-8 .. S-104];
   addi sp,sp,416; ret. Reaches pc = R (the saved ra) with a0 = 0 and the 13 caller registers reloaded. *)
Lemma y3_evt :
  forall (ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sv Rv : Z)
         (w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : word),
    v0 = Z_to_bv 64 Sv -> 416 <= Sv < 2 ^ 64 -> Rv mod 2 = 0 -> 0 <= Rv < 2 ^ 64 ->
    w1 = Z_to_bv 64 Rv ->
    bytes_at rsegs m (Sv - 104) (le8 w27 ++ le8 w26 ++ le8 w25 ++ le8 w24 ++ le8 w23 ++ le8 w22 ++ le8 w21 ++
      le8 w20 ++ le8 w19 ++ le8 w18 ++ le8 w9 ++ le8 w8 ++ le8 w1) ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         ms' = MS (mkR w1 (Z_to_bv 64 Sv) gp tp t0' t1' t2' w8 w9
                       (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
                       t3' t4' t5' t6')
                  Fr (Z_to_bv 64 Rv) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82bb0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Fr fc m Sv Rv w1 w8 w9 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
    -> HS HRe HRb -> HSV.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 104) (le8 w27) _) HSV) as (B27 & Q1).
  rewrite length_le8 in Q1. replace (Sv - 104 + Z.of_nat 8) with (Sv - 96) in Q1 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 96) (le8 w26) _) Q1) as (B26 & Q2).
  rewrite length_le8 in Q2. replace (Sv - 96 + Z.of_nat 8) with (Sv - 88) in Q2 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 88) (le8 w25) _) Q2) as (B25 & Q3).
  rewrite length_le8 in Q3. replace (Sv - 88 + Z.of_nat 8) with (Sv - 80) in Q3 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 80) (le8 w24) _) Q3) as (B24 & Q4).
  rewrite length_le8 in Q4. replace (Sv - 80 + Z.of_nat 8) with (Sv - 72) in Q4 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 72) (le8 w23) _) Q4) as (B23 & Q5).
  rewrite length_le8 in Q5. replace (Sv - 72 + Z.of_nat 8) with (Sv - 64) in Q5 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 64) (le8 w22) _) Q5) as (B22 & Q6).
  rewrite length_le8 in Q6. replace (Sv - 64 + Z.of_nat 8) with (Sv - 56) in Q6 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 56) (le8 w21) _) Q6) as (B21 & Q7).
  rewrite length_le8 in Q7. replace (Sv - 56 + Z.of_nat 8) with (Sv - 48) in Q7 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 48) (le8 w20) _) Q7) as (B20 & Q8).
  rewrite length_le8 in Q8. replace (Sv - 48 + Z.of_nat 8) with (Sv - 40) in Q8 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 40) (le8 w19) _) Q8) as (B19 & Q9).
  rewrite length_le8 in Q9. replace (Sv - 40 + Z.of_nat 8) with (Sv - 32) in Q9 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 32) (le8 w18) _) Q9) as (B18 & Q10).
  rewrite length_le8 in Q10. replace (Sv - 32 + Z.of_nat 8) with (Sv - 24) in Q10 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 24) (le8 w9) _) Q10) as (B9 & Q11).
  rewrite length_le8 in Q11. replace (Sv - 24 + Z.of_nat 8) with (Sv - 16) in Q11 by lia.
  destruct (proj1 (bytes_at_app rsegs m (Sv - 16) (le8 w8) _) Q11) as (B8 & Q12).
  rewrite length_le8 in Q12. replace (Sv - 16 + Z.of_nat 8) with (Sv - 8) in Q12 by lia.
  pose proof (rd8 m (Sv - 104) w27 B27) as L27.
  pose proof (rd8 m (Sv - 96) w26 B26) as L26.
  pose proof (rd8 m (Sv - 88) w25 B25) as L25.
  pose proof (rd8 m (Sv - 80) w24 B24) as L24.
  pose proof (rd8 m (Sv - 72) w23 B23) as L23.
  pose proof (rd8 m (Sv - 64) w22 B22) as L22.
  pose proof (rd8 m (Sv - 56) w21 B21) as L21.
  pose proof (rd8 m (Sv - 48) w20 B20) as L20.
  pose proof (rd8 m (Sv - 40) w19 B19) as L19.
  pose proof (rd8 m (Sv - 32) w18 B18) as L18.
  pose proof (rd8 m (Sv - 24) w9 B9) as L9.
  pose proof (rd8 m (Sv - 16) w8 B8) as L8.
  pose proof (rd8 m (Sv - 8) (Z_to_bv 64 Rv) Q12) as L1.
  clear B27 B26 B25 B24 B23 B22 B21 B20 B19 B18 B9 B8 Q12 HSV.
  step. step.
  do 13 step.
  step. step.
  rewrite ?Z.add_0_r.
  replace (Sv + -416 + 416) with Sv by lia.
  replace (ret_pc (Z_to_bv 64 Rv)) with (Z_to_bv 64 Rv)
    by (symmetry; apply ret_pc_even; [lia | exact HRe]).
  apply LE.evt_done. do 14 eexists. reflexivity.
Qed.

Lemma hcut_y3 : Hcut B APIf ra (Inv_A82bb0 B APIf ra).
Proof.
  intros g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & Ec & HRT & HAH & Hstk0 & Hro & Hsn & Hhalt & Hs0 & Hgp & Htp & Hsaved &
    Herrno & Hwin & HENT).
  subst c. rewrite SEGS.
  assert (HSb : 416 <= g_S g < 2 ^ 64).
  { destruct (Hwin (g_S g - AF.SLOT_STACK) ltac:(unfold AF.SLOT_STACK; lia)) as (_ & (Hlo & _ & _ & _)).
    destruct (Hwin (g_S g - 1) ltac:(unfold AF.SLOT_STACK; lia)) as (_ & (_ & _ & Hhi & _)).
    unfold AF.SLOT_STACK, APPMEM_END in *. lia. }
  pose proof FF as (_ & Hrae & _).
  assert (Hrab : 0 <= ra mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (Hrae2 : (ra mod 2 ^ 64) mod 2 = 0).
  { apply Z.mod_divide in Hrae; [|lia]. destruct Hrae as (k & Ek). rewrite Ek.
    replace (2 ^ 64) with (2 ^ 63 * 2) by (vm_compute; reflexivity).
    rewrite Z.mul_mod_distr_r by lia. apply Z.mod_mul. lia. }
  assert (Era : Z_to_bv 64 (ra mod 2 ^ 64) = Z_to_bv 64 ra)
    by (rewrite <- unsigned_lit_wrap; apply Z_to_bv_lit_self).
  (* the entry sp is S (ENT's first conjunct, aspZ (g_regs g) = g_S g), as a register equality *)
  assert (Hsp2 : getr (g_regs g) 2 = Z_to_bv 64 (g_S g)).
  { pose proof (proj1 (yt_ent_regs g [] mem md HENT)) as Hasp. unfold AC.aspZ in Hasp. rewrite <- Hasp. symmetry.
    apply Z_to_bv_lit_self. }
  apply (sl_run_lib regs (Z_to_bv 64 0x82bb0) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 ra /\ mem' = mem /\
       getr R0 10 = Z_to_bv 64 0 /\
       (forall r, AC.a_callee_saved r -> getr R0 (Z_to_bv 5 r) = getr (g_regs g) (Z_to_bv 5 r)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of.
    eapply LE.evt_mono.
    { eapply y3_evt with (Sv := g_S g) (Rv := ra mod 2 ^ 64)
        (w1 := Z_to_bv 64 (ra mod 2 ^ 64)) (w8 := getr (g_regs g) 8) (w9 := getr (g_regs g) 9) (w18 := getr (g_regs g) 18)
        (w19 := getr (g_regs g) 19) (w20 := getr (g_regs g) 20) (w21 := getr (g_regs g) 21)
        (w22 := getr (g_regs g) 22) (w23 := getr (g_regs g) 23) (w24 := getr (g_regs g) 24)
        (w25 := getr (g_regs g) 25) (w26 := getr (g_regs g) 26) (w27 := getr (g_regs g) 27).
      - unfold rg in Hs0. exact Hs0.
      - exact HSb.
      - exact Hrae2.
      - exact Hrab.
      - reflexivity.
      - unfold saved_bytes in Hsaved. rewrite Era. exact Hsaved. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & E).
      rewrite Era in E.
      eexists _, (Z_to_bv 64 ra), mem. split; [exact E|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      intros r Hr. unfold AC.a_callee_saved in Hr.
      destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
      - replace (getr (g_regs g) (Z_to_bv 5 2)) with (getr (g_regs g) 2)
          by (f_equal; apply bv_eq; vm_compute; reflexivity).
        rewrite Hsp2. reflexivity.
      - replace (getr (g_regs g) (Z_to_bv 5 3)) with (getr (g_regs g) 3)
          by (f_equal; apply bv_eq; vm_compute; reflexivity).
        rewrite <- Hgp. reflexivity.
      - replace (getr (g_regs g) (Z_to_bv 5 4)) with (getr (g_regs g) 4)
          by (f_equal; apply bv_eq; vm_compute; reflexivity).
        rewrite <- Htp. reflexivity.
      - replace (getr (g_regs g) (Z_to_bv 5 8)) with (getr (g_regs g) 8)
          by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
      - replace (getr (g_regs g) (Z_to_bv 5 9)) with (getr (g_regs g) 9)
          by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
      - assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/
                     r = 27) by lia.
        destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
        + replace (getr (g_regs g) (Z_to_bv 5 18)) with (getr (g_regs g) 18)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 19)) with (getr (g_regs g) 19)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 20)) with (getr (g_regs g) 20)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 21)) with (getr (g_regs g) 21)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 22)) with (getr (g_regs g) 22)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 23)) with (getr (g_regs g) 23)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 24)) with (getr (g_regs g) 24)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 25)) with (getr (g_regs g) 25)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 26)) with (getr (g_regs g) 26)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity.
        + replace (getr (g_regs g) (Z_to_bv 5 27)) with (getr (g_regs g) 27)
            by (f_equal; apply bv_eq; vm_compute; reflexivity). reflexivity. }
  - intros R0 pc' mem' regs' md' (Hpc & Hmem & H10 & Hkept) Hreg Hmat.
    subst pc' mem'.
    apply SR_ret.
    destruct (yt_law_mat_le (g_H g) mem md md' Hmat) as (HAHm & _).
    apply (ent_post B APIf ra empty FF).
    + exact (ent_mat APIf g [] mem md md' HENT Hmat).
    + rewrite (proj1 (yt_ent_regs g [] mem md HENT)). exact (AsanRTInv.RT_any (g_S g - 416) (g_S g) mem md md' HRT).
    + exact (HAHm HAH).
    + exact Hro.
    + destruct Hsn as (Hsa & Hsb & Hsc). split; [exact Hsa|]. split; [exact Hsb|].
      rewrite (sl_mat_fds md md' Hmat). exact Hsc.
    + rewrite (AsanLift.mat_le_halted md md' Hmat). exact Hhalt.
    + rewrite Hreg. exact H10.
    + intros r Hr. rewrite Hreg. exact (Hkept r Hr).
    + exact Herrno.
    + exact Hwin.
Qed.

(* S_Y3 of Seg/Slot.v (v1.9 cut names). *)
Theorem seg_Y3 : Hcut B APIf ra (Inv_A82bb0 B APIf ra).
Proof. exact hcut_y3. Qed.

(* ---- Helpers the release tail needs. The cuts of this tail carry FRAH (FRA without the two spills, with the
   frame header word a parameter), so the FRA lemmas of SlotInv.v and Seg/Tac_slot.v do not apply; each helper
   below takes the conjuncts it reads instead of the whole record. ---- *)

(* Above the image there is no read-only byte, so MemNorm.normalize changes nothing there (as F18.v's
   ro_addr_hi): the FakeStack, the real stack and the shadow all sit above GT = 0x5fe000. *)
Definition seg_tops_below (sg : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sg.

Lemma rsegs_below_gt : seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_below : forall sg top x n s,
  seg_tops_below sg top = true -> find_segment sg x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sg as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_tops_below in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma ro_high : forall a, 0x5fe000 <= a -> 0 <= a < 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr rsegs (wa a) = false.
Proof.
  intros a Hgt Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (find_segment_below sg 0x5fe000 x n s rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma ro_high_w : forall a : word, 0x5fe000 <= bv_unsigned a ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr rsegs a = false.
Proof.
  intros a Hgt. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (find_segment_below sg 0x5fe000 x n s rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; lia | cbn in L; lia] end.
Qed.

Lemma ba_rel1 : forall m m0 a bs, mem_rel rsegs m m0 -> bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs.
Proof. intros m m0 a bs R H. exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma addressable_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma asan_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (ba_rel1 m m0 a bs R ltac:(assumption)) end.
Qed.

Lemma wview_rel_hi : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (ro_high a ltac:(lia) ltac:(lia))).
  split; auto.
Qed.

Lemma shadow_rw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma stk_rel_hi : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma stk_rel_hi_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

(* fra_app's content for FRAH's frame-location disjunction: on the real arm the frame lies in
   [stklo, APPMEM_END) and the allocator laws put stklo at or above HIGHMEM_BEG; on the side arm it lies in the
   FakeStack, whose bytes a_laws_fs_place makes app memory above GT. *)
Lemma loc_app : forall (H : list (Z * Z)) fr mem md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  ((forall a, fr <= a < fr + FRAME_BYTES ->
      AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) \/
   (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a)) ->
  AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a).
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros H fr mem md HAH Hloc.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md HAH).
  destruct Hloc as [Hreal|Hfs].
  - destruct (Hreal fr ltac:(lia)) as (Hlo1 & _).
    unfold AC.GT, HIGHMEM_BEG in *.
    split; [lia|]. intros a Ha. destruct (Hreal a Ha) as (Hlo2 & Hhi2).
    unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
  - destruct (Hfs fr ltac:(lia)) as (FS0 & HFS0r & Hw0 & Hlo0 & Hhi0).
    destruct (yt_law_fs_place H mem md FS0 HAH Hw0 HFS0r) as (HGTb & _ & _ & _).
    split; [unfold AC.GT in *; lia|]. intros a Ha.
    destruct (Hfs a Ha) as (FSa & HFSar & Hwa & Hloa & Hhia).
    destruct (yt_law_fs_place H mem md FSa HAH Hwa HFSar) as (_ & _ & _ & Happ).
    exact (Happ a ltac:(lia)).
Qed.

(* The frame covers whole granules (fr mod 32 = 0, FRAME_BYTES = 3136, 3136 mod 8 = 0), so its FRAME_SHADOW = 392
   shadow bytes are exactly the shadow bytes of its own bytes. *)
Lemma fr_mod8 : forall fr, fr mod 32 = 0 -> fr mod 8 = 0.
Proof.
  intros fr H. pose proof (Z.mod_eq fr 32 ltac:(lia)) as X. rewrite H in X.
  replace fr with ((4 * (fr / 32)) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma sh_in_shadow : forall fr, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr Happ x Hx.
  assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
  { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
  pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
  replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
  unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia.
Qed.

Lemma sh_of_frame : forall fr a, fr mod 32 = 0 -> 0 <= fr -> fr <= a < fr + FRAME_BYTES ->
  Sfr fr <= shadow_addr a < Sfr fr + FRAME_SHADOW.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr a Hfrm Hfr0 Ha. pose proof (fr_mod8 fr Hfrm) as Hfr8.
  unfold Sfr, shadow_addr. revert Ha Hfr8 Hfr0 HFBv HFSv. clear. intros. Z.div_mod_to_equations. lia.
Qed.

(* Each of the FRAME_SHADOW shadow bytes is the shadow byte of one frame byte. *)
Lemma sh_inv : forall fr x, Sfr fr <= x < Sfr fr + FRAME_SHADOW ->
  shadow_addr (fr + 8 * (x - Sfr fr)) = x /\ fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr x Hx.
  assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
  { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  unfold Sfr, shadow_addr in *. split; [rewrite Hdiv; lia | lia].
Qed.

Lemma sh_not_frame : forall fr b, fr mod 32 = 0 -> 0 <= fr -> 0 <= b -> ~ (fr <= b < fr + FRAME_BYTES) ->
  ~ (Sfr fr <= shadow_addr b < Sfr fr + FRAME_SHADOW).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr b Hfrm Hfr0 Hb0 Hnb Hin. apply Hnb. pose proof (fr_mod8 fr Hfrm) as Hfr8.
  unfold Sfr, shadow_addr in Hin. revert Hin Hfr8 Hb0 Hfr0 HFBv HFSv. clear. intros. Z.div_mod_to_equations. lia.
Qed.

(* The same three facts for a block of n granules (the FakeStack frame of Y1 is 4096 bytes = 512 granules). *)
Lemma sh_in_shadow_blk : forall base n, 0 < n -> (forall a, base <= a < base + 8 * n -> app_mem a) ->
  forall x, shadow_addr base <= x < shadow_addr base + n -> in_shadow x.
Proof.
  intros base n Hn Happ x Hx.
  assert (Hdiv : (base + 8 * (x - shadow_addr base)) / 8 = base / 8 + (x - shadow_addr base)).
  { replace (8 * (x - shadow_addr base)) with ((x - shadow_addr base) * 8) by lia.
    rewrite Z.div_add by lia. reflexivity. }
  assert (Hin : base <= base + 8 * (x - shadow_addr base) < base + 8 * n) by lia.
  pose proof (shadow_of_app (base + 8 * (x - shadow_addr base)) (Happ _ Hin)) as His.
  replace (shadow_addr (base + 8 * (x - shadow_addr base))) with x in His; [exact His|].
  unfold shadow_addr at 1. rewrite Hdiv. unfold shadow_addr. lia.
Qed.

Lemma sh_inv_blk : forall base n x, shadow_addr base <= x < shadow_addr base + n ->
  shadow_addr (base + 8 * (x - shadow_addr base)) = x /\
  base <= base + 8 * (x - shadow_addr base) < base + 8 * n.
Proof.
  intros base n x Hx.
  assert (Hdiv : (base + 8 * (x - shadow_addr base)) / 8 = base / 8 + (x - shadow_addr base)).
  { replace (8 * (x - shadow_addr base)) with ((x - shadow_addr base) * 8) by lia.
    rewrite Z.div_add by lia. reflexivity. }
  unfold shadow_addr in *. split; [rewrite Hdiv; lia | lia].
Qed.

Lemma sh_not_blk : forall base n b, base mod 8 = 0 -> 0 <= base -> 0 <= b -> ~ (base <= b < base + 8 * n) ->
  ~ (shadow_addr base <= shadow_addr b < shadow_addr base + n).
Proof.
  intros base n b H8 Hb1 Hb0 Hnb Hin. apply Hnb.
  unfold shadow_addr in Hin. revert Hin H8 Hb0 Hb1. clear. intros. Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_rw_rel_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

(* The FakeStack flag bytes of the eleven size classes fill [FS + 4096, FS + 36864) without overlap, so only the
   released frame's own flag byte is the one the release writes. *)
Lemma fs_flag_apart : forall FS c j' j, (c <= 10)%nat -> 0 <= j' < AC.a_fs_M c -> 0 <= j < 256 ->
  AC.a_fs_flag FS c j' = AC.a_fs_flag FS 6 j -> (c = 6)%nat /\ j' = j.
Proof.
  intros FS c j' j Hc Hj' Hj Heq.
  assert (Hcs : (c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/
                 c = 10)%nat) by lia.
  unfold AC.a_fs_flag, AC.a_fs_M in Heq, Hj'.
  destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
    cbn in Heq, Hj'; lia.
Qed.

(* Y1's write set: the frame's flag byte, its 512 shadow bytes and the callee's own 32-byte stack window. All
   three lie above GT, where no runtime cell is. *)
Lemma rt_disjoint_hi3 : forall l1 h1 l2 h2 l3 h3,
  0x5fe000 <= l1 -> 0x5fe000 <= l2 -> 0x5fe000 <= l3 ->
  AsanRTInv.rt_disjoint [(l1, h1); (l2, h2); (l3, h3)].
Proof.
  intros l1 h1 l2 h2 l3 h3 H1 H2 H3.
  unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
    RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM,
    RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
  cbn. repeat split; lia.
Qed.

(* One write interval above GT is apart from every runtime cell (all of them end below GT). *)
Lemma rt_disjoint_hi1 : forall lo hi, 0x5fe000 <= lo -> AsanRTInv.rt_disjoint [(lo, hi)].
Proof.
  intros lo hi Hlo. unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
    RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM,
    RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
  cbn. repeat split; lia.
Qed.

(* ---- Y2's call (0x82bac `jal 54ee8 <meta_fill_00>`): the 392 shadow bytes of the frame are set to 0x00 (the
   bytes are marked usable). The contract (asan_set_shadow_00_contract, proved by asan_set_shadow_00_holds from
   memset_holds) needs mem_inv, which the frame does not carry, so the call is run on the normalized memory
   (MemNorm.evt_normalize from the frame's ro_agree) and its post is carried back across mem_rel / ro_same. *)
Lemma y2_evt :
  forall (ra0 sp0 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (A : Z) (junk : list byte),
  0 <= A < 2 ^ 64 ->
  (forall i, 0 <= i < 392 -> in_shadow (A + i)) ->
  rw_cells rsegs (normalize rsegs mem) A [CB 392%nat junk] ->
  asan_cells (normalize rsegs mem) ->
  ro_agree rsegs mem ->
  LE.evt rsegs
    (fun ms => exists (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82bb0) sp0 gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       Frame.munch [(A, A + 392)] mem m' /\ Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' A (repeat (Z_to_bv 8 0) 392))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 392) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82bac) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem A junk HAb HSh Hrw Hac HRO.
  step.
  pose proof (mem_rel_normalize rsegs mem HRO) as REL.
  pose proof (asan_set_shadow_00_holds memset_holds) as SS0.
  unfold asan_set_shadow_00_contract, asan_set_shadow_contract, ASAN_SET_SHADOW_00 in SS0. cbv zeta in SS0.
  assert (HC : LE.evt rsegs
      (asan_set_shadow_post 0 (Z_to_bv 64 0x82bb0) sp0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         fp_regs fp_csr (Z_to_bv 64 A) (Z_to_bv 64 392) (normalize rsegs mem))
      (MS (mkR (Z_to_bv 64 0x82bb0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 392) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          fp_regs (Z_to_bv 64 0x54ee8) fp_csr None (normalize rsegs mem) (seg_rom rsegs))).
  { apply (SS0 (Z_to_bv 64 0x82bb0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 392)
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             fp_regs fp_csr (normalize rsegs mem) junk).
    - rewrite !(MState.unsigned_lit A) by lia. rewrite !(MState.unsigned_lit 392) by lia. exact HSh.
    - rewrite !(MState.unsigned_lit A) by lia. rewrite !(MState.unsigned_lit 392) by lia. exact Hrw.
    - exact Hac.
    - apply mem_inv_normalize. }
  pose proof (evt_normalize rsegs _ _ fp_regs _ fp_csr None mem (seg_rom rsegs)
                ytail_wx_apart HRO HC) as HE.
  eapply LE.evt_mono; [exact HE|].
  intros ms (st0 & Hp & Hrel & Hro2).
  unfold asan_set_shadow_post in Hp.
  destruct Hp as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m0' & -> & MU & WM & MI & RW).
  rewrite !(MState.unsigned_lit A) in MU, RW by lia.
  rewrite !(MState.unsigned_lit 392) in MU, RW by lia.
  destruct ms as [R' F' pcv' svc' rv' fc' m' ro'].
  destruct Hrel as (HRg & HFg & HPg & HSg & HRv & HFc & HRo & HMR).
  cbn in HRg, HFg, HPg, HSg, HRv, HFc, HRo, HMR. subst.
  cbn in Hro2.
  exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m'.
  split.
  { replace (ret_pc (Z_to_bv 64 0x82bb0)) with (Z_to_bv 64 0x82bb0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    reflexivity. }
  split; [exact (munch_rel rsegs [(A, A + 392)] mem (normalize rsegs mem) m' m0' REL HMR Hro2 MU)|].
  split; [exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' REL HMR Hro2 WM)|].
  split; [exact (ro_agree_same rsegs mem m' HRO Hro2)|].
  destruct RW as ((Hwf & Hba) & Hwr). cbn [cells_bytes app] in Hba. rewrite app_nil_r in Hba.
  exact (proj2 (bytes_at_rel rsegs m' m0' A _ HMR) Hba).
Qed.

(* y2_evt with the two argument registers as plain words plus their value equations, so that the cut's register
   map (Regs6ss.mkR_of) unifies with the start state. *)
Lemma y2_evt_r :
  forall (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (A : Z) (junk : list byte),
  a0w = Z_to_bv 64 A -> a1w = Z_to_bv 64 392 ->
  0 <= A < 2 ^ 64 ->
  (forall i, 0 <= i < 392 -> in_shadow (A + i)) ->
  rw_cells rsegs (normalize rsegs mem) A [CB 392%nat junk] ->
  asan_cells (normalize rsegs mem) ->
  ro_agree rsegs mem ->
  LE.evt rsegs
    (fun ms => exists (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82bb0) sp0 gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A) b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       Frame.munch [(A, A + 392)] mem m' /\ Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' A (repeat (Z_to_bv 8 0) 392))
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82bac) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem A junk -> -> HAb HSh Hrw Hac HRO.
  exact (y2_evt ra0 sp0 gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
           s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem A junk HAb HSh Hrw Hac HRO).
Qed.

(* S_Y2 of Seg/Slot.v (0x82bac `jal 54ee8 <meta_fill_00>` on the real arm, s5 = 0): the call marks the frame's
   FRAME_BYTES = 3136 bytes usable again by clearing its FRAME_SHADOW = 392 shadow bytes, which is exactly what
   Inv_A82bb0's whole-window addressability needs on top of FRAR's outside-the-frame window. *)
Theorem seg_Y2 : Hcut B APIf ra (Inv_A82bb0 B APIf ra) -> Hcut B APIf ra (Inv_A82bac B APIf ra).
Proof.
  intros HY3 g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HInv as (regs & mem & md & fr & s5 & Ec & HFRA & HENT & (Es5 & Ha0 & Ha1)).
  destruct HFRA as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5or & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  subst c s5. rewrite SEGS.
  destruct (loc_app ([] ++ g_H g) fr mem md HAH
              ltac:(destruct Hloc as [(_ & _ & Hx)|(_ & _ & Hx & _)]; [left|right]; exact Hx))
    as (Hgt & Happ).
  assert (HgtN : 6283264 <= fr) by (unfold AC.GT in Hgt; exact Hgt).
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hreal : forall a, fr <= a < fr + FRAME_BYTES ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END)
    by (destruct Hloc as [(_ & _ & Hx)|(Hx & _)]; [exact Hx | exfalso; lia]).
  clear Hloc.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HappW : forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> app_mem x).
  { intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. unfold HIGHMEM_BEG in Hhigh. right. lia. }
  pose proof (sh_in_shadow fr Happ) as HshIS.
  destruct Hsh as (shw & Hshb & Hshl).
  rewrite HFSv in Hshl. change (Z.to_nat 392) with 392%nat in Hshl.
  assert (HSAb : 0 <= Sfr fr /\ Sfr fr + 392 <= 2 ^ 64).
  { destruct Hshb as (H1 & H2 & _). rewrite Hshl in H2. split; [exact H1 | lia]. }
  assert (HSAlo : 0x7fff8000 <= Sfr fr).
  { unfold Sfr, shadow_addr, ASAN_K. assert (0 <= fr / 8) by (apply Z.div_pos; lia). lia. }
  assert (HOUT : forall x, ~ (Sfr fr <= x < Sfr fr + 392) -> Frame.outside [(Sfr fr, Sfr fr + 392)] x)
    by (intros x Hx; cbn; split; [exact Hx | exact I]).
  pose proof (mem_rel_normalize rsegs mem Hro) as REL.
  assert (HRW : rw_cells rsegs (normalize rsegs mem) (Sfr fr) [CB 392%nat shw]).
  { split.
    - split; [cbn; split; [exact Hshl | exact I]|].
      cbn [cells_bytes cbytes]. rewrite app_nil_r. exact (ba_rel1 mem _ _ _ REL Hshb).
    - replace (Z.of_nat (cells_size [CB 392%nat shw])) with 392 by (vm_compute; reflexivity).
      apply (wr_at_norm rsegs mem (normalize rsegs mem) (Sfr fr) 392 REL).
      + split; [lia|]. split; [lia|]. intros i Hi.
        exact (proj1 (AsanRTInv.RT_shadow_rw sp mem md HRT (Sfr fr + i)
                        (HshIS (Sfr fr + i) ltac:(lia)))).
      + intros i Hi. apply ro_high; lia. }
  assert (HAC0 : asan_cells (normalize rsegs mem))
    by exact (asan_cells_rel mem _ REL (AsanRTInv.RT_cells sp mem md HRT)).
  apply (sl_run_lib regs (Z_to_bv 64 0x82bac) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82bb0 /\
       Frame.munch [(Sfr fr, Sfr fr + 392)] mem mem' /\ Frame.wmono rsegs mem mem' /\
       ro_agree rsegs mem' /\ bytes_at rsegs mem' (Sfr fr) (repeat (Z_to_bv 8 0) 392) /\
       getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\ getr R0 8 = getr regs 8)
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of.
    eapply LE.evt_mono.
    { eapply y2_evt_r with (A := Sfr fr) (junk := shw).
      - exact Ha0.
      - exact Ha1.
      - lia.
      - intros i Hi. apply HshIS. lia.
      - exact HRW.
      - exact HAC0.
      - exact Hro. }
    { intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' &
                  E & MU & WM & HRO' & HB0).
      eexists _, _, m'. split; [exact E|].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact HRO'|].
      split; [exact HB0|].
      split; [reflexivity|]. split; [reflexivity | reflexivity]. }
  - intros R0 pc' mem' regs' md' (Hpc & MU & WM & HRO' & HB0 & E3 & E4 & E8) Hreg Hmat.
    subst pc'.
    assert (KBout : forall x, app_mem x -> Frame.outside [(Sfr fr, Sfr fr + 392)] x).
    { intros x Hap. apply HOUT. intro Hin. exact (app_not_shadow x Hap (HshIS x Hin)). }
    assert (KBmb : forall (sg : list Segment) x, app_mem x -> mbyte sg mem' x = mbyte sg mem x).
    { intros sg x Hap.
      assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia).
      assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { apply MU. rewrite MState.unsigned_lit by exact Hx64. exact (KBout x Hap). }
      unfold mbyte. rewrite Hm. reflexivity. }
    assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
    { intros sg x H0 H1. apply KBmb. unfold app_mem, LOWMEM_END. left. lia. }
    assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a _ H; exact (WM (Z_to_bv 64 a) H)).
    (* the heap invariant: the write is the shadow of frame bytes, which lie in [stklo, APPMEM_END) *)
    assert (Hstore : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by exact Ha.
      apply HOUT. intro Hin. apply Hns. destruct (sh_inv fr a Hin) as (Heq & Hran).
      right. right. right. exists (fr + 8 * (a - Sfr fr)). split; [symmetry; exact Heq|].
      right. left. exact (Hreal _ Hran). }
    destruct (yt_law_store ([] ++ g_H g) mem mem' md HAH Hstore Hwm) as (HAH1 & HOWN1 & HLO1 & HHI1).
    destruct (yt_law_mat_le ([] ++ g_H g) mem' md md' Hmat) as (HAHm & HLOm).
    (* every shadow byte is readable afterwards: the frame's 392 from the cleared list, the rest by munch *)
    assert (HshR0 : forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b).
    { intros a Hin.
      assert (Hx64 : 0 <= a < 2 ^ 64) by (pose proof (in_shadow_range a Hin); lia).
      assert (Hc : (Sfr fr <= a < Sfr fr + 392) \/ ~ (Sfr fr <= a < Sfr fr + 392)) by lia.
      destruct Hc as [Hinw|Houtw].
      - destruct HB0 as (Hb0 & Hb1 & Hb2).
        destruct (nth_error (repeat (Z_to_bv 8 0) 392) (Z.to_nat (a - Sfr fr))) as [bb|] eqn:Enth.
        + pose proof (Hb2 (Z.to_nat (a - Sfr fr)) ltac:(rewrite repeat_length; lia)) as HmE.
          rewrite Z2Nat.id in HmE by lia. replace (Sfr fr + (a - Sfr fr)) with a in HmE by lia.
          rewrite Enth in HmE. exists bb. exact HmE.
        + exfalso. apply nth_error_None in Enth. rewrite repeat_length in Enth. lia.
      - destruct (AsanRTInv.RT_shadow_rw sp mem md HRT a Hin) as (_ & b & Hmr).
        assert (Hmem : mem' (wa a) = mem (wa a))
          by (apply MU; rewrite Mem.wa_unsigned by exact Hx64; exact (HOUT a Houtw)).
        exists b. unfold mrd in *. rewrite Hmem. exact Hmr. }
    rewrite <- SEGS. apply HY3.
    exists regs', mem', md'.
    split; [reflexivity|].
    split.
    { exact (AsanRTInv.RT_meta_write sp (g_S g - 416) mem mem' md md' [(Sfr fr, Sfr fr + 392)]
               HRT MU WM (rt_disjoint_hi1 (Sfr fr) (Sfr fr + 392) ltac:(lia)) HshR0). }
    split; [exact (HAHm HAH1)|].
    split; [rewrite HLOm, HLO1; exact Hstklo|].
    split; [exact HRO'|].
    split.
    { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split].
      - destruct Hcse as (Hthrm & Hlockm). split.
        + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. rewrite Hthr in Hx. cbn in Hx.
          apply KBlo; lia.
        + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. rewrite Hlock in Hx. cbn in Hx.
          apply KBlo; lia.
      - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia].
      - rewrite (sl_mat_fds md md' Hmat). exact Hfd. }
    split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
    split; [unfold rg; rewrite Hreg, E8; exact Hr8|].
    split; [rewrite Hreg, E3; exact Hr3|].
    split; [rewrite Hreg, E4, Hr4; symmetry; exact (proj2 (yt_ent_regs g [] mem md HENT))|].
    split.
    { apply (fl_bytes [(Sfr fr, Sfr fr + 392)] mem mem' (g_S g - 104) (saved_bytes ra g) Hsaved MU).
      intros x Hx.
      unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
      apply KBout. apply HappW. unfold AF.SLOT_STACK. lia. }
    split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
    split.
    { intros a Ha. split.
      - destruct Hwin as (Hw0 & Hw1 & Hwv). exact (WM (wa a) (proj1 (Hwv a Ha))).
      - assert (Hcase : (fr <= a < fr + FRAME_BYTES) \/ ~ (fr <= a < fr + FRAME_BYTES)) by lia.
        destruct Hcase as [Hin|Hout].
        + split; [lia|]. split; [lia|].
          split; [pose proof (Happ a Hin) as Hap; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia|].
          intros i Hi. replace (a + i) with a by lia.
          split; [exact (Happ a Hin)|].
          destruct (sh_of_frame fr a Hfrm Hfr0 Hin) as (Hs1 & Hs2).
          destruct HB0 as (Hb0 & Hb1 & Hb2).
          destruct (nth_error (repeat (Z_to_bv 8 0) 392) (Z.to_nat (shadow_addr a - Sfr fr))) as [bb|] eqn:Enth.
          * pose proof (Hb2 (Z.to_nat (shadow_addr a - Sfr fr)) ltac:(rewrite repeat_length; lia)) as HmE.
            rewrite Z2Nat.id in HmE by lia.
            replace (Sfr fr + (shadow_addr a - Sfr fr)) with (shadow_addr a) in HmE by lia.
            rewrite Enth in HmE.
            pose proof (repeat_spec _ _ _ (nth_error_In _ _ Enth)) as Eb.
            exists bb. split; [exact HmE|]. rewrite Eb. left. vm_compute. reflexivity.
          * exfalso. apply nth_error_None in Enth. rewrite repeat_length in Enth. lia.
        + apply (addr1_munch [(Sfr fr, Sfr fr + 392)] mem mem' a MU).
          * apply HOUT. apply (sh_not_frame fr a Hfrm Hfr0); [|exact Hout].
            pose proof (HappW a Ha) as Hap. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap. lia.
          * exact (HWA a Ha Hout). }
    apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
    apply (ent_munch APIf g [] mem mem' md [(Sfr fr, Sfr fr + 392)] HENT HAH MU);
      [| exact HLO1 | exact HHI1 | intros a _ Hx; exact (proj2 (HOWN1 a) Hx)].
    intros x Hk. destruct Hk as [Hblk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
    + destruct Hblk as (q & k & i & Hin & Hni & Hi & ->).
      destruct (yt_law_blocks ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (_ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _). exact (KBout _ Happq).
    + apply KBout. pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
      unfold app_mem, LOWMEM_END. left. lia.
    + apply KBout. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
    + assert (Hb0 : 0 <= b)
        by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
      assert (Hnb : ~ (fr <= b < fr + FRAME_BYTES))
        by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
      exact (HOUT _ (sh_not_frame fr b Hfrm Hfr0 Hb0 Hnb)).
    + (* batch 2: the shadow byte of an entry block's byte; the block lies below stklo, so below the frame *)
      destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
      destruct (yt_law_blocks ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (Hend & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _).
      assert (Hq0 : 0 <= q + i) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
      assert (Hnb : ~ (fr <= q + i < fr + FRAME_BYTES)).
      { intro Hc. destruct (Hreal fr ltac:(lia)) as (Hlo & _). lia. }
      exact (HOUT _ (sh_not_frame fr (q + i) Hfrm Hfr0 Hq0 Hnb)).
Qed.

(* ---- Y1's call (0x82b9c `jal 3dbf4 <frame_release_6>`, side arm s5 = fr) and the `j 0x82bb0` at 0x82ba0
   after it. The contract asan_stack_free_6_contract (proved in tree: Tk/AW/Sf6.stack_free_6) needs mem_inv,
   which the frame does not carry, so the call runs on the normalized memory (MemNorm.evt_normalize) and its post
   is carried back across mem_rel / ro_same. The release sets the frame's flag byte to 0 and its 512 shadow bytes
   to 0xf5 (the bytes are marked unusable). *)
Lemma y1_evt :
  forall (ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
          s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (mem : word -> option byte) (fr FS j lo spv : Z),
  a0w = Z_to_bv 64 fr -> a1w = Z_to_bv 64 3136 -> bv_unsigned sp0 = spv ->
  fr = fs_frame FS 6 j -> 0 <= j < fs_M 6 ->
  fs_place mem FS ->
  bytes_at rsegs mem (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs mem (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells mem -> shadow_rw mem ->
  stk rsegs mem lo spv -> lo + 32 <= spv -> FS + FS_SIZE <= spv - 32 ->
  HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
  ro_agree rsegs mem ->
  LE.evt rsegs
    (fun ms => exists (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m' : word -> option byte),
       ms = MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                fp_regs (Z_to_bv 64 0x82bb0) fp_csr None m' (seg_rom rsegs) /\
       Frame.munch [(fs_flag FS 6 j, fs_flag FS 6 j + 1); (shadow_addr fr, shadow_addr fr + 512);
                    (spv - 32, spv)] mem m' /\
       Frame.wmono rsegs mem m' /\ ro_agree rsegs m' /\ stk rsegs m' lo spv /\
       bytes_at rsegs m' (fs_flag FS 6 j) [Z_to_bv 8 0] /\
       bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0xf5) 512) /\
       shadow_rw m')
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b9c) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 a0w a1w a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mem fr FS j lo spv -> -> Esp EFR Hj PL FLG FLW HAC HSW HST
    HLOK HROOM HHI HSPA HRO.
  subst spv fr.
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (HB6 : fs_B 6 = 4096) by reflexivity.
  assert (Hfrv : fs_frame FS 6 j = FS + 6328320 + j * 4096) by (unfold fs_frame, fs_B; cbn; lia).
  assert (HFSz : FS_SIZE = 11571200) by reflexivity.
  pose proof PL as (HFS0 & _ & _ & _ & _).
  assert (Hfrb : 0 <= fs_frame FS 6 j < 2 ^ 64) by (rewrite Hfrv; rewrite HM6 in Hj; unfold APPMEM_END in *; lia).
  assert (Hlo0 : 0x5fe000 <= lo) by (unfold HIGHMEM_BEG in HHI; lia).
  assert (Hsp64 : bv_unsigned sp0 <= 2 ^ 64) by (unfold APPMEM_END in HSPA; lia).
  step.
  pose proof (mem_rel_normalize rsegs mem HRO) as REL.
  pose proof Sf6.stack_free_6 as SF0.
  unfold SF.asan_stack_free_6_contract, SF.asan_stack_free_contract, SF.ASAN_STACK_FREE_6,
    SF.ASAN_STACK_FREE_K in SF0.
  cbv zeta in SF0.
  assert (HC : LE.evt rsegs
      (SF.asan_stack_free_post 6 32 (Z_to_bv 64 0x82ba0) sp0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         fp_regs fp_csr (bv_unsigned (Z_to_bv 64 3136)) FS j lo (normalize rsegs mem))
      (MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fs_frame FS 6 j)) (Z_to_bv 64 3136)
               a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          fp_regs (Z_to_bv 64 0x3dbf4) fp_csr None (normalize rsegs mem) (seg_rom rsegs))).
  { apply (SF0 (Z_to_bv 64 0x82ba0) sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fs_frame FS 6 j)) (Z_to_bv 64 3136)
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             fp_regs fp_csr (normalize rsegs mem) lo FS j).
    - exact Hj.
    - rewrite (MState.unsigned_lit (fs_frame FS 6 j)) by exact Hfrb. reflexivity.
    - rewrite (MState.unsigned_lit 3136) by lia. rewrite HB6. lia.
    - rewrite (MState.unsigned_lit 3136) by lia. reflexivity.
    - destruct PL as (P1 & P2 & P3 & P4 & P5).
      split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      apply (stk_rel_hi mem _ FS (FS + FS_SIZE) REL); [unfold ASAN_GT in P3; lia | lia | exact P5].
    - exact (ba_rel1 mem _ _ _ REL FLG).
    - rewrite (MState.unsigned_lit (fs_frame FS 6 j)) by exact Hfrb. exact (ba_rel1 mem _ _ _ REL FLW).
    - exact (asan_cells_rel mem _ REL HAC).
    - exact (shadow_rw_rel mem _ REL HSW).
    - exact (mem_inv_normalize rsegs mem).
    - exact (stk_rel_hi mem _ lo (bv_unsigned sp0) REL Hlo0 Hsp64 HST).
    - exact HLOK.
    - exact HROOM.
    - exact HHI.
    - exact HSPA. }
  rewrite (MState.unsigned_lit 3136) in HC by lia.
  pose proof (evt_normalize rsegs _ _ fp_regs _ fp_csr None mem (seg_rom rsegs)
                ytail_wx_apart HRO HC) as HE.
  eapply LE.evt_cut; [exact HE|].
  intros ms (st0 & Hp & Hrel & Hro2).
  unfold SF.asan_stack_free_post in Hp. cbv zeta in Hp.
  destruct Hp as (q0 & q1 & q2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q4 & q5 & q6 & m0' &
                  -> & MU & WM & MI & ST' & PL' & FLG' & SHB' & AC' & SW').
  replace (fs_shadow_n 6 3136) with 512 in MU by (vm_compute; reflexivity).
  replace (Z.to_nat (fs_shadow_n 6 3136)) with 512%nat in SHB' by (vm_compute; reflexivity).
  destruct Hrel as (HRg & HFg & HPg & HSg & HRv & HFc & HRo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS]
    in HRg, HFg, HPg, HSg, HRv, HFc, HRo, HMR.
  (* the state after the return, in MS form so that the `j` at 0x82ba0 can be stepped *)
  assert (Ems : ms = MS (mkR (Z_to_bv 64 0x82ba0) sp0 gp tp q0 q1 q2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q3 q4 q5 q6)
                     fp_regs (Z_to_bv 64 0x82ba0) fp_csr None (ms_mem ms) (seg_rom rsegs)).
  { destruct ms as [R' F' pcv' svc' rv' fc' m' ro']. cbn in HRg, HFg, HPg, HSg, HRv, HFc, HRo |- *. subst.
    replace (ret_pc (Z_to_bv 64 0x82ba0)) with (Z_to_bv 64 0x82ba0)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    reflexivity. }
  rewrite Ems. set (m' := ms_mem ms) in *. clear Ems HRg HFg HPg HSg HRv HFc HRo.
  step.
  apply LE.evt_done.
  exists q0, q1, q2, b0, b1, b2, b3, b4, b5, b6, b7, q3, q4, q5, q6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' REL HMR Hro2 MU)|].
  split; [exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' REL HMR Hro2 WM)|].
  split; [exact (ro_agree_same rsegs mem m' HRO Hro2)|].
  split; [exact (stk_rel_hi_back m' m0' lo (bv_unsigned sp0) HMR Hlo0 Hsp64 ST')|].
  split; [exact (proj2 (bytes_at_rel rsegs m' m0' _ _ HMR) FLG')|].
  split; [exact (proj2 (bytes_at_rel rsegs m' m0' _ _ HMR) SHB')|].
  exact (shadow_rw_rel_back m' m0' HMR SW').
Qed.

(* S_Y1 of Seg/Slot.v (0x82b9c on the side arm, s5 = fr): the release of the FakeStack frame. The frame lies in
   the FakeStack, below stklo and so below the whole slot window; FRAR's outside-the-frame window addressability
   is therefore the whole window, and it survives the release, which writes no shadow byte of the window. The heap
   invariant crosses the release by a_laws_fs_store: the flag byte and the frame's shadow are FakeStack bytes and
   their shadow, the callee window is real stack, and the FakeStack state stays a_fs_ok (the flag goes 1 -> 0). *)
Theorem seg_Y1 : Hcut B APIf ra (Inv_A82bb0 B APIf ra) -> Hcut B APIf ra (Inv_A82b9c B APIf ra).
Proof.
  intros HY3 g c HInv.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HInv as (regs & mem & md & fr & s5 & Ec & HFRA & HENT & (Es5 & Ha0 & Ha1)).
  destruct HFRA as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5or & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  subst c s5. rewrite SEGS.
  destruct (loc_app ([] ++ g_H g) fr mem md HAH
              ltac:(destruct Hloc as [(_ & _ & Hx)|(_ & _ & Hx & _)]; [left|right]; exact Hx))
    as (Hgt & Happ).
  assert (HgtN : 6283264 <= fr) by (unfold AC.GT in Hgt; exact Hgt).
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hside : FSREC fr mem)
    by (destruct Hloc as [(Hx & _)|(_ & _ & _ & Hx)]; [exfalso; lia | exact Hx]).
  clear Hloc.
  destruct Hside as (FS & jj & HwTP & HFSr & Hjj & EFR & HFLG & HFLW).
  destruct (yt_law_fs_place ([] ++ g_H g) mem md FS HAH HwTP HFSr) as (HFSgt & HFSend & HFS4k & HFSapp).
  pose proof (yt_law_fs_ok ([] ++ g_H g) mem md FS HAH HwTP HFSr) as HFSOK.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HFSz' : FS_SIZE = 11571200) by reflexivity.
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (EFRv : fr = FS + 6328320 + jj * 4096) by (rewrite EFR; unfold fs_frame, fs_B; cbn; lia).
  assert (EFLv : fs_flag FS 6 jj = FS + 36352 + jj) by (unfold fs_flag; cbn; lia).
  rewrite HM6 in Hjj.
  unfold AC.GT in HFSgt. unfold HIGHMEM_BEG in Hhigh.
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (Hw0 & Hw1 & _); split; [exact Hw0 | exact Hw1]).
  set (FL := fs_flag FS 6 jj) in *.
  assert (HappW : forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> app_mem x).
  { intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia. }
  assert (HappFS : forall x, FS <= x < FS + 11571200 -> app_mem x)
    by (intros x Hx; apply HFSapp; rewrite HFSz; exact Hx).
  assert (HappFr : forall a, fr <= a < fr + 8 * 512 -> app_mem a) by (intros a Ha; apply HappFS; lia).
  pose proof (sh_in_shadow_blk fr 512 ltac:(lia) HappFr) as HshIS.
  set (SHF := shadow_addr fr) in *.
  assert (Hfr8 : fr mod 8 = 0) by exact (fr_mod8 fr Hfrm).
  assert (HSHlo : 0x7fff8000 <= SHF).
  { unfold SHF, shadow_addr, ASAN_K. assert (0 <= fr / 8) by (apply Z.div_pos; lia). lia. }
  assert (HSHb : SHF + 512 <= 2 ^ 64).
  { pose proof (HshIS (SHF + 511) ltac:(lia)) as X. pose proof (in_shadow_range _ X). lia. }
  (* the stack facts the callee asks for, on the real stack below sp *)
  assert (HstkLo : stk rsegs mem (g_S g - AF.SLOT_STACK) sp).
  { destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)) as (Hx & _). exact Hx. }
  assert (HPL : fs_place mem FS).
  { pose proof (yt_fs_ok_cells mem FS HFSOK) as HW1.
    split; [lia|]. split; [exact HFS4k|]. split; [unfold ASAN_GT; lia|].
    split; [intros a Ha; apply HappFS; lia|].
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (HW1 a ltac:(rewrite HFSz; lia)) as (Hwr & bb & Hbb).
    split; [exact Hwr | exists bb; exact Hbb]. }
  apply (sl_run_lib regs (Z_to_bv 64 0x82b9c) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82bb0 /\
       Frame.munch [(FL, FL + 1); (SHF, SHF + 512); (sp - 32, sp)] mem mem' /\ Frame.wmono rsegs mem mem' /\
       ro_agree rsegs mem' /\ stk rsegs mem' (g_S g - AF.SLOT_STACK) sp /\
       bytes_at rsegs mem' FL [Z_to_bv 8 0] /\ bytes_at rsegs mem' SHF (repeat (Z_to_bv 8 0xf5) 512) /\
       shadow_rw mem' /\
       getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\ getr R0 8 = getr regs 8)
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of.
    eapply LE.evt_mono.
    { eapply y1_evt with (fr := fr) (FS := FS) (j := jj) (lo := g_S g - AF.SLOT_STACK) (spv := sp).
      - exact Ha0.
      - exact Ha1.
      - exact Haspz.
      - exact EFR.
      - rewrite HM6. exact Hjj.
      - exact HPL.
      - exact HFLG.
      - exact HFLW.
      - exact (AsanRTInv.RT_cells sp mem md HRT).
      - exact (AsanRTInv.RT_shadow_rw sp mem md HRT).
      - exact HstkLo.
      - lia.
      - lia.
      - unfold HIGHMEM_BEG. lia.
      - lia.
      - exact Hro. }
    { intros ms' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' &
                  E & MU & WM & HRO' & HST' & HFL' & HSH' & HSW').
      eexists _, _, m'. split; [exact E|].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact HRO'|].
      split; [exact HST'|]. split; [exact HFL'|]. split; [exact HSH'|]. split; [exact HSW'|].
      split; [reflexivity|]. split; [reflexivity | reflexivity]. }
  - intros R0 pc' mem' regs' md' (Hpc & MU & WM & HRO' & HST' & HFL' & HSH' & HSW' & E3 & E4 & E8) Hreg Hmat.
    subst pc'.
    set (W3 := [(FL, FL + 1); (SHF, SHF + 512); (sp - 32, sp)]) in *.
    assert (HO3 : forall x, ~ (FL <= x < FL + 1) -> ~ (SHF <= x < SHF + 512) -> ~ (sp - 32 <= x < sp) ->
                    Frame.outside W3 x)
      by (intros x H1 H2 H3; unfold W3; cbn; split; [exact H1|]; split; [exact H2|]; split; [exact H3 | exact I]).
    assert (HappSP : forall x, sp - 32 <= x < sp -> app_mem x).
    { intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia. }
    (* an app byte that is neither the flag nor in the callee window is outside the write set *)
    assert (HOapp : forall x, app_mem x -> x <> FL -> ~ (sp - 32 <= x < sp) -> Frame.outside W3 x).
    { intros x Hap Hne Hns. apply HO3; [lia| |exact Hns].
      intro Hin. exact (app_not_shadow x Hap (HshIS x Hin)). }
    (* a shadow byte outside the frame's 512 is outside the write set *)
    assert (HOsh : forall x, in_shadow x -> ~ (SHF <= x < SHF + 512) -> Frame.outside W3 x).
    { intros x Hin Hns. apply HO3; [| exact Hns |].
      - intro Hc. assert (x = FL) by lia. subst x.
        exact (app_not_shadow FL (HappFS FL ltac:(lia)) Hin).
      - intro Hc. exact (app_not_shadow x (HappSP x Hc) Hin). }
    assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a _ H; exact (WM (Z_to_bv 64 a) H)).
    assert (KBeq : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W3 x ->
              mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx Ho. unfold mbyte.
      assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho. }
      rewrite Hm. reflexivity. }
    assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
    { intros sg x H0 H1.
      assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { apply MU. rewrite MState.unsigned_lit by lia.
        apply HOapp; [unfold app_mem, LOWMEM_END; left; lia | lia | lia]. }
      unfold mbyte. rewrite Hm. reflexivity. }
    (* the FakeStack state after the release *)
    assert (HFSOK' : AC.a_fs_ok mem' FS).
    { destruct HFSOK as (HW1 & HW2 & HW3 & HW4 & HW5).
      assert (KBfs : forall x, FS <= x < FS + 36864 -> x <> FL -> mbyte rsegs mem' x = mbyte rsegs mem x).
      { intros x Hx Hne. apply KBeq; [lia|]. apply HOapp; [apply HappFS; lia | exact Hne | lia]. }
      split; [|split; [|split; [|split]]].
      - intros a Ha. destruct (HW1 a Ha) as (Hwr & bb & Hbb). split; [exact (WM (Z_to_bv 64 a) Hwr)|].
        assert (Hc : a = FL \/ a <> FL) by lia.
        destruct Hc as [->|Hne].
        + destruct HFL' as (_ & _ & Hf). exists (Z_to_bv 8 0).
          pose proof (Hf 0%nat ltac:(cbn; lia)) as X. cbn [Z.of_nat nth_error] in X.
          rewrite Z.add_0_r in X. exact X.
        + exists bb. rewrite (KBeq a ltac:(lia) (HOapp a (HappFS a ltac:(lia)) Hne ltac:(lia))). exact Hbb.
      - intros k Hk. rewrite KBfs; [exact (HW2 k Hk) | lia | lia].
      - rewrite KBfs; [exact HW3 | lia | lia].
      - intros c' Hc'. destruct (HW4 c' Hc') as (h & Hh). exists h. intros k Hk.
        unfold AC.a_fs_hint in *. rewrite KBfs; [exact (Hh k Hk) | lia | lia].
      - intros c' j' Hc' Hj'. pose proof (Tac_fs.a_fs_flag_range FS c' j' Hc' Hj') as Hrg.
        assert (Hc : AC.a_fs_flag FS c' j' = FL \/ AC.a_fs_flag FS c' j' <> FL) by lia.
        destruct Hc as [Heq|Hne].
        + left. rewrite Heq. destruct HFL' as (_ & _ & Hf).
          pose proof (Hf 0%nat ltac:(cbn; lia)) as X. cbn [Z.of_nat nth_error] in X.
          rewrite Z.add_0_r in X. exact X.
        + rewrite KBfs; [exact (HW5 c' j' Hc' Hj') | lia | exact Hne]. }
    (* the heap invariant *)
    assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              ~ (FS <= a < FS + AC.FS_SIZE) ->
              ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by exact Ha.
      apply HO3.
      - intro Hc. apply Hnfs. rewrite HFSz. lia.
      - intro Hc. apply Hnsh. destruct (sh_inv_blk fr 512 a Hc) as (Heq & Hran).
        exists (fr + 8 * (a - shadow_addr fr)). split; [rewrite HFSz; lia | symmetry; exact Heq].
      - intro Hc. apply Hns. right. left. lia. }
    destruct (yt_law_fs_store ([] ++ g_H g) mem mem' md FS HAH HwTP HFSr Hagree Hwm HFSOK')
      as (HAH1 & HOWN1 & HLO1 & HHI1).
    destruct (yt_law_mat_le ([] ++ g_H g) mem' md md' Hmat) as (HAHm & HLOm).
    rewrite <- SEGS. apply HY3.
    exists regs', mem', md'.
    split; [reflexivity|].
    split.
    { exact (AsanRTInv.RT_meta_write sp (g_S g - 416) mem mem' md md' W3 HRT MU WM
               (rt_disjoint_hi3 FL (FL + 1) SHF (SHF + 512) (sp - 32) sp ltac:(lia) ltac:(lia) ltac:(lia))
               (fun a Ha => proj2 (HSW' a Ha))). }
    split; [exact (HAHm HAH1)|].
    split; [rewrite HLOm, HLO1; exact Hstklo|].
    split; [exact HRO'|].
    split.
    { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split].
      - destruct Hcse as (Hthrm & Hlockm). split.
        + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. rewrite Hthr in Hx. cbn in Hx.
          apply KBlo; lia.
        + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. rewrite Hlock in Hx. cbn in Hx.
          apply KBlo; lia.
      - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia].
      - rewrite (sl_mat_fds md md' Hmat). exact Hfd. }
    split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
    split; [unfold rg; rewrite Hreg, E8; exact Hr8|].
    split; [rewrite Hreg, E3; exact Hr3|].
    split; [rewrite Hreg, E4, Hr4; symmetry; exact (proj2 (yt_ent_regs g [] mem md HENT))|].
    split.
    { apply (fl_bytes W3 mem mem' (g_S g - 104) (saved_bytes ra g) Hsaved MU).
      intros x Hx.
      unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
      apply HOapp; [apply HappW; lia | lia | lia]. }
    split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
    split.
    { intros a Ha. split.
      - destruct Hwin as (Hw0 & Hw1 & Hwv). exact (WM (wa a) (proj1 (Hwv a Ha))).
      - assert (Hout : ~ (fr <= a < fr + FRAME_BYTES)) by lia.
        apply (addr1_munch W3 mem mem' a MU); [|exact (HWA a Ha Hout)].
        pose proof (HappW a Ha) as Hap.
        apply HOsh; [exact (shadow_of_app a Hap)|].
        apply (sh_not_blk fr 512 a Hfr8 Hfr0); [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia | lia]. }
    apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
    apply (ent_munch APIf g [] mem mem' md W3 HENT HAH MU);
      [| exact HLO1 | exact HHI1 | intros a _ Hx; exact (proj2 (HOWN1 a) Hx)].
    intros x Hk. destruct Hk as [Hblk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
    + destruct Hblk as (q & k & i & Hin & Hni & Hi & ->).
      destruct (yt_law_blocks ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (Hend & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
      apply HOapp; [exact Happq | | lia].
      intro Heq. apply Hnfs. rewrite Heq. exact (Tac_fs.a_fs_in AC.ASYMS mem FS FL HwTP HFSr ltac:(rewrite HFSz; lia)).
    + pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
      apply HOapp; [unfold app_mem, LOWMEM_END; left; lia | lia | lia].
    + apply HOapp; [unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia | lia | lia].
    + assert (Hb0 : 0 <= b)
        by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
      assert (Hnb : ~ (fr <= b < fr + 8 * 512))
        by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
      assert (Happb : app_mem b).
      { destruct Hor as [Hi|Hr];
          [pose proof (img_below_GT b Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
          |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
      apply HOsh; [exact (shadow_of_app b Happb) | exact (sh_not_blk fr 512 b Hfr8 Hfr0 Hb0 Hnb)].
    + (* batch 2: the shadow byte of an entry block's byte; the block is outside the FakeStack, so outside the
         released frame, and its shadow outside the frame's 512 *)
      destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
      destruct (yt_law_blocks ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (_ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
      assert (Hq0 : 0 <= q + i) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
      assert (Hnb : ~ (fr <= q + i < fr + 8 * 512)).
      { intro Hc. apply Hnfs. exact (Tac_fs.a_fs_in AC.ASYMS mem FS (q + i) HwTP HFSr ltac:(rewrite HFSz; lia)). }
      apply HOsh; [exact (shadow_of_app (q + i) Happq) | exact (sh_not_blk fr 512 (q + i) Hfr8 Hfr0 Hq0 Hnb)].
Qed.

(* ---- The release join 0x82b80: `lui a0,0x45e03; addiw a0,a0,1550` (a0 = 0x45e0360e), `sd a0,0(s6)` (the frame
   header word goes 0x41b58ab3 -> 0x45e0360e), `beqz s5,0x82ba4`. Real arm (s5 = 0): `li a1,392; mv a0,s3` to Y2
   at 0x82bac. Side arm (s5 = fr): `lui a0,0x1; addiw a1,a0,-960; mv a0,s5` (a1 = 0xc40 = 3136) to Y1 at
   0x82b9c. (v1.8: join 0x82ac0, a1 = 380 / -1056 = 3040, Y2 0x82aec, Y1 0x82adc.) *)

(* Resolve a branch condition c to b from H : c = b. *)
Ltac ytail_br b H :=
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; exact H); cbv iota
  end.

Lemma jrel_evt_real :
  forall (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5w s6w s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr SHv lo hi : Z),
  s3w = Z_to_bv 64 SHv -> s5w = Z_to_bv 64 0 -> s6w = Z_to_bv 64 fr ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  LE.evt rsegs
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SHv) (Z_to_bv 64 392) a2 a3 a4 a5 a6 a7
                    s2 s3w s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82bac) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3w s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b80) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3w s4 s5w s6w s7 s8 s9 s10 s11
    t3 t4 t5 t6 mem fr SHv lo hi -> -> -> HRW HST.
  pose proof (munch_refl [(fr, fr + 8)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  step. step. step.
  assert (HB : bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0) = true) by apply bv_eqb_refl.
  step.
  ytail_br true HB.
  step. step.
  apply LE.evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [|exact HST].
  destruct HRW as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma jrel_evt_side :
  forall (ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5w s6w s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word) (mem : word -> option byte) (fr lo hi : Z),
  s5w = Z_to_bv 64 fr -> s6w = Z_to_bv 64 fr -> 0 < fr < 2 ^ 64 ->
  rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)] ->
  stk rsegs mem lo hi ->
  LE.evt rsegs
    (fun ms => exists m' : word -> option byte,
       ms = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 3136) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
                fp_regs (Z_to_bv 64 0x82b9c) fp_csr None m' (seg_rom rsegs) /\
       munch [(fr, fr + 8)] mem m' /\ wmono rsegs mem m' /\
       bytes_at rsegs m' fr (le8 (Z_to_bv 64 0x45e0360e)) /\ stk rsegs m' lo hi)
    (MS (mkR ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5w s6w s7 s8 s9 s10 s11 t3 t4 t5 t6)
        fp_regs (Z_to_bv 64 0x82b80) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5w s6w s7 s8 s9 s10 s11
    t3 t4 t5 t6 mem fr lo hi -> -> Hfr HRW HST.
  pose proof (munch_refl [(fr, fr + 8)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  step. step. step.
  assert (HB : bv_eqb (Z_to_bv 64 fr) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !MState.unsigned_lit in E by lia. lia. }
  step.
  ytail_br false HB.
  step. step. step.
  apply LE.evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [|exact HST].
  destruct HRW as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

(* FRAS -> FRAR (and ENT) across the header store at 0x82b88: only the frame header word [fr, fr + 8) changes.
   Every other FRAH conjunct is about bytes outside it (the spills and the saved registers above the frame, the
   image below GT <= fr, the shadow, which is never app memory), about the ghost, or about registers the join
   does not write. The heap invariant crosses the store by a_laws_store on the real arm (the header is real
   stack, in [stklo, APPMEM_END)) and by Tac_fs.a_fs_frame_write_AH on the side arm (the header is inside the
   class-6 FakeStack frame). *)
Lemma frah_hdr : forall g fr regs regs' mem mem' md md' s5,
  FRAS B APIf ra g fr [] regs mem md s5 ->
  munch [(fr, fr + 8)] mem mem' -> wmono rsegs mem mem' ->
  bytes_at rsegs mem' fr (le8 (Z_to_bv 64 0x45e0360e)) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  AsanLift.mat_le md md' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRAR B APIf ra g fr [] regs' mem' md' s5 /\ (ENT APIf g [] mem md -> ENT APIf g [] mem' md').
Proof.
  intros g fr regs regs' mem mem' md md' s5 HFRA MU WM Hhdr' Hwin' Hmat E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & HRimg & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HFRA as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5or & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  destruct (loc_app ([] ++ g_H g) fr mem md HAH
              ltac:(destruct Hloc as [(_ & _ & Hx)|(_ & _ & Hx & _)]; [left|right]; exact Hx))
    as (Hgt & Happ).
  assert (HgtN : 6283264 <= fr) by (unfold AC.GT in Hgt; exact Hgt).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (Hw0 & Hw1 & _); split; [exact Hw0 | exact Hw1]).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH).
  assert (HO : forall x, ~ (fr <= x < fr + 8) -> outside [(fr, fr + 8)] x)
    by (intros x Hx; cbn; split; [exact Hx | exact I]).
  assert (HOsh : forall x, in_shadow x -> outside [(fr, fr + 8)] x).
  { intros x Hx. apply HO. intro Hin. exact (app_not_shadow x (Happ x ltac:(lia)) Hx). }
  assert (KB : forall (sg : list Segment) x, 0 <= x < 2 ^ 64 -> ~ (fr <= x < fr + 8) ->
            mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hx Hn. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by exact Hx. exact (HO x Hn). }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x)
    by (intros sg x H0 H1; apply KB; lia).
  (* the heap invariant across the store *)
  assert (HLAW : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                 (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md q <->
                            AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md q) /\
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                   AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [(_ & _ & Hreal)|(_ & _ & _ & (FS & jj & HwTP & HFSr & Hjj & EFR & _ & _))].
    - apply (yt_law_store ([] ++ g_H g) mem mem' md HAH).
      + intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by exact Ha.
        apply HO. intro Hin. apply Hns. right. left. exact (Hreal a ltac:(lia)).
      + intros a _ H. exact (WM (Z_to_bv 64 a) H).
    - destruct (yt_law_fs_place ([] ++ g_H g) mem md FS HAH HwTP HFSr) as (HFSgt & HFSend & _ & _).
      assert (HM6 : fs_M 6 = 256) by reflexivity.
      assert (EFRv : fr = FS + 6328320 + jj * 4096) by (rewrite EFR; unfold fs_frame, fs_B; cbn; lia).
      rewrite HM6 in Hjj.
      assert (HFSz : AC.FS_SIZE = 11571200) by reflexivity.
      apply (Tac_fs.a_fs_frame_write_AH _ _ _ _ _ [(fr, fr + 8)] ([] ++ g_H g) mem mem' md FS 6 jj
               LAWS HAH HwTP HFSr).
      + rewrite HFSz in *. lia.
      + lia.
      + lia.
      + unfold AC.a_fs_frame, AC.a_fs_B. rewrite HFSz. cbn. lia.
      + exact MU.
      + intros x Hx. cbn in Hx |- *. destruct Hx as (Hx & _). split; [|exact I].
        intro Hin. apply Hx. unfold AC.a_fs_frame, AC.a_fs_B. cbn. lia.
      + intros a _ H. exact (WM (Z_to_bv 64 a) H).
      + intros q Hq (bb & Hbb).
        assert (Hc : (fr <= q < fr + 8) \/ ~ (fr <= q < fr + 8)) by lia.
        destruct Hc as [Hin|Hout].
        * destruct Hhdr' as (_ & _ & Hb).
          destruct (nth_error (le8 (Z_to_bv 64 0x45e0360e)) (Z.to_nat (q - fr))) as [b'|] eqn:Enth.
          -- exists b'. pose proof (Hb (Z.to_nat (q - fr)) ltac:(rewrite length_le8; lia)) as X.
             rewrite Z2Nat.id in X by lia. replace (fr + (q - fr)) with q in X by lia.
             rewrite Enth in X. exact X.
          -- exfalso. apply nth_error_None in Enth. rewrite length_le8 in Enth. lia.
        * exists bb. rewrite (KB rsegs q Hq Hout). exact Hbb. }
  destruct HLAW as (HAH1 & HOWN1 & HLO1 & HHI1).
  destruct (yt_law_mat_le ([] ++ g_H g) mem' md md' Hmat) as (HAHm & HLOm).
  split.
  - exists A, sp.
    split.
    { apply (AsanRTInv.RT_meta_write sp sp mem mem' md md' [(fr, fr + 8)] HRT MU WM
               (rt_disjoint_hi1 fr (fr + 8) ltac:(lia))).
      intros a Hin.
      assert (Hx64 : 0 <= a < 2 ^ 64) by (pose proof (in_shadow_range a Hin); lia).
      destruct (AsanRTInv.RT_shadow_rw sp mem md HRT a Hin) as (_ & b & Hmr).
      assert (Hmem : mem' (wa a) = mem (wa a))
        by (apply MU; rewrite Mem.wa_unsigned by exact Hx64; exact (HOsh a Hin)).
      exists b. unfold mrd in *. rewrite Hmem. exact Hmr. }
    split; [exact (HAHm HAH1)|].
    split.
    { apply (ro_agree_same rsegs mem mem' Hro). intros a Hra. apply MU. apply HO. intro Hin.
      rewrite (ro_high_w a ltac:(lia)) in Hra. discriminate Hra. }
    split.
    { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split].
      - destruct Hcse as (Hthrm & Hlockm). split.
        + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. rewrite Hthr in Hx. cbn in Hx.
          apply KBlo; lia.
        + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. rewrite Hlock in Hx. cbn in Hx.
          apply KBlo; lia.
      - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia].
      - rewrite (sl_mat_fds md md' Hmat). exact Hfd. }
    split; [rewrite (AsanLift.mat_le_halted md md' Hmat); exact Hhalt|].
    split.
    { intros a Hin. rewrite KBlo.
      - exact (Hgimg a Hin).
      - pose proof (img_below_GT a (HRimg a Hin)) as X. unfold AC.GT in X. lia.
      - pose proof (img_below_GT a (HRimg a Hin)) as X. unfold AC.GT in X. lia. }
    split; [rewrite E2; exact Hr2|].
    split; [exact Hspm|].
    split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
    split; [rewrite HLOm, HLO1; exact Hstklo|].
    split; [rewrite E4; exact Hr4|].
    split; [unfold rg in *; rewrite E8; exact Hr8|].
    split; [unfold rg in *; rewrite E9; exact Hr9|].
    split; [rewrite E3; exact Hr3|].
    split; [unfold rg in *; rewrite E19; exact Hr19|].
    split; [unfold rg in *; rewrite E26; exact Hr26|].
    split; [exact Hfrm|].
    split; [exact Hs5or|].
    split; [exact HAm|].
    split; [exact HAS|].
    split; [exact Hspa|].
    split; [exact Hfa|].
    split; [exact HA416|].
    split; [exact HS4|].
    split; [exact HAPP|].
    split.
    { unfold q64 in *. apply (fl_bytes [(fr, fr + 8)] mem mem' (A + 304) _ Hspill MU).
      rewrite length_le8. intros x Hx. apply HO. lia. }
    split.
    { destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & Hfsb & Hfs & Hrec)].
      - left. split; [exact H0|]. split; [exact Hspfr|].
        intros a Ha. rewrite HLOm, HLO1. exact (Hreal a Ha).
      - right. split; [exact Hfr0|]. split.
        + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
          intros k Hk. rewrite <- KBlo.
          * exact (Hw k Hk).
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        + split.
          * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
            exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
            intros k Hk. rewrite KBlo.
            -- exact (Hw k Hk).
            -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
            -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          * destruct Hrec as (FS & jj & HwTP & HFSr & Hjj & EFR & HFLG & HFLW).
            assert (HM6 : fs_M 6 = 256) by reflexivity.
            assert (EFRv : fr = FS + 6328320 + jj * 4096) by (rewrite EFR; unfold fs_frame, fs_B; cbn; lia).
            assert (EFLv : fs_flag FS 6 jj = FS + 36352 + jj) by (unfold fs_flag; cbn; lia).
            assert (HB6 : fs_B 6 = 4096) by reflexivity.
            rewrite HM6 in Hjj.
            exists FS, jj. split.
            { intros k Hk. rewrite KBlo.
              - exact (HwTP k Hk).
              - unfold AC.as_tp, AC.ASYMS. cbn. lia.
              - unfold AC.as_tp, AC.ASYMS. cbn. lia. }
            split; [exact HFSr|]. split; [rewrite HM6; exact Hjj|]. split; [exact EFR|]. split.
            { apply (fl_bytes [(fr, fr + 8)] mem mem' _ _ HFLG MU). cbn [length]. intros x Hx.
              apply HO. lia. }
            { apply (fl_bytes [(fr, fr + 8)] mem mem' _ _ HFLW MU). rewrite length_le8. intros x Hx.
              apply HO. rewrite HB6 in Hx. lia. } }
    split; [exact Hhdr'|].
    split.
    { unfold q64 in *. apply (fl_bytes [(fr, fr + 8)] mem mem' (fr + 16) _ Hhdr2 MU).
      rewrite length_le8. intros x Hx. apply HO. lia. }
    split.
    { destruct Hsh as (sh & Hshb & Hshl). exists sh. split; [|exact Hshl].
      apply (fl_bytes [(fr, fr + 8)] mem mem' (Sfr fr) sh Hshb MU). intros x Hx.
      rewrite Hshl, Z2Nat.id in Hx by (rewrite FRAME_SHADOW_val; lia).
      apply HOsh. apply (sh_in_shadow fr Happ). lia. }
    split; [exact Hwin'|].
    split.
    { apply (fl_bytes [(fr, fr + 8)] mem mem' (g_S g - 104) (saved_bytes ra g) Hsaved MU).
      intros x Hx. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
      apply HO. lia. }
    split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
    split.
    { intros a Hin. apply (addr1_munch [(fr, fr + 8)] mem mem' a MU); [|exact (HAG a Hin)].
      apply HOsh. exact (shadow_of_app a (addr1_app mem a (HAG a Hin))). }
    split.
    { intros a H1 H2. apply (addr1_munch [(fr, fr + 8)] mem mem' a MU); [|exact (HWA a H1 H2)].
      apply HOsh. exact (shadow_of_app a (addr1_app mem a (HWA a H1 H2))). }
    split; [exact HSHI1|].
    split; [exact HSHI2|].
    split; [exact HSHI3|].
    split; [exact Hhb | exact Hlive].
  - intros HENT.
    apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
    apply (ent_munch APIf g [] mem mem' md [(fr, fr + 8)] HENT HAH MU);
      [| exact HLO1 | exact HHI1 | intros a _ Hx; exact (proj2 (HOWN1 a) Hx)].
    intros x Hk. destruct Hk as [Hblk | [Hik | [Habk | [(b & Hor & ->) | Hblks]]]].
    + destruct Hblk as (q & k & i & Hin & Hni & Hi & ->).
      destruct (yt_law_blocks ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (Hend & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnfs).
      apply HO. intro Hfr.
      destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
      * destruct (Hreal fr ltac:(lia)). lia.
      * exact (Hnfs (Hfs (q + i) ltac:(lia))).
    + apply HO. pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg. lia.
    + apply HO. lia.
    + assert (Happb : app_mem b).
      { destruct Hor as [Hi|Hr];
          [pose proof (img_below_GT b Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
          |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
      exact (HOsh _ (shadow_of_app b Happb)).
    + (* batch 2: the shadow byte of an entry block's byte, never app memory, so not the header word *)
      destruct Hblks as (q & k & i & Hin & Hni & Hi & ->).
      destruct (yt_law_blocks ([] ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (_ & Hall).
      destruct (Hall (q + i) ltac:(lia)) as (Happq & _).
      exact (HOsh _ (shadow_of_app (q + i) Happq)).
Qed.

(* S_Jrel of Seg/Slot.v (v1.9 cut names). *)
Theorem seg_Jrel : Hcut B APIf ra (Inv_A82b9c B APIf ra) -> Hcut B APIf ra (Inv_A82bac B APIf ra) ->
  Hcut B APIf ra (Inv_Jrel B APIf ra).
Proof.
  intros HY1 HY2 g c HInv.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof FF as (SEGS & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HInv as (regs & mem & md & fr & s5 & Ec & HFRA & HENT & (Hr21 & Hr22)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5or & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  subst c. rewrite SEGS.
  destruct (loc_app ([] ++ g_H g) fr mem md HAH
              ltac:(destruct Hloc as [(_ & _ & Hx)|(_ & _ & Hx & _)]; [left|right]; exact Hx))
    as (Hgt & Happ).
  assert (HgtN : 6283264 <= fr) by (unfold AC.GT in Hgt; exact Hgt).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HfrE : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as X.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* the header word is writable on both arms: real stack inside the window, or FakeStack bytes *)
  assert (Hwr : forall a, fr <= a < fr + 8 -> writable_at rsegs mem a).
  { intros a Ha. destruct Hloc as [(_ & Hspfr & _)|(_ & _ & Hfs & _)].
    - destruct Hwin as (_ & _ & Hwv). exact (proj1 (Hwv a ltac:(lia))).
    - destruct (Hfs a ltac:(lia)) as (FSa & HFSar & Hwa & Hloa & Hhia).
      pose proof (yt_fs_ok_cells mem FSa (yt_law_fs_ok ([] ++ g_H g) mem md FSa HAH Hwa HFSar)) as HW1.
      exact (proj1 (HW1 a ltac:(lia))). }
  assert (HRW : rw_cells rsegs mem fr [C8 (Z_to_bv 64 0x41b58ab3)]).
  { split.
    - split; [cbn; split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hhdr1.
    - replace (Z.of_nat (cells_size [C8 (Z_to_bv 64 0x41b58ab3)])) with 8 by (vm_compute; reflexivity).
      split; [lia|]. split; [unfold APPMEM_END in HfrE; lia|]. intros i Hi. exact (Hwr (fr + i) ltac:(lia)). }
  destruct Hs5or as [Es5|Es5]; subst s5.
  - (* real arm: Y2 *)
    apply (sl_run_lib regs (Z_to_bv 64 0x82b80) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x82bac /\
         munch [(fr, fr + 8)] mem mem' /\ wmono rsegs mem mem' /\
         bytes_at rsegs mem' fr (le8 (Z_to_bv 64 0x45e0360e)) /\
         stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) /\
         getr R0 10 = Z_to_bv 64 (Sfr fr) /\ getr R0 11 = Z_to_bv 64 392 /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
         getr R0 26 = getr regs 26)
      (Post B APIf ra g)).
    + exact Hhalt.
    + unfold Regs6ss.mkR_of.
      eapply LE.evt_mono.
      { eapply jrel_evt_real with (fr := fr) (SHv := Sfr fr).
        - exact Hr19.
        - exact Hr21.
        - exact Hr22.
        - exact HRW.
        - exact Hwin. }
      { intros ms' (m' & E & MU & WM & HB & HST).
        eexists _, _, m'. split; [exact E|].
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact HB|].
        split; [exact HST|].
        repeat (split; [reflexivity|]). reflexivity. }
    + intros R0 pc' mem' regs' md' (Hpc & MU & WM & HB & HST & E10 & E11 & E2 & E3 & E4 & E8 & E9 & E19 & E26)
        Hreg Hmat.
      subst pc'.
      destruct (frah_hdr g fr regs regs' mem mem' md md' 0 HFRA MU WM HB HST Hmat
                  (eq_trans (Hreg _) E2) (eq_trans (Hreg _) E3) (eq_trans (Hreg _) E4) (eq_trans (Hreg _) E8)
                  (eq_trans (Hreg _) E9) (eq_trans (Hreg _) E19) (eq_trans (Hreg _) E26)) as (HFRAR & HENTf).
      rewrite <- SEGS. apply HY2.
      exists regs', mem', md', fr, 0.
      split; [reflexivity|].
      split; [exact HFRAR|].
      split; [exact (HENTf HENT)|].
      split; [reflexivity|].
      split; [unfold a0v, rg; rewrite Hreg; exact E10 | unfold rg; rewrite Hreg; exact E11].
  - (* side arm: Y1 *)
    apply (sl_run_lib regs (Z_to_bv 64 0x82b80) mem md
      (fun R0 pc' mem' =>
         pc' = Z_to_bv 64 0x82b9c /\
         munch [(fr, fr + 8)] mem mem' /\ wmono rsegs mem mem' /\
         bytes_at rsegs mem' fr (le8 (Z_to_bv 64 0x45e0360e)) /\
         stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) /\
         getr R0 10 = Z_to_bv 64 fr /\ getr R0 11 = Z_to_bv 64 3136 /\
         getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
         getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
         getr R0 26 = getr regs 26)
      (Post B APIf ra g)).
    + exact Hhalt.
    + unfold Regs6ss.mkR_of.
      eapply LE.evt_mono.
      { eapply jrel_evt_side with (fr := fr).
        - exact Hr21.
        - exact Hr22.
        - unfold APPMEM_END in HfrE. lia.
        - exact HRW.
        - exact Hwin. }
      { intros ms' (m' & E & MU & WM & HB & HST).
        eexists _, _, m'. split; [exact E|].
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact HB|].
        split; [exact HST|].
        repeat (split; [reflexivity|]). reflexivity. }
    + intros R0 pc' mem' regs' md' (Hpc & MU & WM & HB & HST & E10 & E11 & E2 & E3 & E4 & E8 & E9 & E19 & E26)
        Hreg Hmat.
      subst pc'.
      destruct (frah_hdr g fr regs regs' mem mem' md md' fr HFRA MU WM HB HST Hmat
                  (eq_trans (Hreg _) E2) (eq_trans (Hreg _) E3) (eq_trans (Hreg _) E4) (eq_trans (Hreg _) E8)
                  (eq_trans (Hreg _) E9) (eq_trans (Hreg _) E19) (eq_trans (Hreg _) E26)) as (HFRAR & HENTf).
      rewrite <- SEGS. apply HY1.
      exists regs', mem', md', fr, fr.
      split; [reflexivity|].
      split; [exact HFRAR|].
      split; [exact (HENTf HENT)|].
      split; [reflexivity|].
      split; [unfold a0v, rg; rewrite Hreg; exact E10 | unfold rg; rewrite Hreg; exact E11].
Qed.

End YTail.
