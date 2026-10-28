(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit R_small R_thread R_m2s R_setshadow R_poison I_ikit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require F_fwritex.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import FX_Layout FX_Stdio_iface F_stdio_exit F_fflushA Imp_xifaceA X_ixdefs.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation bsegs := ImageA.bsegs.
Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0).

Definition I_FFLUSH_BODY : Z := 0x77ba4.
Definition ACQ_ENTRY : Z := 0x7a87c.
Definition REL_ENTRY : Z := 0x7b09c.
Definition KWL : Z := 2 ^ 60.

Lemma seg_rom_above : forall a : word, SEGTOP_A <= bv_unsigned a -> seg_rom bsegs a = None.
Proof.
  intros a Ha. unfold seg_rom, memory_read.
  rewrite (find_segment1_none_above bsegs SEGTOP_A (bv_unsigned a) asegs_below Ha). reflexivity.
Qed.

Lemma zword_raw : forall (m : mem) b cs, SEGTOP_A <= b -> rw_cells bsegs m b (C8 z64 :: cs) ->
  forall i, 0 <= i < 8 -> m (wa (b + i)) = Some (Z_to_bv 8 0).
Proof.
  intros m b cs Hb ((WF & B0 & B1 & RD) & _) i Hi.
  specialize (RD (Z.to_nat i)). cbn [cells_bytes cbytes] in RD.
  assert (E8 : le8 z64 = repeat (Z_to_bv 8 0) 8) by (vm_compute; reflexivity). rewrite E8 in RD.
  assert (HL : (Z.to_nat i < length (repeat (Z_to_bv 8 0) 8 ++ cells_bytes cs))%nat) by (rewrite length_app, repeat_length; lia).
  specialize (RD HL). rewrite Z2Nat.id in RD by lia.
  rewrite nth_error_app1 in RD by (rewrite repeat_length; lia). rewrite nth_error_repeat in RD by lia.
  unfold mrd in RD.
  assert (SR : seg_rom bsegs (wa (b + i)) = None).
  { apply seg_rom_above. unfold wa. cbn [cells_bytes cbytes] in B1. rewrite E8, length_app, repeat_length in B1. rewrite unsigned_lit; [lia|]. split; [lia|].
    assert (8 <= Z.of_nat (8 + length (cells_bytes cs)))%Z by lia. lia. }
  destruct (m (wa (b + i))) as [v|] eqn:E; [exact RD|]. rewrite SR in RD. discriminate RD.
Qed.

Lemma munch_restore8 : forall W (m m' : mem) b, munch ((b, b + 8) :: W) m m' ->
  (forall i, 0 <= i < 8 -> m' (wa (b + i)) = m (wa (b + i))) -> munch W m m'.
Proof.
  intros W m m' b MU EQ x Hout.
  destruct (Z_le_gt_dec b (bv_unsigned x)) as [H1|H1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (b + 8)) as [H2|H2]|].
  - pose proof (EQ (bv_unsigned x - b) ltac:(lia)) as E. replace (b + (bv_unsigned x - b)) with (bv_unsigned x) in E by lia.
    unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E.
  - apply MU. cbn [outside]. split; [lia | exact Hout].
  - apply MU. cbn [outside]. split; [lia | exact Hout].
Qed.

Lemma release_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (H lo : Z) (j0 : list byte) (hm hb : word) (hcs : list cell),
  rw_cells bsegs m (H + -8) (CB 8 j0 :: C8 hm :: C8 hb :: C8 z64 :: hcs) -> (8 <= H) -> (H + 48 < 2^63) -> (bv_unsigned sp <= H + -8) ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x6e0000 <= lo ->
  mem_inv bsegs m ->
  evt bsegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0x1891c8 [(bv_unsigned sp - 16, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x1891c8) (Z_to_bv 64 H) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REL_ENTRY) fc None m (seg_rom bsegs)).
Proof.
  intros until hcs. intros HC H0 HH HSP ST LO LOLO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold REL_ENTRY.
  carve_frame 16%nat ST.
  lstep. lstep.
  lstep.
  step. if_true.
  lstep. lstep.
  release_frame FR ST (bv_unsigned sp).
  lstep.
  unfold frame_post. sys_finish.
Qed.

Definition hoff (fp : Z) : Z := if fp =? RSTDOUT then MT_OFF_OUT else MT_OFF_ERR.

Definition handle_frame (j0 : list byte) (hm : word) (b fp : Z) (hrest : list cell) : list cell :=
  CB 8 j0 :: C8 hm :: C8 (Z_to_bv 64 b) :: C8 z64 :: C8 (Z_to_bv 64 fp) :: C8 (Z_to_bv 64 0xffffffff) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: hrest.

Definition acq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (H T fp lo : Z) (j0 : list byte) (hm : word) (hrest : list cell) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (H + 8, H + 43)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (H + -8) (handle_frame j0 hm (T + hoff fp) fp hrest)
    /\ rw_cells bsegs m' (T + hoff fp) Z15
    /\ rw_cells bsegs m' 0x1891c8 [C8 (Z_to_bv 64 T)].

Local Ltac amo8 AMO := MallocKit_AB.amo_step AMO.

Ltac eval_Tsum T :=
  repeat match goal with |- context [Z_to_bv 64 (T + ?e)] =>
    lazymatch e with
    | Zpos _ => fail
    | _ => let v := eval vm_compute in e in progress (change (T + e) with (T + v))
    end end.

Ltac acq_finish T :=
  apply evt_done; unfold acq_post, handle_frame, Z15;
  try (replace (hoff 1592528) with 149400 by reflexivity); try (replace (hoff 1592048) with 1791840 by reflexivity);
  do 16 eexists; split; [reflexivity|];
  lazymatch goal with |- munch _ ?m0 ?mf /\ _ =>
  lazymatch goal with RAW0 : forall i, 0 <= i < 8 -> m0 (wa (T + ?off + i)) = Some _, BKf : rw_cells _ mf (T + ?off) _, MU : munch _ m0 mf |- _ =>
    split; [ apply (munch_restore8 _ m0 mf (T + off) MU); intros i Hi;
             rewrite (RAW0 i Hi); rewrite (zword_raw mf (T + off) _ ltac:(lia) BKf i Hi); reflexivity
           | repeat (split; [assumption|]); assumption ]
  end end.

Lemma acquire_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (H T fp lo : Z) (j0 : list byte) (hm j8 j16 j32 : word) (j40 : byte) (hrest : list cell),
  (fp = RSTDOUT \/ fp = RSTDERR) ->
  rw_cells bsegs m 0x1891c8 [C8 (Z_to_bv 64 T)] ->
  rw_cells bsegs m (T + hoff fp) Z15 ->
  rw_cells bsegs m (H + -8) (CB 8 j0 :: C8 hm :: C8 j8 :: C8 j16 :: C8 (Z_to_bv 64 fp) :: C8 j32 :: C1 j40 :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: hrest) ->
  (SEGTOP_A <= T) -> (T mod 4096 = 0) -> (T + MT_SIZE <= lo) ->
  (8 <= H) -> (H + 72 <= 2^63) -> (bv_unsigned sp <= H + -8) ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> 0x6e0000 <= lo -> (bv_unsigned sp < 2^63) ->
  mem_inv bsegs m ->
  evt bsegs (acq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H T fp lo j0 hm hrest m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x1891c8) (Z_to_bv 64 H) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACQ_ENTRY) fc None m (seg_rom bsegs)).
Proof.
  intros until hrest. intros HFP TW BK HCE TLO TAL TUP H0 HH HSP ST LO LOLO SPH MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold ACQ_ENTRY, MT_SIZE in *.
  assert (HOFF : 0 <= hoff fp /\ hoff fp + 120 <= 0x38e000 /\ hoff fp mod 8 = 0).
  { unfold hoff, MT_OFF_OUT, MT_OFF_ERR. destruct (fp =? RSTDOUT); cbn; lia. }
  destruct HOFF as (HO1 & HO2 & HO3).
  assert (T8 : T mod 8 = 0).
  { rewrite <- (Z.mod_mod_divide T 4096 8) by (first [lia | exists 512; reflexivity]). rewrite TAL. reflexivity. }
  assert (T0 : 0x6e0000 <= T) by (unfold SEGTOP_A in TLO; exact TLO).
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + hoff fp)) = true).
  { unfold amo_aligned, amo_bytes. rewrite unsigned_lit by (clear - T0 TUP LO RSP HO1 HO2; lia). apply Z.eqb_eq.
    rewrite Z.add_mod, T8, HO3 by lia. reflexivity. }

  destruct HFP as [-> | ->];
    [ replace (hoff RSTDOUT) with MT_OFF_OUT in * by reflexivity | replace (hoff RSTDERR) with MT_OFF_ERR in * by reflexivity ];
    unfold MT_OFF_OUT, MT_OFF_ERR in *; change (120 * 1245) with 149400 in *; change (120 * 14932) with 1791840 in *.
  all: pose proof (wmono_refl bsegs m) as WM.
  1: pose proof (munch_refl [(T + 149400, T + 149400 + 8); (bv_unsigned sp - 176, bv_unsigned sp); (H + 8, H + 43)] m) as MU.
  2: pose proof (munch_refl [(T + 1791840, T + 1791840 + 8); (bv_unsigned sp - 176, bv_unsigned sp); (H + 8, H + 43)] m) as MU.
  all: unfold Z15 in BK.
  1: pose proof (zword_raw m (T + 149400) _ ltac:(lia) BK) as RAW0.
  2: pose proof (zword_raw m (T + 1791840) _ ltac:(lia) BK) as RAW0.
  all: carve_frame 176%nat ST.
  all: do 14 lstep.
  all: do 8 lstep.
  all: lstep.
  all: lstep.
  all: lstep.
  all: do 2 lstep.
  all: lstep.
  all: do 6 lstep.
  all: lstep.
  all: do 20 lstep.

  all: eval_Tsum T.
  all: lstep.
  all: lstep.
  all: lstep.
  all: lstep.
  all: do 13 lstep.
  all: step; if_false.
  all: lstep. all: step; if_false.
  all: lstep.
  all: lstep.
  all: step; if_false.
  all: lstep. all: lstep. all: step; if_false.
  all: lstep. all: lstep. all: step; if_false.
  all: lstep.
  all: step; if_true.

  all: lstep.
  all: lstep.
  all: do 8 lstep.
  all: lstep.
  all: lstep. all: step; if_false.
  all: lstep. all: lstep.
  all: amo8 AMO.
  all: step; if_false.
  all: amo8 AMO; try fix_lit_store.
  all: step; if_false.

  all: lstep. all: lstep. all: step; if_false.
  all: lstep. all: lstep. all: step; if_true.
  all: lstep. all: lstep. all: step; if_true.
  all: lstep. all: step; if_true.
  all: lstep. all: step; if_false.
  all: lstep. all: step; if_true.

  all: lstep. all: lstep.
  all: lstep. all: lstep. all: step; if_false.
  all: lstep. all: step; if_true.
  all: do 6 lstep. all: step; if_true.
  all: amo8 AMO.
  all: step; if_false.
  all: amo8 AMO; try fix_lit_store.
  all: step; if_false.
  all: step; if_true.
  all: step; if_true.
  all: do 14 lstep.
  all: release_frame FR ST (bv_unsigned sp).
  all: lstep.
  all: acq_finish T.
Qed.

Ltac ix_consts_unfold :=
  unfold g_asan_inited, g_GOT_lsan_off, LSAN_CTR, g_GOT_flags, g_REAL_cxa_atexit, e_musl_cxa_atexit, g_REAL_fflush, e_musl_fflush, g_REAL_wcrtomb, e_musl_wcrtomb,
    g_GOT_mbstate_t_sz, g_mbstate_t_sz, g_flags_cio, g_icpt_mdmap, g_mdmem, MT_SIZE, MT_OFF_OUT, MT_OFF_ERR, g_flags_dco, g_GOT_verbosity, g_verbosity,
    ps_cells, m2s_cells, setshadow_cells, R_poison.g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset.
Ltac ix_consts_unfold_in H :=
  unfold g_asan_inited, g_GOT_lsan_off, LSAN_CTR, g_GOT_flags, g_REAL_cxa_atexit, e_musl_cxa_atexit, g_REAL_fflush, e_musl_fflush, g_REAL_wcrtomb, e_musl_wcrtomb,
    g_GOT_mbstate_t_sz, g_mbstate_t_sz, g_flags_cio, g_icpt_mdmap, g_mdmem, MT_SIZE, MT_OFF_OUT, MT_OFF_ERR, g_flags_dco, g_GOT_verbosity, g_verbosity,
    ps_cells, m2s_cells, setshadow_cells, R_poison.g_got_common_flags, g_can_poison, g_cf_clear_shadow_mmap_threshold, g_got_real_memset, g_real_memset in H.
Ltac ix_open IXm :=
  let T := fresh "T" in
  unfold ixit_rt, mtab_at in IXm; ix_consts_unfold_in IXm;
  destruct IXm as (AI & GL16 & CTR & GF & RCXA & RFF & RWC & GMB & MBS & CIO & (T & PTRc & TABc & TLO & TUP & TAL & BOUT & BERR)
                   & DCO & GVB & VRB & PS1 & (PS2a & PS2b & PS2c) & (PS3a & PS3b) & PS4 & PS5);
  unfold mtab_at, g_icpt_mdmap, g_mdmem, MT_SIZE, MT_OFF_OUT, MT_OFF_ERR in *;
  change (120 * 1245) with 149400 in *; change (120 * 14932) with 1791840 in *.

Ltac bucket_fin T :=
  let bk := first [ assumption | match goal with H : rw_cells _ _ (T + _) _ |- _ => exact H end ] in
  first [ split; bk | bk ].

Ltac conj_assum := first [ assumption | lazymatch goal with |- _ /\ _ => split; conj_assum end ].
Ltac ix_close T :=
  unfold ixit_rt, mtab_at; ix_consts_unfold; change (120 * 1245) with 149400; change (120 * 14932) with 1791840;
  repeat (split; [assumption|]);
  split; [ exists T; repeat (split; [first [assumption | unfold STACK_WIN in *; lia]|]); bucket_fin T
         | conj_assum ].

Definition keep (P : Prop) : Prop := P.
Ltac box H := lazymatch type of H with ?P => change P with (keep P) in H end.

Ltac stk_over_sp1 sp :=
  lazymatch goal with Hs : bv_unsigned ?sp1 = bv_unsigned sp + -80, STx : stk _ _ _ (bv_unsigned sp + -80) |- _ =>
    replace (bv_unsigned sp + -80) with (bv_unsigned sp1) in STx by lia end.

Ltac bk_now BK T off TUP XL TLO :=
  lazymatch type of BK with keep (rw_cells _ ?m0 _ _) =>
  lazymatch goal with MU : munch _ m0 ?mm, WM : wmono _ m0 ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let name := fresh "BKc" in
    assert (name : rw_cells bsegs mm (T + off) Z15)
      by (generalize BK; unfold keep; intros BK'; eapply (rw_cells_agree bsegs m0 mm _ _ BK'); [| exact WM];
          apply (agree_of_munch _ _ _ _ MU); let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn [cells_size csize Nat.add Z15 Z.of_nat Pos.of_succ_nat Pos.succ] in Hq; cbn [outside]; clear - Hq TUP XL TLO; unfold SEGTOP_A, STACK_WIN in *; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hq; lia)
  end end.

Definition AA8 : list byte := le8 (Z_to_bv 64 12297829382473034410).
Notation z8 := (Z_to_bv 8 0).
Lemma rw_cells_recast : forall (m : mem) A cs cs',
  rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells bsegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma recast48 : forall (m : mem) A j0 (w1 w2 w3 w4 w5 c7 c8 c9 : word),
  rw_cells bsegs m A [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 12297829382473034410); C8 c7; C8 c8; C8 c9] ->
  rw_cells bsegs m A [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C1 (nth 0 AA8 z8); C1 (nth 1 AA8 z8); C1 (nth 2 AA8 z8); CB 5 (skipn 3 AA8); C8 c7; C8 c8; C8 c9].
Proof.
  intros m A j0 w1 w2 w3 w4 w5 c7 c8 c9 H. eapply rw_cells_recast; [exact H | | |].
  - destruct H as [[WF _] _]. cbn [cells_wf cell_wf] in WF |- *. destruct WF as [L _]. repeat split; first [exact L | exact I | reflexivity].
  - cbn [cells_bytes cbytes]. do 6 f_equal; try (vm_compute; reflexivity).
  - reflexivity.
Qed.

Ltac plia := first [lia | unfold MT_SIZE, STACK_WIN, SEGTOP_A in *; lia | match goal with |- ?g => idtac "PREMFAIL" g; fail end].

Section IFflush.
Variable sp0 : Z.
#[local] Notation IX := (ixit_rt sp0).
#[local] Notation XLO := (sp0 - STACK_WIN).

Ltac icpt_tail sp lo T fp off BK TUP XL TLO :=
  step; [if_false|..];
  lstep;
  lstep; lstep;
  lstep; lstep;
  do 6 lstep;
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -80) _ |- _ => apply recast48 in FR end;
  lstep; lstep;
  lstep;
  lstep;
  bk_now BK T off TUP XL TLO;
  name_sp sp (-80)%Z; stk_over_sp1 sp;
  call (acquire_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -72) T fp lo _ _ _ _ _ _ _);
    [ first [left; reflexivity | right; reflexivity]
    | eassumption
    | match goal with H : rw_cells _ _ (T + _) Z15 |- _ => exact H end
    | replace (bv_unsigned sp + -72 + -8) with (bv_unsigned sp + -80) by plia; eassumption
    | assumption | assumption | plia | plia | cbn [cells_size csize Nat.add]; lia | plia
    | eassumption | plia | plia | plia | assumption | ];
  unname_sp;

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?ma _) =>
    match goal with H : rw_cells _ ma (T + _) _ |- _ => replace (hoff fp) with off in H by reflexivity; box H; rename H into BKA end;
    pose proof (munch_refl [(lo, bv_unsigned sp)] ma) as MU2; pose proof (wmono_refl bsegs ma) as WM2 end;
  lazymatch goal with FRH : rw_cells _ _ (bv_unsigned sp + -72 + -8) _ |- _ =>
    replace (bv_unsigned sp + -72 + -8) with (bv_unsigned sp + -80) in FRH by plia; unfold handle_frame in FRH end;
  lstep;
  step; [if_true|..];
  lstep; lstep;
  lstep;
  name_sp sp (-80)%Z; stk_over_sp1 sp;
  call (release_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -72) lo _ _ _ _);
    [ replace (bv_unsigned sp + -72 + -8) with (bv_unsigned sp + -80) by plia; eassumption
    | plia | plia | plia | eassumption | plia | plia | assumption | ];
  unname_sp;
  lstep;
  lstep; lstep; lstep;
  lstep;
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -80) _, STx : stk _ _ _ (bv_unsigned sp + -80) |- _ => release_frame FR STx (bv_unsigned sp) end;
  lstep.

Theorem ifflush_idle_ok : ifflush_idle_stmt IX XLO.
Proof.
  unfold ifflush_idle_stmt. intros until lo. intros FC -> HFP Fp0 FLO WPOS ST LO GLO XL SPH IXm MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_IFFLUSH, ICPT_DEPTH, GLOBALS_TOP, STACK_WIN in *.
  ix_open IXm.
  box BOUT. box BERR.
  pose proof (wmono_refl bsegs m) as WM.
  unfold file_cells in FC.
  destruct HFP as [-> | ->].
  1: pose proof (munch_refl [(lo, bv_unsigned sp); (1592528, 1592528 + 232)] m) as MU.
  2: pose proof (munch_refl [(lo, bv_unsigned sp); (1592048, 1592048 + 232)] m) as MU.
  all: carve_frame 80%nat ST.
  all: lstep.
  all: do 5 lstep.

  all: lstep.
  all: name_sp sp (-80)%Z; stk_over_sp1 sp.
  all: call (try_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo); [ eassumption | eassumption | lia | lia | assumption | ].
  all: unname_sp.
  all: step; [if_false|..].
  all: lstep. all: lstep.
  all: lstep. all: lstep.

  all: name_sp sp (-80)%Z; stk_over_sp1 sp.
  1: call (fflush_idle_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1592528 flags mode wend wpos wfn bufp bufsize fd lbf tail lo);
       [ eassumption | reflexivity | lia | lia | lia | eassumption | lia | unfold GLOBALS_TOP; lia | assumption | ].
  2: call (fflush_idle_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1592048 flags mode wend wpos wfn bufp bufsize fd lbf tail lo);
       [ eassumption | reflexivity | lia | lia | lia | eassumption | lia | unfold GLOBALS_TOP; lia | assumption | ].
  all: unname_sp.
  all: lazymatch goal with H : rw_cells _ _ _ (file_cells _ _ _ _ _ _ _ _ _ _ _) |- _ => unfold file_cells in H end.
  1: icpt_tail sp lo T constr:(1592528) constr:(149400) BOUT TUP XL TLO.
  2: icpt_tail sp lo T constr:(1592048) constr:(1791840) BERR TUP XL TLO.

  1: bk_now BERR T constr:(1791840) TUP XL TLO. 1: bk_now BKA T constr:(149400) TUP XL TLO.
  2: bk_now BOUT T constr:(149400) TUP XL TLO. 2: bk_now BKA T constr:(1791840) TUP XL TLO.
  all: apply evt_done; unfold ifflush_idle_post.
  all: do 15 eexists; split; [reflexivity|].
  all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [unfold file_cells; assumption|].

  all: ix_close T.
Qed.

Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall s so, get_so (set_so so s) = so.
Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.

Theorem ifflush_stdout_ok : ifflush_stdout_stmt IX XLO get_so set_so.
Proof.
  unfold ifflush_stdout_stmt. intros until canary. cbv zeta. intros INACT FC FL72 BUF BUFP BUFL -> ST LO GLO XL SPH SSP IXm MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_IFFLUSH, ICPT_DEPTH, GLOBALS_TOP, STACK_WIN in *.
  ix_open IXm.
  box BOUT. box BERR.
  pose proof (wmono_refl bsegs m) as WM.
  unfold stdout_cells, file_cells in FC. destruct SSP as [SG SC]. unfold got_ssp, ssp_guard in SG, SC.
  pose proof (munch_refl [(lo, bv_unsigned sp); (1592528, 1592528 + 232)] m) as MU.
  eapply (implM_evt bsegs). 2:{ intros ms' H; exact H. } cbv beta.
  carve_frame 80%nat ST.
  lstep.
  do 5 lstep.
  lstep.
  name_sp sp (-80)%Z; stk_over_sp1 sp.
  call (try_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo); [ eassumption | eassumption | lia | lia | assumption | ].
  unname_sp.
  step; [if_false|..].
  lstep. lstep. lstep. lstep.
  apply evt_done.

  name_sp sp (-80)%Z; stk_over_sp1 sp.
  lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mX _) =>
    eapply implM_post_evt';
    [ eapply (fflush_stdout_proof get_so set_so get_set set_set set_get _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mX st flags mode tail bufbytes lo canary);
      [ exact INACT | unfold stdout_cells, file_cells; eassumption | exact FL72 | eassumption | exact BUFP | exact BUFL | reflexivity
      | eassumption | unfold FFLUSH_DEPTH; lia | unfold GLOBALS_TOP; lia | split; assumption | assumption ]
    | cbv beta; intros [] s' ms' PO; unfold fflush_stdout_post, FFLUSH_DEPTH in PO; revert ms' PO; post_call bsegs mX ]
  end.
  unname_sp.
  lazymatch goal with H : rw_cells _ _ _ (stdout_idle_cells _ _ _ _) |- _ => unfold stdout_idle_cells, file_cells in H end.
  match goal with H : ssp_cells _ _ |- _ => destruct H as [SG2 SC2]; unfold got_ssp, ssp_guard in SG2, SC2 end.
  icpt_tail sp lo T constr:(1592528) constr:(149400) BOUT TUP XL TLO.
  bk_now BERR T constr:(1791840) TUP XL TLO. bk_now BKA T constr:(149400) TUP XL TLO.
  apply evt_done; unfold ifflush_stdout_post.
  do 16 eexists. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [eassumption|]. split; [eassumption|].
  split; [unfold file_cells; eassumption|].
  split; [split; assumption|].
  ix_close T.
Qed.
End IFflush.
