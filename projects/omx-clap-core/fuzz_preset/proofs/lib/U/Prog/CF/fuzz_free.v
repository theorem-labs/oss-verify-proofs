(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, addresses and numbers changed; 976 of its 1075 lines of code are new or changed and 647 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_reject_clean_starved.v, with its module names and numbers changed; 714 of its 791 lines of code are new or changed and 998 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/check_as_written.v, with its module paths and module names changed; 295 of its 339 lines of code are new or changed and 747 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YO0f YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require KindBGlue.
Import ListNotations.
Local Open Scope Z_scope.

Module FreeRun.
Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge Img0.
Local Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma wfin : forall m o bs, 0 <= o -> o + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs (write_to_mem m (wa o) bs) o bs /\
  munch [(o, o + Z.of_nat (length bs))] m (write_to_mem m (wa o) bs) /\
  wmono rsegs m (write_to_mem m (wa o) bs).
Proof.
  intros m o bs H1 H2. split; [apply bytes_at_write_same; lia|]. split.
  - apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia].
  - apply wmono_write, wmono_refl.
Qed.

(* fuzz_free of the #102 ubsan twin (27566683, symtab: fuzz_free 0x15ea8 size 140, instruction-equal to the old twin's
   0x15a94 by symbol; g_live 0x35260; libc free 0x18250), from the entry (p <> 0, with the ubsan pointer-overflow
   checks of p - 16) to the tail call of free. *)
Lemma ff_run1 : forall (p sz live : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  16 < p < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= live < 2 ^ 64 -> a0 = Z_to_bv 64 p ->
  (forall k, (k < 8)%nat ->
     ov_read_bytes rsegs m (wa (p - 16 + Z.of_nat k)) 1 = Some [Z_to_bv 8 (YO0f.le_byte sz 8 k)]) ->
  ov_read_bytes rsegs m (wa 0x35260) 8 = Some (le8 (Z_to_bv 64 live)) ->
  store_ok rsegs m (wa 0x35260) 8 = true ->
  evt rsegs
    (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x18250) fc None m' (seg_rom rsegs) /\
       a0' = Z_to_bv 64 (p - 16) /\
       bytes_at rsegs m' 0x35260 (le8 (Z_to_bv 64 (live - sz))) /\
       munch [(0x35260, 0x35260 + 8)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15ea8) fc None m (seg_rom rsegs)).
Proof.
  intros p sz live ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Hp Hsz Hl Ha0 RB RL HS.
  subst a0.
  pose proof (RB 0%nat ltac:(lia)) as R0. pose proof (RB 1%nat ltac:(lia)) as R1.
  pose proof (RB 2%nat ltac:(lia)) as R2. pose proof (RB 3%nat ltac:(lia)) as R3.
  pose proof (RB 4%nat ltac:(lia)) as R4. pose proof (RB 5%nat ltac:(lia)) as R5.
  pose proof (RB 6%nat ltac:(lia)) as R6. pose proof (RB 7%nat ltac:(lia)) as R7. clear RB.
  step.
  assert (C0 : bv_eqb (Z_to_bv 64 p) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite C0; cbv iota.
  do 2 step. if_cases HT1; zify_cond HT1; try (exfalso; lia).
  do 2 step. if_cases HT2; zify_cond HT2; try (exfalso; lia).
  do 28 step.
  match goal with |- context [write_to_mem _ _ (le8 (Z_to_bv 64 ?v))] =>
    replace v with (live - sz) by (KindBGlue.kb_lbu8 sz) end.
  apply evt_done. do 8 eexists. split; [reflexivity|]. split; [f_equal; lia|].
  apply wfin; cbn [length]; rewrite ?length_le8; lia.
Qed.

End FreeRun.

From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YK14 YK1a YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require FrameAPI.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger LedgerFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import fuzz_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require LedgerCells.
Local Open Scope Z_scope.

Lemma ff_D0 : decode_any (0x8050263%bv : bv 32) = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. YK1a.vm_refl_bv. Qed.

Lemma ff_D1 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. YK1a.vm_refl_bv. Qed.

Lemma ff_init_of_block : forall A b, WF A -> In b (user_blocks A) -> st_init_done A = true.
Proof.
  intros A b HW Hin. destruct (st_init_done A) eqn:E; [reflexivity|]. exfalso.
  destruct HW as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinit) & _).
  destruct (Hinit E) as (Hm & _). unfold user_blocks, used_metas in Hin. rewrite Hm in Hin. cbn in Hin. exact Hin.
Qed.

Lemma ff_fst_unique : forall {X Y : Type} (l : list (X * Y)) x a c,
  List.NoDup (map fst l) -> In (x, a) l -> In (x, c) l -> a = c.
Proof.
  intros X Y l. induction l as [|[y d] l IH]; intros x a c ND Ha Hc; [destruct Ha|].
  cbn [map fst] in ND. inversion ND as [|? ? Hn ND']; subst.
  destruct Ha as [Ea|Ha]; destruct Hc as [Ec|Hc].
  - inversion Ea; inversion Ec; subst; reflexivity.
  - inversion Ea; subst. exfalso. apply Hn. apply (in_map fst) in Hc. exact Hc.
  - inversion Ec; subst. exfalso. apply Hn. apply (in_map fst) in Ha. exact Ha.
  - exact (IH x a c ND' Ha Hc).
Qed.

(* The alloc.c cells this walk needs (g_live, g_peak, g_count, g_fail_at) as a globals list: the generated
   LedgerCells.GL_runs (the #102 cells merged into runs), cited by name. A cell lies inside one entry of a list when
   ff_covers says so (vm_compute over the list as generated). *)
Definition ff_covers (G : list (Z * Z)) (lo hi : Z) : bool :=
  existsb (fun e => (fst e <=? lo) && (hi <=? fst e + snd e)) G.

Lemma ff_covers_in : forall G lo hi x, ff_covers G lo hi = true -> lo <= x < hi -> in_globals G x.
Proof.
  intros G lo hi x H Hx. unfold ff_covers in H. apply existsb_exists in H. destruct H as ([l k] & Hin & Hc).
  apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2. cbn [fst snd] in *.
  exists l, k. split; [exact Hin | lia].
Qed.

Lemma ff_glob : forall x, G_LIVE <= x < G_LIVE + 24 \/ G_FAIL <= x < G_FAIL + 8 ->
  in_globals LedgerCells.GL_runs x.
Proof.
  intros x [Hx|Hx].
  - destruct (Z_lt_le_dec x (G_LIVE + 8)); [|destruct (Z_lt_le_dec x (G_LIVE + 16))].
    + apply (ff_covers_in _ G_LIVE (G_LIVE + 8)); [vm_compute; reflexivity | lia].
    + apply (ff_covers_in _ (G_LIVE + 8) (G_LIVE + 16)); [vm_compute; reflexivity | lia].
    + apply (ff_covers_in _ (G_LIVE + 16) (G_LIVE + 24)); [vm_compute; reflexivity | lia].
  - apply (ff_covers_in _ G_FAIL (G_FAIL + 8)); [vm_compute; reflexivity | lia].
Qed.

Definition ff_wseg (segs : list Segment) (a : Z) : bool :=
  match find_segment segs a 1 with Some s => seg_writable s | None => false end.

Lemma ff_range_check : forall segs lo (len : nat) a,
  forallb (fun j => ff_wseg segs (lo + Z.of_nat j)) (List.seq 0 len) = true -> lo <= a < lo + Z.of_nat len ->
  exists seg, find_segment segs a 1 = Some seg /\ seg_writable seg = true.
Proof.
  intros segs lo len a H Ha. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - lo)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (lo + (a - lo)) with a in H by lia.
  unfold ff_wseg in H. destruct (find_segment segs a 1) as [s|]; [|discriminate].
  exists s. split; [reflexivity | exact H].
Qed.

Section Free.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.

Lemma ff_img_low : ms_segs B = Img0.rsegs -> img_low B.
Proof.
  intros Hsegs. apply img_low_of_check with (C := 140735332483072);
    [unfold img_check; rewrite Hsegs; vm_compute; reflexivity | pose proof alloc_ceiling_val; lia].
Qed.

Lemma ff_globals_free :
  ms_segs B = Img0.rsegs ->
  (forall a, in_globals FrameAPI.frame_G a -> in_img B a /\ ~ static_owned B a /\
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
  YL01.AllocExtra B (aa_MR API) ->
  (forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_G a -> ~ owned B L A a) ->
  globals_free B API LedgerCells.GL_runs.
Proof.
  intros Hsegs HGi AX HGo a Ha.
  (* every entry of GL_runs lies inside one entry of frame_G (checked over the two lists as they stand) *)
  assert (Hf : in_globals FrameAPI.frame_G a).
  { destruct Ha as (lo & len & Hin & Hr).
    assert (C : forallb (fun e => ff_covers FrameAPI.frame_G (fst e) (fst e + snd e)) LedgerCells.GL_runs = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in C. specialize (C _ Hin). cbn [fst snd] in C. exact (ff_covers_in _ _ _ a C ltac:(lia)). }
  destruct (HGi a Hf) as (Himg & _ & _ & Herr).
  destruct (ff_img_low Hsegs) as [HIa _].
  split; [exact Himg|]. split; [exact (HIa a Himg)|].
  split.
  { destruct Ha as (lo & len & Hin & Hr). rewrite Hsegs.
    assert (C : forallb (fun e => forallb (fun j => ff_wseg Img0.rsegs (fst e + Z.of_nat j)) (List.seq 0 (Z.to_nat (snd e))))
                  LedgerCells.GL_runs = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in C. specialize (C _ Hin). cbn [fst snd] in C.
    apply (ff_range_check _ lo (Z.to_nat len)); [exact C | lia]. }
  split; [exact Herr|].
  intros L A mem md HM. split; [exact (HGo L A mem md a HM Hf)|].
  intros p n Hin Hr. unfold blocks in Hin. apply in_map_iff in Hin as ([q n'] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as Ep En. subst n'.
  apply (YL01.ax_blocks_img AX L A mem md q n (a - p) HM Hq ltac:(lia)).
  replace (ptr_addr L q + (a - p)) with a by lia. exact Himg.
Qed.

Theorem fuzz_free_holds :
  ms_segs B = Img0.rsegs -> ms_free B = 0x18250 ->
  (forall a, in_globals FrameAPI.frame_G a -> in_img B a /\ ~ static_owned B a /\
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
  YL01.AllocExtra B (aa_MR API) ->
  (forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_G a -> ~ owned B L A a) ->
  free_contract_r B API F -> fuzz_free_contract B API F.
Proof.
  intros Hsegs Hfree HGi AX HGo HF L A regs mem md p k b Lam peak cnt fail Hpre Ha0 Hled Hinv Hpk Hres.
  pose proof (ff_img_low Hsegs) as HI.
  assert (HG : globals_free B API LedgerCells.GL_runs) by exact (ff_globals_free Hsegs HGi AX HGo).
  pose proof Hpre as (HM & HWF & HB & Hra & Hal & Hlo & Hhi & HW & Htp & Herr & Haux).
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  pose proof alloc_ceiling_lt as Hc.
  assert (Has : ALLOC_STACK = 8192) by reflexivity.
  assert (Hstk : forall a, (spZ regs - ALLOC_STACK <= a < spZ regs) \/ (errno_addr B <= a < errno_addr B + 4) ->
            writable_at (ms_segs B) mem a) by (intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]).
  destruct (Z.eq_dec p 0) as [Hp0|Hp0].
  - subst p. unfold FUZZ_FREE.
    eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
    { eapply step_branch_tk_gen with (w := (0x8050263%bv : bv 32));
        [rewrite Hsegs; YK1a.vm_refl_bv | reflexivity | exact ff_D0 |].
      rewrite Ha0. vm_compute. reflexivity. }
    eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
    { eapply YK14.step_jalr_x0 with (w := (0x00008067%bv : bv 32));
        [rewrite Hsegs; YK1a.vm_refl_bv | reflexivity | exact ff_D1 | reflexivity]. }
    match goal with |- context [YK14.v_jalr ?t ?i] =>
      replace (YK14.v_jalr t i) with (getr regs 1) by (symmetry; change i with 0; exact Hra) end.
    apply SR_ret.
    exists L, A, regs, mem, md.
    split; [reflexivity|]. split; [exact Hinv|]. split; [intros i _; reflexivity|]. split; [tauto|].
    split; [intros _ i _; reflexivity|].
    split.
    { apply kb_post; [apply kb_mid_refl; [exact HM | exact HWF | exact HB | exact Hstk] |].
      intros r _. reflexivity. }
    split; [lia|].
    split; [intros a n i _ _ _; reflexivity|].
    split; [intros q n Hq _; exact Hq|].
    left. do 7 (split; [reflexivity|]). split; [exact Hled | exact Hres].
  - destruct Hpk as [[Hp _]|Hin]; [contradiction|].
    pose proof (ledger_block_range B API L A mem md Lam peak cnt fail p k HM Hled Hin) as (Hp1 & Hp2 & Hp3).
    pose proof Hled as ((HWl & HWp & HWc & HWf) & HP & HC & HFl & HN & HBl).
    rewrite Forall_forall in HBl. pose proof (HBl (p, k) Hin) as Hlb. cbn [fst snd] in Hlb.
    pose proof Hlb as (Hk0 & Hblk & Hwk & _).
    apply lblock_user in Hlb. destruct Hlb as (q & Hq & Eq).
    destruct (in_split _ _ Hin) as (l1 & l2 & HLam).
    pose proof (lsum_nonneg _ (ledger_sizes B _ _ _ _ _ _ _ Hled)) as HsL.
    assert (Hsum : lsum Lam - k = lsum (l1 ++ l2)) by (rewrite HLam, !lsum_app; cbn [lsum]; lia).
    assert (Hs12 : 0 <= lsum (l1 ++ l2)).
    { apply lsum_nonneg. pose proof (ledger_sizes B _ _ _ _ _ _ _ Hled) as Hs. rewrite HLam in Hs.
      rewrite Forall_forall in Hs |- *. intros x Hx. apply Hs. apply in_app_or in Hx. apply in_or_app.
      destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]. }
    destruct (HG (G_LIVE + 7) (ff_glob (G_LIVE + 7) ltac:(left; unfold G_LIVE; lia))) as (_ & HGr & _).
    assert (RB : forall j, (j < 8)%nat ->
              ov_read_bytes Img0.rsegs mem (Mem.wa (p - 16 + Z.of_nat j)) 1 = Some [Z_to_bv 8 (le_byte k 8 j)]).
    { intros j Hj. rewrite <- Hsegs. apply word_mem_byte1; [exact Hwk | lia | lia | exact Hj]. }
    assert (RL : ov_read_bytes Img0.rsegs mem (Mem.wa 0x35260) 8 = Some (Mem.le8 (Z_to_bv 64 (lsum Lam)))).
    { rewrite <- Hsegs.
      assert (Hbl : Mem.bytes_at (ms_segs B) mem G_LIVE (Mem.le8 (Z_to_bv 64 (lsum Lam))))
        by (apply word_mem_le8; [exact HWl | lia | unfold G_LIVE; lia | unfold G_LIVE; lia]).
      replace (Mem.wa 0x35260) with (Mem.wa (G_LIVE + 0)) by reflexivity.
      rewrite (Mem.bytes_at_read (ms_segs B) mem G_LIVE _ 0 8 Hbl) by (rewrite ?Mem.length_le8; lia).
      reflexivity. }
    assert (HWr : Mem.wr_at (ms_segs B) mem G_LIVE 8).
    { apply (globals_wr_at B API LedgerCells.GL_runs mem G_LIVE (lsum Lam) HG); [|exact HWl].
      intros j Hj. apply ff_glob. left. lia. }
    assert (HS : store_ok Img0.rsegs mem (Mem.wa 0x35260) 8 = true).
    { rewrite <- Hsegs. exact (Mem.wr_at_store_ok (ms_segs B) mem G_LIVE 8 0 8 HWr ltac:(lia) ltac:(lia)). }
    eapply kb_run with (K := fun R pc' mem' =>
        pc' = Z_to_bv 64 0x18250 /\ getr R 10 = Z_to_bv 64 (p - 16) /\ regs_preserved regs R /\
        getr R 1 = getr regs 1 /\ getr R 2 = getr regs 2 /\ getr R 4 = getr regs 4 /\
        Mem.bytes_at (ms_segs B) mem' G_LIVE (Mem.le8 (Z_to_bv 64 (lsum Lam - k))) /\
        Frame.munch [(G_LIVE, G_LIVE + 8)] mem mem' /\ Frame.wmono (ms_segs B) mem mem');
      [exact Hh | exact Hlz | |].
    + rewrite Hsegs. unfold FUZZ_FREE.
      eapply Exec.evt_mono;
        [unfold rmk; apply (FreeRun.ff_run1 p k (lsum Lam)); [lia | lia | lia | exact Ha0 | exact RB | exact RL | exact HS] |].
      intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & m' & -> & Ha0' & HBL & Hmu & Hwm).
      do 3 eexists. split; [reflexivity|]. cbv beta.
      split; [reflexivity|]. split; [rewrite <- Ha0'; reflexivity|]. split; [kb_saved|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact HBL|]. split; [exact Hmu | exact Hwm].
    + intros R pc' mem1 regs1 (-> & HR10 & HRp & HR1 & HR2 & HR4 & HBL & Hmu & Hwm) Hreg.
      assert (Hsp1 : spZ regs1 = spZ regs) by (unfold spZ; rewrite Hreg, HR2; reflexivity).
      assert (HAv : forall x, 0 <= x < alloc_ceiling ->
                (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
                Frame.outside [(G_LIVE, G_LIVE + 8)] x).
      { apply (globals_avoid B API _ _ L A mem md HG HM). intros lo hi x [E|[]] Hx.
        injection E as <- <-. apply ff_glob. left. lia. }
      assert (HM1 : aa_MR API L A mem1 md) by exact (kb_MR_A B API L A mem mem1 md _ HM Hmu HAv).
      assert (Hown : forall x, owned B L A x -> mbyte (ms_segs B) mem1 x = mbyte (ms_segs B) mem x).
      { intros x Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) as Hx.
        apply (mbyte_munch (ms_segs B) [(G_LIVE, G_LIVE + 8)]); [exact Hmu | lia |].
        apply HAv; [lia | left; exact Ho]. }
      assert (Hro1 : ro_agree (ms_segs B) mem1).
      { intros a Hra'. destruct (kb_outside_dec [(G_LIVE, G_LIVE + 8)] (bv_unsigned a)) as [Ho|Ho].
        - unfold Mem.mrd. rewrite (Hmu a Ho). exact (Hinv a Hra').
        - assert (Hr : G_LIVE <= bv_unsigned a < G_LIVE + 8).
          { destruct (Z_lt_le_dec (bv_unsigned a) G_LIVE) as [H1|H1];
              [exfalso; apply Ho; apply outside_one; lia|].
            destruct (Z_lt_le_dec (bv_unsigned a) (G_LIVE + 8)) as [H2|H2];
              [lia | exfalso; apply Ho; apply outside_one; lia]. }
          destruct (HG (bv_unsigned a) (ff_glob (bv_unsigned a) ltac:(left; lia))) as (_ & _ & (seg & Hf & Hw) & _).
          unfold Mem.ro_addr in Hra'. rewrite Hf, Hw in Hra'. discriminate. }
      assert (Hpre1 : call_pre B (aa_MR API) L A regs1 mem1 md).
      { apply call_pre_k_alloc.
        eapply (kb_pre_A B API ALLOC_STACK 0 ALLOC_STACK);
          [exact Hpre | lia | lia | lia | rewrite Hsp1; lia | rewrite Hsp1; exact Hal
          | rewrite Hreg; exact HR4 | rewrite Hreg, HR1; exact Hra | exact Hmu | exact Hwm | | exact HAv].
        intros x Hx Hx'. apply outside_one. right. lia. }
      replace (Z_to_bv 64 0x18250) with (Z_to_bv 64 (ms_free B)) by (rewrite Hfree; reflexivity).
      eapply SR_mono.
      { apply (HF L A regs1 mem1 md q (k + 16) b Hpre1 Hro1 Hq); [| exact Hres].
        rewrite Hreg, HR10, Eq. reflexivity. }
      intros c' (L' & A' & regs2 & mem2 & md' & Hc' & Hpost & Hsplit & Hkept & Hro2 & Hgk & Hub & Hinit & Hlen & Hres2).
      apply call_post_k_alloc in Hpost.
      destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as [Hmid2 Hpres2].
      assert (Hblkq : In (ptr_addr L q, k + 16) (blocks L A)) by (rewrite Eq; exact Hblk).
      assert (Hkeep : keeps B L A mem mem2 (p - 16)).
      { intros a n i Hin' Hne Hi.
        rewrite (Hkept a n i Hin' ltac:(cbv beta; rewrite Eq; exact Hne) Hi).
        exact (kb_blocks_munch B API L A mem mem1 md _ HM Hmu HAv a n i Hin' Hi). }
      assert (Hg2 : forall x, in_globals LedgerCells.GL_runs x ->
                mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem1 x).
      { intros x Hx. eapply (kb_post_globals B API _ ALLOC_STACK);
          [exact HG | exact HM1 | exact Hpost | rewrite Hsp1; exact Hlo | exact Hx |].
        intros HE. destruct (HG x Hx) as (_ & _ & _ & _ & Ho). destruct (Ho L A mem md HM) as [_ Hnb].
        exact (Hnb _ _ Hblkq HE). }
      assert (HWl2 : word_mem (ms_segs B) mem2 G_LIVE (lsum (l1 ++ l2))).
      { apply (word_mem_frame (ms_segs B) mem1).
        - rewrite <- Hsum. pose proof (bytes_at_le8_word _ _ _ _ HBL) as Hw.
          rewrite MState.unsigned_lit in Hw by lia. exact Hw.
        - intros j Hj. apply Hg2. apply ff_glob. left. lia. }
      assert (Hled2 : ledger B L' A' mem2 (l1 ++ l2) peak cnt fail).
      { destruct Hsplit as (b1 & b2 & Hb1 & Hb2). rewrite Eq in Hb1. rewrite HLam in Hled.
        apply (ledger_free B L A mem L' A' mem2 l1 l2 p k peak cnt fail b1 b2 Hled Hb1 Hb2 Hkeep HWl2).
        intros x Hx.
        rewrite Hg2 by (apply ff_glob; unfold G_PEAK, G_COUNT, G_FAIL, G_LIVE in *; lia).
        apply (mbyte_munch (ms_segs B) [(G_LIVE, G_LIVE + 8)]);
          [exact Hmu | unfold G_PEAK, G_COUNT, G_FAIL, G_LIVE in *; lia |].
        apply outside_one. unfold G_PEAK, G_COUNT, G_FAIL, G_LIVE in *; lia. }
      exists L', A', regs2, mem2, md'.
      split; [rewrite Hc', Hreg, HR1; reflexivity|].
      split; [exact Hro2|].
      split.
      { intros i Hi. rewrite (Hgk i Hi). apply Hown. right. unfold static_owned.
        right; right; right; right; left. lia. }
      split; [exact Hinit|].
      split.
      { intros HA'. exfalso. rewrite (Hinit (ff_init_of_block A _ HWF Hq)) in HA'. discriminate. }
      split.
      { apply kb_post.
        - eapply kb_mid_E.
          + eapply (kb_mid_seqAX B API);
              [ | exact Hmid2 | lia | lia | lia | lia | intros a Ha Hn; exfalso; apply Hn; lia ].
            apply (kb_mid_A B API HI ALLOC_STACK (spZ regs) L A mem md mem1 [(G_LIVE, G_LIVE + 8)]
                     (fun a => G_LIVE <= a < G_LIVE + 8));
              [exact HM | exact HWF | exact HB | exact Hstk | exact Hmu | exact Hwm | | exact HAv].
            intros x Hx Hns Hne. cbv beta in Hne. apply outside_one. lia.
          + intros a [Ha|Ha]; cbv beta in Ha; unfold free_writes;
              [left; exact Ha | right; split; [exact Hp0 | rewrite Eq in Ha; lia]].
        - exact (kb_preserved_trans _ _ _ (kb_preserved_getr _ _ _ HRp Hreg) Hpres2). }
      split; [exact Hlen|].
      split; [exact Hkeep|].
      split.
      { intros q' k' Hin' Hne. apply Hub; [exact Hin'|]. intros ->. apply Hne. rewrite Eq. f_equal.
        pose proof (YO10.user_block_ptrs_NoDup A HWF) as ND.
        exact (ff_fst_unique _ q k' (k + 16) ND Hin' Hq). }
      right. split; [exact Hp0|]. split.
      { destruct Hsplit as (b1 & b2 & Hb1 & Hb2). exists b1, b2. rewrite <- Eq. split; assumption. }
      split; [exists l1, l2; split; [exact HLam | exact Hled2] | exact Hres2].
Qed.

End Free.
