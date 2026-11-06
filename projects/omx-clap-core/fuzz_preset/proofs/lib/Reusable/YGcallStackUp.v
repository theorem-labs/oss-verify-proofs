(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (c-omx-alloc, engine owner): THE LIVE REAL STACK FROM sp UP TO ly_top IS PRESENT, as a
   function-precondition conjunct carried by the journal (h-rw-pre-7's request: B' `same` keeps its argument in s0
   across a recursive call, and the frame-pointer walk YG00.fpchain reads words at fp - 8 / fp - 16 up to ly_top).
   rule 24: proves no function (kind: engine lemma). Image-free: no address, no image number.
   NOT a law about the ASan stack zone; [ly_stk_lo, ly_stk_hi) presence is FALSE, see stack_zone_presence_false.

   WHY A PRECONDITION AND NOT AN AR_laws_x FIELD. [ly_stk_lo, ly_stk_hi) is ASan's stack ZONE (layout_ok, YG0f.v; the
   head of zero_shadow_ranges, YG0n.v), not the mapped stack: at the run's layout it is [page_floor (usp - 8 MiB), 2^47)
   (top_ok, lib/A/AD1v.v), while LPS maps only [usp - 8 MiB, usp) and the entry image above usp (Run.init_machine_state).
   Neither cgif's AR nor ARcf reads a real-stack byte, so no stack-presence field has a discharge at either instance.
   The true fact is about the LIVE stack [sp, ly_top): the callers' frames and the entry image's page.

   THE LEMMAS.
   - astack_up_x: the conjunct, `forall a, sp <= a < ly_top ly -> apresent (w_H W) mem a`. Add it beside afn_pre_x's
     window conjunct at a function's entry.
   - astack_up_need_x: with afn_pre_x, every byte of [spZ regs - STK, ly_top) is present, so every word fpchain reads
     from a chain rooted at or above sp.
   - astack_up_journal_xw: ajournal_xw keeps it, at ANY wild budget WS, and extends it down over the callee's window.
     It uses only the journal's window presence, its unchanged view at and above alloc_ceiling outside the window,
     astk_ok and layout_le's ly_top; no journal change. astack_up_journal_x is its WS = [] corollary (ajournal_x).
   - astack_up_at_xw: the step YCbqG.afn_pre_x_at needs for a callee entered inside the caller's window, at any WS;
     astack_up_at_x is its WS = [] corollary.
   - astack_up_journal_xwR / astack_up_at_xwR: the same two over a journal at any world relation R (ajournal_xwR); the
     world conjunct is not read. astack_up_journal_xw / astack_up_at_xw are their instances at wle.
   - SATISFIABLE AT THE REAL INSTANCE: astack_up_init. At LPS's initial state (Run.init_machine_state, sp register = the
     start draw usp) astack_up_x holds over [usp, ly_top) under the run's layout facts (ly_top page aligned, layout_ok;
     ly_top <= usp + 3920, top_ok lib/A/AD1v.v) and a world that hides no byte of [usp, ly_top): the entry image is
     mapped up to its page top (Run.entry_stack_image_top), which is at or above ly_top. What remains for a harness
     entry: (1) the harness's initial world (YD2i.W1, hidden set H1) hides no byte of [usp, ly_top); (2) the start-up
     code from the process entry to the harness entry keeps those bytes present (it is not journal-structured).
   - NEGATIVE CONTROL: stack_zone_presence_false (zone presence fails at LPS's initial memory for the start draw
     usp = sp_window_lo + 16; stack_zone_presence_false_inhabited shows its premises are satisfiable),
     F25_counterexample_init (both ends of the zone: the byte below usp - 8 MiB and the byte 2^47 - 1),
     lps_init_mem_none and stk_zone_low_gap (the two facts they use).
   - FOR A RECURSIVE CALLER (appended last): astack_up_weaken_x (the conjunct at sp - STK gives it at sp; with
     astack_up_at_x) and astack_up_guard_x (the bridge to the guarded stack premise of the kit text tsame_specX,
     lib/A/PRH_FnEx.v: `spZ regs <= pa -> forall a, spZ regs <= a < ly_top ly -> apresent (w_H W) mem a`). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YI16 YA0n YG00 YG0f YG0n YG0d YM05 YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK14.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* THE CONJUNCT: the live real stack from sp up to ly_top is present. *)
Definition astack_up_x (ly : alayout) (W : world segs) (sp : Z) (mem : word -> option byte) : Prop :=
  forall a, sp <= a < ly_top ly -> apresent (w_H W) mem a.
(* h-rw-pre-7's need: with afn_pre_x, every byte of [spZ regs - STK, ly_top) is present *)
Lemma astack_up_need_x : forall STK ly S Hp W regs mem md ch,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> astack_up_x ly W (spZ regs) mem ->
  forall a, spZ regs - STK <= a < ly_top ly -> apresent (w_H W) mem a.
Proof.
intros STK ly S Hp W regs mem md ch (_ & _ & _ & _ & _ & _ & Hwin & _) Hup a Ha.
destruct (Z_lt_le_dec a (spZ regs)) as [Hlt|Hge]; [apply Hwin; lia | apply Hup; lia].
Qed.
(* the journal keeps it, and extends it down over the callee's window, at ANY wild budget WS and over ANY world
   relation R (it reads only the journal's window presence, its unchanged high view outside the window, astk_ok and
   layout_le's ly_top; neither the budget nor the world conjunct is used). *)
Lemma astack_up_journal_xwR : forall (R : world segs -> world segs -> Prop)
  STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  astack_up_x ly W sp0 mem -> astack_up_x ly' W' (sp0 - STK) mem'.
Proof.
intros R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS HJ Hup a Ha.
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_hi HJ) as Hhi. pose proof (ajxR_pres HJ) as Hpres.
pose proof (ajxR_stk HJ) as Hstk. unfold astk_ok in Hstk.
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). rewrite Etop in Ha.
pose proof (@alloc_ceiling_val rc) as [[CL _] _].
destruct (Z_lt_le_dec a sp0) as [Hlt|Hge].
- apply Hpres. lia.
- eapply apresent_transfer.
  + lia.
  + intros Him. pose proof (segs_low a Him). unfold kLowMemEnd in *. lia.
  + apply Hhi; lia.
  + apply Hup. lia.
Qed.
(* the journal keeps it, and extends it down over the callee's window, at ANY wild budget WS (it reads only the
   journal's window presence, its unchanged high view outside the window, astk_ok and layout_le's ly_top; the budget
   conjunct is not used). The WS = [] forms below are its corollaries, statements unchanged. *)
Lemma astack_up_journal_xw : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  astack_up_x ly W sp0 mem -> astack_up_x ly' W' (sp0 - STK) mem'.
Proof. exact (astack_up_journal_xwR (@wle segs)). Qed.
Lemma astack_up_journal_x : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  astack_up_x ly W sp0 mem -> astack_up_x ly' W' (sp0 - STK) mem'.
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ.
exact (astack_up_journal_xw STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k [] HJ).
Qed.
(* a callee entered at sp1 inside the caller's window [sp0 - STK, sp0), with window STK1, gets it from the caller's
   journal (the window step of YCbqG.afn_pre_x_at), at any wild budget WS, over any world relation R *)
Lemma astack_up_at_xwR : forall (R : world segs -> world segs -> Prop)
  STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS sp1 STK1,
  ajournal_xwR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS ->
  astack_up_x ly W0 sp0 mem -> sp1 <= sp0 -> 0 <= STK1 -> STK1 + (sp0 - sp1) <= STK ->
  astack_up_x lyc W (sp1 - STK1) memc.
Proof.
intros R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS sp1 STK1 HJ Hup H1 H2 H3 a Ha.
apply (astack_up_journal_xwR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS HJ Hup). lia.
Qed.
(* a callee entered at sp1 inside the caller's window [sp0 - STK, sp0), with window STK1, gets it from the caller's
   journal (the window step of YCbqG.afn_pre_x_at), at any wild budget WS *)
Lemma astack_up_at_xw : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS sp1 STK1,
  ajournal_xw segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS ->
  astack_up_x ly W0 sp0 mem -> sp1 <= sp0 -> 0 <= STK1 -> STK1 + (sp0 - sp1) <= STK ->
  astack_up_x lyc W (sp1 - STK1) memc.
Proof. exact (astack_up_at_xwR (@wle segs)). Qed.
Lemma astack_up_at_x : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k sp1 STK1,
  ajournal_x segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  astack_up_x ly W0 sp0 mem -> sp1 <= sp0 -> 0 <= STK1 -> STK1 + (sp0 - sp1) <= STK ->
  astack_up_x lyc W (sp1 - STK1) memc.
Proof.
intros STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k sp1 STK1 HJ.
exact (astack_up_at_xw STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k [] sp1 STK1 HJ).
Qed.
(* SATISFIABILITY WITNESS at the real initial state: astack_up_x holds at LPS's initial machine state, at its own sp
   register, under the run's layout facts and a world that hides no byte of [usp, ly_top). *)
Lemma astack_up_init : forall pc ph (sp : word) draw argv envp uid hw (W : world segs) ly,
  bv_unsigned sp <= sp_window_hi -> ly_top ly mod 4096 = 0 -> ly_top ly <= bv_unsigned sp + 3920 ->
  (forall a, bv_unsigned sp <= a < ly_top ly -> w_H W (Z_to_bv 64 a) = false) ->
  spZ (ms_regs (init_machine_state segs pc ph sp draw argv envp uid hw)) = bv_unsigned sp /\
  astack_up_x ly W (spZ (ms_regs (init_machine_state segs pc ph sp draw argv envp uid hw)))
    (ms_mem (init_machine_state segs pc ph sp draw argv envp uid hw)).
Proof.
intros pc ph sp draw argv envp uid hw W ly Hsp Hal Htop Hhid.
assert (Esp : spZ (ms_regs (init_machine_state segs pc ph sp draw argv envp uid hw)) = bv_unsigned sp).
{ rewrite init_mkst. cbn [ms_regs mkst]. unfold spZ. rewrite getr_same by reg_neq_tac. reflexivity. }
split; [exact Esp|]. rewrite Esp. intros a Ha. split; [exact (Hhid a Ha)|].
pose proof (u64_range sp) as Rsp.
pose proof (entry_stack_image_top ph sp argv envp uid hw draw) as Himg.
assert (Hlen : ly_top ly <= bv_unsigned sp + Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw))).
{ rewrite Himg. unfold entry_page_top, entry_block_top, page_round_up_Z, page_size.
  set (x := bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw draw)) + 4096 - 1).
  assert (Hx : bv_unsigned sp + 4095 <= x) by (unfold x; lia).
  pose proof (Z.div_mod x 4096 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as P.
  pose proof (Z.div_mod (ly_top ly) 4096 ltac:(lia)) as DT. rewrite Hal, Z.add_0_r in DT. lia. }
assert (Hu : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus; cbn. unfold sp_window_hi in Hsp. lia. }
unfold init_machine_state. cbn [ms_mem]. cbv beta zeta. unfold stack_to_mem. cbv beta zeta. rewrite Hu.
destruct (Z.leb_spec (bv_unsigned sp) a) as [L1|L1]; [|lia].
destruct (Z.ltb_spec (a - bv_unsigned sp)
  (Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw)))) as [L2|L2]; [|lia].
destruct (nth_error (entry_stack_image ph sp argv envp uid hw draw) (Z.to_nat (a - bv_unsigned sp))) as [b|] eqn:E.
- exists b. reflexivity.
- exfalso. apply nth_error_None in E. apply Nat2Z.inj_le in E. rewrite Z2Nat.id in E by lia. lia.
Qed.
End u.

(* NEGATIVE CONTROL: the zone-presence law `ly_stk_lo ly <= a < ly_stk_hi ly -> apresent ..` is FALSE. *)
(* LPS's initial memory (Run.init_machine_state): a byte below the zero window [sp - stack_max_size, sp) or at or above
   the top of the entry image is absent. *)
Lemma lps_init_mem_none : forall segs pc ph (sp : word) draw argv envp uid hw (addr : word),
  (bv_unsigned addr < bv_unsigned sp - stack_max_size \/
   bv_unsigned sp + Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw)) <= bv_unsigned addr) ->
  ms_mem (init_machine_state segs pc ph sp draw argv envp uid hw) addr = None.
Proof.
intros segs pc ph sp draw argv envp uid hw addr H.
unfold init_machine_state. cbn [ms_mem]. cbv beta zeta. unfold stack_to_mem.
pose proof stack_max_size_val as SM.
destruct (Z.leb_spec (bv_unsigned sp) (bv_unsigned addr)) as [L1|L1].
- destruct (Z.ltb_spec (bv_unsigned addr - bv_unsigned sp)
    (Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw)))) as [L2|L2]; [lia|].
  destruct (Z.leb_spec (bv_unsigned sp - stack_max_size) (bv_unsigned addr));
  destruct (Z.ltb_spec (bv_unsigned addr) (bv_unsigned sp)); cbn; try reflexivity; lia.
- destruct (Z.leb_spec (bv_unsigned sp - stack_max_size) (bv_unsigned addr));
  destruct (Z.ltb_spec (bv_unsigned addr) (bv_unsigned sp)); cbn; try reflexivity; lia.
Qed.
Section n. Context {rc : YM05.RunCeil}.
(* at the run's zone (top_ok: ly_stk_lo = ASAN_CEIL = page_floor (usp - stack_max_size), ly_stk_hi = kHighMemEnd), for
   a draw usp that is not page aligned the byte usp - stack_max_size - 1 is in the zone and below LPS's zero window *)
Lemma stk_zone_low_gap : forall (usp : Z) (ly : alayout),
  ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd -> ceil_of_top (usp - stack_max_size) ->
  sp_window_lo <= usp <= sp_window_hi -> usp mod 4096 <> 0 ->
  ly_stk_lo ly <= usp - stack_max_size - 1 < ly_stk_hi ly.
Proof.
intros usp ly Elo Ehi CT U Hm. rewrite Elo, Ehi. unfold ASAN_CEIL. rewrite CT. unfold page_floor.
pose proof stack_max_size_val as SM.
pose proof (Z.div_mod (usp - stack_max_size) 4096 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (usp - stack_max_size) 4096 ltac:(lia)) as P.
assert (Hm' : (usp - stack_max_size) mod 4096 <> 0).
{ intros E. apply Hm. replace usp with ((usp - stack_max_size) + 2048 * 4096) by (rewrite SM; lia).
  rewrite Z.add_mod, E by lia. reflexivity. }
unfold kHighMemEnd, sp_window_lo, sp_window_hi in *. lia.
Qed.
(* THE NEGATIVE CONTROL: at the start draw usp = sp_window_lo + 16, at the run's zone, zone presence fails at LPS's
   initial memory, for every hidden set H *)
Lemma stack_zone_presence_false : forall segs pc ph (sp : word) draw argv envp uid hw ly (H : word -> bool),
  bv_unsigned sp = sp_window_lo + 16 ->
  ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd -> ceil_of_top (bv_unsigned sp - stack_max_size) ->
  ~ (forall a, ly_stk_lo ly <= a < ly_stk_hi ly ->
       apresent H (ms_mem (init_machine_state segs pc ph sp draw argv envp uid hw)) a).
Proof.
intros segs pc ph sp draw argv envp uid hw ly H Esp Elo Ehi CT Hall.
pose proof stack_max_size_val as SM.
assert (R : ly_stk_lo ly <= bv_unsigned sp - stack_max_size - 1 < ly_stk_hi ly).
{ apply (stk_zone_low_gap (bv_unsigned sp) ly Elo Ehi CT).
  - rewrite Esp. unfold sp_window_lo, sp_window_hi. lia.
  - rewrite Esp. intros E. vm_compute in E. discriminate E. }
destruct (Hall _ R) as [_ [b Hb]].
rewrite lps_init_mem_none in Hb; [discriminate Hb|].
left. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|].
unfold bv_modulus; cbn. unfold sp_window_lo in *. lia.
Qed.
(* both ends of the zone: the byte below usp - 8 MiB and the byte 2^47 - 1 (above an entry image of <= 2^30 bytes) *)
Lemma F25_counterexample_init : forall segs pc ph (sp : word) draw argv envp uid hw ly,
  bv_unsigned sp = sp_window_lo + 16 ->
  ly_stk_lo ly = ASAN_CEIL -> ly_stk_hi ly = kHighMemEnd -> ceil_of_top (bv_unsigned sp - stack_max_size) ->
  Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw)) <= 2 ^ 30 ->
  (ly_stk_lo ly <= bv_unsigned sp - stack_max_size - 1 < ly_stk_hi ly /\
   ms_mem (init_machine_state segs pc ph sp draw argv envp uid hw) (Z_to_bv 64 (bv_unsigned sp - stack_max_size - 1)) = None) /\
  (ly_stk_lo ly <= kHighMemEnd - 1 < ly_stk_hi ly /\
   ms_mem (init_machine_state segs pc ph sp draw argv envp uid hw) (Z_to_bv 64 (kHighMemEnd - 1)) = None).
Proof.
intros segs pc ph sp draw argv envp uid hw ly Esp Elo Ehi CT Hlen.
pose proof stack_max_size_val as SM.
split.
- split.
  + apply (stk_zone_low_gap (bv_unsigned sp) ly Elo Ehi CT).
    * rewrite Esp. unfold sp_window_lo, sp_window_hi. lia.
    * rewrite Esp. intros E. vm_compute in E. discriminate E.
  + apply lps_init_mem_none. left. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|].
    unfold bv_modulus; cbn. unfold sp_window_lo in *. lia.
- split.
  + rewrite Elo, Ehi. unfold ASAN_CEIL. pose proof (@alloc_ceiling_val rc) as [[_ CM] _]. unfold kHighMemEnd. lia.
  + apply lps_init_mem_none. right. rewrite Z_to_bv_unsigned, bv_wrap_small.
    * unfold kHighMemEnd, sp_window_lo in *. lia.
    * unfold bv_modulus, kHighMemEnd; cbn. lia.
Qed.
End n.
(* the negative control's premises are satisfiable: a run ceiling, a start sp and a layout meet all four *)
Lemma stack_zone_presence_false_inhabited : exists (rc : YM05.RunCeil) (sp : word) (ly : alayout),
  bv_unsigned sp = sp_window_lo + 16 /\ ly_stk_lo ly = @ASAN_CEIL rc /\ ly_stk_hi ly = kHighMemEnd /\
  @ceil_of_top rc (bv_unsigned sp - stack_max_size).
Proof.
assert (Hu : bv_unsigned (Z_to_bv 64 (sp_window_lo + 16)) = sp_window_lo + 16).
{ rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus; cbn. unfold sp_window_lo. lia. }
assert (Hw : sp_window_lo <= sp_window_lo + 16 <= sp_window_hi) by (unfold sp_window_lo, sp_window_hi; lia).
exists (RunCeilOf (sp_window_lo + 16) Hw), (Z_to_bv 64 (sp_window_lo + 16)),
  (ALayout 0 0 0 0 0 0 0 0 0 (run_ceil (sp_window_lo + 16)) kHighMemEnd 0 [] [] 0 [] (0, 0) (fun _ => 0)).
rewrite Hu. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.
Section w.
Variable segs : list Segment.
(* a recursive caller: the conjunct from a lower start (sp - STK) gives it from sp; used with astack_up_at_x *)
Lemma astack_up_weaken_x : forall ly (W : world segs) sp STK mem,
  astack_up_x segs ly W (sp - STK) mem -> 0 <= STK -> astack_up_x segs ly W sp mem.
Proof. intros ly W sp STK mem H HS a Ha. apply H. lia. Qed.
(* the bridge to the guarded stack premise of the kit text tsame_specX (lib/A/PRH_FnEx.v) *)
Lemma astack_up_guard_x : forall ly (W : world segs) regs pa mem,
  astack_up_x segs ly W (spZ regs) mem ->
  (spZ regs <= pa -> forall a, spZ regs <= a < ly_top ly -> apresent (w_H W) mem a).
Proof. intros ly W regs pa mem H _ a Ha. exact (H a Ha). Qed.
End w.
