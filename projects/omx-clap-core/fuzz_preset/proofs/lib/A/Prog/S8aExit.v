(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Exit.v, with its module paths, module names and numbers changed; 354 of its 533 lines of code are new or changed and 282 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102; pin sha256 1be0f53d96cb9d6c, unstripped twin bff8519b): S8a
   PIECE 11, the walk of ex_value's EXIT, A' 0x83d48-0x83e18 (53 instructions), against the piece interface
   lib/A/Prog/S8aIface.v (ev_exit_spec, ev_at_exit, ev_mid, ev_regs, ev_post, ev_Q) at L := A_prog_listing,
   PA := PI_prog_A, PI := prh_img_A. Theorem ev_exit_holds. Same Require / Section shape as S8aEntry.v (piece 1).
   rule 24: the proof index (v5, 2026-10-30T11:28:40Z) finds no released ASan proof of ex_value, no donor
   exit proof on image A'; written new. TEMPLATE: lib/B/Prog/ExvB_Exit.v (image B, the same epilogue on the
   asan-ubsan build: one engine run under YGcallSx.aj_flag_store_x, then YC1fP.paj_ret_at); its lemmas exx_entry /
   exx_wr / exx_keep / exx_region_nth / exx_field / exx_memnorm_keep / exx_dec3 and its segment proof are COPIED and
   restated at A' (s6 / s9 / s11 for B's s8 / s10 / s5, the 256-byte frame for B's 288) as evx_*. MODEL WALK READ, not
   cited: lib/A/Prog/CrsSeg_R.v (image A', the same class-1 release in check_reject_clean_starved).
   THE CODE (objdump of the #102 A' asan binary, unstripped twin sha256 bff8519bbe3ea0e4 of pin 1be0f53d96cb9d6c):
   0x83d48-0x83d50 the retired magic 0x45e0360e by `sd a0, 0(s2)` (s2 = the frame F); 0x83d54 `beqz s6, 0x83da8`
   (s6 = F, NOT TAKEN: the run's fact 4096 <= F on s6's atom decides it); 0x83d58-0x83d98 `li a0, -11` and sixteen
   `sb a0, k(s9)` (s9 = shadow F, k = 0 .. 15); 0x83d9c-0x83da0 THE INLINE RELEASE `ld a0, 120(s6); sb zero, 0(a0)`
   (the word at F + fs_frame_bytes 1 - 8 is the flag's address, ev_mid's flag conjunct); `j 0x83dd8`;
   0x83dd8 `mv a0, s11` (s11 = the result r); 0x83ddc `addi sp, s0, -256` (s0 = the entry sp); the thirteen restores
   from the save area (ev_saved, EV_SAVED's order); `addi sp, sp, 256`; 0x83e18 `ret`.
   THE WALK, every instruction of the piece (53 = 41 run + 12 not reached): ONE run of the listing engine (YC80x over
   YCbqG's ajournal_x) from 0x83d48 to the `ret` under YGcallSx.aj_flag_store_x, which turns the journal's own frame
   list [(1, pos)] into [] at stack_free_state 1 pos; then YC1fP.paj_ret_at.
   NOT REACHED (12): 0x83da8-0x83dd4, the twelve `sb zero, k(s9)` of the s6 = 0 arm (the real-stack frame's shadow
   clear): s6 holds the fake frame F = frame_addr ly 1 pos, and 4096 <= F (frames_bounds_x), so `beqz s6` is not taken.
   No `__asan_report_*` arm and no call lie in the segment.
   THE RUN POSITION (ev_Q's second conjunct `iface_room_pos .. (ea_S a) -> iface_room_pos .. S'`): taken from ev_mid's
   run-position conjunct at P_EXIT, which the kit owner added to S8aIface.v after this piece found it missing
   (S8aIface.v blob c9dc41743560): without it nothing in ev_mid
   related the fields iface_room_pos reads (PresetRoomPos.v :26-33) at the P_EXIT state to ea_S a.
   SECTION HYPOTHESES (beyond B, ARx, LAWS, SK as S8aEntry.v takes them):
   - ASFX: YGcallSx.v's aj_flag_store_x hypothesis of that name, VERBATIM at segs := SEGS (the model's frame free in
     ARx form; cf discharge YGcallScf.v astack_free_x_xs). No law of AR_laws_x gives it.
   - HW : prh_head_wide (8 <= cf_head; S8aEntry.v's HW, preset_head_wide at the instance): a ledger
     head word lies inside its block, away from the runtime-owned flag byte the release writes.
   The rule's other two hypotheses come from LAWS: FFLX = YCbqG.fflx_of_flag_law (field 23 with field 8); SFX =
   YGcallScf.stack_free_x_any (proved for any relation). The flag byte's presence is field 23 (alx_flag).
   THE POST (fpostWFm's parts): the journal at own [] (the rule's), the caller window (ev_mid's window conjunct and the
   run's keep above alloc_ceiling), the callee-saved registers (the restores from ev_saved; sp = s0 + 0, gp / tp the
   entry's), the float state (ev_fx), the memnorm keep (the run writes only bytes the cut's memory defines: the frame's
   word, its shadow, the flag), and ev_Q: room_live_cf by PrhRoomLive's RL_stack_free, the run position by
   PresetRoomPosKeep.room_pos_stack_free (from ev_mid's run-position conjunct), a0 = r, the cursor (struct ex above
   the entry sp, kept), Hp, ablocks (blocks_stack_free_state), the ledger (its cells miss the frame word, the shadow
   band and the flag), and the text's outcome (ev_out).
   COPIED (not Required: S8aEntry's generalised eve_ledger_keep carries its Section's UAR_CELL): S8aEntry.v
   eve_ledger_cell / eve_ledger_keep / eve_in_seg_b / eve_pst_img and eve_pst_chk's image half, statement and proof,
   renamed evx_*.
   NUMERALS (rule 7):
   - LENGTH: 256 (the frame, `addi sp, s0, -256`), 104, 8 (the thirteen saved words below the entry sp, a word), 120
     (the flag word's offset in the class-1 frame, fs_frame_bytes 1 - 8), 128, 16 (fs_frame_bytes 1 and its shadow
     bytes), 272 / 16384 (pi_frame F_ex_value and the stack allowance, read by computation), 4096, 2 ^ 44, 2 ^ 46,
     2 ^ 47, 2 ^ 64 (address-space bounds), 32, 5 (the frame's alignment and its exponent), 400 (the run's fuel).
   - DERIVED: 10088 (= 0x83d48 - A_prog_base, the listing position of P_EXIT, S8aEntry.v's EVE_EXIT), 512 (run_K at
     A_LIM), atom numbers of the symbolic engine (0 .. 31 the registers at the cut, 32 the flag address, 33 .. 45 the
     saved words in EV_SAVED's order), 3 (the flag region's index in the final symbolic state), register numbers 1, 2,
     3, 4, 8, 9, 10, 18 .. 27 (WORD).
   - ADDRESS: none is written. Every address is pa_sigma / pa_val of the listing instance, a frame_addr / flag_addr /
     shadow_addr term, or an ev_act field. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallScf YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* lia here reasons about div only through named facts (Z.div_pos, Z.div_le_upper_bound), as S8aEntry.v *)
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation PA := PI_prog_A.
#[local] Notation PL := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the symbolic state at the cut (0x83d48) ----
   Atoms 0 .. 31 are the registers at the cut (sr_atoms), with s6 (22) written as the atom of s2 (18): both hold the
   frame, and the code stores through s2 and branches / loads through s6. Atom 32 is the flag address (the word at
   F + 120); atoms 33 .. 45 are the thirteen words the prologue spilled (EV_SAVED's order: ra, s0, s1, s2 .. s11 at
   entry). The four regions: the save area below the entry sp (read only, through s0 = the entry sp), the frame (its
   first word written, the flag word read), its sixteen shadow bytes (through s9), the flag byte. The facts give each
   written region's base a range and the frame its alignment, so the engine decides `beqz s6` itself and the segment
   is ONE run to `ret`. *)
Definition EVX_EXIT : Z := 10088.    (* 0x83d48, P_EXIT (DERIVED: pc - A_prog_base) *)
Definition evx_saved_regs : list (bv 5) := map (fun p => Z_to_bv 5 (snd p)) EV_SAVED.
Definition evx_chunk (j : nat) : YP09.chunk :=
  YP09.mkChunk (fst (nth j EV_SAVED (0, 0)) - 256) (CVal 8 (SOff (33 + j) 0)).
Definition evx_saved_chunks : list YP09.chunk := map evx_chunk (seq 0 13).
Definition evx_regions : smem :=
  [ YP09.mkRegion (Some 8%nat) (-104) 0 0 0 evx_saved_chunks;
    YP09.mkRegion (Some 18%nat) 0 128 0 8 [YP09.mkChunk 120 (CVal 8 (SOff 32%nat 0))];
    YP09.mkRegion (Some 25%nat) 0 16 0 16 [];
    YP09.mkRegion (Some 32%nat) 0 1 0 1 [] ].
Definition evx_facts : facts :=
  mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 5); (25%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (32%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition evx_sr : list sv := sr_set sr_atoms 22%bv (SOff 18 0).
Definition ss_evx : sstate := mkSS EVX_EXIT evx_sr evx_regions None evx_facts.
Definition evx_Bx : sv := SLit 0.
Definition evx_Bspan : Z * Z := (0, 0).
Definition evx_SH : list shent := [].

Lemma evx_fb1 : fs_frame_bytes 1 = 128.
Proof. reflexivity. Qed.

(* ---- the memnorm keep across the run (COPIED from ExvB_Exit.v exx_memnorm_keep / exx_dec3, statement and proof) ---- *)
Lemma evx_memnorm_keep : forall segs (m m' : word -> option byte) (Wr : Z -> Prop),
  (forall a, {Wr a} + {~ Wr a}) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> m' x = m x) ->
  (forall x : word, Wr (bv_unsigned x) -> exists b, m x = Some b) ->
  YAkMemnorm.memnorm segs m -> YAkMemnorm.memnorm segs m'.
Proof.
intros segs m m' Wr Hd Hfr Hw Hm. unfold YAkMemnorm.memnorm in Hm |- *. destruct Hm as (Hi & Ht).
split; intros x b E; destruct (Hd (bv_unsigned x)) as [h|h].
- destruct (Hw x h) as (b0 & E0). exact (Hi x b0 E0).
- rewrite (Hfr x h) in E. exact (Hi x b E).
- destruct (Hw x h) as (b0 & E0). exact (Ht x b0 E0).
- rewrite (Hfr x h) in E. exact (Ht x b E).
Qed.
Lemma evx_dec3 : forall F s fl a,
  {(F <= a < F + 8) \/ (s <= a < s + 16) \/ a = fl} + {~ ((F <= a < F + 8) \/ (s <= a < s + 16) \/ a = fl)}.
Proof.
intros F s fl a.
destruct (Z.eq_dec a fl) as [e|e]; [left; right; right; exact e|].
destruct (Z_lt_le_dec a F) as [h1|h1]; destruct (Z_lt_le_dec a (F + 8)) as [h2|h2];
destruct (Z_lt_le_dec a s) as [h3|h3]; destruct (Z_lt_le_dec a (s + 16)) as [h4|h4];
first [left; lia | right; lia].
Qed.

(* a layout the journal reached from the entry's keeps the fake-stack base, so the frame and the flag of (1, pos) sit
   where they sat at entry (YG0f.v layout_le's ly_F conjunct) *)
Lemma evx_layout_frame : forall n ly ly' cid pos, layout_le n ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
intros n ly ly' cid pos (_ & _ & _ & _ & _ & HF & _). unfold frame_addr, flag_addr. rewrite HF. split; reflexivity.
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

Lemma evx_pc : SIGMA AS_ex_value + EV_EXIT = BASE + EVX_EXIT.
Proof. vm_compute. reflexivity. Qed.

Definition evx_E (regs regs0 : bvmap 5 word) (fl : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (w64 fl :: map (getr regs0) evx_saved_regs)).

Lemma evx_E_low : forall regs regs0 fl n, (n < A_TEXT)%nat ->
  ew (evx_E regs regs0 fl) n = ew (Ereg regs (w64 fl :: map (getr regs0) evx_saved_regs)) n.
Proof. intros regs regs0 fl n Hn. unfold evx_E. apply Eimg_low. exact Hn. Qed.
Lemma evx_E_reg : forall regs regs0 fl (r : bv 5) n, Z.of_nat n = bv_unsigned r ->
  ew (evx_E regs regs0 fl) n = getr regs r.
Proof.
intros regs regs0 fl r n Hn. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite evx_E_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma evx_E_fl : forall regs regs0 fl, ew (evx_E regs regs0 fl) 32 = w64 fl.
Proof. intros. rewrite evx_E_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma evx_E_saved : forall regs regs0 fl j, (j < 13)%nat ->
  ew (evx_E regs regs0 fl) (33 + j) = getr regs0 (Z_to_bv 5 (snd (nth j EV_SAVED (0, 0)))).
Proof.
intros regs regs0 fl j Hj. rewrite evx_E_low by (unfold A_TEXT; lia).
replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. cbn [nth].
unfold evx_saved_regs. rewrite map_map.
rewrite (nth_indep _ _ ((fun p : Z * Z => getr regs0 (Z_to_bv 5 (snd p))) (0, 0))) by (rewrite length_map; cbn; lia).
exact (map_nth (fun p : Z * Z => getr regs0 (Z_to_bv 5 (snd p))) EV_SAVED (0, 0) j).
Qed.

(* ---- the entry symbolic state of the segment ---- *)
Lemma evx_entry : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs regs0 : bvmap 5 word) (mem : word -> option byte) (md : Model) (pos : Z),
  ARx ly S Hp W mem md -> In (1, pos) (frames S) ->
  getr regs 8 = w64 (spZ regs0) ->
  getr regs 18 = w64 (frame_addr ly 1 pos) -> getr regs 22 = w64 (frame_addr ly 1 pos) ->
  getr regs 25 = w64 (shadow_addr (frame_addr ly 1 pos)) ->
  (forall o r, In (o, r) EV_SAVED ->
     val_mem SEGS (rdW W mem) (spZ regs0 - 256 + o) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 r)))) ->
  rdword (aview SEGS (w_H W) mem) (frame_addr ly 1 pos + 120) = Some (flag_addr ly 1 pos) ->
  YM05.alloc_ceiling + 104 <= spZ regs0 ->
  st_ok_pi SEGS VAL (evx_E regs regs0 (flag_addr ly 1 pos)) ss_evx
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + EVX_EXIT)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS evx_Bx evx_SH (evx_E regs regs0 (flag_addr ly 1 pos)) (rdW W mem).
Proof.
intros ly S Hp W regs regs0 mem md pos HAR Hin H8 H18 H22 H25 HSAV HFLW Hlo.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (Hmod & Happ & Hfpres & Hshpres).
destruct (alx_flag SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (Hflpres & Hflown & Hflapp & Hflceil).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite evx_fb1 in Happ, Hfpres, Hshpres, HFceil. change (128 / 8) with 16 in Hshpres.
unfold in_app in Hflapp. destruct Hflapp as (Hfl4096 & _).
rewrite restrict_mkst_fx.
set (fl := flag_addr ly 1 pos) in *.
set (F := frame_addr ly 1 pos) in *.
set (E := evx_E regs regs0 fl).
assert (Hsp64 : 0 <= spZ regs0 < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (Usp : bv_unsigned (ew E 8) = spZ regs0)
  by (unfold E; rewrite (evx_E_reg regs regs0 fl 8%bv 8) by reflexivity; rewrite H8; unfold w64; apply unsigned_lit_small; lia).
assert (UF : bv_unsigned (ew E 18) = F)
  by (unfold E; rewrite (evx_E_reg regs regs0 fl 18%bv 18) by reflexivity; rewrite H18; unfold w64; apply unsigned_lit_small; lia).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8p.
assert (HF8 : F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
assert (USH : bv_unsigned (ew E 25) = shadow_addr F).
{ unfold E; rewrite (evx_E_reg regs regs0 fl 25%bv 25) by reflexivity; rewrite H25; unfold w64.
  apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
pose proof (Z.div_mod F 8 ltac:(lia)) as HFd. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HFm.
assert (UFL : bv_unsigned (ew E 32) = fl)
  by (unfold E; rewrite evx_E_fl; unfold w64; apply unsigned_lit_small; lia).
(* the frame's shadow bytes lie in the shadow band, apart from the frame (in_app's two cases) *)
assert (HSB : F + 128 <= shadow_addr F \/ shadow_addr F + 16 <= F).
{ unfold shadow_addr. destruct Happ as (_ & [HL | (HH1 & HH2)]).
  - left. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
  - right. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (HSHhi : shadow_addr F + 16 <= 2 ^ 46) by (unfold shadow_addr, SHADOW_OFF; lia).
(* the flag is runtime-owned and no byte of the frame or of its shadow is *)
assert (HflF : fl < F \/ F + 128 <= fl).
{ destruct (Z_lt_le_dec fl F) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec fl (F + 128)) as [h2|h2]; [|right; exact h2].
  exfalso. exact (proj2 (Hfpres fl (conj h h2)) Hflown). }
assert (HflSH : fl < shadow_addr F \/ shadow_addr F + 16 <= fl).
{ destruct (Z_lt_le_dec fl (shadow_addr F)) as [h|h]; [left; exact h|].
  destruct (Z_lt_le_dec fl (shadow_addr F + 16)) as [h2|h2]; [|right; exact h2].
  exfalso. pose proof (proj2 (Hshpres (fl - shadow_addr F) ltac:(lia))) as Hno.
  replace (shadow_addr F + (fl - shadow_addr F)) with fl in Hno by lia. exact (Hno Hflown). }
split.
- unfold ss_evx. apply (pa_entry_st_ok_full (L := A_prog_listing) (PI := PA)).
  + unfold evx_sr. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. fold E. rewrite UF, Z.add_0_r, H22. reflexivity.
  + vm_compute. reflexivity.
  + unfold evx_regions.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      unfold evx_saved_chunks. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj).
      apply in_seq in Hj. destruct Hj as [_ Hj]. cbn [Nat.add] in Hj.
      destruct (nth j EV_SAVED (0, 0)) as [o rr] eqn:Hor.
      assert (Hin' : In (o, rr) EV_SAVED) by (rewrite <- Hor; apply nth_In; cbn; lia).
      unfold evx_chunk. rewrite Hor. cbn [fst].
      eapply (chunk_ok_val SEGS E _ (spZ regs0) (o - 256) 8 _ (bv_unsigned (getr regs0 (Z_to_bv 5 rr)))).
      -- cbn [sv_denot]. unfold E. rewrite (evx_E_saved regs regs0 fl j Hj), Hor. cbn [snd].
         rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- pose proof (u64_range (getr regs0 (Z_to_bv 5 rr))). zside.
      -- zside.
      -- replace (spZ regs0 + (o - 256)) with (spZ regs0 - 256 + o) by lia. exact (HSAV o rr Hin').
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UF. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply apresent_writable; exact (proj1 (Hfpres (F + o) ltac:(lia)))|].
      apply Forall_cons; [|apply Forall_nil].
      eapply (chunk_ok_val SEGS E _ F 120 8 (SOff 32%nat 0) fl);
      [ cbn [sv_denot]; unfold E; rewrite evx_E_fl; unfold w64; rewrite Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | zside | zside | exact (val_mem_of_rdword SEGS _ _ _ _ HFLW) ].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite USH. split; [unfold shadow_addr, SHADOW_OFF; lia|].
      split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply apresent_writable. exact (proj1 (Hshpres o ltac:(lia))).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UFL. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (fl + o) with fl by lia. apply apresent_writable. exact Hflpres.
  + apply pairwise_disjoint_of_extents. unfold evx_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, UF, USH, UFL.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_addr, SHADOW_OFF in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [evx_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UF, USH, UFL. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold shadow_addr, SHADOW_OFF in *. repeat split; lia.
- unfold sh_ok, evx_SH. apply Forall_nil.
Qed.

(* ---- the run's write set: the frame's first word, its sixteen shadow bytes, the flag byte ---- *)
Lemma evx_wr : forall regs regs0 fl F a,
  getr regs 18 = w64 F -> getr regs 25 = w64 (shadow_addr F) -> 0 <= F -> F + 128 <= 2 ^ 47 -> 0 <= fl < 2 ^ 64 ->
  in_wrange (evx_E regs regs0 fl) evx_regions a ->
  (F <= a < F + 8) \/ (shadow_addr F <= a < shadow_addr F + 16) \/ a = fl.
Proof.
intros regs regs0 fl F a H18 H25 HF0 HF1 Hfl (rg & Hrg & Hr).
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
assert (F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
unfold evx_regions in Hrg. destruct Hrg as [<- | [<- | [<- | [<- | []]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
- lia.
- rewrite (evx_E_reg regs regs0 fl 18%bv 18) in Hr by reflexivity. rewrite H18 in Hr. unfold w64 in Hr.
  rewrite unsigned_lit_small in Hr by lia. lia.
- rewrite (evx_E_reg regs regs0 fl 25%bv 25) in Hr by reflexivity. rewrite H25 in Hr. unfold w64 in Hr.
  rewrite unsigned_lit_small in Hr by (unfold shadow_addr, SHADOW_OFF; lia). lia.
- rewrite evx_E_fl in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by lia. lia.
Qed.
Lemma evx_keep : forall (W : world SEGS) regs regs0 fl (m m' : word -> option byte) F,
  frame_of (evx_E regs regs0 fl) evx_regions (rdW W m) (rdW W m') ->
  getr regs 18 = w64 F -> getr regs 25 = w64 (shadow_addr F) -> 0 <= F -> F + 128 <= 2 ^ 47 -> 0 <= fl < 2 ^ 64 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (shadow_addr F <= a < shadow_addr F + 16) -> a <> fl ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W regs regs0 fl m m' F HFr H18 H25 HF0 HF1 Hfl a Ha N1 N2 N3.
apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros Hw.
destruct (evx_wr regs regs0 fl F a H18 H25 HF0 HF1 Hfl Hw) as [H | [H | H]]; contradiction.
Qed.
(* a region of a final symbolic state, read back (ExvB_Exit.v exx_region_nth / exx_field) *)
Lemma evx_region_nth : forall E ss ms i rg,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some rg -> region_ok SEGS E (ms_mem ms) rg.
Proof.
intros E ss ms i rg HS Hi. unfold st_ok_pi in HS. destruct (st_ok_mem_ok SEGS E _ ms HS) as (_ & Hrs & _).
destruct ss. exact (proj1 (Forall_forall _ _) Hrs rg (nth_error_In _ _ Hi)).
Qed.
Lemma evx_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.
End h.

(* ---- the ledger across a non-allocator memory change (COPIED from S8aEntry.v eve_ledger_cell / eve_ledger_keep, the
   kit's named projections, statement and proof) and alloc.c's statics as image bytes (COPIED from S8aEntry.v
   eve_in_seg_b / eve_pst_chk / eve_pst_img) ---- *)
Section l. Context {rc : YM05.RunCeil} {cp : CfParams}.
Variable B : asyms.
Definition evx_ledger_cell (Lam : list (Z * Z)) (a : Z) : Prop :=
  Exists (in_zr a) PST \/ (exists ak, In ak Lam /\ fst ak - cf_head <= a < fst ak - cf_head + 8).
Lemma evx_ledger_keep : forall ly S Hp (W : world SEGS) mem ly' S' Hp' (W' : world SEGS) mem' Lam peak cnt fail ran
    most own,
  prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  incl (ablocks B ly S) (ablocks B ly' S') -> Hp' = Hp ->
  (forall a, evx_ledger_cell Lam a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger (PI := prh_img_A) (PA := PA) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own LG Hinc -> Hfr.
pose proof (prh_ledger_live _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G1.
pose proof (prh_ledger_peak _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G2.
pose proof (prh_ledger_count _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G3.
pose proof (prh_ledger_fail _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G4.
pose proof (prh_ledger_ran _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G5.
pose proof (prh_ledger_most _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G6.
pose proof (prh_ledger_own _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as G7.
pose proof (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as GR.
pose proof (prh_ledger_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HND.
pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HF.
pose proof (prh_ledger_heads _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HP.
clear LG.
assert (VK : forall x n v, (forall j, 0 <= j < Z.of_nat n -> evx_ledger_cell Lam (x + j)) ->
   val_mem SEGS (mrestrict (w_H W) mem) x n v -> val_mem SEGS (mrestrict (w_H W') mem') x n v).
{ intros x n v Hc Hv j Hj. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') mem mem' (x + Z.of_nat j))
    by (apply Hfr; apply Hc; lia). exact (Hv j Hj). }
assert (VS : forall b w j, In (b, w) PST -> 0 <= j < w -> evx_ledger_cell Lam (b + j)).
{ intros b w j Hin Hj. left. apply Exists_exists. exists (b, w). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
unfold prh_ledger, prh_glob, prh_most, prh_own.
unfold prh_most in G6. unfold prh_own in G7.
split; [|split; [exact HND | split; [| exact HP]]].
- split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact G1]|].
  split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact G2]|].
  split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact G3]|].
  split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact G4]|].
  split; [apply (VK _ 1%nat); [intros j Hj; apply (VS _ 1); [unfold prh_pst; cbn [In]; tauto | lia] | exact G5]|].
  split; [split; [apply (VK _ 8%nat); [intros j Hj; apply (VS _ 8); [unfold prh_pst; cbn [In]; tauto | lia] | exact (proj1 G6)] | exact (proj2 G6)]|].
  split; [split; [apply (VK _ 1%nat); [intros j Hj; apply (VS _ 1); [unfold prh_pst; cbn [In]; tauto | lia] | exact (proj1 G7)] | exact (proj2 G7)]|].
  exact GR.
- apply Forall_forall. intros ak Hak. pose proof (proj1 (Forall_forall _ _) HF ak Hak) as (K0 & K1 & K2 & K3 & K4).
  split; [exact K0|]. split; [exact (Hinc _ K1)|]. split; [exact K2|]. split; [exact K3|].
  apply (VK _ 8%nat); [|exact K4]. intros j Hj. right. exists ak. split; [exact Hak | lia].
Qed.
End l.
Definition evx_in_seg_b {rc : YM05.RunCeil} (r : Z * Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? fst r) &&
    (fst r + snd r <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) SEGS.
Lemma evx_pst_chk {rc : YM05.RunCeil} : forallb evx_in_seg_b PST = true.
Proof. vm_compute; reflexivity. Qed.
Lemma evx_pst_img {rc : YM05.RunCeil} : forall z, Exists (in_zr z) PST -> in_img SEGS z.
Proof.
intros z Hz. apply Exists_exists in Hz as (r & Hr & Hz). unfold in_zr in Hz.
pose proof (proj1 (forallb_forall _ _) evx_pst_chk r Hr) as Hb. unfold evx_in_seg_b in Hb.
apply existsb_exists in Hb as (sg & Hsg & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold in_img. exists sg. split; [exact Hsg | lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the kit's allocator laws at ARx, at the harness head length cf_head, as S8aEntry.v takes them *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* The cf instance's astack_free_law_cf (discharge YGcallScf.v astack_free_x_xs):
   YGcallSx.v's ASFX (aj_flag_store_x's Section hypothesis), VERBATIM at segs := SEGS - the model's frame free in ARx
   form: clearing the flag byte of a live frame, with no other runtime-owned byte changed, is the state
   stack_free_state cid pos S. No law of AR_laws_x gives it. *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
(* The kit's one spelling (PRH_Base.v prh_head_wide; at the preset instance CfParamsPreset.v
   preset_head_wide; S8aEntry.v's HW): a ledger block's head word lies inside its allocator block. *)
Hypothesis HW : prh_head_wide.

#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* ---- the ledger after the release: its reads (the statics, image bytes; the harness heads, inside their blocks since
   cf_head >= 8) miss the frame's word, its shadow and the flag byte ---- *)
Lemma evx_ledger : forall ly S Hp (W : world SEGS) mem md mem' pos Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md -> In (1, pos) (frames S) ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> ~ (frame_addr ly 1 pos <= a < frame_addr ly 1 pos + 8) ->
     ~ (shadow_addr (frame_addr ly 1 pos) <= a < shadow_addr (frame_addr ly 1 pos) + 16) -> a <> flag_addr ly 1 pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  prh_ledger (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prh_ledger (PI := prh_img_A) (PA := PA) B ly (stack_free_state 1 pos S) Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' pos Lam peak cnt fail ran most own HAR Hin HK HLED.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HW as HW8. unfold prh_head_wide in HW8.
destruct (fflx_of_flag_law SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (Hflown & _ & Hflimg).
destruct (alx_flag SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (_ & _ & _ & Hflceil).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite evx_fb1 in HFceil.
pose proof (Z.div_pos (frame_addr ly 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
apply (evx_ledger_keep B ly S Hp W mem ly (stack_free_state 1 pos S) Hp W mem' Lam peak cnt fail ran most own HLED).
- unfold ablocks. rewrite blocks_stack_free_state. apply incl_refl.
- reflexivity.
- intros x [Hx | (ak & Hak & Hx)].
  + pose proof (evx_pst_img x Hx) as Himg. pose proof (Hsegs x Himg) as Hlow.
    unfold kLowMemEnd in Hlow. apply HK.
    * unfold YM05.alloc_ceiling in *; lia.
    * intros Hf. apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md 1 pos x HAR Hin); [rewrite evx_fb1; lia | exact Himg].
    * unfold shadow_addr, SHADOW_OFF. lia.
    * intros E. rewrite E in Himg. exact (Hflimg Himg).
  + pose proof (prh_ledger_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HLED) as HHB.
    destruct (proj1 (Forall_forall _ _) HHB ak Hak) as (Hk0 & Hblk & _).
    destruct ak as [a0 kk]. cbn [fst snd] in Hk0, Hblk, Hx.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hblk) as (B1 & B2 & B3 & Bapp & Bown & _).
    assert (Hreq : req_size (kk + cf_head) = kk + cf_head) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    rewrite Hreq in B3, Bapp, Bown.
    assert (Hxb : a0 - cf_head <= x < a0 - cf_head + (kk + cf_head)) by lia.
    pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md (a0 - cf_head) (kk + cf_head) 1 pos HAR Hblk Hin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Hreq, evx_fb1 in Hsep.
    apply HK.
    * lia.
    * lia.
    * unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp. unfold shadow_addr, SHADOW_OFF.
      pose proof (Z.div_mod (frame_addr ly 1 pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr ly 1 pos) 8 ltac:(lia)).
      lia.
    * intros E. rewrite E in Hxb. exact (proj2 (Bown _ Hxb) Hflown).
Qed.

(* ======== piece 11: the exit ======== *)
Theorem ev_exit_holds : ev_exit_spec (fx := fx) (PI := prh_img_A) (PA := PA) B ARx SK.
Proof.
unfold ev_exit_spec. intros a fxc W regs mem md ly S Hp k r p' dep' dl' HPRE HFX HEX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HEX as (HMID & HREGS & H22 & H27 & HOUT).
destruct HMID as (HJ & HWIN & HHp & HAB & HLED & HCUR & _ & _ & _ & HSAV & HFLW & HRL & HRP & HMN).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & Hqlo & Hqhi & Hwin & _).
destruct HFPRE as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
change (spZ (ea_regs a)) with (ea_sp0 a) in *.
(* the function's stack need (LENGTH, from prh_img_A, as S8aEntry.v) *)
assert (HSTK : ea_STK (PI := prh_img_A) a = Z.of_nat (Nat.succ (ea_n a)) * 272 + 16384).
{ unfold ea_STK, STK_ex_value. cbn [pi_frame prh_img_A]. f_equal; try (vm_compute; reflexivity). }
assert (HSTKlo : 16656 <= ea_STK (PI := prh_img_A) a)
  by (rewrite HSTK, Nat2Z.inj_succ; pose proof (Nat2Z.is_nonneg (ea_n a)); lia).
assert (Hsp : YM05.alloc_ceiling + 104 <= ea_sp0 a) by lia.
(* the journal: the state, the own frame, the layout *)
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_frs HJ) as Hfrs. pose proof (ajx_ly HJ) as Hly.
set (pos := ea_pos a) in *.
assert (Hin : In (1, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (evx_layout_frame _ _ _ 1 pos Hly) as (HFeq & HFLeq).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (_ & _ & Hfpres & Hshpres).
rewrite evx_fb1 in Hfpres, Hshpres. change (128 / 8) with 16 in Hshpres.
destruct (alx_flag SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (Hflpres & Hflown & Hflapp & Hflceil).
unfold in_app in Hflapp. destruct Hflapp as (Hfl4096 & _).
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 1 pos HAR Hin) as (HF4096 & HFceil & _).
rewrite evx_fb1 in HFceil.
set (F := frame_addr ly 1 pos) in *.
set (fl := flag_addr ly 1 pos) in *.
assert (HFra : ea_fr a = F) by (rewrite HFeq; reflexivity).
rewrite HFra in R18, H22, R25, HFLW. rewrite <- HFLeq in HFLW. fold fl in HFLW.
replace (F + fs_frame_bytes 1 - 8) with (F + 120) in HFLW by (rewrite evx_fb1; lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HFd. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HFm.
assert (HSAV' : forall o rr, In (o, rr) EV_SAVED ->
  val_mem SEGS (rdW W mem) (spZ (ea_regs a) - 256 + o) 8 (bv_unsigned (getr (ea_regs a) (Z_to_bv 5 rr)))).
{ intros o rr Hor. exact (proj1 (Forall_forall _ _) HSAV (o, rr) Hor). }
destruct (evx_entry (fx := fxc) B ARx LAWS ly S Hp W regs (ea_regs a) mem md pos HAR Hin R8 R18 H22 R25 HSAV' HFLW Hsp)
  as [HS SHOK].
change (flag_addr ly 1 pos) with fl in HS, SHOK.
remember (evx_E regs (ea_regs a) fl) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; unfold evx_E; apply Eimg_env).
(* the atoms' values *)
assert (E27 : ew Ev 27 = w64 r) by (rewrite HEv, (evx_E_reg regs (ea_regs a) _ 27%bv 27) by reflexivity; exact H27).
assert (E8 : ew Ev 8 = getr (ea_regs a) (Z_to_bv 5 2)).
{ rewrite HEv, (evx_E_reg regs (ea_regs a) _ 8%bv 8) by reflexivity. rewrite R8. unfold w64, ea_sp0, spZ.
  rewrite Z_to_bv_bv_unsigned. all: try (f_equal; apply bv_eq; vm_compute; reflexivity). }
assert (E3 : ew Ev 3 = getr (ea_regs a) (Z_to_bv 5 3)).
{ rewrite HEv, (evx_E_reg regs (ea_regs a) _ 3%bv 3) by reflexivity. rewrite R3.
  all: try (f_equal; apply bv_eq; vm_compute; reflexivity). }
assert (E4 : ew Ev 4 = getr (ea_regs a) (Z_to_bv 5 4)).
{ rewrite HEv, (evx_E_reg regs (ea_regs a) _ 4%bv 4) by reflexivity. rewrite R4.
  all: try (f_equal; apply bv_eq; vm_compute; reflexivity). }
assert (ES : forall j, (j < 13)%nat -> ew Ev (33 + j) = getr (ea_regs a) (Z_to_bv 5 (snd (nth j EV_SAVED (0, 0))))).
{ intros j Hj. rewrite HEv. apply evx_E_saved. exact Hj. }
(* the run: the cut to `ret`, under the inline release *)
pose (FLAG := aj_flag_store_x (fx := fxc) (rc := rc) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) ASFX
  (fflx_of_flag_law SEGS B ARx LAWS) (YGcallScf.stack_free_x_any SEGS ARx)
  asym (@pa_wx _ _ PA) (clookup (@pa_tbl _ _ PA)) VAL SIGMA A_prog_listing (@pl_tpi _ PL) (@pl_tw _ PL)
  (pa_fetch_ok (PI := PA)) (@pa_cert _ _ PA) (@pa_B_ok _ _ PA) A_LIM A_LIM_text (@pl_lim _ PL) (@pl_len _ PL)
  (@pl_tpi_eq _ PL) (@pl_tw_eq _ PL)).
unfold ev_cfg, ev_pc. rewrite evx_pc.
let rr := eval vm_compute in (sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) 512 evx_Bx evx_Bspan evx_SH 400%N ss_evx) in
lazymatch rr with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi _ PL) (@pl_tw _ PL) 512 evx_Bx evx_Bspan evx_SH 400%N ss_evx = (st', rs))
    by (vm_compute; reflexivity)
end.
eapply (FLAG W 400%N Ev 512%nat evx_Bx evx_Bspan evx_SH ss_evx _ _ _ _ _ _ _ _ _ _ _ _ [] ly S Hp md k 1 pos _
  ltac:(unfold A_LIM; lia) HEI ltac:(lia) HS SHOK ltac:(vm_compute; reflexivity) Hrun I HJ).
- cbn [sh_obls]. apply Forall_nil.
- intros x Hx. rewrite HEv in Hx.
  destruct (evx_wr regs (ea_regs a) fl F x R18 R25 ltac:(lia) ltac:(lia) ltac:(lia) Hx) as [Hw | [Hw | Hw]].
  + left. right. right. right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite evx_fb1. lia.
  + left. right. right. right. exists 1, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite evx_fb1. change (128 / 8) with 16. fold F. lia.
  + right. exact Hw.
- intros ws msr Hl HSf. cbn [sh_j] in Hl. destruct ws; [|discriminate Hl]. cbn [extK] in HSf.
  pose proof (evx_region_nth _ _ msr 3 _ HSf eq_refl) as RG.
  assert (UFL : bv_unsigned (ew Ev 32) = fl)
    by (rewrite HEv, evx_E_fl; unfold w64; apply unsigned_lit_small; lia).
  pose proof (evx_field _ _ 32 _ _ _ _ _ _ 0 1 (SLit 0) 0 RG UFL ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
    as V.
  specialize (V 0%nat ltac:(cbn; lia)). replace (fl + 0 + Z.of_nat 0) with fl in V by lia.
  exact V.
- clear HS HJ SHOK. paj_after_run_tok HS HJ SHOK.
  eapply (paj_ret_at (fx := fxc) (PL := PL) (PI := PA) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat2.
  (* the bytes the run kept: everything but the frame's word, its shadow and the flag *)
  assert (KW : forall x, 0 <= x < 2 ^ 64 -> ~ (F <= x < F + 8) -> ~ (shadow_addr F <= x < shadow_addr F + 16) ->
     x <> fl -> aview SEGS (w_H W) (ms_mem ms) x = aview SEGS (w_H W) mem x).
  { rewrite HEv in HFr.
    exact (evx_keep W regs (ea_regs a) fl mem (ms_mem ms) F HFr R18 R25 ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (KALL : forall x, YM05.alloc_ceiling <= x < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) x = aview SEGS (w_H W) mem x).
  { intros x Hx. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
    assert (F / 8 <= F) by (apply Z.div_le_upper_bound; lia).
    apply KW; [lia | lia | unfold shadow_addr, SHADOW_OFF; lia | lia]. }
  (* memnorm: the run wrote only bytes the cut's memory defines (the frame, its shadow, the flag) *)
  assert (KMN : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS (ms_mem ms)).
  { apply (evx_memnorm_keep SEGS mem (ms_mem ms) (fun x => (F <= x < F + 8) \/
      (shadow_addr F <= x < shadow_addr F + 16) \/ x = fl)).
    - intros x. apply evx_dec3.
    - intros x Hx. apply HF. rewrite HEv. intros Hw. apply Hx.
      exact (evx_wr regs (ea_regs a) fl F (bv_unsigned x) R18 R25 ltac:(lia) ltac:(lia) ltac:(lia) Hw).
    - intros x [Hx | [Hx | Hx]].
      + destruct (Hfpres (bv_unsigned x) ltac:(lia)) as ((_ & b & Eb) & _). rewrite Z_to_bv_bv_unsigned in Eb.
        exists b. exact Eb.
      + destruct (Hshpres (bv_unsigned x - shadow_addr F) ltac:(lia)) as ((_ & b & Eb) & _).
        replace (shadow_addr F + (bv_unsigned x - shadow_addr F)) with (bv_unsigned x) in Eb by lia.
        rewrite Z_to_bv_bv_unsigned in Eb. exists b. exact Eb.
      + destruct Hflpres as (_ & b & Eb). rewrite <- Hx, Z_to_bv_bv_unsigned in Eb. exists b. exact Eb. }
  (* the registers at `ret` *)
  prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0.
  pose proof (ES 0%nat ltac:(lia)) as ES0. cbn [Nat.add nth EV_SAVED snd] in ES0.
  assert (RA : v_jalr (getr (ms_regs ms) 1) 0 = YK11.getr (ea_regs a) 1).
  { rewrite Rra, ES0. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    unfold YK0s.ret_ok in Hra. exact Hra. }
  assert (AR : aregs_preserved (ea_regs a) (ms_regs ms)).
  { intros rr Hrr. unfold acallee_saved in Hrr.
    assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
      rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
      let Q := fresh "Q" in prreg HS (Z_to_bv 5 z) Q; rewrite Q end;
    first [ exact E8 | exact E3 | exact E4
          | exact (ES 1%nat ltac:(lia)) | exact (ES 2%nat ltac:(lia)) | exact (ES 3%nat ltac:(lia))
          | exact (ES 4%nat ltac:(lia)) | exact (ES 5%nat ltac:(lia)) | exact (ES 6%nat ltac:(lia))
          | exact (ES 7%nat ltac:(lia)) | exact (ES 8%nat ltac:(lia)) | exact (ES 9%nat ltac:(lia))
          | exact (ES 10%nat ltac:(lia)) | exact (ES 11%nat ltac:(lia)) | exact (ES 12%nat ltac:(lia)) ]. }
  rewrite RA. unfold ev_post, fpostWFm, fpostWF, fQmn, ev_Q. cbv beta.
  exists fxc, ly, (stack_free_state 1 pos S), Hp, (ms_regs ms), (ms_mem ms). eexists. exists k.
  split; [reflexivity|].
  split; [exact (proj1 HFX)|]. split; [exact (proj2 HFX)|].
  split; [apply (ajournal_x_materialize (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA)); exact HJ|].
  split.
  { intros x Hx Hna. change (spZ (ea_regs a)) with (ea_sp0 a) in Hx.
    transitivity (aview SEGS (w_H W) mem x); [apply KALL; lia | exact (HWIN x Hx Hna)]. }
  split; [exact AR|].
  split; [| exact (fun _ => KMN HMN)].
  split.
  { intros HR0. exact (RL_stack_free S 1 pos (proj1 HRL HR0)). }
  (* ev_Q's hull use: ev_mid's (paired with its room keep), then the frame release keeps st_secs *)
  split.
  { exact (PresetHullBudget.hull_used_app _ _ _ nil nil (proj2 HRL)
      (PresetHullBudget.hull_used_secs S (stack_free_state 1 pos S) nil eq_refl)). }
  split.
  { intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist Hrp.
    apply PresetRoomPosKeep.room_pos_stack_free. exact (HRP rp_sm rp_x rp_os rp_i rp_H0 rp_hist Hrp). }
  exists r, p', dep', dl'.
  split; [rewrite Ra0; exact E27|].
  split.
  { unfold prhex_cur in HCUR |- *. destruct HCUR as (V1 & V2 & V3 & V4 & V5).
    assert (VQ : forall x (w : nat) v, val_mem SEGS (rdW W mem) x w v -> ea_q a <= x -> x + Z.of_nat w <= ea_q a + 40 ->
      val_mem SEGS (rdW W (ms_mem ms)) x w v).
    { intros x w v Hv H1 H2 kk Hk.
      rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem (ms_mem ms) (x + Z.of_nat kk)); [exact (Hv kk Hk)|].
      apply KALL. lia. }
    refine (conj (VQ _ _ _ V1 _ _) (conj (VQ _ _ _ V2 _ _) (conj (VQ _ _ _ V3 _ _) (conj (VQ _ _ _ V4 _ _)
      (VQ _ _ _ V5 _ _))))); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  split; [exact (proj1 HOUT)|].
  split; [exact HHp|].
  split; [rewrite <- HAB; unfold ablocks; rewrite blocks_stack_free_state; reflexivity|].
  split.
  { apply (evx_ledger ly S Hp W mem md (ms_mem ms) pos _ _ _ _ _ _ _ HAR Hin); [|exact HLED].
    intros x Hx N1 N2 N3. apply KW; [lia | exact N1 | exact N2 | exact N3]. }
  exact (proj2 HOUT).
Qed.
End f.
End d.
