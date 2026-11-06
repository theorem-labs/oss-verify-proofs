(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths, module names and numbers changed; 892 of its 1130 lines of code are new or changed and 693 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from fuzz_grant's lib/A/Prog/GrantEntrySeat.v (a working branch
   b47e973d564) for libreac/fuzz_boxreg B (fuzz_boxreg.asan-ubsan) over BoxBLxDefs.v: the context is BoxBLxDefs.v's
   lxcx / lx_base / lx_body; the environment is built here from the registers at the seat (the grant context's c_E0
   has no boxreg counterpart); the machine frame's saved words, its spill area, the class-3 side-stack frame
   (512 bytes, flag word at F + 504) and its 64 shadow bytes take boxreg B's numbers; the GOT / shadow-cell regions
   of the prologue are not part of a cut (no phase after the prologue reads them) and were dropped; the landing reads
   the memory facts from the phase's own lemmas (lx_saved_of_ss, lx_shadow_of_ss, lx_word_of_ss) instead of from a
   fixed region shape, and the shent / atom-fact lemmas a token walk needs were added.

   The seat and the landing of a phase of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, stated once for all
   of its phases, at ANY pc of the body (a cut of BoxBLxDefs.v or a phase's own loop head).

   A phase carries its machine state as `lx_body` and its own facts; the walk engine wants a symbolic state
   (`st_ok_pi`). `lx_seat` turns the first into the second, and `lx_land` turns the symbolic state back into
   `lx_body`.

   The environment (`lx_env cx fp regs ex`): atoms 0 .. 31 are the registers at the seat (regs = ms_regs ms3);
   32 is SHADOW_OFF; 33 .. 45 the caller's saved words (33 ra, 34 s0, 35 s1, 36 .. 45 s2 .. s11); 46 the frame F
   on the side stack; 47 its flag word's address; 48 up the phase's own words `ex`; 240 .. 511 the image (Eimg).
   The registers (`lx_sr ov`): sr_atoms with the overrides ov; LX_OV makes s1 the atom of sp (2) and s2 the atom of
   SHADOW_OFF (32), LX_OVP also s5 = F + 64 (prev).
   The regions (`lx_regions`), by index: 0 the saved words (base s0 = sp0, read-only); 1 the spill slots
   sp1 + 0 .. sp1 + 0x97 (base sp, writable); 2 the frame (base 46, writable, flag word chunk at 504); 3 its shadow
   bytes (base s6, window [wlo, whi), which may be empty); then the phase's `extra`. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxSeat.v, with its module paths and module names changed; 286 of its 325 lines of code are new or changed and 1091 lines of the source are left out. *)
(* Case 1 of the switch of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput (op & 3 = 1, the "join" operation of
   fuzz/fuzz_boxreg.c:312-373): the walk from the cut LP_T (0x8034c) to the cut LP_K (0x80b08).

   The cuts inside the case, the model facts and the statement of each segment are in BoxBLxCase1Defs.v; the
   segments are proved in BoxBLxCase1Read.v (read_mac and the width byte), BoxBLxCase1Scan.v (the zero test and
   the scan of prev's rows), BoxBLxCase1Want.v (the width test, the choice of `want` and the inlined lowest_free
   loop) and BoxBLxCase1Tail.v (reac_boxreg_find, reac_boxreg_add and the checks). This file walks the switch
   itself (0x8034c .. 0x80484: `andi a0,s7,3`, the turn number to sp1 + 0x58, the two tests of op & 3 and
   n_before to sp1 + 0x48) and composes the segments into lx_case1. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase1Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBLxCase1Read BoxBLxCase1Scan BoxBLxCase1Want BoxBLxCase1Tail.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The shadow base the engine's token runner works against. *)
Definition C1_SB : Z := 0x7fff8000.
Definition C1_CB : sv := SOff LA_SB 0.
Definition C1_BSPAN : Z * Z := (C1_SB, C1_SB + 2 ^ 44 - 1).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- the switch: LI_T 1 i at 0x8034c -> C1_I1 i at 0x80484 ----
   The seat carries the spill slots the next cut names as chunks (closed numerals as SLit, every value that mentions
   a variable as an atom: the register atoms 20 (r), 27 (fab), 46 (F) and five atoms of its own, 48 .. 52), keeps
   the frame region read-only (fwlo = fwhi = 0) so that frame_of carries prev, and runs 0x8034c .. 0x80484:
   `andi a0,s7,3`, `sd s8,0x58(s1)`, `blt s3,a0` (not taken: s3 = 1 and op & 3 = 1), `sd s10,0x48(s1)`,
   `bnez a0` (taken). No branch of the range reaches a trap or a report. *)
Theorem c1_seg_head : C1_SEG_head B MT.
Proof.
intros HY POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
pose proof (lh_laws B MT HY) as LAWS.
pose proof (lh_tl B MT HY) as TL.
destruct HGI as (pos & r & fab & op & bs & HBODY & Hi64 & Hk & Hacc & HBLK & HREG & HINV & HFAB
  & HPREV & Hposlt & Hopdef & Hop3 & HCUR & HSLL & R19 & R20 & R21 & R23 & R24 & R26 & R27).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG
  & HS10 & HS18 & HS80 & HINP).
pose proof HSLL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
pose proof HCUR as (Hqle & L88 & L90).
assert (RNG : forall off v, lslot cx W3 ms3 off v -> 0 <= v < 2 ^ 64).
{ intros off v Hv. exact (c1_rdword_range (w_H W3) (ms_mem ms3) _ _ Hv). }
pose proof (lx_sp_facts B MT cx HB) as SPF.
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as FF.
pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).

set (ex := [w64 (shadow_addr (r + 280)); w64 (2 ^ 64 - 1 - r); w64 (2 ^ 64 - 1 - (lF cx fp + 64));
            w64 (lc_p cx + Z.of_nat (S pos)); w64 (lc_n cx - Z.of_nat (S pos))]).
set (E := lx_env cx fp (ms_regs ms3) ex).
assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 ex); exact HREGS).
assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
assert (ER : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr (ms_regs ms3) rr)
  by (intros n rr Hn; apply lx_env_reg; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E (48 + j) = nth j ex (w64 0))
  by (intros j Hj; apply (lx_env_ex cx fp (ms_regs ms3) ex j); lia).
pose proof HE as (EA2 & EA8 & EA3 & EA4 & EA22 & EA32 & EASV & EA46 & EA47).
pose proof (RNG _ _ L70) as Rr. pose proof (RNG _ _ L28) as Rr28. pose proof (RNG _ _ L30) as Rfab.
pose proof (RNG _ _ L68) as RF32. pose proof (RNG _ _ L40) as Rsh. pose proof (RNG _ _ L78) as RF78.
pose proof (RNG _ _ L88) as Rp. pose proof (RNG _ _ L90) as Rn.

set (SL := [(0x08, SLit 3); (0x10, SOff 46 0); (0x18, SOff 46 0); (0x28, SOff 20 280); (0x30, SOff 27 0);
            (0x38, SLit 0); (0x40, SOff 48 0); (0x68, SOff 46 32); (0x70, SOff 49 0); (0x78, SOff 50 0);
            (0x80, SOff 46 0); (0x88, SOff 51 0); (0x90, SOff 52 0)] : list (Z * sv)).
assert (HSL : lx_slots cx W3 ms3 E SL).
{ unfold lx_slots, SL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - exact (lx_slot_lit cx W3 ms3 E _ _ L08 (RNG _ _ L08)).
  - apply (lx_slot_atom cx W3 ms3 E 0x10 46 (lF cx fp) 0); [rewrite Z.add_0_r; exact HS10 | exact EA46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x18 46 (lF cx fp) 0); [rewrite Z.add_0_r; exact HS18 | exact EA46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x28 20 r 280 L28); [rewrite (ER 20%nat (Z_to_bv 5 20)); [exact R20 | vm_compute; reflexivity] | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x30 27 fab 0); [rewrite Z.add_0_r; exact L30 | rewrite (ER 27%nat (Z_to_bv 5 27)); [exact R27 | vm_compute; reflexivity] | lia | lia].
  - exact (lx_slot_lit cx W3 ms3 E _ _ L38 (RNG _ _ L38)).
  - apply (lx_slot_atom cx W3 ms3 E 0x40 48 (shadow_addr (r + 280)) 0); [rewrite Z.add_0_r; exact L40 | exact (EX 0%nat ltac:(lia)) | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x68 46 (lF cx fp) 32 L68); [exact EA46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x70 49 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact L70 | exact (EX 1%nat ltac:(lia)) | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x78 50 (2 ^ 64 - 1 - (lF cx fp + 64)) 0); [rewrite Z.add_0_r; exact L78 | exact (EX 2%nat ltac:(lia)) | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x80 46 (lF cx fp) 0); [rewrite Z.add_0_r; exact HS80 | exact EA46 | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x88 51 (lc_p cx + Z.of_nat (S pos)) 0); [rewrite Z.add_0_r; exact L88 | exact (EX 3%nat ltac:(lia)) | lia | lia].
  - apply (lx_slot_atom cx W3 ms3 E 0x90 52 (lc_n cx - Z.of_nat (S pos)) 0); [rewrite Z.add_0_r; exact L90 | exact (EX 4%nat ltac:(lia)) | lia | lia]. }

assert (HS : st_ok_pi SEGS VAL E
  (lx_ss LP_T (lx_sr LX_OV) LSH_iter (lx_slot_chunks SL) [] 0 0 0 0 [] (mkFacts LX_AF [] [])) (restrict (w_H W3) ms3)).
{ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR).
  - exact HE.
  - exact HBODY.
  - apply lx_regs_ok; [apply lx_regs_ok_atoms | apply (lx_ov_ok cx fp ms3 ex); exact HREGS].
  - exact HSL.
  - apply Forall_nil.
  - lia.
  - lia.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - repeat apply Forall_cons; try apply Forall_nil; exact I.
  - split; [exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE) | split; exact I]. }
assert (SHOK : sh_ok SEGS C1_CB [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_branch (PI := PI)) as BR.

assert (EFA : frame_addr ly3 LX_CID fp = lF cx fp)
  by exact (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ).

assert (EW2 : ew E 2 = w64 (lsp1 cx)) by exact EA2.
assert (EW46 : ew E 46 = w64 (lF cx fp)) by exact EA46.
paj_run_tok RUN HS HJ SHOK C1_BSPAN.
{ cbn [ss_mem add_cond lx_ss lx_regions lx_regions0].
  apply awr_ok_cons_ro; [cbn [lx_saved_region r_wlo r_whi]; lia|].
  eapply (awr_ok_cons_stack_off E _ _ LX_STK (lsp0 cx) [] (ablocks B (lc_ly cx) (lc_S cx))
            (ablocks B ly3 S3) ly3 [(LX_CID, fp)] 2%nat (lsp1 cx - lsp0 cx)).
  - cbn [lx_spill_region r_base]. reflexivity.
  - rewrite EW2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - cbn [lx_spill_region r_wlo]. unfold LX_STK. lia.
  - cbn [lx_spill_region r_whi]. unfold LX_SPILL. lia.
  - apply awr_ok_cons_ro; [cbn [lx_frame_region r_wlo r_whi]; lia|].
    apply awr_ok_cons_ro; [cbn [lx_shadow_region fshadow_region r_wlo r_whi]; lia|]. apply awr_ok_nil. }

assert (Hoprng : 0 <= op < 256).
{ rewrite Hopdef. pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as Rb.
  change (bv_modulus 8) with 256 in Rb. exact Rb. }
assert (EW23 : ew E 23 = w64 op).
{ rewrite (ER 23%nat (Z_to_bv 5 23)); [exact R23 | vm_compute; reflexivity]. }
assert (EW19 : ew E 19 = w64 1).
{ rewrite (ER 19%nat (Z_to_bv 5 19)); [exact R19 | vm_compute; reflexivity]. }
assert (DEN : forall (x : sv) (v : Z), U E x = v -> sv_denot E x = Z_to_bv 64 v).
{ intros x v Hx. rewrite <- Hx. unfold U. symmetry. apply Z_to_bv_bv_unsigned. }
assert (U23 : U E (SOff 23 0) = op).
{ apply (U_atom E 23 op EW23). lia. }
assert (U19 : U E (SOff 19 0) = 1).
{ apply (U_atom E 19 1 EW19). lia. }
assert (UAND : U E (SAlu ALU_AND (SOff 23 0) (SLit 3)) = 1).
{ rewrite U_and_lit by lia. rewrite U23. exact Hop3. }

psrr_branch_tok RUN BR HS SHOK C1_BSPAN.
- exfalso. rewrite (DEN _ _ U19), (DEN _ _ UAND) in Hc. cbn [branch_taken] in Hc.
  rewrite bv_lts_small in Hc by lia. discriminate.
- clear Hc. paj_run_tok RUN HS HJ SHOK C1_BSPAN.
{ cbn [ss_mem add_cond lx_ss lx_regions lx_regions0].
  apply awr_ok_cons_ro; [cbn [lx_saved_region r_wlo r_whi]; lia|].
  eapply (awr_ok_cons_stack_off E _ _ LX_STK (lsp0 cx) [] (ablocks B (lc_ly cx) (lc_S cx))
            (ablocks B ly3 S3) ly3 [(LX_CID, fp)] 2%nat (lsp1 cx - lsp0 cx)).
  - cbn [lx_spill_region r_base]. reflexivity.
  - rewrite EW2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - cbn [lx_spill_region r_wlo]. unfold LX_STK. lia.
  - cbn [lx_spill_region r_whi]. unfold LX_SPILL. lia.
  - apply awr_ok_cons_ro; [cbn [lx_frame_region r_wlo r_whi]; lia|].
    apply awr_ok_cons_ro; [cbn [lx_shadow_region fshadow_region r_wlo r_whi]; lia|]. apply awr_ok_nil. }

psrr_branch_tok RUN BR HS SHOK C1_BSPAN.
2: { exfalso. rewrite branch_ne_U, UAND, (U_lit E 0 ltac:(lia)) in Hc. cbn in Hc. discriminate. }
clear Hc.
pose proof (paj_run_to B LAWS) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK C1_BSPAN C1_P1.
{ cbn [ss_mem add_cond lx_ss lx_regions lx_regions0].
  apply awr_ok_cons_ro; [cbn [lx_saved_region r_wlo r_whi]; lia|].
  eapply (awr_ok_cons_stack_off E _ _ LX_STK (lsp0 cx) [] (ablocks B (lc_ly cx) (lc_S cx))
            (ablocks B ly3 S3) ly3 [(LX_CID, fp)] 2%nat (lsp1 cx - lsp0 cx)).
  - cbn [lx_spill_region r_base]. reflexivity.
  - rewrite EW2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - cbn [lx_spill_region r_wlo]. unfold LX_STK. lia.
  - cbn [lx_spill_region r_whi]. unfold LX_SPILL. lia.
  - apply awr_ok_cons_ro; [cbn [lx_frame_region r_wlo r_whi]; lia|].
    apply awr_ok_cons_ro; [cbn [lx_shadow_region fshadow_region r_wlo r_whi]; lia|]. apply awr_ok_nil. }

assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx <= a < lsp1 cx + LX_SPILL) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hw.
  assert (RW : forall (rs : smem),
      Forall (fun rr => r_whi rr <= r_wlo rr \/
                        (r_base rr = Some 2%nat /\ 0 <= r_wlo rr /\ r_whi rr <= LX_SPILL)) rs ->
      forall (m m' : word -> option byte), frame_of E rs m m' ->
      aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a).
  { intros rs HFa m m' HFo. apply (aview_eq_of SEGS (w_H W3)).
    unfold mrestrict. rewrite (HFo (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by lia. intros (rr & Hin & Hr).
    rewrite Forall_forall in HFa. destruct (HFa rr Hin) as [Hro | (Hb & Hlo & Hhi)]; [lia|].
    rewrite Hb in Hr. cbn [base_val] in Hr. rewrite EW2 in Hr. unfold w64 in Hr.
    rewrite unsigned_lit_small in Hr by lia. unfold LX_SPILL in Hw, Hhi. lia. }
  transitivity (aview SEGS (w_H W3) (ms_mem ms0) a).
  { refine (RW _ _ _ _ HF1). cbn [ss_mem add_cond lx_ss lx_regions lx_regions0]; repeat apply Forall_cons; try apply Forall_nil; cbn [lx_saved_region lx_spill_region lx_frame_region lx_shadow_region fshadow_region r_base r_wlo r_whi]; first [left; lia | right; split; [reflexivity | unfold LX_SPILL; lia]]. }
  transitivity (aview SEGS (w_H W3) (ms_mem ms) a).
  { refine (RW _ _ _ _ HF0). cbn [ss_mem add_cond lx_ss lx_regions lx_regions0]; repeat apply Forall_cons; try apply Forall_nil; cbn [lx_saved_region lx_spill_region lx_frame_region lx_shadow_region fshadow_region r_base r_wlo r_whi]; first [left; lia | right; split; [reflexivity | unfold LX_SPILL; lia]]. }
  refine (RW _ _ _ _ HF). cbn [ss_mem add_cond lx_ss lx_regions lx_regions0]; repeat apply Forall_cons; try apply Forall_nil; cbn [lx_saved_region lx_spill_region lx_frame_region lx_shadow_region fshadow_region r_base r_wlo r_whi]; first [left; lia | right; split; [reflexivity | unfold LX_SPILL; lia]]. }

assert (GEOC : alloc_ceiling <= lsp1 cx) by lia.
pose proof HJ as (HAR3 & _).
assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (HinR : In (r, LX_REG) (ablocks B ly3 S3))
  by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).

pose proof SPF as (SPal & SPlo & SPhi & SPr & SPal32).
pose proof FF as (FFlo & FFhi & FFapp & FFimg & FFal & FFsh).

destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 HinR) as (_ & Hr4096 & Hrc & _).
change (req_size LX_REG) with 288 in Hrc.
assert (HinP : 0 < lc_n cx -> In (lc_p cx, lc_n cx) (ablocks B ly3 S3)).
{ intros Hn. pose proof HB as (_ & _ & _ & Hpn & _).
  destruct Hpn as [Hn0 | (_ & Hinc)]; [lia|]. unfold lblk in HBLK; rewrite HBLK; apply in_or_app; left; exact Hinc. }
assert (HpC : 0 < lc_n cx -> 4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling).
{ intros Hn. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 (HinP Hn)) as (_ & Hplo & Hpcc & _).
  assert (Hrq : req_size (lc_n cx) = lc_n cx) by (unfold req_size; destruct (Z.eqb_spec (lc_n cx) 0); lia).
  rewrite Hrq in Hpcc. split; [exact Hplo | exact Hpcc]. }

lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
  assert (HBD : lx_body cx fp C1_P1 W3 msX LSH_iter) end.
{ eapply (lx_land cx fp W3 _ E C1_P1 _ LSH_iter);
  [ exact HE | exact HS | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | .. ].
  - eapply (lx_saved_of_ss B MT cx fp W3 _ HB E _ HE HS). vm_compute. reflexivity.
  - eapply (lx_shadow_of_ss B MT LAWS cx fp W3 _ ly3 S3 _ k HB HJ HFR E _ _ _ _ _ _ LSH_iter HE HS);
    [ reflexivity | vm_compute; reflexivity ].
  - eapply (lx_flag_of_ss B MT LAWS cx fp W3 _ ly3 S3 _ k HB HJ HFR E _ _ _ _ _ _ HE HS);
    [ reflexivity | cbn [r_chunks app In]; tauto ].
  - eapply (lx_slot_of_ss B MT cx fp W3 _ HB E _ _ _ _ _ _ 16 (SOff 46 0) (lF cx fp) HE HS);
    [ reflexivity | cbn [r_chunks app In]; tauto | rewrite lx_sv_SOff0; exact EA46 | lia ].
  - eapply (lx_slot_of_ss B MT cx fp W3 _ HB E _ _ _ _ _ _ 24 (SOff 46 0) (lF cx fp) HE HS);
    [ reflexivity | cbn [r_chunks app In]; tauto | rewrite lx_sv_SOff0; exact EA46 | lia ].
  - eapply (lx_slot_of_ss B MT cx fp W3 _ HB E _ _ _ _ _ _ 128 (SOff 46 0) (lF cx fp) HE HS);
    [ reflexivity | cbn [r_chunks app In]; tauto | rewrite lx_sv_SOff0; exact EA46 | lia ].
  - assert (HPIN : forall x, lc_p cx <= x < lc_p cx + Z.of_nat (length (lc_pl cx)) ->
      0 <= x < 2 ^ 64 /\ ~ (lsp1 cx <= x < lsp1 cx + LX_SPILL)).
    { intros x Hx. assert (Hnp : 0 < lc_n cx) by (unfold lc_n; lia).
      destruct (HpC Hnp) as (Hplo2 & Hpc2). unfold lc_n in Hpc2.
      clear - Hx Hpc2 Hplo2 SPlo SPr C1a. unfold LX_SPILL. split; lia. }
    intros j Hj. pose proof Hj as Hj2. rewrite length_map in Hj2.
    destruct (HINP j Hj) as [Hv Hb]. split; [|exact Hb].
    intros kq Hkq. assert (Hk0 : kq = 0%nat) by lia. subst kq.
    destruct (HPIN (lc_p cx + Z.of_nat j + Z.of_nat 0) ltac:(cbn [Z.of_nat]; lia)) as [Hx1 Hx2].
    rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms1) _ (KEEP _ Hx1 Hx2)).
    apply Hv. lia. }

assert (EW20 : ew E 20 = w64 r) by (rewrite (ER 20%nat (Z_to_bv 5 20)); [exact R20 | vm_compute; reflexivity]).
assert (EW21 : ew E 21 = w64 (lF cx fp + 64)) by (rewrite (ER 21%nat (Z_to_bv 5 21)); [exact R21 | vm_compute; reflexivity]).
assert (EW24 : ew E 24 = w64 (Z.of_nat i)) by (rewrite (ER 24%nat (Z_to_bv 5 24)); [exact R24 | vm_compute; reflexivity]).
assert (EW26 : ew E 26 = w64 (Boxreg.bx_n bs)) by (rewrite (ER 26%nat (Z_to_bv 5 26)); [exact R26 | vm_compute; reflexivity]).
assert (EW27 : ew E 27 = w64 fab) by (rewrite (ER 27%nat (Z_to_bv 5 27)); [exact R27 | vm_compute; reflexivity]).
assert (EW48 : ew E 48 = w64 (shadow_addr (r + 280))) by exact (EX 0%nat ltac:(lia)).
assert (EW49 : ew E 49 = w64 (2 ^ 64 - 1 - r)) by exact (EX 1%nat ltac:(lia)).
assert (EW50 : ew E 50 = w64 (2 ^ 64 - 1 - (lF cx fp + 64))) by exact (EX 2%nat ltac:(lia)).
assert (EW51 : ew E 51 = w64 (lc_p cx + Z.of_nat (S pos))) by exact (EX 3%nat ltac:(lia)).
assert (EW52 : ew E 52 = w64 (lc_n cx - Z.of_nat (S pos))) by exact (EX 4%nat ltac:(lia)).
assert (Hn5 : 0 <= Boxreg.bx_n bs <= 5) by (destruct HINV as ((_ & HBB1 & _) & _); exact HBB1).
(* the registry block and prev lie below the realigned stack pointer, so the two stores left them alone *)
assert (KREG : lreg W3 ms1 r bs).
{ intros j Hj. unfold lview. rewrite (KEEP (r + j) ltac:(unfold LX_REG in Hj; unfold LX_SPILL; lia)
    ltac:(unfold LX_REG in Hj; unfold LX_SPILL; lia)). exact (HREG j Hj). }
assert (KPREV : lprev cx fp W3 ms1 bs).
{ intros j Hj. unfold lview. rewrite (KEEP (lF cx fp + 64 + j) ltac:(unfold LX_REG in Hj; unfold LX_SPILL; lia)
    ltac:(unfold LX_REG in Hj; unfold LX_SPILL; lia)). exact (HPREV j Hj). }

assert (DOFF0 : forall n b, ew E n = w64 b -> sv_denot E (SOff n 0) = w64 b)
  by (intros n b Hn; rewrite lx_sv_SOff0; exact Hn).
assert (DOFF : forall n b c, ew E n = w64 b -> 0 <= b < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (b + c))
  by (intros n b c Hn Hb; cbn [sv_denot]; rewrite Hn; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (S08 : lslot cx W3 ms1 8 3).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 8 (SLit 3) _ HE HS);
  [ reflexivity | cbn [In]; tauto | reflexivity | lia ]. }
assert (S28 : lslot cx W3 ms1 40 (r + 280)).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 40 (SOff 20 280) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF 20%nat r 280 EW20 ltac:(lia)) | exact Rr28 ]. }
assert (S30 : lslot cx W3 ms1 48 fab).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 48 (SOff 27 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF0 27%nat _ EW27) | exact Rfab ]. }
assert (S38 : lslot cx W3 ms1 56 0).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 56 (SLit 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | reflexivity | lia ]. }
assert (S40 : lslot cx W3 ms1 64 (shadow_addr (r + 280))).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 64 (SOff 48 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF0 48%nat _ EW48) | exact Rsh ]. }
assert (S68 : lslot cx W3 ms1 104 (lF cx fp + 32)).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 104 (SOff 46 32) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF 46%nat (lF cx fp) 32 EW46 ltac:(lia)) | exact RF32 ]. }
assert (S70 : lslot cx W3 ms1 112 (2 ^ 64 - 1 - r)).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 112 (SOff 49 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF0 49%nat _ EW49) | exact Rr ]. }
assert (S78 : lslot cx W3 ms1 120 (2 ^ 64 - 1 - (lF cx fp + 64))).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 120 (SOff 50 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF0 50%nat _ EW50) | exact RF78 ]. }
assert (S88 : lslot cx W3 ms1 136 (lc_p cx + Z.of_nat (S pos))).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 136 (SOff 51 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF0 51%nat _ EW51) | exact Rp ]. }
assert (S90 : lslot cx W3 ms1 144 (lc_n cx - Z.of_nat (S pos))).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 144 (SOff 52 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF0 52%nat _ EW52) | exact Rn ]. }
assert (S58 : lslot cx W3 ms1 88 (Z.of_nat i)).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 88 (SOff 24 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF0 24%nat _ EW24) | lia ]. }
assert (S48 : lslot cx W3 ms1 72 (Boxreg.bx_n bs)).
{ eapply (lx_slot_of_ss B MT cx fp W3 ms1 HB E _ _ _ _ _ _ 72 (SOff 26 0) _ HE HS);
  [ reflexivity | cbn [In]; tauto | exact (DOFF0 26%nat _ EW26) | lia ]. }

prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
  apply (HNEXT cx fp k acc ly3 S3 W3 msX mdX); [exact HB | exact HJ | exact HFR | exact HMO | ] end.
exists (S pos), r, fab, op, bs.
split.
{ split; [exact HBD|]. split; [exact Hi64|]. split; [exact Hk|]. split; [exact Hacc|].
  split; [exact HBLK|]. split; [exact KREG|]. split; [exact HINV|]. split; [exact HFAB|].
  split; [exact KPREV|].
  split; [split; [exact Hqle | split; [exact S88 | exact S90]]|].
  split; [split; [exact S08|]; split; [exact S28|]; split; [exact S30|]; split; [exact S38|];
          split; [exact S40|]; split; [exact S68|]; split; [exact S70 | exact S78]|].
  split; [exact S58|]. split; [exact S48|].
  split; [rewrite Q20; exact EW20 | rewrite Q21; exact EW21]. }
split; [lia|]. split; [exact Hop3|]. split; [exact Hqle|].
split; [rewrite Q19; exact EW19|]. split; [rewrite Q23; exact EW23|]. split; [rewrite Q24; exact EW24|].
split; [rewrite Q26; exact EW26 | rewrite Q27; exact EW27].
Qed.

(* ---- the phase: the eight segments composed ----
   LI_T 1 i -(head)-> C1_I1 -(read)-> C1_I2 -(zero)-> C1_I3 -(scan0)-> C1_I4 / C1_I5, C1_I4 -(scan)-> C1_I5
   (the scan of prev's rows, by induction on the rows left), C1_I5 -(want)-> C1_I6 / C1_I7,
   C1_I6 -(lf)-> C1_I7 (the inlined lowest_free loop, by induction on the bases left), C1_I7 -(tail)-> LI_K i. *)
Hypothesis HY : lx_hyps B MT.

Theorem lx_case1 : forall POST i,
  lx_from B MT POST (LI_K B MT i) -> lx_from B MT POST (LI_T B MT 1 i).
Proof.
intros POST i HK.
assert (I7 : lx_from B MT POST (C1_I7 B MT i)) by exact (c1_seg_tail B MT HY POST i HK).
assert (I6 : lx_from B MT POST (C1_I6 B MT i)) by exact (c1_seg_lf B MT HY POST i I7).
assert (I5 : lx_from B MT POST (C1_I5 B MT i)) by exact (c1_seg_want B MT HY POST i I6 I7).
assert (I4 : lx_from B MT POST (C1_I4 B MT i)) by exact (c1_seg_scan B MT HY POST i I5).
assert (I3 : lx_from B MT POST (C1_I3 B MT i)) by exact (c1_seg_scan0 B MT HY POST i I4 I5).
assert (I2 : lx_from B MT POST (C1_I2 B MT i)) by exact (c1_seg_zero B MT HY POST i I3).
assert (I1 : lx_from B MT POST (C1_I1 B MT i)) by exact (c1_seg_read B MT HY POST i I2).
exact (c1_seg_head HY POST i I1).
Qed.

End c.
End b.
End a.
