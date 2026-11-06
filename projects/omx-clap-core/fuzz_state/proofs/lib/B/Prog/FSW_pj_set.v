(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fs.asan-ubsan, UBSan trap mode) walk of grow against
   lib/B/FSH_Fn_reader.v grow_spec (:575, CTX-free; the text of S0 a working branch f32db4da382 = a working branch adfa7850046 on this branch): the STAGES.
   rule 24 (lane brief (internal path), CONFIRM a Theorem Labs lane): proves function
   grow - fuzz_state image B asan-ubsan, entry 0x83ca8, success form. Reuse search, the three
   result lines:
     proof-index grow (exit 0): grow: 16 named, 69 by address, 19 related, 246 lemma(s), an earlier delivery 311 named and 9928
       name(s) holding it
     proof-index grow_spec (exit 0): grow_spec: 0 named, 0 by address, 0 related, 17 lemma(s), 0 by file name, an earlier delivery
       9 named and 48 name(s) holding it
     proof-index 0x83ca8 (exit 4): 0x83ca8: 0 named, 0 by address, 0 related, 0 lemma(s), 0 by file name, an earlier delivery 0
       named and 0 name(s) holding it, 108 unreleased
   Port source (Lookup result): ported from a working branch 75e39a1f41d:
   proofs/omx-clap-core/fuzz_state/lib/B/Prog/grow.v (blob bf8e2804f8dd, 3835 lines, 35 Qed, no admit; grow_holds :
   fuzz_realloc_contract ... -> grow_contract ... CAP, matching rdn1b's grow_c.v a8d1dc75b495): its walk is restated
   against grow_spec's frame (fpreU / fpostU / SRr over W, rd_sum Dold0 <= live, quiet, no CTX) lemma by lemma; NOT
   Required, NOT bridged. The old walk runs on the old lib/Lib engine (zstep over concrete cells), the new frame on the
   symbolic engine of the lib/B FSW kit, so what is ported is its CONTENT: the instruction-level case split (gr_entry_seg
   / gr_lt_seg / gr_a_seg / gr_ret_seg and the realloc arms), the UBSan guard refutations (gr_entry_seg's HV0 v <> 0 and
   HA8 Z.land v 7 = 0; here the symbolic engine decides both from v's fact), the shadow walk (gr_sh = SHADOW_OFF + x / 8 cells, here FSW_grow_shcell's regions and the
   token run's checks), the size arithmetic (gr_cap2 / gr_sz: cap2 cap, 8 * cap2 cap, 56 * cap2 cap), and the frame
   (gr_frame: 96 bytes, ra s0 .. s9 at sp + 0x58 .. sp + 8). The NEW-frame shape is the image-A walk of the same C:
   a working branch 728177ca53c lib/A/Prog/FSW_grow.v (a Theorem Labs lane's final; its stages equal 582c4d69613's and
   the draft a working branch f9ccbd8f565's: grow_stageA / grow_stageB / grow_stageC, grow_FP, grow_post),
   copied here and re-measured for B's code. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_grow.v, with its module paths, module names, addresses and numbers changed; 480 of its 572 lines of code are new or changed and 551 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) walk of pj_set, the twin of lib/A/Prog/FSW_pj_set.v
   (a working branch f9ccbd8f565 = a working branch 6fcf9aa5a9b, blob d5f54d63a6): stages
   A, B, C, E and F are A's, relocated (B's code is A's + 0x1f4 up to stage C, and stages E / F are the same words at the
   same relocation); every address is READ from image B (fuzz_state.asan-ubsan, the unstripped twin's disassembly of
   [0x83adc, 0x83ca8)), never carried from A. Stage D is new: B's code there is not A's (ten UBSan checks to the trap
   `unimp` 0x83c84, the n store before the kids checks); its UBSan guard arguments are ported from
   a working branch 955803f9b2e lib/B/Prog/pj_set_store.v (the same code under the old contract pj_set_c). *)
(* The ASan + UBSan walk of pj_set (fs.asan-ubsan 0x83adc, pf.c:373-391) against lib/B/FSH_Fn_reader.pj_set_spec: STAGES.
   rule 24: pj_set proved new on image B (a Theorem Labs lane's lookup, CONFIRM 05:5xZ: no released proof of pj_set on any ASan image;
   0x83adc is named by no file). The released PLAIN walk (lib/Prog/pj_set_c.v) is the control-flow template; the A walk
   (lib/A/Prog/FSW_pj_set.v) is the structure.

   PROVED STAGES (CPS lemmas, the spec's key-absent success path, every allocation granted):
     pj_set_stageA  entry 0x83adc (FSW_K.fsw_entryT) .. entering pj_get (obj, key) from 0x83b14.
     pj_set_stageB  resume at 0x83b18, a0 = 0 (key absent) .. entering grow (obj) from 0x83b50.
     pj_set_stageC  resume at 0x83b54, a0 = 0 (granted) .. entering fuzz_strdup (key) from 0x83b88.
     pj_set_stageD  resume at 0x83b8c .. entering __asan_memcpy (kids + 56 n, val, 56) from 0x83b30 (via j 0x83b2c).
     pj_set_stageE  resume at 0x83b34 .. entering __asan_memset (val, 0, 56) from 0x83b40.
     pj_set_stageF  resume at 0x83b44 .. the ret 0x83b80, a0 = 0, every callee-saved register restored.
   The resume states are FSW_ret's fss_retT, the state FSW_K3's fsw_after_callFPU_args (program calls) and FSW_rres's
   fsw_resume_after_rtU_args (runtime calls) give. No __asan_report_* and no UBSan trap is reached.
   Named premise: FsShadowSyms B (lib/B/FSH_Base.v: the .got word 0x9fc10 and the cell 0xa8438 of image B; the auipc at
   0x83b00 reads 0x83b00 + 0x1c000 + 0x110 = 0x9fc10), the shadow-base cells (stage A).
   SINK: each Section binds the sink head explicitly, (SK : YI16.sink_head), and every statement passes it with @
   (@ajournal rc SK ...), so no sink argument is left to instance resolution (owner rule, a Theorem Labs lane 06:50Z; MEASURED
   before the change with Set Printing All: every ajournal in the six statements already took the Section's SK). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_pj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_pj_set_tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the frame pj_set's prologue writes (0x83ae0-0x83af4): ra, s0 .. s4 at entry sp - 8 .. entry sp - 48 *)
Definition pj_set_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv)].
Definition pj_set_frame (m : word -> option byte) (sp : Z) (regs0 : bvmap 5 word) : Prop :=
  Forall (fun p => val_mem tfibsegs m (sp + fst p) 8 (bv_unsigned (YK11.getr regs0 (snd p)))) pj_set_saved.

(* what stage A establishes at the call of pj_get (obj, key) 0x83b14: the argument registers, the registers the walk
   reads after the call (s0 = val, s1 = obj, s2 = key, s4 = the shadow base), the untouched callee-saved ones, the frame *)
Definition pj_set_call_get (W : world tfibsegs) (regs regsC : bvmap 5 word) (memC : word -> option byte)
  (o k w : Z) : Prop :=
  YK11.getr regsC 1 = w64 0x83b18 /\ spZ regsC = spZ regs - 48 /\
  YK11.getr regsC 10 = w64 o /\ YK11.getr regsC 11 = w64 k /\
  YK11.getr regsC 8 = w64 w /\ YK11.getr regsC 9 = w64 o /\ YK11.getr regsC 18 = w64 k /\
  YK11.getr regsC 20 = w64 SHADOW_OFF /\
  Forall (fun r => YK11.getr regsC r = YK11.getr regs r) [3; 4; 19; 21; 22; 23; 24; 25; 26; 27]%bv /\
  pj_set_frame (mrestrict (w_H W) memC) (spZ regs) regs.

(* a register of the stopped run, as the symbolic state says: getr (ms_regs ms) r is the denotation of the run's sv for r *)
Ltac gw_reg HS r :=
  rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ r HS);
  lazymatch goal with |- sv_denot _ (sr_get ?l ?q) = _ =>
    let e := eval vm_compute in (sr_get l q) in change (sr_get l q) with e end.
(* ... equal to w64 X: by its unsigned value *)
Ltac gw_val :=
  apply bv_eq; unfold w64; rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia);
  lazymatch goal with |- bv_unsigned (sv_denot ?E ?e) = _ => change (bv_unsigned (sv_denot E e)) with (YP0e.U E e) end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
(* the shadow-base cells of B (FSH_Base.FsShadowSyms, S0 5478e5af284), the one named premise of fs's instrumented walks;
   TfibLib B (A/ACeg.v) discharges it once A/ACej.v builds *)
Hypothesis HSS : FsShadowSyms B.

Lemma pj_set_stageA : forall ly S U (W : world tfibsegs) regs mem md ch (FP : list (Z * Z)) o k w
  (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_pj_set ly S U W regs mem md ch ->
  YK11.getr regs 10 = w64 o -> YK11.getr regs 11 = w64 k -> YK11.getr regs 12 = w64 w ->
  0 <= o < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  (forall regsC memC mat,
     pj_set_call_get W regs regsC memC o k w ->
     @ajournal rc SK tfibsegs B STK_pj_set (spZ regs) FP ly S W (unpoison U mem) md [] ly S W (unpoison U memC)
       (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W memC (with_vm_backing (m_vm_lazy md) mat md) ->
     same_below mem memC alloc_ceiling ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_get regsC memC (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (YG0d.cfg_at tfibsegs A_pj_set regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP o k w Q HPRE H10 H11 H12 Ho Hk Hw KGET.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof HPRE as (HAP & HUOK & HUP).
assert (FS : STK_pj_set = ltac:(let x := eval vm_compute in STK_pj_set in exact x)) by reflexivity.
pose proof (fsw_entryT B STK_pj_set 48 ly S U W regs mem md ch A_pj_set (proj1 HSS) (proj2 HSS) HPRE
  ltac:(rewrite FS; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := Ereg regs fs_extraT) in HS.
assert (ER : forall r : bv 5, (Z.to_nat (bv_unsigned r) < 32)%nat -> ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regs r)
  by (intros r _; subst E; apply ew_Ereg_reg).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U32 : YP0e.U E (SOff 32 0) = SHADOW_OFF).
{ rewrite U_SOff. subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT].
  rewrite Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia). apply zcanon_small. unfold SHADOW_OFF; lia. }
assert (UR : forall (r : bv 5) z, YK11.getr regs r = w64 z -> 0 <= z < 2 ^ 64 -> YP0e.U E (SOff (Z.to_nat (bv_unsigned r)) 0) = z).
{ intros r z Hr Hz. apply U_atom; [|exact Hz]. rewrite ER by (pose proof (u5_range r); lia). exact Hr. }
unfold YG0d.cfg_at. change (w64 A_pj_set) with (Z_to_bv 64 A_pj_set).
pose proof (ajournal_init (rc := rc) (SK := SK) tfibsegs B STK_pj_set FP ly S W regs (unpoison U mem) md ch HAP) as HJ.
pose proof (fsw_ARU B STK_pj_set ly S U W regs mem md ch HPRE) as HARU.
change mem with (ms_mem (mkst regs (Z_to_bv 64 A_pj_set) mem (seg_rom tfibsegs))) in HJ at 2, HARU.
(* ---- 0x83adc .. 0x83b14: prologue, shadow base, argument moves, jal pj_get ---- *)
fsw_aj_run_toU pj_set_tbl_ok HS HJ HARU A_pj_get.
{ awr_ok_tac. exact E2. }
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ intros x Hx. apply HF. intros (r & Hin & Hr). cbn [fss0T fsT_regions ss_mem In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [unfold fstk, fs_got_region, fs_bcell_region in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; try lia|]); [|destruct Hin].
  rewrite E2, unsigned_lit_small in Hr by lia. lia. }
pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl).
apply (KGET (ms_regs ms) (ms_mem ms) mat); [| exact HJ | exact HARU | exact SB1].
unfold pj_set_call_get.
split; [gw_reg HS (1%bv : bv 5); gw_val; apply U_lit; lia|].
split; [unfold spZ at 1; rewrite (fsw_reg_off _ _ _ ms 2%bv 2 (-48) (spZ regs) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)); lia|].
split; [gw_reg HS (10%bv : bv 5); gw_val; exact (UR 10%bv o H10 Ho)|].
split; [gw_reg HS (11%bv : bv 5); gw_val; exact (UR 11%bv k H11 Hk)|].
split; [gw_reg HS (8%bv : bv 5); gw_val; exact (UR 12%bv w H12 Hw)|].
split; [gw_reg HS (9%bv : bv 5); gw_val; exact (UR 10%bv o H10 Ho)|].
split; [gw_reg HS (18%bv : bv 5); gw_val; exact (UR 11%bv k H11 Hk)|].
split; [gw_reg HS (20%bv : bv 5); gw_val; exact U32|].
split.
{ repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ => gw_reg HS r; rewrite fsw_SOff0; exact (ER r ltac:(vm_compute; lia)) end|]). apply Forall_nil. }
unfold pj_set_frame, pj_set_saved.
repeat (apply Forall_cons; [cbn [fst snd];
  lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (YK11.getr regs ?r)) =>
    apply (fsw_field _ _ 2 _ _ _ _ _ _ o 8%N (SOff (Z.to_nat (bv_unsigned r)) 0) _ HR0 E2 ltac:(cbn; tauto));
    [rewrite fsw_SOff0, ER by (vm_compute; lia); symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia] end|]).
apply Forall_nil.
Qed.
End W.

(* ================= the resume stages: after a call, pj_set resumes in FSW_ret's fss_retT (the state FSW_K3's
   fsw_after_callFPU_args gives after a program call, and FSW_rres's fsw_resume_after_rtU_args after a runtime call), with
   frame 48 and the saved ra, s0 .. s4 as chunks. Extra atoms by FSW_K's convention: the alloc.c statics xatom 0..3,
   obj's fields in FSW_pj.pj_fields order xatom 4..8 (ty kids keys n cap = atoms 37..41, read in stage D), the saved
   registers xatom 9 .. 14 (atoms 42..47). ================= *)
Definition pj_set_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20]%bv.
Definition pj_xs (cnt fail live peak ty kids keys n cap : Z) (regs : bvmap 5 word) : list word :=
  map (Z_to_bv 64) [cnt; fail; live; peak] ++ pj_fields ty kids keys n cap ++ map (YK11.getr regs) pj_set_saved_regs.
Definition pS_cs : list YP09.chunk :=
  [YP09.mkChunk 40 (CVal 8 (SOff (xatom 9) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 10) 0));
   YP09.mkChunk 24 (CVal 8 (SOff (xatom 11) 0)); YP09.mkChunk 16 (CVal 8 (SOff (xatom 12) 0));
   YP09.mkChunk 8 (CVal 8 (SOff (xatom 13) 0)); YP09.mkChunk 0 (CVal 8 (SOff (xatom 14) 0))].
Definition ss_pB0 : sstate := Eval vm_compute in fss_retT 0x83b18 48 pS_cs [] [].
Definition ss_pC0 : sstate := Eval vm_compute in fss_retT 0x83b54 48 pS_cs [] [].
Definition ss_pE0 : sstate := Eval vm_compute in fss_retT 0x83b34 48 pS_cs [] [].
Definition ss_pF0 : sstate := Eval vm_compute in fss_retT 0x83b44 48 pS_cs [] [].
(* what a resume stage establishes on entering its next callee: ra, sp, every callee-saved register kept, the frame *)
Definition pj_set_at_call (W : world tfibsegs) (regs regsR regsC : bvmap 5 word) (memC : word -> option byte)
  (ra : Z) : Prop :=
  YK11.getr regsC 1 = w64 ra /\ spZ regsC = spZ regsR /\
  Forall (fun r => YK11.getr regsC r = YK11.getr regsR r) [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv /\
  pj_set_frame (mrestrict (w_H W) memC) (spZ regsR + 48) regs.
(* sp, the saved registers of the frame, or a kept atom: fsw_preserved's expectation at pj_set's ret *)
Definition pS_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 48 | 8 => SOff 43 0 | 9 => SOff 44 0 | 18 => SOff 45 0 | 19 => SOff 46 0 | 20 => SOff 47 0
  | z => SOff (Z.to_nat z) 0 end.
(* the frame at a stop, from the frame region (state index 0) *)
Ltac pS_frame HR0 ER EX regs regsR :=
  unfold pj_set_frame, pj_set_saved;
  repeat (apply Forall_cons; [cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (_ regs ?r)) =>
      let o' := eval vm_compute in (48 + o) in
      replace (spZ regsR + 48 + o) with (spZ regsR + o') by lia;
      let q := eval vm_compute in (Z.to_nat (42 + (40 - o') / 8)) in
      apply (fsw_field _ _ 2 _ _ _ _ _ _ o' 8%N (SOff q 0) _ HR0 ltac:(exact (f_equal bv_unsigned (ER 2%bv))) ltac:(cbn; tauto));
      [rewrite fsw_SOff0; let j := eval vm_compute in (q - 32)%nat in change q with (32 + j)%nat; rewrite EX;
       symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia] end|]);
  apply Forall_nil.
(* a plain stage's memory: only the frame window moves, and it lies above alloc_ceiling *)
Ltac pS_same_below HF E2 :=
  intros x Hx; apply HF; intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?unsigned_lit_small in Hr by lia; first [lia | rewrite E2 in Hr; lia] |]); destruct Hin.

Section WR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.

(* the common premise and conclusion of a resume stage that runs to a call *)
Definition pS_stage_to_call (ss0 : sstate) (pc0 target ra : Z) (pre : bvmap 5 word -> Prop)
  (args : bvmap 5 word -> bvmap 5 word -> Prop) : Prop :=
  forall ly S W0 mem0 md0 own lyc Sc Uc (W : world tfibsegs) regs regsR memR mdR (STK sp0 : Z)
    (FP : list (Z * Z)) k cnt fail live peak ty kids keys n cap (Q : world tfibsegs -> config -> Prop),
  pre regsR ->
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs)) ss0
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 pc0) memR (seg_rom tfibsegs))) ->
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memR) mdR k ->
  ARU tfibsegs B lyc Sc Uc W memR mdR ->
  spZ regsR = sp0 - 48 -> 48 <= STK ->
  (forall regsC memC mat,
     pj_set_at_call W regs regsR regsC memC ra -> args regsR regsC ->
     same_below memR memC alloc_ceiling ->
     @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memC) (with_vm_backing (m_vm_lazy mdR) mat mdR) k ->
     ARU tfibsegs B lyc Sc Uc W memC (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs target regsC memC (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 pc0) memR (seg_rom tfibsegs)) mdR) Q.

(* the frame window and the read-only cells of a resume state *)
Ltac pS_awr E2 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' a1 a2 a3 a4 a5 a6 a7 a8) end;
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - 48); [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* a resume stage that runs to a call: the run, then pj_set_at_call; args_tac proves the stage's argument facts *)
Ltac pS_to_call_tac target pre_tac args_tac :=
  intros ly S W0 mem0 md0 own lyc Sc Uc W regs regsR memR mdR STK sp0 FP k cnt fail live peak ty kids keys n cap Q
    HPRE HS HJ HARU Hsp HSTK KC;
  pose proof fs_segs_low as HSL; pose proof fs_wx as HWX;
  pose proof asan_consts as (C1 & _ & C3 & _);
  set (E := Ereg regsR (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs)) in *;
  assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r) by (intros r; subst E; apply ew_Ereg_reg);
  assert (EX : forall j, ew E (32 + j) = nth j (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs) (Z_to_bv 64 0))
    by (intros j; subst E; apply ew_Ereg_extra);
  assert (E2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (ER 2%bv); exact Hsp);
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _);
  pose proof Hstk as (_ & _ & Hceil & Hslo & _);
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms0) => change memR with (ms_mem ms0) in HJ, HARU end;
  pre_tac HS HPRE ER;
  fsw_aj_run_toU pj_set_tbl_ok HS HJ HARU target;
  [ pS_awr E2
  | lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?matx _)) _ =>
    let SB := fresh "SB" in
    assert (SB : same_below memR (ms_mem msx) alloc_ceiling)
      by (lazymatch goal with HFx : frame_of _ _ memR (ms_mem msx) |- _ => pS_same_below HFx E2 end);
    let HR0 := fresh "HR0" in
    pose proof (fsw_region_nth _ _ _ 0 _ HS eq_refl) as HR0; cbn [ms_mem restrict] in HR0;
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ msx HS eq_refl);
    apply (KC (ms_regs msx) (ms_mem msx) matx); [ | | exact SB | exact HJ | exact HARU ];
    [ unfold pj_set_at_call;
      split; [gw_reg HS (1%bv : bv 5); gw_val; apply U_lit; lia|];
      split; [unfold spZ; f_equal; gw_reg HS (2%bv : bv 5); rewrite fsw_SOff0; exact (ER 2%bv)|];
      split;
      [ repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ => gw_reg HS r; rewrite fsw_SOff0; exact (ER r) end|]);
        apply Forall_nil
      | pS_frame HR0 ER EX regs regsR ]
    | args_tac HS ER ] end end ].

Definition pB_args (regsR regsC : bvmap 5 word) : Prop := YK11.getr regsC 10 = YK11.getr regsR 9.
Definition pC_args (regsR regsC : bvmap 5 word) : Prop := YK11.getr regsC 10 = YK11.getr regsR 18.
Definition pE_args (regsR regsC : bvmap 5 word) : Prop :=
  YK11.getr regsC 10 = YK11.getr regsR 8 /\ YK11.getr regsC 11 = w64 0 /\ YK11.getr regsC 12 = w64 56.
Ltac pS_mv_args HS ER :=
  lazymatch goal with |- YK11.getr _ ?r = YK11.getr _ ?q => gw_reg HS r; rewrite fsw_SOff0; exact (ER q) end.

(* the first instruction of stages B and C is `beqz a0`, and a0 is 0 (pj_get: the key is absent; grow: granted) *)
Definition pS_a0_zero (regsR : bvmap 5 word) : Prop := YK11.getr regsR 10 = w64 0.
Ltac pS_beqz_taken HS HPRE ER :=
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS | clear HS; intros _ HS |];
  [ | let Hb := fresh "Hb" in intros Hb _; exfalso; rewrite branch_eq_U, U_lit in Hb by lia;
      unfold pS_a0_zero in HPRE; rewrite (U_atom _ 10 0) in Hb by (first [rewrite (ER 10%bv); exact HPRE | lia]);
      discriminate Hb ].
Ltac pS_no_pre HS HPRE ER := idtac.

(* STAGE B: 0x83b18 beqz a0 (pj_get answered 0: the key is absent) .. 0x83b50 jal grow (obj) *)
Lemma pj_set_stageB : pS_stage_to_call ss_pB0 0x83b18 A_grow 0x83b54 pS_a0_zero pB_args.
Proof. pS_to_call_tac A_grow pS_beqz_taken ltac:(fun HS ER => unfold pB_args; pS_mv_args HS ER). Qed.
(* STAGE C: 0x83b54 beqz a0 (grow answered 0) .. 0x83b88 jal fuzz_strdup (key) *)
Lemma pj_set_stageC : pS_stage_to_call ss_pC0 0x83b54 A_fuzz_strdup 0x83b8c pS_a0_zero pC_args.
Proof. pS_to_call_tac A_fuzz_strdup pS_beqz_taken ltac:(fun HS ER => unfold pC_args; pS_mv_args HS ER). Qed.
(* STAGE E: 0x83b34 (after __asan_memcpy) .. 0x83b40 jal __asan_memset (val, 0, 56) *)
Lemma pj_set_stageE : pS_stage_to_call ss_pE0 0x83b34 PC_memset 0x83b44 (fun _ => True) pE_args.
Proof.
pS_to_call_tac PC_memset pS_no_pre ltac:(fun HS ER => unfold pE_args;
  split; [pS_mv_args HS ER | split; lazymatch goal with |- YK11.getr _ ?r = _ => gw_reg HS r end; gw_val; apply U_lit; lia]).
Qed.
(* STAGE F: 0x83b44 (after __asan_memset) .. the ret 0x83b80: a0 = 0, the epilogue *)
Lemma pj_set_stageF : forall ly S W0 mem0 md0 own lyc Sc Uc (W : world tfibsegs) regs regsR memR mdR (STK sp0 : Z)
  (FP : list (Z * Z)) k cnt fail live peak ty kids keys n cap (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs)) ss_pF0
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 0x83b44) memR (seg_rom tfibsegs))) ->
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memR) mdR k ->
  ARU tfibsegs B lyc Sc Uc W memR mdR ->
  spZ regsR = sp0 - 48 -> sp0 = spZ regs -> 48 <= STK ->
  Forall (fun r => YK11.getr regsR r = YK11.getr regs r) [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv ->
  (forall E' ssf msf mat,
     st_ok tfibsegs E' ssf (restrict (w_H W) msf) -> ss_resv ssf = None ->
     clookup pj_set_tbl (ss_pc ssf) = Some RET_WORD_r ->
     YK11.getr (ms_regs msf) 1 = YK11.getr regs 1 -> YK11.getr (ms_regs msf) 10 = w64 0 ->
     aregs_preserved regs (ms_regs msf) ->
     same_below memR (ms_mem msf) alloc_ceiling ->
     @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc (ms_mem msf))
       (with_vm_backing (m_vm_lazy mdR) mat mdR) k ->
     ARU tfibsegs B lyc Sc Uc W (ms_mem msf) (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (mkCfg msf (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 0x83b44) memR (seg_rom tfibsegs)) mdR) Q.
Proof.
intros ly S W0 mem0 md0 own lyc Sc Uc W regs regsR memR mdR STK sp0 FP k cnt fail live peak ty kids keys n cap Q
  HS HJ HARU Hsp Hsp0 HSTK Hkeep KRET.
pose proof fs_segs_low as HSL. pose proof fs_wx as HWX. pose proof asan_consts as (C1 & _ & C3 & _).
set (E := Ereg regsR (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r) by (intros r; subst E; apply ew_Ereg_reg).
assert (EX : forall j, ew E (32 + j) = nth j (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs) (Z_to_bv 64 0))
  by (intros j; subst E; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (ER 2%bv); exact Hsp).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
change memR with (ms_mem (mkst regsR (Z_to_bv 64 0x83b44) memR (seg_rom tfibsegs))) in HJ, HARU.
fsw_aj_runU pj_set_tbl_ok HS HJ HARU.
{ pS_awr E2. }
apply (KRET E _ ms mat HS eq_refl ltac:(vm_compute; reflexivity)).
- gw_reg HS (1%bv : bv 5). rewrite fsw_SOff0. change 42%nat with (32 + 10)%nat. rewrite EX. reflexivity.
- gw_reg HS (10%bv : bv 5). gw_val. apply U_lit. lia.
- apply (fsw_preserved (w_H W) E _ ms regs pS_expect HS ltac:(vm_compute; reflexivity)).
  intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (pS_expect ?q) = _ =>
    let e := eval vm_compute in (pS_expect q) in change (pS_expect q) with e end;
  first
  [ lazymatch goal with |- sv_denot _ (SOff 2 48) = _ =>
      apply bv_eq; rewrite denot_SOff, E2, Hsp0; unfold spZ; replace (bv_unsigned (getr regs 2) - 48 + 48) with (bv_unsigned (getr regs 2)) by lia;
      apply zcanon_id; unfold M64; apply u64_range end
  | lazymatch goal with |- sv_denot _ (SOff ?q 0) = _ =>
      let j := eval vm_compute in (q - 32)%nat in change q with (32 + j)%nat end;
    rewrite fsw_SOff0, EX; reflexivity
  | rewrite fsw_SOff0;
    lazymatch goal with |- ew _ ?q = _ regs ?r =>
      change q with (Z.to_nat (bv_unsigned r)); rewrite ER;
      rewrite Forall_forall in Hkeep; apply Hkeep; cbn [In]; repeat (first [left; reflexivity | right]) end ].
- pS_same_below HF E2.
- exact HJ.
- exact HARU.
Qed.
End WR.

(* ================= STAGE D: after fuzz_strdup returns to 0x83b8c, to __asan_memcpy (kids + 56 n, val, 56) =================
   pf.c:384-388: keys[n] = dup; n++; then the shared memcpy / memset tail (j 0x83b2c). B's code (image B, 0x83b8c ..
   0x83c80; it is not A's): the UBSan checks of obj (0x83b8c o <> 0, 0x83b98 o mod 8), the ASan checks of obj + 0x20 /
   + 0x28 (0x83bac / 0x83bc0), ld n, ld keys, a2 = keys + (n << 3) (0x83bd0), the UBSan checks of &keys[n] (0x83bdc
   null-ness, 0x83bf0 8 n signed overflow, 0x83bf4 wrap, 0x83bf8 keys <> 0, 0x83c00 alignment), its ASan check
   (0x83c10), the slot store 0x83c14, dup <> 0 (0x83c18), the ASan checks of obj + 0x18 / + 0x28 (0x83c2c / 0x83c34),
   kids + 56 n, the n store 0x83c54 (before the kids checks), the UBSan checks of kids + 56 n (0x83c58 null-ness, 0x83c5c
   wrap, 0x83c74 56 n signed overflow), a0 = kids + 56 n, j 0x83b2c, a1 = val, jal __asan_memcpy 0x83b30.
   Resume state fss_retT at 0x83b8c with obj as FSW_pj's object region at atom 9 = s1 = obj, write window [24, 56)
   (pj_set's FP on obj), its five fields at xatom 4..8 (pj_fields order: ty kids keys n cap = atoms 37..41), atom facts
   pD_gf for obj (9), the shadow base s4 (20) and dup (10): the same state as A's (lib/A ss_pD0 at A's 0x83998).
   The run: (1) three atom facts from the premises, for kids (38, >= 1), keys (39, >= 1) and n (40, <= 2 ^ 44); (2) to
   0x83bd4 (a2 = &keys[n] computed); (3) FSW_K's fsw_reseat_atom puts a2 on a fresh atom (48) with the 8-byte slot as a
   writable region and the fact pD_slot_fact (>= 4096 + HEAD, 8-aligned); (4) the five UBSan conditions the engine's
   ranges do not decide, pD_c1 .. pD_c5, proved on the env from the premises and added to the state (YP06
   st_ok_add_cond), so that the run decides each guard; (5) the run to __asan_memcpy. The UBSan guards, each refuted
   inside this lemma, and the premise each one rests on (ported from a working branch
   lib/B/Prog/pj_set_store.v, there over pj_set_c):
     0x83b8c beqz s1          o <> 0                    atom 9's fact (pD_gf, lo 4096): 4096 <= o
     0x83b98 bnez (o & 7)     o 8-aligned               atom 9's fact (al 3): o mod 8 = 0
     0x83bdc beq              keys <> 0, slot <> 0      atom 39's fact (0 < keys), the slot fact (4096 + HEAD <= slot)
     0x83bf0 bnez             8 n no signed overflow    pD_c1: n <= 2 ^ 44 (8 n <= slot < alloc_ceiling)
     0x83bf4 bltu             slot >= keys              pD_c2: slot = keys + 8 n, no wrap (slot + 8 <= alloc_ceiling)
     0x83bf8 beqz keys        keys <> 0                 atom 39's fact: 0 < keys
     0x83c00 bnez (slot & 7)  slot 8-aligned            the slot fact (al 3): slot mod 8 = 0
     0x83c58 beq              kids + 56 n <> 0          pD_c3: 0 < kids, kids + 56 n < 2 ^ 64
     0x83c5c bltu             kids + 56 n >= kids       pD_c4: kids + 56 n < 2 ^ 64
     0x83c74 bnez             56 n no signed overflow   pD_c5: n <= 2 ^ 44
   and the ASan checks 0x83bac / 0x83bc0 / 0x83c2c / 0x83c34 (obj's shent, range_addressable of [o, o + 56)) and
   0x83c10 (the slot's shent, range_addressable of [slot, slot + 8)). Both stores are justified by awr_byte premises
   (the slot: FP inside the keys block, or a block grow made; obj + 0x28: inside [o + 24, o + 56)). *)
Definition pD_obj : YP09.region := pj_obj_regionWX 9 4 24 56.
Definition pD_gf : list (nat * afact) :=
  [(9%nat, mkAF 4096 (0x7fffff800000 - 56) 3); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (10%nat, mkAF (4096 + HEAD) (2 ^ 47) 4)].
Definition pD_Bx : sv := SOff 20 0.
Definition pD_SH1 : list shent := [mkSHE 9 0 56].
Definition pD_slot_atom : nat := 48.
Definition pD_slot : YP09.region := YP09.mkRegion (Some pD_slot_atom) 0 8 0 8 [].
Definition pD_slot_fact : afact := mkAF (4096 + HEAD) (0x7fffff800000 - 8) 3.
Definition pD_SH2 : list shent := [mkSHE 9 0 56; mkSHE pD_slot_atom 0 8].
Definition ss_pD0 : sstate := Eval vm_compute in fss_retT 0x83b8c 48 pS_cs [pD_obj] pD_gf.
(* the field facts of step (1): kids (atom 38), keys (39), n (40) *)
Definition pD_kids_fact : afact := mkAF 1 (2 ^ 64 - 1) 0.
Definition pD_keys_fact : afact := mkAF 1 (2 ^ 47) 0.
Definition pD_n_fact : afact := mkAF 0 (2 ^ 44) 0.
(* the conditions of step (4), in the form the engine computes for each guard's operands (MEASURED: sym_run_toN_tok over
   pj_set_tbl from the state after step (3)) *)
Definition pD_k56 : sv := SAlu ALU_ADD (SOff 38 0) (SMd M_MUL (SOff 40 0) (SLit 56)).
Definition pD_c1 : acond := mkAC BC_EQ (SAlu ALU_SRL (SOff 40 (2 ^ 60)) (SLit 61)) (SLit 0).
Definition pD_c2 : acond := mkAC BC_GEU (SOff pD_slot_atom 0) (SOff 39 0).
Definition pD_c3 : acond := mkAC BC_NE (SLit 1) (SAlu ALU_SLTU pD_k56 (SLit 1)).
Definition pD_c4 : acond := mkAC BC_GEU pD_k56 (SOff 38 0).
Definition pD_c5 : acond := mkAC BC_EQ
  (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 40 0) (SLit 56))
     (SAlu ALU_SRA (SMd M_MUL (SOff 40 0) (SLit 56)) (SLit 63)))) (SLit 0).

Section WD. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.

Lemma pj_set_stageD : forall ly S W0 mem0 md0 own lyc Sc Uc (W : world tfibsegs) regs regsR memR mdR (STK sp0 : Z)
  (FP : list (Z * Z)) k cnt fail live peak ty kids keys n cap o w dup (Q : world tfibsegs -> config -> Prop),
  let slot := keys + 8 * n in
  st_ok tfibsegs (Ereg regsR (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs)) ss_pD0
    (restrict (w_H W) (mkst regsR (Z_to_bv 64 0x83b8c) memR (seg_rom tfibsegs))) ->
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memR) mdR k ->
  ARU tfibsegs B lyc Sc Uc W memR mdR ->
  spZ regsR = sp0 - 48 -> 48 <= STK ->
  YK11.getr regsR 9 = w64 o -> YK11.getr regsR 8 = w64 w -> YK11.getr regsR 10 = w64 dup ->
  YK11.getr regsR 20 = w64 SHADOW_OFF ->
  4096 <= o -> o + 56 <= alloc_ceiling -> o mod 8 = 0 -> 0 <= w < 2 ^ 64 ->
  4096 + HEAD <= dup < 2 ^ 47 -> dup mod 16 = 0 ->
  0 < keys -> 0 <= n -> 0 < kids -> kids + 56 * n < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  4096 + HEAD <= slot -> slot + 8 <= alloc_ceiling -> slot mod 8 = 0 ->
  (slot + 8 <= o \/ o + 56 <= slot) -> (slot + 8 <= 0x10000 \/ FS_IMG_END <= slot) ->
  (forall i, 0 <= i < 8 -> writable_at tfibsegs (mrestrict (w_H W) memR) (slot + i)) ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF o 56 ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF slot 8 ->
  (forall a, o <= a < o + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (forall a, slot <= a < slot + 8 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  (forall a, slot <= a < slot + 8 -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (forall a, o + 24 <= a < o + 56 -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  (forall regsC memC mat,
     YK11.getr regsC 1 = w64 0x83b34 -> spZ regsC = spZ regsR ->
     YK11.getr regsC 10 = w64 (kids + 56 * n) -> YK11.getr regsC 11 = w64 w -> YK11.getr regsC 12 = w64 56 ->
     YK11.getr regsC 9 = w64 (o + 24) ->
     Forall (fun r => YK11.getr regsC r = YK11.getr regsR r) [3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
     pj_set_frame (mrestrict (w_H W) memC) (spZ regsR + 48) regs ->
     (forall x, 0 <= x < alloc_ceiling -> ~ (slot <= x < slot + 8) -> ~ (o + 24 <= x < o + 56) ->
        memC (Z_to_bv 64 x) = memR (Z_to_bv 64 x)) ->
     mem_grows (mrestrict (w_H W) memR) (mrestrict (w_H W) memC) ->
     val_mem tfibsegs (mrestrict (w_H W) memC) slot 8 dup ->
     val_mem tfibsegs (mrestrict (w_H W) memC) (o + 24) 8 kids ->
     val_mem tfibsegs (mrestrict (w_H W) memC) (o + 32) 8 keys ->
     val_mem tfibsegs (mrestrict (w_H W) memC) (o + 40) 8 (n + 1) ->
     val_mem tfibsegs (mrestrict (w_H W) memC) (o + 48) 8 cap ->
     @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Uc memC) (with_vm_backing (m_vm_lazy mdR) mat mdR) k ->
     ARU tfibsegs B lyc Sc Uc W memC (with_vm_backing (m_vm_lazy mdR) mat mdR) ->
     SRr tfibsegs W (YG0d.cfg_at tfibsegs PC_memcpy regsC memC (with_vm_backing (m_vm_lazy mdR) mat mdR)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regsR (Z_to_bv 64 0x83b8c) memR (seg_rom tfibsegs)) mdR) Q.
Proof.
intros ly S W0 mem0 md0 own lyc Sc Uc W regs regsR memR mdR STK sp0 FP k cnt fail live peak ty kids keys n cap o w dup Q slot
  HS HJ HARU Hsp HSTK H9 H8 H10 H20 Ho4 Hoc Ho8 Hw Hd Hd16 Hk Hn Hki Hkn Hcap Hs4 Hsc Hs8 Hsd Hsimg Hswr Hrao Hras Happo Happs
  HWS HWO KD.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fs_segs_low as HSL. pose proof fs_wx as HWX.
pose proof asan_consts as (C1 & _ & C3 & _). unfold HEAD in Hd, Hs4.
(* n <= 2 ^ 44 and keys <= 2 ^ 47: 8 n + keys = slot < alloc_ceiling < 2 ^ 47 *)
assert (Hn44 : n <= 2 ^ 44) by (subst slot; lia).
assert (Hk47 : keys <= 2 ^ 47) by (subst slot; lia).
set (E := Ereg regsR (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs)) in *.
assert (ER : forall r : bv 5, ew E (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r) by (intros r; subst E; apply ew_Ereg_reg).
assert (EX : forall j, ew E (32 + j) = nth j (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs) (Z_to_bv 64 0))
  by (intros j; subst E; apply ew_Ereg_extra).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (ER 2%bv); exact Hsp).
assert (UR : forall (r : bv 5) z c, YK11.getr regsR r = w64 z -> 0 <= z < 2 ^ 64 -> 0 <= z + c < 2 ^ 64 ->
  YP0e.U E (SOff (Z.to_nat (bv_unsigned r)) c) = z + c).
{ intros r z c Hr Hz Hzc. apply U_atom_off; [|exact Hz|exact Hzc]. rewrite ER. exact Hr. }
assert (U9 : forall c, 0 <= c <= 56 -> YP0e.U E (SOff 9 c) = o + c) by (intros c Hc; apply (UR 9%bv o c H9); lia).
assert (UB : YP0e.U E pD_Bx = SHADOW_OFF)
  by (pose proof (UR 20%bv SHADOW_OFF 0 H20 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)) as X; rewrite Z.add_0_r in X; exact X).
(* obj's fields: kids at atom 38, keys 39, n 40, cap 41 *)
assert (Ekeys : ew E 39 = Z_to_bv 64 keys) by (change 39%nat with (32 + 7)%nat; rewrite EX; reflexivity).
assert (En : ew E 40 = Z_to_bv 64 n) by (change 40%nat with (32 + 8)%nat; rewrite EX; reflexivity).
assert (Ekids : ew E 38 = Z_to_bv 64 kids) by (change 38%nat with (32 + 6)%nat; rewrite EX; reflexivity).
assert (Ecap : ew E 41 = Z_to_bv 64 cap) by (change 41%nat with (32 + 9)%nat; rewrite EX; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
(* ---- (1) the field facts ---- *)
assert (AFk : afact_ok E 38 pD_kids_fact).
{ unfold afact_ok, pD_kids_fact. cbn [af_lo af_hi af_al2]. rewrite Ekids, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (AFy : afact_ok E 39 pD_keys_fact).
{ unfold afact_ok, pD_keys_fact. cbn [af_lo af_hi af_al2]. rewrite Ekeys, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (AFn : afact_ok E 40 pD_n_fact).
{ unfold afact_ok, pD_n_fact. cbn [af_lo af_hi af_al2]. rewrite En, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_add_fact tfibsegs _ _ _ 40 pD_n_fact
  (st_ok_add_fact tfibsegs _ _ _ 39 pD_keys_fact (st_ok_add_fact tfibsegs _ _ _ 38 pD_kids_fact HS AFk) AFy) AFn) as HS1.
clear HS AFk AFy AFn.
lazymatch type of HS1 with st_ok _ _ ?ss _ =>
  let v := eval vm_compute in ss in change ss with v in HS1 end.
assert (SHOK : sh_ok tfibsegs pD_Bx pD_SH1 E (mrestrict (w_H W) memR)).
{ constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) memR E pD_Bx 9 o 56 o 0 56 Hrao UB); [rewrite U9 by lia; lia | lia | lia |].
  intros x Hx. apply Happo. lia. }
change memR with (ms_mem (mkst regsR (Z_to_bv 64 0x83b8c) memR (seg_rom tfibsegs))) in HJ, HARU, SHOK.
(* ---- (2) 0x83b8c .. 0x83bd4: o <> 0, o aligned, the obj + 0x20 and obj + 0x28 checks, ld n, ld keys,
   a2 = keys + (n << 3) ---- *)
fsw_aj_run_to_tokU pj_set_tbl_ok HS1 HJ HARU SHOK fs_Bspan 0x83bd4.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' a1 a2 a3 a4 a5 a6 a7 a8) end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - 48); [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (k := 9%nat) (b := o); [reflexivity | rewrite (ER 9%bv), H9; apply wz; lia | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HWO. lia. }
  apply awr_ok_nil. }
assert (FR1 : forall x, 0 <= x < alloc_ceiling -> ~ (o + 24 <= x < o + 56) -> ms_mem ms (Z_to_bv 64 x) = memR (Z_to_bv 64 x)).
{ intros x Hx Hx2. apply HF. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?unsigned_lit_small in Hr by lia;
    first [ lia | rewrite E2 in Hr; lia | rewrite (ER 9%bv), H9, wz in Hr by lia; lia ] |]); destruct Hin. }
clear HF HFr. rename HG into HG1.
(* ---- (3) a2 = &keys[n] on the fresh atom 48, with the slot as a writable region ---- *)
assert (Rslot : YK11.getr (ms_regs ms) 12 = Z_to_bv 64 slot).
{ gw_reg HS1 (12%bv : bv 5). apply bv_eq. rewrite unsigned_lit_small by lia.
  change (bv_unsigned (sv_denot E ?e)) with (YP0e.U E e).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 39 keys Ekeys ltac:(lia)), (U_atom E 40 n En ltac:(lia)), U_lit by lia.
  change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_small (n * 8)) by lia. rewrite zcanon_small by lia. subst slot. lia. }
set (E' := ewset E pD_slot_atom (YK11.getr (ms_regs ms) 12)).
assert (EA : forall q, q <> pD_slot_atom -> ew E' q = ew E q) by (intros q Hq; subst E'; apply ew_ewset_other; exact Hq).
assert (E46 : bv_unsigned (ew E' pD_slot_atom) = slot) by (subst E'; rewrite ew_ewset_same, Rslot; apply wz; lia).
assert (E2' : bv_unsigned (ew E' 2) = sp0 - 48) by (rewrite EA by (unfold pD_slot_atom; lia); exact E2).
pose proof (fsw_reseat_atom E _ (restrict (w_H W) ms) 12%bv pD_slot_atom 0 8 pD_slot_fact HS1 ltac:(vm_compute; reflexivity)
  ltac:(intros Hq; discriminate Hq) eq_refl) as HS2.
cbn [ms_regs restrict] in HS2. fold E' in HS2.
assert (AV : forall a, 0 <= a < alloc_ceiling -> ~ (o + 24 <= a < o + 56) ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memR a).
{ intros a Ha Hb. unfold aview, mbyte, mrestrict. rewrite (FR1 a Ha Hb). reflexivity. }
assert (Hreg : region_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) (YP09.mkRegion (Some pD_slot_atom) 0 8 0 8 [])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E46.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros q Hq. apply (writable_at_eq tfibsegs (mrestrict (w_H W) memR)); [|apply Hswr; lia].
  unfold mrestrict. rewrite (FR1 (slot + q)) by lia. reflexivity. }
lazymatch type of HS2 with _ -> all_disjoint _ _ ?rs -> _ =>
  assert (Hdisj : all_disjoint E' (YP09.mkRegion (Some pD_slot_atom) 0 8 0 8 []) rs);
  [let rs' := eval vm_compute in rs in change rs with rs' | ] end.
{ cbn [all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E46, E2', (EA 9%nat) by (unfold pD_slot_atom; lia).
  rewrite (ER 9%bv), H9, wz by lia.
  unfold FS_IMG_END in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (Haf : afact_ok E' pD_slot_atom pD_slot_fact).
{ unfold afact_ok, pD_slot_fact, HEAD. cbn [af_lo af_hi af_al2]. rewrite E46. change (2 ^ 3) with 8. lia. }
pose proof (HS2 Hreg Hdisj Haf) as HS3. clear HS2 HS1 Hreg Hdisj Haf.
(* ---- (4) the five UBSan conditions the engine's ranges leave open, on E' ---- *)
assert (UA : forall q v, q <> pD_slot_atom -> ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> YP0e.U E' (SOff q 0) = v).
{ intros q v Hq Hqv Hv. apply U_atom; [rewrite EA by exact Hq; exact Hqv | exact Hv]. }
assert (Ukids : YP0e.U E' (SOff 38 0) = kids) by (apply UA; [unfold pD_slot_atom; lia | exact Ekids | lia]).
assert (Ukeys : YP0e.U E' (SOff 39 0) = keys) by (apply UA; [unfold pD_slot_atom; lia | exact Ekeys | lia]).
assert (Un : YP0e.U E' (SOff 40 0) = n) by (apply UA; [unfold pD_slot_atom; lia | exact En | lia]).
assert (U46 : YP0e.U E' (SOff pD_slot_atom 0) = slot) by (rewrite U_SOff, E46, Z.add_0_r; apply zcanon_small; lia).
assert (UM : YP0e.U E' (SMd M_MUL (SOff 40 0) (SLit 56)) = n * 56).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite Un, U_lit by lia. apply zcanon_small. lia. }
assert (Uk56 : YP0e.U E' pD_k56 = kids + n * 56).
{ unfold pD_k56. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ukids, UM. apply zcanon_small. lia. }
assert (CC1 : branch_taken BC_EQ (sv_denot E' (SAlu ALU_SRL (SOff 40 (2 ^ 60)) (SLit 61))) (sv_denot E' (SLit 0)) = true).
{ rewrite branch_eq_U, U_SAlu, !U_lit by lia. cbn [zalu_raw].
  rewrite (U_atom_off E' 40 n (2 ^ 60)) by (first [rewrite EA by (unfold pD_slot_atom; lia); exact En | lia]).
  change (Z.land 61 63) with 61. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (n + 2 ^ 60)) by lia.
  reflexivity. }
assert (CC2 : branch_taken BC_GEU (sv_denot E' (SOff pD_slot_atom 0)) (sv_denot E' (SOff 39 0)) = true).
{ rewrite branch_geu_U, U46, Ukeys. apply negb_true_iff, Z.ltb_ge. subst slot. lia. }
assert (CC3 : branch_taken BC_NE (sv_denot E' (SLit 1)) (sv_denot E' (SAlu ALU_SLTU pD_k56 (SLit 1))) = true).
{ rewrite branch_ne_U, U_SAlu, !U_lit by lia. cbn [zalu_raw]. rewrite Uk56.
  rewrite (proj2 (Z.ltb_ge (kids + n * 56) 1)) by lia. reflexivity. }
assert (CC4 : branch_taken BC_GEU (sv_denot E' pD_k56) (sv_denot E' (SOff 38 0)) = true).
{ rewrite branch_geu_U, Uk56, Ukids. apply negb_true_iff, Z.ltb_ge. lia. }
assert (UH : YP0e.U E' (SMd M_MULH (SOff 40 0) (SLit 56)) = 0).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite Un, U_lit by lia.
  rewrite (swrap64_id n), (swrap64_id 56) by (unfold half64; lia).
  change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (n * 56)) by lia. reflexivity. }
assert (US : YP0e.U E' (SAlu ALU_SRA (SMd M_MUL (SOff 40 0) (SLit 56)) (SLit 63)) = 0).
{ rewrite U_SAlu, UM, U_lit by lia. cbn [zalu_raw]. rewrite (swrap64_id (n * 56)) by (unfold half64; lia).
  change (Z.land 63 63) with 63. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (n * 56)) by lia. reflexivity. }
assert (CC5 : branch_taken BC_EQ
  (sv_denot E' (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 40 0) (SLit 56))
     (SAlu ALU_SRA (SMd M_MUL (SOff 40 0) (SLit 56)) (SLit 63))))) (sv_denot E' (SLit 0)) = true).
{ rewrite branch_eq_U, U_SAlu. rewrite (U_SAlu E' ALU_XOR), UH, US, !U_lit by lia. cbn [zalu_raw]. reflexivity. }
pose proof (st_ok_add_cond tfibsegs _ _ _ _ _ _
  (st_ok_add_cond tfibsegs _ _ _ _ _ _
    (st_ok_add_cond tfibsegs _ _ _ _ _ _
      (st_ok_add_cond tfibsegs _ _ _ _ _ _
        (st_ok_add_cond tfibsegs _ _ _ _ _ _ HS3 CC1) CC2) CC3) CC4) CC5) as HS4.
clear HS3 CC1 CC2 CC3 CC4 CC5.
lazymatch type of HS4 with st_ok _ _ ?ss _ =>
  let v := eval vm_compute in ss in change ss with v in HS4 end.
(* ---- the second part's shents: obj and the slot, on the memory after the first part ---- *)
assert (U9' : forall c, 0 <= c <= 56 -> YP0e.U E' (SOff 9 c) = o + c)
  by (intros c Hc; rewrite U_SOff, EA by (unfold pD_slot_atom; lia); rewrite <- U_SOff; apply U9; exact Hc).
assert (UB' : YP0e.U E' pD_Bx = SHADOW_OFF) by (unfold pD_Bx; rewrite U_SOff, EA by (unfold pD_slot_atom; lia); rewrite <- U_SOff; exact UB).
assert (RA : forall p q, 0 <= p -> p + q <= alloc_ceiling -> (forall a, p <= a < p + q -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  range_addressable (aview tfibsegs (w_H W) memR) SHADOW_OFF p q ->
  range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF p q).
{ intros p q Hp Hq Hap Hr x Hx. destruct (Hr x Hx) as (sx & Hs1 & Hs2). exists sx. split; [|exact Hs2].
  rewrite AV; [exact Hs1 | unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia |].
  intros Hin. unfold shadow_of_addr in Hin.
  apply (Happo (SHADOW_OFF + x / 8)); [lia | unfold SHADOW_OFF in *; Z.div_mod_to_equations; lia]. }
assert (SHOK2 : sh_ok tfibsegs pD_Bx pD_SH2 E' (mrestrict (w_H W) (ms_mem ms))).
{ constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem ms) E' pD_Bx 9 o 56 o 0 56 (RA o 56 ltac:(lia) Hoc Happo Hrao) UB');
      [rewrite U9' by lia; lia | lia | lia |].
    intros x Hx. apply Happo. lia.
  - apply (shent_ok_of_range tfibsegs (w_H W) (ms_mem ms) E' pD_Bx pD_slot_atom slot 8 slot 0 8
      (RA slot 8 ltac:(lia) Hsc Happs Hras) UB' U46); [lia | lia |].
    intros x Hx. apply Happs. lia. }
(* ---- (5) 0x83bd4 .. 0x83b30: the &keys[n] guards and check, the slot store, dup <> 0, the obj + 0x18 / + 0x28 checks,
   n + 1 stored, the kids + 56 n guards, a0 = kids + 56 n, j 0x83b2c, a1 = val, jal __asan_memcpy ---- *)
fsw_aj_run_to_tokU pj_set_tbl_ok HS4 HJ HARU SHOK2 fs_Bspan PC_memcpy.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' a1 a2 a3 a4 a5 a6 a7 a8) end.
  eapply awr_ok_cons_gen with (k := pD_slot_atom) (b := slot); [reflexivity | exact E46 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HWS. lia. }
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - 48); [reflexivity | rewrite E2'; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (k := 9%nat) (b := o);
    [reflexivity | rewrite (EA 9%nat) by (unfold pD_slot_atom; lia); rewrite (ER 9%bv), H9; apply wz; lia | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HWO. lia. }
  apply awr_ok_nil. }
assert (ER' : forall r : bv 5, ew E' (Z.to_nat (bv_unsigned r)) = YK11.getr regsR r)
  by (intros r; rewrite EA by (pose proof (u5_range r); unfold pD_slot_atom; lia); apply ER).
assert (E46n : bv_unsigned (ew E' 48) = slot) by exact E46.
assert (FR2 : forall x, 0 <= x < alloc_ceiling -> ~ (slot <= x < slot + 8) -> ~ (o + 24 <= x < o + 56) ->
  ms_mem ms0 (Z_to_bv 64 x) = ms_mem ms (Z_to_bv 64 x)).
{ intros x Hx Hx1 Hx2. apply HF. intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?unsigned_lit_small in Hr by lia;
    first [ lia | rewrite E2' in Hr; lia | rewrite E46n in Hr; lia
          | rewrite (ER' 9%bv), H9, wz in Hr by lia; lia ] |]); destruct Hin. }
pose proof (fsw_region_nth _ _ _ 0 _ HS4 eq_refl) as HRS. pose proof (fsw_region_nth _ _ _ 1 _ HS4 eq_refl) as HR0.
pose proof (fsw_region_nth _ _ _ 4 _ HS4 eq_refl) as HRO.
cbn [ms_mem restrict] in HRS, HR0, HRO.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms0 HS4 eq_refl).
apply (KD (ms_regs ms0) (ms_mem ms0) mat0).
- gw_reg HS4 (1%bv : bv 5). gw_val. apply U_lit. lia.
- unfold spZ. f_equal. gw_reg HS4 (2%bv : bv 5). rewrite fsw_SOff0. exact (ER' 2%bv).
- gw_reg HS4 (10%bv : bv 5). gw_val. change (YP0e.U E' (SAlu ALU_ADD (SOff 38 0) (SMd M_MUL (SOff 40 0) (SLit 56))))
    with (YP0e.U E' pD_k56). rewrite Uk56. lia.
- gw_reg HS4 (11%bv : bv 5). gw_val. apply (U_atom E' 8 w); [rewrite (ER' 8%bv); exact H8 | exact Hw].
- gw_reg HS4 (12%bv : bv 5). gw_val. apply U_lit. lia.
- gw_reg HS4 (9%bv : bv 5). gw_val. rewrite U9' by lia. lia.
- repeat (apply Forall_cons; [lazymatch goal with |- YK11.getr _ ?r = _ => gw_reg HS4 r; rewrite fsw_SOff0; exact (ER' r) end|]).
  apply Forall_nil.
- unfold pj_set_frame, pj_set_saved.
  repeat (apply Forall_cons; [cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (_ + ?o) 8 (bv_unsigned (_ regs ?r)) =>
      let o' := eval vm_compute in (48 + o) in
      replace (spZ regsR + 48 + o) with (spZ regsR + o') by lia;
      let q := eval vm_compute in (Z.to_nat (42 + (40 - o') / 8)) in
      apply (fsw_field _ _ 2 _ _ _ _ _ _ o' 8%N (SOff q 0) _ HR0 ltac:(exact (f_equal bv_unsigned (ER' 2%bv))) ltac:(cbn; tauto));
      [rewrite fsw_SOff0, EA by (unfold pD_slot_atom; lia);
       let j := eval vm_compute in (q - 32)%nat in change q with (32 + j)%nat; rewrite EX;
       symmetry; apply Z_to_bv_bv_unsigned | apply u64_range | cbn; lia] end|]).
  apply Forall_nil.
- intros x Hx Hx1 Hx2. rewrite (FR2 x Hx Hx1 Hx2). exact (FR1 x Hx Hx2).
- apply (mem_grows_trans _ (mrestrict (w_H W) (ms_mem ms))); assumption.
- replace slot with (slot + 0) by lia.
  apply (fsw_field _ _ pD_slot_atom _ _ _ _ _ _ 0 8%N (SOff 10 0) dup HRS E46 ltac:(cbn; tauto));
    [rewrite fsw_SOff0, EA by (unfold pD_slot_atom; lia); exact (eq_trans (ER 10%bv) H10) | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 9 _ _ _ _ _ _ 24 8%N (SOff 38 0) kids HRO
    ltac:(rewrite (ER' 9%bv), H9; apply wz; lia) ltac:(cbn; tauto));
    [rewrite fsw_SOff0, EA by (unfold pD_slot_atom; lia); exact Ekids | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 9 _ _ _ _ _ _ 32 8%N (SOff 39 0) keys HRO
    ltac:(rewrite (ER' 9%bv), H9; apply wz; lia) ltac:(cbn; tauto));
    [rewrite fsw_SOff0, EA by (unfold pD_slot_atom; lia); exact Ekeys | cbn; lia | cbn; lia].
- apply (fsw_field _ _ 9 _ _ _ _ _ _ 40 8%N (SOff 40 1) (n + 1) HRO
    ltac:(rewrite (ER' 9%bv), H9; apply wz; lia) ltac:(cbn; tauto)); [| cbn; lia | cbn; lia].
  apply bv_eq. rewrite denot_SOff, EA by (unfold pD_slot_atom; lia). rewrite En, unsigned_lit_small by lia.
  rewrite zcanon_small by lia. rewrite unsigned_lit_small by lia. reflexivity.
- apply (fsw_field _ _ 9 _ _ _ _ _ _ 48 8%N (SOff 41 0) cap HRO
    ltac:(rewrite (ER' 9%bv), H9; apply wz; lia) ltac:(cbn; tauto));
    [rewrite fsw_SOff0, EA by (unfold pD_slot_atom; lia); exact Ecap | cbn; lia | cbn; lia].
- exact HJ.
- exact HARU.
Qed.
End WD.
