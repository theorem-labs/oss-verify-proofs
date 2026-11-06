(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the invariant of pins_set's ASan walk at its program calls, after
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_cx / cl_mid, the facts a segment of cgif_close carries) over
   fuzz_command's recorder. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/pins_set_s3.v, with its module paths and module names changed; 322 of its 365 lines of code are new or changed and 247 lines of the source are left out. *)
(* sup_add's ASan walk (plugin-hostd/fuzz_command, 0x89dbc), stage 7: the epilogue.

   From M4 (0x8a0c4, after hand_back / answer) to `ret` (0x8a1a4): the buffer's shadow is poisoned again
   (sb a1,4..7(s9), f8), the magic word 0x45e0360e is written at F (sd a1,0(s10)), `beqz s2` is pruned (the frame
   F is an application address, 4096 <= F), the 16 shadow bytes of the frame take f5, the frame's flag pointer is
   loaded from F + 120 and the flag byte is cleared (`sb zero,0(a1)`: the release, PaLibF's aj_flag_store_pi, which
   takes the journal's own list from [(1, pos)] to [] and the state to stack_free_state 1 pos Sc), the 13
   callee-saved registers are restored from the real frame, sp is put back and the function returns.

   One plain symbolic run carries the whole epilogue (paj_run_flag_sh), then CmdPaLib's paj_ret_at returns. The
   post is sup_add_s0.v's sa_final (apost_baseF, here with the FP state of this stage: PaFx.v's apost_baseF_of_base):
   the journal with no frame of its own, the callee-saved registers and sa_postQ, which M4 carries and which the
   epilogue keeps, since it writes only the frame's first word, the frame's 16 shadow bytes and the flag byte: none
   of them is a byte of g_rec, of record.spill or of a block. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 sup_add_lem PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic memory of the epilogue: the frame's first word (s10, atom 26) for the magic word, the frame's
   flag-pointer slot (s2, atom 18) at F + 120, the frame's 16 shadow bytes (s9, atom 25), the flag byte
   (atom 32) and the 13 callee-saved slots of the real frame below sp0 (s0, atom 8; atoms 33..45 their values).
   The frame carries two atoms because s2 and s10 both hold F; the two windows are disjoint. *)
Definition sa7_frame_lo : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 8 [].
Definition sa7_frame_hi : YP09.region :=
YP09.mkRegion (Some 18%nat) 112 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))].
Definition sa7_shadow : YP09.region := YP09.mkRegion (Some 25%nat) 0 16 0 16 [].
Definition sa7_flag : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition sa7_saved : YP09.region :=
YP09.mkRegion (Some 8%nat) (-104) 0 0 0
[YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
 YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Definition sa7_regions : smem := [sa7_frame_lo; sa7_frame_hi; sa7_shadow; sa7_flag; sa7_saved].
(* the frame is an application address of alignment 32 (AR's frames law), under both of its names *)
Definition sa7_facts : facts := mkFacts [(18%nat, HPTR 5); (26%nat, HPTR 5)] [] [].
(* the atoms above 31: the flag's address, then the saved values in the order of sa_saved *)
Definition sa7_extra (fl : Z) (regs : bvmap 5 word) : list word :=
Z_to_bv 64 fl :: map (fun r => getr regs (Z_to_bv 5 r)) sa_saved.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* a reader fact of the walk, in the form the symbolic memory wants *)
Lemma sa7_val_mem : forall (H : word -> bool) (mem : word -> option byte) a n v,
aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb.
destruct (aview_byte SEGS H mem _ _ Hb) as (b & Hm & Hbv & _). rewrite Hm. f_equal.
transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned | f_equal; symmetry; exact Hbv].
Qed.
(* a byte of g_rec or of record.spill is a byte of the program's globals *)
Lemma sa7_rec_img : forall a, in_rec a -> in_img SEGS a.
Proof.
intros a Ha. apply cif_prog_img. unfold cmd_PG, in_rec, REC_SIZE, SC_SIZE in *.
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma sa_m4_ok : SA_M4_stmt B MT.
Proof.
unfold SA_M4_stmt.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos CX M4.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & _).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk0' & Hpres0 & Hch & HQT).
pose proof M4 as (CORE & POSTQ).
unfold sa_core in CORE. cbv zeta in CORE.
destruct CORE as (HJ & HFRAME & _ & _ & _ & HFLPTR & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & _ & _ & Q25 & Q26).
set (sp0 := spZ regs) in *. set (F := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
assert (HFB : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HFB in HFLPTR.
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk1 & _).
assert (Hin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof Hstk1 as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : 104 <= SUP_ADD_STK) by (apply Z.leb_le; vm_compute; reflexivity).
(* the frame, its shadow and its flag byte *)
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 1 pos HAR Hin1) as (HF32 & HFapp & HFpres & HFSpres).
rewrite HFB in HFapp, HFpres. change (fs_frame_bytes 1 / 8) with 16 in HFSpres.
unfold shadow_addr in HFSpres.
destruct (al_flag _ _ LAWS lyc Sc Wc memc mdc 1 pos HAR Hin1) as (HFLpres & HFLown & HFLapp & HFLceil).
destruct (frames_bounds _ _ LAWS lyc Sc Wc memc mdc 1 pos HAR Hin1) as (HF4096 & HFceil & _).
rewrite HFB in HFceil.
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFapp, HFLapp.
cbn [fst snd] in HFapp, HFLapp.
assert (HFdiv : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (HFdiv0 : 0 <= F / 8) by (apply Z.div_pos; lia).
(* the flag byte is owned, the frame's bytes are not, so the flag lies outside the frame *)
assert (HFLsep : FL + 1 <= F \/ F + 128 <= FL).
{ destruct (Z.lt_ge_cases FL F) as [Hlt|Hge]; [left; lia|].
  destruct (Z.lt_ge_cases FL (F + 128)) as [Hlt|Hge2]; [|right; lia].
  exfalso. destruct (HFpres FL ltac:(lia)) as (_ & Hno). exact (Hno HFLown). }
(* the environment of the run *)
remember (Eimg (Ereg regs1 (sa7_extra FL regs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. rewrite HE. rewrite Eimg_low
    by (pose proof (u5_range r); unfold A_TEXT; lia). exact (ew_Ereg_nat regs1 _ n r Hn). }
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (sa7_extra FL regs) (Z_to_bv 64 0))
by (intros j Hj; rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (ERO : regs_ok E sr_atoms regs1) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (E8 : ew E 8 = w64 sp0) by (rewrite (EW 8%nat 8%bv eq_refl); exact Q8).
assert (E18 : ew E 18 = w64 F) by (rewrite (EW 18%nat 18%bv eq_refl); exact Q18).
assert (E25 : ew E 25 = w64 (SHADOW_OFF + F / 8)) by (rewrite (EW 25%nat 25%bv eq_refl); exact Q25).
assert (E26 : ew E 26 = w64 F) by (rewrite (EW 26%nat 26%bv eq_refl); exact Q26).
assert (E32 : ew E 32 = w64 FL) by (exact (EX 0%nat ltac:(lia))).
assert (ESV : forall j r, nth_error sa_saved j = Some r -> ew E (33 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj.
  assert (Hjb : (j < length sa_saved)%nat) by (apply (proj1 (nth_error_Some sa_saved j)); rewrite Hj; discriminate).
  cbn [length sa_saved] in Hjb.
  replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia. rewrite (EX (Datatypes.S j) ltac:(lia)).
  cbn [sa7_extra nth].
  rewrite (nth_error_nth (map (fun r0 => getr regs (Z_to_bv 5 r0)) sa_saved) j (Z_to_bv 64 0)
    (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j sa_saved Hj)).
  reflexivity. }
assert (U8 : bv_unsigned (ew E 8) = sp0) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = F) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8)
by (rewrite E25; unfold w64; rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (U26 : bv_unsigned (ew E 26) = F) by (rewrite E26; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
clear HE.
(* the symbolic state at M4 *)
assert (HS : st_ok_pi SEGS VAL E (mkSS L_M4 sr_atoms sa7_regions None sa7_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + L_M4)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact ERO.
  - vm_compute. reflexivity.
  - unfold sa7_regions. repeat apply Forall_cons; [| | | | | apply Forall_nil].
    + unfold sa7_frame_lo, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U26. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
    + unfold sa7_frame_hi, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ F 120 8 (SOff 32 0) FL).
      * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * zside.
      * zside.
      * replace (F + 120) with (F + 128 - 8) by lia. exact (val_mem_of_rdword SEGS _ _ _ _ HFLPTR).
    + unfold sa7_shadow, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
    + unfold sa7_flag, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLpres.
    + unfold sa7_saved, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; [..|apply Forall_nil];
      (lazymatch goal with
       | |- context [YP09.mkChunk ?off (CVal 8 (SOff ?n 0))] =>
         let j := eval compute in (Z.to_nat ((- off - 8) / 8)) in
         apply (chunk_ok_val SEGS E _ sp0 off 8 (SOff n 0)
           (bv_unsigned (getr regs (Z_to_bv 5 (nth j sa_saved 0)))));
         [ cbn [sv_denot]; rewrite ?Z.add_0_r, !Z_to_bv_bv_unsigned;
           exact (ESV j (nth j sa_saved 0) eq_refl)
         | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth j sa_saved 0))));
           change (bv_modulus 64) with (2 ^ 64) in *; zside
         | zside
         | lazymatch goal with |- val_mem _ _ ?x _ _ =>
             replace x with (sp0 - 8 - 8 * Z.of_nat j) by (cbn [Z.of_nat]; lia) end;
           apply sa7_val_mem; exact (HFRAME j (nth j sa_saved 0) eq_refl) ]
       end).
  - unfold sa7_regions, sa7_frame_lo, sa7_frame_hi, sa7_shadow, sa7_flag, sa7_saved.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U8, U18, U25, U26, U32. unfold SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sa7_facts, facts_ok.
    cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U18, U26. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; first [exact I | exact HF32 | lia]. }
(* the run: the poison, the magic word, the pruned branch, the shadow bytes, the release, the restores *)
paj_run_flag_sh RUNF HS HJ.
- lia.
- (* every byte the run writes is the frame's, its shadow's or the flag's *)
  intros a (r & Hin & Hr). unfold sa7_regions in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  unfold sa7_frame_lo, sa7_frame_hi, sa7_shadow, sa7_flag, sa7_saved in Hr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  + rewrite U26 in Hr. left. right. right. right. left. exists 1, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFB.
    try (change (frame_addr lyc 1 pos) with F). lia.
  + rewrite U18 in Hr. lia.
  + rewrite U25 in Hr. left. right. right. right. left. exists 1, pos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd].
    change (fs_frame_bytes 1 / 8) with 16.
    try (change (frame_addr lyc 1 pos) with F). lia.
  + rewrite U32 in Hr. right. lia.
  + rewrite U8 in Hr. lia.
- (* the flag byte is zero after the run *)
  intros msr HSm.
  destruct (st_ok_mem_ok SEGS E _ _ HSm) as (_ & HFA & _).
  rewrite Forall_forall in HFA.
  specialize (HFA (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))])
    ltac:(vm_compute; tauto)).
  pose proof (field_of_region_any (segs := SEGS) E (ms_mem msr) 32 FL
    [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1%N (SLit 0) HFA U32
    ltac:(left; reflexivity) ltac:(cbn; lia)) as Hv.
  pose proof (Hv 0%nat ltac:(cbn; lia)) as Hb.
  lazymatch type of Hb with _ = Some ?y =>
    replace y with (Z_to_bv 8 0) in Hb by (vm_compute; reflexivity) end.
  replace (FL + 0 + Z.of_nat 0) with FL in Hb by (cbn [Z.of_nat]; lia).
  exact Hb.
- (* after the release: the restores and the return *)
  cbn [ms_mem mkst] in HF, HFr, HG.
  prreg HS (1%bv : bv 5) P1.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
  prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prreg HS (27%bv : bv 5) P27.
  (* the bytes outside the frame's first word, its shadow and the flag byte are the ones M4 left *)
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (UN : forall a, 0 <= a < 2 ^ 64 ->
    ~ (F <= a < F + 8) -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) -> a <> FL ->
    aview SEGS (w_H Wc) (ms_mem msx) a = aview SEGS (w_H Wc) memc a) end.
  { intros a Ha Hf Hs Hfl.
    refine (kept_of_frame (segs := SEGS) E sa7_regions (w_H Wc) memc _
      (fun x => (F <= x < F + 8) \/ (SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 16) \/ x = FL)
      HFr _ a Ha _).
    - intros b wlo whi x Hwin Hx. vm_compute in Hwin.
      repeat (destruct Hwin as [Hq | Hwin];
        [injection Hq as <- <- <-; cbn [base_val] in Hx;
         first [ rewrite U26 in Hx; left; lia
               | rewrite U25 in Hx; right; left; lia
               | rewrite U32 in Hx; right; right; lia
               | rewrite U18 in Hx; lia
               | rewrite U8 in Hx; lia ] |]).
      destruct Hwin.
    - intros [Hq | [Hq | Hq]]; [exact (Hf Hq) | exact (Hs Hq) | exact (Hfl Hq)]. }
  eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  (* the post: apost_base at this stage's FP state is apost_baseF there (PaFx.v, fx' := fx) *)
  unfold sa_final. apply (apost_baseF_of_base SEGS). unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?mf _) ?mdf = _ /\ _ =>
    exists lyc, (stack_free_state 1 pos Sc), rg, mf, mdf end.
  pose proof P1 as A1. change 33%nat with (33 + 0)%nat in A1. rewrite (ESV 0%nat 1 eq_refl) in A1.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) in A1 by (apply bv_eq; vm_compute; reflexivity).
  split; [cbn [ms_regs]; rewrite A1, Hra; reflexivity|].
  split; [eapply ajournal_materialize; first [exact HJ | assumption]|].
  split.
  { apply aregs_preserved_eqs.
    - rewrite P2, E8. unfold sp0, spZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - rewrite P3, (EW 3%nat 3%bv eq_refl), Q3, Hgp. reflexivity.
    - rewrite P4, (EW 4%nat 4%bv eq_refl), Q4, Htp. reflexivity.
    - rewrite P8; change 34%nat with (33 + 1)%nat; rewrite (ESV 1%nat 8 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P9; change 35%nat with (33 + 2)%nat; rewrite (ESV 2%nat 9 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P18; change 36%nat with (33 + 3)%nat; rewrite (ESV 3%nat 18 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P19; change 37%nat with (33 + 4)%nat; rewrite (ESV 4%nat 19 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P20; change 38%nat with (33 + 5)%nat; rewrite (ESV 5%nat 20 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P21; change 39%nat with (33 + 6)%nat; rewrite (ESV 6%nat 21 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P22; change 40%nat with (33 + 7)%nat; rewrite (ESV 7%nat 22 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P23; change 41%nat with (33 + 8)%nat; rewrite (ESV 8%nat 23 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P24; change 42%nat with (33 + 9)%nat; rewrite (ESV 9%nat 24 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P25; change 43%nat with (33 + 10)%nat; rewrite (ESV 10%nat 25 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P26; change 44%nat with (33 + 11)%nat; rewrite (ESV 11%nat 26 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity.
    - rewrite P27; change 45%nat with (33 + 12)%nat; rewrite (ESV 12%nat 27 eq_refl);
      f_equal; apply bv_eq; vm_compute; reflexivity. }
  (* sa_postQ, carried from M4 *)
  unfold sa_postQ in POSTQ |- *. cbv zeta in POSTQ |- *.
  destruct POSTQ as (R' & O' & q & Hm & Hq10 & Hq4096 & HREP & HO1 & HO2 & HO3 & HqIn & Hqfresh & HqNot & HSTR & HBB
    & HMLE).
  exists R', O', q.
  assert (Eab : ablocks B lyc (stack_free_state 1 pos Sc) = ablocks B lyc Sc)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  assert (HFIELDS : forall pn, In pn O' -> In pn (ablocks B lyc Sc) /\ 1 <= snd pn /\
    iv_apart (fst pn) (snd pn) A_G_REC REC_SIZE /\ iv_apart (fst pn) (snd pn) A_REC_SPILL SC_SIZE).
  { pose proof (rec_repA_fields B HB LAWS _ _ _ _ _ HREP) as HF9.
    do 8 destruct HF9 as (_ & HF9). exact HF9. }
  assert (HOin : forall p n, In (p, n) O' -> In (p, n) (ablocks B lyc Sc))
    by (intros p n Hpn; exact (proj1 (HFIELDS (p, n) Hpn))).
  (* the bytes of a live block are kept *)
  assert (HKEEP : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n ->
    aview SEGS (w_H Wc) (ms_mem ms) (p + i) = aview SEGS (w_H Wc) memc (p + i)).
  { intros p n i Hpn Hi.
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hpn)
      as (_ & Hp4096 & Hpceil & Hpapp & Hpb & _).
    destruct (Hpb (p + i) ltac:(lia)) as (_ & Hpno).
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 1 pos HAR Hpn Hin1) as Hdbf.
    unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. rewrite HFB in Hdbf.
    unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Hpapp. cbn [fst snd] in Hpapp.
    apply UN; [lia | lia | unfold SHADOW_OFF; lia | intros Heq; apply Hpno; rewrite Heq; exact HFLown]. }
  (* the bytes of the image are kept *)
  assert (HKIMG : forall a, in_img SEGS a -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
  { intros a Himg. pose proof (pa_img_range a Himg) as Hr.
    apply UN; [lia | | unfold SHADOW_OFF; lia |].
    - intros Hc. destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
        ltac:(right; left; exists 1, pos; split; [exact Hin1 | rewrite HFB; lia])) as (_ & Hni).
      exact (Hni Himg).
    - intros Heq. destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
        ltac:(right; right; exists 1, pos; split; [exact Hin1 | exact Heq])) as (_ & Hni).
      exact (Hni Himg). }
  split; [exact Hm|].
  split; [rewrite P10, (EW 10%nat 10%bv eq_refl); exact Hq10|].
  split; [exact Hq4096|].
  split.
  { refine (rec_repA_kept B HB LAWS _ _ _ _ _ _ _ _ HREP _ _ _).
    - intros a Hrec. apply HKIMG. exact (sa7_rec_img a Hrec).
    - intros p n i Hpn Hi. apply (HKEEP p n i (HOin p n Hpn)).
      pose proof (req_size_pos n ltac:(pose proof (proj1 (proj2 (HFIELDS (p, n) Hpn))); cbn [snd] in *; lia))
        as (_ & Hle). lia.
    - intros pn Hpn. rewrite Eab. exact (proj1 (HFIELDS pn Hpn)). }
  split; [exact HO1|].
  split; [rewrite Eab; exact HO2|].
  split; [rewrite Eab; exact HO3|].
  split; [rewrite Eab; exact HqIn|].
  split; [exact Hqfresh|]. split; [exact HqNot|].
  split.
  { destruct HSTR as (HSb & HSnz). split; [|exact HSnz].
    intros j Hj. rewrite <- (HSb j Hj).
    apply (HKEEP q (Z.of_nat (length (snd (sup_add_m R uri id placement client))) + 1) (Z.of_nat j)).
    - exact HqIn.
    - rewrite length_app in Hj. cbn [length] in Hj.
      pose proof (req_size_pos (Z.of_nat (length (snd (sup_add_m R uri id placement client))) + 1)
        ltac:(lia)) as (_ & Hle). lia. }
  (* the release changes the side-stack state (st_fs), not the chunks: the live bytes are those of M4 *)
  split; [exact HBB|].
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). exact HMLE.
Qed.
End e.
End f.
End d.
