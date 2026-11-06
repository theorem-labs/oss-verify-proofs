(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: chain_words' walk on the ASan build of plugin-hostd/fuzz_command, segment S1
   (chain_words_d.v cw_S1P): from the entry (0x8dfd4) through __asan_stack_malloc_3 (0x8e044) to the refusal cut KR
   (0x8e278) or the first-check cut KC (0x8e1ec). In the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v (entry,
   aj_stack_malloc_atS, re-seat) with the entry seed of lib/A/Prog/numberE.v: a run to the call, the call, a re-seat
   that keeps the three stack regions and adds the frame (the call's a0) and its shadow (the alias of
   (s8 >> 3) + s7), a plain run through the 88 shadow stores to the branch on ntok < 3, and the cut facts (cw_pc)
   read back from the symbolic state at the cut. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s1.v, with its module paths and module names changed; 272 of its 383 lines of code are new or changed and 455 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): segment S00 of the walk of
   the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), file group _s10: from the entry to the
   cut K84eb8 (0x84eb8), the statement lt_seg_S00_stmt of LLVMFuzzerTestOneInput_defs.v.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; checker (fresh, read-only): CONFIRM; none: written new)

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/chain_words_s1.v (origin/ossv/recipes 501c0d516c69, the class-3
   side-stack frame: a run to the call, aj_stack_malloc_atS, a re-seat that keeps the stack regions and adds the
   frame and its shadow, a plain run through the shadow stores) with the entry of fuzz_command's
   lib/A/Prog/LLVMFuzzerTestOneInput_s10.v (lt_base unpacked, the size test refuted by n < 2 ^ 26, the
   continuation applied at the entry's FP state). The code (dis:2-98 of the neutral excerpt):
   - 0x84d34 .. 0x84da8, one token run: the frame (sp -= 320, the zero word, ra and s0 .. s11 saved at sp + 312 ..
     sp + 216), s0 := sp + 320, sp := s1 := (sp - 320) & -32 (the alias of the entry state), s4 := n, s8 := p, the
     flag cell through its .got word (the record's constant 1, so beqz a2 at 0x84da0 falls through), t0 := the
     shadow base through its .got word, spilled to 176(s1), a0 := 288 and the jal of frame_alloc_3;
   - frame_alloc_3 by aj_stack_malloc_atS (SM3; the class-3 count is 0 < 2048 by frames S = []);
   - 0x84dac .. 0x84eb4, one plain run after the re-seat: t0 reloaded from 176(s1) (the kept stack region's chunk),
     a6 := a7 := FR, bnez a6 decided by the frame's HPTR fact (the real-stack probe loop 0x84dc4 .. 0x84ddc dead),
     208(s1) := FR, the three header words (the magic, the description A_OBJ 2, the function A_OBJ 3), s5 := the
     frame's shadow address (the alias of shadow_decl_ok), the 36 shadow stores, a1 := n >> 26;
   - bnez a1 at 0x84eb4: its taken arm (to the release at 0x85c44) refuted by lt_base's n < 2 ^ 26, its other arm
     run to 0x84eb8 and closed by LTA_K84eb8 at the frame position frame_alloc_3 gave. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YI09 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require LLVMFuzzerTestOneInput_s02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the walk's hypotheses: the listing record of the runtime cells and wrappers (PALib, PALibF), the image facts
   lt_img needs at a later reader (s10_img) and the record's symbols (BSYM, AR's stack-protector cells),
   frame_alloc_3's contract, the model and meter laws *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
(* stack_malloc_progressP is the model's own law *)
Let SMP : stack_malloc_progressP B := fun s cid HW Hc Hn => ml_stack_malloc_progress _ ML s cid HW Hc Hn.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.

Theorem lt_seg_S00 : lt_seg_S00_stmt B MT.
Proof.
intros HK cx HBASE HFRM.
destruct cx as [ly S W regs mem md ch p n pl j fpos0].
pose proof HBASE as HB0. unfold lt_base in HB0.
cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_p x_n x_pl x_j] in HB0.
destruct HB0 as (HPRE & HSTP & HRO & HIM & H10 & H11 & Hpn & Hlen & HG8 & Hfr0 & HGI & HEVM & HLIVE & HMO).
cbn [x_W x_regs x_mem x_md x_ly x_S].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstkd & Hpres0 & Hch0 & HQT0).
pose proof Hstkd as (Hal16 & Hsp00 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
destruct (s10_sp1_facts (spZ regs) Hal16) as (Hs1al & Hs1).
assert (HS1b : spZ regs - 336 <= s10_sp1 (spZ regs) <= spZ regs - 320) by (destruct Hs1 as [Hq | Hq]; lia).
assert (HS1R : 0 <= s10_sp1 (spZ regs) < 2 ^ 64) by lia.
pose proof (s10_entry B TL TLF W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B STK_LLVMFuzzerTestOneInput (ltoi_PG longlA) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (s10_extra (spZ regs) (as_uar_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j0, (j0 < 3)%nat -> ew E (32 + j0) = nth j0 (s10_extra (spZ regs) (as_uar_cell B)) (Z_to_bv 64 0))
  by (intros j0 Hj; rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth s10_extra map] in E32, E33, E34. clear EX HE.
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Usp1 : bv_unsigned (ew E N_SP1) = spZ regs + (s10_sp1 (spZ regs) - spZ regs))
  by (rewrite E33, (unsigned_lit_small _ HS1R); lia).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
unfold cfg_at. change (w64 (BASE + AF_LLVMFuzzerTestOneInput)) with (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)).
(* 0x84d34 .. 0x84da8: the frame and the 13 saves, s0, the realigned sp and s1, s4 := n, s8 := p, the flag cell
   (1: beqz a2 falls through) and the shadow base (spilled to 176(s1)), a0 := 288, the jal of frame_alloc_3 *)
paj_run_tok RUN HS HJ SHOK s10_span.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack_off with (n := N_SP1) (d := s10_sp1 (spZ regs) - spZ regs);
  [reflexivity | exact Usp1 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
(* the prologue wrote only its own stack window *)
lazymatch type of HS with context [restrict _ ?ms1] =>
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_LLVMFuzzerTestOneInput <= a < spZ regs) ->
  rdW W (ms_mem ms1) a = rdW W mem a) end.
{ intros a Ha Hn. apply (kept_of_frame E _ (w_H W) mem _ (fun x => spZ regs - STK_LLVMFuzzerTestOneInput <= x < spZ regs) HFr1);
  [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp, ?Usp1 in Hx; cbv beta; lia |]).
  destruct Hin. }
(* the call of frame_alloc_3 (0x84da8) *)
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
pose proof (palf_sm B TLF 3 ltac:(cbn; tauto)) as HSM3. change (cs_stack_malloc 3) with SS___asan_stack_malloc_3 in HSM3.
rewrite HSM3.
assert (Ho16 : (s10_sp1 (spZ regs) - spZ regs) mod 16 = 0)
  by (destruct Hs1 as [Hq | Hq]; rewrite Hq; [replace (spZ regs - 320 - spZ regs) with (-320) by lia
  | replace (spZ regs - 336 - spZ regs) with (-336) by lia]; reflexivity).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 3 (SM3 fx) ltac:(lia) W (ms_regs ms) (ms_mem ms)
  STK_LLVMFuzzerTestOneInput (spZ regs) (ltoi_PG longlA) ly S W mem md [] ly S md1 0 (s10_sp1 (spZ regs) - spZ regs) _ HJ).
  - unfold spZ at 1. rewrite R2. exact Usp1.
  - exact Ho16.
  - lia.
  - change ESTACK with 4096. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp0.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp0.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Hfr0. vm_compute. reflexivity. }
cbv beta. clear R1 R2 R3 R4 SHOK HSM3.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag
  & HKC & HJ1 & (fS2 & ES2)).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (3, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (al_flag _ _ LAWS _ _ _ _ _ 3 fpos HAR2 Hfin2) as (HFLp & HFLo & HFLapp & HFLce).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes 3) with 512 in *. change (512 / 8) with 64 in HFSpres.
set (F := frame_addr ly 3 fpos) in *. set (FL := flag_addr ly 3 fpos) in *.
assert (HFLr : 0 <= FL < 2 ^ 64) by (destruct HFLapp as [Hq _]; lia).
assert (HFrg : 0 <= F < 2 ^ 64) by lia.
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
(* re-seat after the call: the three stack regions are kept (the callee's window is below s1) *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_aj SEGS B) with (sp := spZ regs); [exact HKC | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B) with (sp := spZ regs); [exact HKC | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B) with (sp := s10_sp1 (spZ regs));
    [exact HKC | exact HJ2 | rewrite E33; exact (unsigned_lit_small _ HS1R) | lia | lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
pose proof (st_ok_pi_havoc_hi 1040 _ _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc (havoc E 1024 (map (getr regs2) CLOB)) 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Ev eqn:HEv in HS.
assert (EvE : forall k, (k < 1024)%nat -> ew Ev k = ew E k) by (intros k Hk; rewrite HEv, !ew_havoc_old by lia; reflexivity).
assert (V2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite EvE by lia; exact Usp).
assert (V33 : bv_unsigned (ew Ev 33) = s10_sp1 (spZ regs))
  by (rewrite EvE by lia; rewrite E33; exact (unsigned_lit_small _ HS1R)).
assert (V32 : ew Ev 32 = Z_to_bv 64 SB) by (rewrite EvE by lia; exact E32).
assert (V1028 : ew Ev 1028 = Z_to_bv 64 F).
{ rewrite HEv, ew_havoc_old by lia. change 1028%nat with (1024 + 4)%nat.
  rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia). exact Ha0. }
assert (V1040 : ew Ev 1040 = Z_to_bv 64 FL)
  by (rewrite HEv; exact (ew_havoc_new _ 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (V1041 : ew Ev 1041 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HEv; exact (ew_havoc_new _ 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEIv : img_env VAL A_LIM Ev)
  by (rewrite HEv; apply img_env_havoc_hi; [apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia] | unfold A_LIM; lia]).
assert (UF : bv_unsigned (ew Ev 1028) = F) by (rewrite V1028; exact (unsigned_lit_small _ HFrg)).
assert (USh : bv_unsigned (ew Ev 1041) = SB + F / 8) by (rewrite V1041; apply unsigned_lit_small; unfold SB; lia).
(* the frame's shadow address s5 = (a7 >> 3) + t0 is the atom 1041 (t0 is the shadow base reloaded from 176(s1)) *)
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 1028 32 1041 F SB V1028 HFrg V32 V1041)) as HS3.
clear HS. rename HS3 into HS.
(* the frame (atom 1028, its flag pointer at +504 the atom 1040) and its shadow (atom 1041) *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
assert (RFR : region_ok SEGS Ev (ms_mem msx) (fframe_region 1028 1040 3 []));
[ unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
  change (fs_frame_bytes 3) with 512; rewrite UF;
  split; [lia|]; split; [lia|]; split;
  [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
  | apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS Ev _ F (512 - 8) 8 (SOff 1040 0) FL);
    [ cbn [sv_denot]; rewrite V1040, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
    | replace (F + (512 - 8)) with (F + 512 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag) ] ]
| ];
assert (DFR : all_disjoint Ev (fframe_region 1028 1040 3 []) (ss_mem ssx));
[ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  unfold fframe_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  change (fs_frame_bytes 3) with 512; rewrite UF, V2, V33; repeat split; lia
| ] end.
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 1028 1040 3 []) HS eq_refl RFR DFR) as HS3. clear HS RFR DFR. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
assert (RSH : region_ok SEGS Ev (ms_mem msx) (fshadow_region 1041 3 0 64 []));
[ unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  change (fs_frame_bytes 3 / 8) with 64; rewrite USh;
  split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
  [ intros o Ho; apply (apresent_writable SEGS); pose proof (proj1 (HFSpres o ltac:(lia))) as Hq;
    unfold shadow_addr, SHADOW_OFF in Hq; unfold SB; exact Hq
  | apply Forall_nil ]
| ];
assert (DSH : all_disjoint Ev (fshadow_region 1041 3 0 64 []) (ss_mem ssx));
[ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  unfold fshadow_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  change (fs_frame_bytes 3 / 8) with 64; rewrite USh, UF, V2, V33; unfold SB;
  destruct HFapp as (HFa1 & [HFa2 | (HFa3 & HFa4)]); unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia
| ] end.
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 1041 3 0 64 []) HS eq_refl RSH DSH) as HS3. clear HS RSH DSH. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
(* the frame is a 32-aligned side-stack address (bnez a6 at 0x84dc0 is taken) *)
pose proof (st_ok_pi_add_fact Ev _ _ 1028 (HPTR 5) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite UF; change (2 ^ 5) with 32; lia)) as HS3.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
clear HJ HJ1.
(* what the code below may write: the frame, its shadow, and the three stack regions *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
assert (AWR2 : awr_ok SEGS B Ev (ss_mem ssx) STK_LLVMFuzzerTestOneInput (spZ regs) (ltoi_PG longlA) (ablocks B ly S)
  (ablocks B ly S2) (frames S) ly [(3, fpos)]) end.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen with (n := 1041%nat) (b := SB + F / 8); [reflexivity | exact USh | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 3, fpos. split; [left; reflexivity|].
    right. change (frame_addr ly 3 fpos) with F. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
    change (fs_frame_bytes 3 / 8) with 64. unfold SB in Ha. lia. }
  eapply awr_ok_cons_gen with (n := 1028%nat) (b := F); [reflexivity | exact UF | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 3, fpos. split; [left; reflexivity|].
    left. change (frame_addr ly 3 fpos) with F. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 3) with 512. lia. }
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact V2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact V2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack_off with (n := N_SP1) (d := s10_sp1 (spZ regs) - spZ regs);
  [reflexivity | rewrite V33; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_nil. }
(* 0x84dac .. 0x84eb4: t0 reloaded, a6 := a7 := FR (bnez a6 taken), 208(s1) := FR, the three header words, s5 := the
   frame's shadow address, the 36 shadow stores, a1 := n >> 26; the run stops at bnez a1 *)
paj_run_sh RUNP HS HJ2.
{ exact AWR2. }
rename HF into HF2, HFr into HFr2, HG into HG2.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md3 := mm) in *; clearbody md3 end.
cbn [ms_mem mkst] in HFr2.
lazymatch type of RUNP with forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
let why := eval vm_compute in (sym_step_pi tpi ssx) in
lazymatch why with PStop (SR_branch ?cc ?aa ?bb) =>
apply (BR Wx Ex ssx msx _ _ cc aa bb HS); clear HS; intros Hc HS end end end.
- (* bnez a1 taken (n >= 2 ^ 26, the early exit to 0x85c44): refuted by lt_base's n < 2 ^ 26 *)
  exfalso. rewrite branch_ne_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom Ev 11 n) in Hc by first [rewrite EvE by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11 | lia].
  rewrite !U_lit in Hc by lia.
  change (Z.land 26 63) with 26 in Hc.
  rewrite Z.shiftr_div_pow2 in Hc by lia. rewrite (Z.div_small n (2 ^ 26)) in Hc by lia.
  vm_compute in Hc. discriminate Hc.
- (* bnez a1 not taken: the cut K84eb8 *)
  paj_run_to_sh RUNTOP HS HJ2 LO_K84eb8.
  { lazymatch type of AWR2 with awr_ok _ _ _ ?rsA _ _ _ _ _ _ _ _ =>
      apply (s10_awr_skel _ _ _ rsA); [vm_compute; reflexivity | exact AWR2] end. }
  rename HF into HF3, HFr into HFr3, HG into HG3.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md4 := mm) in *; clearbody md4 end.
  cbn [ms_mem mkst] in HFr3.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msK end.
  (* the registers at the cut *)
  assert (RA : forall (r : bv 5) k, sr_get (ss_regs ltac:(lazymatch type of HS with st_ok_pi _ _ _ ?s _ => exact s end)) r = SOff k 0 ->
    getr (ms_regs msK) r = ew Ev k) by (intros r k Hr; exact (s10_reg_atom (w_H W) Ev _ msK r k HS Hr)).
  assert (G2 : getr (ms_regs msK) 2 = w64 (s10_sp1 (spZ regs)))
    by (rewrite (RA 2%bv 33%nat ltac:(vm_compute; reflexivity)), EvE by lia; exact E33).
  assert (G9 : getr (ms_regs msK) 9 = w64 (s10_sp1 (spZ regs)))
    by (rewrite (RA 9%bv 33%nat ltac:(vm_compute; reflexivity)), EvE by lia; exact E33).
  assert (G3 : getr (ms_regs msK) 3 = getr regs 3)
    by (rewrite (RA 3%bv 3%nat ltac:(vm_compute; reflexivity)), EvE, (EE 3%nat 3%bv eq_refl) by lia; reflexivity).
  assert (G4 : getr (ms_regs msK) 4 = getr regs 4)
    by (rewrite (RA 4%bv 4%nat ltac:(vm_compute; reflexivity)), EvE, (EE 4%nat 4%bv eq_refl) by lia; reflexivity).
  assert (G8 : getr (ms_regs msK) 8 = w64 (spZ regs))
    by (rewrite (RA 8%bv 2%nat ltac:(vm_compute; reflexivity)), EvE, E2 by lia; unfold w64, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (G5 : getr (ms_regs msK) 5 = w64 SHADOW_OFF)
    by (rewrite (RA 5%bv 32%nat ltac:(vm_compute; reflexivity)); exact V32).
  assert (G16 : getr (ms_regs msK) 16 = w64 F) by (rewrite (RA 16%bv 1028%nat ltac:(vm_compute; reflexivity)); exact V1028).
  assert (G17 : getr (ms_regs msK) 17 = w64 F) by (rewrite (RA 17%bv 1028%nat ltac:(vm_compute; reflexivity)); exact V1028).
  assert (G20 : getr (ms_regs msK) 20 = w64 n)
    by (rewrite (RA 20%bv 11%nat ltac:(vm_compute; reflexivity)), EvE, (EE 11%nat 11%bv eq_refl) by lia; exact H11).
  assert (G21 : getr (ms_regs msK) 21 = w64 (SB + F / 8)) by (rewrite (RA 21%bv 1041%nat ltac:(vm_compute; reflexivity)); exact V1041).
  assert (G24 : getr (ms_regs msK) 24 = w64 p)
    by (rewrite (RA 24%bv 10%nat ltac:(vm_compute; reflexivity)), EvE, (EE 10%nat 10%bv eq_refl) by lia; exact H10).
  clear RA.
  (* the regions at the cut: 0 the shadow, 1 the frame, 2 / 3 the stack below the entry sp, 4 the slots of s1 *)
  assert (RK : forall i r, nth_error (ss_mem ltac:(lazymatch type of HS with st_ok_pi _ _ _ ?s _ => exact s end)) i = Some r ->
    region_ok SEGS Ev (mrestrict (w_H W) (ms_mem msK)) r)
    by (intros i r Hi; exact (st_ok_pi_region_nth Ev _ (restrict (w_H W) msK) i r HS Hi)).
  lazymatch type of HS with st_ok_pi _ _ _ ?ssB _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  let r1 := eval vm_compute in (nth 1 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  let r3 := eval vm_compute in (nth 3 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  let r4 := eval vm_compute in (nth 4 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (RK 0%nat r0 ltac:(vm_compute; reflexivity)) as RSH;
  pose proof (RK 1%nat r1 ltac:(vm_compute; reflexivity)) as RFR;
  pose proof (RK 3%nat r3 ltac:(vm_compute; reflexivity)) as RST;
  pose proof (RK 4%nat r4 ltac:(vm_compute; reflexivity)) as RS1 end.
  clear RK.
  destruct RSH as (_ & _ & _ & CSH). destruct RFR as (_ & _ & _ & CFR).
  destruct RST as (_ & _ & _ & CST). destruct RS1 as (_ & _ & _ & CS1).
  cbn [YP09.r_base YP09.r_chunks base_val] in CSH, CFR, CST, CS1.
  rewrite USh in CSH. rewrite UF in CFR. rewrite V2 in CST. rewrite V33 in CS1.
  (* the bytes the code after the call did not write: outside the stack window, the frame and its shadow *)
  pose proof HKC as (HK1 & HK2 & HK3 & HK4 & _).
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_LLVMFuzzerTestOneInput <= a < spZ regs) -> ~ (F <= a < F + 512) ->
    ~ (SB + F / 8 <= a < SB + F / 8 + 64) -> rdW W (ms_mem msK) a = rdW W mem2 a).
  { intros a Ha N1 N2 N3.
    assert (HWZ : forall rs, windows rs = [(Some 1041%nat, 0, 64); (Some 1028%nat, 0, 512); (Some 2%nat, -320, -312);
      (Some 2%nat, -104, 0); (Some 33%nat, 176, 216)] ->
      forall b wlo whi x, In (b, wlo, whi) (windows rs) -> base_val Ev b + wlo <= x < base_val Ev b + whi ->
      (fun y => (spZ regs - STK_LLVMFuzzerTestOneInput <= y < spZ regs) \/ (F <= y < F + 512) \/ (SB + F / 8 <= y < SB + F / 8 + 64)) x).
    { intros rs Hw b wlo whi x Hin Hx. rewrite Hw in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?USh, ?UF, ?V2, ?V33 in Hx; cbv beta; lia |]).
      destruct Hin. }
    assert (HnZ : ~ (fun y => (spZ regs - STK_LLVMFuzzerTestOneInput <= y < spZ regs) \/ (F <= y < F + 512) \/
      (SB + F / 8 <= y < SB + F / 8 + 64)) a) by (cbv beta; intros [Hq|[Hq|Hq]]; contradiction).
    lazymatch type of HFr2 with frame_of _ ?rsA _ (mrestrict _ ?mB) =>
    lazymatch type of HFr3 with frame_of _ ?rsB _ _ =>
    rewrite (kept_of_frame Ev rsB (w_H W) mB (ms_mem msK) _ HFr3 (HWZ rsB ltac:(vm_compute; reflexivity)) a Ha HnZ);
    exact (kept_of_frame Ev rsA (w_H W) mem2 mB _ HFr2 (HWZ rsA ltac:(vm_compute; reflexivity)) a Ha HnZ) end end. }
  (* the image bytes the runtime does not own are the entry's *)
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    rdW W (ms_mem msK) a = rdW W mem a).
  { intros a Himg Hown Herr. pose proof (pa_img_range _ Himg) as HIR. unfold kImgEnd in HIR.
    pose proof (frm_off_imgP B ly S2 W mem2 md2 3 fpos HAR2 Hfin2) as HFoi. unfold off_img in HFoi.
    change (fs_frame_bytes 3) with 512 in HFoi. change (frame_addr ly 3 fpos) with F in HFoi.
    rewrite (K3 a); [| lia | lia | lia | unfold SB; lia].
    rewrite (HK3 a Himg Hown Herr). apply K1; lia. }
  pmkst HS.
  change (SRr SEGS W (cfg_at SEGS (BASE + LO_K84eb8) (ms_regs msK) (ms_mem msK) md4)
    (lt_post B MT (lt_setpos (mkLCX ly S W regs mem md ch p n pl j fpos0) fpos))).
  apply (HK fx (lt_setpos (mkLCX ly S W regs mem md ch p n pl j fpos0) fpos) ly S2 W (ms_regs msK) (ms_mem msK) md4 0
    HBASE HFRM).
  + (* lt_core *)
    split; [|split; [|split]].
    * (* the frame part *)
      unfold lt_frame. cbn [lt_setpos x_sp0 x_s1 x_fr x_fl x_sh x_fpos x_ly x_S x_W x_mem x_md x_regs].
      unfold LT_FRAME, LT_FCLS, LT_FLAGW. fold F FL.
      split; [exact HJ2|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|]. split; [exact G9|].
      split.
      { (* the 13 saved registers *)
        unfold lt_saved. cbn [x_sp0 x_regs]. intros i r Hi. unfold LT_SAVED in Hi.
        assert (ER : forall r0 : bv 5, ew Ev (Z.to_nat (bv_unsigned r0)) = getr regs r0).
        { intros r0. pose proof (bv_unsigned_in_range 5 r0) as Hr5. change (bv_modulus 5) with 32 in Hr5.
          rewrite EvE by lia. apply EE. rewrite Z2Nat.id by lia. reflexivity. }
        do 13 (destruct i as [|i];
          [ cbn [nth_error] in Hi; injection Hi as Hr; subst r;
            apply (s10_saved_one Ev (w_H W) (ms_mem msK) _ (spZ regs) regs _ _ CST);
            [ repeat first [left; reflexivity | right] | apply ER ]
          | ]).
        destruct i; cbn [nth_error] in Hi; discriminate Hi. }
      split.
      { (* the magic at FR + 0 *)
        eapply (s10_rd_chunk8 Ev (w_H W) (ms_mem msK) F 0 _ _ LT_HDR0 _ CFR);
        [ repeat first [left; reflexivity | right] | first [lia | rewrite Z.add_0_r; reflexivity]
        | vm_compute; reflexivity | unfold LT_HDR0; lia ]. }
      split.
      { (* the description at FR + 8 *)
        pose proof (pa_val_range (A_OBJ 2)) as Hv2.
        apply (s10_rd_chunk8 Ev (w_H W) (ms_mem msK) F 8 _ (SOff (A_OBJ 2) 0) _ _ CFR);
        [ repeat first [left; reflexivity | right] | reflexivity | | exact Hv2 ].
        cbn [sv_denot]. rewrite (HEIv (A_OBJ 2) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r. reflexivity. }
      split.
      { (* the function at FR + 16 *)
        pose proof (pa_val_range (A_OBJ 3)) as Hv3.
        apply (s10_rd_chunk8 Ev (w_H W) (ms_mem msK) F 16 _ (SOff (A_OBJ 3) 0) _ _ CFR);
        [ repeat first [left; reflexivity | right] | reflexivity | | exact Hv3 ].
        cbn [sv_denot]. rewrite (HEIv (A_OBJ 3) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Z.add_0_r. reflexivity. }
      split.
      { (* the flag byte's address at FR + 504 *)
        apply (s10_rd_chunk8 Ev (w_H W) (ms_mem msK) F 504 _ (SOff 1040 0) _ _ CFR);
        [ repeat first [left; reflexivity | right] | reflexivity | | exact HFLr ].
        cbn [sv_denot]. rewrite V1040, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      split.
      { (* the shadow base at 176(s1) *)
        apply (s10_rd_chunk8 Ev (w_H W) (ms_mem msK) (s10_sp1 (spZ regs)) 176 _ (SOff 32 0) _ _ CS1);
        [ repeat first [left; reflexivity | right] | reflexivity | | unfold SHADOW_OFF; lia ].
        cbn [sv_denot]. rewrite V32, unsigned_lit_small, Z.add_0_r by (unfold SB; lia). reflexivity. }
      { (* the 36 shadow bytes of the frame, every object out of scope *)
        pose proof (s10_zs_ok Ev (w_H W) (ms_mem msK) (SB + F / 8) _ (lt_fsh LFO0) 0 CSH ltac:(vm_compute; reflexivity)) as HZS.
        rewrite Z.add_0_r in HZS. exact HZS. }
    * (* the image facts: the code after the entry wrote no image byte the runtime does not own *)
      exact (s10_lt_img_kept B IMGS BSYM _ W (ms_mem msK) (rdW W mem) (proj1 HJ2) KIMG (conj HRO (conj HIM HGI))).
    * (* no block of the harness yet *)
      unfold lt_blocks, x_bl0. cbn [app x_ly x_S lt_setpos]. rewrite Eab. apply Permutation_refl.
    * (* nothing spent: the whole of EV_LTOI still to come; the frame's take is metered 0 *)
      unfold lt_bud. cbn [x_pl x_S lt_setpos].
      pose proof (LLVMFuzzerTestOneInput_s02.lt_nfiles_range pl) as Hnf.
      assert (N1 : 0 <= EV_LTOI pl) by (unfold EV_LTOI; lia).
      split; [lia|]. split; [exact N1|]. split; [lia|].
      split; [rewrite ES2; apply (mo_le_set_fs_r MT MTFL); exact (mle_start MT S MTL)|]. split; [lia|].
      rewrite Z.add_0_l. unfold XM_LTOI, LT_U. apply Z.le_refl.
  + exact G5.
  + exact G16.
  + exact G17.
  + exact G20.
  + exact G21.
  + exact G24.
Qed.
End e.
End f.
End d.
Print Assumptions lt_seg_S00.
