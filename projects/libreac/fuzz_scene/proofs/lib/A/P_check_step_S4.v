(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and addresses changed; 145 of its 210 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/P_check_step_S0.v; 144 of its 196 lines of code are new or changed and 158 lines of the source are left out. *)
(* Segment S4 of the ASan walk of check_step in fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026):
   0x83570 .. 0x836f0 (ret). The re-poison run (0x83570-0x835a0), the frame magic (0x835ac), `beqz s2` decided from
   the fake frame (s2 = F >= 4096), the 32 x 0xf5 inline release (0x835b4-0x83634) and the flag clear `ld a0,0xf8(s2);
   sb zero,0(a0)` (0x83638-0x8363c) through aj_flag_store_pi (A/Prog/SceneFrame.v:459), giving own = [] and
   stack_free_state 2 fpos; the jump over the dead real-frame unpoison (0x83640 -> 0x836b4), the epilogue loads from
   the 13 saved slots and the `ret` to the entry ra (paj_ret_at); the post is apost_base with ablocks unchanged
   (blocks_stack_free_state, YG01.v:476). Donor: cgif exitN (A/ACk2.v:319-344).
   The symbolic state at 0x83570 (pc offset AF_check_step + 0x3d4): atoms 0..31 are the cut's registers, atoms 32..44
   the entry values of ra, s0, s1, s2 .. s11 (cs_saved_regs, the slots at sp0 - 8 - 8 j), atom 45 the flag address.
   Regions: the flag byte (atom 45), the frame's 32 shadow bytes (s9, atom 25), the frame's header and flag word (s2,
   atom 18; s10 is pinned to atom 18) and the saved slots below s0 = sp0 (atom 8). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import YC1g YC4b.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import P_check_step_frame P_check_step_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The symbolic state at 0x83570 (AF_check_step + 0x3d4). *)
Definition S4_PC : Z := AF_check_step + 0x3d4.
Definition s4_stack_chunk (j : nat) : YP09.chunk := YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)).
Definition s4_regions : smem :=
[ YP09.mkRegion (Some 45%nat) 0 1 0 1 [];
  YP09.mkRegion (Some 25%nat) 0 32 0 32 [];
  YP09.mkRegion (Some 18%nat) 0 256 0 8 [YP09.mkChunk 248 (CVal 8 (SOff 45 0))];
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0 (map s4_stack_chunk (seq 0 13)) ].
Definition s4_facts : facts := mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition ss_s4 : sstate := mkSS S4_PC sr_atoms s4_regions None s4_facts.
Definition s4_extra (regs : bvmap 5 word) (fl : Z) : list word :=
map (fun r => getr regs (Z_to_bv 5 r)) cs_saved_regs ++ [Z_to_bv 64 fl].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Section h.
Variable B : asyms.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* relocated laws and the glue's bindings (cgif A/ACk1.v:64-74, :82; ScenePaLib.v:307, SceneFrame.v:96). *)
(* LAWS and SMP are theorems, not hypotheses (an internal review, CHECKSTEP-REVIEW item R4): AR_laws_ok (Reusable/YG0q.v:803) and
   the model law ml_stack_malloc_progress (YG0d.v:520-521). The UAR flag reads 1 in every AR state by
   al_const (AR_const_law, YG0d.v:461-467), so no flag hypothesis is taken. *)
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Lemma cs_S4 : CS_S4_stmt SK B.
Proof.
unfold CS_S4_stmt.
intros ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 [HPRE0 HFR].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
destruct HPRE0 as (HPRE & Hal32 & Htop32 & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HFR as (HJ & Hablk & Hflagw & Hsaved & Q2 & Q3 & Q4 & Q8 & Q18 & Q25 & Q26 & Q27).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
pose proof HJ as (HAR1 & _ & _ & _ & _ & Hfrs1 & _).
assert (Hin1 : In (CS_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR1 Hin1) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR1 Hin1) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ _ _ HAR1 Hin1) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLceil)).
change (fs_frame_bytes CS_CID) with 256 in *. change (256 / 8) with 32 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
remember (frame_addr ly1 CS_CID fpos) as F eqn:EF.
remember (flag_addr ly1 CS_CID fpos) as FL eqn:EFL.
assert (HF8 : 8 * (F / 8) <= F < 8 * (F / 8) + 8)
by (pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
(* the environment: atoms 0..31 the cut's registers, 32..44 the saved values, 45 the flag address *)
remember (Eimg (Ereg regs1 (s4_extra regs FL))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = getr regs (Z_to_bv 5 (nth j cs_saved_regs 0))).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  do 13 (destruct j as [|j]; [reflexivity|]). lia. }
assert (E45 : ew E 45 = Z_to_bv 64 FL).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 (s4_extra regs FL) 13). }
assert (E3 : ew E 3 = getr regs 3%bv) by (rewrite (EE 3%nat 3%bv eq_refl); exact Q3).
assert (E4 : ew E 4 = getr regs 4%bv) by (rewrite (EE 4%nat 4%bv eq_refl); exact Q4).
assert (E8 : ew E 8 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 8%nat 8%bv eq_refl); exact Q8).
assert (E18 : ew E 18 = Z_to_bv 64 F) by (rewrite (EE 18%nat 18%bv eq_refl); exact Q18).
assert (E25 : ew E 25 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (rewrite (EE 25%nat 25%bv eq_refl); exact Q25).
assert (UF : bv_unsigned (ew E 18) = F) by (rewrite E18; apply unsigned_lit_small; lia).
assert (UFL : bv_unsigned (ew E 45) = FL) by (rewrite E45; apply unsigned_lit_small; lia).
assert (USH : bv_unsigned (ew E 25) = SHADOW_OFF + F / 8)
by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (USP : bv_unsigned (ew E 8) = spZ regs) by (rewrite E8; apply unsigned_lit_small; lia).
(* the flag byte lies outside the frame and its shadow: it is owned, they are not *)
assert (DFL_F : FL + 1 <= F \/ F + 256 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [?|?]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 256)) as [?|?]; [|right; lia].
  exfalso. exact (proj2 (HFpres FL ltac:(lia)) HFLo). }
assert (DFL_SH : FL + 1 <= SHADOW_OFF + F / 8 \/ SHADOW_OFF + F / 8 + 32 <= FL).
{ destruct (Z_lt_ge_dec FL (SHADOW_OFF + F / 8)) as [?|?]; [left; lia|].
  destruct (Z_lt_ge_dec FL (SHADOW_OFF + F / 8 + 32)) as [?|?]; [|right; lia].
  exfalso. pose proof (proj2 (HFSpres (FL - (SHADOW_OFF + F / 8)) ltac:(lia))) as Hn.
  unfold shadow_addr in Hn. replace (SHADOW_OFF + F / 8 + (FL - (SHADOW_OFF + F / 8))) with FL in Hn by lia.
  exact (Hn HFLo). }
(* the symbolic state at 0x83570, s10 pinned to s2's atom *)
assert (HS : st_ok_pi SEGS VAL E (mkSS S4_PC (sr_set sr_atoms 26%bv (SOff 18 0)) s4_regions None s4_facts)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + S4_PC)) mem1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
  apply (ast_ok_pi_set_reg_fp E ss_s4 _ 26%bv (SOff 18 0)); [| reflexivity | cbn [sv_denot]; rewrite UF, Z.add_0_r; exact (eq_sym Q26)].
  unfold ss_s4. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold s4_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite UFL. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLp.
    + rewrite USH. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). pose proof (proj1 (HFSpres o ltac:(lia))) as Hp.
      unfold shadow_addr in Hp. exact Hp.
    + rewrite UF. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))). }
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ F 248 8 (SOff 45 0) FL).
      * cbn [sv_denot]. rewrite UFL, Z.add_0_r. reflexivity.
      * change (8 * Z.of_N 8) with 64. lia.
      * lia.
      * replace (F + 248) with (F + 256 - 8) by lia. exact (val_mem_of_rdword SEGS (w_H W1) mem1 _ _ Hflagw).
    + rewrite USP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj. unfold s4_stack_chunk.
      apply (chunk_ok_val SEGS E _ (spZ regs) (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
        (bv_unsigned (getr regs (Z_to_bv 5 (nth j cs_saved_regs 0))))).
      * cbn [sv_denot]. rewrite (EX j) by lia. rewrite Z.add_0_r. reflexivity.
      * pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth j cs_saved_regs 0)))) as Hr.
        change (bv_modulus 64) with (2 ^ 64) in Hr. change (8 * Z.of_N 8) with 64. lia.
      * lia.
      * replace (spZ regs + (-8 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
        exact (val_mem_of_rdword SEGS (w_H W1) mem1 _ _ (Hsaved j ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold s4_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UFL, USH, UF, USP.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; lia.
  - split; [|split; exact I].
    cbn [s4_facts f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite UF, Z.pow_0_r, Z.mod_1_r. lia. }
clear HE.
unfold cfg_at.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcw _ _) _) _ =>
  replace pcw with (Z_to_bv 64 (BASE + S4_PC)) by (unfold S4_PC, CS_PC4, A_check_step; rewrite Z.add_assoc; reflexivity) end.
pose proof (aj_flag_store_pi (PL := PL_scene) (PI := PI) B LAWS ML ASF FFL) as RUNF.
paj_run_flag_sh RUNF HS HJ.
- unfold CS_CID. lia.
- intros a (r & Hin & Hr). cbn [ss_mem] in Hin. unfold s4_regions in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  + right. rewrite UFL in Hr. rewrite <- EFL. lia.
  + left. right. right. right. exists CS_CID, fpos. split; [left; reflexivity|]. right.
    unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CS_CID / 8) with 32.
    rewrite USH in Hr. lia.
  + left. right. right. right. exists CS_CID, fpos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CS_CID) with 256. rewrite UF in Hr. lia.
  + rewrite USP in Hr. lia.
- intros msr HSr.
  pose proof (st_ok_pi_region_nth E _ msr 0 _ HSr eq_refl) as HR.
  pose proof (field_of_region E (ms_mem msr) 45 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR UFL
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  rewrite <- EFL. rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(cbn; lia)) as V0.
  cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0.
- lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into msF end.
  eapply (paj_ret_at (PL := PL_scene) (PI := PI) W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros matF.
  unfold cs_post, apost_base. cbv beta.
  lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
    exists ly1, (stack_free_state CS_CID fpos S1), rg, mm, mdx end.
  split; [|split; [|split]].
  + f_equal. f_equal.
    prreg HS (1%bv : bv 5) R1. rewrite R1.
    replace (ew E 32) with (getr regs 1%bv) by (symmetry; exact (EX 0%nat ltac:(lia))).
    exact Hra.
  + apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
  + apply aregs_preserved_eqs;
    lazymatch goal with |- getr _ ?r = _ =>
      let Hr := fresh "Hr" in prreg HS r Hr; rewrite Hr;
      first
      [ lazymatch goal with |- ew E ?n = _ =>
          let j := eval cbv in (n - 32)%nat in exact (EX j ltac:(lia)) end
      | exact E3 | exact E4
      | rewrite E8; unfold spZ; apply Z_to_bv_bv_unsigned
      | lazymatch goal with |- ?g => idtac "REGFAIL" g end; fail ]
    end.
  + exact Hablk.
Qed.
End h.
End f.
End d.
