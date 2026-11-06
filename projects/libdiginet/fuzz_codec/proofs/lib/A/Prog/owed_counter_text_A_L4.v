(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_pin's ASan harness walk (LLVMFuzzerTestOneInput 0x806b4,
   fuzz_pin.asan sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16) from
   proofs/libreac/fuzz_knock/lib/A/APgMain0.v at origin/ossv/recipes 6ebe35ba632, with its module paths changed.
   rule 24: no function proved here alone; this is segment S0 of LLVMFuzzerTestOneInput's walk, whose top claim is
   lib/A/PPgMain.v.

   SEGMENT S0 ENTRY, pc 0x806b4 .. 0x807cc, ending at ss_H (0x807d0, lib/A/PPgMainSt.v). Every address was read from
   the pinned image bytes with capstone 5.0.7. The walk, with knock's line it follows:
   - 0x806b4-0x806f4: the 128-byte save frame (13 saves at [sp0-104, sp0)), s0 = sp0, `andi sp,sp,-0x20`; the first
     run stops at 0x806f8 (knock 0x7ef14); sp1 := 32 * ((sp0 - 128) / 32) into env slot 70 (knock -192).
   - the stack region is trimmed to the saves [sp0-104, sp0) (as knock), and region 70 = [s1+16, s1+24) is added
     for the one spill `sd s8,0x10(s1)` at 0x80758 (knock [16,88)).
   - 0x806f8-0x80724: the two GOT loads (0x99050 shadow base, 0x990a8 use-after-return option), s6 := SB, the
     option test `beqz a2` at 0x8071c decided by the option cell's SLit 1, a0 := 0x60, `jal 3ca58` at 0x80724
     (__asan_stack_malloc_1, class 1); the run stops at 0x3ca58 by SR_fetch.
   - the side-stack call through aj_stack_malloc_atS (lib/A/PPgMainCall.v) with class 1 and ASM1; its premise
     count_cid 1 (frames S) < fs_frames 1 is the call-site lemma pin_fs1_site.
   - the class-1 frame facts (F = frame_addr ly 1 fpos, 128 bytes, 16 shadow bytes, the flag address at F + 120),
     the atoms 75 / 87 / 88 and the alias SB + (F >> 3) = slot 88, as knock.
   - 0x80728-0x807c8: `bnez s2` decided by HPTR 5 on F (the real-stack path 0x8073c-0x80754 is never reached),
     `sd s8,0x10(s1)`, the frame header F[0..24) = 0x41B58AB3 / 0x1ffeb / 0x806b4, the 12 shadow bytes
     f1 x4, f8, f2 x3, f8, f3 x3 (0x80794-0x807c8).
   - 0x807cc `bnez a0` with a0 = n >> 26: split with SRr_sym_branch; the taken side (-> 0x80940) is refuted by
     n < 2 ^ 26 (atom 11); the fall-through runs to 0x807d0.
   - the join into ss_H (window 400) and the hand-off to the rest of the walk (RB).
   Section hypotheses: MTL TL LAWS ML ASM1 SMP FFL MTF and RB : rt_from B MT FP POST ss_H (INV_0 B MT 0). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/A/PPgMain0.v, with its module paths and numbers changed; 387 of its 446 lines of code are new or changed and 228 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/owed_counter_text_A_pre.v; 243 of its 287 lines of code are new or changed and 402 lines of the source are left out. *)
(* owed_counter_text at image A: one step of the first loop from the loop head 0x83f48 with n = 4 digits
   (owed_counter_text_A_Lt.v has the step's shape). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base owed_counter_text_A_Lt.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Section oc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis SEG7 : cdc_owed_seg7_specX tfibsegs B MT CA_RLO CA_RHI GLYPHA ROSTRS 0x8438c.

(* one step of the first loop from the loop head with n = 4 digits *)
Lemma oc_step4 : forall fuel,
  (forall n', (n' <= 8)%nat -> oc_from B MT GLYPHA ROSTRS (ss_L n') (INV_L n' fuel)) ->
  oc_from B MT GLYPHA ROSTRS (ss_Z 4) (INV_Z 4) ->
  oc_from B MT GLYPHA ROSTRS (ss_R 18446744073709551605) (INV_R 18446744073709551605) ->
  oc_from B MT GLYPHA ROSTRS (ss_L 4) (INV_L 4 (Datatypes.S fuel)).
Proof using MTL TL LAWS ML FFL SEG7.
intros fuel IHL HZ HR [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj pos] E ly3 S3 W3 ms3 md3
  Hpre Henv Hst Hinv HS.
pose proof Hpre as Hpre0. pose proof Hst as Hst0.
pose proof (fun sp' T' => oc_cimg_at B MT GLYPHA ROSTRS _ _ _ _ _ _ sp' T' Hpre Hst) as Hcimg3.
cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_q o_sg o_dt o_tb o_sj o_dj o_pos] in *.
unfold oc_pre, oc_n in Hpre; cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_q o_sg o_dt o_tb o_sj o_dj o_pos] in Hpre.
destruct Hpre as (HEN & H10 & Hcstr & Hcq & Hcsg & H11 & Hdsg & Hgsj & Hlsj & H12 & Hdt & Hdj & Hdsd & Hdqs & Hdqd & Hcimg & Hfr8).
pose proof HEN as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
unfold oc_env, oc_sp1, oc_F, oc_FL in Henv; cbn [o_regs o_lyc o_pos] in Henv.
destruct Henv as (HAE & E32 & E70 & E75 & E87 & E88).
unfold oc_st in Hst; cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_pos oc_E] in Hst.
destruct Hst as (HJ & HFRS & Hnin & HPERM & HMO & HIO & KT).
destruct Hinv as (i & s & dot & E300 & Hsd & Hct & Hfuel). cbn [o_q o_tb] in E300, Hct, Hfuel.
oc_sd_split.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_owed_counter_text HEN
  ltac:(unfold T_owed_counter_text, ESTACK; lia)) as (Hceil & H47 & H46 & _ & Hpres).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : T_owed_counter_text = 4288) by reflexivity.
assert (E32o : ew (Ereg regs (cw_extra [])) 32 = Z_to_bv 64 SB) by apply cw_ew_SB.
oc_AG (Ereg regs (cw_extra [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs (cw_extra [])) n = getr regs r)
  by (intros nn r Hnn; apply cw_ew_reg; exact Hnn).
assert (B2o : bv_unsigned (ew (Ereg regs (cw_extra [])) 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact B2o).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat) by lia; exact (EE 1%nat 1%bv eq_refl)).
pose proof (proj1 HJ0) as HAR. pose proof (proj1 HJ) as HAR3.
destruct (oc_fa_eq B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k _ _ _ _ _ _ _ HJ0 HJ) as (EFA & EFL).
assert (Hfin3 : In (1, pos) (frames S3)) by (rewrite HFRS; left; reflexivity).
remember (frame_addr ly3 1 pos) as F eqn:HFeq. rewrite EFA in HFeq. try rewrite <- HFeq in E75, E88.
remember (flag_addr lyc 1 pos) as FL eqn:HFLeq. try rewrite <- HFLeq in E87.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR3 Hfin3) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 1 pos HAR3 Hfin3) as (HF4096 & HFceil & HFhigh).
rewrite EFA, <- HFeq in HFal, HFhi, HFpres, HFSpres, HF4096, HFceil, HFhigh.
change (fs_frame_bytes 1) with 128 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8m : F mod 8 = 0) by (rewrite HFq; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
set (sp1 := 32 * ((spZ regs + -160) / 32)) in *.
destruct (sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by lia. clear Hsp1r.
unfold oc_E in KT; cbn [o_sg o_dt] in KT.
destruct Hct as (Hi & Hnz & Hspec & Hls & Hcinv & Hs128 & Hd01).
pose proof Hcinv as (_ & Hld & _).
pose proof Hcstr as (_ & _ & Hin0 & _).
destruct (oc_text_at B LAWS MT GLYPHA ROSTRS _ _ _ _ _ _ i Hpre0 Hst0 Hi) as (Tv & Tr & Tra & Tam & Tq0 & Tqn & Tcw).
cbn [o_q o_tb o_W o_memc o_regs] in Tv, Tr, Tra, Tam, Tq0, Tqn, Tcw. unfold oc_n in Tam, Tqn, Tcw; cbn [o_tb] in Tam, Tqn, Tcw.
set (c := nth i tb 0) in *.
assert (Tam1 : amem_range (q + Z.of_nat i) 1) by (unfold amem_range in *; lia).
assert (Htf : q + Z.of_nat i + 1 <= F \/ F + 128 <= q + Z.of_nat i).
{ destruct (Z_lt_le_dec (q + Z.of_nat i) F); [left; lia|].
  destruct (Z_lt_le_dec (q + Z.of_nat i) (F + 128)); [exfalso | right; lia].
  assert (Hz : in_zr (q + Z.of_nat i) (frame_rng ly3 (1, pos))).
  { unfold in_zr, frame_rng; cbn [fst snd]. rewrite ?EFA. rewrite <- ?HFeq. change (fs_frame_bytes 1) with 128. lia. }
  pose proof (cw_fresh_own B LAWS lyc Sc ly3 S3 W3 (ms_mem ms3) md3 1 pos (q + Z.of_nat i) HAR3 HFRS HPERM EFA (or_introl Hz))
    as (_ & _ & Hfb & Hff).
  destruct Hcq as [(b & m & Hin & Hb1 & Hb2) | (cid & p & Hin & Hf1 & Hf2)].
  - exact (Hfb b m (q + Z.of_nat i - b) Hin ltac:(lia) ltac:(lia)).
  - destruct (Hff cid p Hin) as (Hx & _). apply Hx. unfold in_zr, frame_rng; cbn [fst snd]. lia. }
(* the walk's own frame, its shadow and its flag byte are fresh for the call state *)
assert (HFR : forall x, (F <= x < F + 128 \/ SB + F / 8 <= x < SB + F / 8 + 16 \/ x = FL) -> cw_fresh B lyc Sc x).
{ intros x Hx. apply (cw_fresh_frame B LAWS FFL ly3 S3 W3 (ms_mem ms3) md3 lyc Sc 1 pos x HAR3 HFRS);
  [ intros ? ?; split; [apply (Permutation_in _ HPERM) | apply (Permutation_in _ (Permutation_sym HPERM))]
  | exact EFA
  | unfold frame_rng, in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, EFL, <- HFeq, <- HFLeq; rewrite <- SB_SHADOW_OFF;
    change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; lia ]. }
(* the text byte: atom 350 = c, the region based at the cursor (atom 300), the shadow entry of [cursor, cursor + 1) *)
pose proof (st_ok_havoc_win tfibsegs 350 E _ _ [Z_to_bv 64 c] HS ltac:(vm_compute; reflexivity)) as HS1.
assert (E350 : ew (havoc E 350 [Z_to_bv 64 c]) 350 = Z_to_bv 64 c) by exact (ew_havoc_new E 350 [Z_to_bv 64 c] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
clear HS. rename HS1 into HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
cpw_rebase.
oc_AG (Ereg regs (cw_extra [])).
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 300%nat (mkAF 0 (2 ^ 47 - 1) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E300, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r;
          unfold amem_range in Tam1; rewrite C3, C4, C5 in Tam1; lia)) as HS1;
  clear HS; rename HS1 into HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 350%nat (mkAF 0 255 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E350, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS1;
  clear HS; rename HS1 into HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv
    (YP09.mkRegion (Some 300%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 350 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
          rewrite E300, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
          apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val tfibsegs Ev _ (q + Z.of_nat i) 0 1 (SOff 350 0) c);
          [rewrite sv_denot_SOff0, E350; reflexivity | zside | zside |];
          rewrite Z.add_0_r; exact (AE36.val_mem1_of_aview _ _ _ _ Tv))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalE AG; unfold SB; unfold amem_range, coff_win in *; rewrite C3, C4, C5 in *;
          unfold in_app, kLowShadowBeg, kHighMemBeg in HFhigh;
          repeat split; first [lia | match goal with |- ?g => idtac "DISJ-FAIL" g; fail end])) as HS1;
  clear HS; rename HS1 into HS end.
oc_frame_shok true.
pose proof HJ as HJn. clear HJ. rename HJn into HJ.
(* 0x83f48 .. 0x83f58: the text byte's check (paid by its shadow entry), lbu s9; stop at beq s9,s3 *)
Time cw_run oc_awr. Time oc_kstep oc_win.
Time cw_branch Hc.
2: { (* c <> '.' *)
  Time cw_run oc_awr. Time oc_kstep oc_win.
  Time cw_branch Hz.
  - (* c = 0: the end of the text, 0x8405c *)
    Time cw_run_to oc_awr 0x8405c. Time oc_kstep oc_win.
    oc_c350 Hz. apply Z.eqb_eq in Hz.
    Time oc_joinX HS (ss_Z 4) ocZ_deads.
    lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H _) ?msx) => eapply (HZ _ Ev _ _ _ msx _) end;
      [exact Hpre0 | oc_env_tac | oc_st_tac | | exact HS].
    exists s, dot. cbn [o_tb]. split; [oc_sd_build|]. split; [|auto].
    exact (oc_step_end tb i 4 s dot (conj Hi (conj Hnz (conj Hspec (conj Hls (conj Hcinv (conj Hs128 Hd01)))))) Hz).
  - (* c <> 0: owed_seg7 (c) *)
    oc_c350 Hz. apply Z.eqb_neq in Hz. oc_c350 Hc. apply Z.eqb_neq in Hc.
    assert (Hxv : (c =? 46) = false) by (apply Z.eqb_neq; exact Hc).
    assert (Harg : (if c =? 46 then 32 else c) = c) by (rewrite Hxv; reflexivity).
    Time cw_run_to oc_awr 0x8438c. Time oc_kstep oc_win.
    oc_unewset.
    Time oc_seg7_call SEG7 sp1.
    oc_AG (Ereg regs (cw_extra [])).
    Time oc_pin (10%bv : bv 5) 314%nat.
    oc_AG (Ereg regs (cw_extra [])).
    Time oc_frame_shok false.
    clear EFA EFL. destruct (oc_fa_eq B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k _ _ _ _ _ _ _ HJ0 HJ) as (EFA & EFL).
    Time cw_run oc_awr. Time oc_kstep oc_win.
    assert (Hv8 : codec_owe.owed_seg7_spec c = -1 \/ 0 <= codec_owe.owed_seg7_spec c < 128) by exact (codec_text.owed_seg7_range c).
    lazymatch goal with Eax : ew ?Ex 314 = getr _ 10, HRcx : getr _ 10 = w64 _ |- _ => cbn [ms_regs restrict mkst] in Eax; rewrite HRcx in Eax; unfold w64 in Eax end.
    cw_branch Hv.
    + (* v < 0: SPEC_E_RANGE *)
      lazymatch type of Hv with context [sv_denot ?Ecur (SOff 314 0)] =>
        lazymatch goal with Eax : ew ?Ex 314 = Z_to_bv 64 _ |- _ =>
        let Hx := fresh in assert (Hx : ew Ecur 314 = Z_to_bv 64 (codec_owe.owed_seg7_spec c)) by (oc_ew_peel; exact Eax);
        rewrite (oc_bltz Ecur 314 _ Hx ltac:(lia)) in Hv; clear Hx end end.
      apply Z.ltb_lt in Hv.
      Time cw_run_to oc_awr 0x84174. Time oc_kstep oc_win.
      Time oc_joinX HS (ss_R 18446744073709551605) ocR_deads.
      lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H _) ?msx) => eapply (HR _ Ev _ _ _ msx _) end;
        [exact Hpre0 | oc_env_tac | oc_st_tac | | exact HS].
      unfold INV_R; cbn [o_tb].
      rewrite (oc_step_err tb i 4 s dot c (conj Hi (conj Hnz (conj Hspec (conj Hls (conj Hcinv (conj Hs128 Hd01)))))) eq_refl Hz
        (fun H => Hc (proj1 H)) ltac:(left; rewrite Harg; exact Hv)).
      split; [unfold w64, DgnSpec.E_RANGE; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | intros Hr; unfold DgnSpec.E_RANGE in Hr; discriminate Hr].
    + (* v >= 0: dot[4], s[4] *)
      lazymatch type of Hv with context [sv_denot ?Ecur (SOff 314 0)] =>
        lazymatch goal with Eax : ew ?Ex 314 = Z_to_bv 64 _ |- _ =>
        let Hx := fresh in assert (Hx : ew Ecur 314 = Z_to_bv 64 (codec_owe.owed_seg7_spec c)) by (oc_ew_peel; exact Eax);
        rewrite (oc_bltz Ecur 314 _ Hx ltac:(lia)) in Hv; clear Hx end end.
      apply Z.ltb_ge in Hv.
      Time cw_run_to oc_awr 0x83fd4. Time oc_kstep oc_win.
      let R := fresh "Rtwelve" in rreg HS (12%bv : bv 5) R.
      lazymatch goal with Rt : getr _ 12 = alu64 ALU_SLTU (Z_to_bv 64 (bv_unsigned (ew ?Ex 350) + -46)) _ |- _ =>
        let Hx := fresh in assert (Hx : ew Ex 350 = Z_to_bv 64 c) by (oc_ew_peel; assumption);
        rewrite (oc_seqz46 Ex c Hx Tr), Hxv in Rt; clear Hx end.
      oc_unewset. oc_AG (Ereg regs (cw_extra [])).
      Time oc_pin (12%bv : bv 5) 324%nat.
      lazymatch goal with Eax : ew ?Ex 324 = getr _ 12, Rt : getr _ 12 = Z_to_bv 64 0 |- _ =>
        cbn [ms_regs restrict mkst] in Eax; rewrite Rt in Eax end.
      oc_AG (Ereg regs (cw_extra [])).
      Time oc_frame_shok false.
      Time cw_run_to oc_awr 0x83f48. Time oc_kstep oc_win.
      Time oc_joinL HS (ss_L 5).
      lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H _) ?msx) => eapply (IHL 5%nat ltac:(lia) _ Ev _ _ _ msx _) end;
        [exact Hpre0 | oc_env_tac | oc_st_tac | | exact HS].
      assert (Hct1 : oc_ct tb (Datatypes.S i) 5 (s ++ [codec_owe.owed_seg7_spec c]) (DgnLib.upd_at dot (Z.of_nat 4) 0)).
      { pose proof (oc_step_call tb i 4 s dot c (conj Hi (conj Hnz (conj Hspec (conj Hls (conj Hcinv (conj Hs128 Hd01))))))
          Hin0 eq_refl Hz (fun H => Hc (proj1 H)) ltac:(rewrite Harg; lia) ltac:(lia)) as H.
        rewrite Harg, Hxv in H. exact H. }
      exists (Datatypes.S i), (s ++ [codec_owe.owed_seg7_spec c]), (DgnLib.upd_at dot (Z.of_nat 4) 0). cbn [o_q o_tb].
      split; [|split; [oc_sd_build | split; [exact Hct1 | lia]]].
      rewrite oc_ew_havoc1, Rcur. cbn [sv_denot]. oc_ew_peel. rewrite E300, unsigned_lit_small by lia. f_equal. lia.
  }
(* c = '.' *)
oc_c350 Hc. apply Z.eqb_eq in Hc.
assert (Hz : c <> 0) by lia.
assert (Hxv : (c =? 46) = true) by (apply Z.eqb_eq; exact Hc).
assert (Harg : (if c =? 46 then 32 else c) = 32) by (rewrite Hxv; reflexivity).
Time cw_run oc_awr. Time oc_kstep oc_win.
Time cw_branch Hd.
- (* dot[3] = 0: the dot joins the previous digit *)
  oc_dot_hd Hd 323%nat. apply Z.eqb_eq in Hd.
  Time cw_run_to oc_awr 0x83f48. Time oc_kstep oc_win.
  Time oc_joinM HS (ss_L 4) 323%nat.
  lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H _) ?msx) => eapply (IHL 4%nat ltac:(lia) _ Ev _ _ _ msx _) end;
    [exact Hpre0 | oc_env_tac | oc_st_tac | | exact HS].
  pose proof (oc_step_merge tb i 4 s dot (conj Hi (conj Hnz (conj Hspec (conj Hls (conj Hcinv (conj Hs128 Hd01)))))) Hin0 Hc ltac:(lia) Hd) as Hct1.
  exists (Datatypes.S i), s, (DgnLib.upd_at dot (Z.of_nat 4 - 1) 1). cbn [o_q o_tb].
  split; [|split; [oc_sd_build | split; [exact Hct1 | lia]]].
  rewrite oc_ew_havoc1, Rcur. cbn [sv_denot]. oc_ew_peel. rewrite E300, unsigned_lit_small by lia. f_equal. lia.
- (* dot[3] <> 0: owed_seg7 (' ') *)
  oc_dot_hd Hd 323%nat. apply Z.eqb_neq in Hd.
  Time cw_run_to oc_awr 0x8438c. Time oc_kstep oc_win.
  oc_unewset.
  Time oc_seg7_call SEG7 sp1.
  oc_AG (Ereg regs (cw_extra [])).
  Time oc_pin (10%bv : bv 5) 314%nat.
  oc_AG (Ereg regs (cw_extra [])).
  Time oc_frame_shok false.
  clear EFA EFL. destruct (oc_fa_eq B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k _ _ _ _ _ _ _ HJ0 HJ) as (EFA & EFL).
  Time cw_run oc_awr. Time oc_kstep oc_win.
  assert (Hv8 : codec_owe.owed_seg7_spec 32 = -1 \/ 0 <= codec_owe.owed_seg7_spec 32 < 128) by exact (codec_text.owed_seg7_range 32).
  lazymatch goal with Eax : ew ?Ex 314 = getr _ 10, HRcx : getr _ 10 = w64 _ |- _ => cbn [ms_regs restrict mkst] in Eax; rewrite HRcx in Eax; unfold w64 in Eax end.
  cw_branch Hv.
  + (* v < 0: SPEC_E_RANGE *)
    lazymatch type of Hv with context [sv_denot ?Ecur (SOff 314 0)] =>
      lazymatch goal with Eax : ew ?Ex 314 = Z_to_bv 64 _ |- _ =>
      let Hx := fresh in assert (Hx : ew Ecur 314 = Z_to_bv 64 (codec_owe.owed_seg7_spec 32)) by (oc_ew_peel; exact Eax);
      rewrite (oc_bltz Ecur 314 _ Hx ltac:(lia)) in Hv; clear Hx end end.
    apply Z.ltb_lt in Hv.
    Time cw_run_to oc_awr 0x84174. Time oc_kstep oc_win.
    Time oc_joinX HS (ss_R 18446744073709551605) ocR_deads.
    lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H _) ?msx) => eapply (HR _ Ev _ _ _ msx _) end;
      [exact Hpre0 | oc_env_tac | oc_st_tac | | exact HS].
    unfold INV_R; cbn [o_tb].
    rewrite (oc_step_err tb i 4 s dot c (conj Hi (conj Hnz (conj Hspec (conj Hls (conj Hcinv (conj Hs128 Hd01)))))) eq_refl Hz
      (fun H => Hd (proj2 (proj2 H))) ltac:(left; rewrite Harg; exact Hv)).
    split; [unfold w64, DgnSpec.E_RANGE; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | intros Hr; unfold DgnSpec.E_RANGE in Hr; discriminate Hr].
  + (* v >= 0: dot[4], s[4] *)
    lazymatch type of Hv with context [sv_denot ?Ecur (SOff 314 0)] =>
      lazymatch goal with Eax : ew ?Ex 314 = Z_to_bv 64 _ |- _ =>
      let Hx := fresh in assert (Hx : ew Ecur 314 = Z_to_bv 64 (codec_owe.owed_seg7_spec 32)) by (oc_ew_peel; exact Eax);
      rewrite (oc_bltz Ecur 314 _ Hx ltac:(lia)) in Hv; clear Hx end end.
    apply Z.ltb_ge in Hv.
    Time cw_run_to oc_awr 0x83fd4. Time oc_kstep oc_win.
    let R := fresh "Rtwelve" in rreg HS (12%bv : bv 5) R.
    lazymatch goal with Rt : getr _ 12 = alu64 ALU_SLTU (Z_to_bv 64 (bv_unsigned (ew ?Ex 350) + -46)) _ |- _ =>
      let Hx := fresh in assert (Hx : ew Ex 350 = Z_to_bv 64 c) by (oc_ew_peel; assumption);
      rewrite (oc_seqz46 Ex c Hx Tr), Hxv in Rt; clear Hx end.
    oc_unewset. oc_AG (Ereg regs (cw_extra [])).
    Time oc_pin (12%bv : bv 5) 324%nat.
    lazymatch goal with Eax : ew ?Ex 324 = getr _ 12, Rt : getr _ 12 = Z_to_bv 64 1 |- _ =>
      cbn [ms_regs restrict mkst] in Eax; rewrite Rt in Eax end.
    oc_AG (Ereg regs (cw_extra [])).
    Time oc_frame_shok false.
    Time cw_run_to oc_awr 0x83f48. Time oc_kstep oc_win.
    Time oc_joinL HS (ss_L 5).
    lazymatch type of HS with st_ok _ ?Ev _ (restrict (w_H _) ?msx) => eapply (IHL 5%nat ltac:(lia) _ Ev _ _ _ msx _) end;
      [exact Hpre0 | oc_env_tac | oc_st_tac | | exact HS].
    assert (Hct1 : oc_ct tb (Datatypes.S i) 5 (s ++ [codec_owe.owed_seg7_spec 32]) (DgnLib.upd_at dot (Z.of_nat 4) 1)).
    { pose proof (oc_step_call tb i 4 s dot c (conj Hi (conj Hnz (conj Hspec (conj Hls (conj Hcinv (conj Hs128 Hd01))))))
        Hin0 eq_refl Hz (fun H => Hd (proj2 (proj2 H))) ltac:(rewrite Harg; lia) ltac:(lia)) as H.
      rewrite Harg, Hxv in H. exact H. }
    exists (Datatypes.S i), (s ++ [codec_owe.owed_seg7_spec 32]), (DgnLib.upd_at dot (Z.of_nat 4) 1). cbn [o_q o_tb].
    split; [|split; [oc_sd_build | split; [exact Hct1 | lia]]].
    rewrite oc_ew_havoc1, Rcur. cbn [sv_denot]. oc_ew_peel. rewrite E300, unsigned_lit_small by lia. f_equal. lia.
Qed.
End oc.
