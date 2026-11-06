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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/owed_counter_text_A_pre.v, with its module names changed; 170 of its 217 lines of code are new or changed and 399 lines of the source are left out. *)
(* owed_counter_text at image A: the release from 0x84174 with a0 = 18446744073709551605 (the frame's shadow marked, its header word
   written, its flag byte cleared and the frame given back), the epilogue and the return. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base owed_counter_text_A_Lt owed_counter_text_A_wr owed_counter_text_A_Qb owed_counter_text_A_Rb.
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
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law tfibsegs B.

Lemma oc_relE : oc_from B MT GLYPHA ROSTRS (ss_R 18446744073709551605) (INV_R 18446744073709551605).
Proof using MTL TL LAWS ML FFL MTF ASF.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj pos] E ly3 S3 W3 ms3 md3
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
unfold INV_R in Hinv; cbn [o_tb o_sg o_dt] in Hinv.
destruct (codec_owe.owed_counter_text_spec tb) as [[rr sres] dres] eqn:Espec. destruct Hinv as (Hrz & Hmem).
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
(* the walk's own frame, its shadow and its flag byte are fresh for the call state *)
assert (HFR : forall x, (F <= x < F + 128 \/ SB + F / 8 <= x < SB + F / 8 + 16 \/ x = FL) -> cw_fresh B lyc Sc x).
{ intros x Hx. apply (cw_fresh_frame B LAWS FFL ly3 S3 W3 (ms_mem ms3) md3 lyc Sc 1 pos x HAR3 HFRS);
  [ intros ? ?; split; [apply (Permutation_in _ HPERM) | apply (Permutation_in _ (Permutation_sym HPERM))]
  | exact EFA
  | unfold frame_rng, in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, EFL, <- HFeq, <- HFLeq; rewrite <- SB_SHADOW_OFF;
    change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; lia ]. }

(* the caller's bytes the call writes: seg[8] at sg (atom 11), *dots at dt (atom 12) *)
pose proof Hdsg as (Hsg0 & Hsg63 & _ & Hsgw & Hsgra & _ & Hsga & Hsgcw).
assert (HDT : 0 < dt /\ dt + 1 <= 2 ^ 63 /\ twr_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc (spZ regs) dt 1 /\
  range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF dt 1 /\ amem_range dt 1 /\
  coff_win (spZ regs) T_owed_counter_text dt 1)
  by (destruct Hdt as [((Ha & Hb & _ & Hc & Hd & _ & He & Hf) & _) | (Ha & Hb & _ & _ & Hc & Hd & _ & He & Hf)];
      exact (conj Ha (conj Hb (conj Hc (conj Hd (conj He Hf)))))).
destruct HDT as (Hdt0 & Hdt63 & Hdtw & Hdtra & Hdta & Hdtcw).
assert (HnIs : forall x, sg <= x < sg + 8 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (oc_twr_not_img B LAWS GLYPHA ROSTRS _ sg 8 x Hpre0 Hsgw Hsga Hx)).
assert (HnId : forall x, dt <= x < dt + 1 -> ~ in_img tfibsegs x)
  by (intros x Hx; exact (oc_twr_not_img B LAWS GLYPHA ROSTRS _ dt 1 x Hpre0 Hdtw Hdta Hx)).
pose proof (oc_ra_at B LAWS MT GLYPHA ROSTRS _ ly3 S3 W3 (ms_mem ms3) md3 sg 8 Hpre0 Hst0 Hsgw Hsga Hsgra) as RAsg.
pose proof (oc_ra_at B LAWS MT GLYPHA ROSTRS _ ly3 S3 W3 (ms_mem ms3) md3 dt 1 Hpre0 Hst0 Hdtw Hdta Hdtra) as RAdt.
assert (E11o : ew (Ereg regs (cw_extra [])) 11 = Z_to_bv 64 sg) by (rewrite (EE 11%nat 11%bv eq_refl), H11; reflexivity).
assert (E12o : ew (Ereg regs (cw_extra [])) 12 = Z_to_bv 64 dt) by (rewrite (EE 12%nat 12%bv eq_refl), H12; reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 sg) by (rewrite (AG 11%nat) by lia; exact E11o).
assert (E12 : ew E 12 = Z_to_bv 64 dt) by (rewrite (AG 12%nat) by lia; exact E12o).

assert (Hsgf : sg + 8 <= F \/ F + 128 <= sg).
{ destruct (Z_lt_le_dec (sg + 8) (F + 1)) as [H | H]; [left; lia|].
  destruct (Z_lt_le_dec (F + 127) sg) as [H' | H']; [right; lia|]. exfalso.
  apply (oc_twr_fresh B LAWS GLYPHA ROSTRS _ sg 8 (Z.max sg F) Hpre0 Hsgw Hsga ltac:(lia)). apply HFR. lia. }
assert (Hdtf : dt + 1 <= F \/ F + 128 <= dt).
{ destruct (Z_lt_le_dec dt F) as [H | H]; [left; lia|].
  destruct (Z_lt_le_dec (F + 127) dt) as [H' | H']; [right; lia|]. exfalso.
  apply (oc_twr_fresh B LAWS GLYPHA ROSTRS _ dt 1 dt Hpre0 Hdtw Hdta ltac:(lia)). apply HFR. lia. }
assert (HF8e : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
assert (Hdt8 : dt / 8 < F / 8 \/ F / 8 + 16 <= dt / 8).
{ destruct Hdtf as [H | H]; [left | right].
  - apply Z.div_lt_upper_bound; lia.
  - apply Z.div_le_lower_bound; lia. }
assert (Hdtb : 0 <= dt / 8 < 17592186044416) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; unfold amem_range in Hdta; rewrite C3, C4, C5 in Hdta; lia).
assert (Hsg2 : ~ (spZ regs - ESTACK <= sg < spZ regs) /\ ~ (spZ regs - ESTACK <= sg + 7 < spZ regs))
  by (split; [exact (proj2 (proj2 (proj2 (Hsgw sg ltac:(lia))))) | exact (proj2 (proj2 (proj2 (Hsgw (sg + 7) ltac:(lia)))))]).
assert (Hdt2 : ~ (spZ regs - ESTACK <= dt < spZ regs)) by exact (proj2 (proj2 (proj2 (Hdtw dt ltac:(lia))))).
pose proof Hsga as Hsga'. pose proof Hdta as Hdta'. unfold amem_range in Hsga', Hdta'. rewrite C3, C4, C5 in Hsga', Hdta'.
unfold in_app, kLowShadowBeg, kHighMemBeg in HFhigh. unfold ESTACK in Hsg2, Hdt2.
destruct Hsg2 as (Hsg2a & Hsg2b).
oc_hide_disj.

assert (Psg : forall j, 0 <= j < 8 -> apresent (w_H W3) (ms_mem ms3) (sg + j))
  by (intros j Hj; exact (oc_pres_at B LAWS MT GLYPHA ROSTRS _ ly3 S3 W3 _ md3 sg 8 (sg + j) Hpre0 Hst0 Hsgw Hsga Hsgcw ltac:(lia) ltac:(lia))).
assert (Pdt : apresent (w_H W3) (ms_mem ms3) dt)
  by (replace dt with (dt + 0) by lia; exact (oc_pres_at B LAWS MT GLYPHA ROSTRS _ ly3 S3 W3 _ md3 dt 1 (dt + 0) Hpre0 Hst0 Hdtw Hdta Hdtcw ltac:(lia) ltac:(lia))).
(* the flag byte: the runtime's own, off the frame, its shadow and the machine stack *)
destruct (FFL ly3 S3 W3 (ms_mem ms3) md3 1 pos HAR3 Hfin3) as (HFLp & HFLo & (HFLapp & HFLni) & (HFL4 & HFLz & HFLc)).
rewrite EFL, <- HFLeq in HFLp, HFLo, HFLapp, HFLni, HFL4, HFLz, HFLc.
assert (HFLa1 : F + 128 <= FL \/ FL + 1 <= F)
  by exact (cw_flag_apart B ly3 S3 FL F (F + 128) HFLo (fun a Ha => proj2 (HFpres a Ha))).
assert (HFLa2 : SB + F / 8 + 16 <= FL \/ FL + 1 <= SB + F / 8).
{ apply (cw_flag_apart B ly3 S3 FL (SB + F / 8) (SB + F / 8 + 16) HFLo).
  intros a Ha. replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
  exact (proj2 (HFSpres (a - (SB + F / 8)) ltac:(change (128 / 8) with 16; lia))). }
unfold zone2, off_img in HFLz. destruct HFLz as (HFLz1 & HFLz2).
oc_hide_disj.
(* the release's regions: the flag byte in front, the frame's header and its shadow writable *)
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (tl (ss_mem ssx)) in
  pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS1;
  clear HS; rename HS1 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv (YP09.mkRegion (Some 88%nat) 0 16 0 16 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite E88, unsigned_lit_small by (unfold SB; lia); unfold SB; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable tfibsegs);
          replace (2147450880 + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, SHADOW_OFF; lia);
          exact (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia))))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in let ry2 := eval vm_compute in ry in change (all_disjoint Ey ry2 rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalE AG; unfold SB; repeat split; oc_dl)) as HS1;
  clear HS; rename HS1 into HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv (YP09.mkRegion (Some 75%nat) 0 8 0 8 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite E75, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable tfibsegs); exact (proj1 (HFpres (F + o) ltac:(lia))))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in let ry2 := eval vm_compute in ry in change (all_disjoint Ey ry2 rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalE AG; unfold SB; repeat split; oc_dl)) as HS1;
  clear HS; rename HS1 into HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv (cw_flag_region 87) HS eq_refl
    (cw_flag_region_ok B FFL Ev 87 ly3 S3 W3 (ms_mem ms3) md3 1 pos HAR3 Hfin3 ltac:(rewrite E87, HFLeq, <- (EFL 1 pos); reflexivity))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in let ry2 := eval vm_compute in ry in change (all_disjoint Ey ry2 rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalE AG; unfold SB; repeat split; oc_dl)) as HS1;
  clear HS; rename HS1 into HS end.
pose proof HJ as HJn. clear HJ. rename HJn into HJ.
Time aj_run_flag_sh tfibtbl_lib_ok HS HJ.
- lia.
- apply (cw_awrf_flag_front _ _ _ _ _ _ _ _ _ _ 87%nat (flag_addr ly3 1 pos)); [reflexivity | | cbn; lia | cbn; lia | oc_awr].
  rewrite E87, unsigned_lit_small by lia. rewrite HFLeq, EFL. reflexivity.
- intros msr HSr.
  pose proof (st_ok_region_nth _ _ msr 0 (YP09.mkRegion (Some 87%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HSr eq_refl) as HRf.
  pose proof (field_of_region _ _ 87 (flag_addr ly3 1 pos) _ 0 1 0 1 0 1%N (SLit 0) 0 HRf
    ltac:(rewrite E87, unsigned_lit_small by lia; rewrite HFLeq, EFL; reflexivity) ltac:(left; reflexivity) ltac:(reflexivity)
    ltac:(lia) ltac:(lia)) as V.
  pose proof (V 0%nat ltac:(lia)) as V0. rewrite !Z.add_0_r in V0. exact V0.
- (* after the release: seg[8] and *dots kept, the walk's kept bytes, the return *)
  assert (Hsgfl : forall j, 0 <= j < 8 -> sg + j <> FL).
  { intros j Hj Heq. apply (oc_twr_fresh B LAWS GLYPHA ROSTRS _ sg 8 (sg + j) Hpre0 Hsgw Hsga ltac:(lia)).
    rewrite Heq. apply HFR. right; right; reflexivity. }
  assert (Hdtfl : dt <> FL).
  { intros Heq. apply (oc_twr_fresh B LAWS GLYPHA ROSTRS _ dt 1 dt Hpre0 Hdtw Hdta ltac:(lia)).
    rewrite Heq. apply HFR. right; right; reflexivity. }
  lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
  assert (NWsg : forall j, (j < 8)%nat -> ~ in_wrange Ex rsx (sg + Z.of_nat j));
  [ intros j Hj; pose proof (Hsgfl (Z.of_nat j) ltac:(lia)) as Hne; unfold cw_hold in Hsgf, Hsg2a, Hsg2b, Hsga'; oc_notwin | ];
  assert (NWdt : forall j, (j < 1)%nat -> ~ in_wrange Ex rsx (dt + Z.of_nat j));
  [ intros j Hj; replace j with 0%nat by lia; rewrite Z.add_0_r; unfold cw_hold in Hdtf, Hdt2, Hdta'; oc_notwin | ];
  assert (GSVD : rr = 0 -> garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms)) sg sres /\
                         val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) dt 1 dres);
  [ intros Hr0; subst rr; destruct (Hmem eq_refl) as (Gs & Vd); pose proof (oc_spec_len tb sres dres Espec) as Hlen;
    split;
    [ apply (oc_garr8_kept Ex rsx _ _ sg sres HFr ltac:(lia) ltac:(rewrite Hlen; lia)); [rewrite Hlen; exact NWsg | exact Gs]
    | exact (oc_val_mem_kept Ex rsx _ _ dt 1 dres HFr ltac:(lia) ltac:(lia) NWdt Vd) ]
  | ] end.
  assert (EXs : exists l, garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms)) sg l /\ length l = 8%nat).
  { apply oc_garr8_exists. intros j Hj. exact (apresent_grows _ _ _ _ HG (Psg j Hj)). }
  assert (EXd : exists dd, val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) dt 1 dd).
  { apply oc_byte_exists. exact (apresent_grows _ _ _ _ HG Pdt). }
  clear NWsg NWdt Hmem.
  oc_kstep oc_win.
  oc_cur.
  cw_frame_leaf ltac:(idtac; exact KT)
    ltac:(unfold oc_R; cbn [o_tb o_sg o_dt]; rewrite Espec; cbv beta iota zeta;
          split; [lazymatch goal with R10x : getr _ 10 = _ |- _ => rewrite R10x end; cbn [sv_denot]; exact Hrz
                 | split; [exact GSVD | intros _; destruct EXs as (l & Hl & Hll); destruct EXd as (dd & Hdd); exists l, dd; auto]]).
Qed.
End oc.
