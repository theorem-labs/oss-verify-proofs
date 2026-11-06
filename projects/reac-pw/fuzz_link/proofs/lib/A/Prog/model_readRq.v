(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths and module names changed; 303 of its 358 lines of code are new or changed and 1252 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readHead.v, with its module names changed; 788 of its 856 lines of code are new or changed and 290 lines of the source are left out. *)
(* model_read on image A: the read, from the branch on index_of's answer at +0x180 (index <> 0) to the exit:
     +0x184 .. +0x1a4  s8 := index, s9 := r = F + 0x20, the request's four shadow bytes 4..7 := 0
     +0x1a8            checked_memset(r + 12, 0, 20)            (link_ajkit.v aj_gx_intrin_at)
     +0x1ac .. +0x1e4  the request's header words, index at r + 20, the arguments of talk
     +0x1e8            talk(m, r, 32, kind, kind_n, alias, alias_n) (talk_c.v, aleaf_rd)
     +0x1ec .. +0x200  the four shadow bytes := 0xf8, j +0x208, where model_readExit.v mr_exit_d ends the walk.
   The cut MR_AT180 holds the state model_readTail.v reaches after index_of returns.
   Proves no function (kind: segment lemma of model_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c model_readDefs model_readExit model_readKit PaJournalFs model_readStr model_readCall LinkWalkZsh model_readWr model_readReq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.


(* the state after index_of returns (+0x180, the branch on its answer, atom 724), its answer not 0: the caller-saved
   registers are the call's fresh atoms 720 .. 735, the realigned area at sp1 and the thirteen saved words *)
Definition mr_ss180 : sstate :=
  mkSS 17376
    [SLit 0; SOff 720 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 721 0; SOff 722 0; SOff 723 0; SOff 2 0; SOff 60 0;
     SOff 724 0; SOff 725 0; SOff 726 0; SOff 727 0; SOff 728 0; SOff 729 0; SOff 730 0; SOff 731 0; SOff 44 0;
     SOff 14 0; SOff 15 0; SOff 12 0; SOff 13 0; SOff 10 0; SOff 11 0; SOff 32 0; SOff 62 0; SOff 44 0;
     SOff 732 0; SOff 733 0; SOff 734 0; SOff 735 0]
    [YP09.mkRegion (Some 60%nat) 0 24 0 24 [YP09.mkChunk 16 (CVal 8 (SOff 44 0))]; mr_stk104] None
    (mkFacts [(62%nat, mkAF MR_SB (MR_SB + 2 ^ 44) 3); (44%nat, mkAF 4096 (2 ^ 47) 6);
              (60%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF MR_SB MR_SB 0)]
             [mkAC BC_NE (SOff 724 0) (SLit 0)]
             [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 44 0) (SLit 3)) (SOff 32 0), SOff 62 0)]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis TB : PcapSyms B.
(* checked_memset (0x53214): lib/A/AE2r.v asan_memset_realizes *)
Hypothesis AMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
(* the own callee talk *)
Hypothesis TALK : forall rlo rhi, talk_acontract SK pa_segs rlo rhi B.

(* the cut at +0x180: index_of answered idx <> 0 for the entry's name s0 and table *)
Definition MR_AT180 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) (E : env) (ms : machine_state) (md2 : Model) (ly2 : alayout) (S2 : astate)
    (W2 : world pa_segs) (pos idx : Z) (s0 : list byte) : Prop :=
  img_env pa_val A_LIM E /\ env_agree 32 (Ereg regs MR_extra) E /\
  ew E 32 = Z_to_bv 64 MR_SB /\ ew E 44 = Z_to_bv 64 (frame_addr lyc 1 pos) /\
  ew E 60 = Z_to_bv 64 (32 * ((spZ regs - 128) / 32)) /\ ew E 61 = Z_to_bv 64 (flag_addr lyc 1 pos) /\
  ew E 62 = Z_to_bv 64 (MR_SB + frame_addr lyc 1 pos / 8) /\
  ew E 724 = Z_to_bv 64 idx /\ 0 < idx < 2 ^ 31 /\
  st_ok_pi pa_segs pa_val E mr_ss180 (restrict (w_H W2) ms) /\
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 (ms_mem ms) md2 k /\
  (exists f, S2 = set_fs f Sc) /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  frames S2 = (1, pos) :: frames Sc /\
  (exists S1 W1 mem1 md1, AR pa_segs B lyc S1 W1 mem1 md1 /\ frames S1 = (1, pos) :: frames Sc /\
     ablocks B lyc S1 = ablocks B lyc Sc) /\ ~ In (1, pos) (frames Sc) /\
  akept pa_segs B lyc Sc W memc W2 (ms_mem ms) (spZ regs - MODEL_READ_AK) (spZ regs)
    (fun a => aside_rng lyc 1 pos a \/ (aarg regs 2 <> 0 /\ 1 <= aarg regs 3 /\ a = aarg regs 2)
              \/ (aarg regs 4 <> 0 /\ 1 <= aarg regs 5 /\ a = aarg regs 4)) /\
  val_mem pa_segs (rdW W2 (ms_mem ms)) (frame_addr lyc 1 pos + 120) 8 (flag_addr lyc 1 pos) /\
  (forall a, inFP (model_read_awr regs (rdW W memc)) a -> writable_at pa_segs (rdW W memc) a ->
     writable_at pa_segs (rdW W2 (ms_mem ms)) a) /\
  (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> aview pa_segs (w_H W2) (ms_mem ms) (aarg regs 2) = Some 0) /\
  (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> aview pa_segs (w_H W2) (ms_mem ms) (aarg regs 4) = Some 0) /\
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
  astr_arg pa_segs (rdW W memc) (aarg regs 1) (Some s0) /\ length s0 <> 0%nat /\
  (forall kbs tab, anlk_at pa_segs (rdW W memc) LA_G_NL kbs -> aiftab_at pa_segs (rdW W memc) LA_G_NL kbs tab ->
     index_of tab s0 = idx).

(* lia without the context's universally quantified facts (their premises cost the zify step most of its time) *)
Ltac lz := repeat match goal with
  | H : ?T |- _ => lazymatch T with
                   | ~ _ => fail
                   | forall _, _ => clear H
                   end
  end; lia.

Lemma mr_rq : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md2 ly2 S2
    W2 pos idx s0,
  MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  MR_AT180 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md2 ly2 S2 W2 pos idx s0 ->
  SRr pa_segs W2 (mkCfg ms md2) (MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
Proof using LAWS TL LV HSEGS TB AMSET TALK.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs E ms md2 ly2 S2 W2 pos idx s0 HENT
  (HEI & HAE & E32 & E44 & E60 & E61 & E62 & E724 & Hidx & HS & HJ2 & Hfs2 & Hperm2 & Hfr2 & HS1 & Hnin & HK
   & VFL & WRX & HK0 & HA0 & Hfd & Hfsy & HNM & Hs0 & HIX).
set (POST := MR_POST SK B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
pose proof HENT as (HPRE & HRD & HP).
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK8 : MODEL_READ_AK = 8416) by reflexivity.
destruct HS1 as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1).
destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 pos HJ2) as (FA2 & FL2).
destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 pos HJ) as (FA1 & FL1).
assert (FA : frame_addr ly2 1 pos = frame_addr lyc 1 pos) by congruence.
assert (FLA : flag_addr ly2 1 pos = flag_addr lyc 1 pos) by congruence.
assert (Hin1 : In (1, pos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frame_al64 pa_segs B lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HFa64 & HFb64 & HFb).
destruct (frames_bounds pa_segs B LAWS lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HF4 & HFc & HFapp2).
destruct (al_flag _ _ LAWS lyc S1 W1 mem1 md1 1 pos HAR1 Hin1) as (HFLpres & HFLown & HFLapp & HFLc).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 (ms_mem ms)
  md2 k HJ2) as HAR2.
assert (Hin2 : In (1, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md2 1 pos HAR2 Hin2) as (_ & _ & HFpres2 & HFSpres2).
rewrite FA in HFpres2, HFSpres2.
assert (HFLF : flag_addr lyc 1 pos + 1 <= frame_addr lyc 1 pos).
{ pose proof HAR1 as [M1 _].
  destruct (frame_facts B lyc S1 _ 1 pos M1 Hin1) as (Cc & Cp & _ & _ & _ & P1 & P2 & _ & _ & _ & P3).
  unfold flag_addr, frame_addr. lz. }
set (F := frame_addr lyc 1 pos) in *.
set (FL := flag_addr lyc 1 pos) in *.
change (fs_frame_bytes 1) with 128 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp2, HFLapp.
assert (HFL64 : 0 <= FL < 2 ^ 64)
  by (destruct HFLapp as (Hq1 & _); revert Hq1 HFLc C1a C1b; clear; intros; lz).
pose proof (Z.mul_div_le F 8 ltac:(lz)) as HF8m.
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lz | apply Z.div_le_upper_bound; lz]).
assert (HF8al : (MR_SB + F / 8) mod 8 = 0).
{ unfold MR_SB. destruct (div8_of_mul64 F HFa64) as [E8 _]. rewrite E8.
  rewrite Z.add_mod by lz. rewrite (Z.mul_comm 8), Z.mod_mul by lz. reflexivity. }
assert (U44 : bv_unsigned (ew E 44) = F) by (rewrite E44; apply unsigned_lit_small; lz).
assert (U61 : bv_unsigned (ew E 61) = FL) by (rewrite E61; apply unsigned_lit_small; lz).
assert (U62 : bv_unsigned (ew E 62) = MR_SB + F / 8) by (rewrite E62; apply unsigned_lit_small; unfold MR_SB; lz).
assert (Hsp64 : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE 2%nat ltac:(lz)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof (aj_gx_unpack SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lz) Hal16 ltac:(lz) Hwhi) as (_ & _ & _ & _ & HSTK & HXO & _ & _ & _ & _ & Hceil & H47).
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
destruct (sp1_facts (spZ regs - 128) ltac:(lz) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (U60 : bv_unsigned (ew E 60) = sp1) by (rewrite E60; apply unsigned_lit_small; lz).
assert (Esp1 : sp1 = 32 * ((spZ regs - 128) / 32)) by reflexivity.
clearbody sp1.
assert (HdFS : F + 128 <= MR_SB + F / 8 \/ MR_SB + F / 8 + 16 <= F).
{ assert (HSBv : MR_SB = 2147450880) by reflexivity.
  pose proof (Z.mod_pos_bound F 8 ltac:(lz)). pose proof (Z_div_mod_eq_full F 8).
  destruct HFapp2 as (Hf4x & [Hlowx | (Hhighx & Hhcx)]).
  - left. clear - Hf4x Hlowx HSBv HF8m H H0. lz.
  - right. clear - Hf4x Hhighx HSBv HF8m H H0. lz. }
(* the frame (its flag word at 120) and the frame's shadow, as regions *)
add_fact HS 61%nat (mkAF 4096 (2 ^ 47) 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U61; rewrite Z.pow_0_r, Z.mod_1_r;
        destruct HFLapp as (Hq1 & Hq2); repeat split; lz).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 1 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1) with 128; rewrite U44; split; [lz|]; split; [lz|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs); apply (HFpres2 (F + o)); unfold in_zr, frame_rng; cbn [fst snd];
          fold F; change (fs_frame_bytes 1) with 128; lz
        | apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val pa_segs _ _ F 120 8 _ FL);
          [ cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VFL ] ])
  ltac:(mr_disj; rewrite ?U60, ?U44, ?Usp; repeat split; lz)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 1 0 16 []) HS eq_refl
  ltac:(unfold region_ok, fshadow_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        change (fs_frame_bytes 1 / 8) with 16; rewrite U62; split; [unfold MR_SB; lz|];
        split; [unfold MR_SB; lz|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs);
        replace (MR_SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr, MR_SB, SHADOW_OFF; lz);
        apply (HFSpres2 o ltac:(change (128 / 8) with 16; lz)))
  ltac:(mr_disj; rewrite ?U60, ?U44, ?U62, ?Usp; unfold MR_SB in *; repeat split; lz)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* ---- +0x180 .. +0x1a4 (plain): the branch, s8 := index, s9 := r = F + 0x20, the request's shadow bytes 4..7 := 0,
   the arguments of checked_memset ---- *)
pose (RUNC := paj_run_call_plain_x SK B LAWS G HGok XO OUT).
lazymatch type of HS with
| st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
    lazymatch r with (?ssf, PRS_call ?sf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
      eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ2);
      clear Hrun
    end
  end
end.
{ cbn [ss_mem].
  repeat (apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fframe_region fshadow_region]; intros a Ha;
      rewrite ?U60, ?Usp, ?U44, ?U62 in Ha;
      first
        [ left; split; [left; rewrite HK8 in Hwlo; lz | lz]
        | left; apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
            ((1, pos) :: own) ly2 S2 W2 (ms_mem ms) md2 k 1 pos a HJ2 ltac:(left; reflexivity));
          rewrite FA; fold F;
          first [ left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F;
                  change (fs_frame_bytes 1) with 128 in Ha; lz
                | right; unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16 in *;
                  unfold MR_SB, SHADOW_OFF in *; lz ] ]
    |]);
  apply awr_ok_x_nil. }
cbv beta. intros ms4 mat4 HS4 HJ4 HFm4 HFr4 HG4.
cbn [ms_mem mkst] in HFm4, HFr4, HG4.
pmkst HS4.
prreg HS4 (1%bv : bv 5) Q1. prreg HS4 (2%bv : bv 5) Q2. prreg HS4 (3%bv : bv 5) Q3. prreg HS4 (4%bv : bv 5) Q4.
prreg HS4 (10%bv : bv 5) Q10. prreg HS4 (11%bv : bv 5) Q11. prreg HS4 (12%bv : bv 5) Q12.
prreg HS4 (25%bv : bv 5) Q25.
assert (HES : ESTACK = 4096) by reflexivity.
assert (E3 : ew E 3 = getr regs 3) by (rewrite (proj1 HAE 3%nat ltac:(lz)); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (proj1 HAE 4%nat ltac:(lz)); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp4 : spZ (ms_regs ms4) = sp1) by (unfold spZ; rewrite Q2; exact U60).
(* the request's four shadow bytes are 0 at the call (the shadow region's chunks) *)
sregion HS4 0%nat HR0.
sregion HS4 1%nat HR1.
assert (SH0 : forall o, 4 <= o < 8 -> aview pa_segs (w_H W2) (ms_mem ms4) (MR_SB + F / 8 + o) = Some 0).
{ intros o Ho.
  assert (Hin : In (YP09.mkChunk o (CVal 1 (SLit 0)))
                   [YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0));
                    YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0))]).
  { assert (Hc : o = 4 \/ o = 5 \/ o = 6 \/ o = 7) by lz.
    destruct Hc as [-> | [-> | [-> | ->]]]; cbn [In]; tauto. }
  pose proof (field_of_region (segs := pa_segs) E _ 62 (MR_SB + F / 8) _ _ _ _ _ o 1%N (SLit 0) 0 HR0 U62 Hin
    eq_refl ltac:(cbn; lz) ltac:(cbn; lz)) as Hv.
  specialize (Hv 0%nat ltac:(cbn; lz)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
  unfold aview. rewrite Hv. reflexivity. }
(* ---- +0x1a8: checked_memset(r + 12, 0, 20), r = F + 0x20 ---- *)
eapply SRr_bind.
{ eapply (aj_gx_intrin_at SK pa_segs B LAWS Hsegs OSet (pa_sigma LS___asan_memset) AMSET G XO OUT W2
    (ms_regs ms4) (ms_mem ms4) STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 _ k (F + 44) 0 20 _ HGok HJ4);
  [ rewrite Q10, U44; reflexivity | rewrite Q11; reflexivity | rewrite Q12; reflexivity | lz | lz | lz
  | rewrite Usp4; exact Hsp1al16 | rewrite Usp4, HES; rewrite HK8 in Hwlo; lz | rewrite Usp4; lz
  | rewrite Q3, E3; exact Hgp | rewrite Q4, E4; exact Htp | reflexivity
  | rewrite Q1; apply ret_ok_codeptr_v; [lz | reflexivity] | | | | | ].
  - intros a Ha. left.
    destruct (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
      ((1, pos) :: own) ly2 S2 W2 (ms_mem ms4) _ k 1 pos a HJ4 ltac:(left; reflexivity)
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA; fold F; change (fs_frame_bytes 1) with 128; lz))
      as (Ha1 & Ha2).
    split; [exact Ha1|]. split; [exact Ha2|]. rewrite Usp4, HES. lz.
  - unfold amem_range. destruct HFapp2 as (Hf4x & [Hlowx | (Hhighx & Hhcx)]); [left | right]; unfold kLowMemEnd,
      kHighMemBeg, kHighMemEnd in *; lz.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (MR_SB + F / 8 + (x / 8 - F / 8)) by (unfold MR_SB, SHADOW_OFF; lz).
    apply SH0. lz.
  - intros _ s' Hs. unfold shadow_addr in Hs.
    assert (Ho : 0 <= s' - (MR_SB + F / 8) < 8) by (unfold MR_SB, SHADOW_OFF in *; lz).
    first [ apply (mr_aview_present (w_H W2) (ms_mem ms4) s') | apply (mr_aview_present B (w_H W2) (ms_mem ms4) s') ].
    apply (apresent_grows _ _ _ _ HG4).
    replace s' with (shadow_addr F + (s' - (MR_SB + F / 8))) by (unfold shadow_addr, MR_SB, SHADOW_OFF; lz).
    apply HFSpres2. change (128 / 8) with 16. lz.
  - exact I. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & H10c & Hset5 & Hun5 & Hpr5 & Hsm5).
Time pose proof (proj1 alloc_ceiling_val) as HCE.
(* the flag word, from the frame region's chunk, at the memset's return *)
Time pose proof (field_of_region (segs := pa_segs) E _ 44 F _ _ _ _ _ 120 8%N (SOff 61 0) FL HR1 U44
  ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lz) ltac:(cbn; lz)) as VFL4.
Time assert (VFL5 : val_mem pa_segs (rdW W2 mem5) (F + 120) 8 FL).
{ apply (mr_val_mem_move pa_segs (rdW W2 (ms_mem ms4)) _ _ 8 FL VFL4). intros x Hx.
  apply (mbyte_of_aview pa_segs). apply Hun5; [unfold kLowMemEnd in *; lz | lz | rewrite Usp4, HES; lz]. }
(* the state after the memset: the shadow, the realigned area and the saved words (the frame's bytes changed) *)
Time jafter_call_keep_hi HS4 760%nat regs5 (mrestrict (w_H W2) mem5) HP5 [0; 2; 3]%nat HS5.
match type of HS5 with ?tq -> _ => assert (HRK : tq); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil; (split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    [ intros a Ha; apply (mbyte_of_aview pa_segs); rewrite ?U62, ?U60, ?Usp in Ha;
      apply Hun5; [unfold MR_SB in *; lz | unfold MR_SB in *; lz | rewrite Usp4, HES; unfold MR_SB in *; lz]
    | intros a Ha Hw; exact (writable_kept (segs := pa_segs) (w_H W2) (ms_mem ms4) mem5 a (Hpr5 a) Hw) ]). }
clear HS4. rewrite <- restrict_mkst_fx in HS5.
Time remember (havoc E 760 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS5.
Time assert (HEI5 : img_env pa_val A_LIM E5) by (rewrite HE5; apply img_env_havoc_hi; [exact HEI | cbv; lz]).
Time assert (OLD5 : forall n, (n < 760)%nat -> ew E5 n = ew E n)
  by (intros n Hn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hn).
Time assert (HED5 : ed E5 = ed E) by (rewrite HE5; reflexivity).
clear HE5.
Time assert (U44_5 : bv_unsigned (ew E5 44) = F) by (rewrite OLD5 by lz; exact U44).
Time assert (U61_5 : bv_unsigned (ew E5 61) = FL) by (rewrite OLD5 by lz; exact U61).
Time assert (U62_5 : bv_unsigned (ew E5 62) = MR_SB + F / 8) by (rewrite OLD5 by lz; exact U62).
Time assert (U60_5 : bv_unsigned (ew E5 60) = sp1) by (rewrite OLD5 by lz; exact U60).
Time assert (Usp_5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lz; exact Usp).
Time assert (E61_5 : ew E5 61 = Z_to_bv 64 FL) by (rewrite OLD5 by lz; exact E61).
(* the frame again, its flag word at 120 *)
lazymatch type of HS5 with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 1 [YP09.mkChunk 44 (CZero 20)]) HS5 eq_refl
  ltac:(unfold region_ok, fframe_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 1) with 128; rewrite U44_5; split; [lz|]; split; [lz|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs); apply Hpr5; apply (apresent_grows _ _ _ _ HG4);
          apply (HFpres2 (F + o)); unfold in_zr, frame_rng; cbn [fst snd];
          fold F; change (fs_frame_bytes 1) with 128; lz
        | apply Forall_cons;
          [ apply chunk_ok_zero; intros i Hi; destruct (aview_byte pa_segs _ _ _ _ (Hset5 i Hi)) as (bb & Hbb & Hv & _);
            rewrite Hbb; f_equal; apply bv_eq; rewrite <- Hv; reflexivity |];
          apply Forall_cons; [|apply Forall_nil];
          apply (chunk_ok_val pa_segs _ _ F 120 8 _ FL);
          [ cbn [sv_denot]; rewrite E61_5, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VFL5 ] ])
  ltac:(mr_disj; rewrite ?U60_5, ?U44_5, ?U62_5, ?Usp_5; unfold MR_SB in *; repeat split; lz)) as HS3 end.
clear HS5; rename HS3 into HS5; norm_pi HS5.
(* ---- +0x1ac .. +0x1e4 (plain): the request's header words and index, talk's arguments ---- *)
Time rewrite Q1.
lazymatch type of HS5 with
| st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
    lazymatch r with (?ssf, PRS_call ?sf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
      eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI5 HS5 Hrun HJ5);
      clear Hrun
    end
  end
end.
{ cbn [ss_mem].
  repeat (apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fframe_region fshadow_region]; intros a Ha;
      rewrite ?U60_5, ?Usp_5, ?U44_5, ?U62_5 in Ha;
      first
        [ left; split; [left; rewrite HK8 in Hwlo; lz | lz]
        | left; apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
            ((1, pos) :: own) ly2 S2 W2 mem5 md5 k 1 pos a HJ5 ltac:(left; reflexivity));
          rewrite FA; fold F;
          first [ left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F;
                  change (fs_frame_bytes 1) with 128 in Ha; lz
                | right; unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16 in *;
                  unfold MR_SB, SHADOW_OFF in *; lz ] ]
    |]);
  apply awr_ok_x_nil. }
cbv beta. intros ms7 mat7 HS7 HJ7 HFm7 HFr7 HG7.
cbn [ms_mem mkst] in HFm7, HFr7, HG7.
pmkst HS7.
Time prreg HS7 (1%bv : bv 5) P1. prreg HS7 (2%bv : bv 5) P2. prreg HS7 (3%bv : bv 5) P3. prreg HS7 (4%bv : bv 5) P4.
Time prreg HS7 (10%bv : bv 5) P10. prreg HS7 (11%bv : bv 5) P11. prreg HS7 (12%bv : bv 5) P12.
Time prreg HS7 (13%bv : bv 5) P13. prreg HS7 (14%bv : bv 5) P14. prreg HS7 (15%bv : bv 5) P15. prreg HS7 (16%bv : bv 5) P16.
Time set (m7 := ms_mem ms7) in *. set (regs7 := ms_regs ms7) in *.
Time set (md7 := with_vm_backing (m_vm_lazy md5) mat7 md5) in *.
(* ---- the entry's facts the talk call needs ---- *)
Time assert (EA : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; rewrite (proj1 HAE n Hn); exact (ew_Ereg_nat regs _ n r Hr)).
Time pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & PMOD & PMWF & PNLK & PNWF & PTAB & PNM & PBK & PBA & PRAN & PRAI & PSCN
  & PSCT & PRAM & PHUM & PMR & PRAC & PHUC & PGNM & PFRM & PFRK & PFRA & PERM & PERK & PERA & PKB & PAB & PNSEP & PKA).
Time set (KB := fun a => aarg regs 2 <> 0 /\ 1 <= aarg regs 3 /\ a = aarg regs 2) in *.
Time set (AB := fun a => aarg regs 4 <> 0 /\ 1 <= aarg regs 5 /\ a = aarg regs 4) in *.
Time set (EX2 := fun a => aside_rng lyc 1 pos a \/ KB a \/ AB a) in *.
Time pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as HAR.
Time assert (Hsk : alloc_ceiling <= spZ regs - MODEL_READ_AK) by lz.
Time pose proof HAR1 as [M1 _].
Time destruct (frame_facts B lyc S1 _ 1 pos M1 Hin1) as (Hc1 & Hp1 & _).
Time assert (WRF : forall a, inFP (model_read_awr regs (rdW W memc)) a ->
          (a < kLowMemEnd \/ kHighMemBeg <= a) /\ ~ (spZ regs - MODEL_READ_AK <= a < spZ regs) /\ 0 <= a < 2 ^ 64 /\
          ~ aside_rng lyc 1 pos a).
{ intros a Ha. destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    HENT a Ha) as (Xapp & Xwin & _ & Xajw & X64).
  refine (conj Xapp (conj Xwin (conj X64 _))).
  exact (ajw_not_side SK pa_segs B LAWS pa_img_range G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
    mdc k 1 pos _ HGok HJ Hc1 Hp1 Hnin Xajw Xapp). }
Time assert (KBW : forall a, KB a -> inFP (model_read_awr regs (rdW W memc)) a).
{ intros a (h2 & h3 & ->). exists (aarg regs 2, aarg regs 2 + aarg regs 3). split; [|cbn [fst snd]; lz].
  right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h2). reflexivity. }
Time assert (ABW : forall a, AB a -> inFP (model_read_awr regs (rdW W memc)) a).
{ intros a (h4 & h5 & ->). exists (aarg regs 4, aarg regs 4 + aarg regs 5). split; [|cbn [fst snd]; lz].
  right; right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h4). reflexivity. }
Time assert (BLK : forall i, 0 <= i < MD_SIZE -> inFP (model_read_awr regs (rdW W memc)) (aarg regs 0 + i)).
{ intros i Hi. exists (aarg regs 0, aarg regs 0 + MD_SIZE). split; [left; reflexivity | cbn [fst snd]; lz]. }
(* the side frame's bytes and the stack window cover what the stretch since the cut wrote *)
Time assert (SIDEF : forall a, F <= a < F + 128 -> aside_rng lyc 1 pos a).
{ intros a Ha. left. unfold in_zr, frame_rng. cbn [fst snd]. fold F. change (fs_frame_bytes 1) with 128. lz. }
Time assert (SIDES : forall a, MR_SB + F / 8 <= a < MR_SB + F / 8 + 16 -> aside_rng lyc 1 pos a).
{ intros a Ha. right; left. unfold in_zr, shadow_addr. cbn [fst snd]. fold F. change (fs_frame_bytes 1 / 8) with 16.
  unfold MR_SB, SHADOW_OFF in *. lz. }
Time set (XW := fun a => aside_rng lyc 1 pos a \/ spZ regs - MODEL_READ_AK <= a < spZ regs).
Time pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ XW HFr4
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                rewrite ?U60, ?Usp, ?U44, ?U62 in Hrr; unfold XW; cbv beta;
                first [ right; rewrite HK8; lz | left; apply SIDEF; lz | left; apply SIDES; unfold MR_SB in *; lz ] |]);
        destruct Hin)) as UN4.
Time pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ XW HFr7
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                rewrite ?U60_5, ?Usp_5, ?U44_5, ?U62_5 in Hrr; unfold XW; cbv beta;
                first [ right; rewrite HK8; lz | left; apply SIDEF; lz | left; apply SIDES; unfold MR_SB in *; lz ] |]);
        destruct Hin)) as UN7.
Time assert (HK4 : akept pa_segs B lyc Sc W memc W2 (ms_mem ms4) (spZ regs - MODEL_READ_AK) (spZ regs) EX2).
{ exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W2 (ms_mem ms) W2 (ms_mem ms4)
    (spZ regs - MODEL_READ_AK) (spZ regs) EX2 EX2 XW HAR Hsk ltac:(lz) HK UN4
    (fun a _ Hp => apresent_grows _ _ _ _ HG4 Hp) (fun a H => H)
    ltac:(intros a [Ha | Ha]; [left; left; exact Ha | right; exact Ha])). }
Time assert (HK5 : akept pa_segs B lyc Sc W memc W2 mem5 (spZ regs - MODEL_READ_AK) (spZ regs) EX2).
{ refine (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W2 (ms_mem ms4) W2 mem5
    (spZ regs - MODEL_READ_AK) (spZ regs) EX2 EX2 (fun a => F + 44 <= a < F + 64 \/ sp1 - ESTACK <= a < sp1)
    HAR Hsk ltac:(lz) HK4 _ (fun a _ Hp => Hpr5 a Hp) (fun a H => H) _).
  - intros a Ha Hn. apply Hun5; [exact Ha | intros Hq; apply Hn; left; lz | intros Hq; apply Hn; right; rewrite Usp4 in Hq; exact Hq].
  - intros a [Ha | Ha]; [left; left; apply SIDEF; lz | right; rewrite HES in Ha; lz]. }
Time assert (HK7 : akept pa_segs B lyc Sc W memc W2 m7 (spZ regs - MODEL_READ_AK) (spZ regs) EX2).
{ exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W2 mem5 W2 m7
    (spZ regs - MODEL_READ_AK) (spZ regs) EX2 EX2 XW HAR Hsk ltac:(lz) HK5 UN7
    (fun a _ Hp => apresent_grows _ _ _ _ HG7 Hp) (fun a H => H)
    ltac:(intros a [Ha | Ha]; [left; left; exact Ha | right; exact Ha])). }
Time assert (PR7 : forall a, apresent (w_H W2) (ms_mem ms) a -> apresent (w_H W2) m7 a)
  by (intros a Hp; apply (apresent_grows _ _ _ _ HG7); apply Hpr5; exact (apresent_grows _ _ _ _ HG4 Hp)).
Time assert (MV7 : forall a, inFP (model_read_awr regs (rdW W memc)) a -> ~ KB a -> ~ AB a ->
          aview pa_segs (w_H W2) m7 a = aview pa_segs (w_H W) memc a).
{ intros a Ha Hk Hab. destruct (WRF a Ha) as (_ & _ & _ & XNS).
  exact (mr_wr_view SK B LAWS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs W2 m7 EX2 a
    HENT Ha HK7 ltac:(intros [Hq | [Hq | Hq]]; [exact (XNS Hq) | exact (Hk Hq) | exact (Hab Hq)])). }
Time assert (WR7 : forall a, inFP (model_read_awr regs (rdW W memc)) a -> writable_at pa_segs (rdW W memc) a ->
          writable_at pa_segs (rdW W2 m7) a)
  by (intros a Ha Hw; exact (writable_kept (segs := pa_segs) (w_H W2) (ms_mem ms) m7 a (PR7 a) (WRX a Ha Hw))).
(* talk's arguments *)
Time assert (A70 : aarg regs7 0 = aarg regs 0).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite P10, OLD5 by lz. rewrite (EA 10%nat 10%bv ltac:(lz) eq_refl). reflexivity. }
Time assert (A71 : aarg regs7 1 = F + 32).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite P11, U44_5. apply unsigned_lit_small. lz. }
Time assert (A72 : aarg regs7 2 = 32).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 2)) with (12%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite P12. reflexivity. }
Time assert (A73 : aarg regs7 3 = aarg regs 2).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (10 + 2)) with (12%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite P13, OLD5 by lz. rewrite (EA 12%nat 12%bv ltac:(lz) eq_refl). reflexivity. }
Time assert (A74 : aarg regs7 4 = aarg regs 3).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite P14, OLD5 by lz. rewrite (EA 13%nat 13%bv ltac:(lz) eq_refl). reflexivity. }
Time assert (A75 : aarg regs7 5 = aarg regs 4).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 5)) with (15%bv : bv 5) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite P15, OLD5 by lz. rewrite (EA 14%nat 14%bv ltac:(lz) eq_refl). reflexivity. }
Time assert (A76 : aarg regs7 6 = aarg regs 5).
{ unfold aarg, argZ. replace (Z_to_bv 5 (10 + 6)) with (16%bv : bv 5) by (apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (10 + 5)) with (15%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite P16, OLD5 by lz. rewrite (EA 15%nat 15%bv ltac:(lz) eq_refl). reflexivity. }
Time assert (Usp7 : spZ regs7 = sp1) by (unfold spZ; rewrite P2, OLD5 by lz; exact U60).
Time sregion HS7 0%nat HR70. sregion HS7 1%nat HR71.
(* ---- talk's Pre at the call ---- *)
Time assert (GNX : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> ~ EX2 x).
{ intros x Hx [Hq | [Hq | Hq]].
  - destruct (mr_gnl_img B TB HSEGS x Hx) as (Hi & _ & _).
    exact (proj1 (mr_aside_facts B LAWS lyc S1 W1 mem1 md1 pos HAR1 Hin1 x Hq) Hi).
  - destruct Hq as (h2 & h3 & ->). destruct (PKB h2 h3) as (Hg & _). unfold apart_gnl in Hg. lz.
  - destruct Hq as (h4 & h5 & ->). destruct (PAB h4 h5) as (Hg & _). unfold apart_gnl in Hg. lz. }
Time assert (HWg : forall (mm : word -> option byte) a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at pa_segs mm a)
  by (intros mm a Ha; rewrite HSEGS; apply LA_G_NL_writable; unfold NK_SIZE in Ha; exact Ha).
Time assert (HN7 : anlk_at pa_segs (rdW W2 m7) LA_G_NL kbs0).
{ apply (mr_anlk_move pa_segs (rdW W memc) _ LA_G_NL kbs0 PNLK).
  - intros x Hx. apply (mbyte_of_aview pa_segs).
    exact (mr_gnl_view_k B TB HSEGS lyc Sc W memc W2 m7 _ _ EX2 x HK7 Hx (GNX x Hx)).
  - intros x Hx. apply HWg. exact Hx. }
Time assert (MNK : forall x, aarg regs 0 <= x < aarg regs 0 + MD_SIZE -> ~ KB x /\ ~ AB x).
{ intros x Hx. split.
  - intros (h2 & h3 & ->). destruct (PKB h2 h3) as (_ & KM & _). unfold apart in KM. lz.
  - intros (h4 & h5 & ->). destruct (PAB h4 h5) as (_ & AM & _). unfold apart in AM. lz. }
Time assert (HM7 : amodel_at pa_segs (rdW W2 m7) (aarg regs 0) mbs0).
{ apply (mr_amodel_move pa_segs (rdW W memc) _ _ mbs0 PMOD).
  - intros x Hx. apply (mbyte_of_aview pa_segs). destruct (MNK x Hx) as (Hk & Ha).
    apply MV7; [replace x with (aarg regs 0 + (x - aarg regs 0)) by lz; apply BLK; lz | exact Hk | exact Ha].
  - intros x Hx. assert (Hb : inFP (model_read_awr regs (rdW W memc)) x)
      by (replace x with (aarg regs 0 + (x - aarg regs 0)) by lz; apply BLK; lz).
    apply (WR7 x Hb). destruct PMOD as ((_ & Hw) & Hl). replace x with (aarg regs 0 + (x - aarg regs 0)) by lz.
    apply Hw. rewrite Hl. lz. }
(* the request: the stores' chunks and checked_memset's zeros *)
Time pose proof (field_of_region (segs := pa_segs) E5 _ 44 F _ _ _ _ _ 32 4%N (SLit 32) 32 HR70 U44_5
  ltac:(cbn; tauto) eq_refl ltac:(cbn; lz) ltac:(cbn; lz)) as V0.
Time pose proof (field_of_region (segs := pa_segs) E5 _ 44 F _ _ _ _ _ 36 4%N (SLit 65554) 65554 HR70 U44_5
  ltac:(cbn; tauto) eq_refl ltac:(cbn; lz) ltac:(cbn; lz)) as V4.
Time pose proof (field_of_region (segs := pa_segs) E5 _ 44 F _ _ _ _ _ 40 4%N (SLit 1) 1 HR70 U44_5
  ltac:(cbn; tauto) eq_refl ltac:(cbn; lz) ltac:(cbn; lz)) as V8.
Time pose proof (field_of_region (segs := pa_segs) E5 _ 44 F _ _ _ _ _ 52 4%N (SOff 724 0) idx HR70 U44_5
  ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite OLD5 by lz; rewrite E724, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lz) ltac:(cbn; lz)) as V20.
Time assert (HRQ7 : abytes pa_segs (rdW W2 m7) (F + 32) (req_read idx)).
{ apply mr_req_read_bytes; [lz | lz | exact V0 | replace (F + 32 + 4) with (F + 36) by lz; exact V4
  | replace (F + 32 + 8) with (F + 40) by lz; exact V8 | | replace (F + 32 + 20) with (F + 52) by lz; exact V20 |].
  - intros i Hi.
    assert (Hz : aview pa_segs (w_H W2) m7 (F + 44 + (i - 12)) = Some 0)
      by (eapply (zero_byte_of_region pa_segs) with (len := 8); [exact HR70 | cbn [base_val]; exact U44_5 | cbn; tauto | lz]).
    destruct (aview_byte pa_segs _ _ _ _ Hz) as (bb & Hbb & Hv & _).
    replace (F + 32 + i) with (F + 44 + (i - 12)) by lz. rewrite Hbb. f_equal. apply bv_eq. rewrite <- Hv. reflexivity.
  - intros i Hi.
    assert (Hz : aview pa_segs (w_H W2) m7 (F + 56 + (i - 24)) = Some 0)
      by (eapply (zero_byte_of_region pa_segs) with (len := 8); [exact HR70 | cbn [base_val]; exact U44_5 | cbn; tauto | lz]).
    destruct (aview_byte pa_segs _ _ _ _ Hz) as (bb & Hbb & Hv & _).
    replace (F + 32 + i) with (F + 56 + (i - 24)) by lz. rewrite Hbb. f_equal. apply bv_eq. rewrite <- Hv. reflexivity. }
(* the request's shadow: bytes 4..7 of the frame's shadow are 0, all eight of its group are present *)
Time assert (SH7 : forall j, 4 <= j < 8 -> aview pa_segs (w_H W2) m7 (SHADOW_OFF + F / 8 + j) = Some 0).
{ intros j Hj.
  assert (Hin : In (YP09.mkChunk j (CVal 1 (SLit 0)))
                   [YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0));
                    YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0))]).
  { assert (Hc : j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lz.
    destruct Hc as [-> | [-> | [-> | ->]]]; cbn [In]; tauto. }
  pose proof (field_of_region (segs := pa_segs) E5 _ 62 (MR_SB + F / 8) _ _ _ _ _ j 1%N (SLit 0) 0 HR71 U62_5 Hin
    eq_refl ltac:(cbn; lz) ltac:(cbn; lz)) as Hv.
  specialize (Hv 0%nat ltac:(cbn; lz)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
  unfold aview. change SHADOW_OFF with MR_SB. change (ms_mem ms7) with m7 in Hv. rewrite Hv. reflexivity. }
Time assert (SHP7 : forall j, 0 <= j < 16 -> aview pa_segs (w_H W2) m7 (SHADOW_OFF + F / 8 + j) <> None).
{ intros j Hj.
  first [ apply (mr_aview_present (w_H W2) m7) | apply (mr_aview_present B (w_H W2) m7) ].
  apply PR7. replace (SHADOW_OFF + F / 8 + j) with (shadow_addr F + j) by (unfold shadow_addr; lz).
  apply HFSpres2. change (128 / 8) with 16. lz. }
(* the entry's write set and the side frame do not meet *)
Time assert (NSW : forall a, aside_rng lyc 1 pos a -> inFP (model_read_awr regs (rdW W memc)) a -> False)
  by (intros a Hs Ha; exact (proj2 (proj2 (proj2 (WRF a Ha))) Hs)).
Time assert (FM2 : fmiss lyc Sc EX2).
{ apply fmiss_or; [exact (fmiss_side pa_segs B lyc Sc W memc mdc 1 pos HAR Hc1 Hp1 Hnin)|].
  apply fmiss_or.
  - apply (fmiss_app pa_segs B LAWS lyc Sc W memc mdc KB HAR). intros x Hx. exact (proj1 (WRF x (KBW x Hx))).
  - apply (fmiss_app pa_segs B LAWS lyc Sc W memc mdc AB HAR). intros x Hx. exact (proj1 (WRF x (ABW x Hx))). }
Time pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 m7 md7 k HJ7)
  as HAR7.
Time pose proof HJ7 as R7. apply (aj_stk_row_eq SK pa_segs B) in R7.
Time pose proof HJ as Rc. apply (aj_stk_row_eq SK pa_segs B) in Rc.
Time assert (Elo : ly_stk_lo ly2 = ly_stk_lo lyc) by (rewrite (proj1 R7), (proj1 Rc); reflexivity).
Time assert (Ehi : ly_stk_hi ly2 = ly_stk_hi lyc) by (rewrite (proj2 R7), (proj2 Rc); reflexivity).
Time assert (Hbl2 : forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm2 | exact Hb]).
Time assert (WAKB : forall a, inFP (model_read_awr regs (rdW W memc)) a ->
          akb pa_segs B lyc Sc (spZ regs - MODEL_READ_AK) (spZ regs) a).
{ intros a Ha.
  destruct (mr_wr_facts SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HENT a Ha)
    as (Happ & Hwin & Herr & Hajw' & Ha64).
  exact (ajw_akb SK pa_segs B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc Sc
    (spZ regs - MODEL_READ_AK) (spZ regs) a HGok HJ Hajw' Hwin Happ Herr eq_refl eq_refl (fun b m H => H)
    (fun c q H => H) (fun c q => eq_refl)). }
(* a range of the write set keeps its shadow facts at the call *)
Time assert (SHT : forall p n, 0 < n -> (forall x, p <= x < p + n -> inFP (model_read_awr regs (rdW W memc)) x) ->
          range_addressable (ard pa_segs (rdW W memc)) SHADOW_OFF p n ->
          shadow_hull_vis (ard pa_segs (rdW W memc)) p n ->
          range_addressable (ard pa_segs (rdW W2 m7)) SHADOW_OFF p n /\ shadow_hull_vis (ard pa_segs (rdW W2 m7)) p n).
{ intros p n Hn Hw Hra Hhv.
  exact (shadow_transport pa_segs B LAWS TB pa_img_range lyc Sc W memc mdc ly2 S2 W2 m7 md7
    (spZ regs - MODEL_READ_AK) (spZ regs) EX2 p n HAR HAR7 Elo Ehi Hbl2 HK7 FM2 Hn
    ltac:(intros x Hx; eapply sclass_of_akb; first [exact LAWS | exact TB | exact pa_img_range | apply WAKB; apply Hw; lz])
    Hra Hhv). }
(* the first bytes of the two buffers are 0 at the call, the rest as at the entry *)
Time assert (NW7 : forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng lyc 1 pos a -> ~ (spZ regs - MODEL_READ_AK <= a < spZ regs) ->
          aview pa_segs (w_H W2) m7 a = aview pa_segs (w_H W2) (ms_mem ms) a).
{ intros a Ha Hs Hw.
  rewrite (UN7 a Ha ltac:(intros [Hq | Hq]; [exact (Hs Hq) | exact (Hw Hq)])).
  rewrite (Hun5 a Ha ltac:(intros Hq; apply Hs; apply SIDEF; lz) ltac:(rewrite Usp4, HES; lz)).
  exact (UN4 a Ha ltac:(intros [Hq | Hq]; [exact (Hs Hq) | exact (Hw Hq)])). }
Time assert (KIV : forall i, 0 <= i < aarg regs 3 -> aarg regs 2 <> 0 -> inFP (model_read_awr regs (rdW W memc)) (aarg regs 2 + i)).
{ intros i Hi h2. exists (aarg regs 2, aarg regs 2 + aarg regs 3). split; [|cbn [fst snd]; lz].
  right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h2). reflexivity. }
Time assert (AIV : forall i, 0 <= i < aarg regs 5 -> aarg regs 4 <> 0 -> inFP (model_read_awr regs (rdW W memc)) (aarg regs 4 + i)).
{ intros i Hi h4. exists (aarg regs 4, aarg regs 4 + aarg regs 5). split; [|cbn [fst snd]; lz].
  right; right; left. unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) h4). reflexivity. }
Time assert (BZ7 : forall p n, p <> 0 -> 1 <= n -> abuf pa_segs (rdW W memc) p n ->
          (forall i, 0 <= i < n -> inFP (model_read_awr regs (rdW W memc)) (p + i)) ->
          aview pa_segs (w_H W2) (ms_mem ms) p = Some 0 ->
          (forall i, 1 <= i < n -> ~ KB (p + i) /\ ~ AB (p + i)) ->
          acstr_at pa_segs (rdW W2 m7) p [] /\ abuf pa_segs (rdW W2 m7) p n).
{ intros p n Hp0 Hn Hbuf HW HZ HKA.
  apply (mr_bufz pa_segs (rdW W memc) (rdW W2 m7) p n Hn Hbuf).
  - assert (HWp : inFP (model_read_awr regs (rdW W memc)) p) by (rewrite <- (Z.add_0_r p); apply HW; lz).
    destruct (WRF p HWp) as (_ & Xwin & X64 & XNS).
    assert (Hz : aview pa_segs (w_H W2) m7 p = Some 0) by (rewrite (NW7 p X64 XNS Xwin); exact HZ).
    destruct (aview_byte pa_segs _ _ _ _ Hz) as (bb & Hbb & Hv & _).
    rewrite Hbb. f_equal. apply bv_eq. rewrite <- Hv. reflexivity.
  - intros i Hi. apply (mbyte_of_aview pa_segs). destruct (HKA i Hi) as (Hk & Ha).
    exact (MV7 (p + i) (HW i ltac:(lz)) Hk Ha).
  - intros x Hx. replace x with (p + (x - p)) by lz. apply (WR7 (p + (x - p)) (HW (x - p) ltac:(lz))).
    destruct Hbuf as (junk & Hl & (_ & Hw)). apply Hw. lz. }
Time assert (KZ7 : aarg regs 2 <> 0 -> 1 <= aarg regs 3 ->
          acstr_at pa_segs (rdW W2 m7) (aarg regs 2) [] /\ abuf pa_segs (rdW W2 m7) (aarg regs 2) (aarg regs 3)).
{ intros h2 h3. apply (BZ7 (aarg regs 2) (aarg regs 3) h2 h3 (PBK h2 h3) (fun i Hi => KIV i Hi h2) (HK0 h2 h3)).
  intros i Hi. split.
  - intros (_ & _ & Hq). lz.
  - intros (h4 & h5 & Hq). pose proof (PKA h2 h4 h3 h5) as Hs. unfold apart in Hs. lz. }
Time assert (AZ7 : aarg regs 4 <> 0 -> 1 <= aarg regs 5 ->
          acstr_at pa_segs (rdW W2 m7) (aarg regs 4) [] /\ abuf pa_segs (rdW W2 m7) (aarg regs 4) (aarg regs 5)).
{ intros h4 h5. apply (BZ7 (aarg regs 4) (aarg regs 5) h4 h5 (PBA h4 h5) (fun i Hi => AIV i Hi h4) (HA0 h4 h5)).
  intros i Hi. split.
  - intros (h2 & h3 & Hq). pose proof (PKA h2 h4 h3 h5) as Hs. unfold apart in Hs. lz.
  - intros (_ & _ & Hq). lz. }
Time assert (EWR : talk_awr regs7 (rdW W2 m7) = model_read_awr regs (rdW W memc))
  by (unfold talk_awr, model_read_awr; rewrite A70, A73, A74, A75, A76; reflexivity).
Time assert (HPRE7 : talk_apre pa_segs regs7 (rdW W2 m7)).
{ exists mbs0, kbs0, (req_read idx).
  rewrite A70, A71, A72, A73, A74, A75, A76.
  pose proof (zsh_gnl_ard B TB pa_segs ly2 S2 W2 m7 md7 HAR7) as (Hgra & Hghv).
  split; [exact HM7|]. split; [exact PMWF|]. split; [exact HN7|]. split; [exact PNWF|].
  split; [exact HRQ7|]. split; [rewrite req_read_len; reflexivity|]. split; [unfold NL_SENT_LEN; lz|].
  split; [intros h2 h3; exact (proj2 (KZ7 h2 h3))|].
  split; [intros h4 h5; exact (proj2 (AZ7 h4 h5))|].
  destruct (SHT (aarg regs 0) MD_SIZE ltac:(unfold MD_SIZE; lz)
    ltac:(intros x Hx; replace x with (aarg regs 0 + (x - aarg regs 0)) by lz; apply BLK; lz) PRAM PHUM)
    as (RAM7 & HUM7).
  split; [exact RAM7|]. split; [exact HUM7|]. split; [exact PMR|].
  split; [intros x Hx; apply Hgra; unfold NK_CHUNK, NK_N_CHUNKS, NK_SIZE in *; lz|].
  split; [apply (mr_hull_sub _ LA_G_NL NK_SIZE); [exact Hghv | unfold NK_CHUNK; lz | unfold NK_N_CHUNKS; lz
                                               | unfold NK_CHUNK, NK_N_CHUNKS, NK_SIZE; lz | unfold LA_G_NL; lz]|].
  split; [unfold amem_range; destruct HFapp2 as (Hf4x & [Hlowx | (Hhighx & Hhcx)]); [left | right];
          unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lz|].
  split; [apply (mr_req_ra _ F); [lz | lz | exact SH7 | lz | lz]|].
  split.
  { intros _ s' Hs. unfold shadow_addr in Hs.
    replace s' with (SHADOW_OFF + F / 8 + (s' - (SHADOW_OFF + F / 8))) by lz.
    apply SHP7. unfold MR_SB, SHADOW_OFF in *. lz. }
  split.
  { apply mr_apart_of_disj; [lz | unfold MD_SIZE; lz |]. intros a Ha Hb.
    apply (NSW a (SIDEF a ltac:(lz))). replace a with (aarg regs 0 + (a - aarg regs 0)) by lz. apply BLK. lz. }
  split.
  { intros h2 h3. destruct (PKB h2 h3) as (Kg & Km & _ & Kam & Kra & Khu).
    assert (HKw : forall x, aarg regs 2 <= x < aarg regs 2 + aarg regs 3 -> inFP (model_read_awr regs (rdW W memc)) x)
      by (intros x Hx; replace x with (aarg regs 2 + (x - aarg regs 2)) by lz; apply KIV; [lz | exact h2]).
    destruct (SHT (aarg regs 2) (aarg regs 3) ltac:(lz) HKw Kra Khu) as (Kra7 & Khu7).
    split; [exact Kg|]. split; [exact Km|]. split; [exact Kam|]. split; [exact Kra7 | exact Khu7]. }
  split.
  { intros h4 h5. destruct (PAB h4 h5) as (Ag & Am & _ & Aam & Ara & Ahu).
    assert (HAw : forall x, aarg regs 4 <= x < aarg regs 4 + aarg regs 5 -> inFP (model_read_awr regs (rdW W memc)) x)
      by (intros x Hx; replace x with (aarg regs 4 + (x - aarg regs 4)) by lz; apply AIV; [lz | exact h4]).
    destruct (SHT (aarg regs 4) (aarg regs 5) ltac:(lz) HAw Ara Ahu) as (Ara7 & Ahu7).
    split; [exact Ag|]. split; [exact Am|]. split; [exact Aam|]. split; [exact Ara7 | exact Ahu7]. }
  split; [intros h2 h3 h4 h5; exact (PKA h2 h4 h3 h5)|]. split; [exact PGNM|].
  split; [unfold apart_frame in *; rewrite Usp7; unfold TALK_AK, TALK_AFRAME; rewrite HES; rewrite HK8 in PFRM; lz|].
  split; [unfold apart_frame; rewrite Usp7; unfold TALK_AK, TALK_AFRAME; rewrite HES; left; lz|].
  split; [intros h2; pose proof (PFRK h2) as Q; unfold apart_frame in *; rewrite Usp7; unfold TALK_AK, TALK_AFRAME;
          rewrite HES; rewrite HK8 in Q; lz|].
  intros h4; pose proof (PFRA h4) as Q; unfold apart_frame in *; rewrite Usp7; unfold TALK_AK, TALK_AFRAME;
    rewrite HES; rewrite HK8 in Q; lz. }
Time assert (HAPRE7 : apre SK pa_segs 0 0 B TALK_AK 0 [] (talk_awr regs7 (rdW W2 m7)) G XO OUT STK sp0 FP ly S W0 mem0 md0
          ((1, pos) :: own) ly2 S2 W2 m7 md7 k regs7).
{ unfold apre. rewrite EWR.
  split; [exact HJ7|]. split; [exact HGok|].
  split.
  { refine (mr_arodata_k B LAWS rlo rhi lyc Sc W memc W2 m7 _ _ EX2 (fun a => inFP (model_read_awr regs (rdW W memc)) a)
      S1 W1 mem1 md1 pos HROD HK7 HAR1 Hin1 _ _).
    - intros a [Hq | [Hq | Hq]]; [left; exact Hq | right; exact (KBW a Hq) | right; exact (ABW a Hq)].
    - intros a Ha. exact (Hnro a Ha). }
  split; [rewrite P1; apply ret_ok_codeptr_v; [lz | reflexivity]|].
  split; [unfold raZ; rewrite P1; pose proof pa_B_ok as (HB0 & HB1 & HB2); rewrite unsigned_lit_small by lz; lz|].
  split; [rewrite P3, OLD5 by lz; rewrite (EA 3%nat 3%bv ltac:(lz) eq_refl); exact Hgp|].
  split; [rewrite P4, OLD5 by lz; rewrite (EA 4%nat 4%bv ltac:(lz) eq_refl); exact Htp|].
  split; [rewrite Usp7; exact Hsp1al16|].
  split; [rewrite Usp7; unfold TALK_AK, TALK_AFRAME; rewrite HES; rewrite HK8 in Hwlo; lz|].
  split; [rewrite Usp7; lz|].
  split; [lz|].
  split; [apply Forall_nil|].
  split.
  - intros a Ha. apply (ajw_mono B _ _ _ _ _ _ _ _ lyc Sc own ly2 S2 ((1, pos) :: own) a (Hajw a Ha) Hbl2
      (fun x Hx => or_intror Hx)).
    intros c q. destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ7) as (Fc7 & _).
    destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ) as (Fcc & _).
    congruence.
  - intros a Ha [Hl | Hr]; [apply (Hnro a Ha); left; exact Hl | lz]. }
assert (HRD7 : forall a, talk_ard regs7 (rdW W2 m7) a ->
          akb pa_segs B ly2 S2 (spZ regs7 - TALK_AK) (spZ regs7) a).
{ intros a Ha. unfold talk_ard, rd_ivl in Ha. rewrite A71, A72 in Ha.
  right; right; right. exists 1, pos. split; [exact Hin2|].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite FA. fold F. change (fs_frame_bytes 1) with 128. lz. }
(* ---- +0x1e8: talk(m, r, 32, kind, kind_n, alias, alias_n) ---- *)
assert (Hsig : pa_sigma LS_talk = TALK_A) by (rewrite (lv_sigma LV); reflexivity).
rewrite Hsig.
eapply SRr_bind.
{ exact (TALK 0 0 G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 m7 md7 k regs7
    HAPRE7 HRD7 HPRE7). }
intros W8 c8 _ (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & Hpres8 & Hfr8 & Hfd8 & Hfs8 & HK8t & Hsh8 & HS8f & Hperm8 & HTP).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly8 S8 W8 mem8 md8 (k + 0)
  HJ8) as HAR8.
assert (Hin8 : In (1, pos) (frames S8)) by (rewrite Hfr8; exact Hin2).
destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 pos HJ8) as (FA8 & FL8).
assert (FA8' : frame_addr ly8 1 pos = F) by (rewrite FA8, FA1; reflexivity).
destruct (al_frames _ _ LAWS ly8 S8 W8 mem8 md8 1 pos HAR8 Hin8) as (_ & _ & HFpres8 & HFSpres8).
rewrite FA8' in HFpres8, HFSpres8.
pose proof (aj_gx_present SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own)
  ly8 S8 W8 mem8 md8 (k + 0) HJ8) as Hpres8x.
pose proof HK8t as (K81 & K82 & K83 & K84 & K85 & K86).
assert (NE8 : forall a, aside_rng lyc 1 pos a -> ~ inFP (talk_awr regs7 (rdW W2 m7)) a)
  by (intros a Hs Ha; rewrite EWR in Ha; exact (NSW a Hs Ha)).
(* the flag word at talk's return *)
pose proof (field_of_region (segs := pa_segs) E5 _ 44 F _ _ _ _ _ 120 8%N (SOff 61 0) FL HR70 U44_5
  ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E61_5, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
  ltac:(cbn; lz) ltac:(cbn; lz)) as VFL7.
assert (VFL8 : val_mem pa_segs (rdW W8 mem8) (F + 120) 8 FL).
{ apply (mr_val_mem_move pa_segs (rdW W2 m7) _ _ 8 FL VFL7). intros x Hx.
  apply (mbyte_of_aview pa_segs).
  apply (K84 1 pos x Hin2); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA; fold F;
                             change (fs_frame_bytes 1) with 128; change (Z.of_nat 8) with 8 in Hx; lz|].
  apply NE8. apply SIDEF. change (Z.of_nat 8) with 8 in Hx. lz. }
(* the state after talk: the frame's shadow, the realigned area and the saved words *)
jafter_call_keep_hi HS7 800%nat regs8 (mrestrict (w_H W8) mem8) Hpres8 [1; 2; 3]%nat HS8.
match type of HS8 with ?tq -> _ => assert (HRK : tq); [|specialize (HS8 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?U62_5 in Ha.
    + apply (mbyte_of_aview pa_segs).
      apply (K84 1 pos a Hin2); [right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite FA; fold F;
                                 change (fs_frame_bytes 1 / 8) with 16; unfold MR_SB, SHADOW_OFF in *; lz|].
      apply NE8. apply SIDES. unfold MR_SB in *. lz.
    + intros _. apply (apresent_writable pa_segs).
      replace a with (shadow_addr F + (a - (MR_SB + F / 8))) by (unfold shadow_addr, MR_SB, SHADOW_OFF; lz).
      apply HFSpres8. change (fs_frame_bytes 1 / 8) with 16. unfold MR_SB in *. lz.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?U60_5 in Ha.
    + apply (mbyte_of_aview pa_segs). apply K81; [lz | rewrite Usp7; unfold TALK_AK, TALK_AFRAME; lz |].
      intros Hq. rewrite EWR in Hq. destruct (WRF a Hq) as (_ & Xw & _). apply Xw. rewrite HK8. lz.
    + intros _. apply (apresent_writable pa_segs). apply Hpres8x. rewrite HK8 in Hwlo. lz.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite ?Usp_5 in Ha.
    + apply (mbyte_of_aview pa_segs). apply K81; [lz | rewrite Usp7; unfold TALK_AK, TALK_AFRAME; lz |].
      intros Hq. rewrite EWR in Hq. destruct (WRF a Hq) as (_ & Xw & _). apply Xw. rewrite HK8. lz.
    + intros _. apply (apresent_writable pa_segs). apply Hpres8x. rewrite HK8 in Hwlo. lz. }
clear HS7. rewrite <- restrict_mkst_fx in HS8.
remember (havoc E5 800 (map (getr regs8) CLOB)) as E8 eqn:HE8 in HS8.
assert (HEI8 : img_env pa_val A_LIM E8) by (rewrite HE8; apply img_env_havoc_hi; [exact HEI5 | cbv; lz]).
assert (OLD8 : forall n, (n < 800)%nat -> ew E8 n = ew E5 n)
  by (intros n Hn; rewrite HE8; apply YN3v.ew_havoc_old; exact Hn).
assert (HED8 : ed E8 = ed E5) by (rewrite HE8; reflexivity).
assert (E804 : ew E8 804 = getr regs8 10).
{ rewrite HE8. change 804%nat with (800 + 4)%nat.
  rewrite (ew_havoc_new E5 800 (map (getr regs8) CLOB) 4 (Z_to_bv 64 0) ltac:(cbn; lz)). reflexivity. }
clear HE8.
assert (U62_8 : bv_unsigned (ew E8 62) = MR_SB + F / 8) by (rewrite OLD8 by lz; exact U62_5).
assert (U60_8 : bv_unsigned (ew E8 60) = sp1) by (rewrite OLD8 by lz; exact U60_5).
assert (Usp_8 : bv_unsigned (ew E8 2) = spZ regs) by (rewrite OLD8 by lz; exact Usp_5).
rewrite P1. rewrite Z.add_0_r in HJ8.
(* ---- +0x1ec .. +0x204 (plain): the request's shadow bytes 4..7 := 0xf8 again, j +0x208 ---- *)
pose (RUNPT := paj_run_to_plain_x SK B LAWS G HGok XO OUT).
mr_run_plain_to RUNPT HS8 HJ8 (AF_model_read + 0x208).
{ cbn [ss_mem].
  repeat (apply awr_ok_x_cons;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fframe_region fshadow_region]; intros a Ha;
      rewrite ?U60_8, ?Usp_8, ?U62_8 in Ha;
      first
        [ left; split; [left; rewrite HK8 in Hwlo; lz | lz]
        | left; apply (aj_gx_awr_frame SK pa_segs B LAWS Hsegs G XO OUT STK sp0 FP ly S W0 mem0 md0
            ((1, pos) :: own) ly8 S8 W8 mem8 md8 k 1 pos a HJ8 ltac:(left; reflexivity));
          rewrite FA8'; right; unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16 in *;
          unfold MR_SB, SHADOW_OFF in *; lz ]
    |]);
  apply awr_ok_x_nil. }
lazymatch type of HS8 with st_ok_pi _ _ _ _ (restrict _ ?m) => set (ms9 := m) in * end.
set (X9 := fun a => MR_SB + F / 8 <= a < MR_SB + F / 8 + 16 \/ spZ regs - MODEL_READ_AK <= a < spZ regs).
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ X9 HFr
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                rewrite ?U60_8, ?Usp_8, ?U62_8 in Hrr; unfold X9; cbv beta;
                first [ left; clear - Hrr; unfold MR_SB in *; lz | right; rewrite HK8; lz ] |]);
        destruct Hin)) as UN9.
prreg HS8 (10%bv : bv 5) R10.
pmkst HS8.
mr_joinS HS8 1000%nat 0x208 CLOB208 mr_ss208d HSj.
(* the kept clause from the entry to the end *)
assert (FAall : forall c q, frame_addr ly2 c q = frame_addr lyc c q).
{ intros c q. destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ7) as (Fc7 & _).
  destruct (aj_gx_frame_addr SK pa_segs B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ) as (Fcc & _).
  congruence. }
assert (HK8c : akept pa_segs B lyc Sc W memc W8 mem8 (spZ regs - MODEL_READ_AK) (spZ regs)
          (fun a => inFP (model_read_awr regs (rdW W memc)) a \/ aside_rng lyc 1 pos a)).
{ eapply (akept_trans_ly SK pa_segs B LAWS Hsegs);
    [ exact Hsk | lz | exact HK7 | exact HK8t
    | rewrite Usp7; unfold TALK_AK, TALK_AFRAME; rewrite HES; rewrite HK8; lz | rewrite Usp7; lz
    | exact Hbl2 | rewrite Hfr2; intros f Hf; right; exact Hf | exact FAall
    | intros a [Hq | [Hq | Hq]]; [right; exact Hq | left; exact (KBW a Hq) | left; exact (ABW a Hq)]
    | intros a Ha; left; rewrite EWR in Ha; exact Ha ]. }
assert (HK9 : akept pa_segs B lyc Sc W memc W8 (ms_mem ms9) (spZ regs - MODEL_READ_AK) (spZ regs)
          (fun a => inFP (model_read_awr regs (rdW W memc)) a \/ aside_rng lyc 1 pos a)).
{ exact (akept_step SK pa_segs B LAWS Hsegs lyc Sc W memc mdc W8 mem8 W8 (ms_mem ms9)
    (spZ regs - MODEL_READ_AK) (spZ regs) _ _ X9 HAR Hsk ltac:(lz) HK8c UN9
    (fun a _ Hp => apresent_grows _ _ _ _ HG Hp) (fun a H => H)
    ltac:(intros a [Ha | Ha]; [left; right; apply SIDES; exact Ha | right; exact Ha])). }
(* bytes of the write set at the end are talk's *)
assert (V9 : forall a, inFP (model_read_awr regs (rdW W memc)) a ->
          aview pa_segs (w_H W8) (ms_mem ms9) a = aview pa_segs (w_H W8) mem8 a).
{ intros a Ha. destruct (WRF a Ha) as (_ & Xwin & X64 & XNS). apply UN9; [exact X64|].
  intros [Hq | Hq]; [exact (XNS (SIDES a Hq)) | exact (Xwin Hq)]. }
assert (WR9 : forall a, writable_at pa_segs (rdW W8 mem8) a -> writable_at pa_segs (rdW W8 (ms_mem ms9)) a)
  by (intros a Hw; exact (writable_kept (segs := pa_segs) (w_H W8) mem8 (ms_mem ms9) a
                            (fun Hp => apresent_grows _ _ _ _ HG Hp) Hw)).
(* talk's Post *)
destruct (HTP mbs0 kbs0 (req_read idx) ltac:(rewrite A70; exact HM7) HN7 ltac:(rewrite A71; exact HRQ7)
  ltac:(rewrite req_read_len, A72; reflexivity))
  as (RC & (mbs' & MA8 & MWF8 & NX8 & SO8 & SN8 & NM8 & MK8 & RQ8 & NR8) & KT & AT & KN & AN & KB8 & AB8).
rewrite A73, A74 in KT, KN, KB8. rewrite A75, A76 in AT, AN, AB8. rewrite A70 in MA8.
set (K0 := md_kstate mbs0 kbs0) in *.
(* a buffer's bytes, from the call to the end *)
assert (BUF9 : forall p n, (forall x, p <= x < p + n -> inFP (model_read_awr regs (rdW W memc)) x) ->
          forall x, p <= x < p + n -> mbyte pa_segs (rdW W8 (ms_mem ms9)) x = mbyte pa_segs (rdW W8 mem8) x)
  by (intros p n Hw x Hx; apply (mbyte_of_aview pa_segs); exact (V9 x (Hw x Hx))).
assert (KBX : aarg regs 2 <> 0 -> forall x, aarg regs 2 <= x < aarg regs 2 + aarg regs 3 ->
          inFP (model_read_awr regs (rdW W memc)) x)
  by (intros h2 x Hx; replace x with (aarg regs 2 + (x - aarg regs 2)) by lz; apply KIV; [lz | exact h2]).
assert (ABX : aarg regs 4 <> 0 -> forall x, aarg regs 4 <= x < aarg regs 4 + aarg regs 5 ->
          inFP (model_read_awr regs (rdW W memc)) x)
  by (intros h4 x Hx; replace x with (aarg regs 4 + (x - aarg regs 4)) by lz; apply AIV; [lz | exact h4]).
(* the kind / alias answer at the end *)
assert (TXT9 : forall (p n : Z) (o : option (list byte)) (Hw : p <> 0 -> forall x, p <= x < p + n -> inFP (model_read_awr regs (rdW W memc)) x),
          p <> 0 -> 1 <= n ->
          (forall pay, o = Some pay -> acstr_at pa_segs (rdW W8 mem8) p (cut_text pay n)) ->
          (o = None -> acstr_at pa_segs (rdW W8 mem8) p []) ->
          acstr_at pa_segs (rdW W8 (ms_mem ms9)) p (text_of_attr o n)).
{ intros p n o Hw Hp Hn HS' HN'. unfold text_of_attr. destruct o as [pay|].
  - apply (mr_acstr_move pa_segs (rdW W8 mem8) _ p _ (HS' pay eq_refl)). intros x Hx.
    pose proof (cut_text_len pay n Hn). apply (BUF9 p n (Hw Hp)). lz.
  - apply (mr_cstr_nil_move pa_segs (rdW W8 mem8) _ p (HN' eq_refl)). apply (BUF9 p n (Hw Hp)). lz. }
assert (NUL8 : forall p n, p <> 0 -> 1 <= n -> acstr_at pa_segs (rdW W2 m7) p [] -> abuf pa_segs (rdW W2 m7) p n ->
          (forall kb, abytes pa_segs (rdW W2 m7) p kb -> Z.of_nat (length kb) = n -> abytes pa_segs (rdW W8 mem8) p kb) ->
          acstr_at pa_segs (rdW W8 mem8) p []).
{ intros p n Hp Hn Hc (junk & Hl & (Hjb & _)) Hkeep.
  apply (mr_cstr_nil_of_abytes pa_segs _ p junk (Hkeep junk Hjb Hl)).
  destruct Hjb as (_ & _ & Hjb). destruct Hc as ((_ & _ & Hcb) & _).
  rewrite <- (Hjb 0%nat ltac:(lz)). exact (Hcb 0%nat ltac:(cbn; lz)). }
(* ---- the exit ---- *)
refine (mr_exit_d SK B LAWS rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ ly8 S8 W8 k pos
  (talk_rc_model K0) HENT _ _ _ _ _ _ _ HSj _ HJ8 ltac:(lz) _ _
  (ex_intro _ S1 (ex_intro _ W1 (ex_intro _ mem1 (ex_intro _ md1 (conj HAR1 (conj Hfrs1 Eab1)))))) Hnin HK9 _ _ _ _).
- apply img_env_havoc_hi; [exact HEI8 | cbv; lz].
- split; [intros n Hn; rewrite YN3v.ew_havoc_old by lz; rewrite OLD8, OLD5 by lz; exact (proj1 HAE n Hn)
         | transitivity (ed E8); [reflexivity | rewrite HED8, HED5; exact (proj2 HAE)]].
- rewrite YN3v.ew_havoc_old by lz; rewrite OLD8, OLD5 by lz; exact E32.
- rewrite YN3v.ew_havoc_old by lz; rewrite OLD8, OLD5 by lz; exact E44.
- rewrite YN3v.ew_havoc_old by lz; rewrite OLD8, OLD5 by lz; rewrite <- Esp1; exact E60.
- rewrite YN3v.ew_havoc_old by lz; rewrite OLD8, OLD5 by lz; exact E61.
- rewrite YN3v.ew_havoc_old by lz; rewrite OLD8, OLD5 by lz; exact E62.
- apply (mr_val_mem_move pa_segs (rdW W8 mem8) _ _ 8 FL VFL8). intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  apply (mbyte_of_aview pa_segs). apply UN9; [lz|]. intros [Hq | Hq]; [clear - Hq Hx HdFS; unfold MR_SB in *; lz | lz].
- exists (st_fs S8). apply (set_fs_trans S2 S8 Sc); [exact (set_fs_of_exists S2 Sc Hfs2) | exact HS8f].
- exact (perm_trans Hperm8 Hperm2).
- transitivity (m_fds md8); [exact (proj1 (wvb_fds_fs _ _ md8))|]. rewrite Hfd8.
  unfold md7. transitivity (m_fds md5); [exact (proj1 (wvb_fds_fs _ _ md5))|].
  rewrite (proj1 (same_but_materialized_fs _ _ Hsm5)).
  transitivity (m_fds md2); [exact (proj1 (wvb_fds_fs _ _ md2)) | exact Hfd].
- transitivity (m_fs md8); [exact (proj2 (wvb_fds_fs _ _ md8))|]. rewrite Hfs8.
  unfold md7. transitivity (m_fs md5); [exact (proj2 (wvb_fds_fs _ _ md5))|].
  rewrite (proj2 (same_but_materialized_fs _ _ Hsm5)).
  transitivity (m_fs md2); [exact (proj2 (wvb_fds_fs _ _ md2)) | exact Hfsy].
- cbn [ms_regs mkst]. rewrite R10, E804. exact RC.
- intros regs' R10' mbs kbs tab nm Hm Hk Ht Hn. cbv zeta.
  rewrite <- (mr_amodel_unique pa_segs _ _ mbs0 mbs PMOD Hm).
  rewrite <- (mr_anlk_unique pa_segs _ _ kbs0 kbs PNLK Hk) in Ht |- *.
  rewrite <- (mr_aiftab_unique pa_segs _ _ kbs0 tab0 tab PTAB Ht).
  rewrite <- (mr_astr_arg_unique pa_segs _ _ (Some s0) nm HNM Hn).
  fold K0.
  unfold read_model, read_core. rewrite (proj2 (Nat.eqb_neq _ _) Hs0).
  rewrite (HIX kbs0 tab0 PNLK PTAB). rewrite (proj2 (Z.eqb_neq idx 0) ltac:(lz)).
  cbv zeta. cbn [r_rc r_kind r_alias r_reqs r_state].
  split; [exact R10'|].
  split.
  { exists mbs'. split.
    { apply (mr_amodel_move pa_segs (rdW W8 mem8) _ _ mbs' MA8).
      - apply (BUF9 (aarg regs 0) MD_SIZE). intros x Hx. replace x with (aarg regs 0 + (x - aarg regs 0)) by lz.
        apply BLK. lz.
      - intros x Hx. apply WR9. destruct MA8 as ((_ & Hw) & Hl). replace x with (aarg regs 0 + (x - aarg regs 0)) by lz.
        apply Hw. rewrite Hl. lz. }
    split; [exact MWF8|]. split; [exact NX8|]. split; [rewrite mr_talk_after_sock; exact SO8|].
    split; [exact SN8|]. split; [exact RQ8|]. split; [rewrite NR8, RQ8; reflexivity|]. split; [exact NM8 | exact MK8]. }
  split.
  { intros h2 h3. rewrite (proj2 (Z.ltb_ge (aarg regs 3) 1) h3).
    destruct (KZ7 h2 h3) as (Kc7 & Kb7).
    apply (TXT9 (aarg regs 2) (aarg regs 3) _ KBX h2 h3).
    - intros pay Hpay. exact (KT pay Hpay h2 h3).
    - intros Hnone. exact (NUL8 (aarg regs 2) (aarg regs 3) h2 h3 Kc7 Kb7 (KN Hnone h2 h3)). }
  split.
  { intros h4 h5. rewrite (proj2 (Z.ltb_ge (aarg regs 5) 1) h5).
    destruct (AZ7 h4 h5) as (Ac7 & Ab7).
    apply (TXT9 (aarg regs 4) (aarg regs 5) _ ABX h4 h5).
    - intros pay Hpay. exact (AT pay Hpay h4 h5).
    - intros Hnone. exact (NUL8 (aarg regs 4) (aarg regs 5) h4 h5 Ac7 Ab7 (AN Hnone h4 h5)). }
  split.
  { intros h2 h3. apply (mr_abuf_move pa_segs (rdW W8 mem8) _ _ _ (KB8 h2 h3)); [exact (BUF9 _ _ (KBX h2))|].
    intros x Hx. apply WR9. destruct (KB8 h2 h3) as (junk & Hl & (_ & Hw)).
    replace x with (aarg regs 2 + (x - aarg regs 2)) by lz. apply Hw. lz. }
  { intros h4 h5. apply (mr_abuf_move pa_segs (rdW W8 mem8) _ _ _ (AB8 h4 h5)); [exact (BUF9 _ _ (ABX h4))|].
    intros x Hx. apply WR9. destruct (AB8 h4 h5) as (junk & Hl & (_ & Hw)).
    replace x with (aarg regs 4 + (x - aarg regs 4)) by lz. apply Hw. lz. }
Qed.


End b.
End a.
