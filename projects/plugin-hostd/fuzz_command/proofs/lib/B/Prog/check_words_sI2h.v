(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module paths and module names changed; 430 of its 506 lines of code are new or changed and 1584 lines of the source are left out. *)
(* check_words' ASan+UBSan walk (plugin-hostd/fuzz_command.asan-ubsan), segment I2, the stretch after the second atoi
   of a '#' item (0x87ea0, listing 0x1970) to ICMP (0x87ee4, listing 0x19b4). The B twin of lib/A/Prog/check_words_sI2h.v
   (an earlier version).
     0x87ea0 .. 0x87eb4  a3 := the number atoi read; a2 := "%d" (0x218e0, the auipc/addi pair 0x87ea4 / 0x87ea8, the
                         image object A_OBJ 25); a1 := 16; s5 := a0 := number = F + 32 (the scratch slot sp1 + 88,
                         0x87eb0), all from the seed i2h_ss of this file;
     0x87eb8             jal snprintf (the wrapper's trampoline, ra = BASE + 0x198c): the "%d" text of the number into
                         number[16] of the own class-0 frame F, the shared contract asnprintf_sh (RtPFCmd.v) composed by
                         PaFx.v's aj_art_own_atF with the write set [F + 32, F + 32 + |text| + 1) and srr_art_postF_of_pf;
     0x87ebc             `j 87ee4`, at the FP state fx1 the call returned (i2h_J_run, in a section of its own so that it
                         holds at every FP state);
     0x87ee4             ICMP, with s5 = number, which holds want_at's text of the item; the ICMP statement at fx1 lifts
                         back to the entry's FP state by srr_after_artF.
   i2h_H_run is the run to the call, i2h_call_snpF the call, i2_at_H the frozen statement i2_H_spec of sI2a. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0t YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d check_words_ki.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_sI2a PaArtOwn PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFShared RtPFCmd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* closed facts *)
(* a callee-saved register is kept by aregs_preserved *)
Lemma i2h_pres_r : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
Ltac i2h_cs_tac := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.
(* the bytes of a list of byte values, read back *)
Lemma i2h_nth_bytes : forall (l : list Z) j, Forall (fun c => 0 <= c < 256) l ->
  bv_unsigned (nth j (map (Z_to_bv 8) l) (Z_to_bv 8 0)) = nth j l 0.
Proof.
intros l j H. rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
destruct (Nat.lt_ge_cases j (length l)) as [Hj|Hj].
- apply Z.mod_small. rewrite Forall_forall in H. apply H. apply nth_In. exact Hj.
- rewrite nth_overflow by exact Hj. reflexivity.
Qed.
(* the ranges the snprintf chain reads as constants lie in the image *)
Lemma i2h_crb : forall r, In r CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) cmd_snp_cr_img r Hr) as Hb.
unfold in_cmd_img, CMD_IMG_LO, CMD_IMG_HI in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
(* "%d" at 0x218e0 as the shared contract's format (fmt_at), apart from the window and the destination *)
Lemma i2h_fmt_at : forall (rd : reader) sp K d w, astr_atR rd 0x218e0 (pf_bytes [37; 100]) ->
  range_addressable rd SHADOW_OFF 0x218e0 3 -> shadow_hull_vis rd 0x218e0 3 ->
  0x218e3 <= sp - K -> 0 <= K -> (d + w <= 0x10000 \/ 0x606000 <= d) ->
  fmt_at rd (snp_out K sp d w) 0x218e0 [37; 100].
Proof.
intros rd sp K d w [Hb _] RA HV Hsp HK Hd. unfold fmt_at.
change (Z.of_nat (length [37; 100]) + 1) with 3.
split; [lia|]. split.
{ intros i Hi. change (Z.of_nat (length [37; 100])) with 2 in Hi.
  assert (Hi' : (Z.to_nat i < 3)%nat) by lia.
  pose proof (Hb (Z.to_nat i) ltac:(change (length (pf_bytes [37; 100] ++ [Z_to_bv 8 0])) with 3%nat; exact Hi')) as H.
  rewrite Z2Nat.id in H by lia. rewrite H. f_equal.
  assert (Hc : (Z.to_nat i = 0 \/ Z.to_nat i = 1 \/ Z.to_nat i = 2)%nat) by lia.
  destruct Hc as [E|[E|E]]; rewrite E; vm_compute; reflexivity. }
split.
{ unfold snp_out. constructor; [unfold zdisjoint; cbn [fst snd]; lia|].
  constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor]. }
split; [unfold amem_range, kLowMemEnd; left; lia|]. split; [exact RA | exact HV].
Qed.

(* the seed at 0x87ea0 (listing 0x1970): atom 9 = sp1 with the scratch slot sp1 + 88 holding atom 32 = number = F + 32
   (stored at 0x87c64), atom 22 = the shadow base; no window, so the token executor runs it (no writable region) *)
Definition i2h_regions : smem :=
[ YP09.mkRegion (Some 9%nat) 88 96 0 0 [YP09.mkChunk 88 (CVal 8 (SOff 32 0))] ].
Definition i2h_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (22%nat, mkAF CW_SB CW_SB 0); (32%nat, mkAF 4096 PCEIL 0) ] [] [].
Definition i2h_ss : sstate := mkSS 0x1970 sr_atoms i2h_regions None i2h_facts.
(* the seed at 0x87ebc (listing 0x198c), after snprintf: no region *)
Definition i2h_ssJ : sstate := mkSS 0x198c sr_atoms [] None (mkFacts [ (22%nat, mkAF CW_SB CW_SB 0) ] [] []).

(* ---------------------------------------------------------------------------------------------------------- *)
(* 0x87ebc: `j 87ee4`, then ICMP. Its own section: after the section closes it holds at every FP state, and i2_at_H
   applies it at the FP state fx1 snprintf returned. *)
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
Hypothesis LAWS : AR_laws SEGS B.
Let RUNTO := paj_run_to B LAWS.

Lemma i2h_seedJ : forall (W : world SEGS) (regsc : bvmap 5 word) memc,
  getr regsc 22 = w64 CW_SB ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [])) i2h_ssJ
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x198c)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc H22.
assert (E22 : ew (Eimg (Ereg regsc [])) 22 = Z_to_bv 64 CW_SB) by (rewrite (i2_EE regsc _ 22%nat 22%bv eq_refl); exact H22).
unfold i2h_ssJ. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E22, unsigned_lit_small by (unfold CW_SB; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold CW_SB. repeat split; lia.
Qed.

Lemma i2h_J_run : forall e lyc Sc Wc regs mem md pos Q,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc mem md EV_JOINED ->
  getr regs 22 = w64 CW_SB ->
  (forall regsT memT mdT,
     ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
       lyc Sc Wc memT mdT EV_JOINED ->
     i2_rk regs regsT -> getr regsT 21 = getr regs 21 ->
     (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memT x = rdW Wc mem x) ->
     SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (BASE + CW_PC_ICMP)) memT (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x198c)) mem (seg_rom SEGS)) md) Q.
Proof.
intros e lyc Sc Wc regs mem md pos Q HJ H22 HK.
pose proof (i2h_seedJ Wc regs mem H22) as HS.
assert (SHOK : sh_ok SEGS IBx [] (Eimg (Ereg regs [])) (mrestrict (w_H Wc) mem)) by apply Forall_nil.
pose proof (Eimg_env (Ereg regs [])) as HEI.
pose proof (i2_HAE regs []) as HAE.
pose proof (i2_EE regs []) as EE.
remember (Eimg (Ereg regs [])) as E eqn:HE in *. clear HE.
paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_ICMP; [awr_ok_tac |].
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ mem) (mrestrict _ ?m2) |- _ =>
  pose proof (i2_kept_ro _ rs _ mem m2 HFr ltac:(vm_compute; reflexivity)) as KEEP end.
prreg HS (21%bv : bv 5) R21.
pose proof (i2_rk_pi _ _ _ regs [] HS HAE ltac:(vm_compute; reflexivity)) as RK.
cbn [ms_regs restrict] in RK.
pmkst HS.
apply (HK (ms_regs ms) (ms_mem ms) mdv HJ RK).
- rewrite R21. exact (EE 21%nat 21%bv eq_refl).
- exact KEEP.
Qed.

End e.
End f.
End d.

(* ---------------------------------------------------------------------------------------------------------- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:124-141) this file uses, word for word *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis RRO : RRO_P.
(* the record facts of check_words_d.v (check_words_rf.v proves them from lib/B/Prog/CmdRecFacts.v) *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
(* the record and the image facts (walk hypotheses HB and IMG, cgif's names), for CmdRecImg's cmd_consts_view_snp *)
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.

#[local] Notation CWJ e pos lyc Sc Wc memc mdc :=
  (ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
     lyc Sc Wc memc mdc EV_JOINED).

(* where sp1 and the own frame lie *)
Lemma i2h_jloc : forall e lyc Sc Wc memc mdc pos k sp1,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  cw_sp0 e - 336 <= sp1 <= cw_sp0 e - 320 ->
  alloc_ceiling + 4 * ESTACK <= sp1 /\ cw_sp0 e <= 2 ^ 47 /\ cw_sp0 e mod 16 = 0 /\
  4096 <= frame_addr (e_ly e) 0 pos /\ frame_addr (e_ly e) 0 pos + 64 <= alloc_ceiling.
Proof.
intros e lyc Sc Wc memc mdc pos k sp1 HJ Hsp.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 0 pos HAR Hin) as (F1 & F2 & _).
assert (FB : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold frame_addr in F1, F2 |- *. rewrite EF in F1, F2. rewrite FB in F2.
repeat split; lia.
Qed.

(* number[16] of the own frame, [F + 32, F + 48), is a range the snprintf entry may write: a byte of the own frame,
   which the journal admits (awr_byte_present, the own-frame disjunct of awr_byte), its shadow 0 (cw_core's two
   shadow bytes, check_words_d.v:252) *)
Lemma i2h_num_wr : forall e lyc Sc Wc memc mdc pos k (regsT : bvmap 5 word),
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc memc mdc k ->
  rdW Wc memc (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 4) = Some 0 ->
  rdW Wc memc (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 5) = Some 0 ->
  alloc_ceiling <= spZ regsT - 3 * ESTACK ->
  awrite_ok SEGS B (3 * ESTACK) lyc Sc Wc regsT memc (frame_addr (e_ly e) 0 pos + 32) 16.
Proof.
intros e lyc Sc Wc memc mdc pos k regsT HJ S4 S5 HspT.
pose proof HJ as (HAR & Hlyl & _ & _ & _ & Hfrs & _).
pose proof Hlyl as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (FEQ : frame_addr lyc 0 pos = frame_addr (e_ly e) 0 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (FB : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 0 pos HAR Hin) as (F1 & F2 & Fapp).
destruct (frame_al64 SEGS B lyc Sc Wc memc mdc 0 pos HAR Hin) as (F64 & _).
pose proof (fun d n H1 H2 H3 => shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc memc mdc 0 pos d n HAR Hin H1 H2 H3) as FHV.
assert (WRB : forall x, frame_addr lyc 0 pos <= x < frame_addr lyc 0 pos + fs_frame_bytes 0 ->
  writable_at SEGS (mrestrict (w_H Wc) memc) x /\ ~ aowned B lyc Sc x).
{ intros x Hx. apply (awr_byte_present SEGS B LAWS CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(0, pos)] lyc Sc Wc memc mdc k x HJ).
  - right; right; right; left. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. exact Hx.
  - intros (r & Hr & _). destruct Hr. }
rewrite FEQ in F1, F2, Fapp, F64, FHV, WRB. rewrite FB in F2, Fapp, FHV, WRB.
set (F := frame_addr (e_ly e) 0 pos) in *. clearbody F.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; pose proof (Z.div_mod F 8 ltac:(lia)) as D8;
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HD4 : (F + 32) / 8 = F / 8 + 4) by (rewrite HF8; replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia;
  rewrite Z.div_mul by lia; replace (8 * (F / 8)) with ((F / 8) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
unfold awrite_ok. split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros x Hx. destruct (WRB x ltac:(lia)) as [Hw Ho]. split; [exact Hw|]. split; [exact Ho|]. unfold ascratch_stk. lia. }
split.
{ unfold in_app, kLowShadowBeg, ASAN_CEIL in Fapp. unfold amem_range.
  destruct Fapp as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; lia. }
split.
{ apply zero_shadow_range; [rewrite HF8; replace (8 * (F / 8) + 32) with ((F / 8 + 4) * 8) by lia; apply Z_mod_mult
                           | reflexivity |].
  intros i Hi. change (16 / 8) with 2 in Hi. unfold shadow_of_addr. rewrite HD4.
  assert (Hi2 : i = 0 \/ i = 1) by lia.
  destruct Hi2 as [-> | ->].
  - replace (SHADOW_OFF + (F / 8 + 4) + 0) with (CW_SB + F / 8 + 4) by (unfold CW_SB, SHADOW_OFF; lia). exact S4.
  - replace (SHADOW_OFF + (F / 8 + 4) + 1) with (CW_SB + F / 8 + 5) by (unfold CW_SB, SHADOW_OFF; lia). exact S5. }
intros _. apply FHV; lia.
Qed.

Lemma i2h_seedH : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 d,
  getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 22 = w64 CW_SB ->
  4096 <= d <= PCEIL ->
  aval_mem (rdW W memc) (sp1 + 88) 8 d ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [Z_to_bv 64 d])) i2h_ss
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x1970)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc sp1 d H9 Hsp Hsp32 H22 Hd V88.
set (E := Eimg (Ereg regsc [Z_to_bv 64 d])).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (subst E; rewrite (i2_EE regsc _ 9%nat 9%bv eq_refl); exact H9).
assert (E22 : ew E 22 = Z_to_bv 64 CW_SB) by (subst E; rewrite (i2_EE regsc _ 22%nat 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 d) by (subst E; exact (i2_EX regsc _ 0 ltac:(unfold A_TEXT; lia))).
unfold i2h_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold i2h_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ sp1 88 8 (SOff 32 0) d);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold PCEIL in *; lia | lia |].
  exact (i2_val_of_aval _ _ _ _ _ V88).
- apply pairwise_disjoint_of_extents. cbn [i2h_regions map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok i2h_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E22, E32, !unsigned_lit_small by (unfold CW_SB, PCEIL in *; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  change (2 ^ 5) with 32. unfold CW_SB. repeat split; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 0x87ea0 .. the call: the seed i2h_ss and one run, which stops at the snprintf call (0x87eb8) *)
Lemma i2h_H_run : forall e lyc Sc Wc regs mem md pos sp1 Q,
  VAL (A_OBJ 25) = 0x218e0 ->
  CWJ e pos lyc Sc Wc mem md ->
  spZ regs = sp1 -> cw_sp0 e - 336 <= sp1 <= cw_sp0 e - 320 -> sp1 mod 32 = 0 ->
  getr regs 9 = w64 sp1 -> getr regs 22 = w64 CW_SB ->
  aval_mem (rdW Wc mem) (sp1 + 88) 8 (frame_addr (e_ly e) 0 pos + 32) ->
  (forall regsT memT mdT, CWJ e pos lyc Sc Wc memT mdT ->
     i2_rk regs regsT ->
     (forall x, 0 <= x < 2 ^ 64 -> rdW Wc memT x = rdW Wc mem x) ->
     getr regsT 1 = Z_to_bv 64 (BASE + 6540) ->
     getr regsT 10 = w64 (frame_addr (e_ly e) 0 pos + 32) -> getr regsT 11 = w64 16 ->
     getr regsT 12 = w64 0x218e0 -> getr regsT 13 = getr regs 10 ->
     getr regsT 21 = w64 (frame_addr (e_ly e) 0 pos + 32) ->
     SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x1970)) mem (seg_rom SEGS)) md) Q.
Proof.
intros e lyc Sc Wc regs mem md pos sp1 Q V25 HJ Hsp Hrng Hsp32 H9 H22 L88 HK.
destruct (i2h_jloc e lyc Sc Wc mem md pos EV_JOINED sp1 HJ Hrng) as (HLO & H47 & H16 & HF1 & HF2).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
assert (Hes : ESTACK = 4096) by reflexivity.
set (F := frame_addr (e_ly e) 0 pos) in *.
pose proof (i2h_seedH Wc regs mem sp1 (F + 32) H9 ltac:(lia) Hsp32 H22 ltac:(unfold PCEIL; lia) L88) as HS.
assert (SHOK : sh_ok SEGS IBx [] (Eimg (Ereg regs [Z_to_bv 64 (F + 32)])) (mrestrict (w_H Wc) mem)) by apply Forall_nil.
pose proof (Eimg_env (Ereg regs [Z_to_bv 64 (F + 32)])) as HEI.
pose proof (i2_HAE regs [Z_to_bv 64 (F + 32)]) as HAE.
pose proof (i2_EE regs [Z_to_bv 64 (F + 32)]) as EE.
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 (F + 32)])) 32 = Z_to_bv 64 (F + 32))
  by exact (i2_EX regs _ 0 ltac:(unfold A_TEXT; lia)).
(* "%d": the auipc/addi pair 0x87ea4 / 0x87ea8 is the listing's PAddHi of the image object A_OBJ 25 = atom 266 *)
assert (E266 : ew (Eimg (Ereg regs [Z_to_bv 64 (F + 32)])) 266 = Z_to_bv 64 0x218e0).
{ rewrite (Eimg_img _ 266%nat ltac:(unfold A_TEXT, A_LIM; lia)). change 266%nat with (A_OBJ 25). rewrite V25. reflexivity. }
remember (Eimg (Ereg regs [Z_to_bv 64 (F + 32)])) as E eqn:HE in *. clear HE.
paj_run_tok RUN HS HJ SHOK IBspan; [awr_ok_tac |].
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ mem) (mrestrict _ ?m2) |- _ =>
  pose proof (i2_kept_ro _ rs _ mem m2 HFr ltac:(vm_compute; reflexivity)) as KEEP end.
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (12%bv : bv 5) R12. prreg HS (13%bv : bv 5) R13. prreg HS (21%bv : bv 5) R21.
pose proof (i2_rk_st _ _ _ regs [Z_to_bv 64 (F + 32)] HS HAE ltac:(cbn [setpc ss_regs]; vm_compute; reflexivity)) as RK.
cbn [ms_regs restrict] in RK.
pmkst HS.
apply (HK (ms_regs ms) (ms_mem ms) mdv HJ RK KEEP).
- exact R1.
- rewrite R10, E32. reflexivity.
- exact R11.
- rewrite R12, E266. reflexivity.
- rewrite R13. exact (EE 10%nat 10%bv eq_refl).
- rewrite R21, E32. reflexivity.
Qed.

(* the call snprintf(number, 16, "%d", v) at 0x87eb8 (pc = the entry, ra = BASE + 0x198c): the shared contract at
   the ambient FP state fx, the walk continuing at the FP state fx1 it returns, any apost_baseF post lifted back *)
Lemma i2h_call_snpF : forall e lyc Sc Wc regsT memT mdT pos sp1 v STK0 FP0 regs0 ly0 S0 W0 mem0 md0 k0 Q0,
  cw_ent B MT e -> CWJ e pos lyc Sc Wc memT mdT ->
  spZ regsT = sp1 -> cw_sp0 e - 336 <= sp1 <= cw_sp0 e - 320 -> sp1 mod 32 = 0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = Z_to_bv 64 (BASE + 6540) ->
  getr regsT 10 = w64 (frame_addr (e_ly e) 0 pos + 32) -> getr regsT 11 = w64 16 -> getr regsT 12 = w64 0x218e0 ->
  getr regsT 13 = w64 v -> -2^31 <= v < 2^31 ->
  rdW Wc memT (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 4) = Some 0 ->
  rdW Wc memT (CW_SB + frame_addr (e_ly e) 0 pos / 8 + 5) = Some 0 ->
  (forall (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 ->
     CWJ e pos lyc Sc Wc mem2 md2 ->
     aregs_preserved regsT regs2 ->
     astr_atR (rdW Wc mem2) (frame_addr (e_ly e) 0 pos + 32) (pf_bytes (pf_dec v)) ->
     cw_mem_kept B (rdW Wc memT) (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) ->
     SRr SEGS Wc (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + 6540)) mem2 (seg_rom SEGS)) md2)
       (apost_baseF (fx := fx1) SEGS B STK0 FP0 regs0 ly0 S0 W0 mem0 md0 k0 Q0)) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT)
    (apost_baseF (fx := fx) SEGS B STK0 FP0 regs0 ly0 S0 W0 mem0 md0 k0 Q0).
Proof.
intros e lyc Sc Wc regsT memT mdT pos sp1 v STK0 FP0 regs0 ly0 S0 W0 mem0 md0 k0 Q0
  HE HJ Hsp Hrng Hsp32 Hgp Htp Hra Ha0 Ha1 Ha2 Ha3 Hv S4 S5 HK.
pose proof HE as (_ & Hfrm & _).
destruct (i2h_jloc e lyc Sc Wc memT mdT pos EV_JOINED sp1 HJ Hrng) as (HLO & H47 & H16 & HF1 & HF2).
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HK2 : CMD_SNP_K = 2 * ESTACK) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (i2_arodata_now B MT RRO e pos lyc Sc Wc memT mdT EV_JOINED HE HJ) as HROD.
destruct (cmd_rec_cells lyc Sc Wc memT mdT (proj1 HJ)) as (_ & (Hg1 & cval & Hg2) & _).
destruct (i2_fmt_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc memT mdT pos EV_JOINED HE HJ)
  as (FS & FRA & FHV & FT).
pose proof (i2h_num_wr e lyc Sc Wc memT mdT pos EV_JOINED regsT HJ S4 S5 ltac:(rewrite Hsp; lia)) as WR.
pose proof (i2_pf_dec_len v Hv) as HL.
pose proof HJ as (HAR & Hlyl & _ & _ & _ & Hfrs & _).
pose proof Hlyl as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof (frm_off_imgP B lyc Sc Wc memT mdT 0 pos HAR Hin) as HOFF.
destruct (ecall_pre_stk_at SEGS B CMD_SNP_K CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e)
  (e_md e) [(0, pos)] lyc Sc Wc memT mdT EV_JOINED regsT (sp1 - cw_sp0 e) HJ ltac:(rewrite Hsp; lia)
  ltac:(apply i2_o16; [exact Hsp32 | exact H16]) ltac:(lia) ltac:(rewrite HK2; lia) ltac:(rewrite HK2, Hes, WS; lia)
  ltac:(rewrite Hra; apply ret_ok_codeptr_v; [lia | reflexivity]) Hgp Htp) as (HPRE & HSTK & HSCR).
set (F := frame_addr (e_ly e) 0 pos) in *.
assert (FEQ : frame_addr lyc 0 pos = F) by (unfold F, frame_addr; rewrite EF; reflexivity).
rewrite FEQ in HOFF. change (fs_frame_bytes 0) with 64 in HOFF. unfold off_img in HOFF.
assert (Hw : sn_len (16 - 1) (pf_dec v) = Z.of_nat (length (pf_dec v)) + 1)
  by (unfold sn_len, sn_bytes; rewrite length_app, firstn_all2 by lia; cbn [length]; lia).
assert (Hbs : sn_bytes (16 - 1) (pf_dec v) = pf_dec v ++ [0]) by (unfold sn_bytes; rewrite firstn_all2 by lia; reflexivity).
destruct WR as (_ & _ & _ & WB & WAM & WRA & WHV).
eapply (srr_after_artF (fx := fx) SEGS Wc _ (Z_to_bv 64 (BASE + 6540))).
{ apply (aj_art_own_atF (fx := fx) SEGS B LAWS pa_segs_low CMD_SNP_K
    (fun a => F + 32 <= a < F + 32 + sn_len (16 - 1) (pf_dec v))
    (SIG CS___interceptor_trampoline_snprintf) Wc regsT memT CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e)
    (e_mem e) (e_md e) [(0, pos)] lyc Sc mdT EV_JOINED (sp1 - cw_sp0 e) (Z_to_bv 64 (BASE + 6540))
    (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length (pf_dec v))) /\
       forall i, 0 <= i < sn_len (16 - 1) (pf_dec v) ->
       aview SEGS (w_H Wc) mem' (F + 32 + i) = Some (nth (Z.to_nat i) (sn_bytes (16 - 1) (pf_dec v)) 0))
    HJ ltac:(rewrite Hsp; lia) ltac:(apply i2_o16; [exact Hsp32 | exact H16]) ltac:(lia) ltac:(rewrite HK2; lia)
    ltac:(rewrite HK2, Hes, WS; lia) Hra).
  - intros x Hx. cbv beta in Hx. rewrite Hw in Hx.
    right; right; right; left. exists 0, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite FEQ. change (fs_frame_bytes 0) with 64. lia.
  - apply (srr_art_postF_of_pf (fx := fx) SEGS B CMD_SNP_K lyc Sc Wc regsT memT mdT _ (F + 32)
      (sn_len (16 - 1) (pf_dec v)) (sn_bytes (16 - 1) (pf_dec v)) (Z.of_nat (length (pf_dec v))) HSCR).
    apply (ASNPRINTF fx lyc Sc Wc regsT memT mdT (F + 32) 16 0x218e0 [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ [])
      (pf_dec v) cval).
    + exact HPRE.
    + exact HSTK.
    + exact HSCR.
    + exact Ha0.
    + exact Ha1.
    + exact Ha2.
    + exact (cmd_consts_view_snp SEGS B LAWS HB IMG _ _ Wc memT HROD).
    + apply Forall_forall. intros r Hr. pose proof (i2h_crb r Hr). lia.
    + apply Forall_forall. intros r Hr. pose proof (i2h_crb r Hr). unfold snp_out. rewrite Hsp, HK2, Hw.
      constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor]].
    + exact Hg1.
    + exact Hg2.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold snp_out. rewrite Hsp, HK2, Hw.
      constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor]].
    + unfold snp_out. rewrite Hsp, HK2, Hw.
      constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor]].
    + split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
    + cbn [length]. rewrite Hsp. lia.
    + cbn [length]. unfold snp_out. rewrite Hsp, HK2, Hw.
      constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor]].
    + apply (FR_cmd_intro _ _ _ _ _ [37; 100] [Pd] [AInt v]).
      * rewrite Hsp, HK2, Hw. apply i2h_fmt_at; [exact FS | exact FRA | exact FHV | lia | lia | lia].
      * reflexivity.
      * cbn [map app arg_of pf_args_asan pf_arg_asan]. split; [|exact I]. split; [exact Hv|].
        unfold argZ.
        match goal with |- context [getr regsT (Z_to_bv 5 ?x)] =>
          replace (Z_to_bv 5 x) with (13%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity) end.
        rewrite Ha3.
        unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        pose proof (Z.div_mod v (2 ^ 64) ltac:(lia)) as D.
        replace (v mod 2 ^ 64) with (v + (- (v / 2 ^ 64) * 2 ^ 32) * 2 ^ 32) by lia.
        rewrite Z.mod_add by lia. reflexivity.
      * cbn [pf_text option_map]. rewrite app_nil_r. reflexivity.
      * exact I.
      * (* FR_cmd_intro's check of the format "%d" at 0x218e0 and its one int argument *)
        vm_compute; reflexivity.
    + lia.
    + lia.
    + lia.
    + rewrite Hw. lia.
    + unfold snp_out. rewrite Hsp, HK2, Hw. cbn [pairwise].
      split; [constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor] | split; [constructor | exact I]].
    + intros x Hx. rewrite Hw in Hx. destruct (WB x ltac:(lia)) as (Hw1 & Ho & Hs).
      split; [exact Hw1|]. split; [exact Ho|]. unfold ascratch_stk in Hs. lia.
    + (* the `+ 8` band premise: [F + 32, F + 32 + |text| + 1 + 8) ends at most at F + 56,
         inside the 64-byte class-0 frame, which frames_bounds puts in application memory *)
      rewrite Hw.
      destruct (frames_bounds SEGS B LAWS lyc Sc Wc memT mdT 0 pos HAR Hin) as (_ & _ & Fapp).
      rewrite FEQ in Fapp. change (fs_frame_bytes 0) with 64 in Fapp.
      unfold in_app, kLowShadowBeg, ASAN_CEIL in Fapp. unfold amem_range.
      destruct Fapp as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; lia.
    + rewrite Hw. apply (range_addressable_sub _ _ (F + 32) 16); [exact WRA | lia | lia].
    + rewrite Hw. apply (i2_hull_sub _ (F + 32) 16); [exact (WHV ltac:(lia)) | lia | lia | lia].
    + unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. rewrite Hw. lia.
    + exact Hfrm. }
intros fx1 regs2 mem2 md2 Hrel (HJ2 & HP2 & (HQa & HQb) & Hfr2).
apply (HK fx1 regs2 mem2 md2 Hrel HJ2 HP2).
- assert (HB8 : Forall (fun c => 0 <= c < 256) (pf_dec v ++ [0])).
  { apply Forall_app. split; [|constructor; [lia | constructor]].
    apply (Forall_impl _ (fun c (Hc : 0 < c < 256) => conj (Z.lt_le_incl _ _ (proj1 Hc)) (proj2 Hc))).
    exact (i2_pf_dec_nz v). }
  split; [|exact (i2_pf_bytes_nonul _ (i2_pf_dec_nz v))].
  replace (pf_bytes (pf_dec v) ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (pf_dec v ++ [0]))
    by (unfold pf_bytes; rewrite map_app; reflexivity).
  intros j Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  rewrite (HQb (Z.of_nat j) ltac:(rewrite Hw; lia)). rewrite Nat2Z.id, Hbs. f_equal.
  symmetry. exact (i2h_nth_bytes _ j HB8).
- intros x Hx Hwin He Hn. apply (Hfr2 x Hx); [rewrite HK2; lia | cbv beta; rewrite Hw; lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the stretch: from 0x87ea0 after atoi(w->w[k]) of a '#' item, snprintf(number, 16, "%d", that), `j`, to ICMP *)
Lemma i2_at_H : i2_H_spec B MT.
Proof.
unfold i2_H_spec. intros c a HICMP e lyc Sc Wc regs mem md pos sp1 line fn args j1 k Hent Hst Hit Hk H10.
pose proof Hst as (HCOM & Hj1 & H23 & H19 & Hparse).
pose proof HCOM as (HCORE & HLINE & HLS & _).
pose proof HCORE as (HJ & Hsp & Hsp32 & Hrng & H3 & H4 & _ & H9 & H22 & _ & _ & _ & _ & _ & S4 & S5).
pose proof HLS as (_ & _ & _ & L88 & _).
pose proof Hent as (HPRE & Hfrm & _ & _ & _ & HOBJ & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
assert (V25 : VAL (A_OBJ 25) = 0x218e0) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
destruct (i2h_jloc e lyc Sc Wc mem md pos EV_JOINED sp1 HJ Hrng) as (HLO & H47 & H16 & HF1 & HF2).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
assert (Hes : ESTACK = 4096) by reflexivity.
set (v := atoi_a (nth (Z.to_nat k) (e_ws e) [])) in *.
set (F := frame_addr (e_ly e) 0 pos) in *.
pose proof (i2_pf_dec_len v (i2_atoi_range _)) as HL.
assert (HF8 : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
apply (i2h_H_run e lyc Sc Wc regs mem md pos sp1 _ V25 HJ Hsp Hrng Hsp32 H9 H22 L88).
intros regsT memT mdT HJT RK KEEP R1 R10 R11 R12 R13 R21.
pose proof RK as ((K2 & K3 & K4 & _) & _).
assert (S4T : rdW Wc memT (CW_SB + F / 8 + 4) = Some 0) by (rewrite KEEP by (unfold CW_SB; lia); exact S4).
assert (S5T : rdW Wc memT (CW_SB + F / 8 + 5) = Some 0) by (rewrite KEEP by (unfold CW_SB; lia); exact S5).
apply (i2h_call_snpF e lyc Sc Wc regsT memT mdT pos sp1 v CHECK_WORDS_STK [] (e_regs e) (e_ly e) (e_S e) (e_W e)
  (e_mem e) (e_md e) EV_CHECK_WORDS _ Hent HJT).
- unfold spZ. rewrite K2. exact Hsp.
- exact Hrng.
- exact Hsp32.
- rewrite K3, H3. exact Hgp.
- rewrite K4, H4. exact Htp.
- exact R1.
- exact R10.
- exact R11.
- exact R12.
- rewrite R13. exact H10.
- exact (i2_atoi_range _).
- exact S4T.
- exact S5T.
- intros fx1 regs2 mem2 md2 Hrel HJ2 HP2 HSTR HMK2.
  pose proof (i2_rk_trans _ _ _ RK (i2_rk_of_pres _ _ HP2)) as RK2.
  pose proof RK2 as ((_ & _ & _ & _ & _ & _ & K22 & _) & _).
  (* 0x87ebc: `j 87ee4`, at fx1 *)
  apply (i2h_J_run (fx := fx1) (PI := PI) B LAWS e lyc Sc Wc regs2 mem2 md2 pos _ HJ2 ltac:(rewrite K22; exact H22)).
  intros regs3 mem3 md3 HJ3 RK3 R21c KEEP3.
  pose proof (i2_rk_trans _ _ _ RK2 RK3) as RK4.
  assert (HMK : cw_mem_kept B (rdW Wc mem) (rdW Wc mem3) sp1 F).
  { intros x H0 H1 H2 H3'. rewrite (KEEP3 x H0), (HMK2 x H0 H1 H2 H3'). exact (KEEP x H0). }
  pose proof (i2_st_kept (fx := fx) B MT LAWS TL e lyc Sc Wc regs mem md regs3 mem3 md3 pos sp1 line c a fn args j1
    Hent Hst HJ3 RK4 HMK) as HST3.
  assert (INV : INV_ICMP B MT e lyc Sc Wc regs3 mem3 md3 pos sp1 line c a j1 (F + 32) (Some (pf_bytes (pf_dec v)))).
  { apply (i2_icmp B MT e lyc Sc Wc regs3 mem3 md3 pos sp1 line c a fn args j1 (F + 32) (Some (pf_bytes (pf_dec v)))
      HST3).
    - rewrite R21c, (i2h_pres_r _ _ 21%bv HP2 ltac:(i2h_cs_tac)). exact R21.
    - cbn [cw_wq].
      apply (i2_wsrc_eq B e lyc Sc (rdW Wc mem2) (rdW Wc mem3) pos line (F + 32) (pf_bytes (pf_dec v)) KEEP3);
        [lia | unfold pf_bytes; rewrite length_map; lia |].
      split; [exact HSTR|]. split; [lia|]. right; right; left. split; [reflexivity|].
      unfold pf_bytes. rewrite length_map. lia.
    - rewrite Hit. cbn [want_at]. rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hk)). reflexivity. }
  exact (HICMP fx1 e lyc Sc Wc regs3 mem3 md3 pos sp1 line j1 (F + 32) (Some (pf_bytes (pf_dec v)))
    (cw_ent_fx fx fx1 B MT e Hent (fxrel_frm0 fx fx1 Hfrm Hrel)) INV).
Qed.

End e.
End f.
End d.
