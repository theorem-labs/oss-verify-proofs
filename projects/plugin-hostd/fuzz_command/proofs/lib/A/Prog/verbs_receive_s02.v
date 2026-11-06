(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S02 (DUP, 0x8d5c4-0x8d608) of the ASan walk of verbs_receive on
   plugin-hostd/fuzz_command: from vr_b1 (lib/A/Prog/verbs_receive_iface.v) the message size is checked inline (its
   shadow byte is the literal 0, by tok_load), line = strndup(data, n) through astrndup04_rule, the frame's
   shadow is opened over tok (__asan_set_shadow_00, the journal step aj_set_shadow_at of verbs_receive_s02_kit.v) and
   over save (`sb zero,76(s9)`), save is cleared (`sd zero,0(s10)`), strlen measures the line through PaArt's
   aj_art_at, and the branch at 0x8d608 ends the segment at vr_b2 (a non-empty line) or at vr_b3 (an empty one, which
   is already trimmed). The walk is cut at each return into the states s2_P1 (0x8d5e8), s2_P2 (0x8d5f8) and s2_P3
   (0x8d608), each re-seeded as a symbolic state; the shapes are those of cgif_file_fuzzer's walk (A/ACh1.v..ACh8.v)
   as the kit ports it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_s02_kit verbs_receive_s02_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the two bytes ranges the stores of 0x8d5f8 and 0x8d5fc write: save's shadow byte at s9 + 76 and save at s10 *)
Definition s2_rsh : YP09.region := YP09.mkRegion (Some 25%nat) 76 77 76 77 [].
Definition s2_rsv : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 8 [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Variables PC_STRDUP_RA0 PC_STRNDUP_RA0 : Z.
Hypothesis SH00 : RtShadow.aset_shadow_realizes SEGS B (SIGMA CS___asan_set_shadow_00) 0.
Hypothesis STRLEN : RtString.astrlen_realizes SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis ASTRNDUP : RtAlloc04.astrndup04_rule SEGS B MT (SIGMA CS___interceptor_trampoline_strndup) PC_STRNDUP_RA0.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis BLKT : vr_blktail B.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Let RUN := paj_run B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* ----------------------------------------------------------------------------------------------------------
   The states at the three returns of the segment: the journal, the meter, s2_st, the side-stack frame's shadow sh,
   the registers rl, the line block (strndup's copy) among the live blocks, and one more fact X *)
Definition s2_at (e : vrE) (pc : Z) (sh : list Z) (rl : Z -> Z -> list (Z * Z))
  (X : Z -> Z -> world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q lyc Sc regs memc mdc k nm,
cf = cfg_at SEGS (vr_pc pc) regs memc mdc /\
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc Wc memc mdc k /\
k <= 1 /\ vr_meter MT e Sc k nm /\ nm <= 1 /\
s2_st B e pos F lyc Sc Wc memc /\
(forall i, (i < 128)%nat -> rdW Wc memc (shadow_addr F + Z.of_nat i) = Some (nth i sh 0)) /\
vr_rv regs (vr_base B e ++ rl F q) /\
Permutation (ablocks B lyc Sc) (e_O e ++ [vr_lb e q] ++ e_rest e) /\
vr_line0 B e q Wc memc /\ X F q Wc memc.
(* 0x8d5e8, strndup has returned the line block in a0 *)
Definition s2_P1 (e : vrE) : world SEGS -> config -> Prop :=
s2_at e 0x8d5e8 vr_sh1 (fun F q => vr_rl1 e F ++ [(26, F + 608); (10, q)]) (fun _ _ _ _ => True).
(* 0x8d5f8, the shadow of tok is opened *)
Definition s2_P2 (e : vrE) : world SEGS -> config -> Prop :=
s2_at e 0x8d5f8 vr_shm (fun F q => vr_rl2 e F q) (fun _ _ _ _ => True).
(* 0x8d608, save's shadow is opened, save is cleared and a0 holds the length of the line *)
Definition s2_P3 (e : vrE) : world SEGS -> config -> Prop :=
s2_at e 0x8d608 vr_sh2 (fun F q => (10, vr_l (e_n e) (e_D e)) :: vr_rl2 e F q)
  (fun F _ Wc memc => rdword (rdW Wc memc) (F + 608) = Some 0).

(* ----------------------------------------------------------------------------------------------------------
   0x8d5c4 .. 0x8d5e4: the inline check of msg+16, n and data, s10 = F + 608, and strndup(data, n) *)
Lemma s2_A : forall e W cf, vr_ent B MT e -> vr_b1 B MT e W cf -> SRr SEGS W cf (s2_P1 e).
Proof.
intros e W cf HENT Hb1.
destruct Hb1 as (pos & F & lyc & Sc & regsc & memc & mdc & k & nm & -> & HCORE).
destruct (vr_s02_seed_ok B MT e W pos F lyc Sc regsc memc mdc k nm HENT HCORE) as (E & HEI & HS & SHOK & EE & E32 & E33).
pose proof HENT as (HPRE0 & HROD0 & Hr10 & HOBJ & Hfd & Hdata & Hnv & Hnb & HlenD & Hinblk & HnotO & HbytesD & Hmsg64
  & HREC0 & Hcalls & Hans & Hrep & Hnrep & Hdecl & HPERM0 & Hq0 & HGOT0 & HRO0 & HROIN & HVOBJ & Herrno & Hflag
  & HguardE & Hfrlen & Hevb & Hlive & HMOK & HFRM0).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof HCORE as (HJ & Hkk & HMET & Hnmm & HFRM & HRV & HSAV & HSPL & HENV & HREC & HnOc & HPERM & HQV).
unfold cfg_at. change (w64 (vr_pc 0x8d5c4)) with (Z_to_bv 64 (BASE + (AF_verbs_receive + 0x144))).
paj_run_tok RUN HS HJ SHOK vr_Bspan.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
match goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mt ?m0] =>
  set (mdv := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdv end.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof s2_stk_ge as [Hstk1 Hstk2]. assert (HAS : ASTACK = 16384) by reflexivity.
pose proof HJ as (HAR1 & Hly & _ & _ & _ & Hfrs & Hnev & Hk0 & JF1 & JF2 & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (s2_s1_shape e Hal16) as [Hs1 Hs1al].
assert (Hs1r : vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192) by lia.
pose proof pa_B_ok as HBASE.
pose proof HFRM as (EF & HFL & HSH).
assert (Hfr : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W (ms_mem ms) mdv 4 pos HAR1 Hfr) as (HF0 & HFc & HFapp).
change (fs_frame_bytes 4) with 1024 in HFc. rewrite <- EF in HF0, HFc.
(* the run wrote nothing: the memory at the call reads as the boundary's *)
assert (KM : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (r & Hin & Hr). unfold vr_s02_ss in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | []]. unfold vr_msg_region in Hr. cbn [YP09.r_wlo YP09.r_whi YP09.r_base] in Hr. lia. }
(* the registers of the boundary, and those at the call *)
assert (R2 : getr regsc (Z_to_bv 5 2) = w64 (vr_s1 e)) by (apply (vr_rv_get regsc _ 2 _ HRV); cbn; tauto).
assert (R3 : getr regsc (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (vr_rv_get regsc _ 3 _ HRV); cbn; tauto).
assert (R4 : getr regsc (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (vr_rv_get regsc _ 4 _ HRV); cbn; tauto).
assert (R8 : getr regsc (Z_to_bv 5 8) = w64 (vr_sp0 e)) by (apply (vr_rv_get regsc _ 8 _ HRV); cbn; tauto).
assert (R20 : getr regsc (Z_to_bv 5 20) = w64 F) by (apply (vr_rv_get regsc _ 20 _ HRV); cbn; tauto).
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2.
prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
assert (Q10 : getr (ms_regs ms) 10 = w64 (e_data e)) by (rewrite T10; exact E32).
assert (Q11 : getr (ms_regs ms) 11 = w64 (e_n e)) by (rewrite T11; exact E33).
assert (Q2 : getr (ms_regs ms) 2 = w64 (vr_s1 e))
  by (rewrite T2, (EE 2%nat (2%bv : bv 5) eq_refl), <- R2; f_equal; apply bv_eq; reflexivity).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite T3, (EE 3%nat (3%bv : bv 5) eq_refl), <- R3; f_equal; apply bv_eq; reflexivity).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite T4, (EE 4%nat (4%bv : bv 5) eq_refl), <- R4; f_equal; apply bv_eq; reflexivity).
assert (Q8 : getr (ms_regs ms) 8 = w64 (vr_sp0 e))
  by (rewrite T8, (EE 8%nat (8%bv : bv 5) eq_refl), <- R8; f_equal; apply bv_eq; reflexivity).
assert (Hsp1 : spZ (ms_regs ms) = vr_s1 e) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z (ms_regs ms) = vr_sp0 e) by (unfold s0Z; rewrite Q8; unfold w64; apply unsigned_lit_small; lia).
assert (Hra : 4096 <= raZ (ms_regs ms)) by (unfold raZ; rewrite T1; rewrite unsigned_lit_small by lia; lia).
assert (Hsame : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)).
{ intros r Hr.
  repeat (destruct Hr as [<- | Hr];
    [match goal with |- getr _ ?rr = _ =>
       let T := fresh "T" in prreg HS rr T; rewrite T; apply EE; reflexivity end |]).
  destruct Hr. }
(* the message bytes, at the call *)
assert (HOincl : forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ _ HREC0 Hpn)).
assert (HOc : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn).
assert (Hdc : In (e_data e, Z.max (e_n e) 1) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). pose proof (Permutation_in _ HPERM0 Hinblk) as H1.
  apply in_app_or in H1 as [H1 | H1]; [exfalso; exact (HnotO H1) | apply in_or_app; right; exact H1]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hdc) as (_ & Hd4096 & Hdceil & _ & _ & _ & _).
pose proof (req_size_pos (Z.max (e_n e) 1) ltac:(lia)) as [_ Hrq].
pose proof (s2_l_range (e_n e) (e_D e) ltac:(lia)) as Hl. unfold vr_l in Hl.
assert (HbytesT : abytes_atR (rdW W (ms_mem ms)) (e_data e) (e_D e)).
{ intros i Hi. rewrite (JF2 (e_data e) (Z.max (e_n e) 1) (Z.of_nat i) Hinblk Hdc ltac:(lia)).
  - exact (HbytesD i Hi).
  - apply (s2_blk_not_fp B PROGU e lyc Sc W (ms_mem ms) mdv _ _ _ HAR1 HOc Hdc HnotO). lia. }
assert (HRD : aread_ok SEGS ASTACK W (ms_regs ms) (ms_mem ms) (e_data e)
  (Z.min (StrFun.strnlen_res (e_n e) (e_D e) + 1) (Z.of_nat (length (e_D e))))).
{ apply (aread_ok_of_block SEGS B LAWS ASTACK lyc Sc W (ms_regs ms) (ms_mem ms) mdv (e_data e) (Z.max (e_n e) 1));
  [exact HAR1 | exact Hdc | lia | lia | lia | rewrite Hsp1; lia]. }
assert (HAROm : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ destruct HENV as (HARO & _). apply (s2_aro_keep B RRO _ _ HARO). intros a _ _ _. apply KM. }
pose proof (vr_rtrom_ok B W (ms_mem ms) HAROm) as HROM.
assert (HBB : blocks_bytes Sc + (StrFun.strnlen_res (e_n e) (e_D e) + 1) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B lyc Sc), (s2_bsum_perm _ _ HPERM).
  rewrite (blocks_bytes_bsum B (e_ly e) (e_S e)), (s2_bsum_perm _ _ HPERM0) in Hlive.
  rewrite !bsum_app in *. replace (bsum []) with 0 in * by reflexivity.
  unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in Hlive. lia. }
assert (HSAVm : vr_saved e W (ms_mem ms)).
{ intros j r Hj. apply (aval_mem_agree _ _ _ _ _ (HSAV j r Hj)). intros kk _. apply KM. }
destruct (vr_chain_at B e [(4, pos)] lyc Sc W (ms_mem ms) mdv k (ms_regs ms) HJ HPRE0 HSAVm HOincl Hsp1 Hs0 Hra)
  as (ch & Hch).
assert (HMO : mo_ok MT Sc (mo_malloc MT (StrFun.strnlen_res (e_n e) (e_D e) + 1)))
  by exact (s2_mo_first B MT MTL e Sc k nm (StrFun.strnlen_res (e_n e) (e_D e) + 1) HENT HMET Hkk
    ltac:(unfold VERBS_RECEIVE_REQ; lia)).
pmkst HS.
eapply SRr_bind.
{ eapply (ASTRNDUP W (ms_regs ms) (ms_mem ms) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(4, pos)] lyc Sc mdv k (e_data e) (e_n e) (e_D e) (vr_s1 e - vr_sp0 e) (getr (ms_regs ms) 1) ch HJ Q10 Q11).
  - lia.
  - lia.
  - exact HbytesT.
  - exact (s2_memchr (e_data e) (e_D e) (e_n e) (eq_sym HlenD)).
  - exact HRD.
  - exists (e_data e), (Z.max (e_n e) 1). split; [exact Hdc | lia].
  - intros (a & Ha & Herr). pose proof (pal_env B TL) as (_ & Himg & _).
    apply (blk_img SEGS B LAWS lyc Sc W (ms_mem ms) mdv _ _ a HAR1 Hdc); [lia | exact (Himg a Herr)].
  - exact HROM.
  - unfold MALLOC_MAX. lia.
  - exact HBB.
  - rewrite Hsp1. lia.
  - destruct Hs1 as [E1 | E1]; rewrite E1;
    [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia];
    reflexivity.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - pose proof (s2_ev_vr_pos (e_R e) (e_D e)). lia.
  - exact Hch.
  - exact HMO. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & H10' & Hfr2 & Hres & Hab2 & Hkept
  & Hbytes & Hmo2).
apply SRr_ret.
pose proof HJ2 as (HAR2 & Hly2 & _).
assert (EF2 : forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p).
{ intros cid p. unfold frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EFa & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EFb & _). rewrite EFa, EFb. reflexivity. }
assert (EG2 : forall cid p, flag_addr ly2 cid p = flag_addr lyc cid p).
{ intros cid p. unfold flag_addr. pose proof Hly as (_ & _ & _ & _ & _ & EFa & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & EFb & _). rewrite EFa, EFb. reflexivity. }
destruct (s2_keep_call B e pos F lyc Sc W (ms_mem ms) ly2 S2 W2 mem2 md2
  (vr_sp0 e + (vr_s1 e - vr_sp0 e) - ASTACK) (vr_sp0 e + (vr_s1 e - vr_sp0 e)) res
  (StrFun.strnlen_res (e_n e) (e_D e) + 1) Hkept HAR2 Hab2 Hfr Hfr2 EF (eq_trans (EF2 4 pos) (eq_sym EF)) HOc
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [KS KSH].
exists pos, F, res, ly2, S2, regs2, mem2, md2, (k + 1), (nm + 1).
split; [unfold cfg_at; rewrite T1; reflexivity|].
split; [exact HJ2|].
split; [lia|].
split; [exact (s2_meter_malloc MT MTL e Sc S2 k nm (StrFun.strnlen_res (e_n e) (e_D e) + 1) HMET Hmo2
  ltac:(unfold VERBS_RECEIVE_REQ; lia))|].
split; [lia|].
split.
{ apply (s2_st_keep B RRO PROGU e pos F lyc Sc W memc ly2 S2 W2 mem2); [| exact (EF2 4 pos) | exact (EG2 4 pos) | |].
  - exact (conj EF (conj HFL (conj HSAV (conj HSPL (conj (proj1 HENV) (conj HREC HQV)))))).
  - intros pn Hpn _. rewrite Hab2. apply in_or_app. left. exact (HOc pn Hpn).
  - intros a Ha. rewrite (KS a Ha). apply KM. }
split.
{ intros i Hi. rewrite (KSH (Z.of_nat i) ltac:(lia)), KM. exact (HSH i Hi). }
split.
{ rewrite app_assoc. apply (s2_rv_from regsc regs2 _ _ HRV).
  - intros r Hr. rewrite (HP2 r).
    + apply Hsame. exact Hr.
    + cbn [map fst vr_base vr_rl1 app In] in Hr. unfold acallee_saved. lia.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    + rewrite (HP2 26) by (unfold acallee_saved; lia). prreg HS (Z_to_bv 5 26) T26.
      rewrite T26, (EE 20%nat (Z_to_bv 5 20) eq_refl), R20. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + rewrite <- H10'. f_equal. }
split.
{ rewrite Hab2. eapply Permutation_trans; [apply Permutation_app_tail; exact HPERM|].
  rewrite <- app_assoc. apply Permutation_app_head. cbn [app]. apply Permutation_sym, Permutation_cons_append. }
split; [|exact I].
assert (Hnew : ~ In (vr_lb e res) (ablocks B lyc Sc)) by exact (s2_blk_new B ly2 S2 W2 mem2 md2 _ _ HAR2 Hab2).
split; [split|exact Hbytes].
- cbn [fst vr_lb]. lia.
- intros Hin. apply Hnew. apply (Permutation_in _ (Permutation_sym HPERM)). exact (Permutation_in _ HPERM0 Hin).
Qed.

(* ----------------------------------------------------------------------------------------------------------
   0x8d5e8 .. 0x8d5f4: s5 = line, and __asan_set_shadow_00(s11, 64) opens the shadow of tok *)
Lemma s2_B : forall e W cf, vr_ent B MT e -> s2_P1 e W cf -> SRr SEGS W cf (s2_P2 e).
Proof.
intros e W cf HENT HP1.
destruct HP1 as (pos & F & q & lyc & Sc & regs & memc & mdc & k & nm & -> & HJ & Hk1 & HMET & Hnm1 & HST & HSH & HRV
  & HPERM & HLINE & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof s2_stk_ge as [Hstk1 Hstk2]. assert (HES : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & Hk0 & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (s2_s1_shape e Hal16) as [Hs1 Hs1al].
assert (Hs1r : vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192) by lia.
pose proof pa_B_ok as HBASE.
pose proof HST as (EF & _).
assert (Hfr : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hfr) as (HF0 & HFc & HFapp).
change (fs_frame_bytes 4) with 1024 in HFc. rewrite <- EF in HF0, HFc.
pose proof (s2_fshadow_band B pos F lyc Sc W memc mdc 0 HAR Hfr EF ltac:(lia)) as Hsb0.
pose proof (s2_fshadow_band B pos F lyc Sc W memc mdc 127 HAR Hfr EF ltac:(lia)) as Hsb1.
assert (HOc : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; left; reflexivity).
pose proof (s2_l_range (e_n e) (e_D e) ltac:(destruct HENT as (_ & _ & _ & _ & _ & _ & _ & Hn & _); lia)) as Hl.
assert (R2 : getr regs (Z_to_bv 5 2) = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ HRV); cbn; tauto).
assert (R3 : getr regs (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ HRV); cbn; tauto).
assert (R4 : getr regs (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ HRV); cbn; tauto).
assert (R10 : getr regs (Z_to_bv 5 10) = w64 q) by (apply (vr_rv_get regs _ 10 _ HRV); cbn; tauto).
assert (R27 : getr regs (Z_to_bv 5 27) = w64 (shadow_addr F + 4)) by (apply (vr_rv_get regs _ 27 _ HRV); cbn; tauto).
(* the seed at 0x8d5e8 *)
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
unfold cfg_at. change (w64 (vr_pc 0x8d5e8)) with (Z_to_bv 64 (BASE + 28932)).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s2_ss 28932 [])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 28932)) memc (seg_rom SEGS))))
  by (apply s2_seed; [reflexivity | constructor | exact I]).
set (E := Eimg (Ereg regs [])) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; unfold E; apply s2_ew; exact Hn).
clearbody E.
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
match goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mt ?m0] =>
  set (mdv := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdv end.
assert (KM : forall a, rdW W (ms_mem ms) a = rdW W memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (r & Hin & _). cbn in Hin. destruct Hin. }
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (1%bv : bv 5) T1.
prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
assert (Q10 : getr (ms_regs ms) 10 = w64 (shadow_addr F + 4))
  by (rewrite T10, (EE 27%nat (Z_to_bv 5 27) eq_refl); exact R27).
assert (Q11 : getr (ms_regs ms) 11 = w64 64) by exact T11.
assert (Q2 : getr (ms_regs ms) 2 = w64 (vr_s1 e)) by (rewrite T2, (EE 2%nat (Z_to_bv 5 2) eq_refl); exact R2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite T3, (EE 3%nat (Z_to_bv 5 3) eq_refl); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite T4, (EE 4%nat (Z_to_bv 5 4) eq_refl); exact R4).
assert (Hsp1 : spZ (ms_regs ms) = vr_s1 e) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS.
eapply SRr_bind.
{ apply (aj_set_shadow_at B 0 (SIGMA CS___asan_set_shadow_00) SH00 ltac:(lia) W (ms_regs ms) (ms_mem ms)
    VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv k 4 pos
    (shadow_addr F + 4) 64 (vr_s1 e - vr_sp0 e) (getr (ms_regs ms) 1) HJ).
  - rewrite Hsp1. lia.
  - destruct Hs1 as [E1 | E1]; rewrite E1;
    [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia];
    reflexivity.
  - lia.
  - lia.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Q3.
  - exact Q4.
  - left. reflexivity.
  - lia.
  - exact Q10.
  - exact Q11.
  - lia.
  - rewrite <- EF. lia.
  - rewrite <- EF. change (fs_frame_bytes 4 / 8) with 128. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hset & Hkeep).
apply SRr_ret.
assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 4 <= a < shadow_addr F + 4 + 64) ->
  rdW W mem2 a = rdW W memc a) by (intros a Ha Hn; rewrite (Hkeep a Ha Hn); apply KM).
exists pos, F, q, lyc, Sc, regs2, mem2, md2, k, nm. cbv beta.
split; [unfold cfg_at; rewrite T1; reflexivity|].
split; [exact HJ2|]. split; [exact Hk1|]. split; [exact HMET|]. split; [exact Hnm1|].
split.
{ apply (s2_st_keep B RRO PROGU e pos F lyc Sc W memc lyc Sc W mem2 HST eq_refl eq_refl (fun pn _ H => H)).
  intros a Ha. apply KK.
  - destruct (s2_keep_disj B e pos F lyc Sc W memc mdc a HAR Hfr EF HOc ltac:(lia) Ha) as [(Ha1 & _ & _) | Ha1]; lia.
  - destruct (s2_keep_disj B e pos F lyc Sc W memc mdc a HAR Hfr EF HOc ltac:(lia) Ha) as [(Ha1 & Ha2 & _) | Ha1]; lia. }
split.
{ intros i Hi.
  pose proof (s2_fshadow_band B pos F lyc Sc W memc mdc (Z.of_nat i) HAR Hfr EF ltac:(lia)) as Hb.
  destruct (Nat.lt_ge_cases i 4) as [Hi4 | Hi4]; [|destruct (Nat.lt_ge_cases i 68) as [Hi68 | Hi68]].
  - rewrite (s2_shm_kept i Hi ltac:(lia)), KK by lia. exact (HSH i Hi).
  - rewrite (s2_shm_set i ltac:(lia)).
    replace (shadow_addr F + Z.of_nat i) with (shadow_addr F + 4 + (Z.of_nat i - 4)) by lia. apply Hset. lia.
  - rewrite (s2_shm_kept i Hi ltac:(lia)), KK by lia. exact (HSH i Hi). }
split.
{ assert (Hrv1 : vr_rv regs (vr_base B e ++ vr_rl1 e F ++ [(26, F + 608)])).
  { apply (s2_rv_incl regs _ _ HRV). intros x Hx. unfold vr_base, vr_rl1 in *. cbn [app In] in Hx |- *. tauto. }
  apply (s2_rv_incl regs2 ((vr_base B e ++ vr_rl1 e F ++ [(26, F + 608)]) ++ [(21, q)])).
  - apply (s2_rv_from regs regs2 _ _ Hrv1).
    + intros r Hr. rewrite (HP2 r).
      * cbn [map fst vr_base vr_rl1 app] in Hr.
        repeat (destruct Hr as [<- | Hr];
          [match goal with |- getr _ ?rr = _ =>
             let T := fresh "T" in prreg HS rr T; rewrite T; apply EE; reflexivity end |]).
        destruct Hr.
      * cbn [map fst vr_base vr_rl1 app In] in Hr. unfold acallee_saved. lia.
    + apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
      rewrite (HP2 21) by (unfold acallee_saved; lia). prreg HS (Z_to_bv 5 21) T21.
      rewrite T21, (EE 10%nat (Z_to_bv 5 10) eq_refl). exact R10.
  - intros x Hx. unfold vr_base, vr_rl1, vr_rl2 in *. cbn [app In] in Hx |- *. tauto. }
split; [exact HPERM|].
split; [|exact I].
apply (s2_line0_agree B e q W memc W mem2 HLINE ltac:(lia)). intros kk Hkk.
destruct (s2_blk_disj B pos F lyc Sc W memc mdc q (vr_l (e_n e) (e_D e) + 1) (q + kk) HAR Hfr EF Hlb ltac:(lia))
  as (Hb1 & Hb2 & Hb3).
apply KK; lia.
Qed.

(* ----------------------------------------------------------------------------------------------------------
   0x8d5f8 .. 0x8d604: save's shadow byte and save are cleared, and strlen(line) *)
Lemma s2_C : forall e W cf, vr_ent B MT e -> s2_P2 e W cf -> SRr SEGS W cf (s2_P3 e).
Proof.
intros e W cf HENT HP2.
destruct HP2 as (pos & F & q & lyc & Sc & regs & memc & mdc & k & nm & -> & HJ & Hk1 & HMET & Hnm1 & HST & HSH & HRV
  & HPERM & HLINE & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof s2_stk_ge as [Hstk1 Hstk2]. assert (HES : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & Hk0 & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (s2_s1_shape e Hal16) as [Hs1 Hs1al].
assert (Hs1r : vr_sp0 e - 208 <= vr_s1 e <= vr_sp0 e - 192) by lia.
pose proof pa_B_ok as HBASE.
pose proof HST as (EF & _).
assert (Hfr : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR Hfr) as (HF0 & HFc & HFapp).
change (fs_frame_bytes 4) with 1024 in HFc, HFapp. rewrite <- EF in HF0, HFc, HFapp.
pose proof (s2_fshadow_band B pos F lyc Sc W memc mdc 0 HAR Hfr EF ltac:(lia)) as Hsb0.
pose proof (s2_fshadow_band B pos F lyc Sc W memc mdc 127 HAR Hfr EF ltac:(lia)) as Hsb1.
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hfr) as (_ & _ & Hfb & Hfsh).
assert (HOc : forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact Hpn).
assert (Hlb : In (vr_lb e q) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; left; reflexivity).
pose proof (s2_l_range (e_n e) (e_D e) ltac:(destruct HENT as (_ & _ & _ & _ & _ & _ & _ & Hn & _); lia)) as Hl.
assert (R2 : getr regs (Z_to_bv 5 2) = w64 (vr_s1 e)) by (apply (vr_rv_get regs _ 2 _ HRV); cbn; tauto).
assert (R3 : getr regs (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (vr_rv_get regs _ 3 _ HRV); cbn; tauto).
assert (R4 : getr regs (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (vr_rv_get regs _ 4 _ HRV); cbn; tauto).
assert (R21 : getr regs (Z_to_bv 5 21) = w64 q) by (apply (vr_rv_get regs _ 21 _ HRV); cbn; tauto).
assert (R25 : getr regs (Z_to_bv 5 25) = w64 (shadow_addr F)) by (apply (vr_rv_get regs _ 25 _ HRV); cbn; tauto).
assert (R26 : getr regs (Z_to_bv 5 26) = w64 (F + 608)) by (apply (vr_rv_get regs _ 26 _ HRV); cbn; tauto).
(* the seed at 0x8d5f8, with the two bytes ranges the stores write *)
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (E25 : bv_unsigned (ew (Eimg (Ereg regs [])) 25) = shadow_addr F)
  by (rewrite (s2_ew regs 25 (Z_to_bv 5 25) eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (E26 : bv_unsigned (ew (Eimg (Ereg regs [])) 26) = F + 608)
  by (rewrite (s2_ew regs 26 (Z_to_bv 5 26) eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (vr_pc 0x8d5f8)) with (Z_to_bv 64 (BASE + 28948)).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s2_ss 28948 [s2_rsh; s2_rsv])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 28948)) memc (seg_rom SEGS)))).
{ apply s2_seed; [reflexivity | |].
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, s2_rsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E25. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace o with 76 by lia. rewrite EF.
      exact (proj1 (Hfsh 76 ltac:(change (fs_frame_bytes 4 / 8) with 128; lia))).
    + unfold region_ok, s2_rsv. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E26. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hfb. rewrite <- EF. change (fs_frame_bytes 4) with 1024. lia.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, s2_rsh, s2_rsv. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E25, E26.
    unfold in_app, kLowShadowBeg in HFapp. lia. }
set (E := Eimg (Ereg regs [])) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; unfold E; apply s2_ew; exact Hn).
clearbody E.
paj_run_shc RUNP RUNC HS HJ.
{ change (ss_mem (s2_ss 28948 [s2_rsh; s2_rsv])) with [s2_rsh; s2_rsv].
  eapply awr_ok_cons_gen with (b := shadow_addr F); [reflexivity | exact E25 | |].
  - intros a Ha. cbn [s2_rsh YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists 4, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite <- EF.
    change (fs_frame_bytes 4 / 8) with 128. lia.
  - eapply awr_ok_cons_gen with (b := F + 608); [reflexivity | exact E26 | | apply awr_ok_nil].
    intros a Ha. cbn [s2_rsv YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left.
    exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite <- EF.
    change (fs_frame_bytes 4) with 1024. lia. }
match goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mt ?m0] =>
  set (mdv := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdv end.
pose proof HJ as (HAR1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hlb) as (_ & Hq4096 & Hqc & _ & _ & _ & _).
cbn [fst snd vr_lb] in Hq4096, Hqc.
pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)) as [_ Hrql].
pose proof HENT as (_ & _ & _ & _ & _ & _ & _ & Hn & HlenD & _).
(* the two stores, read back from the regions of the symbolic state *)
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as Hr0.
pose proof (field_of_region_any E _ 25 (shadow_addr F) _ _ _ _ _ 76 1 (SLit 0) Hr0 E25 (or_introl eq_refl) ltac:(lia))
  as V0.
pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as Hr1.
pose proof (field_of_region_any E _ 26 (F + 608) _ _ _ _ _ 0 8 (SLit 0) Hr1 E26 (or_introl eq_refl) ltac:(lia))
  as V1.
cbn [ms_mem restrict] in V0, V1. rewrite Z.add_0_r in V1.
assert (Ez1 : bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 1) = 0) by (vm_compute; reflexivity).
assert (Ez8 : bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 8) = 0) by (vm_compute; reflexivity).
rewrite Ez1 in V0. rewrite Ez8 in V1.
assert (Hsh76 : rdW W (ms_mem ms) (shadow_addr F + 76) = Some 0).
{ pose proof (s2_aval_of_val SEGS (w_H W) (ms_mem ms) _ _ _ V0 0%nat ltac:(cbn; lia)) as A0.
  rewrite Z.add_0_r in A0. rewrite A0. vm_compute. reflexivity. }
assert (Hsv : rdword (rdW W (ms_mem ms)) (F + 608) = Some 0)
  by (apply (rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [exact V1 | lia]).
(* every other byte is the boundary's *)
assert (KMC : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr F + 76 <= a < shadow_addr F + 77) -> ~ (F + 608 <= a < F + 616) ->
  rdW W (ms_mem ms) a = rdW W memc a).
{ intros a Ha H1 H2. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros (r & Hin & Hr). change (ss_mem (s2_ss 28948 [s2_rsh; s2_rsv])) with [s2_rsh; s2_rsv] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [s2_rsh s2_rsv YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite E25 in Hr | rewrite E26 in Hr]; lia. }
(* the registers at the call of strlen *)
prreg HS (10%bv : bv 5) T10. prreg HS (1%bv : bv 5) T1.
prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
assert (Q10 : getr (ms_regs ms) 10 = w64 q) by (rewrite T10, (EE 21%nat (Z_to_bv 5 21) eq_refl); exact R21).
assert (Q2 : getr (ms_regs ms) 2 = w64 (vr_s1 e)) by (rewrite T2, (EE 2%nat (Z_to_bv 5 2) eq_refl); exact R2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite T3, (EE 3%nat (Z_to_bv 5 3) eq_refl); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite T4, (EE 4%nat (Z_to_bv 5 4) eq_refl); exact R4).
assert (Hsp1 : spZ (ms_regs ms) = vr_s1 e) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Ho16 : (vr_s1 e - vr_sp0 e) mod 16 = 0).
{ destruct Hs1 as [E1 | E1]; rewrite E1;
  [replace (vr_sp0 e - 192 - vr_sp0 e) with (-192) by lia | replace (vr_sp0 e - 208 - vr_sp0 e) with (-208) by lia];
  reflexivity. }
(* strlen's premises: the line as a C string, readable, its tail word, and the runtime's read-only words *)
set (s := firstn (Z.to_nat (vr_l (e_n e) (e_D e))) (e_D e)).
assert (Hslen : astr_len s = vr_l (e_n e) (e_D e)).
{ unfold astr_len, s. rewrite length_firstn.
  assert (Hz : Z.of_nat (Z.to_nat (vr_l (e_n e) (e_D e))) = vr_l (e_n e) (e_D e)) by (apply Z2Nat.id; lia).
  rewrite Nat.min_l by lia. exact Hz. }
assert (HL1 : vr_line0 B e q W (ms_mem ms)).
{ apply (s2_line0_agree B e q W memc W (ms_mem ms) HLINE ltac:(lia)). intros kk Hkk.
  destruct (s2_blk_disj B pos F lyc Sc W memc mdc q (vr_l (e_n e) (e_D e) + 1) (q + kk) HAR Hfr EF Hlb ltac:(lia))
    as (Hb1 & Hb2 & Hb3).
  apply KMC; lia. }
assert (HstrT : astr_at SEGS W (ms_mem ms) q s).
{ apply astr_atR_view. split; [exact (proj2 HL1)|]. exact (s2_prefix_no0 (e_D e) (e_n e) (eq_sym HlenD)). }
assert (HRDs : aread_ok SEGS ESTACK W (ms_regs ms) (ms_mem ms) q (astr_len s + 1)).
{ apply (aread_ok_of_block SEGS B LAWS ESTACK lyc Sc W (ms_regs ms) (ms_mem ms) mdv q (vr_l (e_n e) (e_D e) + 1));
  [exact HAR1 | exact Hlb | lia | lia | lia | rewrite Hsp1; lia]. }
assert (Htail : atail_vis SEGS W (ms_mem ms) (q + astr_len s))
  by (apply (BLKT lyc Sc W (ms_mem ms) mdv q (vr_l (e_n e) (e_D e) + 1)); [exact HAR1 | exact Hlb | lia]).
assert (HAROm : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ pose proof HST as (_ & _ & _ & _ & HARO & _). apply (s2_aro_keep B RRO _ _ HARO). intros a Hi _ _.
  pose proof (pa_img_range a Hi) as Hia. apply KMC; [lia | lia |].
  intros Ha. apply (frm_img SEGS B LAWS lyc Sc W memc mdc 4 pos a HAR Hfr); [|exact Hi].
  rewrite <- EF. change (fs_frame_bytes 4) with 1024. lia. }
pose proof (vr_rtrom_ok B W (ms_mem ms) HAROm) as HROM.
assert (HPRE : ecall_pre_stk SEGS B ESTACK lyc Sc W (ms_regs ms) (ms_mem ms) mdv).
{ apply (ecall_pre_stk_at SEGS B ESTACK VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(4, pos)] lyc Sc W (ms_mem ms) mdv k (ms_regs ms) (vr_s1 e - vr_sp0 e) HJ);
  [rewrite Hsp1; lia | exact Ho16 | lia | lia | lia | rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | exact Q3 | exact Q4]. }
pmkst HS.
eapply SRr_bind.
{ apply (ART ESTACK (fun _ => False) (SIGMA CS___interceptor_trampoline_strlen) W (ms_regs ms) (ms_mem ms)
    VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc mdv k
    (vr_s1 e - vr_sp0 e) (getr (ms_regs ms) 1) (fun regs' _ => getr regs' 10 = w64 (astr_len s)) HJ).
  - rewrite Hsp1. lia.
  - exact Ho16.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - intros a [].
  - exact (STRLEN lyc Sc W (ms_regs ms) (ms_mem ms) mdv q s HPRE Q10 ltac:(lia) HstrT HRDs Htail HROM). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & Hkeep).
apply SRr_ret.
assert (KA : forall a, 0 <= a < alloc_ceiling -> rdW W mem2 a = rdW W (ms_mem ms) a).
{ intros a Ha. apply Hkeep; [lia | lia | intros []]. }
assert (KK : forall a, 0 <= a < 2 ^ 64 -> (a < alloc_ceiling \/ vr_s1 e <= a) ->
  ~ (shadow_addr F + 76 <= a < shadow_addr F + 77) -> ~ (F + 608 <= a < F + 616) -> rdW W mem2 a = rdW W memc a).
{ intros a Ha Hw H1 H2. rewrite (Hkeep a Ha); [exact (KMC a Ha H1 H2) | lia | intros []]. }
exists pos, F, q, lyc, Sc, regs2, mem2, md2, k, nm. cbv beta.
split; [unfold cfg_at; rewrite T1; reflexivity|].
split; [exact HJ2|]. split; [exact Hk1|]. split; [exact HMET|]. split; [exact Hnm1|].
split.
{ apply (s2_st_keep B RRO PROGU e pos F lyc Sc W memc lyc Sc W mem2 HST eq_refl eq_refl (fun pn _ H => H)).
  intros a Ha.
  destruct (s2_keep_disj B e pos F lyc Sc W memc mdc a HAR Hfr EF HOc ltac:(lia) Ha) as [(Ha1 & Ha2 & Ha3) | Ha1];
  apply KK; lia. }
split.
{ intros i Hi.
  pose proof (s2_fshadow_band B pos F lyc Sc W memc mdc (Z.of_nat i) HAR Hfr EF ltac:(lia)) as Hb.
  destruct (Nat.eq_dec i 76) as [-> | Hi76].
  - rewrite s2_sh2_76. rewrite KA by lia. exact Hsh76.
  - rewrite (s2_sh2_of_shm i Hi Hi76). unfold in_app, kLowShadowBeg in HFapp. rewrite KK by lia. exact (HSH i Hi). }
split.
{ apply (s2_rv_incl regs2 ((vr_base B e ++ vr_rl2 e F q) ++ [(10, vr_l (e_n e) (e_D e))])).
  - apply (s2_rv_from regs regs2 _ _ HRV).
    + intros r Hr. rewrite (HP2 r).
      * cbn [map fst vr_base vr_rl2 app] in Hr.
        repeat (destruct Hr as [<- | Hr];
          [match goal with |- getr _ ?rr = _ =>
             let T := fresh "T" in prreg HS rr T; rewrite T; apply EE; reflexivity end |]).
        destruct Hr.
      * cbn [map fst vr_base vr_rl2 app In] in Hr. unfold acallee_saved. lia.
    + apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. rewrite <- Hslen, <- HQ2. f_equal.
  - intros x Hx. unfold vr_base, vr_rl2 in *. cbn [app In] in Hx |- *. tauto. }
split; [exact HPERM|].
split.
{ apply (s2_line0_agree B e q W memc W mem2 HLINE ltac:(lia)). intros kk Hkk.
  destruct (s2_blk_disj B pos F lyc Sc W memc mdc q (vr_l (e_n e) (e_D e) + 1) (q + kk) HAR Hfr EF Hlb ltac:(lia))
    as (Hb1 & Hb2 & Hb3).
  apply KK; lia. }
rewrite (rdword_ext (rdW W (ms_mem ms)) (rdW W mem2) (F + 608)); [exact Hsv|].
intros kk Hkk. apply KA. lia.
Qed.

(* ----------------------------------------------------------------------------------------------------------
   The record vr_core of the segment's exits, from the facts of a state of the segment *)
Lemma s2_core : forall e pos F q sh rl lyc Sc (Wc : world SEGS) regs memc mdc k nm,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc Wc memc mdc k -> k <= 1 -> vr_meter MT e Sc k nm -> nm <= 1 ->
s2_st B e pos F lyc Sc Wc memc ->
(forall i, (i < 128)%nat -> rdW Wc memc (shadow_addr F + Z.of_nat i) = Some (nth i sh 0)) ->
vr_rv regs (vr_base B e ++ rl) ->
Permutation (ablocks B lyc Sc) (e_O e ++ [vr_lb e q] ++ e_rest e) ->
vr_core B MT e pos F [vr_lb e q] sh (vr_sl1 F) rl (e_R e) (e_O e) (e_q0 e) k 1 nm 1 lyc Sc Wc regs memc mdc.
Proof.
intros e pos F q sh rl lyc Sc Wc regs memc mdc k nm HENT HJ Hk HM Hnm (EF & HFL & HSAV & HSPL & HARO & HREC & HQV) HSH
  HRV HPERM.
pose proof HJ as (HAR & _).
split; [exact HJ|]. split; [exact Hk|]. split; [exact HM|]. split; [exact Hnm|].
split; [exact (conj EF (conj HFL HSH))|].
split; [exact HRV|]. split; [exact HSAV|]. split; [exact HSPL|].
split; [exact (vr_env_of_aro B ROA RECC lyc Sc Wc memc mdc HAR HARO)|].
split; [exact HREC|].
split; [destruct HENT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HnotO & _); exact HnotO|].
split; [exact HPERM | exact HQV].
Qed.

(* ----------------------------------------------------------------------------------------------------------
   0x8d608: beqz a0 leaves for 0x8d67c (an empty line, vr_b3) or goes on at 0x8d60c (vr_b2) *)
Lemma s2_D : forall e W cf, vr_ent B MT e -> s2_P3 e W cf -> SRr SEGS W cf (vr_or (vr_b2 B MT) (vr_b3 B MT) e).
Proof.
intros e W cf HENT HP3.
destruct HP3 as (pos & F & q & lyc & Sc & regs & memc & mdc & k & nm & -> & HJ & Hk1 & HMET & Hnm1 & HST & HSH & HRV
  & HPERM & HLINE & HSV).
pose proof HENT as (_ & _ & _ & _ & _ & _ & _ & Hn & HlenD & _).
pose proof (s2_l_range (e_n e) (e_D e) ltac:(lia)) as Hl.
assert (R10 : getr regs (Z_to_bv 5 10) = w64 (vr_l (e_n e) (e_D e))) by (apply (vr_rv_get regs _ 10 _ HRV); cbn; tauto).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
unfold cfg_at. change (w64 (vr_pc 0x8d608)) with (Z_to_bv 64 (BASE + 28964)).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s2_ss 28964 [])
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 28964)) memc (seg_rom SEGS))))
  by (apply s2_seed; [reflexivity | constructor | exact I]).
set (E := Eimg (Ereg regs [])) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn'; unfold E; apply s2_ew; exact Hn').
clearbody E.
assert (UA : U E (SOff 10 0) = vr_l (e_n e) (e_D e)).
{ unfold U. cbn [sv_denot]. rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), R10. unfold w64.
  rewrite (unsigned_lit_small (vr_l (e_n e) (e_D e))) by lia. rewrite Z.add_0_r. apply unsigned_lit_small. lia. }
assert (UB : U E (SLit 0) = 0) by (vm_compute; reflexivity).
psrr_branch_pi RUNP BR HS.
- (* a0 = 0: the line is empty, and so already trimmed *)
  rewrite branch_eq_U, UA, UB in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_sh RUNTO HS HJ 29080.
  { apply awr_ok_nil. }
  match goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mt ?m0] =>
    set (mdv := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdv end.
  assert (KM : forall a, rdW W (ms_mem ms) a = rdW W memc a).
  { intros a. apply aview_eq_of. apply HFr. intros (r & Hin & _). cbn in Hin. destruct Hin. }
  assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ vr_rl2 e F q)).
  { assert (Hrv0 : vr_rv regs (vr_base B e ++ vr_rl2 e F q)).
    { apply (s2_rv_incl regs _ _ HRV). intros x Hx. unfold vr_base, vr_rl2 in *. cbn [app In] in Hx |- *. tauto. }
    apply (s2_rv_incl (ms_regs ms) ((vr_base B e ++ vr_rl2 e F q) ++ [])); [|intros x Hx; rewrite app_nil_r; exact Hx].
    apply (s2_rv_from regs (ms_regs ms) _ _ Hrv0); [|apply Forall_nil].
    intros r Hr. cbn [map fst vr_base vr_rl2 app] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [match goal with |- getr _ ?rr = _ =>
         let T := fresh "T" in prreg HS rr T; rewrite T; apply EE; reflexivity end |]).
    destruct Hr. }
  pmkst HS. apply SRr_ret. right.
  exists pos, F, q, lyc, Sc, (ms_regs ms), (ms_mem ms), mdv, k, nm.
  split; [reflexivity|].
  split.
  { apply (s2_core e pos F q vr_sh2 (vr_rl2 e F q) lyc Sc W (ms_regs ms) (ms_mem ms) mdv k nm HENT HJ Hk1 HMET Hnm1);
    [| | exact Hrv | exact HPERM].
    - apply (s2_st_keep B RRO PROGU e pos F lyc Sc W memc lyc Sc W (ms_mem ms) HST eq_refl eq_refl (fun pn _ H => H)).
      intros a _. apply KM.
    - intros i Hi. rewrite KM. exact (HSH i Hi). }
  split.
  { destruct HLINE as [Hfresh Hb]. split; [exact Hfresh|].
    rewrite (vr_line_nil (e_D e) (e_n e) (eq_sym HlenD) Hc). split; [|intros []].
    rewrite Hc in Hb. cbn [Z.to_nat firstn app] in Hb |- *. intros i Hi. rewrite KM. exact (Hb i Hi). }
  rewrite (rdword_ext (rdW W memc) (rdW W (ms_mem ms)) (F + 608)); [exact HSV|].
  intros kk _. apply KM.
- (* a0 <> 0: a non-empty line, to be trimmed *)
  rewrite branch_eq_U, UA, UB in Hc. apply Z.eqb_neq in Hc.
  paj_run_to_sh RUNTO HS HJ 28968.
  { apply awr_ok_nil. }
  match goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mt ?m0] =>
    set (mdv := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdv end.
  assert (KM : forall a, rdW W (ms_mem ms) a = rdW W memc a).
  { intros a. apply aview_eq_of. apply HFr. intros (r & Hin & _). cbn in Hin. destruct Hin. }
  assert (Hrv : vr_rv (ms_regs ms) (vr_base B e ++ (10, vr_l (e_n e) (e_D e)) :: vr_rl2 e F q)).
  { apply (s2_rv_incl (ms_regs ms) ((vr_base B e ++ (10, vr_l (e_n e) (e_D e)) :: vr_rl2 e F q) ++ []));
      [|intros x Hx; rewrite app_nil_r; exact Hx].
    apply (s2_rv_from regs (ms_regs ms) _ _ HRV); [|apply Forall_nil].
    intros r Hr. cbn [map fst vr_base vr_rl2 app] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [match goal with |- getr _ ?rr = _ =>
         let T := fresh "T" in prreg HS rr T; rewrite T; apply EE; reflexivity end |]).
    destruct Hr. }
  pmkst HS. apply SRr_ret. left.
  exists pos, F, q, lyc, Sc, (ms_regs ms), (ms_mem ms), mdv, k, nm.
  split; [reflexivity|].
  split; [lia|].
  split.
  { apply (s2_core e pos F q vr_sh2 ((10, vr_l (e_n e) (e_D e)) :: vr_rl2 e F q) lyc Sc W (ms_regs ms) (ms_mem ms) mdv
      k nm HENT HJ Hk1 HMET Hnm1); [| | exact Hrv | exact HPERM].
    - apply (s2_st_keep B RRO PROGU e pos F lyc Sc W memc lyc Sc W (ms_mem ms) HST eq_refl eq_refl (fun pn _ H => H)).
      intros a _. apply KM.
    - intros i Hi. rewrite KM. exact (HSH i Hi). }
  split.
  { apply (s2_line0_agree B e q W memc W (ms_mem ms) HLINE ltac:(lia)). intros kk _. apply KM. }
  rewrite (rdword_ext (rdW W memc) (rdW W (ms_mem ms)) (F + 608)); [exact HSV|].
  intros kk _. apply KM.
Qed.

(* ----------------------------------------------------------------------------------------------------------
   The segment *)
Lemma vr_s02 : vr_s02_stmt B MT.
Proof.
unfold vr_s02_stmt, vr_seg. intros e W cf HENT Hb1.
eapply SRr_bind; [exact (s2_A e W cf HENT Hb1)|]. intros W1 c1 _ HP1.
eapply SRr_bind; [exact (s2_B e W1 c1 HENT HP1)|]. intros W2 c2 _ HP2.
eapply SRr_bind; [exact (s2_C e W2 c2 HENT HP2)|]. intros W3 c3 _ HP3.
exact (s2_D e W3 c3 HENT HP3).
Qed.

End e.
End f.
End d.
