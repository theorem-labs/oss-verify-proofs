(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 321 of its 357 lines of code are new or changed and 376 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (0x8a400), the M6 stage's accepted arm:
   0x8a604 (id in range, g_rec.refuse = 0) to M7 (0x8a628).

   `ld a0,944(s5)` (g_rec.state, s5 = g_rec), `mv a1,s8` (the slot record() filled), `jal mix_call` (0x8ad54, at
   0x8a60c), `sd a0,944(s5)` (the mixed state back into g_rec.state), then the four arguments of the shared
   snprintf: a2 = "resp %d" (0x21d40), a1 = 32, a0 = s4 = buf, a3 = s3 = id. mix_call's contract
   (lib/B/Prog/mix_call_c.v) is afn_pre_na / apost_base: it returns at the SAME FP state, so the call rule is
   PaNoChain.v's cl_callS_na and M7 is taken at the ambient fx. The recorder after the store is
   rec_mix R1 (REC_ADD, A) (sup_add_s7a.v's sab_rep_set_state); the model's accepted arm is sab_m_accepted. The
   donor is the A walk's stage 5, accepted arm (lib/A/Prog/sup_add_s5.v on a working branch 87f17ee4716). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain PaLibF
PaLibG PaLibH PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem sup_add_s7a.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts RecBLemmas RecBridge.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at 0x8a604: the registers are atoms 0..31 and atom 32 is g_rec.state; the field the arm
   loads is a read-only window on s5 = g_rec (atom 21) *)
Definition sabc_rg_state : YP09.region :=
  YP09.mkRegion (Some 21%nat) 944 952 944 944 [YP09.mkChunk 944 (CVal 8 (SOff 32 0))].
Definition sabc_regions : smem := [ sabc_rg_state ].
Definition sabc_facts : facts := mkFacts [] [] [].
Definition ss_sabc : sstate := mkSS (AF_sup_add + 0x204) sr_atoms sabc_regions None sabc_facts.
Definition sabc_extra (st : Z) : list word := [Z_to_bv 64 st].
(* after mix_call (0x8a610): g_rec.state as a writable window with no chunk; the store fills it *)
Definition sabc_rg_store : YP09.region := YP09.mkRegion (Some 21%nat) 944 952 944 952 [].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition sabc_E (regs : bvmap 5 word) (st : Z) : env := Eimg (Ereg regs (sabc_extra st)).

Lemma sabc_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem st,
getr regs 21 = w64 A_G_REC ->
aval_mem (rdW W mem) (A_G_REC + 944) 8 st -> 0 <= st < 2 ^ 64 ->
st_ok_pi SEGS VAL (sabc_E regs st) ss_sabc
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_sup_add + 0x204))) mem (seg_rom SEGS)))
/\ sh_ok SEGS sab_Bx [] (sabc_E regs st) (mrestrict (w_H W) mem).
Proof.
intros W regs mem st H21 Hst Hst0.
set (E := sabc_E regs st).
assert (E21 : ew E 21 = getr regs 21) by (subst E; unfold sabc_E; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 st)
  by (subst E; unfold sabc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (B21 : base_val E (Some 21%nat) = A_G_REC).
{ cbn [base_val]. rewrite E21, H21. unfold w64. rewrite unsigned_lit_small by (unfold A_G_REC; lia). reflexivity. }
split.
- unfold ss_sabc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold sabc_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sabc_regions, sabc_rg_state. constructor; [|constructor].
    unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B21.
    split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC 944 8 (SOff 32 0) st);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem _ 8 st Hst).
  + cbn [pairwise_disjoint all_disjoint sabc_regions]. first [exact I | repeat split].
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
(* the statement's own (sup_add_c.v) *)
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

Lemma sab_arm_accept :
@SA_M7_at fx rc SK PI B MT ->
forall ly S W (regs : bvmap 5 word) mem md ch pu id pp pc uri placement client R O
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc pos,
sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
sa_M6m B MT ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos ->
0 <= id < 10000 ->
r_refuse (rec_record R REC_ADD (sa_A uri id placement client)) = 0 ->
getr regs1 21 = w64 A_G_REC ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF_sup_add + 0x204))) memc (seg_rom SEGS)) mdc)
(sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using HB LAWS SIGP PRW IMG TMIX_CALL VOBJS.
intros HM7 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos
  HCXs HFRM0 HM HIN HREF0 H21.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as (HBa & HBb & HBc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
assert (WS2 : MIX_CALL_STK + 144 <= SUP_ADD_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (WS3 : 0 <= MIX_CALL_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof HCXs as HCX. unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT & HC &
  HCT & HREP & Hev & Hlive & MOK).
pose proof HM as HMs. unfold sa_M6m, sa_core in HM. cbv zeta in HM.
destruct HM as ((HJ & HFRM & HFLG & Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q23 & Q25 & Q26 & Q27) &
  Hs4 & Hs8 & HBUF & O6 & HREP6 & HACCT & HMO6).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (sp0 := spZ regs) in *.
set (s1 := sa_s1 sp0) in *.
set (F := frame_addr lyc 1 pos) in *.
set (A := sa_A uri id placement client) in *.
set (R1 := rec_record R REC_ADD A) in *.
assert (Hs1 : s1 = sp0 - 128 \/ s1 = sp0 - 144) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
assert (Hal1 : (s1 - sp0) mod 16 = 0).
{ destruct Hs1 as [E1 | E1]; rewrite E1;
  [replace (sp0 - 128 - sp0) with (-128) by lia | replace (sp0 - 144 - sp0) with (-144) by lia]; reflexivity. }
pose proof HJ as (HARc & Hlyc & Hsecsc & Hwlec & Hioc & Hfrsc & Hnevc & Hkc & JF1 & JF2 & JF3 & JF4 & JGone & JPres
  & JStk & JF5 & JQT).
assert (HFin : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil. fold F in HF4096, HFceil.
assert (HF8 : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
destruct HACCT as (HA1 & HA2 & HA3 & HA4 & HA5).
destruct (sab_rep_fields B lyc Sc (rdW Wc memc) R1 O6 HREP6) as (_ & _ & Hst & Hstr & _ & HO6b).
(* ---- the seed at 0x8a604 ---- *)
destruct (sabc_seed Wc regs1 memc (r_state R1) H21 Hst Hstr) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (sabc_E regs1 (r_state R1))) by (unfold sabc_E; apply Eimg_env).
remember (sabc_E regs1 (r_state R1)) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr).
{ intros n rr Hn. rewrite HE. unfold sabc_E. apply ew_Eimg_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (r_state R1))
  by (rewrite HE; unfold sabc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
clear HE.
(* 0x8a604 .. 0x8a60c: a0 := g_rec.state, a1 := s8, jal mix_call *)
paj_run_tok RUN HS HJ SHOK sab_Bspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md2 := m) in *; clearbody md2 end.
sab_memeq Wc MEQ1. sab_clear_frames.
pmkst HS.
rename ms into ms2.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10.
prreg HS (11%bv : bv 5) U11.
prreg HS (18%bv : bv 5) U18. prreg HS (19%bv : bv 5) U19. prreg HS (20%bv : bv 5) U20.
prreg HS (21%bv : bv 5) U21. prreg HS (23%bv : bv 5) U23. prreg HS (24%bv : bv 5) U24.
prreg HS (25%bv : bv 5) U25. prreg HS (26%bv : bv 5) U26. prreg HS (27%bv : bv 5) U27.
assert (U2' : getr (ms_regs ms2) 2 = w64 s1) by (rewrite U2, (EEo 2%nat 2%bv eq_refl); exact Q2).
assert (U3' : getr (ms_regs ms2) 3 = w64 (as_gp B)) by (rewrite U3, (EEo 3%nat 3%bv eq_refl); exact Q3).
assert (U4' : getr (ms_regs ms2) 4 = w64 (as_tp B)) by (rewrite U4, (EEo 4%nat 4%bv eq_refl); exact Q4).
assert (U8' : getr (ms_regs ms2) 8 = w64 sp0) by (rewrite U8, (EEo 8%nat 8%bv eq_refl); exact Q8).
assert (U10' : getr (ms_regs ms2) 10 = w64 (r_state R1)) by (rewrite U10, E32; reflexivity).
assert (U11' : getr (ms_regs ms2) 11 = w64 (rec_slot R))
  by (rewrite U11, (EEo 24%nat 24%bv eq_refl); exact Hs8).
assert (HB1 : alloc_ceiling + SUP_ADD_STK <= sp0) by lia.
assert (HB2 : sp0 <= 2 ^ 47) by lia.
assert (HspT2 : spZ (ms_regs ms2) = sp0 + (s1 - sp0))
  by (unfold spZ at 1; rewrite U2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
(* the recorder at the call *)
assert (HREP2' : rec_repA B lyc Sc (rdW Wc (ms_mem ms2)) R1 O6).
{ refine (rec_repA_kept B _ _ _ _ _ _ _ _ HREP6 HA4 _). intros a Ha. apply MEQ1.
  destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia
  | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
  destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hr).
  pose proof (HO6b (p, n) Hpn) as Hbl.
  destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HARc Hbl) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn1).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. lia. }
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms2)))
  by (exact (sab_aro_kept B HB LAWS IMG SUP_ADD_STK sp0 ly S W mem md [(1, pos)] lyc Sc Wc (ms_mem ms2) md2
       (sa_ev6 R) R O HAR0 HJ HREP HROD)).
assert (HRO2 : cmd_ro_ok (rdW Wc (ms_mem ms2)))
  by (exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc (ms_mem ms2) md2 (proj1 HJ) HROD2)).
destruct (rec_bridge_slot B lyc Sc (rdW Wc (ms_mem ms2)) R REC_ADD A O6 HREP2')
  as (HSLOT & _ & _ & Pc & HACALL & HPcO).
assert (HEVle : sa_ev6 R + EV_MIX_CALL <= EV_SUP_ADD R).
{ unfold EV_SUP_ADD, sa_ev6, sa_ev5, sa_ev4, sa_ev2, sa_ev1, EV_MIX_CALL, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC.
  lia. }
assert (HNEVm : st_nev Sc + EV_MIX_CALL <= EV_MAX) by lia.
assert (Hsig : SIG CS_mix_call = BASE + AF_mix_call).
{ rewrite (SIGP CS_mix_call ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
(* 0x8a60c: mix_call(g_rec.state, c) *)
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS) with (STK1 := MIX_CALL_STK) (FP1 := @nil (Z * Z))
    (EV1 := EV_MIX_CALL) (o := s1 - sp0).
  - exact HJ.
  - exact HspT2.
  - exact Hal1.
  - lia.
  - exact WS3.
  - lia.
  - exact U3'.
  - exact U4'.
  - reflexivity.
  - rewrite U1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite U1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HFN. try rewrite Hsig.
    exact (TMIX_CALL fx lyc Sc Wc (ms_regs ms2) (ms_mem ms2) md2 (r_state R1) (rec_slot R) (REC_ADD, A) Pc
      HFN HROD2 U10' Hstr U11' HSLOT HACALL HRO2 HNEVm).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & HQ10 & HQperm & -> & ->).
(* what the call kept: it writes only its own stack window (FP1 = []) *)
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & Fi1 & Fi2 & Fi3 & Fi4 & _).
assert (NOFP : forall a, ~ inFP (@nil (Z * Z)) a) by (intros a (r & Hr & _); destruct Hr).
assert (KEEPc : forall a, sp0 - 104 <= a < sp0 \/ F + 120 <= a < F + 128 ->
  rdW W3 mem3 a = rdW Wc (ms_mem ms2) a).
{ intros a Ha. destruct Ha as [Ha | Ha].
  - apply Fi1; [destruct Hs1 as [Es1|Es1]; lia | destruct Hs1 as [Es1|Es1]; lia | exact (NOFP a)].
  - apply (Fi4 1 pos a HFin); [|exact (NOFP a)].
    left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia. }
assert (KEEPsh : forall i, 0 <= i < 4 -> rdW W3 mem3 (SHADOW_OFF + F / 8 + 8 + i) =
  rdW Wc (ms_mem ms2) (SHADOW_OFF + F / 8 + 8 + i)).
{ intros i Hi. apply (Fi4 1 pos _ HFin); [|exact (NOFP _)].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. fold F. lia. }
assert (KEEPrec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
  rdW W3 mem3 a = rdW Wc (ms_mem ms2) a).
{ intros a Hin.
  assert (HPGa : inFP cmd_PG a).
  { unfold REC_SIZE, SC_SIZE in Hin. destruct Hin as [Hin | Hin].
    - exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; lia].
    - exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
  destruct (CmdRecImg.cmd_prog_unowned SEGS B LAWS HB IMG a HPGa) as (Himg & Hown & Herr).
  apply Fi3; [exact Himg | exact Hown | exact Herr |].
  apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | exact (NOFP a)]. }
assert (KEEPblk : forall p n i, In (p, n) O6 -> 0 <= i < req_size n ->
  rdW W3 mem3 (p + i) = rdW Wc (ms_mem ms2) (p + i)).
{ intros p n i Hpn Hi. pose proof (HO6b (p, n) Hpn) as Hbl.
  apply (Fi2 p n i Hbl Hbl); [lia | exact (NOFP _)]. }
(* the call's frame is no byte of g_rec: a frame byte is not an image byte (AR's client law) *)
assert (HFnotrec : forall a, F <= a < F + 128 -> ~ (A_G_REC + 944 <= a < A_G_REC + 952)).
{ intros a Ha Hin.
  assert (HPG : inFP cmd_PG a)
    by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC in *; lia]).
  destruct (al_client_img _ _ LAWS lyc Sc Wc (ms_mem ms2) md2 a (proj1 HJ)
    ltac:(right; left; exists 1, pos;
          split; [exact HFin | change (fs_frame_bytes 1) with 128; fold F; lia])) as (_ & Hni).
  exact (Hni (cif_prog_img a HPG)). }
(* back at 0x8a610: a fresh state with g_rec.state writable *)
rewrite U1.
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)).
clear HS. rewrite <- restrict_mkst_fx in HS2.
pose proof (img_env_havoc E 40%nat (map (getr regs3) CLOB) HEI ltac:(vm_compute; lia)) as HEIhv.
assert (U21h : bv_unsigned (ew (havoc E 40 (map (getr regs3) CLOB)) 21) = A_G_REC).
{ rewrite ew_havoc_old by (cbv; lia). rewrite (EEo 21%nat (21%bv : bv 5) eq_refl), H21.
  unfold w64. apply unsigned_lit_small. unfold A_G_REC. lia. }
assert (ROK : forall m, region_ok SEGS (havoc E 40 (map (getr regs3) CLOB)) m sabc_rg_store).
{ intros m. unfold region_ok, sabc_rg_store.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U21h. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [|constructor].
  intros o Ho. apply (CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW m (A_G_REC + o)).
  exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC; lia]. }
pose proof (st_ok_pi_add_region _ _ _ sabc_rg_store HS2 eq_refl (ROK _) I) as HS3.
clear HS2 ROK.
assert (AF21 : afact_ok (havoc E 40 (map (getr regs3) CLOB)) 21 (mkAF A_G_REC A_G_REC 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21h, Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_pi_add_fact _ _ _ 21%nat (mkAF A_G_REC A_G_REC 0) HS3 AF21) as HS. clear HS3.
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?s ?m =>
  let s' := eval vm_compute in s in change (st_ok_pi sg vl Ex s' m) in HS end.
assert (SHOK2 : sh_ok SEGS sab_Bx [] (havoc E 40 (map (getr regs3) CLOB)) (mrestrict (w_H W3) mem3))
  by (unfold sh_ok; apply Forall_nil).
(* 0x8a610 .. 0x8a624: sd a0,944(s5); a2 := "resp %d"; a1 := 32; a0 := s4; a3 := s3 *)
paj_run_to_tok RUNTO HS HJo SHOK2 sab_Bspan L_M7.
{ cbn [ss_mem]. eapply awr_ok_cons_gen; [reflexivity | exact U21h | | apply awr_ok_nil].
  intros a Ha. cbn [sabc_rg_store YP09.r_wlo YP09.r_whi] in Ha.
  assert (HPGa : inFP cmd_PG a) by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]).
  unfold awr_byte, awr_prog_or_caller. right; right; right; right; left.
  split; [|split; [exact (sab_prog_static B HB a HPGa) | exact (cif_prog_img a HPGa)]].
  unfold sa_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left. unfold OFF_STATE. lia. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md4 := m) in *; clearbody md4 end.
sab_memeq_st W3 U21h MEQ5. sab_clear_frames.
pmkst HS.
rename ms into ms4.
prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
prreg HS (19%bv : bv 5) T19. prreg HS (23%bv : bv 5) T23. prreg HS (25%bv : bv 5) T25.
prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
prreg HS (13%bv : bv 5) T13. prreg HS (20%bv : bv 5) T20.
repeat (rewrite ew_havoc_old in T2, T3, T4, T8, T9, T18, T19, T23, T25, T26, T27, T13, T20 by (cbv; lia)).
rewrite (EEo 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EEo 3%nat (3%bv : bv 5) eq_refl) in T3.
rewrite (EEo 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EEo 8%nat (8%bv : bv 5) eq_refl) in T8.
rewrite (EEo 9%nat (9%bv : bv 5) eq_refl) in T9. rewrite (EEo 18%nat (18%bv : bv 5) eq_refl) in T18.
rewrite (EEo 19%nat (19%bv : bv 5) eq_refl) in T19. rewrite (EEo 23%nat (23%bv : bv 5) eq_refl) in T23.
rewrite (EEo 25%nat (25%bv : bv 5) eq_refl) in T25. rewrite (EEo 26%nat (26%bv : bv 5) eq_refl) in T26.
rewrite (EEo 27%nat (27%bv : bv 5) eq_refl) in T27.
rewrite (EEo 20%nat (20%bv : bv 5) eq_refl) in T10, T20.
rewrite (EEo 19%nat (19%bv : bv 5) eq_refl) in T13.
(* the stored state, read back from the region *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
  assert (D44 : sv_denot Ex (SOff 44 0) = Z_to_bv 64 (mixcall (r_state R1) (fst (REC_ADD, A)) (snd (REC_ADD, A))))
    by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact HQ10);
  assert (U21x : bv_unsigned (ew Ex 21) = A_G_REC) by exact U21h;
  pose proof (sab_chunk_aval Ex _ msx (w_H W3) 0 _ 0 944 8 (SOff 44 0) _ HS eq_refl eq_refl D44
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply mixcall_range; exact Hstr) ltac:(cbn; lia)) as AST;
  cbn [YP09.r_base base_val] in AST; rewrite U21x in AST
end.
change (N.to_nat 8) with 8%nat in AST.
(* the recorder after the store *)
assert (HREP4 : rec_repA B lyc Sc (rdW W3 (ms_mem ms4)) (rec_mix R1 (REC_ADD, A)) O6).
{ unfold rec_mix. cbn [fst snd].
  apply (sab_rep_set_state B lyc Sc (rdW Wc (ms_mem ms2)) lyc Sc (rdW W3 (ms_mem ms4)) R1 O6 _ HREP2' HA4).
  - intros a Ha Hns. rewrite MEQ5; [| |unfold OFF_STATE in Hns; exact Hns].
    + destruct Ha as [Ha | [Ha | Ha]]; [exact (KEEPrec a (or_introl Ha)) | exact (KEEPrec a (or_intror Ha)) |].
      destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hr).
      pose proof (HO6b (p, n) Hpn) as Hbl.
      replace a with (p + (a - p)) by lia. apply (KEEPblk p n (a - p)); [exact Hpn | lia].
    + destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia
      | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
      destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hr).
      pose proof (HO6b (p, n) Hpn) as Hbl.
      destruct (al_blocks SEGS B LAWS lyc Sc Wc (ms_mem ms2) md2 p n (proj1 HJ) Hbl)
        as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn1).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. lia.
  - unfold OFF_STATE. exact AST.
  - apply mixcall_range. exact Hstr. }
(* M7 at 0x8a628, v = id and the recorder mixed *)
apply (HM7 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc W3 _ _ _ pos HCXs HFRM0).
unfold sa_M7m. cbv zeta. fold F.
split.
{ eapply sab_core_kept; [exact (proj1 HMs) | | reflexivity | |].
  - eapply ajournal_mono_k; [exact HJo | unfold EV_MIX_CALL; lia].
  - intros a Ha. rewrite MEQ5; [| |].
    + rewrite (KEEPc a Ha). apply MEQ1. destruct Ha as [Ha | Ha]; lia.
    + destruct Ha as [Ha | Ha]; lia.
    + destruct Ha as [Ha | Ha]; [unfold A_G_REC; lia | apply (HFnotrec a); lia].
  - rewrite T2, T3, T4, T8, T9, T18, T19, T23, T25, T26, T27.
    repeat (split; [reflexivity|]). reflexivity. }
split; [rewrite T10; exact Hs4|].
split; [rewrite T11; reflexivity|].
split.
{ cbn [map CLOB nth] in T12. rewrite T12.
  lazymatch goal with |- ew ?Ev _ = _ =>
    lazymatch goal with HX : img_env _ _ Ev |- _ =>
      pose proof (HX 288%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H288 end end.
  change (VAL 288%nat) with (VAL (A_OBJ 47)) in H288.
  rewrite (VOBJS 47%nat ltac:(vm_compute; lia)) in H288.
  apply bv_eq. rewrite H288. unfold w64, SA_FMT_RESP. rewrite unsigned_lit_small by lia.
  vm_compute. reflexivity. }
split; [rewrite T20; exact Hs4|].
split.
{ intros i Hi. rewrite MEQ5 by (try unfold SHADOW_OFF; try unfold A_G_REC; lia).
  rewrite (KEEPsh i Hi). rewrite MEQ1 by (unfold SHADOW_OFF; lia). exact (HBUF i Hi). }
exists id, (rec_mix R1 (REC_ADD, A)), O6.
split.
{ unfold sa_arm. cbv zeta. right. split; [reflexivity|]. split; [exact HIN|].
  split; [exact HREF0 | reflexivity]. }
split; [rewrite T13; exact (eq_trans Q19 H11)|].
split; [exact HREP4|].
split; [repeat (split; [assumption|]); assumption | exact HMO6].
Qed.
End e.
End f.
End d.
