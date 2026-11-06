(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of descriptors_get on plugin-hostd/fuzz_command.asan-ubsan, the B
   re-walk of lib/A/Prog/descriptors_get.v (a working branch 565c61eeead, dg_entry_holds o dg_walkJ) at B's
   addresses: B calls record() and arg_s() where A inlines them, so the two arms and the four inline ASan checks of
   A's walk become two callee contracts and this file is one straight walk. *)

(* descriptors_get on fuzz_command.asan-ubsan (MEASURED with capstone over the pin's .symtab, sha256 658cefbe...):
   entry 0x8cca4, 88 bytes, 22 instructions, a 32-byte frame (ra, s0, s1), no branch, NO `jal __asan_report_*` and
   NO UBSan trap site, so this walk has no report edge of its own; A's four report edges are inside record()
   (0x8a80c, 0x8a81c) and arg_s() (0x8a948, 0x8a95c, 0x8a970, 0x8a974) on B, refuted by their own contracts.

   The walk: the entry seed (one region, the 32-byte frame), then
     0x8cca4 .. 0x8ccbc  prologue, a0 := 23, call record    (trecord_spec, cl_callS_wide)
     0x8ccc0 .. 0x8ccc8  s1 := the slot, a1 := uri, call arg_s   (targ_s_spec, cl_callS_wide)
     0x8cccc .. 0x8ccd8  a0 := the verb 0x21fa0, a1 := 14, call rec_shape_of  (trec_shape_of_spec, cl_callS_na)
     0x8ccdc .. 0x8ccf8  a1 := the shape, a0 := the slot, a2 := 0, frame released, `j answer`
                         (tanswer_spec, PaFx's callS_wideF: answer's post is FP-existential).
   The statement is a Theorem Labs lane's lib/B/Prog/descriptors_get_c.v at a working branch f490061c104, over core
   a working branch c022a2f6a88; the helpers are lib/B/Prog/descriptors_get_aux.v; callS_wideF is lib/B/Prog/PaFx.v's.
   The frame chains at the calls: record's and arg_s's s0 is uri, a heap address below alloc_ceiling (achain_low);
   rec_shape_of asks none; answer runs with the caller's s0 and the entry's chain, kept (achain_kept). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal PaCall PaCallRun PaDenot PaNoChain PaLibF PaLibG PaLibH PaSB CmdSyms
CmdList CmdAddr CmdPa CmdPaLib CmdBase CmdRep CmdObj CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c rec_shape_of_c answer_c descriptors_get_c descriptors_get_aux PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c hand_back_c mix_call_c rec_calls_free_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition dgb_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition dgb_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition dgb_SH : list shent := [].
Definition dgb_Bx : sv := SOff (A_OBJ 12) 0.
Definition dgb_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ss_dgb0 : sstate := mkSS AF_descriptors_get sr_atoms [dgb_stk] None dgb_facts.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma dgb_shok : forall E m, sh_ok SEGS dgb_Bx dgb_SH E m.
Proof. intros E m. constructor. Qed.

Lemma dgb_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md B,
AR SEGS B ly S W mem md ->
astk_ok DESCRIPTORS_GET_STK ly (spZ regs) ->
(forall a, spZ regs - DESCRIPTORS_GET_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_dgb0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_descriptors_get)) mem (seg_rom SEGS))).
Proof.
intros W regs mem ly S md B HAR Hstk Hpres.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : DESCRIPTORS_GET_STK = 16592) by (vm_compute; reflexivity).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])) in *.
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold ss_dgb0. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dgb_stk;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HTS. lia.
- apply pairwise_disjoint_of_extents. unfold dgb_stk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f_atoms dgb_facts atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. split; [|exact I].
  split; [lia|]. split; [|lia]. change (2 ^ 4) with 16. exact Hsp0al.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
(* the one pinned record fact the walk carries, under a Theorem Labs lane's own name (lib/B/Prog/CmdRecImg.v's
   cmd_img_facts_tfib at the concrete image): the lane's closing file discharges it by `exact cmd_img_facts_tfib` *)
Hypothesis cmd_img_facts_tfib : forall B0 : asyms, CmdBSyms B0 -> cmd_img_facts SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
(* a Theorem Labs lane's record facts at this walk's hypotheses (lib/B/Prog/CmdRecImg.v, CmdRecRo.v) *)
Let IMG : cmd_img_facts SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img := cif_prog_img SEGS B IMG.
Let cmd_heap_tail_vis := CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let CMD_RO_IN := CmdRecRo.CMD_RO_IN SEGS B LAWS HB IMG.
Let RELRO_IMG := CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG.
Let RRO : ro_below_ofl SEGS CMD_RLO CMD_RHI := CmdRecRo.ROB SEGS B LAWS HB IMG.
Let RPG := CmdRecRo.RPG SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro := CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Lemma dgb_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hgot)].
Qed.
Lemma dgb_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ inFP cmd_PG a.
Proof. intros a Hro. split; [exact (dgb_ro_img a Hro) | intros Hpg; exact (RPG a Hpg Hro)]. Qed.

Theorem tdescriptors_get_holds : tdescriptors_get_spec B MT.
Proof.
unfold tdescriptors_get_spec.
intros ly S W regs mem md ch pu uri R O HPRE Hfrm HROD HRO H10 Hpu HSTR HREP HFR8 HEV HLV HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (WS : DESCRIPTORS_GET_STK = 16592) by (vm_compute; reflexivity).
assert (WSA : ANSWER_STK = 16592) by (vm_compute; reflexivity).
pose proof (dgb_seed W regs mem ly S md B HAR Hstk Hpres) as HS.
pose proof (dgb_shok (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) as SHOK.
set (FP0 := (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O).
pose proof (ajournal_init SEGS B DESCRIPTORS_GET_STK FP0 ly S W regs mem md ch HPRE) as HJ.
set (E := Eimg (Ereg regs [])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2u : bv_unsigned (ew E 2) = spZ regs)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK dgb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2u | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
prreg HS (10%bv : bv 5) P10.
prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
(* the facts the walk needs at the record call *)
assert (HOB : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hpn; destruct HREP as (Q & HAQ & HOQ); exact (dgb_lay_blocks_in _ _ _ _ _ _ HAQ pn (proj1 (HOQ pn) Hpn))).
assert (Psp : spZ (ms_regs ms) = spZ regs + -32)
by (unfold spZ at 1; rewrite P2, E2u, unsigned_lit_small by lia; reflexivity).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 REC_DESCRIPTORS_GET) by (rewrite P10; reflexivity).
assert (Ppu : getr (ms_regs ms) 8 = w64 pu) by (rewrite P8, (EEo 10%nat 10%bv eq_refl); exact H10).
(* what the prologue changed: only the frame *)
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H1.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr).
  - intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E2u in Hrr; lia|]).
    destruct Hin.
  - exact Ha.
  - exact H1. }
assert (NFP0h : forall a, alloc_ceiling <= a -> ~ inFP FP0 a).
{ intros a Ha (r & Hr & Hin). unfold FP0 in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hin.
  - unfold A_G_REC, REC_SIZE in *. lia.
  - unfold A_REC_SPILL, SC_SIZE in *. lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOB (p, n) Hb)) as (_ & _ & Hc & _). lia. }
assert (ROFP0 : forall a, in_roP SEGS RLO RHI a -> ~ inFP FP0 a).
{ intros a Hro (r & Hr & Ha). destruct (dgb_ro_prog_apart a Hro) as (Himg & Hpg).
  unfold FP0 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
  - exact (Hpg (dgb_grec_in a Ha)).
  - exact (Hpg (dgb_spill_in a Ha)).
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Ha.
    exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HOB (p, n) Hb) Ha Himg). }
assert (HRODJ : forall ly' S' (W' : world SEGS) mem' md' k,
  ajournal SEGS B DESCRIPTORS_GET_STK (spZ regs) FP0 ly S W mem md [] ly' S' W' mem' md' k ->
  arodata_okP SEGS RLO RHI B (rdW W' mem')).
{ intros ly' S' W' mem' md' k HJx.
  exact (arodata_ok_journalP (RO := RRO) SEGS RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ k HJx ROFP0 HROD). }
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ intros a Hro Ho He. destruct (dgb_ro_prog_apart a Hro) as (Himg & Hpg).
  pose proof (pa_img_range a Himg) as Hr.
  rewrite UN; [exact (HROD a Hro Ho He) | lia | lia]. }
assert (HREP1 : rec_repA B ly S (rdW W (ms_mem ms)) R O).
{ destruct HREP as (Q & HAQ & HOQ). exists Q. split; [|exact HOQ].
  apply (dgb_arep_kept _ (rdW W mem)); [exact HAQ | | |].
  - intros a Ha. apply UN; unfold A_G_REC, REC_SIZE in *; lia.
  - intros a Ha. apply UN; unfold A_REC_SPILL, SC_SIZE in *; lia.
  - intros p n i Hin Hi.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. apply UN; lia. }
assert (HCH : achain ly (rdW W (ms_mem ms)) (spZ regs + -32) (s0Z (ms_regs ms)) []).
{ apply achain_low. unfold s0Z. rewrite Ppu.
  destruct HSTR as (x & -> & (qb & kb & Hqb & Hq1 & Hq2) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ qb kb HAR Hqb) as (_ & _ & Hc & _).
  pose proof (req_size_pos kb) as Hrq. rewrite unsigned_lit_small by lia. lia. }
(* the record call's footprint: g_rec.ncalls, the slot's fn/nargs word, and the spill arm's freed blocks *)
set (FP1 := (A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
  (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)).
assert (Hslot : (A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/
  rec_slot R = A_REC_SPILL).
{ unfold rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Hlt; [|right; reflexivity].
  apply Nat.ltb_lt in Hlt. left. pose proof (Nat2Z.is_nonneg (length (r_calls R))).
  assert (Z.of_nat (length (r_calls R)) <= 15) by lia.
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER. lia. }
assert (NFP1s : forall a, alloc_ceiling <= a -> ~ inFP FP1 a).
{ intros a Ha (r & Hr & Hin). unfold FP1 in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hin.
  - unfold A_G_REC, OFF_NCALLS in *. lia.
  - destruct Hslot as [[H1 H2] | He]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, OFF_ANSWER in *; lia|].
    rewrite He in Hin. unfold A_REC_SPILL in *. lia.
  - destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HOB (p, n) Hb)) as (_ & _ & Hc & _). lia. }
assert (HEVB : st_nev S + EV_RECORD R <= EV_MAX).
{ unfold EV_DESCRIPTORS_GET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in HEV. lia. }
assert (XMrec : 0 <= XM_RECORD MT R).
{ unfold XM_RECORD, rec_spill_frees. pose proof (mo_free_nonneg MT MTL).
  destruct (Nat.ltb (length (r_calls R)) 16); [lia|].
  pose proof (Nat2Z.is_nonneg (length (snd (r_spill R)))). nia. }
assert (XMarg : 0 <= XM_ARG_S MT uri).
{ unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC.
  apply (mo_malloc_nonneg MT MTL). lia. }
assert (XMans : 0 <= XM_ANSWER MT (snd (descriptors_get_m R uri))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC.
  pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL
    (Z.max (Z.of_nat (length (snd (descriptors_get_m R uri))) + 1) 1) ltac:(lia)). lia. }
assert (XMA : 0 <= XM_ARG_S MT uri + XM_ANSWER MT (snd (descriptors_get_m R uri))) by lia.
assert (HMOKB : mo_ok MT S (XM_RECORD MT R)).
{ apply (mok_station MT S S (XM_DESCRIPTORS_GET MT R uri) 0 (XM_RECORD MT R) MTL HMOK (mle_start MT S MTL));
  [lia | unfold XM_DESCRIPTORS_GET; lia]. }
eapply SRr_bind;
[ eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ DESCRIPTORS_GET_STK (spZ regs) FP0 ly S W mem md []
    ly S _ 0 RECORD_STK FP1 (EV_RECORD R) (-32) (Z_to_bv 64 (BASE + 26512)) [] _ HJ Psp);
  [ reflexivity | lia | unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK; lia
  | rewrite WS; unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK; lia
  | exact P3' | exact P4' | exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite unsigned_lit_small by lia; lia
  | exact HCH
  | intros HPRE1; rewrite (rca_sig_record cmd_sig_prog_PB); eapply SRr_mono;
    [ exact (TRECORD fx ly S W (ms_regs ms) (ms_mem ms) _ [] REC_DESCRIPTORS_GET R O
        HPRE1 HROD1 P10' ltac:(unfold REC_DESCRIPTORS_GET, REC_FN_COUNT; lia) HREP1 HEVB HMOKB)
    | cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
      exists ly3, S3, regs3, mem3, md3;
      split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
  | intros aa Hf
  | intros ly2 S2 W2 regs2 mem2 md2 HK aa Hf Hst Hn; exfalso; exact (NFP1s aa ltac:(lia) Hf) ]
| ].
{ destruct Hf as (r & Hr & Ha). unfold FP1 in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
  - right; right; right; right. left.
    split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS, REC_SIZE in *; lia]|].
    split; [rewrite (ts_prog B HB); apply dgb_static_grec; unfold OFF_NCALLS, REC_SIZE in *; lia
          | apply cmd_prog_img; apply dgb_grec_in; unfold OFF_NCALLS, REC_SIZE in *; lia].
  - right; right; right; right. left. destruct Hslot as [[H1 H2] | He].
    + split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold CALL_SIZE, OFF_CALLS, OFF_ANSWER, REC_SIZE in *; lia]|].
      split; [rewrite (ts_prog B HB); apply dgb_static_grec; unfold CALL_SIZE, OFF_CALLS, OFF_ANSWER, REC_SIZE in *; lia
            | apply cmd_prog_img; apply dgb_grec_in; unfold CALL_SIZE, OFF_CALLS, OFF_ANSWER, REC_SIZE in *; lia].
    + rewrite He in Ha.
      split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE; lia]|].
      split; [rewrite (ts_prog B HB); apply dgb_static_spill; unfold SC_SIZE; lia
            | apply cmd_prog_img; apply dgb_spill_in; unfold SC_SIZE; lia].
  - destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|].
    right; left. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Ha.
    split.
    + exists (p, p + req_size n). split;
      [right; right; unfold ablocks_fp; apply in_map_iff; exists (p, n); split; [reflexivity | exact Hb]
      | cbn [fst snd]; exact Ha].
    + exists p, n. split; [exact (HOB (p, n) Hb) | exact Ha]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
destruct HK2 as (F & O1 & Ha02 & HPerm2 & HlenF & HFO & HREP2 & HO1 & HBB2 & HMLE2).
destruct HREP2 as (Qb & HAQ2 & HOQ2).
destruct (dgb_old _ _ _ _ _ _ HAQ2) as (old & HoldE & Hold').
pose proof (proj1 HJ2) as HAR2.
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub SEGS B); [exact HJc2 | exact HJ2 | exact E2u | lia | rewrite WS; lia | lia
  | cbn [YP09.r_lo YP09.r_wlo]; lia | cbn [YP09.r_hi YP09.r_whi]; lia
  | intros a Ha; apply NFP1s; cbn [YP09.r_lo YP09.r_hi] in Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 32)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (E2u2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact E2u).
pose proof (dgb_shok E2 (mrestrict (w_H W2) mem2)) as SHOK2.
(* 0x8ccc0 .. 0x8ccc8: s1 := the slot, a1 := uri, and the call of arg_s *)
paj_run_tok RUN HS HJ2 SHOK2 dgb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2u2 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
(* the run after the call writes only the frame *)
assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  rdW W2 (ms_mem ms0) a = rdW W2 mem2 a).
{ intros a Ha H1.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr0).
  - intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E2u2 in Hrr; lia|]).
    destruct Hin.
  - exact Ha.
  - exact H1. }
assert (A36 : ew E2 36 = getr regs2 10) by (rewrite HE2; reflexivity).
assert (Q10' : getr (ms_regs ms0) 10 = w64 (rec_slot R)) by (rewrite Q10, A36; exact Ha02).
assert (Q11' : getr (ms_regs ms0) 11 = w64 pu)
by (rewrite Q11, OLD2 by lia; rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (Q3' : getr (ms_regs ms0) 3 = w64 (as_gp B))
by (rewrite Q3, OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (Q4' : getr (ms_regs ms0) 4 = w64 (as_tp B))
by (rewrite Q4, OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (Qsp : spZ (ms_regs ms0) = spZ regs + -32)
by (unfold spZ at 1; rewrite Q2, OLD2, E2u by lia; rewrite unsigned_lit_small by lia; reflexivity).
pose proof (proj1 HJ2) as HAR2b.
(* the arg_s call at 0x8ccc8: the slot in a0, uri in a1 *)
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms0)))
by exact (HRODJ ly2 S2 W2 (ms_mem ms0) _ _ HJ2).
assert (HRO2 : cmd_ro_ok (rdW W2 (ms_mem ms0)))
by exact (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem ms0) _ (proj1 HJ2) HROD2).
(* the heap block of uri is none of the recorder's, so record() did not free it, and its bytes are kept *)
destruct HSTR as (x & Huri & HXB & HXS & HXL & HXO).
destruct HXB as (qb & kb & Hqb & Hqb1 & Hqb2).
assert (HqbO : ~ In (qb, kb) O).
{ intros HO. rewrite Forall_forall in HXO. specialize (HXO (qb, kb) HO).
  unfold iv_apart in HXO. cbn [fst snd] in HXO. lia. }
assert (HqbF : ~ In (qb, kb) F) by (intros HFb; exact (HqbO (HFO (qb, kb) HFb))).
assert (Hqb2' : In (qb, kb) (ablocks B ly2 S2)).
{ destruct (in_app_or _ _ _ (Permutation_in _ HPerm2 Hqb)) as [H | H]; [exact H | exfalso; exact (HqbF H)]. }
assert (Hkbpos : 0 <= kb /\ 4096 <= qb /\ qb + req_size kb <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ qb kb HAR Hqb) as (_ & H4 & Hc & _ & _ & _ & Hn). lia. }
assert (NBLK : forall a, qb <= a < qb + req_size kb -> ~ inFP FP1 a).
{ intros a Ha (r & Hr & Hin). unfold FP1 in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hin.
  - exact (blk_img SEGS B LAWS ly S W mem md qb kb a HAR Hqb Ha
      (cmd_prog_img a (dgb_grec_in a ltac:(unfold OFF_NCALLS, REC_SIZE in *; lia)))).
  - destruct Hslot as [[H1 H2] | He].
    + exact (blk_img SEGS B LAWS ly S W mem md qb kb a HAR Hqb Ha
        (cmd_prog_img a (dgb_grec_in a ltac:(unfold OFF_CALLS, CALL_SIZE, REC_SIZE, OFF_ANSWER in *; lia)))).
    + rewrite He in Hin. exact (blk_img SEGS B LAWS ly S W mem md qb kb a HAR Hqb Ha
        (cmd_prog_img a (dgb_spill_in a ltac:(unfold SC_SIZE in *; lia)))).
  - destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hin.
    assert (Hne : (p, n) <> (qb, kb)) by (intros He; rewrite He in Hb; exact (HqbO Hb)).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md p n qb kb HAR (HOB (p, n) Hb) Hqb Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HKB2 : forall i, 0 <= i < req_size kb -> rdW W2 (ms_mem ms0) (qb + i) = rdW W (ms_mem ms) (qb + i)).
{ intros i Hi.
  assert (Hnoimg : ~ in_img SEGS (qb + i))
  by (intros Him; exact (blk_img SEGS B LAWS ly S W mem md qb kb (qb + i) HAR Hqb ltac:(lia) Him)).
  rewrite (UN2 (qb + i) ltac:(lia) ltac:(lia)).
  pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
  exact (K2 qb kb i Hqb Hqb2' Hi (NBLK (qb + i) ltac:(lia))). }
assert (HKBfull : forall a, qb <= a < qb + req_size kb -> rdW W2 (ms_mem ms0) a = rdW W mem a).
{ intros a Ha. replace a with (qb + (a - qb)) by lia. rewrite (HKB2 (a - qb) ltac:(lia)).
  apply UN; lia. }
assert (Hrq : req_size kb >= kb /\ 0 < req_size kb)
by (pose proof (req_size_pos kb ltac:(lia)) as Hz; lia).
assert (HXS2 : astr_atR (rdW W2 (ms_mem ms0)) pu x).
{ apply (dgb_rastr_kept (rdW W mem)); [exact HXS|]. intros i Hi. apply HKBfull. lia. }
assert (HAR2c : AR SEGS B ly2 S2 W2 (ms_mem ms0) (with_vm_backing (m_vm_lazy md2) mat0 md2)) by exact (proj1 HJ2).
assert (HREP3 : rec_repA B ly2 S2 (rdW W2 (ms_mem ms0)) (rec_record R REC_DESCRIPTORS_GET []) O1).
{ exists Qb. split; [|exact HOQ2].
  apply (dgb_arep_kept _ (rdW W2 mem2)); [exact HAQ2 | | |].
  - intros a Ha. apply UN2; unfold A_G_REC, REC_SIZE in *; lia.
  - intros a Ha. apply UN2; unfold A_REC_SPILL, SC_SIZE in *; lia.
  - intros p n i Hin Hi.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2c Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)). apply UN2; lia. }
assert (HARGA : astr_argA B ly2 S2 (rdW W2 (ms_mem ms0)) (in_roP SEGS RLO RHI) [] pu uri).
{ rewrite Huri. unfold astr_argA. cbv beta iota zeta.
  split; [lia|]. split; [exact HXS2|]. split; [exact HXL|].
  left. split; [exists qb, kb; split; [exact Hqb2' | lia] | constructor]. }
assert (HTAIL : forall y, uri = Some y -> atail_vis SEGS W2 (ms_mem ms0) (pu + Z.of_nat (length y))).
{ intros y Hy. rewrite Huri in Hy. injection Hy as <-.
  exact (cmd_heap_tail_vis ly2 S2 W2 (ms_mem ms0) _ qb kb (pu + Z.of_nat (length x)) HAR2c Hqb2' ltac:(lia)). }
pose proof HJ2 as (_ & _ & _ & _ & _ & HfrS2 & HnevS2 & _).
assert (HEVa : st_nev S2 + EV_ARG_S <= EV_MAX).
{ unfold EV_DESCRIPTORS_GET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia. }
assert (HLVa : blocks_bytes S2 + LIVE_ARG_S uri <= LIVE_MAX).
{ unfold LIVE_DESCRIPTORS_GET, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC in *.
  pose proof (Nat2Z.is_nonneg (length (snd (descriptors_get_m R uri)))). lia. }
assert (HMOKa : mo_ok MT S2 (XM_ARG_S MT uri)).
{ apply (mok_station MT S S2 (XM_DESCRIPTORS_GET MT R uri) (XM_RECORD MT R) (XM_ARG_S MT uri) MTL HMOK HMLE2);
  [lia | unfold XM_DESCRIPTORS_GET; lia]. }
set (FP2 := if Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX
  then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
        (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
         rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)]
  else []).
assert (FP2eq : FP2 = [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
                       (rec_slot R + CALL_OFF_ARGS, rec_slot R + CALL_OFF_ARGS + 8)])
by (unfold FP2, REC_ARGS_MAX; cbn [length]; change (Z.of_nat 0) with 0; change (0 <? 6) with true;
    cbv iota; rewrite !Z.mul_0_r, !Z.add_0_r; reflexivity).
assert (NFP2s : forall a, alloc_ceiling <= a -> ~ inFP FP2 a).
{ intros a Ha (r & Hr & Hin). rewrite FP2eq in Hr. cbn [In] in Hr.
  destruct Hslot as [[H1 H2] | He];
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hin;
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, OFF_ANSWER in *;
  try (rewrite He in Hin; unfold A_REC_SPILL in *); lia. }
assert (AWR2 : forall a, inFP FP2 a -> Exists (in_zr a) TFIB_PROG_STATIC /\ in_img SEGS a /\
  inFP FP0 a).
{ intros a (r & Hr & Hin). rewrite FP2eq in Hr. cbn [In] in Hr.
  destruct Hslot as [[H1 H2] | He].
  - assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE)
    by (destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hin;
        unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, OFF_CALLS, OFF_ANSWER, REC_SIZE in *; lia).
    split; [exact (dgb_static_grec a Hg)|]. split; [exact (cmd_prog_img a (dgb_grec_in a Hg))|].
    exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
  - assert (Hg : A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE)
    by (destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hin; rewrite He in Hin;
        unfold CALL_OFF_NARGS, CALL_OFF_ARGS, SC_SIZE in *; lia).
    split; [exact (dgb_static_spill a Hg)|]. split; [exact (cmd_prog_img a (dgb_spill_in a Hg))|].
    exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
eapply SRr_bind;
[ eapply (cl_callS_wide B LAWS W2 (ms_regs ms0) (ms_mem ms0) _ DESCRIPTORS_GET_STK (spZ regs) FP0 ly S W mem md []
    ly2 S2 _ (0 + EV_RECORD R) ARG_S_STK FP2 EV_ARG_S (-32) (Z_to_bv 64 (BASE + 26524)) [] _ HJ2 Qsp);
  [ reflexivity | lia | unfold ARG_S_STK, XMALLOC_STK, ASTACK, ESTACK; lia
  | rewrite WS; unfold ARG_S_STK, XMALLOC_STK, ASTACK, ESTACK; lia
  | exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite unsigned_lit_small by lia; lia
  | apply achain_low; unfold s0Z; rewrite Q8, OLD2 by lia; rewrite (EEo 10%nat 10%bv eq_refl), H10;
    rewrite unsigned_lit_small by lia; lia
  | intros HPRE2; rewrite (dgb_sig_arg_s cmd_sig_prog_PB); eapply SRr_mono;
    [ exact (TARG_S fx ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ [] (rec_slot R) pu REC_DESCRIPTORS_GET [] uri R O1
        HPRE2 HROD2 HRO2 Q10' Q11' eq_refl HREP3 (or_introl HARGA) HTAIL HEVa HLVa HMOKa)
    | cbv beta; unfold apost_base; intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HK4);
      exists ly4, S4, regs4, mem4, md4;
      split; [rewrite Q1; reflexivity | split; [exact HJ4 | split; [exact HP4 | exact HK4]]] ]
  | intros aa Hf; destruct (AWR2 aa Hf) as (Hpg & Himg & Hfp0);
    right; right; right; right; left; split; [exact Hfp0|];
    split; [rewrite (ts_prog B HB); exact Hpg | exact Himg]
  | intros ly4 S4 W4 regs4 mem4 md4 HK aa Hf Hst Hn; exfalso; exact (NFP2s aa ltac:(lia) Hf) ]
| ].
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (HBB3 & HMLE3 & [ (Hbad & _) | (_ & p & Hp4096 & HPerm3 & HFresh3 & HREP4) ]);
[exfalso; cbn [length Z.of_nat] in Hbad; unfold REC_ARGS_MAX in Hbad; discriminate|].
pose proof (proj1 HJ3) as HAR3.
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact E2u2 | lia | rewrite WS; lia | lia
  | cbn [YP09.r_lo YP09.r_wlo]; lia | cbn [YP09.r_hi YP09.r_whi]; lia
  | intros a Ha; apply NFP2s; cbn [YP09.r_lo YP09.r_hi] in Ha; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E2 48 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (E2u3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact E2u2).
pose proof (dgb_shok E3 (mrestrict (w_H W3) mem3)) as SHOK3.
(* 0x8cccc .. 0x8ccd8: a0 := the verb 0x21fa0, a1 := 14, and the call of rec_shape_of *)
paj_run_tok RUN HS HJ3 SHOK3 dgb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2u3 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
assert (HAR3c : AR SEGS B ly3 S3 W3 (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat1 md3)) by exact (proj1 HJ3).
assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  rdW W3 (ms_mem ms1) a = rdW W3 mem3 a).
{ intros a Ha H1.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr1).
  - intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E2u3 in Hrr; lia|]).
    destruct Hin.
  - exact Ha.
  - exact H1. }
assert (T10' : getr (ms_regs ms1) 10 = w64 0x21fa0).
{ rewrite T10, <- (Z_to_bv_bv_unsigned 64 (ew E3 328)), (HEI3 328%nat ltac:(cbv; lia)), <- dgb_verb_atom,
    (dgb_verb_val VOBJS). reflexivity. }
assert (T11' : getr (ms_regs ms1) 11 = w64 (Z.of_nat (length dgb_verb))) by (rewrite T11; reflexivity).
assert (T3' : getr (ms_regs ms1) 3 = w64 (as_gp B))
by (rewrite T3, OLD3, OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (T4' : getr (ms_regs ms1) 4 = w64 (as_tp B))
by (rewrite T4, OLD3, OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (Tsp : spZ (ms_regs ms1) = spZ regs + -32)
by (unfold spZ at 1; rewrite T2, OLD3, OLD2, E2u by lia; rewrite unsigned_lit_small by lia; reflexivity).
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms1)))
by exact (HRODJ ly3 S3 W3 (ms_mem ms1) _ _ HJ3).
assert (HRO3 : cmd_ro_ok (rdW W3 (ms_mem ms1)))
by exact (cmd_ro_ok_of_aro ly3 S3 W3 (ms_mem ms1) _ HAR3c HROD3).
pose proof HJ3 as (_ & _ & _ & _ & _ & HfrS3 & HnevS3 & _).
assert (HEVs : st_nev S3 + EV_REC_SHAPE_OF <= EV_MAX).
{ unfold EV_REC_SHAPE_OF, EV_DESCRIPTORS_GET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia. }
eapply SRr_bind;
[ eapply (cl_callS_na B LAWS W3 (ms_regs ms1) (ms_mem ms1) _ DESCRIPTORS_GET_STK (spZ regs) FP0 ly S W mem md []
    ly3 S3 _ (0 + EV_RECORD R + EV_ARG_S) REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-32)
    (Z_to_bv 64 (BASE + 26540)) _ HJ3 Tsp);
  [ reflexivity | lia | unfold REC_SHAPE_OF_STK, ESTACK; lia
  | rewrite WS; unfold REC_SHAPE_OF_STK, ESTACK; lia
  | exact T3' | exact T4' | exact T1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite unsigned_lit_small by lia; lia
  | intros HPRE3; rewrite (dgb_sig_rec_shape_of cmd_sig_prog_PB); eapply SRr_mono;
    [ exact (TREC_SHAPE_OF fx ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ 0x21fa0 dgb_verb
        HPRE3 HROD3 T10' ltac:(lia) T11' ltac:(vm_compute; reflexivity) HRO3 VOBJS
        (proj2 (dgb_verb_pre B HB ly3 S3 (rdW W3 (ms_mem ms1)) HRO3 CMD_RO_IN)) HEVs)
    | cbv beta; unfold apost_base; intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HK5);
      exists ly5, S5, regs5, mem5, md5;
      split; [rewrite T1; reflexivity | split; [exact HJ5 | split; [exact HP5 | exact HK5]]] ]
  | intros aa (r & Hr & _); destruct Hr ]
| ].
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HK4).
destruct HK4 as ((q & Hq10 & Hq64 & HqA) & HPerm4 & Hly4 & HS4eq).
pose proof (proj1 HJ4) as HAR4.
jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  eapply (region_kept_stack_sub SEGS B); [exact HJc4 | exact HJ4 | exact E2u3 | lia | rewrite WS; lia | lia
  | cbn [YP09.r_lo YP09.r_wlo]; lia | cbn [YP09.r_hi YP09.r_whi]; lia
  | intros a Ha (r & Hr & _); destruct Hr ]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 64 (map (getr regs4) CLOB)) as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLDd : forall n, (n < 64)%nat -> ew Ed n = ew E3 n) by (intros n Hn; rewrite HEd; apply YN3v.ew_havoc_old; exact Hn).
assert (E2ud : bv_unsigned (ew Ed 2) = spZ regs) by (rewrite OLDd by lia; exact E2u3).
pose proof (dgb_shok Ed (mrestrict (w_H W4) mem4)) as SHOKd.
(* 0x8ccdc .. 0x8ccf8: a1 := the shape, a0 := the slot, a2 := 0, the frame released, and the tail jump *)
paj_run_tok RUN HS HJ4 SHOKd dgb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2ud | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11.
prreg HS (12%bv : bv 5) U12.
(* the final run writes nothing: the epilogue only loads *)
assert (UNd : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  rdW W4 (ms_mem ms2) a = rdW W4 mem4 a).
{ intros a Ha H1.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr2).
  - intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E2ud in Hrr; lia|]).
    destruct Hin.
  - exact Ha.
  - exact H1. }
subst ly4. subst S4.
assert (HAR4c : AR SEGS B ly3 S3 W4 (ms_mem ms2) (with_vm_backing (m_vm_lazy md4) mat2 md4)) by exact (proj1 HJ4).
set (n := Z.of_nat (length (sarg uri)) + 1) in *.
set (RT := rec_record R REC_DESCRIPTORS_GET [sarg uri]).
set (O2 := (p, n) :: O1).
(* what the rec_shape_of call (empty footprint) and the two runs around it kept *)
assert (KEEPT : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  rdW W4 (ms_mem ms2) a = rdW W3 mem3 a).
{ intros a Ha.
  assert (HP : Exists (in_zr a) TFIB_PROG_STATIC)
  by (destruct Ha as [H|H]; [exact (dgb_static_grec a H) | exact (dgb_static_spill a H)]).
  assert (HPg : inFP cmd_PG a)
  by (destruct Ha as [H|H]; [exact (dgb_grec_in a H) | exact (dgb_spill_in a H)]).
  destruct (prog_static_sep B a (ts_ok B HB) ltac:(rewrite (ts_prog B HB); exact HP)) as (Ho & He & _).
  pose proof (cmd_prog_img a HPg) as Himg. pose proof (pa_img_range a Himg) as Hr.
  rewrite (UNd a ltac:(lia) ltac:(lia)).
  pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Himg Ho He ltac:(apply fp_spares_closed; [intros (r & Hr' & _); destruct Hr' | intros (r & Hr' & _); destruct Hr'])).
  exact (UN3 a ltac:(lia) ltac:(lia)). }
assert (KEEPB : forall b m i, In (b, m) (ablocks B ly3 S3) -> 0 <= i < m ->
  rdW W4 (ms_mem ms2) (b + i) = rdW W3 mem3 (b + i)).
{ intros b m i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR4c Hin) as (_ & H4b & Hcb & _ & _ & _ & Hnb).
  pose proof (req_size_pos m ltac:(lia)) as Hrqb.
  rewrite (UNd (b + i) ltac:(lia) ltac:(lia)).
  pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K2 & _).
  rewrite (K2 b m i Hin Hin ltac:(lia) ltac:(intros (r & Hr' & _); destruct Hr')).
  exact (UN3 (b + i) ltac:(lia) ltac:(lia)). }
assert (HREPT : rec_repA B ly3 S3 (rdW W4 (ms_mem ms2)) RT O2).
{ subst RT O2. destruct HREP4 as (Qc & HAQ4 & HOQ4). exists Qc. split; [|exact HOQ4].
  cbn [app] in HAQ4.
  apply (dgb_arep_kept _ (rdW W3 mem3)); [exact HAQ4 | | |].
  - intros a Ha. exact (KEEPT a (or_introl Ha)).
  - intros a Ha. exact (KEEPT a (or_intror Ha)).
  - intros b m i Hin Hi. exact (KEEPB b m i Hin Hi). }
destruct HREPT as (QT & HAQT & HOQT).
assert (HREPT : rec_repA B ly3 S3 (rdW W4 (ms_mem ms2)) RT O2) by (exists QT; split; [exact HAQT | exact HOQT]).
(* the registers at the tail jump *)
assert (A36b : ew Ed 36 = getr regs2 10) by (rewrite OLDd, OLD3 by lia; exact A36).
assert (A68 : ew Ed 68 = getr regs4 10) by (rewrite HEd; reflexivity).
assert (U10' : getr (ms_regs ms2) 10 = w64 (rec_slot R)) by (rewrite U10, A36b; exact Ha02).
assert (U11' : getr (ms_regs ms2) 11 = w64 q) by (rewrite U11, A68; exact Hq10).
assert (U12' : false = negb (bv_unsigned (getr (ms_regs ms2) 12) =? 0))
by (rewrite U12, unsigned_lit_small by lia; reflexivity).
assert (U3' : getr (ms_regs ms2) 3 = w64 (as_gp B))
by (rewrite U3, OLDd, OLD3, OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (U4' : getr (ms_regs ms2) 4 = w64 (as_tp B))
by (rewrite U4, OLDd, OLD3, OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (Uraw : getr (ms_regs ms2) 1 = getr regs 1)
by (rewrite U1, OLDd, OLD3, OLD2 by lia; exact (EEo 1%nat 1%bv eq_refl)).
assert (Usp : spZ (ms_regs ms2) = spZ regs + 0)
by (unfold spZ at 1; rewrite U2, OLDd, OLD3, OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ; lia).
assert (Us0 : s0Z (ms_regs ms2) = s0Z regs)
by (unfold s0Z; rewrite U8, OLDd, OLD3, OLD2 by lia; rewrite (EEo 8%nat 8%bv eq_refl); reflexivity).
(* the stack words at and above the entry's sp are the caller's, so the frame chain is the caller's *)
assert (KHI : forall a, spZ regs <= a < 2 ^ 64 -> rdW W4 (ms_mem ms2) a = rdW W mem a).
{ intros a Ha.
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  exact (F1 a ltac:(lia) ltac:(lia) (NFP0h a ltac:(lia))). }
pose proof HJ4 as (_ & HLY4 & _).
pose proof HLY4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
assert (HchT : achain ly3 (rdW W4 (ms_mem ms2)) (spZ regs + 0) (s0Z (ms_regs ms2)) ch).
{ rewrite Us0, Z.add_0_r. apply (achain_ly_top ly ly3 _ _ _ _ Etop4).
  exact (achain_kept ly (rdW W mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia) ltac:(lia) KHI). }
(* answer's premises at the tail jump *)
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms2)))
by exact (HRODJ ly3 S3 W4 (ms_mem ms2) _ _ HJ4).
assert (HROT : cmd_ro_ok (rdW W4 (ms_mem ms2)))
by exact (cmd_ro_ok_of_aro ly3 S3 W4 (ms_mem ms2) _ HAR4c HRODT).
(* the shape rec_shape_of returned, kept by the epilogue *)
assert (HqLOW : forall (O0 : list (Z * Z)) i, 0 <= i < Z.of_nat (length (shape_of dgb_verb)) + 1 -> q + i < alloc_ceiling).
{ intros O0 i Hi. pose proof (HqA O0) as HA. unfold astr_argA in HA. cbv beta iota zeta in HA.
  destruct HA as (_ & _ & _ & [ ((qq & kk & Hin & Hq1 & Hq2) & _) | (HR & _) ]).
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ qq kk HAR4 Hin) as (_ & _ & Hc & _ & _ & _ & Hk).
    pose proof (req_size_pos kk ltac:(lia)). lia.
  - destruct (HR i Hi) as (Hro & _). destruct (dgb_ro_prog_apart _ Hro) as (Himg & _).
    pose proof (pa_img_range _ Himg). lia. }
assert (HshT : astr_argA B ly3 S3 (rdW W4 (ms_mem ms2)) (in_roP SEGS RLO RHI) O2 q (Some (shape_of dgb_verb))).
{ apply (dgb_argA_kept B ly3 S3 (rdW W4 mem4)); [exact (HqA O2)|].
  intros i Hi. apply UNd; [pose proof (HqLOW O2 i Hi); lia | pose proof (HqLOW O2 i Hi); lia]. }
(* the old answer: the value g_rec.answer held after record(), kept to the tail jump *)
assert (NFPANS : forall i, 0 <= i < 8 -> ~ inFP FP2 (A_G_REC + OFF_ANSWER + i)).
{ intros i Hi (r & Hr & Hin). rewrite FP2eq in Hr. cbn [In] in Hr.
  destruct Hslot as [[H1 H2] | He];
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hin;
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, OFF_ANSWER, A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *;
  try (rewrite He in Hin; unfold A_REC_SPILL in *); lia. }
assert (KEEPG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ inFP FP2 a ->
  rdW W4 (ms_mem ms2) a = rdW W2 mem2 a).
{ intros a Ha Hnf.
  assert (HP : Exists (in_zr a) TFIB_PROG_STATIC) by exact (dgb_static_grec a Ha).
  destruct (prog_static_sep B a (ts_ok B HB) ltac:(rewrite (ts_prog B HB); exact HP)) as (Ho & He & _).
  pose proof (cmd_prog_img a (dgb_grec_in a Ha)) as Himg. pose proof (pa_img_range a Himg) as Hr.
  rewrite (KEEPT a (or_introl Ha)).
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Himg Ho He ltac:(apply fp_spares_closed;
    [intros Hopen; apply (sink_closed_pos FP2); [rewrite FP2eq; repeat apply Forall_cons; try apply Forall_nil;
       cbn [fst]; destruct Hslot as [[H1 H2] | He2];
       unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, OFF_CALLS in *;
       try (rewrite He2; unfold A_REC_SPILL); lia | exact Hopen] | exact Hnf])).
  exact (UN2 a ltac:(lia) ltac:(lia)). }
assert (Hold0 : aval_mem (rdW W4 (ms_mem ms2)) (A_G_REC + OFF_ANSWER) 8 old).
{ apply (dgb_aval_mem_kept (rdW W2 mem2)); [exact HoldE|].
  intros k Hk. apply KEEPG; [unfold OFF_ANSWER, REC_SIZE in *; lia | apply NFPANS; lia]. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Hold' as [-> | (m & Hm & Hm1)]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ old m (proj1 HJ2) (dgb_lay_blocks_in _ _ _ _ _ _ HAQ2 _ Hm))
    as (_ & H4b & Hcb & _ & _ & _ & Hnb). pose proof (req_size_pos m ltac:(lia)). lia. }
(* the callee-saved registers at the tail jump are the caller's *)
prreg HS (18%bv : bv 5) U18. prreg HS (19%bv : bv 5) U19. prreg HS (20%bv : bv 5) U20.
prreg HS (21%bv : bv 5) U21. prreg HS (22%bv : bv 5) U22. prreg HS (23%bv : bv 5) U23.
prreg HS (24%bv : bv 5) U24. prreg HS (25%bv : bv 5) U25. prreg HS (26%bv : bv 5) U26.
prreg HS (27%bv : bv 5) U27.
assert (HPRT : aregs_preserved regs (ms_regs ms2)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hcs : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  [ rewrite (dgb_bv5 2 2%bv eq_refl), U2 | rewrite (dgb_bv5 3 3%bv eq_refl), U3
  | rewrite (dgb_bv5 4 4%bv eq_refl), U4 | rewrite (dgb_bv5 8 8%bv eq_refl), U8
  | rewrite (dgb_bv5 9 9%bv eq_refl), U9 | rewrite (dgb_bv5 18 18%bv eq_refl), U18
  | rewrite (dgb_bv5 19 19%bv eq_refl), U19 | rewrite (dgb_bv5 20 20%bv eq_refl), U20
  | rewrite (dgb_bv5 21 21%bv eq_refl), U21 | rewrite (dgb_bv5 22 22%bv eq_refl), U22
  | rewrite (dgb_bv5 23 23%bv eq_refl), U23 | rewrite (dgb_bv5 24 24%bv eq_refl), U24
  | rewrite (dgb_bv5 25 25%bv eq_refl), U25 | rewrite (dgb_bv5 26 26%bv eq_refl), U26
  | rewrite (dgb_bv5 27 27%bv eq_refl), U27 ];
  rewrite OLDd, OLD3, OLD2 by lia;
  first [exact (EEo 2%nat 2%bv eq_refl) | exact (EEo 3%nat 3%bv eq_refl) | exact (EEo 4%nat 4%bv eq_refl)
        | exact (EEo 8%nat 8%bv eq_refl) | exact (EEo 9%nat 9%bv eq_refl) | exact (EEo 18%nat 18%bv eq_refl)
        | exact (EEo 19%nat 19%bv eq_refl) | exact (EEo 20%nat 20%bv eq_refl) | exact (EEo 21%nat 21%bv eq_refl)
        | exact (EEo 22%nat 22%bv eq_refl) | exact (EEo 23%nat 23%bv eq_refl) | exact (EEo 24%nat 24%bv eq_refl)
        | exact (EEo 25%nat 25%bv eq_refl) | exact (EEo 26%nat 26%bv eq_refl) | exact (EEo 27%nat 27%bv eq_refl)]. }
(* the budgets answer asks for *)
pose proof HJ4 as (_ & _ & _ & _ & _ & HfrS4 & HnevS4 & _).
set (tA := snd (rec_answer RT (REC_DESCRIPTORS_GET, [sarg uri]) (shape_of dgb_verb) false)).
assert (HtA : descriptors_get_m R uri = (fst (rec_answer RT (REC_DESCRIPTORS_GET, [sarg uri]) (shape_of dgb_verb) false), tA)).
{ subst tA RT. rewrite (dgb_model R uri). apply surjective_pairing. }
assert (HtAeq : tA = snd (descriptors_get_m R uri)) by (rewrite HtA; reflexivity).
assert (HEVt : st_nev S3 + EV_ANSWER <= EV_MAX).
{ unfold EV_REC_SHAPE_OF, EV_DESCRIPTORS_GET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia. }
assert (HLVt : blocks_bytes S3 + LIVE_ANSWER tA <= LIVE_MAX).
{ unfold LIVE_DESCRIPTORS_GET in HLV. rewrite HtAeq. lia. }
assert (HMOKt : mo_ok MT S3 (XM_ANSWER MT tA)).
{ apply (mok_station MT S S3 (XM_DESCRIPTORS_GET MT R uri) (XM_RECORD MT R + XM_ARG_S MT uri) (XM_ANSWER MT tA) MTL
    HMOK (mle_station MT S S2 S3 _ _ MTL HMLE2 HMLE3));
  [rewrite HtAeq; lia | unfold XM_DESCRIPTORS_GET; rewrite HtAeq; lia]. }
assert (HFRT : Z.of_nat (length (frames S3)) <= 8) by (rewrite HfrS4; cbn [app]; exact HFR8).
assert (Hc64 : 0 <= rec_slot R < 2 ^ 64).
{ destruct Hslot as [[H1 H2] | He]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; [lia|].
  rewrite He. unfold A_REC_SPILL. lia. }
set (FPT := (A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
  ablocks_fp (filter (fun pn => fst pn =? old) O2)).
assert (HO2S3 : forall pn, In pn O2 -> In pn (ablocks B ly3 S3))
by (intros pn Hpn; exact (dgb_lay_blocks_in _ _ _ _ _ _ HAQT pn (proj1 (HOQT pn) Hpn))).
assert (HO1O : forall pn, In pn O1 -> In pn O) by (intros pn Hpn; exact (proj1 (proj1 (HO1 pn) Hpn))).
assert (HfiltO : forall pn, In pn (filter (fun pn => fst pn =? old) O2) -> In pn O1 /\ In pn O).
{ intros pn Hpn. destruct (dgb_in_filter old O2 pn Hpn) as [Hin Hfst].
  destruct Hold' as [Hz | (m & Hm & Hm1)].
  - exfalso. destruct (al_blocks _ _ LAWS _ _ _ _ _ (fst pn) (snd pn) (proj1 HJ4)
      ltac:(rewrite <- surjective_pairing; exact (HO2S3 pn Hin))) as (_ & H4b & _). lia.
  - subst O2. destruct Hin as [<- | Hin].
    + exfalso. cbn [fst] in Hfst.
      rewrite Forall_forall in HFresh3.
      pose proof (HFresh3 (old, m) ltac:(apply (dgb_lay_blocks_in _ _ _ _ _ _ HAQ2); exact Hm)) as Hap.
      unfold iv_apart in Hap. cbn [fst snd] in Hap.
      unfold n in *. pose proof (Nat2Z.is_nonneg (length (sarg uri))). lia.
    + split; [exact Hin | exact (HO1O pn Hin)]. }
assert (NFPTs : forall a, alloc_ceiling <= a -> ~ inFP FPT a).
{ intros a Ha (r & Hr & Hin). unfold FPT in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hin.
  - unfold A_G_REC, OFF_ANSWER in *. lia.
  - unfold A_G_REC, OFF_STATE in *. lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b m] & <- & Hb). cbn [fst snd] in Hin.
    destruct (HfiltO (b, m) Hb) as (_ & HbO).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HOB (b, m) HbO)) as (_ & _ & Hc & _). lia. }
(* the tail jump into answer *)
eapply SRr_mono;
[ eapply (callS_wideF B LAWS W4 (ms_regs ms2) (ms_mem ms2) _ DESCRIPTORS_GET_STK (spZ regs) FP0 ly S W mem md []
    ly3 S3 _ (0 + EV_RECORD R + EV_ARG_S + EV_REC_SHAPE_OF) ANSWER_STK FPT EV_ANSWER 0 (getr regs 1) ch
    (fun ly' S' W' regs' mem' md' => exists p1 p2 O',
      let nt := Z.of_nat (length tA) + 1 in
      getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
      (forall pn, In pn (ablocks B ly3 S3) -> fst pn <> old -> pn <> (p1, nt) /\ pn <> (p2, nt)) /\
      (forall pn, In pn (ablocks B ly' S') <->
        (In pn (ablocks B ly3 S3) /\ fst pn <> old) \/ pn = (p1, nt) \/ pn = (p2, nt)) /\
      rec_repA B ly' S' (rdW W' mem') (fst (rec_answer RT (REC_DESCRIPTORS_GET, [sarg uri]) (shape_of dgb_verb) false)) O' /\
      (forall pn, In pn O' <-> (In pn O2 /\ fst pn <> old) \/ pn = (p1, nt)) /\
      astr_atR (rdW W' mem') p2 tA /\
      blocks_bytes S' <= blocks_bytes S3 + LIVE_ANSWER tA /\
      mo_le MT S3 S' (XM_ANSWER MT tA)) HJ4 Usp);
  [ reflexivity | lia | rewrite WSA; lia
  | rewrite WS, WSA; lia
  | exact U3' | exact U4' | exact Uraw | exact Hra | exact Hra4
  | exact HchT
  | intros HPREt; rewrite (dgb_sig_answer cmd_sig_prog_PB); eapply SRr_mono;
    [ exact (TANSWER fx ly3 S3 W4 (ms_regs ms2) (ms_mem ms2) _ ch (rec_slot R) q old
        (REC_DESCRIPTORS_GET, [sarg uri]) (shape_of dgb_verb) false RT O2
        HPREt Hfrm HFRT HRODT HROT U10' Hc64 U11' Hq64 U12' HREPT Hold0 Hold64
        (fun _ => conj HshT dgb_fits) ltac:(intros _ Hf; discriminate Hf) HEVt HLVt HMOKt)
    | cbv beta; unfold apost_baseF; intros Wx cx _ (fxx & lyx & Sx & regsx & memx & mdx & -> & HFRx & HFCx & HJx & HPx & HKx);
      exists fxx, lyx, Sx, regsx, memx, mdx;
      split; [rewrite Uraw; reflexivity|]; split; [exact HFRx|]; split; [exact HFCx|];
      split; [exact HJx | split; [exact HPx | exact HKx]] ]
  | intros aa Hf;
    (destruct Hf as (r & Hr & Ha); unfold FPT in Hr; cbn [In] in Hr;
     destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha;
     [ right; right; right; right; left;
       split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
                 [left; reflexivity | cbn [fst snd]; unfold OFF_ANSWER, REC_SIZE in *; lia]|];
       split; [rewrite (ts_prog B HB); apply dgb_static_grec; unfold OFF_ANSWER, REC_SIZE in *; lia
             | apply cmd_prog_img; apply dgb_grec_in; unfold OFF_ANSWER, REC_SIZE in *; lia]
     | right; right; right; right; left;
       split; [exists (A_G_REC, A_G_REC + REC_SIZE); split;
                 [left; reflexivity | cbn [fst snd]; unfold OFF_STATE, REC_SIZE in *; lia]|];
       split; [rewrite (ts_prog B HB); apply dgb_static_grec; unfold OFF_STATE, REC_SIZE in *; lia
             | apply cmd_prog_img; apply dgb_grec_in; unfold OFF_STATE, REC_SIZE in *; lia]
     | right; left; unfold ablocks_fp in Hr; apply in_map_iff in Hr as ([b m] & <- & Hb);
       cbn [fst snd] in Ha; destruct (HfiltO (b, m) Hb) as (Hb1 & HbO);
       split;
       [ exists (b, b + req_size m); split;
         [right; right; unfold ablocks_fp; apply in_map_iff; exists (b, m); split; [reflexivity | exact HbO]
         | cbn [fst snd]; exact Ha]
       | exists b, m; split; [exact (HO2S3 (b, m) ltac:(subst O2; right; exact Hb1)) | exact Ha] ] ])
  | intros ly5 S5 W5 regs5 mem5 md5 HK aa Hf Hst Hn; exfalso; lia ]
| ].
cbv beta. intros Wf cf _ (fxf & lyf & Sf & regsf & memf & mdf & -> & HFRf & HFCf & HJf & HJcf & HPf & HKf).
destruct HKf as (p1 & p2 & O' & HKf). cbv zeta in HKf.
destruct HKf as (Hp2 & Hp2b & H12 & HGa & HLf & HRf & HO' & Hstr2 & HBBf & HMLEf).
(* two live blocks: one block per start, and distinct blocks apart *)
assert (STARTS : forall lyx Sx (Wx : world SEGS) memx mdx b1 b2, AR SEGS B lyx Sx Wx memx mdx ->
  In b1 (ablocks B lyx Sx) -> In b2 (ablocks B lyx Sx) -> fst b1 = fst b2 -> b1 = b2).
{ intros lyx Sx Wx memx mdx [pa na] [pb nb] HARx H1 H2 He. cbn [fst] in He.
  destruct (dgb_pair_dec (pa, na) (pb, nb)) as [Eq|Hne]; [exact Eq|]. exfalso.
  pose proof (sep_blocks SEGS B LAWS lyx Sx Wx memx mdx pa na pb nb HARx H1 H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ pa na HARx H1) as (_ & _ & _ & _ & _ & _ & Hn1).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HARx H2) as (_ & _ & _ & _ & _ & _ & Hn2).
  pose proof (req_size_pos na ltac:(lia)). pose proof (req_size_pos nb ltac:(lia)). lia. }
assert (IVS : forall lyx Sx (Wx : world SEGS) memx mdx b1 b2, AR SEGS B lyx Sx Wx memx mdx ->
  In b1 (ablocks B lyx Sx) -> In b2 (ablocks B lyx Sx) -> b1 <> b2 ->
  iv_apart (fst b1) (snd b1) (fst b2) (snd b2)).
{ intros lyx Sx Wx memx mdx [pa na] [pb nb] HARx H1 H2 Hne.
  pose proof (sep_blocks SEGS B LAWS lyx Sx Wx memx mdx pa na pb nb HARx H1 H2 Hne) as Hd.
  unfold zdisjoint, iv_apart in *. cbn [fst snd] in *.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ pa na HARx H1) as (_ & _ & _ & _ & _ & _ & Hn1).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HARx H2) as (_ & _ & _ & _ & _ & _ & Hn2).
  pose proof (req_size_pos na ltac:(lia)). pose proof (req_size_pos nb ltac:(lia)). lia. }
assert (NODUP0 : List.NoDup (ablocks B ly S)).
{ destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  assert (Hpos : forall b, In b (ablocks B ly S) -> 1 <= req_size (snd b)).
  { intros [pa na] Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ pa na HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    exact (proj1 (req_size_pos na ltac:(lia))). }
  revert Hp Hpos. generalize (ablocks B ly S) as l. induction l as [|y l IH]; intros Hp Hpos; [constructor|].
  cbn [map pairwise] in Hp. destruct Hp as [Hfa Hp]. constructor.
  - intros Hin. rewrite Forall_forall in Hfa.
    pose proof (Hfa (fst y, req_size (snd y)) (in_map (fun b => (fst b, req_size (snd b))) l y Hin)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (Hpos y (or_introl eq_refl)). lia.
  - apply IH; [exact Hp | intros b Hb; apply Hpos; right; exact Hb]. }
(* the block lists of the post *)
assert (HQc : forall pn, In pn O1 -> In pn (ablocks B ly2 S2))
by (intros pn Hpn; exact (dgb_lay_blocks_in _ _ _ _ _ _ HAQ2 pn (proj1 (HOQ2 pn) Hpn))).
assert (HOQc : forall pn, In pn O -> In pn (ablocks B ly2 S2) -> In pn O1).
{ intros pn HpO Hpc. apply HO1. split; [exact HpO|]. intros HpF.
  exact (dgb_nodup_app_disj _ _ pn (Permutation_NoDup HPerm2 NODUP0) Hpc HpF). }
assert (HoldQL : old = 0 \/ exists m, In (old, m) O1)
by (destruct Hold' as [Hz | (m & Hm & _)]; [left; exact Hz | right; exists m; apply HOQ2; exact Hm]).
destruct (dgb_post_blocks (ablocks B ly S) (ablocks B ly2 S2) (ablocks B ly3 S3) (ablocks B lyf Sf) F O1 O2 O O'
  p n p1 p2 (Z.of_nat (length tA) + 1) old
  HPerm2 HFO HO1O HQc HOQc HPerm3 HFresh3 ltac:(unfold n; lia)
  ltac:(subst O2; apply Permutation_cons_append) HoldQL
  (fun b1 b2 H1 H2 He => STARTS ly3 S3 W4 (ms_mem ms2) _ b1 b2 HAR4c H1 H2 He)
  ltac:(intros b Hb; destruct (al_blocks _ _ LAWS _ _ _ _ _ (fst b) (snd b) HAR4c
          ltac:(rewrite <- surjective_pairing; exact Hb)) as (_ & H4b & _); exact H4b)
  HGa H12 HLf HO'
  (fun b1 b2 H1 H2 He => STARTS lyf Sf Wf memf mdf b1 b2 (proj1 HJf) H1 H2 He)
  (fun b1 b2 H1 H2 Hne => IVS lyf Sf Wf memf mdf b1 b2 (proj1 HJf) H1 H2 Hne))
  as (B1 & B2 & B3 & B4 & B5).
(* the post *)
unfold apost_baseF. exists fxf, lyf, Sf, regsf, memf, mdf.
split; [reflexivity|]. split; [exact HFRf|]. split; [exact HFCf|].
split; [eapply (ajournal_mono_k SEGS B); [exact HJf | unfold EV_DESCRIPTORS_GET, EV_REC_SHAPE_OF in *; lia]|].
split; [exact (aregs_preserved_trans _ _ _ HPRT HPf)|].
exists (fst (rec_answer RT (REC_DESCRIPTORS_GET, [sarg uri]) (shape_of dgb_verb) false)), tA, p2, O'.
split; [exact HtA|]. split; [exact Hp2|]. split; [exact Hp2b|]. split; [exact HRf|]. split; [exact B1|].
split; [apply HLf; right; right; reflexivity|].
split; [exact B2|]. split; [exact B3|]. split; [exact Hstr2|]. split; [exact B4|]. split; [exact B5|].
split.
- unfold LIVE_DESCRIPTORS_GET. rewrite HtAeq in HBBf. lia.
- unfold XM_DESCRIPTORS_GET. rewrite HtAeq in HMLEf.
  exact (mle_station MT S S3 Sf _ _ MTL (mle_station MT S S2 S3 _ _ MTL HMLE2 HMLE3) HMLEf).
Qed.
End e.
End f.
End d.
