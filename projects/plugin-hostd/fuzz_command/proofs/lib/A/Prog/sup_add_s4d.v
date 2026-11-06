(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: descriptors_panel_get's walk from the join of record()'s arms (0x8d180) to the call of xstrdup (plugin-hostd/fuzz_command.asan), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment proved from the next one's statement: seed, run, branch, call) and lib/A/Prog/sup_reply_code.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_panel_get_s4.v, with its module paths and module names changed; 243 of its 288 lines of code are new or changed and 262 lines of the source are left out. *)
(* sup_add's walk, stage M2 -> M3 (plugin-hostd/fuzz_command, ASan build): from the return of the first xstrdup
   (0x89fd4) to the second call (0x8a01c): the check of nargs, nargs := 3, the check of args[2], args[2] := the
   copy, the pruned `blt`, client's spill and the branch on it (a0 = client, or "-" when client is NULL). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdAddr CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s4a sup_add_s4b sup_add_s4c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a :=
  CmdRecBase.cif_relro_img _ _ IMG.
Let cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a :=
  CmdRecBase.cif_prog_not_ro _ _ IMG.
Let cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) :=
  CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md -> In e cmd_ro_ends ->
  atail_vis SEGS W mem e :=
  CmdRecRo.cmd_tail_vis_at SEGS B LAWS HB IMG.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Let RUN := paj_run B LAWS.

(* the image atom of "-" (A_OBJ 53) *)
Lemma s4_dash : forall E, img_env VAL A_LIM E -> ew E 294 = w64 0x21d40.
Proof using fx rc SK PI VOBJS.
intros E HEI. rewrite <- (Z_to_bv_bv_unsigned _ (ew E 294)).
rewrite (HEI 294%nat ltac:(split; [unfold A_TEXT; lia | apply Nat.ltb_lt; vm_compute; reflexivity])).
change 294%nat with (A_OBJ 53%nat). rewrite (VOBJS 53%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
vm_compute. reflexivity.
Qed.

(* 0x89fd4 .. 0x8a01c, then the second call of xstrdup *)
Lemma s4_ret1 : SA_M3_stmt B MT ->
  forall ly S W regs mem md ch pu id pp pcl uri placement client R O ly1 S1 W1 regs1 mem1 md1 pos Oj p n,
  sa_cx B MT ly S W regs mem md ch pu id pp pcl uri placement client R O ->
  s4_mid B MT ly S W regs mem md R O ly1 S1 W1 regs1 mem1 md1 pos [sarg uri; dec id] Oj (Oj ++ [(p, n)])
    (sa_ev2 R + EV_XSTRDUP) (sa_acc2 MT R uri id + XM_XSTRDUP MT (darg placement (bstr "-"%string)))
    (sa_live2 uri id + LIVE_XSTRDUP (darg placement (bstr "-"%string))) ->
  s4_fresh B ly1 S1 (rdW W1 mem1) Oj p n (darg placement (bstr "-"%string)) ->
  getr regs1 10 = w64 p ->
  SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + S4_RET1)) mem1 (seg_rom SEGS)) md1)
    (sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using fx rc SK PI HB LAWS MTL SIGP PRW cif_prog_img cif_relro_img cif_prog_not_ro cmd_ro_in_img
  cmd_ro_ok_of_aro cmd_heap_tail_vis cmd_tail_vis_at TXSTRDUP VOBJS.
intros M3 ly S W regs mem md ch pu id pp pcl uri placement client R O ly1 S1 W1 regs1 mem1 md1 pos Oj p n
  HCX HMID HFR H10.
pose proof HCX as HCX0.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr & HROD & HRO & Hr10 & Hpu & Hr11 & Hid & Hr12 & Hpp & Hr13 & Hpc & HU & HP & HPT &
  HC & HCT & HREP0 & Hev & Hlive & MOK).
clear Hfr HRO Hr10 Hpu Hr11 Hid Hr12 Hpp HU HP HPT HCT.
pose proof HPRE as (HAR0 & _).
pose proof HMID as HMID0.
destruct HMID as (HCORE & H20 & H22 & H23 & H24 & H27 & HBUF & HREP & HSUB & HACCT & HMLE).
unfold sa_core in HCORE. cbv zeta in HCORE.
destruct HCORE as (HJ & HFRAME & Hs16 & Hs24 & Hs48 & HFLAG & A2 & A3 & A4 & A8 & A9 & A18 & A19 & A21 & A25 & A26).
clear HFRAME Hs48 HFLAG A3 A4 A8 A18 A19 A21 A25 A26 HBUF HSUB HMLE.
pose proof HACCT as (_ & _ & HLIVE3 & _ & _). clear HACCT.
pose proof (proj1 HJ) as HAR1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as (HB0 & HB1 & HB4).
assert (HSTKa : 176 <= SUP_ADD_STK) by (vm_compute; discriminate).
pose proof (s4_s1_facts (spZ regs) Hal16) as Hs1v. pose proof (s4_s1_al (spZ regs)) as Hs1a.
pose proof (s4_c_of_R R) as [Hc Hc8]. pose proof (s4_c_range (sa_c R) Hc) as (Hc1 & Hc2 & Hc3).
(* the copy's address, in range *)
pose proof HFR as (Hnew & Hp4096 & Hn & _).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 mem1 md1 p n HAR1 Hnew) as (_ & _ & Hpc' & _).
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
(* nargs = 2 at the return *)
destruct (rec_repA_last_call B HB LAWS ly1 S1 (rdW W1 mem1) R _ Oj HREP) as (P & HCALL & _).
destruct HCALL as (_ & _ & _ & _ & HNA & _). cbn [snd length Z.of_nat] in HNA. unfold CALL_OFF_NARGS in HNA.
clear HREP P.
assert (Hvp : 0 <= bv_unsigned (getr regs 12) < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs 12)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; lia).
assert (Hvc : 0 <= bv_unsigned (getr regs 13) < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs 13)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; lia).
assert (Hvcpc : bv_unsigned (getr regs 13) = pcl) by (rewrite Hr13; unfold w64; apply unsigned_lit_small; lia).
(* the budgets of the second call *)
assert (HEVb : sa_ev2 R + EV_XSTRDUP + EV_XSTRDUP <= EV_SUP_ADD R).
{ unfold EV_SUP_ADD, sa_ev2, sa_ev1. pose proof (Z.le_max_r EV_ANSWER EV_HAND_BACK).
  unfold EV_HAND_BACK, EV_ARG_I, EV_XSTRDUP in *. lia. }
assert (HLIVEb : sa_live2 uri id + LIVE_XSTRDUP (darg placement (bstr "-"%string)) +
    LIVE_XSTRDUP (darg client (bstr "-"%string)) <=
  LIVE_SUP_ADD uri id placement client (snd (sup_add_m R uri id placement client))).
{ unfold LIVE_SUP_ADD, sa_live2.
  pose proof (Z.le_max_r (LIVE_ANSWER (snd (sup_add_m R uri id placement client)))
    (LIVE_HAND_BACK (snd (sup_add_m R uri id placement client)))).
  unfold LIVE_HAND_BACK, LIVE_XSTRDUP in *. lia. }
assert (HACCb : sa_acc2 MT R uri id + XM_XSTRDUP MT (darg placement (bstr "-"%string)) +
    XM_XSTRDUP MT (darg client (bstr "-"%string)) <=
  XM_SUP_ADD MT R uri id placement client (snd (sup_add_m R uri id placement client))).
{ unfold XM_SUP_ADD, sa_acc2, sa_acc1.
  pose proof (Z.le_max_r (XM_ANSWER MT (snd (sup_add_m R uri id placement client)))
    (XM_HAND_BACK MT (snd (sup_add_m R uri id placement client)))) as Hm.
  pose proof (mo_free_nonneg MT MTL).
  assert (0 <= XM_XSTRDUP MT (snd (sup_add_m R uri id placement client)))
    by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
  unfold XM_HAND_BACK in *. lia. }
(* the seed at 0x89fd4 *)
destruct (s4_seed B HB LAWS PRW 1 2 ly1 S1 W1 mem1 md1 regs1 S4_RET1 (sa_s1 (spZ regs)) (sa_c R)
  (bv_unsigned (getr regs 12)) (bv_unsigned (getr regs 13)) HAR1 A2 A9 H20 H22 H23 H24 H27
  ltac:(lia) ltac:(lia) Hs1a Hc Hc8 ltac:(lia) Hvp Hvc Hs16 Hs24 (fun _ => HNA)) as [HS SHOK].
clear Hs16 Hs24 HNA.
destruct (s4_E_facts regs1 (bv_unsigned (getr regs 12)) (bv_unsigned (getr regs 13))) as (EE & _ & E33 & HEI & _).
set (E := s4_E regs1 (bv_unsigned (getr regs 12)) (bv_unsigned (getr regs 13))) in *.
clearbody E.
assert (U22 : bv_unsigned (ew E 22) = sa_c R)
  by (rewrite (EE 22%nat (22%bv : bv 5) eq_refl), H22; unfold w64; apply unsigned_lit_small; lia).
assert (D10 : sv_denot E (SOff 10 0) = Z_to_bv 64 p).
{ cbn [sv_denot]. rewrite (EE 10%nat (10%bv : bv 5) eq_refl), H10. unfold w64.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
pose proof (fun r => st_ok_pi_restrict_reg _ _ _ _ r HS) as HRA.
(* the branch on client's spill (atom 33), decided at the seed *)
apply (paj_branch (PI := PI) W1 E _ _ md1 _ BC_NE (SOff 33 0) (SLit 0) HS); intros Hcnd HS'; clear HS.
- (* client is not NULL: a0 = client *)
  assert (Hvc0 : bv_unsigned (getr regs 13) <> 0).
  { rewrite branch_ne_U in Hcnd. apply negb_true_iff, Z.eqb_neq in Hcnd.
    rewrite (U_atom E 33 _ E33 Hvc), U_SLit in Hcnd. change (zcanon 0) with 0 in Hcnd. exact Hcnd. }
  destruct client as [x|]; [| unfold astr_argA in HC; cbv beta iota in HC; lia].
  rename HS' into HS. paj_run_tok RUN HS HJ SHOK s4_Bspan.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact U22 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
      exact (s4_awr_slot B HB LAWS IMG (sa_c R) O _ _ _ _ _ _ _ a Hc ltac:(lia)) |].
    eapply awr_ok_cons_gen; [reflexivity | exact U22 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
      exact (s4_awr_slot B HB LAWS IMG (sa_c R) O _ _ _ _ _ _ _ a Hc ltac:(lia)) |].
    apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m2) => set (ms2 := m2) in * end.
  pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HR1.
  pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HR2.
  pose proof (fun r => st_ok_restrict_reg SEGS _ E _ _ r HS) as HRB.
  cbn [ms_mem restrict mkst] in HR1, HR2.
  assert (KR : forall z, In z s4_kz -> getr (ms_regs ms2) (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z))
    by exact (s4_regs_eq E _ _ regs1 (ms_regs ms2) HRA HRB ltac:(vm_compute; reflexivity)).
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ mem1) (mrestrict _ (ms_mem ms2)) |- _ =>
    pose proof (kept_of_frame (segs:=SEGS) E _ (w_H W1) mem1 (ms_mem ms2)
      (fun a => sa_c R + 4 <= a < sa_c R + 8 \/ sa_c R + 24 <= a < sa_c R + 32) Hfr ltac:(s4_kof U22)) as KM
  end.
  pose proof (s4_aval_of_val (w_H W1) (ms_mem ms2) (sa_c R + 4) 4 3
    (field_of_region E _ 22%nat (sa_c R) _ 4 8 4 8 4 4%N (SLit 3) 3 HR1 U22 ltac:(cbn; tauto) eq_refl
      ltac:(cbn; lia) ltac:(lia))) as VNA.
  pose proof (s4_aval_of_val (w_H W1) (ms_mem ms2) (sa_c R + 24) 8 p
    (field_of_region E _ 22%nat (sa_c R) _ 24 32 24 32 24 8%N (SOff 10 0) p HR2 U22 ltac:(cbn; tauto) D10
      ltac:(cbn; lia) ltac:(lia))) as VARG.
  clear HR1 HR2 HRA HRB.
  pose proof (s4_store B MT HB LAWS ly S W regs mem md R O ly1 S1 W1 regs1 mem1 md1
    (ms_regs ms2) (ms_mem ms2) mdv pos [sarg uri; dec id] Oj
    (sa_ev2 R + EV_XSTRDUP) (sa_acc2 MT R uri id + XM_XSTRDUP MT (darg placement (bstr "-"%string)))
    (sa_live2 uri id + LIVE_XSTRDUP (darg placement (bstr "-"%string)))
    p n (darg placement (bstr "-"%string)) HMID0 HFR ltac:(cbn; lia) HJ
    ltac:(intros a Ha Hn1 Hn2; cbn [length] in Hn2; apply KM; [exact Ha | cbv beta; lia])
    VNA
    ltac:(replace (sa_c R + 8 + 8 * Z.of_nat (length [sarg uri; dec id]))
            with (sa_c R + 24) by (cbn [length]; lia); exact VARG)
    KR) as HM.
  assert (P10' : getr (ms_regs ms2) 10 = w64 pcl) by (rewrite P10, E33, Hvcpc; reflexivity).
  change (BASE + 15164) with (BASE + S4_RET2) in P1.
  assert (HAROc : arodata_okP SEGS RLO RHI B (rdW W1 (ms_mem ms2)))
    by exact (sa_aro_kept B HB LAWS IMG
      SUP_ADD_STK (spZ regs) ly S W mem md [(1, pos)] ly1 S1 W1 (ms_mem ms2) mdv (sa_ev2 R + EV_XSTRDUP) R O
      HAR0 HJ HREP0 HROD).
  destruct (sa_str_ready B HB LAWS IMG
    SUP_ADD_STK (spZ regs) ly S W mem md [(1, pos)] ly1 S1 W1 (ms_mem ms2) mdv (sa_ev2 R + EV_XSTRDUP) R O pcl x
    HAR0 HJ HREP0 HROD HC HAROc HLIVE3) as [HSTR HTAIL].
  exact (s4_call B MT HB LAWS MTL SIGP IMG
    TXSTRDUP ly S W regs mem md ch pu id pp pcl uri placement (Some x) R O ly1 S1 W1
    (ms_regs ms2) (ms_mem ms2) mdv pos [sarg uri; dec id; darg placement (bstr "-"%string)] (Oj ++ [(p, n)])
    (sa_ev2 R + EV_XSTRDUP) (sa_acc2 MT R uri id + XM_XSTRDUP MT (darg placement (bstr "-"%string)))
    (sa_live2 uri id + LIVE_XSTRDUP (darg placement (bstr "-"%string))) pcl x S4_RET2
    HCX0 HM P1 ltac:(unfold S4_RET2, AF_sup_add; lia) eq_refl P10' HSTR HTAIL HEVb HLIVEb HACCb
    (fun ly2 S2 W2 regs2 mem2 md2 p2 n2 HM2 HF2 H102 =>
       s4_ret2 B MT HB LAWS PRW IMG M3 ly S W regs mem md ch pu id pp pcl uri placement
         (Some x) R O ly2 S2 W2 regs2 mem2 md2 pos (Oj ++ [(p, n)]) p2 n2 HCX0 HM2 HF2 H102)).
- (* client is NULL: a0 = "-" *)
  assert (Hvc0 : bv_unsigned (getr regs 13) = 0).
  { rewrite branch_ne_U in Hcnd. apply negb_false_iff, Z.eqb_eq in Hcnd.
    rewrite (U_atom E 33 _ E33 Hvc), U_SLit in Hcnd. change (zcanon 0) with 0 in Hcnd. exact Hcnd. }
  destruct client as [x|]; [destruct HC as (Hne & _); lia|].
  rename HS' into HS. paj_run_tok RUN HS HJ SHOK s4_Bspan.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact U22 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
      exact (s4_awr_slot B HB LAWS IMG (sa_c R) O _ _ _ _ _ _ _ a Hc ltac:(lia)) |].
    eapply awr_ok_cons_gen; [reflexivity | exact U22 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
      exact (s4_awr_slot B HB LAWS IMG (sa_c R) O _ _ _ _ _ _ _ a Hc ltac:(lia)) |].
    apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m2) => set (ms2 := m2) in * end.
  pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HR1.
  pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HR2.
  pose proof (fun r => st_ok_restrict_reg SEGS _ E _ _ r HS) as HRB.
  cbn [ms_mem restrict mkst] in HR1, HR2.
  assert (KR : forall z, In z s4_kz -> getr (ms_regs ms2) (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z))
    by exact (s4_regs_eq E _ _ regs1 (ms_regs ms2) HRA HRB ltac:(vm_compute; reflexivity)).
  lazymatch goal with Hfr : frame_of _ _ (mrestrict _ mem1) (mrestrict _ (ms_mem ms2)) |- _ =>
    pose proof (kept_of_frame (segs:=SEGS) E _ (w_H W1) mem1 (ms_mem ms2)
      (fun a => sa_c R + 4 <= a < sa_c R + 8 \/ sa_c R + 24 <= a < sa_c R + 32) Hfr ltac:(s4_kof U22)) as KM
  end.
  pose proof (s4_aval_of_val (w_H W1) (ms_mem ms2) (sa_c R + 4) 4 3
    (field_of_region E _ 22%nat (sa_c R) _ 4 8 4 8 4 4%N (SLit 3) 3 HR1 U22 ltac:(cbn; tauto) eq_refl
      ltac:(cbn; lia) ltac:(lia))) as VNA.
  pose proof (s4_aval_of_val (w_H W1) (ms_mem ms2) (sa_c R + 24) 8 p
    (field_of_region E _ 22%nat (sa_c R) _ 24 32 24 32 24 8%N (SOff 10 0) p HR2 U22 ltac:(cbn; tauto) D10
      ltac:(cbn; lia) ltac:(lia))) as VARG.
  clear HR1 HR2 HRA HRB.
  pose proof (s4_store B MT HB LAWS ly S W regs mem md R O ly1 S1 W1 regs1 mem1 md1
    (ms_regs ms2) (ms_mem ms2) mdv pos [sarg uri; dec id] Oj
    (sa_ev2 R + EV_XSTRDUP) (sa_acc2 MT R uri id + XM_XSTRDUP MT (darg placement (bstr "-"%string)))
    (sa_live2 uri id + LIVE_XSTRDUP (darg placement (bstr "-"%string)))
    p n (darg placement (bstr "-"%string)) HMID0 HFR ltac:(cbn; lia) HJ
    ltac:(intros a Ha Hn1 Hn2; cbn [length] in Hn2; apply KM; [exact Ha | cbv beta; lia])
    VNA
    ltac:(replace (sa_c R + 8 + 8 * Z.of_nat (length [sarg uri; dec id]))
            with (sa_c R + 24) by (cbn [length]; lia); exact VARG)
    KR) as HM.
  assert (P10' : getr (ms_regs ms2) 10 = w64 0x21d40) by (rewrite P10; exact (s4_dash E HEI)).
  change (BASE + 15164) with (BASE + S4_RET2) in P1.
  pose proof (proj1 HJ) as HAR2.
  assert (HAROc : arodata_okP SEGS RLO RHI B (rdW W1 (ms_mem ms2)))
    by exact (sa_aro_kept B HB LAWS IMG
      SUP_ADD_STK (spZ regs) ly S W mem md [(1, pos)] ly1 S1 W1 (ms_mem ms2) mdv (sa_ev2 R + EV_XSTRDUP) R O
      HAR0 HJ HREP0 HROD).
  destruct (sa_lit_ready B HB LAWS IMG
    ly1 S1 W1 (ms_mem ms2) mdv 0x21d40 (bstr "-"%string) HAR2
    (cmd_ro_ok_of_aro ly1 S1 W1 (ms_mem ms2) mdv HAR2 HAROc) (or_intror eq_refl)) as [HSTR HTAIL].
  exact (s4_call B MT HB LAWS MTL SIGP IMG
    TXSTRDUP ly S W regs mem md ch pu id pp pcl uri placement None R O ly1 S1 W1
    (ms_regs ms2) (ms_mem ms2) mdv pos [sarg uri; dec id; darg placement (bstr "-"%string)] (Oj ++ [(p, n)])
    (sa_ev2 R + EV_XSTRDUP) (sa_acc2 MT R uri id + XM_XSTRDUP MT (darg placement (bstr "-"%string)))
    (sa_live2 uri id + LIVE_XSTRDUP (darg placement (bstr "-"%string))) 0x21d40 (bstr "-"%string) S4_RET2
    HCX0 HM P1 ltac:(unfold S4_RET2, AF_sup_add; lia) eq_refl P10' HSTR HTAIL HEVb HLIVEb HACCb
    (fun ly2 S2 W2 regs2 mem2 md2 p2 n2 HM2 HF2 H102 =>
       s4_ret2 B MT HB LAWS PRW IMG M3 ly S W regs mem md ch pu id pp pcl uri placement
         None R O ly2 S2 W2 regs2 mem2 md2 pos (Oj ++ [(p, n)]) p2 n2 HCX0 HM2 HF2 H102)).
Qed.
End e.
End f.
End d.
