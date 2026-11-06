(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module names changed; 224 of its 267 lines of code are new or changed and 516 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_set56: Lemma lc_set56_ok : lc_set56_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   segment SET56 of the image-A walk of LLVMFuzzerTestOneInput, offsets +0x1018 .. +0x1020 of the listing
   lib/A/Prog/DgnTransportList.v (fuzz_transport.asan 0x8227c .. 0x82284), from the cut SET56 of ops 5 and 6 to the
   loop tail TAIL (+0x12ec).

   What the code does. +0x1018 `li a0, 0` (ticked = 0), +0x101c `jal settle` (return address +0x1020), +0x1020
   `j +0x12ec`.

   How it is proved.
     the run (+0x1018)       TransportGRunA.v paj_run_x over the caller's G journal from a state with no region; it
                             writes no byte (YC4b.v kept_of_frame).
     settle                  TransportGCg.v gx_call_cg with the contract settle_cg.v transport_settle_cg (lp_settle),
                             ticked = 0, at the world Bw the cut carries with settle_m Bw 0 = Some (Bw, tt); its
                             queue-length premise from the kit statement K6 (lc_runinv_stmt, the lemma's argument; the
                             composer supplies it from the kit row) at agree timg_A (ops + 1)
                             Bw, which LLVMFuzzerTestOneInput_st.v lc_tail_agree gives from the operation's equation at
                             the stream fun _ => 1. Its window SETTLE_STK lies below the realigned sp1, so the core, the
                             spill slots and the frame's shadow are kept (lc_core_kept, lc_spills_kept, lc_fsh_kept);
                             the world relation is kept through gx_kept (TMAP_A's rows are ranges of G).
     the jump (+0x1020)      paj_run_x to the cut TAIL from a state with no region; it writes no byte.
   The tail's model equation is the cut's at the stream fun _ => 1 (recv_addr_ok 1), the cursor and the reception
   count unchanged. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import settle_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The return address of the call of settle, and the span and base of the runs' states (no region). *)
Definition S56_RET : Z := 0x1020.
Definition S56_B0 : Z * Z := (0, 0).
Definition S56_Bx : sv := SLit 0.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac s56_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* The write right of a run from a state with no region. *)
Ltac s56_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.
(* A run from a state with no region writes no byte. *)
Ltac s56_kept HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin; destruct Hin
  | ].

(* A payload byte of the world table is a byte of G. *)
Lemma s56_tw_in_G : forall x, tw_in TMAP_A x -> inG TG.G_HARNESS x.
Proof.
intros x (o & b & n & Hin & Hx). unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Section s56. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition s56_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).

Lemma s56_env_img : forall regs, img_env VAL A_LIM (s56_E regs).
Proof. intros regs. unfold s56_E. apply Eimg_env. Qed.

(* A symbolic state with no region holds of any machine state at its pc. *)
Lemma s56_entry0 : forall fx (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (s56_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros fx W regs mem pc. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The cut pcs as the listing's code addresses. *)
Lemma s56_pc : forall o, w64 (transport_text + o) = Z_to_bv 64 (BASE + o).
Proof. intros o. unfold w64. f_equal; try (vm_compute; reflexivity). Qed.

Lemma lc_set56_ok (K6 : lc_runinv_stmt) : @lc_set56_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_set56_stmt. intros HP cx op W' c' HB HST.
destruct HST as (ly' & S' & regs' & mem' & md' & e & Bw & -> & Hopc & HL & HTW & HSET & HOP & HCUR & R20 & R22).
pose proof HL as (HC & HFR & HSPL & HFSH & HOK & He & HMET & R21).
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof HOK as (HAG & Hops & Hcin & Hcn & Hk).
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC)
  as [HAR Hsp0al Hstk Hsp1c HFaddr HFin HnG HINg HLIVEg].
pose proof HB as HB'. unfold lc_base, tfib_lib_pre_x in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (G_HARNESS_gx_noerrno B (lp_g_no_errno _ _ _ _ _ HP)) as HGE.
destruct HCUR as [R24 R23].
(* the model: the operation's end world agrees at ops + 1, so settle's queue-length premise holds there *)
destruct (lc_tail_agree (l_pl cx) (lo_ops op) (lo_B op) (lo_c op) (lo_k op) 1 Bw (lc_oc (l_pl cx) (lo_c op))
  (lo_k op) HAG Hops Hcin Hcn Hk ltac:(unfold recv_addr_ok; lia) (HOP (fun _ => 1))) as (HAG1 & _ & _).
pose proof (K6 (lo_ops op + 1) Bw HAG1) as (_ & HQL & _).
(* the numbers *)
assert (EOPS : TC.OPS_MAX = 1024) by reflexivity.
assert (ESTK : SETTLE_STK = 8288) by reflexivity.
assert (ELST : LLVMF_STK = 32768) by reflexivity.
assert (EEV : EV_LIB = 2048) by reflexivity.
assert (ERE : RECV_EV = 2) by reflexivity.
unfold LF_FRAME in Hsp1.
assert (Hsp1c' : alloc_ceiling + 32432 <= lc_sp1 cx) by exact Hsp1c.
pose proof alloc_ceiling_val as EAC.
(* ---- +0x1018: `li a0, 0`, up to the call ---- *)
pose proof (s56_entry0 (l_fx cx) W' regs' mem' LO_SET56) as HS.
assert (HEI : img_env VAL A_LIM (s56_E regs')) by apply s56_env_img.
assert (SHOK : sh_ok segs S56_Bx (@nil shent) (s56_E regs') (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
unfold lc_cfg. rewrite s56_pc.
paj_run_tok RUN HS HJ SHOK S56_B0.
{ s56_awr. }
s56_kept HFr KR W' mem' ms.
assert (GR1 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the registers at the call *)
assert (HPR1 : aregs_preserved regs' (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W') _ _ ms regs' [] HS).
  - split; [intros n Hn; unfold s56_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
  - vm_compute. reflexivity. }
s56_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + S56_RET)) Q1 ltac:(apply codeptr_val; exact HEI).
s56_reg HS (10%bv : bv 5) (w64 0) Q10 ltac:(reflexivity).
assert (Q2 : YK11.getr (ms_regs ms) 2 = w64 (lc_sp1 cx))
  by exact (eq_trans (HPR1 2 ltac:(unfold acallee_saved; lia)) Rsp).
assert (Q3 : YK11.getr (ms_regs ms) 3 = w64 (as_gp B))
  by exact (eq_trans (HPR1 3 ltac:(unfold acallee_saved; lia)) Rgp).
assert (Q4 : YK11.getr (ms_regs ms) 4 = w64 (as_tp B))
  by exact (eq_trans (HPR1 4 ltac:(unfold acallee_saved; lia)) Rtp).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx)
  by (unfold spZ; change (Z_to_bv 5 2) with (2%bv : bv 5); rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (ERA : BASE + S56_RET = 0x82284) by (vm_compute; reflexivity).
assert (RAok : YK0s.ret_ok (Z_to_bv 64 (BASE + S56_RET)))
  by (apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold S56_RET; lia | reflexivity]).
(* the world relation at the call memory *)
assert (TWc : tw_at TMAP_A (aview segs (w_H W') (ms_mem ms)) Bw).
{ apply (tw_kept TMAP_A (aview segs (w_H W') mem')); [exact HTW|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KR. lia. }
(* +0x101c: the call of settle *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS_settle)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_call_cg (l_fx cx) rc tfib_sink_head segs B MT TG.G_HARNESS LLVMF_STK (lc_sp0 cx) _
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W' (ms_mem ms) _ e _
    (ms_regs ms) SETTLE_STK SETTLE_EV 0 (fun _ => False) (fun _ _ _ => Bw = Bw) HGX HGE HJ).
  intros memS HJd.
  eapply SRr_mono.
  { apply (lp_settle _ _ _ _ _ HP (l_fx cx) LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) memS
      (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W' (ms_mem ms) _ e (ms_regs ms) 0 Bw Bw HJd).
    - exact (eq_ind_r (fun w => YK0s.ret_ok w) RAok Q1).
    - unfold raZ. change (Z_to_bv 5 1) with (1%bv : bv 5). rewrite Q1, ERA, unsigned_lit_small by lia. lia.
    - exact Q3.
    - exact Q4.
    - exact Q10.
    - lia.
    - rewrite QSP. pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1.
      rewrite Hsp1al, Z.add_0_r in D1. rewrite D1.
      replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring. apply Z.mod_mul. lia.
    - rewrite QSP, ESTK, ELST. lia.
    - rewrite QSP. lia.
    - exact TWc.
    - exact HSET.
    - exact HQL.
    - unfold SETTLE_EV. lia. }
  cbv beta. intros W3 c3 _ H3. apply decode_cg_post_dcg. exact H3. }
cbv beta.
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & HFR3 & HPM3 & HK3 & HMO3 & (_ & HGK3)).
assert (Ee3 : e3 = 0) by (unfold SETTLE_EV in He3; lia). subst e3. rewrite Z.add_0_r in HJ3.
pose proof HK3 as (K31 & K32 & _ & K34 & _).
rewrite QSP in K31.
rename ms into msC.
(* ---- +0x1020: `j +0x12ec` ---- *)
rewrite Q1.
pose proof (s56_entry0 (l_fx cx) W3 regs3 mem3 S56_RET) as HS3.
assert (HEI3 : img_env VAL A_LIM (s56_E regs3)) by apply s56_env_img.
assert (SHOK3 : sh_ok segs S56_Bx (@nil shent) (s56_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 S56_B0 LO_TAIL.
{ s56_awr. }
s56_kept HFr KR2 W3 mem3 ms.
clear HF HFr HG.
assert (HPR3 : aregs_preserved regs3 (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok segs (w_H W3) _ _ ms regs3 [] HS3).
  - split; [intros n Hn; unfold s56_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
  - vm_compute. reflexivity. }
assert (HPRT : aregs_preserved regs' (ms_regs ms))
  by exact (aregs_preserved_trans _ _ _ (aregs_preserved_trans _ _ _ HPR1 HP3) HPR3).
pmkst HS3.
apply SRr_ret.
(* ---- the cut TAIL ---- *)
assert (KALL : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - SETTLE_STK <= a < lc_sp1 cx) ->
  aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha Hw. rewrite KR2 by lia. rewrite K31 by lia. apply KR. lia. }
assert (KFR : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W3) (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a Ha. rewrite KR2 by (unfold lc_SH, LF_FBYTES, SHADOW_OFF in *; lia).
  transitivity (aview segs (w_H W') (ms_mem msC) a).
  - apply (K34 LF_CID (l_fpos cx) a HFin); [|intros []].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID) with LF_FBYTES.
    destruct Ha as [Ha | Ha]; [left; lia | right].
    unfold shadow_addr, lc_SH in *. change (LF_FBYTES / 8) with 32. lia.
  - apply KR. unfold lc_SH, LF_FBYTES, SHADOW_OFF in *; lia. }
assert (KBL : forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
  aview segs (w_H W3) (ms_mem ms) (b + i) = aview segs (w_H W') mem' (b + i)).
{ intros b m i Hb Hi. assert (Hr : 0 <= b + i < 2 ^ 64).
  { destruct (al_blocks _ _ LAWS ly' S' W' mem' md' b m HAR Hb) as (_ & H4096 & Hce & _).
    pose proof alloc_ceiling_val. lia. }
  rewrite KR2 by exact Hr.
  transitivity (aview segs (w_H W') (ms_mem msC) (b + i)); [exact (K32 b m i Hb Hi ltac:(intros [])) | apply KR; exact Hr]. }
exists ly3, S3, (ms_regs ms), (ms_mem ms). eexists. exists e, 1, Bw, (lc_oc (l_pl cx) (lo_c op)), (lo_k op).
split; [unfold lc_cfg; first [reflexivity | rewrite s56_pc; reflexivity | f_equal; f_equal; vm_compute; reflexivity]|].
split.
{ split; [exact (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e SETTLE_STK ly3 S3 W3 (ms_regs ms)
            (ms_mem ms) _ e LAWS HB HC HJ3 HFR3 HPM3 HPRT ltac:(rewrite ESTK, ELST; lia) KALL KBL KFR)|].
  split; [split; [exact (eq_trans (HPRT 18 ltac:(unfold acallee_saved; lia)) (proj1 HFR))
                 | exact (eq_trans (HPRT 26 ltac:(unfold acallee_saved; lia)) (proj2 HFR))]|].
  split.
  { apply (lc_spills_kept cx _ (aview segs (w_H W') mem') (aview segs (w_H W3) (ms_mem ms))); [| | exact HSPL].
    - intros o Ho. unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm in Ho.
      cbn [app In] in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho.
    - intros a Ha. apply KALL; lia. }
  split; [apply (lc_fsh_kept cx (aview segs (w_H W') mem')); [intros a Ha; apply KFR; right; exact Ha | exact HFSH]|].
  split; [exact HOK|].
  split; [lia|].
  split.
  { destruct HMET as [HM1 HM2]. split.
    - replace (Z.of_nat (lo_k op) * lf_rcost MT) with (Z.of_nat (lo_k op) * lf_rcost MT + 0) by lia.
      exact (mo_le_trans MT MTL _ _ _ _ _ HM1 HMO3).
    - apply (mo_ok_step MT MTL S' S3 0 _); [rewrite Z.add_0_l; exact HM2 | exact HMO3]. }
  exact (eq_trans (HPRT 21 ltac:(unfold acallee_saved; lia)) R21). }
split; [unfold recv_addr_ok; lia|].
split; [exact (HOP (fun _ => 1))|].
split.
{ unfold lc_tw. apply (tw_kept TMAP_A (aview segs (w_H W') mem')); [exact HTW|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  rewrite KR2 by lia.
  transitivity (aview segs (w_H W') (ms_mem msC) x); [exact (HGK3 x (s56_tw_in_G x Hx)) | apply KR; lia]. }
split; [split; [exact (eq_trans (HPRT 24 ltac:(unfold acallee_saved; lia)) R24)
               | exact (eq_trans (HPRT 23 ltac:(unfold acallee_saved; lia)) R23)]|].
split; [exact (eq_trans (HPRT 20 ltac:(unfold acallee_saved; lia)) R20)|].
exact (eq_trans (HPRT 22 ltac:(unfold acallee_saved; lia)) R22).
Qed.

End s56.
