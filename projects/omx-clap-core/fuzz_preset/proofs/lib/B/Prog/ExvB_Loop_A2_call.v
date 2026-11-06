(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece A2 (the key path): the three CALLS the piece
   makes from a cut-like state with EXBs (sp = s1), each in one lemma: ex_ws (B 0x83b28 / 0x83c28, the tex_ws_specX
   = EXV_HYP's exv_ws, YCbqGcallW.v aj_call_xW at e1 = exv_sp E + e_d E - exv_s1 E), ex_string (B 0x83b74, eh_string,
   the same rule) and strcmp (B 0x83c04, eh_strcmp = YGcallMxmn.v astrcmp_realizes_xrom, its rule aj_strcmp_at_xrom
   with KIT_RODATA's arodata_okP). After each call EXBs again (ExvB_Loop_Stmt.v KIT_CALLs / KIT_RUNs) and the bytes
   the piece reads later (ex_value's frame, the cursor cells outside the callee's footprint, the root node of the tree)
   unchanged. Also the facts the key compare reads at a state with EXB: the parent node (a2_node), the key slot and
   string (a2_key, from ExvB_Loop_kitL.v exvl_node_key), the scratch block (a2_scr).
   Old-pin kit 4f18c75d4900 rebind: fpre's `raZ regs < alloc_ceiling` from the jal's return pc (a listing literal
   below 2 ^ 32 <= CEIL_MIN); the program callees' m-form posts (S' = S: exv_room_refl; their memnorm keep composed
   with EXB's exv_rm keep) and strcmp's keep (aj_strcmp_at_xrom's last conjunct) feed KIT_CALLs / KIT_RUNs.
   Rule 24: proves no function (kind: segment lemma helper).
   Numerals: 2, 3, 4, 8, 10, 11, 24 (WORD: register numbers); 8, 16, 24, 32, 36, 40, 56, 176, 288, 304, 319 (LENGTH:
   struct ex fields, node size, ex_value's frame); 4096, 8192 = 2 * ESTACK, 16384 (LENGTH: stack budgets of the
   STK_* table, vm_compute); 2 ^ 32, 2 ^ 46, 2 ^ 47, 2 ^ 63, 2 ^ 64 (LENGTH: address-space bounds). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW YGcallMx YC88 YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_exw ExvB_Loop_kit ExvB_Loop_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Open_sh ExvB_Open_kt ExvB_Loop_A2_ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_kitL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Lemma a2_stk : forall n, STK_ex_value n = Z.of_nat (S n) * 304 + 16384.
Proof.
intros n. unfold STK_ex_value.
match goal with |- ?a * ?b + ?c = _ =>
  let b' := eval vm_compute in b in let c' := eval vm_compute in c in change b with b'; change c with c' end.
reflexivity.
Qed.
Lemma a2_stk_ws : STK_ex_ws = 16. Proof. vm_compute. reflexivity. Qed.
Lemma a2_stk_str : STK_ex_string = 160. Proof. vm_compute. reflexivity. Qed.

Local Ltac a2_ne := let H := fresh in intros H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis KCALL : forall fx : YK11.FPState, KIT_CALLs (fx := fx) B ARx SK.
Hypothesis KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Hypothesis KCH : forall fx : YK11.FPState, KIT_CALL_CHAIN (fx := fx) B ARx SK.
Hypothesis KROD : forall fx : YK11.FPState, KIT_RODATA (fx := fx) B ARx SK.
Hypothesis KWD : forall fx : YK11.FPState, KIT_WDEST (fx := fx) B ARx SK.
Local Abbreviation LAWS := (eh_laws B ARx SK HYP).
(* every lemma of this section takes every section hypothesis, so the walk file calls them with one argument list *)
#[local] Set Default Proof Using "All".

(* the geometry of a state with EXB: the frame, the cursor, the stack budget *)
Lemma a2_geom : forall E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  alloc_ceiling + exv_STK E <= exv_sp E /\ exv_sp E mod 16 = 0 /\ 0 <= e_d E /\ e_d E mod 16 = 0 /\
  exv_sp E + e_d E <= ly_stk_hi lyc /\ ly_stk_hi lyc <= 2 ^ 47 /\ exv_sp E + 64 <= ly_stk_hi lyc /\
  exv_sp E - 304 <= exv_s1 E <= exv_sp E - 288 /\ exv_s1 E mod 32 = 0 /\
  exv_sp E <= e_q E /\ e_q E + 40 <= exv_sp E + e_d E /\ e_q E mod 8 = 0 /\
  exv_STK E = Z.of_nat (S (e_n E)) * 304 + 16384 /\
  spZ regs = exv_s1 E /\ s0Z regs = exv_sp E /\
  ARx lyc Sc Hpc Wc memc mdc /\ ly_top lyc = ly_top (e_ly E) /\ exv_sp E + e_d E <= ly_top lyc.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos HP HB.
pose proof asan_consts as (C1 & _).
unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFN & _ & _ & _ & _ & _ & PQ8 & _ & PSPQ & PQD & PWIN & _).
destruct HFN as ((_ & _ & _ & _ & _ & HSTK & _) & _ & H64 & _).
unfold EXB in HB. cbv zeta in HB.
destruct HB as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & _).
destruct HJ as (JAR & JLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JSTK & _).
destruct JLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
destruct HSTK as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
destruct JSTK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
destruct PWIN as (D0 & D16 & Dtop & _).
pose proof (exv_s1_le E) as ((S1a & S1b) & S1c).
pose proof (a2_stk (e_n E)) as HSTKv. fold (exv_STK E) in HSTKv.
assert (Hsp0 : 0 <= exv_sp E) by (unfold exv_sp, spZ; pose proof (bv_unsigned_in_range _ (getr (e_regs E) 2%bv)); lia).
unfold exv_sp in *.
assert (S1d : spZ (e_regs E) - 304 <= exv_s1 E).
{ unfold exv_s1, exv_sp. rewrite exv_land32. clear - A1. lia. }
assert (U2 : spZ regs = exv_s1 E).
{ unfold spZ. rewrite R2. apply unsigned_lit_small. lia. }
assert (U8 : s0Z regs = spZ (e_regs E)).
{ unfold s0Z. rewrite R8. apply unsigned_lit_small. lia. }
repeat split; try lia; try exact JAR.
Qed.

(* EXBs's registers: every one but s8 is the EXB state's *)
Lemma a2_exbs_reg : forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos,
  EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exists regs0, EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs0 memc mdc k pos /\
    getr regs 2 = w64 (exv_s1 E) /\ getr regs 8 = w64 (exv_sp E) /\ getr regs 9 = w64 (exv_s1 E) /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 19 = w64 (e_q E) /\
    getr regs 25 = w64 SHADOW_OFF /\ getr regs 18 = w64 (frame_addr lyc 1 pos) /\
    getr regs 26 = w64 (shadow_addr (frame_addr lyc 1 pos)) /\
    (forall r, r <> 24%bv -> getr regs r = getr regs0 r).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos (regs0 & HB & Hrr). exists regs0. split; [exact HB|].
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & _).
rewrite !Hrr by a2_ne. repeat split; first [assumption | reflexivity].
Qed.

(* the tree's root node is kept across a program call (its home: a Lam block, a live fake frame, or the real stack
   above s1, which is the caller window or above it) *)
Lemma a2_root_kept : forall E lyc Sc Hpc Wc regs memc mdc k pos FP1 STK1 ly2 S2 Hp2 (W2 : world rsegs) mem2 md2 k1,
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  (forall a, inFP FP1 a -> inFP (exv_FP E) a) ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx STK1 (exv_sp E + e_d E) FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, exv_s1 E <= a < exv_sp E + e_d E -> ~ inFP FP1 a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
  ablocks B ly2 S2 = ablocks B lyc Sc ->
  forall a, e_v E <= a < e_v E + 56 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos FP1 STK1 ly2 S2 Hp2 W2 mem2 md2 k1 HP HB Hv0 HFP HJ1 HW1 HAB a Ha.
pose proof (a2_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & GAR & _).
pose proof asan_consts as (C1 & _).
pose proof HP as HP'. unfold EXV_PRE in HP'. cbv zeta in HP'.
destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PV & _).
destruct PV as [PV | (_ & _ & PDJ)]; [exfalso; exact (Hv0 PV)|].
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & HLED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTREE).
destruct HTREE as [HT0 | (_ & Hhome & _ & _)]; [exfalso; exact (Hv0 HT0)|].
assert (Hnfp : ~ inFP FP1 a).
{ intros Hf. apply HFP in Hf. destruct (PDJ a ltac:(left; lia)) as (D1 & D2 & _).
  destruct Hf as (r & Hr & Hra). unfold exv_FP in Hr.
  repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hra; lia|]). destruct Hr. }
destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & JSTK & JBLK & _ & JFR & _).
destruct Hhome as [(b & kk & Hin & Hb1 & Hb2) | [(cid & pos' & Hin & Hf1 & Hf2) | (Hs1 & Hs2)]].
- pose proof HLED as (_ & _ & HLB & _). rewrite Forall_forall in HLB.
  destruct (HLB (b, kk) Hin) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
  pose proof (@cf_head_nonneg cp) as CH0.
  replace a with ((b - cf_head) + (a - (b - cf_head))) by lia.
  apply (JBLK (b - cf_head) (kk + cf_head) (a - (b - cf_head)) Hblk); [rewrite HAB; exact Hblk | | ].
  + unfold req_size. destruct (Z.eqb_spec (kk + cf_head) 0); lia.
  + replace (b - cf_head + (a - (b - cf_head))) with a by lia. exact Hnfp.
- apply (JFR cid pos' a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hnfp].
- rewrite G14 in Hs1. destruct (Z_lt_le_dec a (exv_sp E + e_d E)) as [Hlt | Hge].
  + apply HW1; [lia | exact Hnfp].
  + apply JSTK; lia.
Qed.

(* the callee-saved registers EXB reads are kept by a call that preserves the callee-saved registers *)
Lemma a2_bregs_of_preserved : forall regs regs2 : bvmap 5 word, aregs_preserved regs regs2 ->
  forall r, In r exv_bregs -> r <> 24%bv -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 HPR r Hr _. unfold exv_bregs in Hr.
repeat (destruct Hr as [<- | Hr];
  [ match goal with |- getr _ ?r = _ => let z := eval vm_compute in (bv_unsigned r) in
      exact (HPR z ltac:(unfold acallee_saved; lia)) end |]).
destruct Hr.
Qed.

(* the ex_ws call (B 0x83b28 and B 0x83c28): from the call's entry state (pc = ex_ws, ra = ret, a0 = q) *)
Lemma a2_call_ws : forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos (ip ret : Z)
  (Post : world rsegs -> config -> Prop),
  EXV_PRE B ARx E -> EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  getr regs 10 = w64 (e_q E) -> getr regs 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) -> 4096 <= ret < 2 ^ 32 ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_q E) 8 (e_x0 E + ip) ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_q E + 8) 8 (e_x0 E + exv_len E) -> 0 <= ip <= exv_len E ->
  (forall ly2 S2 Hp2 (W2 : world rsegs) (regs2 : bvmap 5 word) mem2 md2 k1,
     EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos ->
     aregs_preserved regs regs2 ->
     (forall a, exv_s1 E <= a < exv_sp E + e_d E -> ~ (e_q E <= a < e_q E + 8) ->
        aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
     (e_v E <> 0 -> forall a, e_v E <= a < e_v E + 56 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
     val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E) 8
       (e_x0 E + exv_len E - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat ip) (e_x E))))) ->
     SRr rsegs W2 (cfg_at (fx := fx) rsegs ret regs2 mem2 md2) Post) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_WS regs memc mdc) Post.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos ip ret Post HP HBs H10 H1 Hret Hret4 Vp Ve Hip HK.
destruct (a2_exbs_reg E lyc Sc Hpc Wc regs memc mdc k pos HBs)
  as (regs0 & HB & R2 & R8 & R9 & R3 & R4 & R19 & R25 & R18 & R26 & Hrr).
pose proof (a2_geom E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB) as G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & _ & _ & GAR & Gtop & Gtop2).
pose proof asan_consts as (C1 & _).
assert (U2 : spZ regs = exv_s1 E) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (U8 : s0Z regs = exv_sp E) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
pose proof HP as HP'. unfold EXV_PRE in HP'. cbv zeta in HP'.
destruct HP' as (HFN & PFZ & _ & _ & _ & _ & PQ8 & _ & PSPQ & PQD & PWIN & _ & _ & PLEN & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (HJ & HWIN & HFRG & HFRM & HHP & HAB & HROOM & HLED & HCNT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HSAV & HSLOT & HFLAG & HSRC & HINB & HWD & HSINB & HQRA & HTREE).
destruct (KCH fx E lyc Sc Hpc Wc regs0 memc mdc k pos regs HP HB R2 R8) as (ch1 & Hch & _).
destruct (KROD fx E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB) as (HROD & _).
pose proof a2_stk_ws as HWS.
assert (HRA : raZ regs < alloc_ceiling /\ YK0o.frm_zero (@YK11.fp_csr fx)).
{ split; [pose proof alloc_ceiling_value as [[AC _] _]; unfold raZ; rewrite H1, unsigned_lit_small by lia; lia | exact HFRM]. }
unfold cfg_at at 1.
eapply SRr_bind.
{ eapply (YCbqGcallW.aj_call_xW (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low Wc regs memc A2_WS
    (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)]
    lyc Sc Hpc mdc k STK_ex_ws (exv_sp E + e_d E - exv_s1 E) [(e_q E, e_q E + 8)] (exv_s1 E - (exv_sp E + e_d E))
    (Z_to_bv 64 ret) ch1 _ HJ).
  - rewrite U2. lia.
  - lia.
  - lia.
  - rewrite a2_stk_ws. lia.
  - rewrite a2_stk_ws. lia.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact H1.
  - exact Hret.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) by lia. rewrite U8. exact Hch.
  - intros HPRE1 HWIN1.
    refine (exv_ws B ARx SK HYP fx lyc Sc Hpc Wc regs memc mdc ch1 (e_q E) (e_x0 E) ip
      (exv_sp E + e_d E - exv_s1 E) (e_x E) (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
      (conj HPRE1 (conj HROD (conj _ HRA))) H10 Vp Ve G12 _ _ HWIN1 HSRC HINB PLEN Hip HLED); rewrite U2; lia.
  - intros a Ha. left. destruct Ha as (r & [<- | []] & Hr). exists (e_q E, e_q E + 8).
    split; [unfold exv_FP; right; left; reflexivity | exact Hr]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HJ2 & HW2 & HPR & HQ).
destruct HQ as ((HRM2 & Vq2 & HHp2 & HS2 & HAB2 & HLED2) & HMN2).
replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)) + (exv_sp E + e_d E - exv_s1 E))
  with (exv_sp E + e_d E) in HJ2 by lia.
assert (HFP : forall a, inFP [(e_q E, e_q E + 8)] a -> inFP (exv_FP E) a).
{ intros a (r & [<- | []] & Hr). exists (e_q E, e_q E + 8). split; [unfold exv_FP; right; left; reflexivity | exact Hr]. }
assert (HW2' : forall a, exv_s1 E <= a < exv_sp E + e_d E -> ~ inFP [(e_q E, e_q E + 8)] a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros a Ha Hn. apply HW2; [lia | exact Hn]. }
destruct (KCALL fx E lyc Sc Hpc Wc regs memc mdc k pos fx [(e_q E, e_q E + 8)] (STK_ex_ws + (exv_sp E + e_d E - exv_s1 E))
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HP HBs HFP HJ1 HJ2 HW2' (a2_bregs_of_preserved regs regs2 HPR)
  (fun r _ => eq_refl) HFRM (exv_room_eq Sc Sc S2 (exv_room_refl Sc) HS2) (fun H0 => HMN2 (proj2 HROOM H0))
  HHp2 HAB2 HLED2) as (HBs2 & _).
apply (HK ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HBs2 HPR).
- intros a Ha Hn. apply HW2'; [exact Ha|]. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. exact (Hn Hr).
- intros Hv0. exact (a2_root_kept E lyc Sc Hpc Wc regs0 memc mdc k pos [(e_q E, e_q E + 8)] _ ly2 S2 Hp2 W2 mem2 md2 k1
    HP HB Hv0 HFP HJ2 HW2' HAB2).
- exact Vq2.
Qed.

(* the ex_string call (B 0x83b74): from its entry state (pc = ex_string, ra = ret, a0 = q), the opening quote at
   x0 + i0 *)
Lemma a2_call_str : forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos (i0 ret : Z)
  (Post : world rsegs -> config -> Prop),
  EXV_PRE B ARx E -> EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  getr regs 10 = w64 (e_q E) -> getr regs 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) -> 4096 <= ret < 2 ^ 32 ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_q E) 8 (e_x0 E + i0) ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_q E + 8) 8 (e_x0 E + exv_len E) ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_q E + 24) 8 (e_scr E) -> 0 <= i0 < exv_len E ->
  (forall ly2 S2 Hp2 (W2 : world rsegs) (regs2 : bvmap 5 word) mem2 md2 k1,
     EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos ->
     aregs_preserved regs regs2 ->
     (forall a, exv_s1 E <= a < exv_sp E + e_d E -> ~ (e_q E <= a < e_q E + 8) ->
        aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
     (e_v E <> 0 -> forall a, e_v E <= a < e_v E + 56 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
     match exv_run0 (PjGrammar.jr_string (skipn (S (Z.to_nat i0)) (e_x E))) with
     | None => getr regs2 10 = w64 (-1) /\ val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E) 8 (e_x0 E + i0)
     | Some (s, rest) => getr regs2 10 = w64 0 /\
         (exists c, PjGrammar.scan (skipn (S (Z.to_nat i0)) (e_x E)) = Some c /\
            rest = skipn (S c) (skipn (S (Z.to_nat i0)) (e_x E)) /\
            val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E) 8 (e_x0 E + i0 + Z.of_nat c + 2)) /\
         bytes_at W2 mem2 (e_scr E) (s ++ [0])
     end ->
     SRr rsegs W2 (cfg_at (fx := fx) rsegs ret regs2 mem2 md2) Post) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_STR regs memc mdc) Post.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos i0 ret Post HP HBs H10 H1 Hret Hret4 Vp Ve Vs Hi0 HK.
destruct (a2_exbs_reg E lyc Sc Hpc Wc regs memc mdc k pos HBs)
  as (regs0 & HB & R2 & R8 & R9 & R3 & R4 & R19 & R25 & R18 & R26 & Hrr).
pose proof (a2_geom E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB) as G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & _ & _ & GAR & Gtop & Gtop2).
pose proof asan_consts as (C1 & _).
assert (U2 : spZ regs = exv_s1 E) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (U8 : s0Z regs = exv_sp E) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
pose proof HP as HP'. unfold EXV_PRE in HP'. cbv zeta in HP'.
destruct HP' as (HFN & PFZ & _ & _ & _ & _ & PQ8 & _ & PSPQ & PQD & PWIN & _ & _ & PLEN & _ & _ & _ & _ & _ & _ &
  PSX & PSQ & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (HJ & HWIN & HFRG & HFRM & HHP & HAB & HROOM & HLED & HCNT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HSAV & HSLOT & HFLAG & HSRC & HINB & HWD & HSINB & HQRA & HTREE).
destruct (KCH fx E lyc Sc Hpc Wc regs0 memc mdc k pos regs HP HB R2 R8) as (ch1 & Hch & _).
destruct (KROD fx E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB) as (HROD & _).
pose proof a2_stk_str as HSS.
assert (HWDs : wdest_ok B STK_ex_string lyc Sc Wc regs memc (e_scr E) (exv_len E + 1)).
{ apply (KWD fx E lyc Sc Hpc Wc regs0 memc mdc k pos regs STK_ex_string HP HB R2); lia. }
pose proof HWDs as (WD0 & WD1 & _).
assert (Hlen0 : 0 < exv_len E) by lia.
assert (HRA : raZ regs < alloc_ceiling /\ YK0o.frm_zero (@YK11.fp_csr fx)).
{ split; [pose proof alloc_ceiling_value as [[AC _] _]; unfold raZ; rewrite H1, unsigned_lit_small by lia; lia | exact HFRM]. }
unfold cfg_at at 1.
eapply SRr_bind.
{ eapply (YCbqGcallW.aj_call_xW (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low Wc regs memc A2_STR
    (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)]
    lyc Sc Hpc mdc k STK_ex_string (exv_sp E + e_d E - exv_s1 E) [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8)]
    (exv_s1 E - (exv_sp E + e_d E)) (Z_to_bv 64 ret) ch1 _ HJ).
  - rewrite U2. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact H1.
  - exact Hret.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) by lia. rewrite U8. exact Hch.
  - intros HPRE1 HWIN1.
    refine (eh_string B ARx SK HYP fx lyc Sc Hpc Wc regs memc mdc ch1 (e_q E) (e_x0 E) i0 (e_scr E)
      (exv_sp E + e_d E - exv_s1 E) (e_x E) (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
      (conj HPRE1 (conj HROD (conj _ HRA))) H10 Vp Ve Vs G12 _ _ HWIN1 HSRC (HINB Hlen0) PLEN Hi0 HWDs HSINB PSX PSQ HLED);
      rewrite U2; lia.
  - intros a Ha. left. destruct Ha as (r & [<- | [<- | []]] & Hr).
    + exists (e_scr E, e_scr E + exv_len E + 1). split; [unfold exv_FP; left; reflexivity | exact Hr].
    + exists (e_q E, e_q E + 8). split; [unfold exv_FP; right; left; reflexivity | exact Hr]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HJ2 & HW2 & HPR & HQ).
destruct HQ as ((HRM2 & HHp2 & HS2 & HAB2 & HLED2 & HM) & HMN2).
replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)) + (exv_sp E + e_d E - exv_s1 E))
  with (exv_sp E + e_d E) in HJ2 by lia.
assert (HFP : forall a, inFP [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8)] a -> inFP (exv_FP E) a).
{ intros a (r & [<- | [<- | []]] & Hr).
  - exists (e_scr E, e_scr E + exv_len E + 1). split; [unfold exv_FP; left; reflexivity | exact Hr].
  - exists (e_q E, e_q E + 8). split; [unfold exv_FP; right; left; reflexivity | exact Hr]. }
assert (HW2' : forall a, exv_s1 E <= a < exv_sp E + e_d E ->
  ~ inFP [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8)] a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros a Ha Hn. apply HW2; [lia | exact Hn]. }
destruct (KCALL fx E lyc Sc Hpc Wc regs memc mdc k pos fx [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8)]
  (STK_ex_string + (exv_sp E + e_d E - exv_s1 E))
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HP HBs HFP HJ1 HJ2 HW2' (a2_bregs_of_preserved regs regs2 HPR)
  (fun r _ => eq_refl) HFRM (exv_room_eq Sc Sc S2 (exv_room_refl Sc) HS2) (fun H0 => HMN2 (proj2 HROOM H0))
  HHp2 HAB2 HLED2) as (HBs2 & _).
assert (HWQ : forall a, exv_s1 E <= a < exv_sp E + e_d E -> ~ (e_q E <= a < e_q E + 8) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros a Ha Hn. apply HW2'; [exact Ha|]. intros (r & [<- | [<- | []]] & Hr); cbn [fst snd] in Hr; lia. }
apply (HK ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HBs2 HPR HWQ).
- intros Hv0. exact (a2_root_kept E lyc Sc Hpc Wc regs0 memc mdc k pos _ _ ly2 S2 Hp2 W2 mem2 md2 k1
    HP HB Hv0 HFP HJ2 HW2' HAB2).
- change (Nat.succ (Z.to_nat i0)) with (S (Z.to_nat i0)) in HM.
  revert HM. unfold exv_run0. destruct (fst (fst (PjGrammar.jr_string (skipn (S (Z.to_nat i0)) (e_x E)) []))) as [[s rest]|];
    intros HM.
  + destruct HM as (HM10 & (c & Hc1 & Hc2 & Hc3) & HM3). split; [exact HM10|]. split; [|exact HM3].
    exists c. split; [exact Hc1|]. split; [exact Hc2 | exact Hc3].
  + destruct HM as (HM10 & HMq). split; [exact HM10|].
    apply (YC88.val_mem_aview_kept_x rsegs (w_H Wc) (w_H W2) memc mem2); [|exact Vp].
    intros a Ha. exact (HMq a ltac:(change (Z.of_nat 8) with 8 in Ha; lia)).
Qed.

(* bytes of a garr8 seen through aview *)
Lemma a2_aview_garr8 : forall H mem p L j, garr8 rsegs (mrestrict H mem) p L -> (j < length L)%nat ->
  aview rsegs H mem (p + Z.of_nat j) = Some (nth j L 0).
Proof.
intros H mem p L j HG Hj. destruct (HG j Hj) as (Hv & Hr).
unfold aview. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YO0f.le_byte.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r.
rewrite !Z.mod_mod by lia. apply Z.mod_small. exact Hr.
Qed.
Lemma a2_apresent_aview : forall H mem a, apresent H mem a -> aview rsegs H mem a <> None.
Proof. intros H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

(* a NUL-terminated string at p whose bytes before the NUL are not 0: strcmp's first_byte *)
Lemma a2_first_byte : forall (W : world rsegs) mem p (l : list Z),
  garr8 rsegs (mrestrict (w_H W) mem) p (l ++ [0]) -> Forall (fun c => c <> 0) l ->
  first_byte rsegs W mem p (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros W mem p l HG HF. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + rewrite <- (Z2Nat.id i) at 1 by lia. rewrite (a2_aview_garr8 _ _ _ _ _ HG) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + rewrite Forall_forall in HF. apply HF. apply nth_In. lia.
- intros _.
  rewrite (a2_aview_garr8 _ _ _ _ (length l) HG) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

(* two NUL-terminated strings compare equal byte for byte exactly when the lists are equal *)
Lemma a2_str_eq : forall (W : world rsegs) mem x y (kl sl : list Z),
  garr8 rsegs (mrestrict (w_H W) mem) x (kl ++ [0]) -> garr8 rsegs (mrestrict (w_H W) mem) y (sl ++ [0]) ->
  (Z.of_nat (length kl) = Z.of_nat (length sl) /\
   forall i, 0 <= i < Z.of_nat (length kl) -> aview rsegs (w_H W) mem (x + i) = aview rsegs (w_H W) mem (y + i)) <->
  kl = sl.
Proof.
intros W mem x y kl sl Hx Hy. split.
- intros (Hl & Hi). apply (nth_ext kl sl 0 0); [lia|]. intros n Hn.
  specialize (Hi (Z.of_nat n) ltac:(lia)).
  rewrite (a2_aview_garr8 _ _ _ _ _ Hx) in Hi by (rewrite length_app; cbn; lia).
  rewrite (a2_aview_garr8 _ _ _ _ _ Hy) in Hi by (rewrite length_app; cbn; lia).
  injection Hi as Hi. rewrite !app_nth1 in Hi by lia. exact Hi.
- intros <-. split; [reflexivity|]. intros i Hi.
  rewrite <- (Z2Nat.id i) by lia.
  rewrite (a2_aview_garr8 _ _ _ _ _ Hx) by (rewrite length_app; cbn; lia).
  rewrite (a2_aview_garr8 _ _ _ _ _ Hy) by (rewrite length_app; cbn; lia). reflexivity.
Qed.

(* a range inside a live block, past its head when hidden: strcmp's amem_range8, tail granule *)
Lemma a2_blk_str : forall ly S Hp (W : world rsegs) mem md b m p n,
  ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> b <= p -> p + n + 1 <= b + m -> 0 <= n ->
  YGcallMx.amem_range8 p (n + 1) /\
  (forall a, p + n < a < p + n - (p + n) mod 8 + 8 -> aview rsegs (w_H W) mem a <> None).
Proof.
intros ly S Hp W mem md b m p n HAR Hin Hbp Hpm Hn.
pose proof (eh_blk_amem8 B ARx SK HYP ly S Hp W mem md b m (p - b + n) HAR Hin ltac:(lia)) as H8.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4096 & _ & _ & Hpres & _).
assert (Hreq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split.
- unfold YGcallMx.amem_range8 in *. lia.
- intros a Ha. destruct (Z_lt_le_dec a (b + m)) as [Hlt | Hge].
  + apply a2_apresent_aview. apply (proj1 (Hpres a ltac:(rewrite Hreq; lia))).
  + apply (alx_blocks_tail _ _ _ LAWS ly S Hp W mem md b m a HAR Hin). rewrite Hreq. split; [lia|].
    clear - Ha Hge Hpm Hn. lia.
Qed.

(* the strcmp call (B 0x83c04): a0 = the key string of the ledger (Lam), a1 = the scratch holding s ++ [0] *)
Lemma a2_call_cmp : forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos (x ret kk : Z) (kl sl : list Z)
  (Post : world rsegs -> config -> Prop),
  EXV_PRE B ARx E -> EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  getr regs 10 = w64 x -> getr regs 11 = w64 (e_scr E) -> getr regs 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  In (x, kk) (e_Lam E) -> Z.of_nat (length kl) + 1 <= kk -> PRH_Reader.pj_cbytesR rsegs (mrestrict (w_H Wc) memc) x kl ->
  bytes_at Wc memc (e_scr E) (sl ++ [0]) -> Forall (fun c => c <> 0) sl -> (length sl <= length (e_x E))%nat ->
  (forall (regs2 : bvmap 5 word) mem2 md2 (v : word),
     EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs2 mem2 md2 k pos ->
     aregs_preserved regs regs2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_s1 E - 8192 <= a < exv_s1 E) ->
        aview rsegs (w_H Wc) mem2 a = aview rsegs (w_H Wc) memc a) ->
     getr regs2 10 = v -> (v = w64 0 <-> kl = sl) ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs ret regs2 mem2 md2) Post) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs A2_CMP regs memc mdc) Post.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos x ret kk kl sl Post HP HBs H10 H11 H1 Hret HinL Hkl HKB HSB HSNZ HSL HK.
destruct (a2_exbs_reg E lyc Sc Hpc Wc regs memc mdc k pos HBs)
  as (regs0 & HB & R2 & R8 & R9 & R3 & R4 & R19 & R25 & R18 & R26 & Hrr).
pose proof (a2_geom E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB) as G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & _ & _ & GAR & Gtop & Gtop2).
pose proof asan_consts as (C1 & _).
assert (HES : ESTACK = 4096) by reflexivity.
assert (U2 : spZ regs = exv_s1 E) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
pose proof HP as HP'. unfold EXV_PRE in HP'. cbv zeta in HP'.
destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PLEN & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (HJ & HWIN & HFRG & HFRM & HHP & HAB & HROOM & HLED & HCNT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HSAV & HSLOT & HFLAG & HSRC & HINB & HWD & HSINB & HQRA & HTREE).
destruct (KROD fx E lyc Sc Hpc Wc regs0 memc mdc k pos HP HB) as (HROM & _).
pose proof (@cf_head_nonneg cp) as CH0.
(* the key: its harness block *)
pose proof HLED as (_ & _ & HLB & _). rewrite Forall_forall in HLB.
destruct (HLB (x, kk) HinL) as (Hkk0 & Hkblk & _). cbn [fst snd] in Hkk0, Hkblk.
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ GAR Hkblk) as (_ & Hk4096 & Hkce & _).
pose proof (eh_blk32 B ARx SK HYP _ _ _ _ _ _ _ _ GAR Hkblk) as Hk32.
assert (Hkreq : req_size (kk + cf_head) = kk + cf_head) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
destruct HKB as (HKF & HKG).
assert (HKNZ : Forall (fun c => c <> 0) kl) by (revert HKF; apply Forall_impl; intros c Hc; lia).
(* the scratch: its block *)
pose proof HSINB as (sb & sm & Hsin & Hsb1 & Hsb2 & Hsb3).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ GAR Hsin) as (_ & Hs4096 & _ & _).
pose proof HWD as (_ & HWD1 & _).
remember (Z.of_nat (length kl)) as kx eqn:Ekx. remember (Z.of_nat (length sl)) as ky eqn:Eky.
assert (Hky : 0 <= ky <= exv_len E) by (subst ky; unfold exv_len; lia).
assert (Hkx : 0 <= kx) by (subst kx; lia).
destruct (a2_blk_str lyc Sc Hpc Wc memc mdc (x - cf_head) (kk + cf_head) x kx GAR Hkblk ltac:(lia) ltac:(lia) ltac:(lia))
  as (KA8 & KTL).
destruct (a2_blk_str lyc Sc Hpc Wc memc mdc sb sm (e_scr E) ky GAR Hsin ltac:(lia) ltac:(lia) ltac:(lia))
  as (SA8 & STL).
destruct (exv_sh_lam B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
  x kk x (kx + 1) GAR HLED HinL ltac:(lia) ltac:(lia) ltac:(lia)) as (KRA & KHV).
assert (HSIB : prhex_inblk B lyc Sc Hpc (e_scr E) (ky + 1)).
{ exists sb, sm. split; [exact Hsin|]. split; [lia|]. split; [lia | exact Hsb3]. }
destruct (exv_sh_blk B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
  (e_scr E) (ky + 1) GAR HLED HSIB ltac:(lia)) as (SRA & SHV).
assert (HKG' : garr8 rsegs (mrestrict (w_H Wc) memc) x (kl ++ [0])) by exact HKG.
assert (HSB' : garr8 rsegs (mrestrict (w_H Wc) memc) (e_scr E) (sl ++ [0])) by exact HSB.
assert (KSRC : forall a, x <= a < x + (kx + 1) -> aview rsegs (w_H Wc) memc a <> None).
{ intros a Ha. replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
  rewrite (a2_aview_garr8 _ _ _ _ _ HKG') by (rewrite length_app; cbn; lia). discriminate. }
assert (SSRC : forall a, e_scr E <= a < e_scr E + (ky + 1) -> aview rsegs (w_H Wc) memc a <> None).
{ intros a Ha. replace a with (e_scr E + Z.of_nat (Z.to_nat (a - e_scr E))) by lia.
  rewrite (a2_aview_garr8 _ _ _ _ _ HSB') by (rewrite length_app; cbn; lia). discriminate. }
unfold cfg_at at 1.
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_strcmp_at_xrom (SK := SK) rsegs B prh_pst ARx B_prog_relro_lo B_prog_relro_hi LAWS
    B_prog_segs_low A2_CMP (eh_strcmp B ARx SK HYP fx)
    Wc regs memc (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    [(1, pos)] lyc Sc Hpc mdc k x (e_scr E) kx ky (exv_s1 E - (exv_sp E + e_d E)) (Z_to_bv 64 ret) HJ H10 H11).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite U2. lia.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact H1.
  - exact Hret.
  - subst kx. exact (a2_first_byte Wc memc x kl HKG' HKNZ).
  - subst ky. exact (a2_first_byte Wc memc (e_scr E) sl HSB' HSNZ).
  - intros a Ha. split; [exact (KSRC a Ha) | rewrite U2; lia].
  - intros a Ha. split; [exact (SSRC a Ha) | rewrite U2; lia].
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact KA8.
  - exact SA8.
  - exact KRA.
  - exact KHV.
  - exact SRA.
  - exact SHV.
  - exact KTL.
  - exact STL.
  - exact HROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HPR & Hv & Hcmp & Hfr & Hpres & HMN2).
replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) in Hfr by lia.
rewrite HES in Hfr.
assert (HBs2 : EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs2 mem2 md2 k pos).
{ apply (KRUN fx E lyc Sc Hpc Wc regs memc mdc k pos regs2 mem2 md2 HP HBs HJ2); [| exact Hpres | |].
  - intros a Ha Hn _ _. apply Hfr; [exact Ha|]. intros Hw. apply Hn. lia.
  - intros H0. exact (HMN2 (proj2 HROOM H0)).
  - exact (a2_bregs_of_preserved regs regs2 HPR). }
apply (HK regs2 mem2 md2 v HBs2 HPR Hfr Hv).
rewrite Hcmp. subst kx ky. exact (a2_str_eq Wc memc x (e_scr E) kl sl HKG' HSB').
Qed.
(* bytes kept: a NUL-terminated string read through aview *)
Lemma a2_garr8_kept : forall H H' m m' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview rsegs H' m' a = aview rsegs H m a) ->
  garr8 rsegs (mrestrict H m) p l -> garr8 rsegs (mrestrict H' m') p l.
Proof.
intros H H' m m' p l HK HG j Hj. destruct (HG j Hj) as (Hv & Hr). split; [|exact Hr].
apply (YC88.val_mem_aview_kept_x rsegs H H' m m'); [|exact Hv].
intros a Ha. apply HK. change (Z.of_nat 1) with 1 in Ha. lia.
Qed.

(* a Lam block: inside the application range, apart from the shadow band *)
Lemma a2_lam_blk : forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (b, m) Lam ->
  4096 <= b /\ b + m <= alloc_ceiling /\
  (forall z, b <= z < b + m -> ~ (SHADOW_OFF <= z < SHADOW_OFF + 17592186044416)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
pose proof HLED as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
destruct (HBL (b, m) Hin) as (Hm0 & Hblk & _). cbn [fst snd] in Hm0, Hblk.
destruct (alx_blocks rsegs B ARx LAWS ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hblk)
  as (_ & H4096 & Hce & Happ & _).
assert (Hrq : m + cf_head <= req_size (m + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
split; [clear - H4096 CH0; lia|]. split; [clear - Hce Hrq; lia|].
intros z Hz.
destruct (in_app_addr (b - cf_head) (req_size (m + cf_head)) z Happ ltac:(clear - Hz Hrq CH0 Hm0; lia)) as (Ha1 & Ha2).
unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. clear - Ha1 Ha2. lia.
Qed.

(* the parent node: in the application range, apart from the shadow band, from ex_value's stack window and from the
   cursor; 8-aligned, addressable *)
Lemma a2_node : forall E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  4096 <= e_v E /\ e_v E + 56 <= 2 ^ 47 /\ e_v E mod 8 = 0 /\
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_v E) 56 /\
  (forall z, e_v E <= z < e_v E + 56 -> ~ (SHADOW_OFF <= z < SHADOW_OFF + 17592186044416) /\
     ~ (exv_sp E - exv_STK E <= z < exv_sp E) /\ ~ (e_q E <= z < e_q E + 40)).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos HP HB Hv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (a2_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & (G8a & G8b) & G9 & G10 & G11 & G12 & G13 & G14 & G15 & GAR & _).
pose proof HP as HP'. unfold EXV_PRE in HP'. cbv zeta in HP'.
destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PV & _).
destruct PV as [PV | (_ & _ & PDJ)]; [exfalso; exact (Hv PV)|].
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & HLED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & HTREE).
destruct HTREE as [HT0 | (Hnd & Hhome & Hra & _)]; [exfalso; exact (Hv HT0)|].
destruct (exvl_node_hdr _ _ _ _ _ Hnd) as (num & str & kids & keys & cap & Hh & _).
destruct Hh as ((Hal & _) & _).
assert (HALL : (4096 <= e_v E /\ e_v E + 56 <= 2 ^ 47) /\
  (forall z, e_v E <= z < e_v E + 56 -> ~ (SHADOW_OFF <= z < SHADOW_OFF + 17592186044416))).
{ destruct Hhome as [(b & m & Hin & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
  - destruct (a2_lam_blk lyc Sc Hpc Wc memc mdc _ _ _ _ _ _ _ b m GAR HLED Hin) as (L1 & L2 & L3).
    split; [clear - H1 H2 L1 L2 C1; lia|].
    intros z Hz. apply L3. clear - Hz H1 H2. lia.
  - destruct (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' GAR Hin) as (F1 & F2 & F3).
    pose proof (fs_frame_bytes_nonneg cid) as FB.
    split; [clear - H1 H2 F1 F2 FB C1; lia|].
    intros z Hz.
    destruct (in_app_addr (frame_addr lyc cid pos') (fs_frame_bytes cid) z F3 ltac:(clear - Hz H1 H2; lia))
      as (Ha1 & Ha2).
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. clear - Ha1 Ha2. lia.
  - rewrite G14 in H1. split; [clear - H1 H2 G1 G6 G8a G13 C1; lia|].
    intros z Hz. unfold SHADOW_OFF. clear - H1 Hz G1 G8a G13 C1. lia. }
split; [exact (proj1 (proj1 HALL))|]. split; [exact (proj2 (proj1 HALL))|]. split; [exact Hal|].
split; [exact Hra|].
intros z Hz. split; [exact (proj2 HALL z Hz)|].
destruct (PDJ z ltac:(left; clear - Hz; lia)) as (_ & Hq & Hstk & _). split; [exact Hstk | exact Hq].
Qed.

(* an object's key i: the keys word, the slot, the key string *)
Lemma a2_key : forall E lyc Sc Hpc Wc regs memc mdc k pos (ms : list (list Z * PjTree.jv)) (i : nat),
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  e_t E = PjTree.JObj ms -> (i < length ms)%nat ->
  exists keys x kk,
    val_mem rsegs (mrestrict (w_H Wc) memc) (e_v E + 32) 8 keys /\ 0 <= keys < 2 ^ 64 /\ keys mod 8 = 0 /\
    4096 <= keys /\ keys + 8 * Z.of_nat (length ms) <= alloc_ceiling /\
    range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat i) 8 /\
    (forall z, keys + 8 * Z.of_nat i <= z < keys + 8 * Z.of_nat i + 8 ->
       ~ (SHADOW_OFF <= z < SHADOW_OFF + 17592186044416)) /\
    val_mem rsegs (mrestrict (w_H Wc) memc) (keys + 8 * Z.of_nat i) 8 x /\ 0 <= x < 2 ^ 64 /\
    In (x, kk) (e_Lam E) /\ 4096 <= x /\ x + kk <= alloc_ceiling /\
    Z.of_nat (length (fst (nth i ms ([], PjTree.JNull)))) + 1 <= kk /\
    PRH_Reader.pj_cbytesR rsegs (mrestrict (w_H Wc) memc) x (fst (nth i ms ([], PjTree.JNull))).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos ms i HP HB Hv Et Hi.
pose proof (a2_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & GAR & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & HLED & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & HTREE).
destruct HTREE as [HT0 | (Hnd & _ & _ & _)]; [exfalso; exact (Hv HT0)|].
rewrite Et in Hnd.
destruct (exvl_node_key _ _ _ _ _ i Hnd Hi) as (keys & cap & x & kk & (Hkr & Hkeys) & Hcap & Hlen & Hkl & _
  & (Hxr & Hx) & (Hxl & Hxk & Hxb)).
unfold prh_lin in Hkl, Hxl.
destruct (a2_lam_blk lyc Sc Hpc Wc memc mdc _ _ _ _ _ _ _ keys (8 * cap) GAR HLED Hkl) as (K1 & K2 & K3).
assert (K8 : keys mod 8 = 0).
{ pose proof HLED as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
  destruct (exvl_lam_rng B ARx SK HYP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GAR HLED Hkl) as (_ & _ & K16).
  rewrite (Z.div_mod keys 16) by lia. rewrite K16, Z.add_0_r.
  replace (16 * (keys / 16)) with ((2 * (keys / 16)) * 8) by lia. apply Z_mod_mult. }
exists keys, x, kk.
split; [exact Hkeys|]. split; [exact Hkr|]. split; [exact K8|]. split; [lia|]. split; [lia|].
split.
{ apply (proj1 (exv_sh_lam B ARx SK HYP lyc Sc Hpc Wc memc mdc (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
    keys (8 * cap) (keys + 8 * Z.of_nat i) 8 GAR HLED Hkl ltac:(lia) ltac:(lia) ltac:(lia))). }
split; [intros z Hz; apply K3; lia|].
destruct (a2_lam_blk lyc Sc Hpc Wc memc mdc _ _ _ _ _ _ _ x kk GAR HLED Hxl) as (X1 & X2 & _).
split; [exact Hx|]. split; [exact Hxr|]. split; [exact Hxl|]. split; [exact X1|]. split; [exact X2|].
split; [exact Hxk | exact (proj2 Hxb)].
Qed.

(* the scratch: inside a harness block, below alloc_ceiling *)
Lemma a2_scr : forall E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  4096 <= e_scr E /\ e_scr E + exv_len E + 1 <= alloc_ceiling.
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos HP HB.
pose proof (a2_geom E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & GAR & _).
pose proof HB as HB'. unfold EXB in HB'. cbv zeta in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HSINB & _).
destruct HSINB as (sb & sm & Hsin & Hsb1 & Hsb2 & _).
destruct (alx_blocks rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc sb sm GAR Hsin) as (_ & H4096 & Hce & _).
assert (Hrq : sm <= req_size sm) by (unfold req_size; destruct (Z.eqb_spec sm 0); lia).
split; lia.
Qed.
End a.
