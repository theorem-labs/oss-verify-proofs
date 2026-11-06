(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_free's image-B walk (fuzz_preset asan-ubsan, B 0x86a24; lib/B/Prog/pj_free_defs.v), the
   ENTRY segment: from tpj_free_specO's premises (pf_pre) at the entry to the cuts
     v = NULL                     -> pf_EP (+0x1a8): nothing freed, the post holds;
     v <> NULL, n = 0             -> pf_LX (+0x14c): no slot to free;
     v <> NULL, n > 0             -> pf_LH (+0xa8) at slot 0.
   The body walked (whole-program listing lib/B/Listing_prog.v, PA := PI_prog_B, engine YC80x / YC1fPx over YCbqG's
   journal at the caller-window widened window (STK_pj_free n + d) (sp0 + d), YCbqGcallW.v ajournal_x_init_WR), at the
   walk's relation wle' SEGS RZ_cf (pj_free_defs.v): the R runners (YC1fPx paj_run_x_invR / paj_run_to_x_invR,
   YSRrG.paj_branchR) with the journal at it, concluding SRr' SEGS RZ_cf:
     +0x000 .. +0x034  sp -= 128; ra, s0 .. s11 saved at sp+120 .. sp+24 (the frame region, written over
                       [sp0 - 120, sp0); the slot [sp0 - 128, sp0 - 120) is never written)
     +0x038            beqz a0: the engine stops; the NULL arm (v = 0, the premise's first disjunct) jumps to +0x1a8;
                       the other is refuted by v's premise
     +0x03c .. +0x084  (v <> 0) s0 := v; the UBSan alignment check (v mod 8 = 0: atom 10's alignment fact); s7 := the
                       shadow offset through the GOT slot and the cell (got_regionP / bcell_regionP, PALib); the ASan
                       check of v+40 (shadow entry mkSHE 10 0 56: v's 56 bytes addressable, prhPj_slot); n := v->n
                       (atom 33); s3 := v+24, s1 := v+32 and their shadow indices spilled at sp+8 / sp+16; beqz n
     +0x088 .. +0x0a4  (n <> 0) s8 = s9 = s10 = 0, s11 := sh(v+24), s5 := 56, s4 := sh(v+32): the cut pf_LH at 0.
   proves no function (kind: segment lemma).
   Section hypotheses: AR_laws_x (the engine), PALib (STAND-IN for the unit's image binding of B: the GOT slot of
   the shadow offset and its cell, owner a Theorem Labs lane, the convention of lib/B/Prog/FuzzFreeB.v), and the pure lemma
   pf_oitemsR_frame (the kit's lib/A/PRH_PjOrder.v, cited).
   Numerals: 128 / 120 .. 24 / 8 / 16 (LENGTH: frame and slots), 56 / 40 / 32 / 24 (LENGTH: struct pj and its
   fields), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 47 - 64 / 4096 (LENGTH: shadow span, stack band, the node's range);
   atoms 32 (shadow offset), 33 (n) (DERIVED). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_free_defs pj_free_glue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- the symbolic states at pj_free's entry ---- *)
(* the frame below the entry sp (atom 2), written over [sp0 - 120, sp0) *)
Definition pfn_frame : YP09.region := YP09.mkRegion (Some 2%nat) (- PJF_FR) 0 (- PJF_FR + 8) 0 [].
(* v = NULL: the frame only *)
Definition pf0_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_pf0 : sstate := mkSS PJF_PC sr_atoms [pfn_frame] None pf0_facts.
(* v <> NULL: also v's n word (atom 33), the GOT slot of the shadow offset and its cell (atom 32), v's range and
   alignment, the shadow entry of v's 56 bytes *)
Definition PFN_Bx : sv := SOff 32 0.
Definition PFN_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pfn_vhdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 56 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
Definition pfn_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 64) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_pfn : sstate := mkSS PJF_PC sr_atoms [pfn_frame; pfn_vhdr; got_regionP; bcell_regionP 32] None pfn_facts.
Definition pfn_SH : list shent := [mkSHE 10 0 56].

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* every region of the entry states is the frame (written over [sp0 - 120, sp0)) or read-only *)
Definition pfn_rs (rs : smem) : Prop :=
  forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r \/ (r_base r = Some 2%nat /\ r_wlo r = - PJF_FR + 8 /\ r_whi r = 0).
Ltac pfn_rs_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; vm_compute in Hr;
  repeat (destruct Hr as [<- | Hr]; [first [left; vm_compute; congruence | right; repeat split; reflexivity] |]);
  destruct Hr.
Lemma pfn_awr_ok : forall E rs STK sp0 d FP bl0 blc ly own,
  pfn_rs rs -> bv_unsigned (ew E 2) = sp0 -> PJF_FR <= STK -> 0 <= d ->
  awr_ok E rs (STK + d) (sp0 + d) FP bl0 blc ly own.
Proof.
intros E rs STK sp0 d FP bl0 blc ly own Hrs Hsp HS Hd a (r & Hin & Hr).
destruct (Hrs r Hin) as [Hw | (Hb & Hl & Hh)]; [lia|].
rewrite Hb, Hl, Hh in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. unfold PJF_FR in *. left. lia.
Qed.
Lemma pfn_frame_keep : forall (Wx : world SEGS) E rs (m m' : word -> option byte) sp0,
  pfn_rs rs -> bv_unsigned (ew E 2) = sp0 ->
  frame_of E rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - PJF_FR + 8 <= a < sp0) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E rs m m' sp0 Hrs Hsp HF a Ha Hn. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr). destruct (Hrs r Hin) as [Hw | (Hb & Hl & Hh)]; [lia|].
rewrite Hb, Hl, Hh in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. unfold PJF_FR in *. lia.
Qed.

(* ---- v's node at the entry: pj_foR's witnesses ---- *)
Lemma pf_node_of_pre : forall PB FX CTX0 en, pf_pre B ARx PB FX CTX0 en -> fe_v en <> 0 -> exists nd, pf_node en nd.
Proof.
intros PB FX CTX0 en HPRE Hv.
destruct HPRE as (_ & _ & _ & _ & _ & [(Hv0 & _) | (_ & _ & HFO & _)] & _); [exfalso; exact (Hv Hv0)|].
destruct (fe_n en) as [|d'] eqn:En; cbn [pj_foR] in HFO;
  destruct HFO as (HND & Hap & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
    Hhdr & HS & HK & HY & HP & HPi & HF);
  exists (MkPfNode ty num str kids keys n cap ks Ds Dk Dy Di Fi); unfold pf_node, fn_own; cbn [fn_ty fn_num fn_str
    fn_kids fn_keys fn_n fn_cap fn_ks fn_Ds fn_Dk fn_Dy fn_Di fn_Fi]; rewrite En;
  repeat (split; [assumption|]); exact HPi.
Qed.

(* ---- the saved words of the prologue, read off a seated state's frame chunks ---- *)
Lemma pfn_saved : forall E ss ms regs sp0,
  st_ok_pi SEGS VAL E ss ms -> bv_unsigned (ew E 2) = sp0 ->
  (forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r) ->
  (forall r o, In (r, o) PJF_SAVED ->
     pfg_cv (ss_mem ss) 2 (o - PJF_FR) 8 = Some (YP09.mkChunk (o - PJF_FR) (CVal 8 (SOff (Z.to_nat r) 0)))) ->
  forall r o, In (r, o) PJF_SAVED -> val_mem SEGS (ms_mem ms) (sp0 - PJF_FR + o) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros E ss ms regs sp0 HS Hsp Er HC r o Hro.
assert (Hr : (Z.to_nat r < 32)%nat /\ Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r) /\ 0 <= o < 128).
{ cbn [PJF_SAVED In] in Hro.
  repeat (destruct Hro as [Hro | Hro];
    [injection Hro as <- <-; split; [cbv; lia | split; [vm_compute; reflexivity | lia]] |]).
  destruct Hro. }
destruct Hr as (Hrn & Hru & Ho).
apply (pfg_val E ss ms 2 (o - PJF_FR) 8 (SOff (Z.to_nat r) 0) _ sp0 _ HS (HC r o Hro) Hsp).
- unfold PJF_FR. lia.
- rewrite U_SOff, (Er _ _ Hrn Hru), Z.add_0_r. apply zcanon_id.
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Rr. unfold bv_modulus in Rr. unfold M64. exact Rr.
- cbn. lia.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Rr. unfold bv_modulus in Rr. cbn in Rr |- *. lia.
Qed.

(* ---- the frame at a cut after the prologue, from what the entry stretches leave (the journal at any R) ---- *)
Lemma pfn_frame_ok : forall (R : world SEGS -> world SEGS -> Prop) PB FX CTX0 en rg mm dd,
  pf_pre B ARx PB FX CTX0 en ->
  ajournal_xR (SK := SK) SEGS B PST ARx R (STK_pj_free (fe_n en) + fe_d en) (fe_sp0 en + fe_d en) (fe_FP en)
    (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) (fe_mem en) (fe_md en) [] (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en)
    mm dd 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - PJF_FR + 8 <= a < fe_sp0 en) ->
     aview SEGS (w_H (fe_W en)) mm a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) ->
  spZ rg = fe_sp1 en ->
  (forall r o, In (r, o) PJF_SAVED ->
     val_mem SEGS (rdW (fe_W en) mm) (fe_sp1 en + o) 8 (bv_unsigned (getr (fe_regs en) (Z_to_bv 5 r)))) ->
  getr rg 3 = getr (fe_regs en) 3 -> getr rg 4 = getr (fe_regs en) 4 ->
  (YAkMemnorm.memnorm SEGS (fe_mem en) -> YAkMemnorm.memnorm SEGS mm) ->
  pf_frameR (SK := SK) B ARx R en (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) rg mm dd 0.
Proof.
intros R PB FX CTX0 en rg mm dd HPRE HJ KALL Hsp HSV H3 H4 HMN.
destruct HPRE as (HFPRE & _ & _ & _ & HWIN & _).
pose proof HFPRE as (HAFN & HROD & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (pfg_stk (fe_n en)) as ESTK.
pose proof (ajxR_pres HJ) as HpresJ.
pose proof (YM05.alloc_ceiling_value) as HAC.
pose proof (bv_unsigned_in_range 64 (getr (fe_regs en) 2)) as Rsp. unfold bv_modulus in Rsp. cbn [Z.of_N] in Rsp.
unfold pf_frameR, fe_sp1, fe_sp0, PJF_FR, spZ in *.
split; [exact HJ|].
split; [intros a Ha _; apply KALL; lia|].
split; [exact Hsp|].
split; [exact HSV|].
split; [intros a Ha; apply HpresJ; rewrite ESTK; lia|].
split; [exact H3|]. split; [exact H4|].
split; [|exact HMN].
intros a Hro Hno Herr.
assert (Hi : in_img SEGS a).
{ destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
pose proof (Hsegs a Hi) as Hlo.
rewrite KALL; [exact (HROD a Hro Hno Herr) | lia | lia].
Qed.

(* ---- the ledger at a cut after the prologue: the statics and the heads lie below the frame ---- *)
Lemma pfn_ledger_ok : forall PB FX CTX0 en mm,
  pf_pre B ARx PB FX CTX0 en ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - PJF_FR + 8 <= a < fe_sp0 en) ->
     aview SEGS (w_H (fe_W en)) mm a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) ->
  prh_ledger (PA := PA) B (fe_ly en) (fe_S en) (fe_Hp en) (fe_W en) mm (fe_Lam en)
    (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en).
Proof.
intros PB FX CTX0 en mm HPRE KALL.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & HLED).
pose proof HFPRE as (HAFN & _ & _).
pose proof HAFN as (HAR & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pfg_stk (fe_n en)) as ESTK.
pose proof (@cf_head_nonneg cp) as Hc0.
unfold fe_sp0, PJF_FR in *.
apply (prh_ledger_kept_aview B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED).
- intros a Ha. pose proof (pst_in_img_B a Ha) as Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hlo.
  apply KALL; lia.
- intros a k i Hin Hi.
  destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hin) as (Hk0 & Ha & Hak & _).
  apply KALL; rewrite ?ESTK in *; lia.
- intros a k _ H. exact H.
- apply Permutation_refl.
Qed.

(* ---- the image's objects (FuzzFreeB.v ff_lits / ff_obj_in_img's form): numbers computed from the instance ---- *)
Ltac pfn_lits :=
  repeat match goal with
  | |- context [@pa_val ?r B_prog_listing PI_prog_B ?j] =>
    let v := eval vm_compute in (@pa_val r B_prog_listing PI_prog_B j) in
    change (@pa_val r B_prog_listing PI_prog_B j) with v
  | |- context [B_prog_val ?j] =>
    let v := eval vm_compute in (B_prog_val j) in change (B_prog_val j) with v end.
Ltac pfn_bnd := match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
  let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end; lia.
Lemma pfn_obj_in_img : forall i, (i = 0 \/ i = 12)%nat -> forall x, VAL (A_OBJ i) <= x < VAL (A_OBJ i) + 8 ->
  in_img SEGS x.
Proof.
intros i Hi x Hx. destruct Hi as [ -> | -> ].
- change SEGS with rsegs. unfold in_img. change (VAL (A_OBJ 0)) with (B_prog_val (A_OBJ 0)) in Hx.
  let v := eval vm_compute in (B_prog_val (A_OBJ 0)) in change (B_prog_val (A_OBJ 0)) with v in Hx.
  first [ eexists; split; [do 2 right; left; reflexivity | pfn_bnd] | eexists; split; [do 3 right; left; reflexivity | pfn_bnd] ].
- change SEGS with rsegs. unfold in_img. change (VAL (A_OBJ 12)) with (B_prog_val (A_OBJ 12)) in Hx.
  let v := eval vm_compute in (B_prog_val (A_OBJ 12)) in change (B_prog_val (A_OBJ 12)) with v in Hx.
  first [ eexists; split; [do 2 right; left; reflexivity | pfn_bnd] | eexists; split; [do 3 right; left; reflexivity | pfn_bnd] ].
Qed.

(* ---- the node's facts at a cut after the prologue: nothing below the frame moved ---- *)
Lemma pfn_perm : forall (D Ds Dk Dy Di : list (Z * Z)),
  Permutation D (Ds ++ Dk ++ Dy ++ Di) -> Permutation D ([] ++ Di ++ (Dk ++ Dy ++ Ds)).
Proof.
intros D Ds Dk Dy Di H. cbn [app]. eapply Permutation_trans; [exact H|].
eapply Permutation_trans; [apply Permutation_app_comm|].
rewrite !app_assoc. apply Permutation_app_tail. rewrite <- (app_assoc Di Dk Dy). apply Permutation_app_comm.
Qed.

Lemma pfn_vnode_ok : forall PB FX CTX0 en nd mm,
  pf_pre B ARx PB FX CTX0 en -> pf_node en nd -> fe_v en <> 0 -> fe_v en + 56 <= YM05.alloc_ceiling ->
  ((exists a k, In (a, k) (fe_Lam en) /\ ~ In (a, k) (fe_D en) /\ a <= fe_v en /\ fe_v en + 56 <= a + k) \/
   (exists b m, In (b, m) (ablocks B (fe_ly en) (fe_S en)) /\ ~ In (b + cf_head, m - cf_head) (fe_Lam en) /\
      b <= fe_v en /\ fe_v en + 56 <= b + m) \/
   (exists cid pos, In (cid, pos) (frames (fe_S en)) /\ frame_addr (fe_ly en) cid pos <= fe_v en /\
      fe_v en + 56 <= frame_addr (fe_ly en) cid pos + fs_frame_bytes cid)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - PJF_FR + 8 <= a < fe_sp0 en) ->
     aview SEGS (w_H (fe_W en)) mm a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) ->
  mem_grows (rdW (fe_W en) (fe_mem en)) (rdW (fe_W en) mm) ->
  pf_vnode B en nd (fe_ly en) (fe_S en) (fe_Lam en) (fe_W en) mm.
Proof.
intros PB FX CTX0 en nd mm HPRE HND Hv0 Hv56 Hplace KALL MG.
destruct HPRE as (HFPRE & _ & _ & _ & _ & [(Hv & _) | (_ & Hvc & _ & HSLOT)] & _); [exfalso; exact (Hv0 Hv)|].
pose proof HFPRE as (HAFN & _ & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pfg_stk (fe_n en)) as ESTK.
pose proof HSLOT as (Hv4096 & _ & Hrw & Hamr & Hown & Hvra & Hvhull).
pose proof Hrw as (Hv8 & Hrw56).
pose proof HND as (_ & _ & HHDR & _).
pose proof HHDR as (_ & _ & _ & Hstr & Hkids & Hkeys & Hnn & _).
assert (Kv : forall x, fe_v en <= x < fe_v en + 56 ->
  aview SEGS (w_H (fe_W en)) mm x = aview SEGS (w_H (fe_W en)) (fe_mem en) x).
{ intros x Hx. apply KALL; unfold fe_sp0, PJF_FR in *; rewrite ?ESTK in *; lia. }
assert (Ksh : forall s, kLowMemEnd <= s < kHighShadowEnd ->
  aview SEGS (w_H (fe_W en)) mm s = aview SEGS (w_H (fe_W en)) (fe_mem en) s).
{ intros s Hs. apply KALL; unfold fe_sp0, PJF_FR in *; rewrite ?ESTK in *; lia. }
unfold pf_vnode.
split; [exact Hv4096|]. split; [exact Hv56|]. split; [exact Hv8|]. split; [exact Hamr|].
split; [apply (pfg_u64_keep _ _ _ _ _ _ Hstr); intros x Hx; apply Kv; lia|].
split; [apply (pfg_u64_keep _ _ _ _ _ _ Hkids); intros x Hx; apply Kv; lia|].
split; [apply (pfg_u64_keep _ _ _ _ _ _ Hkeys); intros x Hx; apply Kv; lia|].
split; [apply (pfg_u64_keep _ _ _ _ _ _ Hnn); intros x Hx; apply Kv; lia|].
split; [split; [exact Hv8 | intros x Hx; exact (writable_at_grows SEGS _ _ x MG (Hrw56 x Hx))]|].
split; [intros a Ha; exact (proj1 (Hown a Ha))|].
split.
{ eapply range_addressable_agree; [|exact Hvra]. intros x Hx.
  pose proof (shadow_addr_bounds x ltac:(unfold amem_range in Hamr; lia)) as Hsx. unfold shadow_addr in Hsx.
  unfold shadow_of_addr. apply Ksh. exact Hsx. }
split.
{ intros s Hs. unfold amem_range in Hamr.
  rewrite Ksh by exact (pfg_hull_bounds (fe_v en) 56 s ltac:(lia) ltac:(lia) ltac:(lia) Hs). exact (Hvhull s Hs). }
destruct Hplace as [H1 | [H2 | H3]]; [left; exact H1 | right; left; exact H2 | right; right; left; exact H3].
Qed.

Lemma pfn_items_ok : forall PB FX CTX0 en nd d' mm,
  pf_pre B ARx PB FX CTX0 en -> pf_node en nd -> fe_n en = S d' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - PJF_FR + 8 <= a < fe_sp0 en) ->
     aview SEGS (w_H (fe_W en)) mm a = aview SEGS (w_H (fe_W en)) (fe_mem en) a) ->
  mem_grows (rdW (fe_W en) (fe_mem en)) (rdW (fe_W en) mm) ->
  pf_oitemsR SEGS (rdW (fe_W en) mm) (prh_lin (fe_Lam en)) (pj_foR SEGS (rdW (fe_W en) mm) (prh_lin (fe_Lam en)) d')
    (fn_ks nd) (fn_kids nd + 56 * 0) (fn_keys nd + 8 * 0) (Z.to_nat (fn_n nd - 0)) (fn_Di nd) (fn_Fi nd).
Proof.
intros PB FX CTX0 en nd d' mm HPRE HND Hn KALL MG.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & HLED).
pose proof HFPRE as (HAFN & _ & _).
pose proof HAFN as (HAR & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (pfg_stk (fe_n en)) as ESTK.
pose proof HND as (_ & _ & HHDR & _ & HKIDS & HKEYS & _ & _ & HITEMS).
rewrite Hn in HITEMS.
pose proof HHDR as (_ & _ & _ & _ & _ & _ & Hnn & _).
replace (fn_kids nd + 56 * 0) with (fn_kids nd) by lia. replace (fn_keys nd + 8 * 0) with (fn_keys nd) by lia.
replace (fn_n nd - 0) with (fn_n nd) by lia.
(* every byte of the slots' footprint lies in a harness block of the entry, below alloc_ceiling *)
assert (Hlow : forall a k x, In (a, k) (fe_Lam en) -> a <= x < a + k ->
  aview SEGS (w_H (fe_W en)) mm x = aview SEGS (w_H (fe_W en)) (fe_mem en) x).
{ intros a k x Hin Hx.
  destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hin) as (Hk0 & Ha0 & Hak & _).
  pose proof (@cf_head_nonneg cp) as Hc0.
  apply KALL; unfold fe_sp0, PJF_FR in *; rewrite ?ESTK in *; lia. }
apply (pf_oitemsR_frame SEGS d' _ _ (prh_lin (fe_Lam en)) (prh_lin (fe_Lam en)) _ _ _ _ _ _ HITEMS).
- intros x k Hin. exact (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HITEMS x k Hin).
- apply (pfg_agree _ _ _ _ _ MG). intros x [Hx | [(Hks & Hx) | ((a & k) & Hin & Hh)]].
  + destruct HKIDS as [(Hk0 & Hn0 & _) | (kk & Hkk & Hkn & _)].
    * rewrite Hn0 in Hx. cbn in Hx. lia.
    * apply (Hlow (fn_kids nd) kk x Hkk). pose proof (proj1 Hnn). lia.
  + destruct HKEYS as [(_ & Hks' & _) | (_ & ky & Hky & Hkn & _)]; [congruence|].
    apply (Hlow (fn_keys nd) ky x Hky). pose proof (proj1 Hnn). lia.
  + apply (Hlow a k x (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HITEMS a k Hin)). unfold pj_holdsR in Hh. cbn in Hh. lia.
Qed.

(* ---- THE SEGMENT ---- *)
(* the loop continuation is asked of THIS entry only: the top theorem's induction on the depth gives it from the
   children's text *)
Theorem pfs_entry_holds : forall PB FX CTX0,
  pfs_EP (SK := SK) B ARx FX -> pfs_LX (SK := SK) B ARx PB FX CTX0 ->
  forall en, pf_pre B ARx PB FX CTX0 en ->
  (forall nd d' ly S Hp W regs mem md k, pf_node en nd ->
     pf_LH (SK := SK) B ARx FX en nd d' 0 ly S Hp W regs mem md k ->
     SRr' SEGS RZ_cf W (pf_cfg PJF_LH regs mem md) (pf_FIN (SK := SK) B ARx FX en)) ->
  SRr' SEGS RZ_cf (fe_W en) (cfg_at SEGS (SIGMA AS_pj_free) (fe_regs en) (fe_mem en) (fe_md en))
    (pf_FIN (SK := SK) B ARx FX en).
Proof.
intros PB FX CTX0 SEP SLX en HPRE SLH. pose proof HPRE as HPRE0.
(* the walk's relation, its two laws *)
unfold SRr' in SLH |- *.
set (R := wle' SEGS RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS RZ_cf).
destruct en as [ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran most own n].
unfold pf_pre in HPRE.
cbn [fe_ly fe_S fe_Hp fe_W fe_regs fe_mem fe_md fe_ch fe_d fe_v fe_D fe_F fe_Lam fe_peak fe_cnt fe_fail fe_ran fe_most fe_own fe_n]
  in HPRE |- *.
set (en := MkPfEnt ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran most own n) in *.
destruct HPRE as (HFPRE & HUNIV & HROOM & H10 & HWIN & HCASE & HSAFE & HLED).
pose proof HFPRE as (HAFN & HROD & HSTKHI).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof (pfg_stk n) as ESTK.
assert (Hes : ESTACK = 4096) by reflexivity.
set (sp0 := spZ regs) in *.
pose proof (ajournal_x_init_WR (SK := SK) SEGS B PST ARx R Rr (STK_pj_free n) d (fe_FP en) ly S Hp W regs mem md ch
  HAFN HWIN) as HJ.
(* the memnorm keep from the entry memory, carried by the _inv runners (YSRrMemnorm.v, YC1fPx.v) *)
pose (PM := fun m : word -> option byte => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
pose (PMLAW := srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)).
assert (HPM : PM mem) by (intros H; exact H).
pose (RUN := @paj_run_x_invR fx rc SK B_prog_listing PL PA B PST ARx hl LAWS PM PMLAW R Rr Rt).
pose (RUNTO := @paj_run_to_x_invR fx rc SK B_prog_listing PL PA B PST ARx hl LAWS PM PMLAW R Rr Rt).
pose (BR := paj_branchR (fx := fx) (rc := rc) (L := B_prog_listing) (PI := PA) R).
assert (HFRle : PJF_FR <= STK_pj_free n) by (rewrite ESTK; unfold PJF_FR; lia).
unfold cfg_at. change (w64 (SIGMA AS_pj_free)) with (Z_to_bv 64 (BASE + PJF_PC)).
destruct HCASE as [(Hv0 & HD0 & HF0) | (Hv0 & Hvc & HFO & HSLOT)].
- (* ======== v = NULL ======== *)
  subst v D F.
  remember (@Eimg _ B_prog_listing PA (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
  { intros n0 r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
  assert (E2 : ew E 2 = getr regs 2) by (apply Er; [lia | reflexivity]).
  assert (E10 : ew E 10 = getr regs 10) by (apply Er; [lia | reflexivity]).
  assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (subst E; split; [intros n0 Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HS : st_ok_pi SEGS VAL E ss_pf0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PJF_PC)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_pf0. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pfn_frame, PJF_FR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite ESTK. lia.
    - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    - split; [|split; [exact I | exact I]].
      cbn [pf0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [exact Hal16 | lia]. }
  assert (SHOK : sh_ok SEGS PFN_Bx [] E (mrestrict (w_H W) mem)) by constructor.
  clear HE.
  (* +0x000 .. +0x034: the frame and the saves; stop at beqz a0 *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PFN_Bspan;
    [apply (pfn_awr_ok E _ (STK_pj_free n) sp0 d); [pfn_rs_tac | exact Usp | exact HFRle | exact Hd0] |].
  clear HF. rename HG into G1.
  pose proof (fun Hrs => pfn_frame_keep W E _ mem _ sp0 Hrs Usp HFr) as K1. specialize (K1 ltac:(pfn_rs_tac)). clear HFr.
  psrr_branch_tok RUN BR HS SHOK PFN_Bspan.
  2:{ (* beqz not taken: a0 is 0 *)
    exfalso. rewrite branch_eq_U, (U_atom E 10 0), U_SLit in Hc by (first [lia | rewrite E10, H10; reflexivity]).
    vm_compute in Hc. discriminate Hc. }
  (* the cut pf_EP at +0x1a8 *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PFN_Bspan PJF_EP;
    [apply (pfn_awr_ok E _ (STK_pj_free n) sp0 d); [pfn_rs_tac | exact Usp | exact HFRle | exact Hd0] |].
  clear HF. rename HG into G2.
  pose proof (fun Hrs => pfn_frame_keep W E _ _ _ sp0 Hrs Usp HFr) as K2. specialize (K2 ltac:(pfn_rs_tac)). clear HFr.
  prreg HS (2%bv : bv 5) R2.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs [] [3%bv; 4%bv] HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pose proof (pfn_saved E _ _ regs sp0 HS Usp Er) as HSV.
  specialize (HSV ltac:(intros r o Hro; cbn [PJF_SAVED In] in Hro;
    repeat (destruct Hro as [Hro | Hro]; [injection Hro as <- <-; vm_compute; reflexivity |]); destruct Hro)).
  pmkst HS.
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?pc)) ?mm _; cfg_model := ?dd |} _ =>
    replace pc with PJF_EP by (vm_compute; reflexivity);
    apply (SEP PB CTX0 en ly S Hp W rg mm dd 0 HPRE0) end.
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - PJF_FR + 8 <= a < fe_sp0 en) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hn. cbn [fe_sp0 en fe_regs] in Hn. fold sp0 in Hn. rewrite K2, K1 by assumption. reflexivity. }
  split.
  + apply (pfn_frame_ok R PB FX CTX0 en _ _ _ HPRE0 HJ KALL).
    * unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by lia.
      unfold fe_sp1, fe_sp0, PJF_FR. cbn [en fe_regs]. fold sp0. lia.
    * intros r o Hro. unfold fe_sp1, fe_sp0. cbn [en fe_regs]. fold sp0. exact (HSV r o Hro).
    * exact (KR 3%bv ltac:(left; reflexivity)).
    * exact (KR 4%bv ltac:(right; left; reflexivity)).
    * exact HPM.
  + split; [|apply pfr_refl].
    split; [exact HROOM|]. exists Lam.
    split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
    split; [exact (pfn_ledger_ok PB FX CTX0 en _ HPRE0 KALL)|].
    split; [intros _; split; [reflexivity | split; reflexivity]|].
    intros Hn0. exfalso. exact (Hn0 eq_refl).
- (* ======== v <> NULL ======== *)
  destruct (pf_node_of_pre PB FX CTX0 en HPRE0 Hv0) as [nd HND].
  pose proof HND as (HNDD & HAPD & HHDR & HSTR & HKIDS & HKEYS & HPD & HFD & HITEMS).
  destruct nd as [ty num str kids keys nn cap ks Ds Dk Dy Di Fi].
  cbn [fn_ty fn_num fn_str fn_kids fn_keys fn_n fn_cap fn_ks fn_Ds fn_Dk fn_Dy fn_Di fn_Fi en fe_W fe_mem fe_Lam fe_D
    fe_v fe_F fe_n fn_own] in HNDD, HAPD, HHDR, HSTR, HKIDS, HKEYS, HPD, HFD, HITEMS.
  pose proof HHDR as (HRW & Hty & Hnum & Hstr & Hkids & Hkeys & Hnn & Hcap).
  pose proof HSLOT as (Hv4096 & Hat & Hrw & Hamr & Hown & Hvra & Hvhull).
  pose proof Hrw as (Hv8 & _).
  pose proof (YM05.alloc_ceiling_value) as HAC.
  (* v's place: a harness block that is none of D's, a non-harness live block or a live fake frame (the caller's
     window is above alloc_ceiling) *)
  assert (Hvplace : (exists a k, In (a, k) Lam /\ ~ In (a, k) D /\ a <= v /\ v + 56 <= a + k) \/
    (exists b m, In (b, m) (ablocks B ly S) /\ ~ In (b + cf_head, m - cf_head) Lam /\ b <= v /\ v + 56 <= b + m) \/
    (exists cid pos, In (cid, pos) (frames S) /\
       frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid)).
  { destruct Hat as [(a & k & Hin & Ha & Hk) | [Hb | [Hf | (Hw1 & Hw2)]]].
    - left. exists a, k. split; [exact Hin|]. split; [|lia].
      intros HinD. apply (HAPD (a, k) v HinD); unfold pj_holdsR; cbn [fst snd]; lia.
    - right; left; exact Hb.
    - right; right; exact Hf.
    - exfalso. fold sp0 in Hw1. lia. }
  assert (Hvlow : v + 56 <= YM05.alloc_ceiling /\ forall x, v <= x < v + 56 -> ~ in_img SEGS x).
  { destruct Hvplace as [(a & k & Hin & _ & Ha & Hk) | [(b & m & Hin & _ & Hb & Hm) | (cid & pos & Hin & Hf & Hfm)]].
    - destruct (pfg_lam_blk B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hin) as (Hk0 & Ha0 & Hak & _ & Hab & _).
      pose proof (@cf_head_nonneg cp) as Hc0.
      assert (Hkc : 0 <= k + cf_head) by lia. pose proof (req_size_pos (k + cf_head) Hkc) as [_ Hrq].
      split; [lia|]. intros x Hx. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hab). lia.
    - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & Hc & _).
      assert (Hm0 : 0 <= m) by lia. pose proof (req_size_pos m Hm0) as [_ Hrq].
      split; [lia|]. intros x Hx. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m x HAR Hin). lia.
    - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hc & _).
      split; [lia|]. intros x Hx. apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos x HAR Hin). lia. }
  destruct Hvlow as (Hv56 & Hvimg).
  destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
  assert (Hnn64 : 0 <= nn < 2 ^ 64) by exact (proj1 Hnn).
  remember (@Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 nn])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
  { intros n0 r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
  assert (E2 : ew E 2 = getr regs 2) by (apply Er; [lia | reflexivity]).
  assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite (Er 10%nat 10%bv) by (first [lia | reflexivity]); exact H10).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew E 33 = Z_to_bv 64 nn).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
  assert (Uv : bv_unsigned (ew E 10) = v) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j).
  { intros j Hj. subst E. rewrite Eimg_img by exact Hj. apply unsigned_lit_small. apply pa_val_range. }
  assert (Dimg : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
  { intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
  assert (BV : forall j, (A_TEXT <= j < A_LIM)%nat -> base_val E (Some j) = VAL j)
    by (intros j Hj; cbn [base_val]; apply Uimg; exact Hj).
  assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 nn]) E)
    by (subst E; split; [intros n0 Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  (* the GOT slot and the cell are image objects, apart from v's bytes *)
  pose proof (pfn_obj_in_img 0 (or_introl eq_refl)) as Img0.
  pose proof (pfn_obj_in_img 12 (or_intror eq_refl)) as Img12.
  assert (Dv0 : v + 56 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= v).
  { destruct (Z_le_dec (v + 56) (VAL (A_OBJ 0))) as [H|H]; [left; exact H|].
    destruct (Z_le_dec (VAL (A_OBJ 0) + 8) v) as [H'|H']; [right; exact H'|]. exfalso.
    apply (Hvimg (Z.max v (VAL (A_OBJ 0)))); [lia|]. apply Img0. lia. }
  assert (Dv12 : v + 56 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= v).
  { destruct (Z_le_dec (v + 56) (VAL (A_OBJ 12))) as [H|H]; [left; exact H|].
    destruct (Z_le_dec (VAL (A_OBJ 12) + 8) v) as [H'|H']; [right; exact H'|]. exfalso.
    apply (Hvimg (Z.max v (VAL (A_OBJ 12)))); [lia|]. apply Img12. lia. }
  assert (HS : st_ok_pi SEGS VAL E ss_pfn (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PJF_PC)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_pfn. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold pfn_frame, pfn_vhdr, got_regionP, bcell_regionP, PJF_FR.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
      rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
      + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite ESTK. lia.
      + cbn [base_val]. rewrite Uv. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ _ 40 8 (SOff 33 0) nn);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
        exact (proj2 Hnn).
      + pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 0)). pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)).
        split; [lia|]. split; [pfn_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [apply Dimg; unfold A_OBJ, A_TEXT, A_LIM; lia | lia | lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      + pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)).
        split; [lia|]. split; [pfn_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity
        | unfold SHADOW_OFF; lia | lia |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    - apply pairwise_disjoint_of_extents.
      unfold pfn_frame, pfn_vhdr, got_regionP, bcell_regionP, extent_of_region, PJF_FR.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uv.
      rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 0)). pose proof (@pa_val_range _ B_prog_listing PI_prog_B (A_OBJ 12)).
      pose proof (@pa_segs_low _ _ PA (VAL (A_OBJ 0)) ltac:(apply Img0; lia)) as Lo0.
      pose proof (@pa_segs_low _ _ PA (VAL (A_OBJ 12)) ltac:(apply Img12; lia)) as Lo12.
      pose proof (pal_got_cell B PAL) as HgcD. rewrite ESTK in *. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      unfold pfn_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, Uv, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hal16; try exact Hv8; lia. }
  assert (SHOK : sh_ok SEGS PFN_Bx pfn_SH E (mrestrict (w_H W) mem)).
  { unfold sh_ok, pfn_SH. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) mem E PFN_Bx 10 v 56 v 0 56 Hvra).
    - unfold PFN_Bx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      apply zcanon_id. unfold SHADOW_OFF, M64. lia.
    - rewrite U_SOff, Uv, Z.add_0_r. apply zcanon_id. unfold M64. lia.
    - lia. - lia.
    - intros x Hx. unfold amem_range in Hamr. unfold SHADOW_OFF in *. lia. }
  clear HE.
  (* +0x000 .. +0x084: the frame, the saves, the checks, n, the spills; stop at beqz n *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PFN_Bspan;
    [apply (pfn_awr_ok E _ (STK_pj_free n) sp0 d); [pfn_rs_tac | exact Usp | exact HFRle | exact Hd0] |].
  clear HF. rename HG into G1.
  pose proof (fun Hrs => pfn_frame_keep W E _ mem _ sp0 Hrs Usp HFr) as K1. specialize (K1 ltac:(pfn_rs_tac)). clear HFr.
  (* what both cuts need of the entry: v's place, the node record *)
  set (nd := MkPfNode ty num str kids keys nn cap ks Ds Dk Dy Di Fi) in *.
  assert (Uat : forall c, 0 <= c <= 56 -> U E (SOff 10 c) = v + c).
  { intros c Hc. apply (U_atom_off E 10 v c E10); lia. }
  assert (Ubx : U E (SOff 32 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
  assert (Hvr : 0 <= v < 2 ^ 47) by lia.
  psrr_branch_tok RUN BR HS SHOK PFN_Bspan.
  + (* beqz n taken: n = 0; the cut pf_LX at +0x14c *)
    rewrite branch_eq_U, (U_atom E 33 nn E33 Hnn64), U_SLit in Hc. apply Z.eqb_eq in Hc.
    change (zcanon 0) with 0 in Hc. subst nn.
    assert (HDF : Di = [] /\ Fi = []).
    { destruct n as [|d']; [destruct HITEMS as (_ & HDi & HFi); auto | destruct HITEMS as (HDi & HFi); auto]. }
    destruct HDF as [-> ->].
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PFN_Bspan PJF_LX;
      [apply (pfn_awr_ok E _ (STK_pj_free n) sp0 d); [pfn_rs_tac | exact Usp | exact HFRle | exact Hd0] |].
    clear HF. rename HG into G2.
    pose proof (fun Hrs => pfn_frame_keep W E _ _ _ sp0 Hrs Usp HFr) as K2. specialize (K2 ltac:(pfn_rs_tac)). clear HFr.
    pfg_reg HS (2%bv : bv 5) R2. pfg_reg HS (8%bv : bv 5) R8. pfg_reg HS (9%bv : bv 5) R9. pfg_reg HS (18%bv : bv 5) R18. pfg_reg HS (19%bv : bv 5) R19.
    pfg_reg HS (22%bv : bv 5) R22. pfg_reg HS (23%bv : bv 5) R23.
    pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ [3%bv; 4%bv] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pose proof (pfn_saved E _ _ regs sp0 HS Usp Er) as HSV.
    specialize (HSV ltac:(intros r o Hro; cbn [PJF_SAVED In] in Hro;
      repeat (destruct Hro as [Hro | Hro]; [injection Hro as <- <-; vm_compute; reflexivity |]); destruct Hro)).
    assert (VS8 : val_mem SEGS (rdW W (ms_mem ms0)) (sp0 - PJF_FR + 8) 8 ((v + 24) / 8)).
    { refine (pfg_val E _ _ 2 (-120) 8 (SAlu ALU_SRL (SOff 10 24) (SLit 3)) _ sp0 _ HS _ Usp _ _ _ _).
      - vm_compute. reflexivity.
      - unfold PJF_FR. lia.
      - rewrite pfg_U_srl3, Uat by lia. reflexivity.
      - cbn. lia.
      - cbn. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (VS16 : val_mem SEGS (rdW W (ms_mem ms0)) (sp0 - PJF_FR + 16) 8 ((v + 32) / 8)).
    { refine (pfg_val E _ _ 2 (-112) 8 (SAlu ALU_SRL (SOff 10 32) (SLit 3)) _ sp0 _ HS _ Usp _ _ _ _).
      - vm_compute. reflexivity.
      - unfold PJF_FR. lia.
      - rewrite pfg_U_srl3, Uat by lia. reflexivity.
      - cbn. lia.
      - cbn. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    pmkst HS.
    lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?pc)) ?mm _; cfg_model := ?dd |} _ =>
      replace pc with PJF_LX by (vm_compute; reflexivity);
      apply (SLX en nd ly S Hp W rg mm dd 0 HPRE0 HND) end.
    assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - PJF_FR + 8 <= a < fe_sp0 en) ->
      aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
    { intros a Ha Hn. cbn [fe_sp0 en fe_regs] in Hn. fold sp0 in Hn. rewrite K2, K1 by assumption. reflexivity. }
    assert (MG : mem_grows (rdW W mem) (rdW W (ms_mem ms0))) by (intros x Hx; apply G2, G1, Hx).
    split.
    { apply (pfn_frame_ok R PB FX CTX0 en _ _ _ HPRE0 HJ KALL).
      - unfold spZ at 1. rewrite R2. cbn [sv_denot]. rewrite Usp, unsigned_lit_small by lia.
        unfold fe_sp1, fe_sp0, PJF_FR. cbn [en fe_regs]. fold sp0. lia.
      - intros r o Hro. unfold fe_sp1, fe_sp0. cbn [en fe_regs]. fold sp0. exact (HSV r o Hro).
      - exact (KR 3%bv ltac:(left; reflexivity)).
      - exact (KR 4%bv ltac:(right; left; reflexivity)).
      - exact HPM. }
    split.
    { unfold pf_spill, fe_sp1, fe_sp0. cbn [en fe_regs fe_v]. fold sp0. split; [exact VS8 | exact VS16]. }
    split.
    { unfold pf_vregs. cbn [en fe_v]. unfold w64.
      split; [apply (pfg_reg_of_U E _ _ _ R8); rewrite Uat by lia; lia|].
      split; [apply (pfg_reg_of_U E _ _ _ R9); rewrite Uat by lia; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R18); rewrite Uat by lia; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R19); rewrite Uat by lia; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R23); exact Ubx|].
      apply (pfg_reg_of_U E _ _ _ R22). apply pfg_U_cell; [apply Uat; lia | exact Ubx | lia]. }
    exists [], Lam. split.
    { split; [exact HROOM|]. split; [exact (pfn_ledger_ok PB FX CTX0 en _ HPRE0 KALL)|].
      split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
      cbn [en fe_F fn_own nd fn_Dk fn_Dy fn_Ds]. rewrite HFD. split; [reflexivity | apply pfr_refl]. }
    split.
    { apply (pfn_vnode_ok PB FX CTX0 en nd _ HPRE0 HND Hv0 Hv56 Hvplace KALL MG). }
    cbn [en fe_D fn_own nd fn_Dk fn_Dy fn_Ds app]. pose proof (pfn_perm _ _ _ _ _ HPD) as HP'. exact HP'.
  + (* beqz n not taken: the loop's setup; the cut pf_LH at +0xa8, slot 0 *)
    rewrite branch_eq_U, (U_atom E 33 nn E33 Hnn64), U_SLit in Hc. apply Z.eqb_neq in Hc.
    change (zcanon 0) with 0 in Hc.
    assert (Hd' : exists d', n = Datatypes.S d').
    { destruct n as [|d']; [exfalso; destruct HITEMS as (Hn0 & _); exact (Hc Hn0) | exists d'; reflexivity]. }
    destruct Hd' as [d' En].
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PFN_Bspan PJF_LH;
      [apply (pfn_awr_ok E _ (STK_pj_free n) sp0 d); [pfn_rs_tac | exact Usp | exact HFRle | exact Hd0] |].
    clear HF. rename HG into G2.
    pose proof (fun Hrs => pfn_frame_keep W E _ _ _ sp0 Hrs Usp HFr) as K2. specialize (K2 ltac:(pfn_rs_tac)). clear HFr.
    pfg_reg HS (2%bv : bv 5) R2. pfg_reg HS (8%bv : bv 5) R8. pfg_reg HS (9%bv : bv 5) R9. pfg_reg HS (18%bv : bv 5) R18. pfg_reg HS (19%bv : bv 5) R19.
    pfg_reg HS (20%bv : bv 5) R20. pfg_reg HS (21%bv : bv 5) R21. pfg_reg HS (22%bv : bv 5) R22. pfg_reg HS (23%bv : bv 5) R23.
    pfg_reg HS (24%bv : bv 5) R24. pfg_reg HS (25%bv : bv 5) R25. pfg_reg HS (26%bv : bv 5) R26. pfg_reg HS (27%bv : bv 5) R27.
    pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ [3%bv; 4%bv] HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pose proof (pfn_saved E _ _ regs sp0 HS Usp Er) as HSV.
    specialize (HSV ltac:(intros r o Hro; cbn [PJF_SAVED In] in Hro;
      repeat (destruct Hro as [Hro | Hro]; [injection Hro as <- <-; vm_compute; reflexivity |]); destruct Hro)).
    assert (VS8 : val_mem SEGS (rdW W (ms_mem ms0)) (sp0 - PJF_FR + 8) 8 ((v + 24) / 8)).
    { refine (pfg_val E _ _ 2 (-120) 8 (SAlu ALU_SRL (SOff 10 24) (SLit 3)) _ sp0 _ HS _ Usp _ _ _ _).
      - vm_compute. reflexivity.
      - unfold PJF_FR. lia.
      - rewrite pfg_U_srl3, Uat by lia. reflexivity.
      - cbn. lia.
      - cbn. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (VS16 : val_mem SEGS (rdW W (ms_mem ms0)) (sp0 - PJF_FR + 16) 8 ((v + 32) / 8)).
    { refine (pfg_val E _ _ 2 (-112) 8 (SAlu ALU_SRL (SOff 10 32) (SLit 3)) _ sp0 _ HS _ Usp _ _ _ _).
      - vm_compute. reflexivity.
      - unfold PJF_FR. lia.
      - rewrite pfg_U_srl3, Uat by lia. reflexivity.
      - cbn. lia.
      - cbn. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    pmkst HS.
    lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst ?rg (Z_to_bv 64 (_ + ?pc)) ?mm _; cfg_model := ?dd |} _ =>
      replace pc with PJF_LH by (vm_compute; reflexivity);
      apply (SLH nd d' ly S Hp W rg mm dd 0 HND) end.
    assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (fe_sp0 en - PJF_FR + 8 <= a < fe_sp0 en) ->
      aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
    { intros a Ha Hn. cbn [fe_sp0 en fe_regs] in Hn. fold sp0 in Hn. rewrite K2, K1 by assumption. reflexivity. }
    assert (MG : mem_grows (rdW W mem) (rdW W (ms_mem ms0))) by (intros x Hx; apply G2, G1, Hx).
    split; [cbn [en fe_n]; exact En|].
    split; [cbn [nd fn_n]; lia|].
    split.
    { apply (pfn_frame_ok R PB FX CTX0 en _ _ _ HPRE0 HJ KALL).
      - unfold spZ at 1. rewrite R2. cbn [sv_denot]. rewrite Usp, unsigned_lit_small by lia.
        unfold fe_sp1, fe_sp0, PJF_FR. cbn [en fe_regs]. fold sp0. lia.
      - intros r o Hro. unfold fe_sp1, fe_sp0. cbn [en fe_regs]. fold sp0. exact (HSV r o Hro).
      - exact (KR 3%bv ltac:(left; reflexivity)).
      - exact (KR 4%bv ltac:(right; left; reflexivity)).
      - exact HPM. }
    split.
    { unfold pf_spill, fe_sp1, fe_sp0. cbn [en fe_regs fe_v]. fold sp0. split; [exact VS8 | exact VS16]. }
    split.
    { unfold pf_vregs. cbn [en fe_v]. unfold w64.
      split; [apply (pfg_reg_of_U E _ _ _ R8); rewrite Uat by lia; lia|].
      split; [apply (pfg_reg_of_U E _ _ _ R9); rewrite Uat by lia; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R18); rewrite Uat by lia; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R19); rewrite Uat by lia; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R23); exact Ubx|].
      apply (pfg_reg_of_U E _ _ _ R22). apply pfg_U_cell; [apply Uat; lia | exact Ubx | lia]. }
    split.
    { unfold pf_lregs. cbn [en fe_v]. unfold w64.
      split; [apply (pfg_reg_of_U E _ _ _ R20); apply pfg_U_cell; [apply Uat; lia | exact Ubx | lia]|].
      split; [apply (pfg_reg_of_U E _ _ _ R21); rewrite U_SLit; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R24); rewrite U_SLit; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R25); rewrite U_SLit; reflexivity|].
      split; [apply (pfg_reg_of_U E _ _ _ R26); rewrite U_SLit; reflexivity|].
      apply (pfg_reg_of_U E _ _ _ R27). apply pfg_U_cell; [apply Uat; lia | exact Ubx | lia]. }
    exists [], Lam, Di, Fi. split.
    { split; [exact HROOM|]. split; [exact (pfn_ledger_ok PB FX CTX0 en _ HPRE0 KALL)|].
      split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
      cbn [en fe_F fn_own nd fn_Dk fn_Dy fn_Ds]. rewrite HFD. split; [reflexivity | apply pfr_refl]. }
    split.
    { apply (pfn_vnode_ok PB FX CTX0 en nd _ HPRE0 HND Hv0 Hv56 Hvplace KALL MG). }
    split.
    { cbn [en fe_D fn_own nd fn_Dk fn_Dy fn_Ds]. exact (pfn_perm _ _ _ _ _ HPD). }
    exact (pfn_items_ok PB FX CTX0 en nd d' _ HPRE0 HND En KALL MG).
Qed.
End e.
