(* fuzz_preset, slice S5b, lane PI-key (the S3 walk, a Theorem Labs lane for a Theorem Labs lane): parse_items' OBJECT KEY PATH in image A,
   rows 108..209 of the #102 pin A' disassembly of parse_items (A 0x87440 .. 0x875d8, listing slots 6040 .. 6142),
   the step lemma tvrd_ikey_a CTX of lib/A/VrdIElem.v, over its boundary states vrd_ielem_a / vrd_islot_a /
   vrd_iexit_a.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Every callee (parse_string, fuzz_free) is its record text,
   taken as a named Section hypothesis; every neighbouring segment is a boundary state of VrdIElem.v.
   SET (history): written on a working branch over a working branch 9783bcadf88 and the record texts of
   a working branch b0262503e74 (old pins, image A). NOW: relocated to image A' (asan 1be0f53d, lane
   P102Reloc2, a working branch 43e0d7669c5b) and adapted to the kit reader text (PRH_FnParse.v
   94232293d483, PRH_FnReader.v fb7b12dfa169, PRH_Base.v ee2f5cd7ed35) by lane A2Step on a working branch.
   RE-FIT onto the kit's cut 7cdbb61b5fa0 (lane RItems): the journal at the budget ie_CW E (runs from VrdIElem.vrd_ijrn_base,
   back by vrd_ijrn_unbase), parse_string's budgeted post (VrdArm.vrd_call_Wb_P) and its cursor-set, wild-room and
   per-event live premises, and the batch kit's layer of the boundaries (vk_k1h before the call, vk_jfk after the key, the
   exits' free order).
   Build (route of record, pins102): the internal file zfb-targets.85055e6079bccb28.sh with PAU pau-preset-102 and facts
   8f3e7e1a07f1 - never cb, whose facts predate the A' image.

   THE TWO ARMS AT THE LOOP HEAD (row 108, `beqz s3, +0x198`, s3 = (o ? 1 : 0) by vrd_iregs):
   - ARRAY (o = false): the branch is taken straight to row 210 (slot 6142 = A_ISLOT_SLOT); nothing is read or
     written, and the model's jr_name false y = jret ([], y), so the position moves only its continuation to
     vrd_jval .. [] y. That is vk_arr below.
   - OBJECT (o = true): rows 109..209 (not yet in this file; see the internal file VrdIKey.NEXT.md).

   THE SYMBOLIC STATE OF A STEP THAT TOUCHES NO MEMORY. vk_ss k has no region, no fact and no shadow entry; the
   environment is the position's registers (vk_EI). A run from it writes nothing, so its frame_of keeps every byte
   (vk_frame_none) and the memory after it IS the memory before it.
   Numerals: listing slots (DERIVED, VrdIElem.v), 4 (LENGTH, a slot), 2 ^ 44 (LENGTH, the shadow span). No ADDRESS
   literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdIElem
VrdCurStore VrdIFd VrdArm VrdCallKeep VrdIStep VrdLedgerStep VrdCallPos VrdLedgerEv VrdSlotStore.
(* vrd_ws_mask / vrd_mask_ws: the one white-space mask lemma (a Theorem Labs lane's VrdPro.v) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require VrdPro.
(* the re-hiding move's SRr' / wle' (YA0nH, YSRrG) and preset's zone (YGcfRehidePost.RZ_cf); the threaded hull
   budget *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {HL : Z}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation PLA := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
#[local] Notation VAL := (@pa_val _ A_prog_listing PAI).
#[local] Notation BASE := (@pa_val _ A_prog_listing PAI A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
(* instance facts, as VrdCurStore.v states them: the head width (the kit's prh_head_wide) and alloc.c's statics in
   the image (S1ImgA.v pst_in_img_A); and the generated frame / cursor facts of parse_items (VrdIElem.v's
   vrd_chain_keep_w premises) *)
Variable HW : 8 <= cf_head.
Variable PST_IMG : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.
(* the instance facts IelemE's after-call lemmas take (VrdIStep.v Section S, a Theorem Labs lane's list): the harness-block
   shadow law's head length, the image's zero-shadow alignment, the image shadow's visibility *)
Hypothesis H_HL : HL = cf_head.
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis Hfr144 : pi_frame F_parse_items = 144.
Hypothesis Hs0c : pi_s0cur F_parse_items = Some 0.

(* ---- the symbolic state of a step that touches no memory ---- *)
Definition vk_EI (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PAI (Ereg regs []).
Definition vk_ss (k : nat) : sstate := mkSS (4 * Z.of_nat k) sr_atoms [] None (mkFacts [] [] []).
Definition vk_Bx : sv := SOff 26 0.
Definition vk_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma vk_st_ok : forall (fxP : YK11.FPState) (W : world SEGS) regs mem k,
  st_ok_pi (fx := fxP) SEGS VAL (vk_EI regs) (vk_ss k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS vk_Bx [] (vk_EI regs) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem k.
  split; [|unfold sh_ok; apply Forall_nil].
  rewrite (restrict_mkst_fx (fx := fxP)).
  change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
  unfold vk_ss. apply (pa_entry_st_ok_full (fx := fxP)).
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - exact (conj I (conj I I)).
Qed.

(* a run over a state with no region writes nothing *)
Lemma vk_frame_none : forall E' (m m' : word -> option byte), frame_of E' [] m m' -> m' = m.
Proof.
  intros E' m m' HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & _). destruct Hin.
Qed.

(* the registers of the position after a run that ran no instruction but a branch *)
Lemma vk_regs_kept : forall E' ss ms regs,
  st_ok_pi SEGS VAL E' ss ms -> env_agree 32 (Ereg regs []) E' -> ss_regs ss = sr_atoms ->
  forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r.
Proof.
  intros E' ss ms regs HS HA Hr.
  apply (regs_kept_of_st_ok_pi E' ss ms regs [] _ HS HA). rewrite Hr. reflexivity.
Qed.

(* ---- 1. the ARRAY arm: row 108's branch is taken straight to the value slot ---- *)
Lemma vk_arr_P : forall CTX CTX0 CW E P (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ielem_a B ARx SK E P -> ie_o E = false ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IELEM_SLOT P)
    (fun W2 c2 => (exists P' nm, W2 = ip_W P' /\ c2 = vrd_cfg A_ISLOT_SLOT P' /\ ip_n P' = ip_n P /\
                                 vrd_islot_a B ARx SK E P' nm)
                  /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P Pm PLAW HEN HI Ho HPM.
  pose proof HI as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Hcont & Hcap1 & Hinc & af & HFO & HFL).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ. pose proof HJN as (_ & HJrest).
  destruct (vk_st_ok (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) A_IELEM_SLOT) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (vk_EI (ip_regs P))) by (unfold vk_EI; apply Eimg_env).
  assert (E19 : ew (vk_EI (ip_regs P)) 19 = Z_to_bv 64 0).
  { unfold vk_EI. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat (ip_regs P) [] 19 19%bv eq_refl).
    destruct HRG as (_ & _ & _ & _ & _ & H19 & _). rewrite Ho in H19. exact H19. }
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  psrr_branch_tok RUN BR HS SHOK vk_Bspan.
  - (* taken: s3 = 0; the run stops at the value slot, having run the branch only *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat A_ISLOT_SLOT); [apply awr_ok_nil|].
    match goal with H : frame_of _ _ (ip_mem P) _ |- _ => rename H into HF0 end.
    assert (HM : ms_mem ms = ip_mem P) by (eapply vk_frame_none; exact HF0).
    match goal with H : st_ok_pi _ _ ?E' _ _ |- _ =>
      assert (HA : env_agree 32 (Ereg (ip_regs P) []) E')
        by (split; [intros j Hj; cbn [extK havoc ew]; unfold vk_EI;
                    rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia);
                    repeat match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b); [|lia] end;
                    reflexivity | reflexivity]) end.
    assert (HR : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
                   getr (ms_regs ms) r = getr (ip_regs P) r).
    { exact (regs_kept_of_st_ok_pi _ _ _ (ip_regs P) [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
               HS HA ltac:(vm_compute; reflexivity)). }
    pmkst HS.
    apply SRr'_ret. split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]].
    exists (MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ms_regs ms) (ms_mem ms)
      (with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P)) (ip_k P)
      (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P) (ip_p P) (ip_acc P) (ip_f P)
      (vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) []
         (rest_atR (ie_tb E) (ie_text E) (ip_p P)))
      (ip_ok P) (ip_tr P) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)), [].
    split; [reflexivity|]. split; [unfold vrd_cfg; reflexivity|]. split; [reflexivity|].
    assert (R2 : spZ (ms_regs ms) = spZ (ip_regs P)) by (unfold spZ; rewrite (HR 2%bv ltac:(cbn; tauto)); reflexivity).
    (* the continuation: jr_name false y = jret ([], y) *)
    assert (HC : forall okr, ip_cont P okr =
      (fst (fst (vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) []
                  (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr)),
       snd (fst (vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) []
                  (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr)),
       snd (vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) []
                  (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr))).
    { intros okr. rewrite Hcont. unfold vrd_jtail, PjGrammar.jbind, PjGrammar.jr_name. rewrite Ho.
      unfold PjGrammar.jret. cbv beta iota.
      destruct (vrd_jval _ _ _ _ _ _ _ _ _) as [[r t] ok2]. reflexivity. }
    unfold vrd_islot_a. rewrite Ho. rewrite Ho in HC.
    destruct HFR as (FR1 & FRrest). destruct HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 &
      G26 & G27).
    split.
    { unfold vrd_iframe in *. cbn [ip_regs ip_mem ip_W]. rewrite HM, R2. exact (conj FR1 FRrest). }
    split.
    { unfold vrd_iregs. cbn [ip_regs].
      rewrite !HR by (cbn; tauto).
      exact (conj G3 (conj G4 (conj G8 (conj G9 (conj G18 (conj G19 (conj G20 (conj G21 (conj G22 (conj G23
        (conj G24 (conj G25 (conj G26 G27))))))))))))). }
    split.
    { unfold vrd_icur in *. cbn [ip_mem ip_W ip_p ip_ly ip_S ip_Hp ip_Lam ip_peak ip_cnt ip_fail ip_ran]. rewrite HM.
      exact HCU. }
    split.
    { unfold vrd_ijrn in *. cbn [ip_mem ip_W ip_ly ip_S ip_Hp ip_md ip_k ip_fx ip_D ip_tr].
      destruct HJrest as (J2 & J3 & J4 & J5 & J6 & J7).
      split; [exact (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)|]. rewrite HM.
      exact (conj J2 (conj J3 (conj J4 (conj J5 (conj J6 J7))))). }
    split.
    { destruct HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
      unfold vrd_imodel. cbn [ip_ok ip_tr ip_cont ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran ip_S ip_p ip_f ip_acc].
      split; [exact M1|]. split.
      - intros okr. rewrite (M2 okr), (HC okr). reflexivity.
      - split; [exact M3|]. split; [rewrite (HC []) in M4; exact M4|]. exact (conj M5 (conj M6 (conj M7 M8))). }
    split; [exact Hnc|].
    split; [split; [reflexivity|]; unfold vrd_inode in *; cbn [ip_mem ip_W ip_n ip_cap ip_kids ip_keys ip_Lam ip_acc ip_D];
            rewrite HM; exact HND|].
    split; [reflexivity|].
    (* The kit's cut, the batch kit's layer: an array reads no key (Dk = [], lk = []); the model's jr_name false is jret ([], y), so
       jfl's body after the grow (vrd_jfb) is its body after the key (vrd_jfvk) at the same rest *)
    split; [exact Hcap1|].
    split; [unfold vrd_incaps in *; cbn [ip_W ip_mem ip_kids ip_acc]; rewrite HM; exact Hinc|].
    exists [], af, []. split; [unfold pj_keyR; reflexivity|].
    split; [unfold vrd_iforder in *; cbn [ip_W ip_mem ip_Lam ip_D ip_kids ip_keys ip_n ip_cap ip_acc]; rewrite HM;
            exact HFO|].
    split; [intros _; reflexivity|].
    intros okr. cbn [ip_ok ip_f ip_n ip_cap ip_p]. rewrite Ho in HFL. rewrite (HFL okr).
    rewrite (vrd_jfb_key (ip_f P) (S (ie_d E)) false (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af
               (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr [] (rest_atR (ie_tb E) (ie_text E) (ip_p P)) [] okr
               eq_refl).
    reflexivity.
  - (* not taken: refuted, s3 = 0 *)
    exfalso.
    match goal with H : branch_taken _ _ _ = false |- _ => rename H into Hb end.
    cbn [sv_denot] in Hb. rewrite E19 in Hb. vm_compute in Hb. discriminate Hb.
Qed.

(* ---- 2. the OBJECT arm: the symbolic state over the cursor ---- *)
(* atoms 32 / 33: the cursor's p and end words; s7 / s11 as the shadow addresses of q + 8 / q over Bx = s10 *)
Definition vk_EO (regs : bvmap 5 word) (p e : Z) : env := @Eimg _ A_prog_listing PAI (Ereg regs [w64 p; w64 e]).
Definition vk_sh_of (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 k) (SLit 3)) (SOff 26 0).
Definition vk_sr0 : list sv := sr_set (sr_set sr_atoms 23%bv (vk_sh_of 8)) 27%bv (vk_sh_of 0).
(* the cursor's 24 bytes over atom 8, with the write window [q, q + 8) when w (a run that stores q->p) and none
   otherwise *)
Definition vk_cur_region (w : bool) : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 24 0 (if w then 8 else 0) [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition vk_facts0 : facts :=
  mkFacts [ (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 0 (2 ^ 62) 0); (33%nat, mkAF 0 (2 ^ 62) 0) ] [] [].
Definition vk_SH0 : list shent := [mkSHE 8 0 24].
Definition vk_ss0 (w : bool) (k : nat) : sstate := mkSS (4 * Z.of_nat k) vk_sr0 [vk_cur_region w] None vk_facts0.

(* the shadow address s7 / s11 hold, as the engine reads it *)
Lemma vk_U_sh : forall E' q k, ew E' 8 = w64 q -> ew E' 26 = w64 SHADOW_OFF ->
  0 <= q -> 0 <= k -> q + k < 2 ^ 47 ->
  U E' (vk_sh_of k) = SHADOW_OFF + (q + k) / 8.
Proof.
  intros E' q k H8 H26 Hq Hk Hqk. unfold vk_sh_of.
  rewrite !U_SAlu, (U_lit E' 3) by lia.
  rewrite U_SOff, H8. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite (U_atom E' 26 SHADOW_OFF H26) by (unfold SHADOW_OFF; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite (zcanon_id (q + k)) by (unfold M64; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= (q + k) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (zcanon_id ((q + k) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* the symbolic state over the cursor at slot k: q = s0 (atom 8), its p and end words (atoms 32, 33), s7 / s11 as
   shadow expressions, Bx = s10; one shadow entry, q's 24 bytes *)
Lemma vk_seat0 : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q p en (w : bool) (k : nat),
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 23 = w64 (shadow_addr (q + 8)) -> getr regs 27 = w64 (shadow_addr q) ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  0 <= p <= 2 ^ 62 -> 0 <= en <= 2 ^ 62 ->
  rd_rw SEGS (mrestrict (w_H W) mem) q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  st_ok_pi (fx := fxP) SEGS VAL (vk_EO regs p en) (vk_ss0 w k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vk_SH0 (vk_EO regs p en) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q p en w k R8 R26 R23 R27 Hq1 Hq2 Hq8 Vp Ve Hp He Hrw Hra.
  set (EO := vk_EO regs p en).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EO j = getr regs r).
  { intros j Hj r Hr. unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E8 : ew EO 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E26 : ew EO 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew EO 32 = w64 p).
  { unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew EO 33 = w64 en).
  { unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Uq : U EO (SOff 8 0) = q).
  { unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. lia. }
  assert (UB : U EO (SOff 26 0) = SHADOW_OFF).
  { unfold U. cbn [sv_denot]. rewrite E26, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vk_ss0. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vk_sr0. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
      * rewrite R23. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EO (vk_sh_of 8)).
        rewrite (vk_U_sh EO q 8 E8 E26) by lia. unfold shadow_addr.
        assert (0 <= (q + 8) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
      * rewrite R27. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EO (vk_sh_of 0)).
        rewrite (vk_U_sh EO q 0 E8 E26) by lia. unfold shadow_addr. rewrite Z.add_0_r.
        assert (0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
    + destruct w; reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vk_cur_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E8. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split.
      * intros a Ha. apply Hrw. destruct w; lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS EO _ q 0 8 (SOff 32 0) p);
             [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
           rewrite Z.add_0_r. exact Vp.
        -- apply (chunk_ok_val SEGS EO _ q 8 8 (SOff 33 0) en);
             [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
           exact Ve.
    + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    + split; [|split; [exact I | exact I]].
      cbn [vk_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E8, E26, E32, E33. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vk_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) mem EO (SOff 26 0) 8 q 24 q 0 24 Hra UB Uq); [lia | lia |].
    intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

(* ---- moving a position to a new machine state that has the same memory and the same live registers ---- *)
Definition vk_live : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition vk_with (P : vrd_ipos) (regs : bvmap 5 word) (md : Model) : vrd_ipos :=
  MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) regs (ip_mem P) md (ip_k P)
    (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (ip_cont P)
    (ip_ok P) (ip_tr P) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P).

Lemma vk_with_ok : forall E P regs md,
  (forall r, In r vk_live -> getr regs r = getr (ip_regs P) r) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) md (ip_k P) (ie_CW E) ->
  vrd_iframe E P -> vrd_iregs B E P -> vrd_inode E P [] -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  vrd_imodel E P ->
  vrd_iframe E (vk_with P regs md) /\ vrd_iregs B E (vk_with P regs md) /\ vrd_inode E (vk_with P regs md) [] /\
  vrd_icur B E (vk_with P regs md) /\ vrd_ijrn B ARx SK E (vk_with P regs md) /\ vrd_imodel E (vk_with P regs md).
Proof.
  intros E P regs md HR HJ HFR HRG HND HCU HJN HMD.
  assert (R2 : spZ regs = spZ (ip_regs P)) by (unfold spZ; rewrite (HR 2%bv ltac:(cbn; tauto)); reflexivity).
  split.
  { unfold vrd_iframe in *. cbn [vk_with ip_regs ip_mem ip_W]. rewrite R2. exact HFR. }
  split.
  { unfold vrd_iregs in *. cbn [vk_with ip_regs]. rewrite !HR by (cbn; tauto). exact HRG. }
  split; [exact HND|]. split; [exact HCU|].
  split; [|exact HMD].
  destruct HJN as (_ & HJrest). split; [exact HJ | exact HJrest].
Qed.

(* the states the object arm passes through at row 117 (the first white-space loop's top, slot 6049) and row 136
   (after it, slot 6068): the loop head's facts with o = true and the cursor not yet moved past a key *)
Definition VK_W1_SLOT : nat := 6049%nat.
Definition VK_C1_SLOT : nat := 6068%nat.
(* The kit's cut: THE BATCH KIT'S LAYER OF THE LOOP HEAD (VrdIElem.vrd_ielem_a's last conjuncts), which every state of the object arm
   carries until parse_string is called: cap = ncap (S n), the members' caps, the completed slots' order list against
   af, and the model's free list at jfl's body after the grow (VrdIElem.vrd_jfb) at the cursor *)
Definition vk_k1h (E : vrd_ient) (P : vrd_ipos) : Prop :=
  ip_cap P = Z.of_nat (PresetReqAt.ncap (S (Z.to_nat (ip_n P)))) /\ vrd_incaps E P /\
  exists af, vrd_iforder E P [] af /\
    (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
       vrd_jfb (ip_f P) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af
         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr).
Definition vk_head (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vrd_iframe E P /\ vrd_iregs B E P /\ vrd_inode E P [] /\ vrd_icur B E P /\ vrd_ijrn B ARx SK E P /\
  vrd_imodel E P /\ ip_n P < ip_cap P /\
  ip_cont P = vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P)
                 (ip_f P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
  ie_o E = true /\ getr (ip_regs P) 11 = w64 (ie_text E + ie_len E) /\ vk_k1h E P.
Definition vk_w1 (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vk_head E P /\ getr (ip_regs P) 10 = w64 (ip_p P) /\ getr (ip_regs P) 12 = w64 (ip_p P) /\
  ip_p P < ie_text E + ie_len E.
Definition vk_c1 (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vk_head E P /\
  (ip_p P = ie_text E + ie_len E \/
   (ip_p P < ie_text E + ie_len E /\ exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\
      PjGrammar.ws b = false)).

(* the cursor's position bounds every walk state needs, from the entry *)
Lemma vk_q_bounds : forall CTX CTX0 CW E, vrd_ient_ok B ARx CTX CTX0 CW E ->
  2 ^ 46 <= ie_q E /\ ie_q E + 24 <= 2 ^ 47.
Proof.
  intros CTX CTX0 CW E HEN.
  destruct HEN as ((HAF & _) & _ & _ & _ & HRD & _).
  destruct HAF as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & HS0 & Hceil & Hslo & _ & H47 & _ & _ & Htop).
  destruct HRD as (_ & _ & _ & _ & _ & (He0 & _ & Hetop & _) & Hq0 & Hq24 & _).
  pose proof asan_consts as (C1 & _).
  split; lia.
Qed.

(* a run over the read-only cursor region writes nothing *)
Lemma vk_frame_ro : forall E' (m m' : word -> option byte), frame_of E' [vk_cur_region false] m m' -> m' = m.
Proof.
  intros E' m m' HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Hr). destruct Hin as [<- | []].
  cbn [vk_cur_region YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* the values of the live registers after a run that only read: the atoms are kept, and s7 / s11 keep their seated
   shadow expressions *)
Lemma vk_regs_after : forall (fxP : YK11.FPState) (H : word -> bool) E' ss ms regs0 extra,
  st_ok_pi (fx := fxP) SEGS VAL E' ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E' ->
  sr_get (ss_regs ss) 23%bv = vk_sh_of 8 -> sr_get (ss_regs ss) 27%bv = vk_sh_of 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%bv = true ->
  getr regs0 23 = sv_denot E' (vk_sh_of 8) -> getr regs0 27 = sv_denot E' (vk_sh_of 0) ->
  forall r, In r vk_live -> getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fxP H E' ss ms regs0 extra HS HA H23 H27 Hl R23 R27 r Hr.
  pose proof (st_ok_pi_restrict_reg (fx := fxP) H E' ss ms r HS) as Hg.
  assert (HK : forall r', In r' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%bv -> getr (ms_regs ms) r' = getr regs0 r')
    by exact (regs_kept_of_st_ok_pi (fx := fxP) E' ss (restrict H ms) regs0 extra
                [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%bv HS HA Hl).
  unfold vk_live in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ first [ rewrite H23 in Hg; rewrite Hg; symmetry; exact R23
            | rewrite H27 in Hg; rewrite Hg; symmetry; exact R27
            | apply HK; cbn; tauto ] |]).
  destruct Hr.
Qed.

(* ---- 3. C0: from the loop head (o = true) through the two shadow gates of the cursor and the loads of p and end,
   to the first white-space loop's top (p < end) or past it (p = end) ---- *)
Lemma vk_c0_P : forall CTX CTX0 CW E P (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ielem_a B ARx SK E P -> ie_o E = true ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IELEM_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ ip_n P' = ip_n P /\
       ((c2 = vrd_cfg VK_W1_SLOT P' /\ vk_w1 E P') \/ (c2 = vrd_cfg VK_C1_SLOT P' /\ vk_c1 E P')))
                  /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P Pm PLAW HEN HI Ho HPM.
  pose proof HI as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Hcont & Hcap1 & Hinc & HK1x).
  assert (HK1 : vk_k1h E P) by exact (conj Hcap1 (conj Hinc HK1x)). clear Hcap1 Hinc HK1x.
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ. pose proof HJN as (_ & HJrest).
  destruct (vk_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & _).
  pose proof Hin as (Vp & Ve & _ & Hrw & Hq8 & Ht0 & Htl & Hpp & _).
  assert (Hp62 : 0 <= ip_p P <= 2 ^ 62) by lia.
  assert (He62 : 0 <= ie_text E + ie_len E <= 2 ^ 62) by lia.
  destruct (vk_seat0 (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) false
              A_IELEM_SLOT G8 G26 G23 G27 Hq1 Hq2 Hq8 Vp Ve Hp62 He62 Hrw Hraq) as [HS SHOK].
  set (EO := vk_EO (ip_regs P) (ip_p P) (ie_text E + ie_len E)) in *.
  assert (HEI : img_env VAL A_LIM EO) by (unfold EO, vk_EO; apply Eimg_env).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EO j = getr (ip_regs P) r).
  { intros j Hj r Hr. unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ j r Hr). }
  assert (E19 : ew EO 19 = w64 1) by (rewrite (EL 19%nat ltac:(lia) 19%bv eq_refl), G19, Ho; reflexivity).
  assert (E32 : ew EO 32 = w64 (ip_p P)).
  { unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew EO 33 = w64 (ie_text E + ie_len E)).
  { unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 1). }
  assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E)]) EO)
    by (split; [intros j Hj; unfold EO, vk_EO; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  (* the seated shadow expressions denote the live s7 / s11 *)
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  change (sr_get (ss_regs (vk_ss0 false A_IELEM_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
  change (sr_get (ss_regs (vk_ss0 false A_IELEM_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  psrr_branch_tok RUN BR HS SHOK vk_Bspan.
  { (* row 108 taken: s3 = 0, refuted (o = true) *)
    exfalso. match goal with H : branch_taken _ _ _ = true |- _ => rename H into Hb end.
    cbn [sv_denot] in Hb. rewrite E19 in Hb. vm_compute in Hb. discriminate Hb. }
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
  match goal with H : frame_of _ _ (ip_mem P) _ |- _ => rename H into HF1 end.
  match goal with ms0 : machine_state |- _ => rename ms0 into ms1 end.
  assert (HM1 : ms_mem ms1 = ip_mem P) by (eapply vk_frame_ro; exact HF1).
  (* row 115: bgeu p, end *)
  psrr_branch_tok RUN BR HS SHOK vk_Bspan.
  - (* p >= end: on to row 136 with p = end *)
    match goal with H : branch_taken _ _ _ = true |- _ => rename H into Hb end.
    assert (Hpe : ip_p P = ie_text E + ie_len E).
    { rewrite branch_geu_U, (U_atom EO 32 (ip_p P) E32), (U_atom EO 33 _ E33) in Hb by lia.
      apply Bool.negb_true_iff, Z.ltb_ge in Hb. lia. }
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_C1_SLOT);
      [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
    match goal with H : frame_of _ _ (ms_mem ms1) _ |- _ => rename H into HF2 end.
    match goal with ms0 : machine_state |- _ => lazymatch ms0 with ms1 => fail | _ => rename ms0 into ms2 end end.
    assert (HM2 : ms_mem ms2 = ip_mem P) by (rewrite <- HM1; eapply vk_frame_ro; exact HF2).
    assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r).
    { eapply (vk_regs_after _ _ _ _ _ _ _ HS HA); [reflexivity | reflexivity | vm_compute; reflexivity | exact R23 | exact R27]. }
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as R11.
    match type of R11 with _ = sv_denot _ (sr_get ?l _) =>
      let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in R11 end.
    cbn [sv_denot] in R11. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R11. rewrite E33 in R11.
    cbn [ms_regs restrict] in R11.
    pmkst HS. apply SRr'_ret. split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]].
    exists (vk_with P (ms_regs ms2) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P)))
                                           mat0 (with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P)))).
    split; [reflexivity|]. split; [reflexivity|]. right. split.
    { unfold vrd_cfg, vk_with. cbn [ip_fx ip_regs ip_mem ip_md]. rewrite HM2. reflexivity. }
    rewrite HM2 in HJ.
    destruct (vk_with_ok E P (ms_regs ms2) _ HRk (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
                HFR HRG HND HCU HJN HMD) as (W1 & W2 & W3 & W4 & W5 & W6).
    split; [|left; exact Hpe].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
    split; [exact W6|]. split; [exact Hnc|]. split; [exact Hcont|]. split; [exact Ho|].
    split; [exact R11 | exact HK1].
  - (* p < end: one `mv a0, a2` to row 117 *)
    match goal with H : branch_taken _ _ _ = false |- _ => rename H into Hb end.
    assert (Hpe : ip_p P < ie_text E + ie_len E).
    { rewrite branch_geu_U, (U_atom EO 32 (ip_p P) E32), (U_atom EO 33 _ E33) in Hb by lia.
      apply Bool.negb_false_iff, Z.ltb_lt in Hb. exact Hb. }
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_W1_SLOT);
      [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
    match goal with H : frame_of _ _ (ms_mem ms1) _ |- _ => rename H into HF2 end.
    match goal with ms0 : machine_state |- _ => lazymatch ms0 with ms1 => fail | _ => rename ms0 into ms2 end end.
    assert (HM2 : ms_mem ms2 = ip_mem P) by (rewrite <- HM1; eapply vk_frame_ro; exact HF2).
    assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r).
    { eapply (vk_regs_after _ _ _ _ _ _ _ HS HA); [reflexivity | reflexivity | vm_compute; reflexivity | exact R23 | exact R27]. }
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS) as R10.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as R11.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 12%bv HS) as R12.
    match type of R10 with _ = sv_denot _ (sr_get ?l _) =>
      let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in R10;
      let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in R11;
      let v := eval vm_compute in (sr_get l 12%bv) in change (sr_get l 12%bv) with v in R12 end.
    cbn [sv_denot] in R10, R11, R12. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R10, R11, R12.
    rewrite E32 in R10, R12. rewrite E33 in R11. cbn [ms_regs restrict] in R10, R11, R12.
    pmkst HS. apply SRr'_ret. split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]].
    exists (vk_with P (ms_regs ms2) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P)))
                                           mat0 (with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P)))).
    split; [reflexivity|]. split; [reflexivity|]. left. split.
    { unfold vrd_cfg, vk_with. cbn [ip_fx ip_regs ip_mem ip_md]. rewrite HM2. reflexivity. }
    rewrite HM2 in HJ.
    destruct (vk_with_ok E P (ms_regs ms2) _ HRk (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
                HFR HRG HND HCU HJN HMD) as (W1 & W2 & W3 & W4 & W5 & W6).
    split; [|split; [exact R10 | split; [exact R12 | exact Hpe]]].
    split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
    split; [exact W6|]. split; [exact Hnc|]. split; [exact Hcont|]. split; [exact Ho|].
    split; [exact R11 | exact HK1].
Qed.

(* ---- 4. the first white-space loop, rows 117..135: one byte per iteration ---- *)
(* the symbolic state at the loop top: the cursor (writable p word), the byte at p as a one-byte region over atom
   32 with its value atom 34, a0 = a2 = p, a1 = end *)
Definition vk_EW (regs : bvmap 5 word) (p e b : Z) : env :=
  @Eimg _ A_prog_listing PAI (Ereg regs [w64 p; w64 e; w64 b]).
(* the register file of a white-space loop's top, generic in its three registers: the copy of p (rc), end (re) and
   p (rp). The first loop (rows 117..135) has a0 / a1 / a2, the second (rows 176..194) a1 / a3 / a4. *)
Definition vk_srWg (wc we wp : bv 5) : list sv :=
  sr_set (sr_set (sr_set vk_sr0 wc (SOff 32 0)) we (SOff 33 0)) wp (SOff 32 0).
Definition vk_srW : list sv := vk_srWg 10%bv 11%bv 12%bv.
Definition vk_byte_region : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition vk_factsW : facts :=
  mkFacts [ (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0); (33%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (34%nat, mkAF 0 255 0) ] [] [].
Definition vk_ssWg (wc we wp : bv 5) (k : nat) : sstate :=
  mkSS (4 * Z.of_nat k) (vk_srWg wc we wp) [vk_cur_region true; vk_byte_region] None vk_factsW.
Definition vk_ssW (k : nat) : sstate := vk_ssWg 10%bv 11%bv 12%bv k.

Lemma vk_seatWg : forall (wc we wp : bv 5) (fxP : YK11.FPState) (W : world SEGS) regs mem q p en b (k : nat),
  bv_eqb wc 0 = false -> bv_eqb we 0 = false -> bv_eqb wp 0 = false ->
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 23 = w64 (shadow_addr (q + 8)) -> getr regs 27 = w64 (shadow_addr q) ->
  getr regs wc = w64 p -> getr regs we = w64 en -> getr regs wp = w64 p ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  4096 <= p <= 2 ^ 47 - 8 -> 4096 <= en <= 2 ^ 47 - 8 ->
  val_mem SEGS (mrestrict (w_H W) mem) p 1 b -> 0 <= b < 256 -> (p + 1 <= q \/ q + 24 <= p) ->
  rd_rw SEGS (mrestrict (w_H W) mem) q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  st_ok_pi (fx := fxP) SEGS VAL (vk_EW regs p en b) (vk_ssWg wc we wp k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vk_SH0 (vk_EW regs p en b) (mrestrict (w_H W) mem).
Proof.
  intros wc we wp fxP W regs mem q p en b k Hrc Hre Hrp R8 R26 R23 R27 R10 R11 R12 Hq1 Hq2 Hq8 Vp Ve Hp He Vb Hb Hdj Hrw Hra.
  set (EW := vk_EW regs p en b).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EW j = getr regs r).
  { intros j Hj r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E8 : ew EW 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew EW 32 = w64 p).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew EW 33 = w64 en).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (E34 : ew EW 34 = w64 b).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Uq : U EW (SOff 8 0) = q).
  { unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. lia. }
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF).
  { unfold U. cbn [sv_denot]. rewrite E26, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (S32 : sv_denot EW (SOff 32 0) = w64 p).
  { cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (S33 : sv_denot EW (SOff 33 0) = w64 en).
  { cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vk_ssWg. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vk_srWg, vk_sr0.
      apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [|exact Hrc|]|exact Hre|]|exact Hrp|];
        [| rewrite R10; symmetry; exact S32 | rewrite R11; symmetry; exact S33 | rewrite R12; symmetry; exact S32].
      apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
      * rewrite R23. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EW (vk_sh_of 8)).
        rewrite (vk_U_sh EW q 8 E8 E26) by lia. unfold shadow_addr.
        assert (0 <= (q + 8) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
      * rewrite R27. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EW (vk_sh_of 0)).
        rewrite (vk_U_sh EW q 0 E8 E26) by lia. unfold shadow_addr. rewrite Z.add_0_r.
        assert (0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
    + reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold region_ok, vk_cur_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E8. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split.
        -- intros a Ha. apply Hrw. lia.
        -- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
           ++ apply (chunk_ok_val SEGS EW _ q 0 8 (SOff 32 0) p); [exact S32 | cbn; lia | cbn; lia |].
              rewrite Z.add_0_r. exact Vp.
           ++ apply (chunk_ok_val SEGS EW _ q 8 8 (SOff 33 0) en); [exact S33 | cbn; lia | cbn; lia |].
              exact Ve.
      * unfold region_ok, vk_byte_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS EW _ p 0 1 (SOff 34 0) b);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vb.
    + apply pairwise_disjoint_of_extents. unfold vk_cur_region, vk_byte_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite E8, E32. unfold w64. rewrite !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [vk_factsW f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E8, E26, E32, E33, E34. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vk_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) mem EW (SOff 26 0) 8 q 24 q 0 24 Hra UB Uq); [lia | lia |].
    intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

Lemma vk_seatW : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q p en b (k : nat),
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 23 = w64 (shadow_addr (q + 8)) -> getr regs 27 = w64 (shadow_addr q) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 en -> getr regs 12 = w64 p ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  4096 <= p <= 2 ^ 47 - 8 -> 4096 <= en <= 2 ^ 47 - 8 ->
  val_mem SEGS (mrestrict (w_H W) mem) p 1 b -> 0 <= b < 256 -> (p + 1 <= q \/ q + 24 <= p) ->
  rd_rw SEGS (mrestrict (w_H W) mem) q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  st_ok_pi (fx := fxP) SEGS VAL (vk_EW regs p en b) (vk_ssW k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vk_SH0 (vk_EW regs p en b) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q p en b k. exact (vk_seatWg 10%bv 11%bv 12%bv fxP W regs mem q p en b k eq_refl eq_refl eq_refl).
Qed.
Ltac vk_proj := unfold vk_move; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
  ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].

(* ---- the model across a white-space byte: jr_name true skips it ---- *)
Lemma vk_skipn_cons : forall (l : list Z) k x, nth_error l k = Some x -> skipn k l = x :: skipn (S k) l.
Proof.
  induction l as [|y l IH]; intros k x H; [destruct k; discriminate H|].
  destruct k as [|k]; cbn in H |- *; [injection H as <-; reflexivity | exact (IH k x H)].
Qed.

Lemma vk_rest_cons : forall tb text p b, text <= p -> nth_error tb (Z.to_nat (p - text)) = Some b ->
  rest_atR tb text p = b :: rest_atR tb text (p + 1).
Proof.
  intros tb text p b Hp H. unfold rest_atR. rewrite (vk_skipn_cons tb _ b H). f_equal. f_equal. lia.
Qed.

Lemma vk_jtail_ws : forall d n cap1 acc f tb text p b, text <= p ->
  nth_error tb (Z.to_nat (p - text)) = Some b -> PjGrammar.ws b = true ->
  vrd_jtail d true n cap1 acc f (rest_atR tb text p) = vrd_jtail d true n cap1 acc f (rest_atR tb text (p + 1)).
Proof.
  intros d n cap1 acc f tb text p b Hp Hb Hws. rewrite (vk_rest_cons tb text p b Hp Hb).
  unfold vrd_jtail, PjGrammar.jr_name. cbn [PjGrammar.skip]. rewrite Hws. reflexivity.
Qed.

(* the model's free list at jfl's body after the grow (VrdIElem.vrd_jfb) across a white-space byte: jr_name true skips it *)
Lemma vk_jfb_ws : forall f d n cap1 af tb text p b ok, text <= p ->
  nth_error tb (Z.to_nat (p - text)) = Some b -> PjGrammar.ws b = true ->
  vrd_jfb f d true n cap1 af (rest_atR tb text p) ok = vrd_jfb f d true n cap1 af (rest_atR tb text (p + 1)) ok.
Proof.
  intros f d n cap1 af tb text p b ok Hp Hb Hws. rewrite (vk_rest_cons tb text p b Hp Hb).
  unfold vrd_jfb, PjGrammar.jr_name. cbn [PjGrammar.skip]. rewrite Hws. reflexivity.
Qed.

Lemma vk_rest_len : forall tb text p p', text <= p <= p' ->
  (length (rest_atR tb text p') <= length (rest_atR tb text p))%nat.
Proof. intros tb text p p' H. unfold rest_atR. rewrite !length_skipn. lia. Qed.

(* ---- leaving a run that may have stored the cursor's p word: the position at the new state ---- *)
Lemma vk_unseat : forall CTX CTX0 CW E P (regs' : bvmap 5 word) (mem' : word -> option byte) md' k' p',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_head E P ->
  (forall r, In r vk_live -> getr regs' r = getr (ip_regs P) r) ->
  getr regs' 11 = w64 (ie_text E + ie_len E) ->
  (forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8) -> mem' x = ip_mem P x) ->
  val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 8 p' ->
  (forall a, ie_q E <= a < ie_q E + 8 -> writable_at SEGS (mrestrict (w_H (ip_W P)) mem') a) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  (p' = ip_p P \/
   (p' = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\
    exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\ PjGrammar.ws b = true)) ->
  vk_head E (vk_move P regs' mem' md' k' p').
Proof.
  intros CTX CTX0 CW E P regs' mem' md' k' p' HEN HH HR R11 HKr Vp' Wq HJ' Hp'.
  pose proof HH as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Hcont & Ho & R11o & HK1).
  pose proof HCU as (Hin & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose proof asan_consts as (C1 & _).
  assert (Hpr : ie_text E <= p' <= ie_text E + ie_len E) by (destruct Hp' as [-> | (-> & ? & _)]; lia).
  assert (HK : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8) ->
                 mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x)
    by (intros x Hx; unfold mrestrict; rewrite (HKr x Hx); reflexivity).
  assert (HKo : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                  (fun x => ie_q E + 8 <= x < ie_q E + 24 \/ ie_text E <= x < ie_text E + ie_len E)).
  { apply (vk_keep_rd _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) _ HK). intros a Ha. lia. }
  assert (Hpin' : pj_in_okR SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) (ie_text E) (ie_len E) p'
                    (Z.of_nat (ie_d E) + 1) (ie_tb E)).
  { split; [exact Vp'|].
    split; [eapply VrdFrame.val_mem_keep; [exact Ve | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]|].
    split; [eapply VrdFrame.val_mem_keep; [exact Vd | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]|].
    split.
    { intros x Hx. destruct (Z_lt_le_dec x (ie_q E + 8)) as [Hl | Hl]; [apply Wq; lia|].
      apply (proj2 HKo x); [cbn beta; lia | apply Hrw; lia]. }
    split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hpr|]. split; [exact Hlen|].
    split; [|exact (conj Hdisj Hd)].
    eapply VrdFrame.garr8_keep; [exact Hga | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]. }
  assert (Hsp' : spZ regs' = spZ (ip_regs P)) by (unfold spZ; rewrite (HR 2%bv ltac:(cbn; tauto)); reflexivity).
  destruct (vk_cur_store_keep B ARx SK LAWS HW PST_IMG
              CTX CTX0 CW E P [] regs' mem' md' k' p' (ie_q E) 8 Hfr144 Hs0c HEN HFR HND HCU HJN
              ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; exists (ie_q E, ie_q E + 8); split; [left; reflexivity | cbn; lia])
              ltac:(intros a Ha; lia) HK Hsp' HJ' Hpin'
              ltac:(apply vk_rest_len; destruct Hp' as [-> | (-> & _)]; lia))
    as (W1 & W2 & W3 & W4).
  split; [exact W1|]. split.
  { unfold vrd_iregs in *. vk_proj. rewrite !HR by (cbn; tauto). exact HRG. }
  split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
  split.
  { pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
    unfold vrd_imodel. vk_proj.
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
    split; [|exact (conj M6 (conj M7 M8))].
    pose proof (vk_rest_len (ie_tb E) (ie_text E) (ip_p P) p' ltac:(destruct Hp' as [-> | (-> & _)]; lia)). lia. }
  (* The kit's cut, the batch kit's layer: the store wrote only the cursor's p word, above alloc_ceiling, so every block the position
     owns (below it, VrdCurStore.vk_D_low) keeps its bytes (VrdIFd.vrd_k1_keep); the model's free list moves with the
     cursor over a white-space byte as the continuation does *)
  destruct HK1 as (Hcap1 & Hinc & af & HFO & HFL).
  pose proof HJN as ((HAR & _) & _ & _ & _ & _ & HBM & _).
  pose proof HMD as (_ & _ & HLM & _). pose proof HLM as (_ & _ & _ & HPL & _).
  assert (HKD : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem') (rd_blk (ip_D P))).
  { apply (vk_keep_rd _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) _ HK). intros a Ha.
    unfold rd_blk in Ha. apply Exists_exists in Ha as (b & Hb & Hab).
    pose proof (vk_D_low B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ b a HAR HBM Hb Hab). lia. }
  destruct (vrd_k1_keep E P (vk_move P regs' mem' md' k' p') [] af eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              ltac:(intros xx kk Hx; unfold prh_lin; vk_proj; apply (Permutation_in _ (Permutation_sym HPL));
                    apply in_or_app; left; exact Hx)
              HKD HND Hinc HFO) as (Hinc' & HFO').
  assert (Hjt : vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P)
                  (rest_atR (ie_tb E) (ie_text E) (ip_p P)) =
                vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P)
                  (rest_atR (ie_tb E) (ie_text E) p') /\
                forall okr, vrd_jfb (ip_f P) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af
                  (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr =
                vrd_jfb (ip_f P) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af
                  (rest_atR (ie_tb E) (ie_text E) p') okr).
  { destruct Hp' as [-> | (-> & Hlt & b & Hb & Hws)]; [split; reflexivity|]. rewrite Ho. split.
    - apply (vk_jtail_ws _ _ _ _ _ _ _ _ b); [lia | exact Hb | exact Hws].
    - intros okr. apply (vk_jfb_ws _ _ _ _ _ _ _ _ b); [lia | exact Hb | exact Hws]. }
  destruct Hjt as (Hjt1 & Hjt2).
  vk_proj. split; [exact Hnc|].
  split; [rewrite Hcont; exact Hjt1|].
  split; [exact Ho|]. split; [exact R11|].
  split; [exact Hcap1|]. split; [exact Hinc'|]. exists af. split; [exact HFO'|].
  intros okr. cbn [ip_ok ip_f ip_n ip_cap ip_p]. rewrite (HFL okr). exact (Hjt2 okr).
Qed.

(* ---- reading the cursor word and its write window off a run's end state ---- *)
Lemma vk_end_cur : forall (fxP : YK11.FPState) (H : word -> bool) E' ss ms cs e0 q v,
  st_ok_pi (fx := fxP) SEGS VAL E' ss (restrict H ms) ->
  In (YP09.mkRegion (Some 8%nat) 0 24 0 8 cs) (ss_mem ss) -> In (YP09.mkChunk 0 (CVal 8 e0)) cs ->
  bv_unsigned (ew E' 8) = q -> U E' e0 = v ->
  val_mem SEGS (ms_mem (restrict H ms)) q 8 v /\
  (forall a, q <= a < q + 8 -> writable_at SEGS (ms_mem (restrict H ms)) a).
Proof.
  intros fxP H E' ss ms cs e0 q v HS Hin Hc Hq Hv.
  destruct (st_ok_mem_ok SEGS E' (abs_ss VAL ss) (restrict H ms) HS) as (_ & Hrs & _).
  pose proof (proj1 (Forall_forall _ _) Hrs _ Hin) as (_ & _ & Hw & Hcs).
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hw, Hcs. rewrite Hq in Hw, Hcs.
  split.
  - rewrite <- (Z.add_0_r q). apply (val_of_chunk_ok SEGS E' _ q 0 8 e0 v).
    + exact (proj1 (Forall_forall _ _) Hcs _ Hc).
    + rewrite <- Hv. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite <- Hv. unfold U. pose proof (bv_unsigned_in_range _ (sv_denot E' e0)) as Hr.
      unfold bv_modulus in Hr. cbn in Hr |- *. lia.
    + cbn. lia.
  - intros a Ha. replace a with (q + (a - q)) by lia. apply Hw. lia.
Qed.

(* a W1-run's frame: only the cursor's p word may change *)
Lemma vk_frame_cur : forall E' (m m' : word -> option byte) q cs1 cs2,
  frame_of E' [YP09.mkRegion (Some 8%nat) 0 24 0 8 cs1; YP09.mkRegion (Some 32%nat) 0 1 0 0 cs2] m m' ->
  bv_unsigned (ew E' 8) = q ->
  forall x : word, ~ (q <= bv_unsigned x < q + 8) -> m' x = m x.
Proof.
  intros E' m m' q cs1 cs2 HF Hq x Hx. apply HF. intros (r & Hin & Hr).
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [rewrite Hq in Hr|]; lia.
Qed.

(* the side goals of a W1 run: the byte's shadow, and the store into the cursor's p word (in the caller window) *)
Ltac vk_ra_byte Hrat UB U32 := cbn [ms_mem mkst restrict]; rewrite UB, U32; intros y Hy; apply Hrat; lia.
Ltac vk_awr E8u HSTK :=
  lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  eapply awr_ok_cons_gen;
  [ reflexivity | cbn [ew ewset Nat.eqb]; exact E8u
  | intros a Ha; left; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia
  | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ].

(* the white-space mask test of row 123..125 *)
Lemma vk_mask_U : forall E' b, ew E' 25 = Z_to_bv 64 VrdPro.vrd_ws_mask -> ew E' 34 = Z_to_bv 64 b -> 0 <= b <= 32 ->
  U E' (SAlu ALU_AND (SAlu ALU_SRL (SOff 25 0) (SOff 34 0)) (SLit 1)) = (if PjGrammar.ws b then 1 else 0).
Proof.
  intros E' b H25 H34 Hb.
  rewrite U_and_lit by lia. rewrite U_SAlu, (U_atom E' 25 VrdPro.vrd_ws_mask H25), (U_atom E' 34 b H34)
    by (unfold VrdPro.vrd_ws_mask; lia).
  cbn [zalu_raw]. rewrite <- (VrdPro.vrd_mask_ws b Hb).
  assert (Hm : Z.land b 63 = b mod 64) by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; reflexivity).
  rewrite Hm. f_equal. apply zcanon_id. unfold M64.
  assert (H0 : 0 <= b mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hp : 0 < 2 ^ (b mod 64)) by (apply Z.pow_pos_nonneg; lia).
  assert (VrdPro.vrd_ws_mask / 2 ^ (b mod 64) <= VrdPro.vrd_ws_mask) by (apply Z.div_le_upper_bound; [lia | unfold VrdPro.vrd_ws_mask; nia]).
  assert (0 <= VrdPro.vrd_ws_mask / 2 ^ (b mod 64)) by (apply Z.div_pos; unfold VrdPro.vrd_ws_mask; lia).
  unfold VrdPro.vrd_ws_mask in *. lia.
Qed.

(* leaving a W1 run at its end state: the position there, through vk_unseat (HH' : vk_head E P') *)
Ltac vk_leave CTX CTX0 CW E P HEN HH E8u E32 E33 HA R23 R27 HJ HPM p' Hpd :=
  lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
    let HKr := fresh "HKr" in let Vq := fresh "Vq" in let Wq := fresh "Wq" in let HA2 := fresh "HA2" in
    let HRk := fresh "HRk" in let R11e := fresh "R11e" in let HHo := fresh "HH'" in
    assert (HKr : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8) -> ms_mem ms2 x = ip_mem P x)
      by (intros x Hx;
          repeat match goal with HF : frame_of _ _ ?m ?m' |- ?m' x = _ =>
            rewrite (vk_frame_cur _ _ _ (ie_q E) _ _ HF ltac:(cbn [ew ewset Nat.eqb]; exact E8u) x Hx) end;
          reflexivity);
    let rs := eval vm_compute in (ss_mem ss2) in
    lazymatch rs with (YP09.mkRegion (Some 8%nat) 0 24 0 8 ?cs) :: _ =>
    lazymatch cs with (YP09.mkChunk 0 (CVal 8 ?e0)) :: _ =>
      destruct (vk_end_cur _ _ E2 ss2 ms2 cs e0 (ie_q E) p' HSe
                  ltac:(change (ss_mem ss2) with rs; left; reflexivity) ltac:(left; reflexivity)
                  ltac:(cbn [ew ewset Nat.eqb]; exact E8u)
                  ltac:(rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E32; unfold w64;
                        rewrite unsigned_lit_small by lia; rewrite ?Z.add_0_r; apply zcanon_id; unfold M64; lia))
        as [Vq Wq]
    end end;
    lazymatch type of HA with env_agree _ ?RX _ =>
    assert (HA2 : env_agree 32 RX E2)
      by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros k Hk; cbn [ew ewset];
          repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity)
    end;
    assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
      by (eapply (vk_regs_after _ _ _ _ _ _ _ HSe HA2);
          [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | rewrite R23; reflexivity | rewrite R27; reflexivity]);
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HSe) as R11e;
    cbn [ms_regs restrict] in R11e;
    (lazymatch type of R11e with _ = sv_denot _ (sr_get ?l _) =>
       let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in R11e end);
    cbn [sv_denot] in R11e; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R11e;
    cbn [ew ewset Nat.eqb] in R11e; rewrite E33 in R11e;
    cbn [restrict ms_mem] in Vq, Wq;
    lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K =>
      pose proof (vk_unseat CTX CTX0 CW E P (ms_regs ms2) (ms_mem ms2) MD K p' HEN HH HRk R11e HKr
                    Vq Wq (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HH))))) HJ)
                    Hpd) as HHo;
      pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
      exists (vk_move P (ms_regs ms2) (ms_mem ms2) MD K p')
    end
  end.

(* the W1 step: one byte of the first white-space loop *)
Definition vk_w1_post (E : vrd_ient) (P : vrd_ipos) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P', W2 = ip_W P' /\ ip_n P' = ip_n P /\
    ((c2 = vrd_cfg VK_C1_SLOT P' /\ vk_c1 E P') \/
     (c2 = vrd_cfg VK_W1_SLOT P' /\ vk_w1 E P' /\ ip_p P' = ip_p P + 1)).

Lemma vk_w1_step_P : forall CTX CTX0 CW E P (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_w1 E P ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_W1_SLOT P)
    (fun W2 c2 => vk_w1_post E P W2 c2 /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P Pm PLAW HEN HW1 HPM.
  pose proof HW1 as ((HFR & HRG & HND & HCU & HJN & HMD & Hnc & Hcont & Ho & R11 & HK1) & R10 & R12 & Hpe).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ. pose proof HJN as (_ & HJrest).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof Hsrc as (_ & Ht4 & Htl8 & _ & Hrat & _).
  rewrite Hlen in Htl8.
  pose proof asan_consts as (C1 & _).
  destruct (vk_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  set (j := Z.to_nat (ip_p P - ie_text E)).
  assert (Hj : (j < length (ie_tb E))%nat) by (unfold j; lia).
  set (b := nth j (ie_tb E) 0).
  destruct (Hga j Hj) as [Vb Hb]. fold b in Vb, Hb.
  replace (ie_text E + Z.of_nat j) with (ip_p P) in Vb by (unfold j; lia).
  destruct (vk_seatW (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) b VK_W1_SLOT
     G8 G26 G23 G27 R10 R11 R12 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Vb Hb ltac:(lia) Hrw Hraq) as [HS SHOK].
  set (EW := vk_EW (ip_regs P) (ip_p P) (ie_text E + ie_len E) b) in *.
  assert (HEI : img_env VAL A_LIM EW) by (unfold EW, vk_EW; apply Eimg_env).
  assert (EL : forall k, (k < 32)%nat -> forall r : bv 5, Z.of_nat k = bv_unsigned r -> ew EW k = getr (ip_regs P) r).
  { intros k Hk r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ k r Hr). }
  assert (E8 : ew EW 8 = w64 (ie_q E)) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact G8).
  assert (E8u : bv_unsigned (ew EW 8) = ie_q E) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (E21 : ew EW 21 = w64 32) by (rewrite (EL 21%nat ltac:(lia) 21%bv eq_refl); exact G21).
  assert (E25 : ew EW 25 = w64 4294977024) by (rewrite (EL 25%nat ltac:(lia) 25%bv eq_refl); exact G25).
  assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact G26).
  assert (E32 : ew EW 32 = w64 (ip_p P)).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew EW 33 = w64 (ie_text E + ie_len E)).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 1). }
  assert (E34 : ew EW 34 = w64 b).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 2). }
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF) by (apply (U_atom EW 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
  assert (U32 : U EW (SOff 32 0) = ip_p P) by (apply (U_atom EW 32 (ip_p P) E32); lia).
  assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) EW)
    by (split; [intros k Hk; unfold EW, vk_EW; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  change (sr_get (ss_regs (vk_ssW VK_W1_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
  change (sr_get (ss_regs (vk_ssW VK_W1_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
  assert (HSTK : 0 <= STK_parse_items (ie_d E)).
  { destruct HEN as ((HAF & _) & _). destruct HAF as (_ & _ & _ & _ & _ & Hstk & _). exact (proj1 (proj2 Hstk)). }
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [ vk_ra_byte Hrat UB U32 | vk_awr E8u HSTK | ].
  match goal with H : frame_of _ _ (ip_mem P) _ |- _ => rename H into HF1 end.
  psrr_branch_tok RUN BR HS SHOK vk_Bspan.
  - (* row 122 taken: 32 < b, so b is not white space: on to row 136 with p *)
    match goal with Hb1 : branch_taken _ (sv_denot ?E' _) _ = true |- _ =>
      assert (Hgt : 32 < b);
      [ assert (F21 : ew E' 21 = Z_to_bv 64 32) by (cbn [ew ewset Nat.eqb]; exact E21);
        assert (F34 : ew E' 34 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E34);
        rewrite branch_ltu_U, (U_atom E' 21 32 F21), (U_atom E' 34 b F34) in Hb1 by lia;
        apply Z.ltb_lt in Hb1; exact Hb1 | ] end.
    assert (Hnws : PjGrammar.ws b = false)
      by (unfold PjGrammar.ws; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_C1_SLOT); [vk_awr E8u HSTK|].
    lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
    lazymatch goal with HF2 : frame_of _ _ (ms_mem ?ms1) (ms_mem ms2) |- _ =>
      assert (HKr : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8) -> ms_mem ms2 x = ip_mem P x);
      [ intros x Hx; rewrite (vk_frame_cur _ _ _ (ie_q E) _ _ HF2 ltac:(cbn [ew ewset Nat.eqb]; exact E8u) x Hx);
        exact (vk_frame_cur _ _ _ (ie_q E) _ _ HF1 ltac:(cbn [ew ewset Nat.eqb]; exact E8u) x Hx) |];
      let rs := eval vm_compute in (ss_mem ss2) in
      lazymatch rs with (YP09.mkRegion (Some 8%nat) 0 24 0 8 ?cs) :: _ =>
      lazymatch cs with (YP09.mkChunk 0 (CVal 8 ?e0)) :: _ =>
        destruct (vk_end_cur _ _ E2 ss2 ms2 cs e0 (ie_q E) (ip_p P) HSe
                    ltac:(change (ss_mem ss2) with rs; left; reflexivity) ltac:(left; reflexivity)
                    ltac:(cbn [ew ewset Nat.eqb]; exact E8u)
                    ltac:(apply (U_atom E2 32 (ip_p P)); [cbn [ew ewset Nat.eqb]; exact E32 | lia])) as [Vq Wq]
      end end;
      assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) E2)
        by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros k Hk; cbn [ew ewset];
            repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
      assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
        by (eapply (vk_regs_after _ _ _ _ _ _ _ HSe HA2);
            [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
            | rewrite R23; reflexivity | rewrite R27; reflexivity]);
      pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HSe) as R11e;
      cbn [ms_regs restrict] in R11e;
      (lazymatch type of R11e with _ = sv_denot _ (sr_get ?l _) =>
         let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in R11e end);
      cbn [sv_denot] in R11e; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R11e;
      cbn [ew ewset Nat.eqb] in R11e; rewrite E33 in R11e;
      cbn [restrict ms_mem] in Vq, Wq;
      lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K =>
        pose proof (vk_unseat CTX CTX0 CW E P (ms_regs ms2) (ms_mem ms2) MD K (ip_p P) HEN (proj1 HW1) HRk R11e HKr
                      Vq Wq (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) (or_introl eq_refl)) as HH';
        pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
        exists (vk_move P (ms_regs ms2) (ms_mem ms2) MD K (ip_p P))
      end
    end end.
    split; [reflexivity|]. split; [reflexivity|]. left. split; [unfold vrd_cfg; vk_proj; reflexivity|].
    split; [exact HH'|]. right. vk_proj. split; [lia|]. exists b. split; [unfold b; apply nth_error_nth'; exact Hj | exact Hnws].
  - (* row 122 not taken: b <= 32 *)
    match goal with Hb1 : branch_taken _ (sv_denot ?E' _) _ = false |- _ =>
      assert (Hle : b <= 32);
      [ assert (F21 : ew E' 21 = Z_to_bv 64 32) by (cbn [ew ewset Nat.eqb]; exact E21);
        assert (F34 : ew E' 34 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E34);
        rewrite branch_ltu_U, (U_atom E' 21 32 F21), (U_atom E' 34 b F34) in Hb1 by lia;
        apply Z.ltb_ge in Hb1; exact Hb1 | ] end.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [vk_awr E8u HSTK|].
    psrr_branch_tok RUN BR HS SHOK vk_Bspan.
    + (* row 125 taken: the mask bit is 0, so b is not white space: on to row 136 with p *)
      match goal with Hb2 : branch_taken _ (sv_denot ?E' _) _ = true |- _ =>
        assert (Hnws : PjGrammar.ws b = false);
        [ assert (F25 : ew E' 25 = Z_to_bv 64 VrdPro.vrd_ws_mask) by (cbn [ew ewset Nat.eqb]; exact E25);
          assert (F34 : ew E' 34 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E34);
          rewrite branch_eq_U, (vk_mask_U E' b F25 F34 ltac:(lia)), (U_lit E' 0) in Hb2 by lia;
          destruct (PjGrammar.ws b); [discriminate Hb2 | reflexivity] | ] end.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_C1_SLOT); [vk_awr E8u HSTK|].
      assert (Hpd : ip_p P = ip_p P \/ (ip_p P = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\ exists b0, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b0 /\ PjGrammar.ws b0 = true)) by (left; reflexivity).
      vk_leave CTX CTX0 CW E P HEN (proj1 HW1) E8u E32 E33 HA R23 R27 HJ HPM (ip_p P) Hpd.
      split; [reflexivity|]. split; [reflexivity|]. left. split; [unfold vrd_cfg; vk_proj; reflexivity|].
      split; [exact HH'|]. right. vk_proj. split; [lia|]. exists b.
      split; [unfold b; apply nth_error_nth'; exact Hj | exact Hnws].
    + (* row 125 not taken: b is white space; rows 126..131 store q->p := p + 1 and compare it with end *)
      match goal with Hb2 : branch_taken _ (sv_denot ?E' _) _ = false |- _ =>
        assert (Hws : PjGrammar.ws b = true);
        [ assert (F25 : ew E' 25 = Z_to_bv 64 VrdPro.vrd_ws_mask) by (cbn [ew ewset Nat.eqb]; exact E25);
          assert (F34 : ew E' 34 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E34);
          rewrite branch_eq_U, (vk_mask_U E' b F25 F34 ltac:(lia)), (U_lit E' 0) in Hb2 by lia;
          destruct (PjGrammar.ws b); [reflexivity | discriminate Hb2] | ] end.
      assert (Hnth : nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b)
        by (unfold b; apply nth_error_nth'; exact Hj).
      paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [vk_awr E8u HSTK|].
      match goal with Hb3 : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = _ |- _ => idtac end.
      psrr_branch_tok RUN BR HS SHOK vk_Bspan.
      * (* row 131 taken: p + 1 <> end: back to row 117 with p + 1 *)
        match goal with Hb3 : branch_taken _ (sv_denot ?E' _) _ = true |- _ =>
          assert (Hne : ip_p P + 1 <> ie_text E + ie_len E);
          [ rewrite branch_ne_U in Hb3;
            rewrite (U_SOff E' 32 1), (U_SOff E' 33 0) in Hb3; cbn [ew ewset Nat.eqb] in Hb3;
            rewrite E32, E33 in Hb3; unfold w64 in Hb3; rewrite !unsigned_lit_small in Hb3 by lia;
            rewrite !zcanon_id in Hb3 by (unfold M64; lia); rewrite Z.add_0_r in Hb3;
            apply Bool.negb_true_iff, Z.eqb_neq in Hb3; exact Hb3 | ] end.
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_W1_SLOT); [vk_awr E8u HSTK|].
        lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
          assert (D32 : sv_denot E2 (SOff 32 1) = Z_to_bv 64 (ip_p P + 1));
          [ rewrite <- (Z_to_bv_bv_unsigned _ (sv_denot E2 (SOff 32 1))); f_equal;
            change (bv_unsigned (sv_denot E2 (SOff 32 1))) with (U E2 (SOff 32 1));
            rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia;
            apply zcanon_id; unfold M64; lia |];
          pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HSe) as R10e;
          pose proof (st_ok_pi_restrict_reg _ _ _ _ 12%bv HSe) as R12e;
          cbn [ms_regs restrict] in R10e, R12e;
          (lazymatch type of R10e with _ = sv_denot _ (sr_get ?l _) =>
             let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in R10e;
             let v := eval vm_compute in (sr_get l 12%bv) in change (sr_get l 12%bv) with v in R12e end);
          rewrite D32 in R10e, R12e
        end.
        assert (Hpd : ip_p P + 1 = ip_p P \/ (ip_p P + 1 = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\ exists b0, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b0 /\ PjGrammar.ws b0 = true))
          by (right; split; [reflexivity | split; [exact Hpe | exists b; split; [exact Hnth | exact Hws]]]).
        vk_leave CTX CTX0 CW E P HEN (proj1 HW1) E8u E32 E33 HA R23 R27 HJ HPM (ip_p P + 1) Hpd.
        split; [reflexivity|]. split; [reflexivity|]. right. split; [unfold vrd_cfg; vk_proj; reflexivity|].
        split; [|vk_proj; reflexivity].
        split; [exact HH'|]. vk_proj. split; [exact R10e|]. split; [exact R12e|]. lia.
      * (* row 131 not taken: p + 1 = end: row 132 jumps to row 136 *)
        match goal with Hb3 : branch_taken _ (sv_denot ?E' _) _ = false |- _ =>
          assert (Heq : ip_p P + 1 = ie_text E + ie_len E);
          [ rewrite branch_ne_U in Hb3;
            rewrite (U_SOff E' 32 1), (U_SOff E' 33 0) in Hb3; cbn [ew ewset Nat.eqb] in Hb3;
            rewrite E32, E33 in Hb3; unfold w64 in Hb3; rewrite !unsigned_lit_small in Hb3 by lia;
            rewrite !zcanon_id in Hb3 by (unfold M64; lia); rewrite Z.add_0_r in Hb3;
            apply Bool.negb_false_iff, Z.eqb_eq in Hb3; exact Hb3 | ] end.
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_C1_SLOT); [vk_awr E8u HSTK|].
        assert (Hpd : ip_p P + 1 = ip_p P \/ (ip_p P + 1 = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\ exists b0, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b0 /\ PjGrammar.ws b0 = true))
          by (right; split; [reflexivity | split; [exact Hpe | exists b; split; [exact Hnth | exact Hws]]]).
        vk_leave CTX CTX0 CW E P HEN (proj1 HW1) E8u E32 E33 HA R23 R27 HJ HPM (ip_p P + 1) Hpd.
        split; [reflexivity|]. split; [reflexivity|]. left. split; [unfold vrd_cfg; vk_proj; reflexivity|].
        split; [exact HH'|]. left. vk_proj. exact Heq.
Qed.

(* the first white-space loop, rows 117..135, by the loop rule with measure end - p *)
Lemma vk_w1_loop_P : forall CTX CTX0 CW E P (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_w1 E P -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_W1_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg VK_C1_SLOT P' /\ ip_n P' = ip_n P /\ vk_c1 E P')
                  /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P Pm PLAW HEN HW1 HPM.
  apply (SRr'_loopZ SEGS YGcfRehidePost.RZ_cf vrd_ipos (fun x => ie_text E + ie_len E - ip_p x)
           (fun x W c => W = ip_W x /\ c = vrd_cfg VK_W1_SLOT x /\ vk_w1 E x /\ Pm (ip_mem x) /\ ip_n x = ip_n P)
           (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg VK_C1_SLOT P' /\ ip_n P' = ip_n P /\ vk_c1 E P')
                         /\ Pm (ms_mem (cfg_ms c2))))
    with (x := P); [|auto].
  intros x W c (-> & -> & Hx & HPx & Hnx).
  eapply SRr'_mono; [exact (vk_w1_step_P CTX CTX0 CW E x Pm PLAW HEN Hx HPx)|].
  intros W' c' _ ((P' & -> & Hn' & [(-> & HC) | (-> & HW' & Hp)]) & HPc).
  - left. split; [exists P'; split; [reflexivity|]; split; [reflexivity|]; split; [congruence | exact HC] | exact HPc].
  - right. exists P'. split.
    + destruct HW' as (_ & _ & _ & Hlt). destruct Hx as (_ & _ & _ & Hlt0). lia.
    + split; [reflexivity|]. split; [reflexivity|]. split; [exact HW'|].
      cbn [vrd_cfg cfg_ms ms_mem] in HPc. split; [exact HPc | congruence].
Qed.

(* ---- 5. C1, rows 136..148: the opening quote of the key, or a refusal ---- *)
Definition VK_CALL_SLOT : nat := 6080%nat.   (* row 148, A 0x874e0: `jal parse_string` *)
(* the call state: a0 = q at the jal (a1 = 34 there, so not vk_head), the byte at p is the opening quote *)
Definition vk_call (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vrd_iframe E P /\ vrd_iregs B E P /\ vrd_inode E P [] /\ vrd_icur B E P /\ vrd_ijrn B ARx SK E P /\
  vrd_imodel E P /\ ip_n P < ip_cap P /\
  ip_cont P = vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P)
                 (ip_f P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
  ie_o E = true /\ ip_p P < ie_text E + ie_len E /\
  nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some 34 /\ getr (ip_regs P) 10 = w64 (ie_q E) /\
  vk_k1h E P.
(* a refusal at the join (row 310): s2 = -1 (so vrd_iregs no longer holds; gp / tp do), the position's memory facts,
   and the model refuses there (p = end, or a byte that is neither white space nor the opening quote) *)
Definition vk_refA (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vrd_iframe E P /\ vrd_inode E P [] /\ vrd_icur B E P /\ vrd_ijrn B ARx SK E P /\ vrd_imodel E P /\
  ip_cont P = vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P)
                 (ip_f P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
  ie_o E = true /\
  getr (ip_regs P) 3 = w64 (as_gp B) /\ getr (ip_regs P) 4 = w64 (as_tp B) /\ getr (ip_regs P) 18 = w64 (-1) /\
  (ip_p P = ie_text E + ie_len E \/
   (ip_p P < ie_text E + ie_len E /\ exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\
      PjGrammar.ws b = false /\ b <> 34)) /\
  vk_k1h E P.

(* the C1 state with the byte at p seated: the cursor read-only, the byte as atom 34 *)
Definition vk_ssC (k : nat) : sstate := mkSS (4 * Z.of_nat k) vk_sr0 [vk_cur_region false; vk_byte_region] None vk_factsW.

Lemma vk_seatC : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q p en b (k : nat),
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 23 = w64 (shadow_addr (q + 8)) -> getr regs 27 = w64 (shadow_addr q) ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  4096 <= p <= 2 ^ 47 - 8 -> 4096 <= en <= 2 ^ 47 - 8 ->
  val_mem SEGS (mrestrict (w_H W) mem) p 1 b -> 0 <= b < 256 -> (p + 1 <= q \/ q + 24 <= p) ->
  rd_rw SEGS (mrestrict (w_H W) mem) q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  st_ok_pi (fx := fxP) SEGS VAL (vk_EW regs p en b) (vk_ssC k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vk_SH0 (vk_EW regs p en b) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q p en b k R8 R26 R23 R27 Hq1 Hq2 Hq8 Vp Ve Hp He Vb Hb Hdj Hrw Hra.
  set (EW := vk_EW regs p en b).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EW j = getr regs r).
  { intros j Hj r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E8 : ew EW 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew EW 32 = w64 p).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew EW 33 = w64 en).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (E34 : ew EW 34 = w64 b).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Uq : U EW (SOff 8 0) = q).
  { unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. lia. }
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF).
  { unfold U. cbn [sv_denot]. rewrite E26, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
  assert (S32 : sv_denot EW (SOff 32 0) = w64 p).
  { cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (S33 : sv_denot EW (SOff 33 0) = w64 en).
  { cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vk_ssC. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vk_sr0.
      apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |] | reflexivity |].
      * rewrite R23. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EW (vk_sh_of 8)).
        rewrite (vk_U_sh EW q 8 E8 E26) by lia. unfold shadow_addr.
        assert (0 <= (q + 8) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
      * rewrite R27. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EW (vk_sh_of 0)).
        rewrite (vk_U_sh EW q 0 E8 E26) by lia. unfold shadow_addr. rewrite Z.add_0_r.
        assert (0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
    + reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold region_ok, vk_cur_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E8. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split.
        -- intros a Ha. lia.
        -- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
           ++ apply (chunk_ok_val SEGS EW _ q 0 8 (SOff 32 0) p); [exact S32 | cbn; lia | cbn; lia |].
              rewrite Z.add_0_r. exact Vp.
           ++ apply (chunk_ok_val SEGS EW _ q 8 8 (SOff 33 0) en); [exact S33 | cbn; lia | cbn; lia |].
              exact Ve.
      * unfold region_ok, vk_byte_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS EW _ p 0 1 (SOff 34 0) b);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vb.
    + apply pairwise_disjoint_of_extents. unfold vk_cur_region, vk_byte_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite E8, E32. unfold w64. rewrite !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [vk_factsW f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E8, E26, E32, E33, E34. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vk_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) mem EW (SOff 26 0) 8 q 24 q 0 24 Hra UB Uq); [lia | lia |].
    intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

(* a run over read-only regions writes nothing *)
Lemma vk_frame_ro_gen : forall E' rs (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E' rs m m' -> m' = m.
Proof.
  intros E' rs m m' Hro HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Hr). rewrite Forall_forall in Hro. pose proof (Hro r Hin). lia.
Qed.

Ltac vk_mem_same P HM :=
  lazymatch goal with HSe : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
    assert (HM : ms_mem ms = ip_mem P)
      by (repeat match goal with HF : frame_of _ ?rs ?m ?m' |- ?m' = _ =>
            rewrite (vk_frame_ro_gen _ rs m m'
                       ltac:(let rs' := eval vm_compute in rs in change rs with rs'; repeat constructor; cbn; lia) HF)
          end; reflexivity)
  end.

Definition vk_c1_post (E : vrd_ient) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P', W2 = ip_W P' /\
    ((c2 = vrd_cfg VK_CALL_SLOT P' /\ vk_call E P') \/ (c2 = vrd_cfg A_IEPI_SLOT P' /\ vk_refA E P')).
(* the same post with the element count of the reached position (the loop's progress, VrdIElem.tvrd_ikey_aP) *)
Definition vk_c1_postn (E : vrd_ient) (n : Z) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P', W2 = ip_W P' /\ ip_n P' = n /\
    ((c2 = vrd_cfg VK_CALL_SLOT P' /\ vk_call E P') \/ (c2 = vrd_cfg A_IEPI_SLOT P' /\ vk_refA E P')).

Lemma vk_c1_step_P : forall CTX CTX0 CW E P (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_c1 E P ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_C1_SLOT P)
    (fun W2 c2 => vk_c1_postn E (ip_n P) W2 c2 /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P Pm PLAW HEN (HH & Hcase) HPM.
  pose proof HH as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Hcont & Ho & R11 & HK1).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ. pose proof HJN as (_ & HJrest).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof Hsrc as (_ & Ht4 & Htl8 & _ & Hrat & _).
  rewrite Hlen in Htl8.
  pose proof asan_consts as (C1 & _).
  destruct (vk_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  assert (HSTK : 0 <= STK_parse_items (ie_d E)).
  { destruct HEN as ((HAF & _) & _). destruct HAF as (_ & _ & _ & _ & _ & Hstk & _). exact (proj1 (proj2 Hstk)). }
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  assert (R2r : forall regs', getr regs' 2 = getr (ip_regs P) 2 -> spZ regs' = spZ (ip_regs P))
    by (intros regs' H; unfold spZ; rewrite H; reflexivity).
  destruct Hcase as [Hend | (Hlt & b & Hnth & Hnws)].
  - (* p = end: rows 136..139, the bgeu is taken to row 309, then s2 := -1 *)
    destruct (vk_seat0 (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) false
                VK_C1_SLOT G8 G26 G23 G27 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Hrw Hraq) as [HS SHOK].
    set (EO := vk_EO (ip_regs P) (ip_p P) (ie_text E + ie_len E)) in *.
    assert (HEI : img_env VAL A_LIM EO) by (unfold EO, vk_EO; apply Eimg_env).
    assert (E11 : ew EO 11 = w64 (ie_text E + ie_len E)).
    { unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
      rewrite (ew_Ereg_nat (ip_regs P) _ 11 11%bv eq_refl). exact R11. }
    assert (E32 : ew EO 32 = w64 (ip_p P)).
    { unfold EO, vk_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
    assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E)]) EO)
      by (split; [intros k Hk; unfold EO, vk_EO; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
                 | reflexivity]).
    unfold vrd_cfg.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
    psrr_branch_tok RUN BR HS SHOK vk_Bspan.
    + paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat A_IEPI_SLOT);
        [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
      vk_mem_same P HM.
      lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
        assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E)]) E2)
          by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros k Hk; cbn [ew ewset];
              repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
        assert (HR : forall r, In r [2; 3; 4]%bv -> getr (ms_regs ms2) r = getr (ip_regs P) r)
          by exact (regs_kept_of_st_ok_pi _ _ _ (ip_regs P) _ [2; 3; 4]%bv HSe HA2 ltac:(vm_compute; reflexivity));
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 18%bv HSe) as R18e;
        cbn [ms_regs restrict] in R18e;
        (lazymatch type of R18e with _ = sv_denot _ (sr_get ?l _) =>
           let v := eval vm_compute in (sr_get l 18%bv) in change (sr_get l 18%bv) with v in R18e end);
        cbn [sv_denot] in R18e;
        rewrite HM in HJ;
        lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD _ =>
          pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
          exists (vk_with P (ms_regs ms2) MD) end;
        split; [reflexivity|]; split; [reflexivity|]; right; split;
        [ unfold vrd_cfg, vk_with; cbn [ip_fx ip_regs ip_mem ip_md]; rewrite HM; reflexivity |];
        assert (R2' : spZ (ms_regs ms2) = spZ (ip_regs P)) by (apply R2r; apply HR; cbn; tauto)
      end.
      unfold vk_refA, vk_with. cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
        ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
      split; [unfold vrd_iframe in *; cbv zeta in *; cbn [ip_regs ip_mem ip_W]; rewrite R2'; exact HFR|].
      split; [exact HND|]. split; [exact HCU|].
      split; [exact (conj (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) HJrest)|]. split; [exact HMD|].
      split; [exact Hcont|]. split; [exact Ho|].
      split; [rewrite (HR 3%bv ltac:(cbn; tauto)); exact G3|].
      split; [rewrite (HR 4%bv ltac:(cbn; tauto)); exact G4|].
      split; [rewrite R18e; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
      split; [left; exact Hend | exact HK1].
    + (* the bgeu not taken: refuted, p = end *)
      exfalso. match goal with Hb : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = false |- _ =>
        rewrite branch_geu_U, (U_SOff E' 32 0), (U_SOff E' 11 0) in Hb; cbn [ew ewset Nat.eqb] in Hb;
        rewrite E32, E11 in Hb; unfold w64 in Hb; rewrite !unsigned_lit_small in Hb by lia;
        rewrite !Z.add_0_r, !zcanon_id in Hb by (unfold M64; lia);
        apply Bool.negb_false_iff, Z.ltb_lt in Hb; lia end.
  - (* p < end: the byte at p, rows 136..146 *)
    assert (Hj : (Z.to_nat (ip_p P - ie_text E) < length (ie_tb E))%nat) by lia.
    destruct (Hga _ Hj) as [Vb Hb].
    rewrite (nth_error_nth' _ 0 Hj) in Hnth. injection Hnth as Hbv.
    replace (ie_text E + Z.of_nat (Z.to_nat (ip_p P - ie_text E))) with (ip_p P) in Vb by lia.
    rewrite Hbv in Vb, Hb.
    assert (Hnth : nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b)
      by (rewrite <- Hbv; apply nth_error_nth'; exact Hj).
    destruct (vk_seatC (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) b VK_C1_SLOT
       G8 G26 G23 G27 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Vb Hb ltac:(lia) Hrw Hraq) as [HS SHOK].
    set (EW := vk_EW (ip_regs P) (ip_p P) (ie_text E + ie_len E) b) in *.
    assert (HEI : img_env VAL A_LIM EW) by (unfold EW, vk_EW; apply Eimg_env).
    assert (EL : forall k, (k < 32)%nat -> forall r : bv 5, Z.of_nat k = bv_unsigned r -> ew EW k = getr (ip_regs P) r).
    { intros k Hk r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
      exact (ew_Ereg_nat (ip_regs P) _ k r Hr). }
    assert (E8 : ew EW 8 = w64 (ie_q E)) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact G8).
    assert (E11 : ew EW 11 = w64 (ie_text E + ie_len E)) by (rewrite (EL 11%nat ltac:(lia) 11%bv eq_refl); exact R11).
    assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact G26).
    assert (E32 : ew EW 32 = w64 (ip_p P)).
    { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
    assert (E34 : ew EW 34 = w64 b).
    { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 2). }
    assert (UB : U EW (SOff 26 0) = SHADOW_OFF) by (apply (U_atom EW 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
    assert (U32 : U EW (SOff 32 0) = ip_p P) by (apply (U_atom EW 32 (ip_p P) E32); lia).
    assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) EW)
      by (split; [intros k Hk; unfold EW, vk_EW; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
                 | reflexivity]).
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
    change (sr_get (ss_regs (vk_ssC VK_C1_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
    change (sr_get (ss_regs (vk_ssC VK_C1_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
    unfold vrd_cfg.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan;
      [ first [ vk_ra_byte Hrat UB U32
              | lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ =>
                  let rs' := eval vm_compute in rs in change rs with rs';
                  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil end ] .. | ].
    psrr_branch_tok RUN BR HS SHOK vk_Bspan.
    + (* the bgeu taken: refuted, p < end *)
      exfalso. match goal with Hb1 : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = true |- _ =>
        rewrite branch_geu_U, (U_SOff E' 32 0), (U_SOff E' 11 0) in Hb1; cbn [ew ewset Nat.eqb] in Hb1;
        rewrite E32, E11 in Hb1; unfold w64 in Hb1; rewrite !unsigned_lit_small in Hb1 by lia;
        rewrite !Z.add_0_r, !zcanon_id in Hb1 by (unfold M64; lia);
        apply Bool.negb_true_iff, Z.ltb_ge in Hb1; lia end.
    + vk_mem_same P HM1.
      paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan;
        [ first [ rewrite HM1, UB, U32; intros y Hy; apply Hrat; lia
                | lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ =>
                    let rs' := eval vm_compute in rs in change rs with rs';
                    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil end ] .. | ].
      psrr_branch_tok RUN BR HS SHOK vk_Bspan.
      * (* row 146 taken: b <> 34: on to row 309, s2 := -1, row 310 *)
        assert (Hb34 : b <> 34).
        { match goal with Hb2 : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = true |- _ =>
            rewrite branch_ne_U, (U_SOff E' 34 0), (U_lit E' 34) in Hb2 by lia; cbn [ew ewset Nat.eqb] in Hb2;
            rewrite E34 in Hb2; unfold w64 in Hb2; rewrite unsigned_lit_small in Hb2 by lia;
            rewrite Z.add_0_r, zcanon_id in Hb2 by (unfold M64; lia);
            apply Bool.negb_true_iff, Z.eqb_neq in Hb2; exact Hb2 end. }
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat A_IEPI_SLOT);
          [ lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ =>
              let rs' := eval vm_compute in rs in change rs with rs';
              repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil end |].
        vk_mem_same P HM.
        lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
          assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) E2)
            by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros k Hk; cbn [ew ewset];
                repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
          assert (HR : forall r, In r [2; 3; 4]%bv -> getr (ms_regs ms2) r = getr (ip_regs P) r)
            by exact (regs_kept_of_st_ok_pi _ _ _ (ip_regs P) _ [2; 3; 4]%bv HSe HA2 ltac:(vm_compute; reflexivity));
          pose proof (st_ok_pi_restrict_reg _ _ _ _ 18%bv HSe) as R18e;
          cbn [ms_regs restrict] in R18e;
          (lazymatch type of R18e with _ = sv_denot _ (sr_get ?l _) =>
             let v := eval vm_compute in (sr_get l 18%bv) in change (sr_get l 18%bv) with v in R18e end);
          cbn [sv_denot] in R18e;
          rewrite HM in HJ;
          lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD _ =>
            pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
          exists (vk_with P (ms_regs ms2) MD) end;
          split; [reflexivity|]; split; [reflexivity|]; right; split;
          [ unfold vrd_cfg, vk_with; cbn [ip_fx ip_regs ip_mem ip_md]; rewrite HM; reflexivity |];
          assert (R2' : spZ (ms_regs ms2) = spZ (ip_regs P)) by (apply R2r; apply HR; cbn; tauto)
        end.
        unfold vk_refA, vk_with. cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
          ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
        split; [unfold vrd_iframe in *; cbv zeta in *; cbn [ip_regs ip_mem ip_W]; rewrite R2'; exact HFR|].
        split; [exact HND|]. split; [exact HCU|].
        split; [exact (conj (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) HJrest)|]. split; [exact HMD|].
        split; [exact Hcont|]. split; [exact Ho|].
        split; [rewrite (HR 3%bv ltac:(cbn; tauto)); exact G3|].
        split; [rewrite (HR 4%bv ltac:(cbn; tauto)); exact G4|].
        split; [rewrite R18e; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
        split; [|exact HK1].
        right. split; [exact Hlt|]. exists b. split; [exact Hnth|]. split; [exact Hnws | exact Hb34].
      * (* row 146 not taken: b = 34: row 147 a0 := s0, to the jal at row 148 *)
        assert (Hb34 : b = 34).
        { match goal with Hb2 : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = false |- _ =>
            rewrite branch_ne_U, (U_SOff E' 34 0), (U_lit E' 34) in Hb2 by lia; cbn [ew ewset Nat.eqb] in Hb2;
            rewrite E34 in Hb2; unfold w64 in Hb2; rewrite unsigned_lit_small in Hb2 by lia;
            rewrite Z.add_0_r, zcanon_id in Hb2 by (unfold M64; lia);
            apply Bool.negb_false_iff, Z.eqb_eq in Hb2; exact Hb2 end. }
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_CALL_SLOT);
          [ lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ =>
              let rs' := eval vm_compute in rs in change rs with rs';
              repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil end |].
        vk_mem_same P HM.
        lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
          assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) E2)
            by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros k Hk; cbn [ew ewset];
                repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
          assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
            by (eapply (vk_regs_after _ _ _ _ _ _ _ HSe HA2);
                [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
                | rewrite R23; reflexivity | rewrite R27; reflexivity]);
          pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HSe) as R10e;
          cbn [ms_regs restrict] in R10e;
          (lazymatch type of R10e with _ = sv_denot _ (sr_get ?l _) =>
             let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in R10e end);
          cbn [sv_denot] in R10e; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R10e;
          cbn [ew ewset Nat.eqb] in R10e; rewrite E8 in R10e;
          rewrite HM in HJ;
          lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD _ =>
            pose proof (vk_with_ok E P (ms_regs ms2) MD HRk (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
                          HFR HRG HND HCU HJN HMD) as (V1 & V2 & V3 & V4 & V5 & V6);
            pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
          exists (vk_with P (ms_regs ms2) MD) end;
          split; [reflexivity|]; split; [reflexivity|]; left; split;
          [ unfold vrd_cfg, vk_with; cbn [ip_fx ip_regs ip_mem ip_md]; rewrite HM; reflexivity |]
        end.
        split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|].
        split; [exact V6|].
        unfold vk_with. cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
          ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
        split; [exact Hnc|]. split; [exact Hcont|]. split; [exact Ho|]. split; [exact Hlt|].
        split; [rewrite Hnth, Hb34; reflexivity|]. split; [exact R10e | exact HK1].
Qed.


(* ---- 6. REFUSE-A: the join's refusal, as the loop's exit boundary ---- *)
Lemma vk_refA_exit : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vk_refA E P ->
  vrd_iexit_a B ARx SK E P (-1).
Proof.
  intros CTX CTX0 CW E P HEN (HFR & HND & HCU & HJN & HMD & Hcont & Ho & G3 & G4 & G18 & Hcase & HK1).
  pose proof HCU as (Hin & _ & _ & _ & Hled & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd32).
  pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11).
  (* the model's name refuses at p, with no event and no grant eaten *)
  assert (Hname : PjGrammar.jr_name true (rest_atR (ie_tb E) (ie_text E) (ip_p P)) [] = (None, [], [])).
  { destruct Hcase as [Hend | (Hlt & b & Hnth & Hnws & Hb34)].
    - assert (Hr : rest_atR (ie_tb E) (ie_text E) (ip_p P) = []) by (unfold rest_atR; apply skipn_all2; lia).
      rewrite Hr. reflexivity.
    - rewrite (vk_rest_cons (ie_tb E) (ie_text E) (ip_p P) b ltac:(lia) Hnth).
      unfold PjGrammar.jr_name. cbn [PjGrammar.skip]. rewrite Hnws.
      rewrite (proj2 (Z.eqb_neq b 34) Hb34). reflexivity. }
  assert (Hcont0 : ip_cont P [] = (None, [], [])).
  { rewrite Hcont, Ho. unfold vrd_jtail, PjGrammar.jbind. rewrite Hname. reflexivity. }
  assert (Hans : PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
                   (ip_ok P) = (None, ip_tr P, [])).
  { pose proof (M2 []) as H. rewrite app_nil_r in H. rewrite H, Hcont0. cbn [fst snd]. rewrite app_nil_r. reflexivity. }
  unfold vrd_iexit_a.
  split; [exact HFR|]. split; [exact HJN|]. split; [exact G3|]. split; [exact G4|]. split; [exact G18|].
  split; [right; reflexivity|]. split; [exact Hled|]. split; [exact (proj1 M4)|]. split; [exact M9|].
  split; [exact (vc_outc_granted E P None [] M1 Hans M3 M9)|].
  split; [exact M3|]. split; [exact M6|]. split; [exact M8|].
  (* the hull use over the call's all-granted events: the events so far, then nothing (no callee since), then the
     rest of the granted continuation (VrdCallPos.vc_gt_split, VrdIElem.vrd_huse_out with an empty callee list); the
     outcome of an injected reading: the exit is on the granted prefix, no call refused (VrdIElem.vrd_inj_granted) *)
  split; [|split; [exact M10|split; [
    rewrite (vc_gt_split E P HMD), PresetHullBudget.hull_rd_app;
    exact (vrd_huse_out _ _ _ _ [] _ M11 (PresetHullBudget.hull_used_refl _ _)) | exact (vrd_inj_granted E P M1)]]].
  exists [], [].
  split; [exact Hans|].
  split; [intros H; discriminate H|].
  intros _. split; [|split].
  - exists (ip_p P), (Z.of_nat (ie_d E) + 1). split; [exact Hpp|]. split; [lia|]. exact (conj Vp (conj Ve (conj Vd Hrw))).
  - exact (vrd_inode_fd B ARx SK LAWS CTX CTX0 CW E P HEN HND HCU HJN HMD).
  - (* The kit's cut, the None arm's free order: the model's free list at the refused name is jfl's body's None arm, the
       completed slots' list then the arrays (VrdIElem.vrd_jfb), which is the open node's order list
       (VrdIFd.vrd_inode_fo) at every depth bound above the members' *)
    destruct HK1 as (Hcap1 & Hinc & af & HFO & HFL).
    assert (HFL0 : prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
                   af ++ PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P))).
    { rewrite <- (app_nil_r (ip_ok P)), (HFL []). unfold vrd_jfb. rewrite Ho, Hname. reflexivity. }
    intros Hh n0 Hn0.
    assert (Hdlt : (ie_d E < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
    destruct n0 as [|nn]; [lia|].
    assert (Hdep : Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) (ip_acc P))
      by (apply (vi_dep_le (ip_acc P) (PjGrammar.MAXD - S (ie_d E)) nn); [lia | exact M7]).
    assert (HF : exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (S nn)
                   (ie_v E) (ip_D P) F /\
                   map (fun b => snd b + cf_head) F = af ++ PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P)))
      by (eapply vrd_inode_fo; eassumption).
    destruct HF as (F & HF & HFm). exists F. split; [exact HF|]. rewrite HFm, HFL0. reflexivity.
Qed.


(* ---- 7. the call of parse_string at row 148 (slot 6080), returning to row 149 (slot 6081) ---- *)
Definition VK_RET_SLOT : nat := 6081%nat.
Hypothesis Hs0ps : pi_s0cur F_parse_string = Some 0.
(* the instance fact that parse_string's event lists (cf_head) meet the position's rd_hevs (the model's HEAD): the
   one spelling, VrdIStep.v's HI_head, discharged by reflexivity at CfParams_preset *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.

Lemma vk_stk_budget : forall d, STK_parse_string + 144 <= STK_parse_items d.
Proof.
  intros d. unfold STK_parse_items, LEAF_pv_pi, zmaxl. cbn [fold_right].
  pose proof (pi_frame_nonneg F_parse_items). pose proof (pi_frame_nonneg F_parse_value).
  assert (0 <= Z.of_nat (PjGrammar.MAXD - d) * (pi_frame F_parse_value + pi_frame F_parse_items))
    by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Hfr144 in *. lia.
Qed.

(* the stack bound of parse_string's frame *)
Lemma vk_stk_ps_nonneg : 0 <= STK_parse_string.
Proof.
  assert (Hz : forall l, 0 <= zmaxl l) by (intros l; unfold zmaxl; induction l; cbn [fold_right]; lia).
  unfold STK_parse_string. pose proof (pi_frame_nonneg F_parse_string). pose proof (Hz [STK_fuzz_free; STK_fuzz_malloc; STK_hex4; STK_put_utf8]).
  lia.
Qed.

(* the granted trace at the opening quote starts with the string's block *)
Lemma vk_jbind_hd : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok x,
  hd_error (snd (fst (m ok))) = Some x -> hd_error (snd (fst (PjGrammar.jbind m k ok))) = Some x.
Proof.
  intros A C m k ok x H. unfold PjGrammar.jbind. destruct (m ok) as [[[a|] t] ok1]; cbn [fst snd] in H |- *.
  - destruct (k a ok1) as [[r t'] ok2]. cbn [fst snd]. destruct t; [discriminate H | exact H].
  - exact H.
Qed.

Lemma vk_hd_exists : forall (l : list PjGrammar.ev) x, hd_error l = Some x -> exists t', l = x :: t'.
Proof. intros [|y l] x H; [discriminate H|]. injection H as ->. exists l. reflexivity. Qed.

Lemma vk_gt_head : forall d n cap1 acc f tb text p Q,
  text <= p -> nth_error tb (Z.to_nat (p - text)) = Some 34 ->
  PjGrammar.scan (rest_atR tb text (p + 1)) = Some Q ->
  exists t', snd (fst (vrd_jtail d true n cap1 acc f (rest_atR tb text p) [])) = PjGrammar.EAlloc (S Q) :: t'.
Proof.
  intros d n cap1 acc f tb text p Q Hp Hnth Hsc. apply vk_hd_exists.
  rewrite (vk_rest_cons tb text p 34 Hp Hnth).
  unfold vrd_jtail. apply vk_jbind_hd.
  unfold PjGrammar.jr_name. cbn [PjGrammar.skip PjGrammar.ws Z.eqb Pos.eqb orb]. apply vk_jbind_hd.
  unfold PjGrammar.jr_string. rewrite Hsc. apply vk_jbind_hd. reflexivity.
Qed.

(* the room the call at the quote has, from the position's rd_room over its granted continuation: the request bound,
   and (the kit's cut: rd_room's live room is per event, PRH_Base.prh_live_evs) the live room at the string's own event *)
Lemma vk_room_head : forall (S0 : astate) Q t',
  rd_room S0 (PjGrammar.EAlloc (Datatypes.S Q) :: t') ->
  LIVE_parse_string Q < cf_malloc_max /\
  prh_live_evs S0 (PresetReqAt.rd_hevs [PjGrammar.EAlloc (Datatypes.S Q)]).
Proof.
  intros S0 Q t' (_ & Hmax & Hlive). split.
  - unfold prh_maxreq in Hmax. unfold LIVE_parse_string. cbn [map fold_right PjGrammar.esize] in Hmax.
    pose proof (@cf_head_nonneg cp).
    assert (0 <= fold_right Z.max 0 (map (fun e => Z.of_nat (PjGrammar.esize e)) t'))
      by (induction t'; cbn [map fold_right]; lia).
    lia.
  - change (PresetReqAt.rd_hevs (PjGrammar.EAlloc (Datatypes.S Q) :: t')) with
      (PresetReqAt.rd_hevs [PjGrammar.EAlloc (Datatypes.S Q)] ++ PresetReqAt.rd_hevs t') in Hlive.
    exact (vl_live_evs_prefix _ _ _ Hlive).
Qed.



(* ---- the model at the key's opening quote, for each outcome of parse_string ---- *)
(* the rest of jr_name after the string returned (name, r): the colon, else the name's block is given back *)
Definition vk_kname (z name r : list Z) : PjGrammar.M (list Z * list Z) :=
  match PjGrammar.skip r with
  | c :: r1 => if c =? 58 then PjGrammar.jret (name, r1)
               else PjGrammar.jbind (PjGrammar.jfree (PjGrammar.sblock z)) (fun _ => PjGrammar.jrefuse)
  | [] => PjGrammar.jbind (PjGrammar.jfree (PjGrammar.sblock z)) (fun _ => PjGrammar.jrefuse)
  end.
Definition vk_kont (d : nat) (n cap1 : nat) (acc : list (list Z * jv)) (f : nat) (z name r : list Z)
  : PjGrammar.M (jv * list Z) :=
  PjGrammar.jbind (vk_kname z name r) (fun '(name1, y1) => vrd_jval d true n cap1 acc f name1 y1).

(* The kit's cut: THE MODEL'S FREE LIST AFTER THE KEY, vk_kname's twin over jfl's body (VrdIElem.vrd_jfvk): the colon goes
   on to jfl's body after the key at the rest after it; anything else gives the key's block back, so the call's free
   list is the completed slots' list then the arrays (the text VrdIKeyB's colon test reads) *)
Definition vk_jfk (f d n cap1 : nat) (af lk r : list Z) (ok : list bool) : list Z :=
  match PjGrammar.skip r with
  | c :: r1 => if c =? 58 then vrd_jfvk f d true n cap1 af lk r1 ok else af ++ PresetReqAt.arrz true cap1
  | [] => af ++ PresetReqAt.arrz true cap1
  end.

(* across a white-space byte before the colon: vk_kname skips it, and so does vk_jfk *)
Lemma vk_jfk_ws : forall f d n cap1 af lk tb text p b ok, text <= p ->
  nth_error tb (Z.to_nat (p - text)) = Some b -> PjGrammar.ws b = true ->
  vk_jfk f d n cap1 af lk (rest_atR tb text p) ok = vk_jfk f d n cap1 af lk (rest_atR tb text (p + 1)) ok.
Proof.
  intros f d n cap1 af lk tb text p b ok Hp Hb Hws. rewrite (vk_rest_cons tb text p b Hp Hb).
  unfold vk_jfk. cbn [PjGrammar.skip]. rewrite Hws. reflexivity.
Qed.

(* the free list after the grow (vrd_jfb) at a name the model refuses: the completed slots' list then the arrays *)
Lemma vk_jfb_none : forall f d o n cap1 af y ok t ok', PjGrammar.jr_name o y ok = (None, t, ok') ->
  vrd_jfb f d o n cap1 af y ok = af ++ PresetReqAt.arrz o cap1.
Proof. intros f d o n cap1 af y ok t ok' H. unfold vrd_jfb. rewrite H. reflexivity. Qed.

Lemma vk_jbind_none : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok t ok1,
  m ok = (None, t, ok1) -> PjGrammar.jbind m k ok = (None, t, ok1).
Proof. intros A C m k ok t ok1 H. unfold PjGrammar.jbind. rewrite H. reflexivity. Qed.

Lemma vk_jbind_some : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok a t ok1,
  m ok = (Some a, t, ok1) ->
  PjGrammar.jbind m k ok = (fst (fst (k a ok1)), t ++ snd (fst (k a ok1)), snd (k a ok1)).
Proof. intros A C m k ok a t ok1 H. unfold PjGrammar.jbind. rewrite H. destruct (k a ok1) as [[r t'] ok2]. reflexivity. Qed.

Section quote.
Variables (d n cap1 : nat) (acc : list (list Z * jv)) (f : nat) (tb : list Z) (text p : Z).
Hypothesis Hp : text <= p.
Hypothesis Hnth : nth_error tb (Z.to_nat (p - text)) = Some 34.
Let z := rest_atR tb text (p + 1).
Let K := vrd_jtail d true n cap1 acc f (rest_atR tb text p).

Lemma vk_K_unfold : K = PjGrammar.jbind (PjGrammar.jbind (PjGrammar.jr_string z) (fun '(name, r) => vk_kname z name r))
                          (fun '(name, y1) => vrd_jval d true n cap1 acc f name y1).
Proof.
  unfold K, z, vrd_jtail. rewrite (vk_rest_cons tb text p 34 Hp Hnth).
  unfold PjGrammar.jr_name. cbn [PjGrammar.skip PjGrammar.ws Z.eqb Pos.eqb orb]. reflexivity.
Qed.

(* no closing quote: the model refuses with no event *)
Lemma vk_K_noscan : PjGrammar.scan z = None -> forall okr, K okr = (None, [], okr).
Proof.
  intros Hs okr. rewrite vk_K_unfold. apply vk_jbind_none. apply vk_jbind_none.
  unfold PjGrammar.jr_string. rewrite Hs. reflexivity.
Qed.

(* the string's block is refused (the chosen failure or the allocator's refusal): one EFail *)
Lemma vk_K_fail : forall Q, PjGrammar.scan z = Some Q -> forall okr,
  K (false :: okr) = (None, [PjGrammar.EFail (S Q)], okr).
Proof.
  intros Q Hs okr. rewrite vk_K_unfold. apply vk_jbind_none. apply vk_jbind_none.
  unfold PjGrammar.jr_string. rewrite Hs. apply vk_jbind_none. reflexivity.
Qed.

(* a bad escape: the block is taken and given back *)
Lemma vk_K_badesc : forall Q, PjGrammar.scan z = Some Q -> PjGrammar.decode z = None -> forall okr,
  K (true :: okr) = (None, [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)], okr).
Proof.
  intros Q Hs Hd okr. rewrite vk_K_unfold. apply vk_jbind_none. apply vk_jbind_none.
  unfold PjGrammar.jr_string. rewrite Hs. unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take.
  cbn beta iota. rewrite Hd. reflexivity.
Qed.

(* the string: the block, then the rest of the name and the value *)
Lemma vk_K_str : forall Q s r, PjGrammar.scan z = Some Q -> PjGrammar.decode z = Some (s, r) -> forall okr,
  K (true :: okr) =
    (fst (fst (vk_kont d n cap1 acc f z s r okr)),
     PjGrammar.EAlloc (S Q) :: snd (fst (vk_kont d n cap1 acc f z s r okr)),
     snd (vk_kont d n cap1 acc f z s r okr)).
Proof.
  intros Q s r Hs Hd okr. rewrite vk_K_unfold. unfold vk_kont.
  assert (Hstr : PjGrammar.jr_string z (true :: okr) = (Some (s, r), [PjGrammar.EAlloc (S Q)], okr)).
  { unfold PjGrammar.jr_string. rewrite Hs. unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take.
    cbn beta iota. rewrite Hd. reflexivity. }
  unfold PjGrammar.jbind. rewrite Hstr. cbn beta iota.
  destruct (vk_kname z s r okr) as [[[[nm y1]|] t1] ok1]; cbn beta iota.
  - destruct (vrd_jval d true n cap1 acc f nm y1 ok1) as [[r2 t2] ok2]. cbn [fst snd app]. reflexivity.
  - cbn [fst snd app]. reflexivity.
Qed.

(* The kit's cut, the model's FREE LIST at the quote (jfl's body after the grow, VrdIElem.vrd_jfb, reads jr_name alone): the
   name itself, on each outcome of the string *)
Lemma vk_N_unfold : forall ok, PjGrammar.jr_name true (rest_atR tb text p) ok =
  PjGrammar.jbind (PjGrammar.jr_string z) (fun '(name, r) => vk_kname z name r) ok.
Proof.
  intros ok. unfold z. rewrite (vk_rest_cons tb text p 34 Hp Hnth).
  unfold PjGrammar.jr_name. cbn [PjGrammar.skip PjGrammar.ws Z.eqb Pos.eqb orb]. reflexivity.
Qed.

Lemma vk_N_noscan : PjGrammar.scan z = None -> forall okr,
  PjGrammar.jr_name true (rest_atR tb text p) okr = (None, [], okr).
Proof.
  intros Hs okr. rewrite vk_N_unfold. apply vk_jbind_none. unfold PjGrammar.jr_string. rewrite Hs. reflexivity.
Qed.

Lemma vk_N_fail : forall Q, PjGrammar.scan z = Some Q -> forall okr,
  PjGrammar.jr_name true (rest_atR tb text p) (false :: okr) = (None, [PjGrammar.EFail (S Q)], okr).
Proof.
  intros Q Hs okr. rewrite vk_N_unfold. apply vk_jbind_none.
  unfold PjGrammar.jr_string. rewrite Hs. apply vk_jbind_none. reflexivity.
Qed.

Lemma vk_N_badesc : forall Q, PjGrammar.scan z = Some Q -> PjGrammar.decode z = None -> forall okr,
  PjGrammar.jr_name true (rest_atR tb text p) (true :: okr) =
    (None, [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)], okr).
Proof.
  intros Q Hs Hd okr. rewrite vk_N_unfold. apply vk_jbind_none.
  unfold PjGrammar.jr_string. rewrite Hs. unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take.
  cbn beta iota. rewrite Hd. reflexivity.
Qed.

(* the string in its block: jfl's body after the grow is the free list after the key (vk_jfk), with the key's
   request lf [EAlloc (S Q)] *)
Lemma vk_jfb_str : forall Q s r af okr, PjGrammar.scan z = Some Q -> PjGrammar.decode z = Some (s, r) ->
  vrd_jfb f d true n cap1 af (rest_atR tb text p) (true :: okr) =
  vk_jfk f d n cap1 af (PresetReqAt.lf [PjGrammar.EAlloc (S Q)]) r okr.
Proof.
  intros Q s r af okr Hs Hd. unfold vrd_jfb. rewrite (vk_N_unfold (true :: okr)).
  assert (Hstr : PjGrammar.jr_string z (true :: okr) = (Some (s, r), [PjGrammar.EAlloc (S Q)], okr)).
  { unfold PjGrammar.jr_string. rewrite Hs. unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take.
    cbn beta iota. rewrite Hd. reflexivity. }
  unfold PjGrammar.jbind at 1. rewrite Hstr. cbn beta iota.
  unfold vk_kname, vk_jfk. destruct (PjGrammar.skip r) as [|c r1]; [reflexivity|].
  destruct (c =? 58); reflexivity.
Qed.
End quote.

(* ---- parse_string's arm event lists ARE the model's (PRH_FnReader.prhPs_evs_model at HI_head), and jr_string's trace
   on each arm's outcomes ---- *)
Lemma vk_ps_evs : forall z ok, prhPs_evs z ok = PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_string z ok))).
Proof. intros z ok. exact (prhPs_evs_model z ok HI_head). Qed.

Lemma vk_jrs_noscan : forall z ok, PjGrammar.scan z = None -> snd (fst (PjGrammar.jr_string z ok)) = [].
Proof. intros z ok Hs. unfold PjGrammar.jr_string. rewrite Hs. reflexivity. Qed.

Lemma vk_jrs_fail : forall z Q okr, PjGrammar.scan z = Some Q ->
  snd (fst (PjGrammar.jr_string z (false :: okr))) = [PjGrammar.EFail (S Q)].
Proof. intros z Q okr Hs. unfold PjGrammar.jr_string. rewrite Hs. reflexivity. Qed.

Lemma vk_jrs_badesc : forall z Q okr, PjGrammar.scan z = Some Q -> PjGrammar.decode z = None ->
  snd (fst (PjGrammar.jr_string z (true :: okr))) = [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)].
Proof.
  intros z Q okr Hs Hd. unfold PjGrammar.jr_string. rewrite Hs. unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take.
  cbn beta iota. rewrite Hd. reflexivity.
Qed.

Lemma vk_jrs_str : forall z Q s r okr, PjGrammar.scan z = Some Q -> PjGrammar.decode z = Some (s, r) ->
  snd (fst (PjGrammar.jr_string z (true :: okr))) = [PjGrammar.EAlloc (S Q)].
Proof.
  intros z Q s r okr Hs Hd. unfold PjGrammar.jr_string. rewrite Hs. unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take.
  cbn beta iota. rewrite Hd. reflexivity.
Qed.

(* THE CALL'S ALL-GRANTED TRACE AT THE KEY'S OPENING QUOTE: the trace so far, then parse_string's granted trace, then
   the rest (VrdCallPos.vc_gt_split, vk_K_unfold, PRH_FnReader.prhReader_jbind_pre twice) *)
Lemma vk_gt_ps : forall E P, vrd_imodel E P ->
  ip_cont P = vrd_jtail (S (ie_d E)) true (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P)
                (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ->
  ie_text E <= ip_p P -> nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some 34 ->
  exists rest, prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) =
    ip_tr P ++ snd (fst (PjGrammar.jr_string (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)) [])) ++ rest.
Proof.
  intros E P HM Hc Hp Hn. rewrite (vc_gt_split E P HM), Hc.
  rewrite (vk_K_unfold (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) (ie_tb E) (ie_text E)
             (ip_p P) Hp Hn).
  match goal with |- context [snd (fst (PjGrammar.jbind ?m ?k []))] =>
    destruct (prhReader_jbind_pre _ _ m k []) as (t2 & Ht2); rewrite Ht2 end.
  match goal with |- context [snd (fst (PjGrammar.jbind ?m ?k []))] =>
    destruct (prhReader_jbind_pre _ _ m k []) as (t1 & Ht1); rewrite Ht1 end.
  exists (t1 ++ t2). rewrite <- !app_assoc. reflexivity.
Qed.

(* THE OUTCOME OF AN INJECTED READING AT parse_string: under any grant list the continuation's events at the opening
   quote begin with parse_string's (vk_K_unfold, VrdIElem.vrd_jbind_prefix twice, vrd_run_prefix), and parse_string
   makes ONE call, so under a list that grants its first call its events are its all-granted ones *)
Lemma vk_ps_prefix : forall d n cap1 acc f tb text p okt (sm : list Z -> Z * Z) (x : list Z)
    (os : list (option nat * option nat * option nat)) (i : nat),
  text <= p -> nth_error tb (Z.to_nat (p - text)) = Some 34 ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (vrd_jtail d true n cap1 acc f (rest_atR tb text p) okt)))) ->
  PRH_Base.prh_cons_from sm x os i
    (length (PresetReqAt.rd_hevs (snd (fst (vrd_jtail d true n cap1 acc f (rest_atR tb text p) okt))))) ->
  PRH_Base.prh_run_at sm x os i (prhPs_evs (rest_atR tb text (p + 1)) okt) /\
  PRH_Base.prh_cons_from sm x os i (length (prhPs_evs (rest_atR tb text (p + 1)) okt)).
Proof.
  intros d n cap1 acc f tb text p okt sm x os i Hp Hn HR HC.
  rewrite (vk_K_unfold d n cap1 acc f tb text p Hp Hn) in HR, HC.
  lazymatch type of HR with context [snd (fst (PjGrammar.jbind ?m ?k okt))] =>
    destruct (vrd_jbind_prefix _ _ m k okt) as (t2 & E2); rewrite E2 in HR, HC end.
  destruct (vrd_run_prefix sm x os i _ _ HR HC) as (HR1 & HC1).
  lazymatch type of HR1 with context [snd (fst (PjGrammar.jbind ?m ?k okt))] =>
    destruct (vrd_jbind_prefix _ _ m k okt) as (t1 & E1); rewrite E1 in HR1, HC1 end.
  destruct (vrd_run_prefix sm x os i _ _ HR1 HC1) as (HR2 & HC2).
  rewrite <- vk_ps_evs in HR2, HC2. exact (conj HR2 HC2).
Qed.

Lemma vk_ps_evs_grant : forall z o, prhPs_evs z (repeat true 1 ++ o) = prhPs_evs z [].
Proof. intros z o. reflexivity. Qed.

(* ---- the node across a call: its bytes (node and D blocks) kept, new blocks appended to D, the shadow rebuilt ---- *)
Lemma vk_rd_blk_in : forall D b z, In b D -> pj_holdsR b z -> rd_blk D z.
Proof. intros D b z Hb Hz. unfold rd_blk. apply Exists_exists. exists b. split; assumption. Qed.

Lemma vk_inode_keep : forall E P P2 Dn,
  vrd_inode E P [] ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
    (fun a => ie_v E <= a < ie_v E + 56 \/ rd_blk (ip_D P) a) ->
  ip_D P2 = ip_D P ++ Dn ->
  ip_n P2 = ip_n P -> ip_cap P2 = ip_cap P -> ip_kids P2 = ip_kids P -> ip_keys P2 = ip_keys P ->
  ip_acc P2 = ip_acc P ->
  (forall x k, prh_lin (ip_Lam P) x k -> prh_lin (ip_Lam P2) x k) ->
  range_addressable (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) SHADOW_OFF (ie_v E) 56 ->
  (0 < ip_cap P -> range_addressable (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) SHADOW_OFF
                     (ip_kids P) (56 * ip_cap P)) ->
  (ie_o E = true -> 0 < ip_cap P ->
     range_addressable (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) SHADOW_OFF (ip_keys P) (8 * ip_cap P)) ->
  vrd_inode E P2 Dn.
Proof.
  intros E P P2 Dn HND HK HD2 En Ec Ek Ey Ea Hlin2 Rv Rk Ry.
  pose proof HND as (Hhdr & Hnc & Hcap & Hc0 & Hlin & Hlen & (Di & HPerm & HTree) & Hrw & _ & _ & _ & Hkz).
  cbn [app] in HPerm.
  assert (HinD : forall b, In b (kids_blkR (ip_kids P) (ip_cap P) ++
                    keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) -> In b (ip_D P))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
  assert (Hkr : forall z, 0 < ip_cap P -> ip_kids P <= z < ip_kids P + 56 * ip_cap P -> rd_blk (ip_D P) z).
  { intros z Hc Hz. apply (vk_rd_blk_in _ (ip_kids P, 56 * ip_cap P)); [|unfold pj_holdsR; cbn [fst snd]; lia].
    apply HinD. apply in_or_app. left. unfold kids_blkR. destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
  assert (Hyr : forall z, ie_o E = true -> 0 < ip_cap P -> ip_keys P <= z < ip_keys P + 8 * ip_cap P ->
                  rd_blk (ip_D P) z).
  { intros z Ho Hc Hz. apply (vk_rd_blk_in _ (ip_keys P, 8 * ip_cap P)); [|unfold pj_holdsR; cbn [fst snd]; lia].
    apply HinD. apply in_or_app. right. apply in_or_app. left. unfold keys_blkR. rewrite Ho.
    destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
  assert (Hdr : forall z, rd_blk Di z -> rd_blk (ip_D P) z).
  { intros z Hz. unfold rd_blk in Hz. apply Exists_exists in Hz as (b & Hb & Hzb).
    apply (vk_rd_blk_in _ b); [|exact Hzb]. apply HinD. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  unfold vrd_inode. cbv zeta. rewrite En, Ec, Ek, Ey, Ea, HD2.
  split; [eapply pj_hdrR_keep; [exact Hhdr | eapply rd_keep_mono; [exact HK | intros; left; assumption]]|].
  split; [exact Hnc|]. split; [exact Hcap|]. split; [exact Hc0|].
  split; [intros Hc; destruct (Hlin Hc) as [H1 H2]; split; [apply Hlin2; exact H1 | intros Ho; apply Hlin2; exact (H2 Ho)]|].
  split; [exact Hlen|].
  split.
  { exists Di. split.
    - eapply perm_trans; [apply Permutation_app_comm|]. cbn [app]. apply Permutation_app_head. exact HPerm.
    - destruct (ie_o E) eqn:Ho.
      + eapply pj_memsR_keep; [exact HTree | intros x k _ H; apply Hlin2; exact H|].
        eapply rd_keep_mono; [exact HK|]. rewrite length_rev, Hlen. intros z [Hz | [Hz | Hz]]; right.
        * apply Hkr; lia.
        * apply Hyr; [reflexivity | lia | lia].
        * apply Hdr. exact Hz.
      + eapply pj_itemsR_keep; [exact HTree | intros x k _ H; apply Hlin2; exact H|].
        eapply rd_keep_mono; [exact HK|]. rewrite length_map, length_rev, Hlen. intros z [Hz | Hz]; right.
        * apply Hkr; lia.
        * apply Hdr. exact Hz. }
  split.
  { eapply rd_rw_keep; [exact Hrw|]. eapply rd_keep_mono; [exact HK|]. intros z Hz. right. apply Hkr; lia. }
  split; [exact Rv|]. split; [exact Rk|]. split; [exact Ry|]. exact Hkz.
Qed.


(* ---- 8. after a REFUSED parse_string (res = 0): the state at row 149 the refusal path leaves from. The ledger, the
   position transfer, the OUTCOME and the live requests are vrd_iexit_a's, in the kit reader text's form (most own,
   the whole call's granted trace prhPi_gtrace at the entry cursor): the refusal exit hands them on unchanged ---- *)
Definition vk_retR (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vrd_iframe E P /\ vrd_iregs B E P /\ vrd_inode E P [] /\ vrd_ijrn B ARx SK E P /\
  pj_in_okR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ie_q E) (ie_text E) (ie_len E) (ip_p P)
    (Z.of_nat (ie_d E) + 1) (ie_tb E) /\
  range_addressable (aview SEGS (w_H (ip_W P)) (ip_mem P)) SHADOW_OFF (ie_q E) 24 /\
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
    (ie_most E) (ie_own E) /\
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) /\
  blocks_bytes (ip_S P) <= blocks_bytes (ie_S E) + prh_held (ip_tr P) /\
  Ledger.lsum (ip_D P) = PjGrammar.held (ip_tr P) /\
  room_live_cf (ip_S P) /\
  (* THE POSITION TRANSFER (vrd_iexit_a's conjunct) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (ip_tr P)) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs (ip_tr P)))%nat H0 hist'
       (ip_S P)) /\
  (* THE OUTCOME (vrd_iexit_a's conjunct) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i
       (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
     PRH_Base.prh_cons_from sm x os i
       (length (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))) ->
     (ie_fail E < ie_cnt E \/
      ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))
        <= ie_fail E) ->
     ip_ran P = ie_ran E /\
     fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) []) =
       fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
              (ip_ok P)) /\
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))))%nat
       H0 hist' (ip_S P)) /\
  (* the live requests (vrd_iexit_a's conjunct) *)
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf (ip_S P)))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (ie_S E))) (PresetReqAt.rd_hevs (ip_tr P))) /\
  (* the hull use (vrd_iexit_a's conjunct) *)
  PresetHullBudget.hull_used (ie_S E) (ip_S P)
    (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) /\
  (* the outcome of an injected reading (vrd_iexit_a's conjunct) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E)
       (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E))))))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_items ReaderRes.jr_strtod
       (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E)))))))) ->
     ie_cnt E <= ie_fail E <
       ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
     PRH_Base.prh_granted (ip_ok P) (ie_cnt E) (ie_fail E) (PjGrammar.calls (ip_tr P))) /\
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - S (ie_d E))%nat) (ip_acc P) /\
  (exists okr, PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P)
                 = (None, ip_tr P, okr)) /\
  ip_n P < ip_cap P /\ ie_o E = true /\ getr (ip_regs P) 10 = w64 0 /\
  (* The kit's cut: the members' caps and the completed slots' order list against af (carried across the slot store
     REFUSE's C2 makes, vk_k1_slot), and the model's free list at the refused name, the None arm of jfl's body after the
     grow: af then the arrays (the exit's free order, VrdIFd.vrd_inode_fo_core) *)
  vrd_incaps E P /\
  exists af, vrd_iforder E P [] af /\
    prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
      af ++ PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P)).

Lemma vk_fregs_refl : forall f, fregs_kept_x f f.
Proof. intros f r _. reflexivity. Qed.

Lemma vk_after_refuse : forall CTX CTX0 CW E Pc P2 STKc k1 WS1 t ob,
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E Pc -> vrd_iregs B E Pc -> vrd_inode E Pc [] -> vrd_icur B E Pc -> vrd_ijrn B ARx SK E Pc ->
  vrd_imodel E Pc -> ip_n Pc < ip_cap Pc -> ie_o E = true ->
  (* vrd_call_Wb_P's clauses for the call at Pc (the kit's cut: parse_string posts at the budget wbudget CW 0, so its journal
     is at its budget WS1 and the composed one at ie_CW E ++ WS1) *)
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc (spZ (ie_regs E) + ie_e E) [(ie_q E, ie_q E + 8)]
    (ip_ly Pc) (ip_S Pc) (ip_Hp Pc) (ip_W Pc) (ip_mem Pc) (ip_md Pc) []
    (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2) (ip_md P2) k1 WS1 ->
  (forall a, spZ (ie_regs E) - 144 <= a < spZ (ie_regs E) + ie_e E -> ~ inFP [(ie_q E, ie_q E + 8)] a ->
     aview SEGS (w_H (ip_W P2)) (ip_mem P2) a = aview SEGS (w_H (ip_W Pc)) (ip_mem Pc) a) ->
  aregs_preserved (ip_regs Pc) (ip_regs P2) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2) (ip_md P2) (ip_k P2) (ie_CW E ++ WS1) ->
  YCbqGwild.wbudget CW 0 WS1 ->
  ip_fx P2 = ip_fx Pc ->
  (* the callee's post at P2: no new block, the ledger by one event shape (or none) *)
  getr (ip_regs P2) 10 = w64 0 ->
  ablocks B (ip_ly P2) (ip_S P2) = ablocks B (ip_ly Pc) (ip_S Pc) ->
  ip_n P2 = ip_n Pc -> ip_cap P2 = ip_cap Pc -> ip_kids P2 = ip_kids Pc -> ip_keys P2 = ip_keys Pc ->
  ip_acc P2 = ip_acc Pc -> ip_p P2 = ip_p Pc ->
  ip_D P2 = ip_D Pc -> ip_Lam P2 = ip_Lam Pc -> ip_tr P2 = ip_tr Pc ++ t -> ip_ok P2 = ip_ok Pc ++ ob ->
  rd_ledger_move (ip_Lam Pc) (ip_peak Pc) (ip_cnt Pc) (ip_fail Pc) (ip_ran Pc) (ie_most E) ob (snd (fst (ip_cont Pc [])))
    t [] (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2) ->
  Permutation (lszR (ip_tr Pc ++ t)) (lszR (ip_tr Pc) ++ lszR t) -> PjGrammar.held t = 0 ->
  prh_ledger B (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2)
    (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2) (ie_most E) (ie_own E) ->
  pj_in_okR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ie_q E) (ie_text E) (ie_len E) (ip_p P2)
    (Z.of_nat (ie_d E) + 1) (ie_tb E) ->
  room_live_cf (ip_S P2) ->
  (* the callee's position transfer and live requests over its events, and the exit's OUTCOME at P2: derived here
     when the arm's outcomes are granted (no closing quote, a bad escape: vc_outc_granted), else given by the arm
     (the chosen failure: vc_outc_chosen; the allocator's refusal: vc_outc_refused) *)
  vc_xfer (ip_S Pc) (ip_S P2) t -> vc_live (ip_S Pc) (ip_S P2) t ->
  (* the exit's hull use over the call's all-granted events, composed at the call (VrdIStep.vi_hull_exit: the use
     so far, then the callee's over its all-granted list) *)
  PresetHullBudget.hull_used (ie_S E) (ip_S P2)
    (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
  ob = repeat true (PjGrammar.calls t) \/ vc_outc E P2 ->
  (* the callee's part of the exit's outcome of an injected reading (VrdIElem.vrd_inj_exit's callee premise): at a
     model run whose next events are the continuation's under the model's list from the call, with the chosen failure
     at or after the call's counter, the callee's oks ob refuse only the chosen call *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S Pc) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (ip_cont Pc
       (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr Pc))))))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (ip_cont Pc
       (PresetReqAt.okk (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr Pc)))))))) ->
     ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr Pc)) <= ie_fail E <
       ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
     PRH_Base.prh_granted ob (ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr Pc))) (ie_fail E) (PjGrammar.calls t)) ->
  blocks_bytes (ip_S P2) <= blocks_bytes (ip_S Pc) + prh_held t ->
  hpeakR (ip_tr Pc ++ t) <= 224 * Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ie_p E))) +
                           512 * Z.of_nat (PjGrammar.MAXD - ie_d E) ->
  0 <= ie_cnt E -> ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr Pc)) < 2 ^ 64 ->
  (forall okr, ip_cont Pc (ob ++ okr) = (None, t, okr)) ->
  (* The kit's cut: the batch kit's layer at the call (vk_k1h), and the model's name refusing on the same outcomes *)
  vk_k1h E Pc ->
  (forall okr, PjGrammar.jr_name true (rest_atR (ie_tb E) (ie_text E) (ip_p Pc)) (ob ++ okr) = (None, t, okr)) ->
  vk_retR E P2.
Proof.
  intros CTX CTX0 CW E Pc P2 STKc k1 WS1 t ob HEN HFR HRG HND HCU HJN HMD Hnc Ho HJc HWIN HPR HJ2 HWB Efx
    R10 Hab En Ec Ek Ey Ea Ep ED EL Etr Eok HLM1 Hlsz Hheld HLED2 Hin2 HRL2 HXF2 HLV2 HHX2 HOC2 HINJc HBB Hpk Hc0 Hnw
    Hcont HK1 HNm.
  pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & _).
  pose proof HCU as (Hin & Hraq & Hsrc & Hhome & Hled & Hfrs & Hcnt).
  pose proof HJN as (_ & _ & _ & _ & _ & HBM & _).
  pose proof (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  assert (Bv56 : ie_v E + 56 <= alloc_ceiling) by (eapply vrd_node_low; eassumption).
  pose proof asan_consts as (C1 & _).
  (* the position facts at P2 *)
  destruct (vrd_pos_after_call B ARx SK LAWS H_pst_ro CTX CTX0 CW E Pc P2 STKc [(ie_q E, ie_q E + 8)] k1 WS1 [] t
              Hfr144 Hs0c HEN HFR HRG HJN) as (F2 & G2 & J2 & K2).
  { intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha. left. lia. }
  { exact HJc. } { exact HWIN. } { exact HPR. } { exact HJ2. } { exact HWB. }
  { rewrite Efx. pose proof HJN as (_ & _ & Hfz & _). exact Hfz. }
  { rewrite Efx. apply vk_fregs_refl. }
  { intros a k []. }
  { rewrite Hab. cbn [prhReader_ab map app]. apply Permutation_refl. }
  { pose proof HJc as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. cbn [app]. apply Permutation_refl. }
  { rewrite ED, app_nil_r. reflexivity. }
  { exact Etr. }
  { exact Hpk. }
  (* the ledger move E -> P2 *)
  assert (HLM2 : rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E)
                   (ip_ok P2) (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P2)
                   (ip_D P2) (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2)).
  { rewrite (vc_gt_split E Pc HMD), Eok, Etr, ED, M1, <- (app_nil_r (ip_D Pc)). rewrite M1 in M3.
    apply (vl_ledger_move_app (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E)
             (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr Pc) (ip_D Pc)
             (ip_Lam Pc) (ip_peak Pc) (ip_cnt Pc) (ip_fail Pc) (ip_ran Pc) ob (snd (fst (ip_cont Pc []))) t []
             (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2)).
    all: first [lia | exact M3 | exact HLM1 | exact M8 | exact Hlsz]. }
  pose proof HLM2 as (_ & _ & _ & HPL2 & _).
  pose proof J2 as (HJ2' & _ & _ & _ & _ & HBM2 & _).
  pose proof HJ2' as (HAR2 & _).
  pose proof HJN as (HJ & _).
  pose proof HJ as (HARc & _).
  (* the bytes the node reads are kept, and are off the callee's footprint *)
  assert (K2' : rd_keep SEGS (mrestrict (w_H (ip_W Pc)) (ip_mem Pc)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
                  (fun a => ie_v E <= a < ie_v E + 56 \/ rd_blk (ip_D Pc) a)).
  { eapply rd_keep_mono; [exact K2|]. intros a Ha. split; [|exact Ha].
    intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    destruct Ha as [Ha | Ha]; [lia|].
    unfold rd_blk in Ha. apply Exists_exists in Ha as (b & Hb & Hab').
    pose proof (vk_D_low B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ b a HARc HBM Hb Hab'). lia. }
  assert (HinL2 : forall b, In b (ip_D Pc) -> In b (ip_Lam P2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPL2)). apply in_or_app. left. rewrite ED. exact Hb. }
  pose proof HND as (_ & _ & _ & _ & _ & _ & (Di & HPerm & _) & _).
  cbn [app] in HPerm.
  assert (HDin : forall b, In b (kids_blkR (ip_kids Pc) (ip_cap Pc) ++
                   keys_blkR (if ie_o E then 6 else 5) (ip_keys Pc) (ip_cap Pc) ++ Di) -> In b (ip_D Pc))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
  assert (HND2 : vrd_inode E P2 []).
  { apply (vk_inode_keep E Pc P2 [] HND K2'); try assumption.
    - rewrite ED, app_nil_r. reflexivity.
    - rewrite EL. intros x k H. exact H.
    - eapply vrd_node_ra_after_call; try eassumption; rewrite ED; exact HPL2.
    - intros Hc.
      assert (Hkin : In (ip_kids Pc, 56 * ip_cap Pc) (ip_Lam P2)).
      { apply HinL2. apply HDin. apply in_or_app. left. unfold kids_blkR.
        destruct (Z.eqb_spec (ip_cap Pc) 0); [lia | left; reflexivity]. }
      eapply (fun H : _ /\ _ => proj1 H). eapply vrd_lam_shadow; eassumption.
    - intros Hoo Hc.
      assert (Hyin : In (ip_keys Pc, 8 * ip_cap Pc) (ip_Lam P2)).
      { apply HinL2. apply HDin. apply in_or_app. right. apply in_or_app. left. unfold keys_blkR.
        rewrite Hoo. destruct (Z.eqb_spec (ip_cap Pc) 0); [lia | left; reflexivity]. }
      eapply (fun H : _ /\ _ => proj1 H). eapply vrd_lam_shadow; eassumption. }
  assert (Hraq2 : range_addressable (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) SHADOW_OFF (ie_q E) 24).
  { eapply (fun H : _ /\ _ /\ _ => proj2 (proj2 H)). eapply vrd_icur_after_call; eassumption. }
  assert (HXF2' : vc_xfer (ie_S E) (ip_S P2) (ip_tr P2)) by (rewrite Etr; exact (vc_xfer_app _ _ _ _ _ M9 HXF2)).
  assert (HANS : exists okr, PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E)
                   (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P2) = (None, ip_tr P2, okr)).
  { exists []. rewrite Eok, Etr. rewrite <- (app_nil_r ob) at 1.
    rewrite (M2 (ob ++ [])), (Hcont []). cbn [fst snd]. reflexivity. }
  assert (HOC : vc_outc E P2).
  { destruct HOC2 as [Hob | HOC2]; [|exact HOC2]. destruct HANS as (okr & Hans).
    apply (vc_outc_granted E P2 None okr); [| exact Hans | exact HLM2 | exact HXF2'].
    rewrite Eok, Etr, M1, Hob, vle_calls_app, repeat_app. reflexivity. }
  unfold vk_retR.
  split; [exact F2|]. split; [exact G2|]. split; [exact HND2|]. split; [exact J2|]. split; [exact Hin2|].
  split; [exact Hraq2|]. split; [exact HLED2|]. split; [exact HLM2|].
  split; [rewrite Etr; exact (vle_blocks_step _ _ _ _ _ M6 HBB)|].
  split; [rewrite ED, Etr, vle_held_app, Hheld, Z.add_0_r; exact M8|].
  split; [exact HRL2|].
  split; [exact HXF2'|]. split; [exact HOC|].
  split; [rewrite Etr; exact (vc_live_app _ _ _ _ _ M10 HLV2)|]. split; [exact HHX2|].
  (* the outcome of an injected reading: the position's oks, then the callee's (VrdIElem.vrd_inj_exit) *)
  split.
  { intros sm x os i H0 hist Hq1 Hq2 Hq3 Hq4. rewrite Eok, Etr.
    eapply vrd_inj_exit; [exact HMD | exact HINJc | exact Hq1 | exact Hq2 | exact Hq3 | exact Hq4]. }
  split; [rewrite Ea; exact M7|].
  split; [exact HANS|].
  split; [rewrite En, Ec; exact Hnc|]. split; [exact Ho|]. split; [exact R10|].
  (* The kit's cut: the order list at P2 (the call kept every block of Pc's, VrdIFd.vrd_k1_keep), and the model's free list
     at the refused name (vk_jfb_none) *)
  destruct HK1 as (_ & Hinc & af & HFO & HFL).
  destruct (vrd_k1_keep E Pc P2 [] af Ek Ey En Ec Ea ED
              ltac:(intros xx kk Hx; exact (HinL2 _ Hx))
              ltac:(eapply rd_keep_mono; [exact K2'|]; intros a Ha; right; exact Ha)
              HND Hinc HFO) as (Hinc2 & HFO2).
  split; [exact Hinc2|].
  exists af. split; [exact HFO2|].
  pose proof (HNm []) as HN0. rewrite app_nil_r in HN0.
  rewrite Eok, Ec, (HFL ob), Ho. exact (vk_jfb_none _ _ _ _ _ _ _ _ _ _ HN0).
Qed.


(* ---- 9. after a parse_string that returned the KEY (res = the new block of Q + 1 bytes) ---- *)
Lemma vk_fresh_block : forall ly S Hp W mem md lyc Sc b n,
  ARx ly S Hp W mem md -> ablocks B ly S = ablocks B lyc Sc ++ [(b, n)] -> 0 < req_size n ->
  ~ In (b, n) (ablocks B lyc Sc).
Proof.
  intros ly S Hp W mem md lyc Sc b n HAR Heq Hr Hin.
  destruct (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HAR) as [Hq _]. rewrite Heq in Hq.
  apply in_split in Hin as (l1 & l2 & Hl). rewrite Hl in Hq.
  rewrite !map_app in Hq. cbn [map app] in Hq. rewrite <- !app_assoc in Hq. cbn [app] in Hq.
  assert (Hd : zdisjoint (b, req_size n) (b, req_size n)).
  { eapply (pairwise_In2 zdisjoint); [exact Hq|]. reflexivity. }
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma vk_K_str0 : forall d n cap1 acc f tb text p Q s r,
  text <= p -> nth_error tb (Z.to_nat (p - text)) = Some 34 ->
  PjGrammar.scan (rest_atR tb text (p + 1)) = Some Q -> PjGrammar.decode (rest_atR tb text (p + 1)) = Some (s, r) ->
  vrd_jtail d true n cap1 acc f (rest_atR tb text p) [] =
    vrd_jtail d true n cap1 acc f (rest_atR tb text p) [true].
Proof.
  intros d n cap1 acc f tb text p Q s r Hp Hnth Hs Hd.
  rewrite (vk_K_unfold d n cap1 acc f tb text p Hp Hnth). unfold PjGrammar.jbind at 1 2 3 4.
  unfold PjGrammar.jr_string. rewrite Hs. unfold PjGrammar.jbind at 1 2, PjGrammar.jalloc, PjGrammar.take.
  reflexivity.
Qed.

Lemma vk_gtrace_str : forall z Q s r, PjGrammar.scan z = Some Q -> PjGrammar.decode z = Some (s, r) ->
  prhPs_gtrace z = [PjGrammar.EAlloc (S Q)].
Proof.
  intros z Q s r Hs Hd. unfold prhPs_gtrace, PjGrammar.jr_string. rewrite Hs.
  unfold PjGrammar.jbind, PjGrammar.jalloc, PjGrammar.take. cbn beta iota. rewrite Hd. reflexivity.
Qed.

Lemma vk_rest_decode : forall tb text p Q s r, text <= p ->
  PjGrammar.scan (rest_atR tb text (p + 1)) = Some Q -> PjGrammar.decode (rest_atR tb text (p + 1)) = Some (s, r) ->
  r = rest_atR tb text (p + Z.of_nat Q + 2) /\ (length s <= Q)%nat.
Proof.
  intros tb text p Q s r Hp Hs Hd. destruct (PjGrammar.G1_4 _ _ _ Hd) as (q & Hq & Hr & Hl & _).
  rewrite Hs in Hq. injection Hq as <-. split; [|exact Hl].
  rewrite Hr. unfold rest_atR. rewrite skipn_skipn. f_equal. lia.
Qed.


(* the state at row 149 after the KEY: the position owns the key's block (x, k) beside the node's; the model is past
   the closing quote (vk_kont), the cursor is past it. The kit's cut appends the batch kit's layer after the key (VrdIElem.vrd_islot_a's,
   at the colon test's model): cap = ncap (S n), the members' caps, the order list with the key's block as its extra
   block, and the model's free list after the key (vk_jfk) with the key's request k + cf_head *)
Definition vk_retK (E : vrd_ient) (P : vrd_ipos) (x k : Z) (nm : list Z) : Prop :=
  vrd_iframe E P /\ vrd_iregs B E P /\ vrd_inode E P [(x, k)] /\ vrd_icur B E P /\ vrd_ijrn B ARx SK E P /\
  vrd_imodel E P /\ ip_n P < ip_cap P /\ ie_o E = true /\ getr (ip_regs P) 10 = w64 x /\
  pj_cstrR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) x k nm /\
  prhReader_vis (ip_W P) (ip_mem P) x k /\ 4096 + cf_head <= x /\ x mod 16 = 0 /\
  exists z, ip_cont P = vk_kont (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) z nm
                         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
            PjGrammar.sblock z = Z.to_nat k /\
  ip_cap P = Z.of_nat (PresetReqAt.ncap (S (Z.to_nat (ip_n P)))) /\ vrd_incaps E P /\
  exists af, vrd_iforder E P [(x, k)] af /\
    (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
       vk_jfk (ip_f P) (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af [k + cf_head]
         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr).

Lemma vk_after_str : forall CTX CTX0 CW E Pc P2 STKc k1 WS1 Q s x,
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E Pc -> vrd_iregs B E Pc -> vrd_inode E Pc [] -> vrd_icur B E Pc -> vrd_ijrn B ARx SK E Pc ->
  vrd_imodel E Pc -> ip_n Pc < ip_cap Pc -> ie_o E = true ->
  ip_cont Pc = vrd_jtail (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n Pc)) (Z.to_nat (ip_cap Pc)) (ip_acc Pc) (ip_f Pc)
                 (rest_atR (ie_tb E) (ie_text E) (ip_p Pc)) ->
  ip_p Pc < ie_text E + ie_len E -> nth_error (ie_tb E) (Z.to_nat (ip_p Pc - ie_text E)) = Some 34 ->
  PjGrammar.scan (rest_atR (ie_tb E) (ie_text E) (ip_p Pc + 1)) = Some Q ->
  PjGrammar.decode (rest_atR (ie_tb E) (ie_text E) (ip_p Pc + 1)) =
    Some (s, rest_atR (ie_tb E) (ie_text E) (ip_p Pc + Z.of_nat Q + 2)) ->
  (* vrd_call_Wb_P's clauses for the call at Pc, at the callee's budget WS1 (the kit's cut) *)
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc (spZ (ie_regs E) + ie_e E) [(ie_q E, ie_q E + 8)]
    (ip_ly Pc) (ip_S Pc) (ip_Hp Pc) (ip_W Pc) (ip_mem Pc) (ip_md Pc) []
    (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2) (ip_md P2) k1 WS1 ->
  (forall a, spZ (ie_regs E) - 144 <= a < spZ (ie_regs E) + ie_e E -> ~ inFP [(ie_q E, ie_q E + 8)] a ->
     aview SEGS (w_H (ip_W P2)) (ip_mem P2) a = aview SEGS (w_H (ip_W Pc)) (ip_mem Pc) a) ->
  aregs_preserved (ip_regs Pc) (ip_regs P2) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2) (ip_md P2) (ip_k P2) (ie_CW E ++ WS1) ->
  YCbqGwild.wbudget CW 0 WS1 ->
  ip_fx P2 = ip_fx Pc ->
  (* the callee's KEY arm, at P2 *)
  ip_cnt Pc <> ip_fail Pc ->
  4096 + cf_head <= x -> x mod 16 = 0 ->
  ablocks B (ip_ly P2) (ip_S P2) = ablocks B (ip_ly Pc) (ip_S Pc) ++
    [(x - cf_head, Z.of_nat Q + 1 + cf_head)] ->
  prhReader_vis (ip_W P2) (ip_mem P2) (x) (Z.of_nat Q + 1) ->
  pj_cbytesR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (x) s ->
  prh_ledger B (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2)
    (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2) (ie_most E) (ie_own E) ->
  pj_in_okR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ie_q E) (ie_text E) (ie_len E) (ip_p P2)
    (Z.of_nat (ie_d E) + 1) (ie_tb E) ->
  room_live_cf (ip_S P2) ->
  (* the callee's position transfer, live requests and hull use over its one event *)
  vc_xfer (ip_S Pc) (ip_S P2) [PjGrammar.EAlloc (S Q)] -> vc_live (ip_S Pc) (ip_S P2) [PjGrammar.EAlloc (S Q)] ->
  PresetHullBudget.hull_used (ip_S Pc) (ip_S P2) (PresetReqAt.rd_hevs [PjGrammar.EAlloc (S Q)]) ->
  blocks_bytes (ip_S P2) <= blocks_bytes (ip_S Pc) + prh_held [PjGrammar.EAlloc (S Q)] ->
  (* P2's fields *)
  getr (ip_regs P2) 10 = w64 (x) ->
  ip_n P2 = ip_n Pc -> ip_cap P2 = ip_cap Pc -> ip_kids P2 = ip_kids Pc -> ip_keys P2 = ip_keys Pc ->
  ip_acc P2 = ip_acc Pc -> ip_f P2 = ip_f Pc -> ip_p P2 = ip_p Pc + Z.of_nat Q + 2 ->
  ip_D P2 = ip_D Pc ++ [(x, Z.of_nat (S Q))] ->
  ip_Lam P2 = (x, Z.of_nat (S Q)) :: ip_Lam Pc ->
  ip_peak P2 = Z.max (ip_peak Pc) (Ledger.lsum (ip_Lam Pc) + Z.of_nat (S Q)) ->
  ip_cnt P2 = ip_cnt Pc + 1 -> ip_fail P2 = ip_fail Pc -> ip_ran P2 = ip_ran Pc ->
  ip_tr P2 = ip_tr Pc ++ [PjGrammar.EAlloc (S Q)] -> ip_ok P2 = ip_ok Pc ++ [true] ->
  ip_cont P2 = vk_kont (S (ie_d E)) (Z.to_nat (ip_n Pc)) (Z.to_nat (ip_cap Pc)) (ip_acc Pc) (ip_f Pc)
                 (rest_atR (ie_tb E) (ie_text E) (ip_p Pc + 1)) s (rest_atR (ie_tb E) (ie_text E) (ip_p P2)) ->
  (* The kit's cut: the batch kit's layer at the call *)
  vk_k1h E Pc ->
  vk_retK E P2 (x) (Z.of_nat (S Q)) s.
Proof.
  intros CTX CTX0 CW E Pc P2 STKc k1 WS1 Q s x HEN HFR HRG HND HCU HJN HMD Hnc Ho Hcont Hlt Hnth Hsc Hdec HJc HWIN
    HPR HJ2 HWB Efx Hcf Hx4 Hx16 Hab Hvis Hcb HLED2 Hin2 HRL2 HXF2 HLV2 HHU2 HBB R10 En Ec Ek Ey Ea Ef Ep ED EL Epk Ecnt
    Efl Eran Etr Eok Ecn HK1.
  pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11).
  pose proof HCU as (Hin & Hraq & Hsrc & Hhome & Hled & Hfrs & Hcnt).
  pose proof HJN as (HJ & _ & _ & _ & _ & HBM & _).
  pose proof HJ as (HARc & _).
  pose proof HJ2 as (HAR2 & _).
  pose proof (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  assert (Bv56 : ie_v E + 56 <= alloc_ceiling) by (eapply vrd_node_low; eassumption).
  pose proof asan_consts as (C1 & _).
  pose proof Hin as (_ & _ & _ & _ & _ & Ht0 & _ & Hpp & Hlen & _).
  pose proof Hin2 as (_ & _ & _ & _ & _ & _ & _ & Hpp2 & _).
  assert (Hp0 : ie_text E <= ip_p Pc) by lia.
  pose proof HEN as (_ & _ & _ & _ & HRD & Hplt & Hpnth & _).
  pose proof HRD as (_ & _ & _ & _ & HinE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _ & HCB0).
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED0) as (_ & _ & Hc0 & _).
  pose proof HinE as (_ & _ & _ & _ & _ & Ht0E & _ & HppE & _).
  rewrite Ho in Hpnth.
  (* the granted trace of the loop from the entry, and its bounds *)
  set (x0 := rest_atR (ie_tb E) (ie_text E) (ie_p E)) in *.
  assert (Hx0 : x0 = 123 :: rest_atR (ie_tb E) (ie_text E) (ie_p E + 1))
    by (unfold x0; apply vk_rest_cons; [lia | exact Hpnth]).
  pose proof (M2 []) as HT. rewrite app_nil_r in HT.
  rewrite Hcont, Ho in HT.
  destruct (vk_gt_head (S (ie_d E)) (Z.to_nat (ip_n Pc)) (Z.to_nat (ip_cap Pc)) (ip_acc Pc) (ip_f Pc) (ie_tb E)
              (ie_text E) (ip_p Pc) Q Hp0 Hnth Hsc) as (t' & Ht').
  rewrite Ht' in HT.
  assert (HTcalls : (PjGrammar.calls (ip_tr Pc ++ PjGrammar.EAlloc (S Q) :: t') <= 2 * length x0)%nat).
  { pose proof (PjGrammar.G7_4_items prh_jr_strtod (ie_d E) true 123 (rest_atR (ie_tb E) (ie_text E) (ie_p E + 1))
                  (ip_ok Pc)) as G. rewrite <- Hx0, HT in G. exact G. }
  assert (HTpre : forall pp rr, ip_tr Pc ++ PjGrammar.EAlloc (S Q) :: t' = pp ++ rr ->
                    PjGrammar.held pp <= 224 * Z.of_nat (length x0) + 512 * Z.of_nat (PjGrammar.MAXD - ie_d E)).
  { intros pp rr Hpr. pose proof (PjGrammar.G10_2_items prh_jr_strtod (ie_d E) true 123
      (rest_atR (ie_tb E) (ie_text E) (ie_p E + 1)) (ip_ok Pc) pp rr) as G. rewrite <- Hx0, HT in G. exact (G Hpr). }
  assert (Hpk : hpeakR (ip_tr Pc ++ [PjGrammar.EAlloc (S Q)]) <=
                224 * Z.of_nat (length x0) + 512 * Z.of_nat (PjGrammar.MAXD - ie_d E)).
  { apply vl_hpeak_bound; [lia|]. intros pp rr Hpr. apply (HTpre pp (rr ++ t')).
    rewrite app_assoc, <- Hpr, <- app_assoc. reflexivity. }
  assert (Hnw : ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr Pc)) < 2 ^ 64).
  { rewrite vle_calls_app in HTcalls. unfold x0 in *. lia. }
  pose proof M3 as (_ & HcntM & _).
  assert (Hcp0 : 0 <= ip_cnt Pc) by (rewrite HcntM; apply Z.mod_pos_bound; lia).
  (* the ledger move E -> P2 *)
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ Hled) as ((Hls0c & Hpk0c) & _).
  assert (HLM2 : rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E)
                   (ip_ok P2) (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P2)
                   (ip_D P2) (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2)).
  { rewrite (vc_gt_split E Pc HMD), Eok, Etr, ED, M1, EL, Epk, Ecnt, Efl, Eran. rewrite M1 in M3.
    apply (vl_ledger_move_app (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E)
             (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr Pc) (ip_D Pc)
             (ip_Lam Pc) (ip_peak Pc) (ip_cnt Pc) (ip_fail Pc) (ip_ran Pc) [true] (snd (fst (ip_cont Pc [])))
             [PjGrammar.EAlloc (S Q)] [(x, Z.of_nat (S Q))] ((x, Z.of_nat (S Q)) :: ip_Lam Pc)
             (Z.max (ip_peak Pc) (Ledger.lsum (ip_Lam Pc) + Z.of_nat (S Q))) (ip_cnt Pc + 1) (ip_fail Pc) (ip_ran Pc)).
    all: first [lia | exact M3 | exact M8 | apply vle_lsz_alloc | (apply vle_alloc; lia)]. }
  pose proof HLM2 as (_ & _ & _ & HPL2 & _).
  (* the position facts at P2 *)
  assert (Hfresh : forall a k, In (a, k) [(x, Z.of_nat (S Q))] ->
                     ~ In (a - cf_head, k + cf_head) (ablocks B (ip_ly Pc) (ip_S Pc))).
  { intros a k [Heq | []]. injection Heq as <- <-.
    apply (vk_fresh_block _ _ _ _ _ _ _ _ _ _ HAR2); [rewrite Hab; f_equal; f_equal; f_equal; lia|].
    pose proof (@cf_head_nonneg cp). destruct (req_size_pos (Z.of_nat (S Q) + cf_head)) as [Hr _]; lia. }
  destruct (vrd_pos_after_call B ARx SK LAWS H_pst_ro CTX CTX0 CW E Pc P2 STKc [(ie_q E, ie_q E + 8)] k1 WS1
              [(x, Z.of_nat (S Q))] [PjGrammar.EAlloc (S Q)] Hfr144 Hs0c HEN HFR HRG HJN) as (F2 & G2 & J2 & K2).
  { intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha. left. lia. }
  { exact HJc. } { exact HWIN. } { exact HPR. } { exact HJ2. } { exact HWB. }
  { rewrite Efx. pose proof HJN as (_ & _ & Hfz & _). exact Hfz. }
  { rewrite Efx. apply vk_fregs_refl. }
  { exact Hfresh. }
  { rewrite Hab. cbn [prhReader_ab map fst snd]. replace (Z.of_nat Q + 1 + cf_head) with (Z.of_nat (S Q) + cf_head) by lia.
    apply Permutation_app_comm. }
  { pose proof HJc as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. cbn [app]. apply Permutation_refl. }
  { exact ED. }
  { exact Etr. }
  { exact Hpk. }
  pose proof J2 as (HJ2' & _ & _ & _ & _ & HBM2 & _).
  assert (K2' : rd_keep SEGS (mrestrict (w_H (ip_W Pc)) (ip_mem Pc)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
                  (fun a => ie_v E <= a < ie_v E + 56 \/ rd_blk (ip_D Pc) a)).
  { eapply rd_keep_mono; [exact K2|]. intros a Ha. split; [|exact Ha].
    intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    destruct Ha as [Ha | Ha]; [lia|].
    unfold rd_blk in Ha. apply Exists_exists in Ha as (b & Hb & Hab').
    pose proof (vk_D_low B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ b a HARc HBM Hb Hab'). lia. }
  assert (HinL2 : forall b, In b (ip_D Pc) -> In b (ip_Lam P2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPL2)). apply in_or_app. left. rewrite ED.
    apply in_or_app. left. exact Hb. }
  pose proof HND as (_ & _ & _ & _ & _ & _ & (Di & HPerm & _) & _).
  cbn [app] in HPerm.
  assert (HDin : forall b, In b (kids_blkR (ip_kids Pc) (ip_cap Pc) ++
                   keys_blkR (if ie_o E then 6 else 5) (ip_keys Pc) (ip_cap Pc) ++ Di) -> In b (ip_D Pc))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
  assert (HND2 : vrd_inode E P2 [(x, Z.of_nat (S Q))]).
  { apply (vk_inode_keep E Pc P2 [(x, Z.of_nat (S Q))] HND K2'); try assumption.
    - rewrite EL. intros a k H. right. exact H.
    - eapply vrd_node_ra_after_call; try eassumption; rewrite ED; exact HPL2.
    - intros Hc.
      assert (Hkin : In (ip_kids Pc, 56 * ip_cap Pc) (ip_Lam P2)).
      { apply HinL2. apply HDin. apply in_or_app. left. unfold kids_blkR.
        destruct (Z.eqb_spec (ip_cap Pc) 0); [lia | left; reflexivity]. }
      eapply (fun H : _ /\ _ => proj1 H). eapply vrd_lam_shadow; eassumption.
    - intros Hoo Hc.
      assert (Hyin : In (ip_keys Pc, 8 * ip_cap Pc) (ip_Lam P2)).
      { apply HinL2. apply HDin. apply in_or_app. right. apply in_or_app. left. unfold keys_blkR.
        rewrite Hoo. destruct (Z.eqb_spec (ip_cap Pc) 0); [lia | left; reflexivity]. }
      eapply (fun H : _ /\ _ => proj1 H). eapply vrd_lam_shadow; eassumption. }
  assert (Hica : src_rd (ip_W P2) (ip_mem P2) (ie_text E) (ie_tb E) /\
                 prhReader_home B (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_Lam P2) (ie_text E) (ie_len E) /\
                 range_addressable (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) SHADOW_OFF (ie_q E) 24)
    by (eapply vrd_icur_after_call; eassumption).
  destruct Hica as (Hsrc2 & Hhome2 & Hraq2).
  (* the rest of the text after the string *)
  assert (Hlr : (length (rest_atR (ie_tb E) (ie_text E) (ip_p P2)) + Q + 2 <=
                 length (rest_atR (ie_tb E) (ie_text E) (ip_p Pc)))%nat).
  { unfold rest_atR. rewrite !length_skipn. rewrite Ep in *. lia. }
  destruct (vk_rest_decode (ie_tb E) (ie_text E) (ip_p Pc) Q s _ Hp0 Hsc Hdec) as (_ & Hls).
  unfold x0 in *. clear x0.
  unfold vk_retK.
  split; [exact F2|]. split; [exact G2|]. split; [exact HND2|].
  split.
  { unfold vrd_icur. cbv zeta.
    split; [exact Hin2|]. split; [exact Hraq2|]. split; [exact Hsrc2|]. split; [exact Hhome2|].
    split; [exact HLED2|].
    split; [pose proof HJc as (_ & _ & _ & _ & _ & Hfr & _); rewrite Hfr; cbn [app]; exact Hfrs|].
    rewrite Ecnt. lia. }
  split; [exact J2|].
  split.
  { unfold vrd_imodel.
    split; [rewrite Eok, Etr, M1, vle_calls_app, repeat_app; cbn [PjGrammar.calls PjGrammar.is_call]; reflexivity|].
    split.
    { intros okr. rewrite Eok, Etr, Ecn, <- app_assoc. cbn [app].
      rewrite (M2 (true :: okr)), Hcont, Ho.
      rewrite (vk_K_str (S (ie_d E)) (Z.to_nat (ip_n Pc)) (Z.to_nat (ip_cap Pc)) (ip_acc Pc) (ip_f Pc) (ie_tb E)
                 (ie_text E) (ip_p Pc) Hp0 Hnth Q s _ Hsc Hdec okr).
      cbn [fst snd]. rewrite <- app_assoc. cbn [app]. rewrite Ep. reflexivity. }
    split; [exact HLM2|].
    split.
    { rewrite Ecn.
      assert (H4' : rd_room (ip_S Pc) ([PjGrammar.EAlloc (S Q)] ++
                      snd (fst (vk_kont (S (ie_d E)) (Z.to_nat (ip_n Pc)) (Z.to_nat (ip_cap Pc)) (ip_acc Pc) (ip_f Pc)
                         (rest_atR (ie_tb E) (ie_text E) (ip_p Pc + 1)) s
                         (rest_atR (ie_tb E) (ie_text E) (ip_p Pc + Z.of_nat Q + 2)) [])))).
      { rewrite Hcont, Ho in M4.
        rewrite (vk_K_str0 (S (ie_d E)) (Z.to_nat (ip_n Pc)) (Z.to_nat (ip_cap Pc)) (ip_acc Pc) (ip_f Pc) (ie_tb E)
                   (ie_text E) (ip_p Pc) Q s _ Hp0 Hnth Hsc Hdec) in M4.
        rewrite (vk_K_str (S (ie_d E)) (Z.to_nat (ip_n Pc)) (Z.to_nat (ip_cap Pc)) (ip_acc Pc) (ip_f Pc) (ie_tb E)
                   (ie_text E) (ip_p Pc) Hp0 Hnth Q s _ Hsc Hdec []) in M4.
        cbn [fst snd app] in M4 |- *. exact M4. }
      rewrite Ep. exact (vl_room_tail _ _ _ _ H4' HRL2 HLV2). }
    split; [rewrite Ef; lia|].
    split; [rewrite Etr; exact (vle_blocks_step _ _ _ _ _ M6 HBB)|].
    split; [rewrite Ea; exact M7|].
    split; [rewrite ED, Etr, vl_lsum_app, vle_held_app; cbn [Ledger.lsum PjGrammar.held PjGrammar.held_ev]; lia|].
    split; [rewrite Etr; exact (vc_xfer_app _ _ _ _ _ M9 HXF2)|].
    split; [rewrite Etr; exact (vc_live_app _ _ _ _ _ M10 HLV2)|].
    (* the hull use: the use so far, then the callee's over its one event (VrdIStep.vi_hull_step) *)
    rewrite Etr. exact (vi_hull_step _ _ _ (ip_tr Pc) [PjGrammar.EAlloc (S Q)] _ eq_refl M11 HHU2). }
  split; [rewrite En, Ec; exact Hnc|]. split; [exact Ho|]. split; [exact R10|].
  split.
  { unfold pj_cstrR. split; [rewrite EL; left; reflexivity|]. split; [lia|]. split; [|exact Hcb].
    (* the new third conjunct (texts 265bfe65918): the granted request Q + 1 + cf_head is below cf_malloc_max
       (rd_room at Pc, vk_room_head), which is below 2 ^ 30 (YG08cf.cf_malloc_max_bound), and length s <= Q *)
    pose proof M4 as HR4. rewrite Hcont, Ho, Ht' in HR4.
    destruct (vk_room_head (ip_S Pc) Q t' HR4) as (Hmx & _). unfold LIVE_parse_string in Hmx.
    pose proof (@YG08cf.cf_malloc_max_bound cp) as Hcm. pose proof (@cf_head_nonneg cp). lia. }
  split; [replace (Z.of_nat (S Q)) with (Z.of_nat Q + 1) by lia; exact Hvis|].
  split; [exact Hx4|]. split; [exact Hx16|].
  exists (rest_atR (ie_tb E) (ie_text E) (ip_p Pc + 1)). split.
  { rewrite Ecn, En, Ec, Ea, Ef. reflexivity. }
  split; [unfold PjGrammar.sblock; rewrite Hsc; lia|].
  (* The kit's cut, the batch kit's layer after the key: the call kept every block of Pc's (VrdIFd.vrd_k1_keep, at P2's memory over
     Pc's blocks), the key's block is the order list's extra block, and the model's free list at the quote, the string
     granted, is the free list after the key (vk_jfb_str) with the key's request k + cf_head (HI_head) *)
  destruct HK1 as (Hcap1 & Hinc & af & HFO & HFL).
  pose (P2' := MkIPos (ip_fx P2) (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_regs P2) (ip_mem P2) (ip_md P2) (ip_k P2)
                 (ip_n P2) (ip_cap P2) (ip_kids P2) (ip_keys P2) (ip_p P2) (ip_acc P2) (ip_f P2) (ip_cont P2)
                 (ip_ok P2) (ip_tr P2) (ip_D Pc) (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2)).
  destruct (vrd_k1_keep E Pc P2' [] af Ek Ey En Ec Ea eq_refl
              ltac:(intros xx kk Hx; exact (HinL2 _ Hx))
              ltac:(eapply rd_keep_mono; [exact K2'|]; intros a Ha; right; exact Ha)
              HND Hinc HFO) as (Hinc2 & HFO2).
  split; [rewrite En, Ec; exact Hcap1|]. split; [exact Hinc2|].
  exists af. split.
  { intros Hh nn Hnn. destruct (HFO2 Hh nn Hnn) as (Di' & Facc & HP & HOI & Hm).
    exists Di', Facc. split; [|split; [exact HOI | exact Hm]].
    unfold P2' in HP. cbn [ip_D ip_kids ip_keys ip_cap app] in HP. rewrite ED.
    eapply perm_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact HP. }
  intros okr. rewrite Eok, <- app_assoc. cbn [app].
  rewrite (HFL (true :: okr)), Ho.
  rewrite (vk_jfb_str _ _ _ _ _ _ _ Hp0 Hnth Q s _ af okr Hsc Hdec).
  rewrite Ef, En, Ec, Ep, HI_head. reflexivity.
Qed.


(* ---- 10. the call of parse_string at row 148 ---- *)
(* no event: the ledger stays *)
Lemma vk_lm_nil : forall Lam peak cnt fail ran most gt,
  0 <= cnt < 2 ^ 64 -> 0 <= Ledger.lsum Lam <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [] gt [] [] Lam peak cnt fail ran.
Proof.
  intros Lam peak cnt fail ran most gt Hc Hpk. unfold rd_ledger_move, prh_oks, prh_refused_peak.
  cbn [PjGrammar.calls PjGrammar.is_call hpeakR length map app List.seq fold_right].
  split; [split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
  split; [cbn [Z.of_nat]; rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|].
  split; [unfold fail_afterR; split; intros Hf; [cbn [Z.of_nat] in Hf; lia | reflexivity]|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|]. lia.
Qed.

(* an event list that holds nothing at its end charges only its heads *)
Lemma vk_prh_held0 : forall t, PjGrammar.held t = 0 -> 0 <= prh_held t.
Proof.
  intros t H. unfold prh_held. rewrite H. pose proof (@cf_head_nonneg cp).
  apply Z.add_nonneg_nonneg; [lia | apply Z.mul_nonneg_nonneg; lia].
Qed.

Ltac vk_pj := unfold vk_with; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys
  ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].
Ltac vk_retcfg := unfold vrd_cfg; cbn [ip_fx ip_regs ip_mem ip_md];
  change (w64 (A_IPC VK_RET_SLOT)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat VK_RET_SLOT)); reflexivity.

(* fpre's fourth conjunct at the parse_string call (kit 04388d628fb on): the jal's return pc, listing slot VK_RET_SLOT,
   is below the run's allocation ceiling - PRW_StepKit's ONE copy, in a CLOSED goal (S7bPjWrite: its vm_compute in a
   large proof context timed out; here it ran away for 40 min / 60 GB, measured 2026-10-29) *)
Lemma vk_ret_slot_ceil : bv_unsigned (Z_to_bv 64 (BASE + 24324)) < YM05.alloc_ceiling.
Proof.
  pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PAI) 24324 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
  rewrite unsigned_lit_small; [exact H|]. rewrite vi_base. unfold A_prog_base. lia.
Qed.

Definition vk_ret_post (E : vrd_ient) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P2, W2 = ip_W P2 /\ c2 = vrd_cfg VK_RET_SLOT P2 /\ (vk_retR E P2 \/ exists x k nm, vk_retK E P2 x k nm).
(* the same post with the element count of the reached position (the loop's progress) *)
Definition vk_ret_postn (E : vrd_ient) (n : Z) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P2, W2 = ip_W P2 /\ c2 = vrd_cfg VK_RET_SLOT P2 /\ ip_n P2 = n /\
    (vk_retR E P2 \/ exists x k nm, vk_retK E P2 x k nm).

Lemma vk_call_step_P : forall CTX CTX0 CW E P (Pm : (word -> option byte) -> Prop),
  srr_inv_laws SEGS Pm -> srr_inv_call SEGS Pm ->
  (forall fxP : YK11.FPState, tparse_string_specX (fx := fxP) B ARx SK CTX0 CW) ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_call E P ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_CALL_SLOT P)
    (fun W2 c2 => vk_ret_postn E (ip_n P) W2 c2 /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P Pm PLAW PCALL HPS HEN HC HPM.
  pose proof HC as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Hcont & Ho & Hlt & Hnth & R10 & HK1).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ. pose proof HJN as (_ & HJrest).
  (* The kit's cut: the depot's room for the cursor set CW at the call state (the entry's, carried by the journal at the
     budget CW, VrdIElem.vrd_wild_room_at) *)
  pose proof (vrd_wild_room_at B ARx SK CTX CTX0 CW E P HEN HJN) as HWR.
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & Hhome & Hled & Hfrs & Hcnt).
  pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11).
  (* the entry's hull budget: room for the call's all-granted events (vrd_ient_ok's trailing slot) *)
  pose proof HEN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & HHB)).
  pose proof Hin as (_ & _ & _ & _ & _ & Ht0 & _ & Hpp & _).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose proof HFR as (Hf0 & _).
  pose proof (vrd_reader_call_pre B ARx SK LAWS) as VRC.
  destruct (VRC CTX CTX0 CW E P (ip_regs P) Hfr144 Hs0c Hs0ps HEN HFR HJN Hf0 G8)
    as (HCUR & HCE & HCH & Hq16 & Hq24' & HFW & HROD & HTOP).
  destruct (vk_st_ok (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) VK_CALL_SLOT) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (vk_EI (ip_regs P))) by (unfold vk_EI; apply Eimg_env).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [cbn; apply awr_ok_nil|].
  match goal with H : frame_of _ _ (ip_mem P) _ |- _ => rename H into HF1 end.
  assert (HM : ms_mem ms = ip_mem P) by (eapply vk_frame_none; exact HF1).
  set (EI := vk_EI (ip_regs P)) in *.
  assert (EW : forall n (r : bv 5), (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r -> ew EI n = getr (ip_regs P) r)
    by (intros n r Hn Hr; unfold EI, vk_EI; rewrite (Eimg_low (PI := PAI)) by exact Hn; exact (ew_Ereg_nat (ip_regs P) _ n r Hr)).
  prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  rewrite (EW 2%nat (2%bv : bv 5) ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
  rewrite (EW 3%nat (3%bv : bv 5) ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EW 4%nat (4%bv : bv 5) ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EW 8%nat (8%bv : bv 5) ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EW 10%nat (10%bv : bv 5) ltac:(unfold A_TEXT; lia) eq_refl) in Q10.
  set (MD1 := with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P)) in *.
  pose proof HFW as (He0' & He16 & Hetop & Hepres).
  assert (Hsp : spZ (ms_regs ms) = spZ (ip_regs P)) by (unfold spZ; rewrite Q2; reflexivity).
  (* the call's all-granted trace through parse_string's (the live counts at its calls, and its refused arm's
     OUTCOME), and the entry's live counts *)
  pose proof Hcont as Hcont1. rewrite Ho in Hcont1.
  destruct (vk_gt_ps E P HMD Hcont1 ltac:(lia) Hnth) as (rest & Hgt).
  pose proof HEN as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & HSEC0 & H240) & _).
  pose proof asan_consts as (C1 & _).
  assert (Hq64 : 0 <= ie_q E < 2 ^ 64) by lia.
  destruct (HCH (spZ (ip_regs P)) ltac:(lia)) as (chc & Hchc & _).
  eapply SRr'_bind.
  { (* The kit's cut: parse_string posts at the budget wbudget CW 0 (fpostWbm), so the call rule is the budgeted one,
       from the position's journal at its budget ie_CW E (VrdArm.vrd_call_Wb_P) *)
    eapply (vrd_call_Wb_P (fx := ip_fx P) B ARx SK LAWS Pm PCALL (ip_W P) EI _ ms
        (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
        (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] (ip_ly P) (ip_S P)
        (ip_Hp P) MD1 (ip_k P) (ie_CW E) STK_parse_string (ie_e E + 144) [(ie_q E, ie_q E + 8)]
        (- (ie_e E + 144)) _ _ (YCbqGwild.wbudget CW 0)).
    + exact HS.
    + reflexivity.
    + exact (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ).
    + rewrite Hsp. lia.
    + replace (- (ie_e E + 144)) with ((- (ie_e E / 16) - 9) * 16)
        by (pose proof (Z.div_mod (ie_e E) 16 ltac:(lia)); lia).
      apply Z_mod_mult.
    + lia.
    + exact vk_stk_ps_nonneg.
    + pose proof (vk_stk_budget (ie_d E)). lia.
    + lia.
    + rewrite Q3. exact G3.
    + rewrite Q4. exact G4.
    + exact Q1.
    + apply ret_ok_codeptr_v; [lia | reflexivity].
    + pose proof (@pa_B_ok _ _ PI_prog_A) as HBok. rewrite unsigned_lit_small by lia. lia.
    + unfold s0Z. rewrite Q8, G8, HM. unfold w64. rewrite unsigned_lit_small by lia.
      replace (spZ (ie_regs E) + ie_e E + - (ie_e E + 144)) with (spZ (ip_regs P)) by lia.
      exact Hchc.
    + first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM) | (cbn [cfg_ms]; rewrite HM; exact HPM)].
    + intros HPRE1. cbn [ss_pc setpc].
      refine (HPS (ip_fx P) (ie_most E) (ie_own E)
                (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ms_regs ms) (ms_mem ms) MD1 chc (ie_e E + 144) (ie_q E)
                (ie_text E) (ie_len E) (ip_p P) (Z.of_nat (ie_d E) + 1) (ie_tb E)
                (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      * split; [exact HPRE1|]. rewrite HM. split; [exact HROD|]. split; [rewrite Hsp; exact HTOP|].
        (* fpre's fourth conjunct, kit 04388d628fb: the jal's return pc is listing slot VK_RET_SLOT; its fifth (the kit
           reader text), the float state's frm_zero, is vrd_ijrn's *)
        unfold raZ. rewrite Q1. split; [exact vk_ret_slot_ceil|].
        pose proof HJN as (_ & _ & Hfz & _). exact Hfz.
      * destruct HEN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCL & _). exact HCL.
      * rewrite HM, Hsp. unfold prh_s0. rewrite Hs0ps, Z.add_0_r.
        destruct (HCH (spZ (ip_regs P) - pi_frame F_parse_string)) as (chs & Hchs & _);
          [pose proof (pi_frame_nonneg F_parse_string); lia|].
        exists chs. exact Hchs.
      * (* prh_cur_low *) rewrite HM. exact (proj2 (HCUR F_parse_string (or_introl eq_refl))).
      * (* The kit's cut: the cursor set CW in prh_cur_ok's slot (PRH_Base.prh_cw_ok) *)
        rewrite HM. exact (proj1 (HCUR F_parse_string (or_introl eq_refl))).
      * rewrite Hsp. exact Hq16.
      * exact (proj1 M4).
      * (* The kit's cut: the wild room for CW with no fresh slot *) exact HWR.
      * rewrite vk_ps_evs. eapply Z.le_trans; [| exact HSEC0]. apply Nat2Z.inj_le. rewrite Hgt.
        exact (vi_pk_mid _ (ie_S E) (ip_S P) (ip_tr P) _ rest M10).
      * rewrite vk_ps_evs. eapply Z.le_trans; [| exact H240]. apply Nat2Z.inj_le. rewrite Hgt.
        exact (vi_pk_mid _ (ie_S E) (ip_S P) (ip_tr P) _ rest M10).
      * (* the hull budget at parse_string's all-granted events: the entry's, past the events so far
           (PresetHullBudget.hull_budget_infix over the call's all-granted events split at the call) *)
        rewrite vk_ps_evs. pose proof HHB as HHB'. rewrite Hgt, !PresetHullBudget.hull_rd_app in HHB'.
        exact (PresetHullBudget.hull_budget_infix (ie_S E) (ip_S P) _ _ _ HHB' M11).
      * rewrite Q10, R10. reflexivity.
      * rewrite HM. exact Hin.
      * exact Hlt.
      * exact Hnth.
      * unfold fwin. rewrite Hsp, HM. exact HFW.
      * rewrite Hsp. lia.
      * rewrite Hsp. lia.
      * rewrite HM. exact Hraq.
      * rewrite HM. exact Hsrc.
      * exact Hhome.
      * rewrite HM. exact Hled.
      * lia.
      * (* The kit's cut: the request bound, and the live room at each event of parse_string's all-granted run (rd_room's
           per-event room, PRH_Base.prh_live_evs, over the call's segment of the granted trace) *)
        split.
        -- intros Qn HQn.
           assert (Hp0 : ie_text E <= ip_p P) by lia.
           destruct (vk_gt_head (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P)
                       (ie_tb E) (ie_text E) (ip_p P) Qn Hp0 Hnth HQn) as (t' & Ht').
           rewrite Ho in Hcont. rewrite Hcont, Ht' in M4.
           exact (proj1 (vk_room_head (ip_S P) Qn t' M4)).
        -- rewrite vk_ps_evs. pose proof M4 as (_ & _ & HL4).
           assert (Hsplit : snd (fst (ip_cont P [])) =
                            snd (fst (PjGrammar.jr_string (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)) [])) ++ rest).
           { apply (app_inv_head (ip_tr P)). rewrite <- (vc_gt_split E P HMD). exact Hgt. }
           rewrite Hsplit in HL4. unfold PresetReqAt.rd_hevs in HL4 |- *. rewrite flat_map_app in HL4.
           exact (vl_live_evs_prefix _ _ _ HL4).
    + intros a Ha. left. destruct Ha as (r & Hin' & Hr). cbn [In] in Hin'.
      destruct Hin' as [<- | []]. cbn [fst snd] in Hr.
      exists (ie_q E, ie_q E + 8). split; [left; reflexivity | cbn [fst snd]; exact Hr]. }
  intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & Hc2 & HWB & HJ2 & HJc2 & HWIN2 & HP2 & HQ2 &
                     HMN2).
  (* the call-site position Pc: P with the registers and the model after the jal *)
  assert (HRk : forall r, In r vk_live -> getr (ms_regs ms) r = getr (ip_regs P) r).
  { intros r Hr. unfold vk_live in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ match goal with |- getr _ ?rr = _ =>
          let Qr := fresh "Qr" in prreg HS rr Qr; rewrite Qr; apply EW; [unfold A_TEXT; lia | reflexivity] end |]).
    destruct Hr. }
  rewrite HM in HJ.
  destruct (vk_with_ok E P (ms_regs ms) MD1 HRk (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
              HFR HRG HND HCU HJN HMD) as (C1f & C2r & C3n & C4c & C5j & C6m).
  rewrite HM in HJc2, HWIN2.
  destruct HQ2 as (res & R10' & HRL2 & HHU2 & HBB & HQ).
  (* THE HULL USE at an exit after the call, on every refused arm: the use so far, then parse_string's over its
     all-granted list, inside the call's all-granted events (VrdIStep.vi_hull_exit over vk_gt_ps's split) *)
  assert (HHX : PresetHullBudget.hull_used (ie_S E) S2
                  (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))))
    by exact (vi_hull_exit _ _ _ (ip_tr P) _ rest _ _ Hgt (vk_ps_evs _ []) M11 HHU2).
  assert (HWIN2' : forall a, spZ (ie_regs E) - 144 <= a < spZ (ie_regs E) + ie_e E ->
            ~ inFP [(ie_q E, ie_q E + 8)] a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H (ip_W P)) (ip_mem P) a)
    by (intros a Ha; apply HWIN2; lia).
  assert (Hp0 : ie_text E <= ip_p P) by lia.
  pose proof HEN as (_ & _ & _ & _ & HRD & _ & Hpnth & _).
  pose proof HRD as (_ & _ & _ & _ & HinE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED0 & _ & HCB0).
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED0) as (_ & _ & Hc0 & _).
  pose proof HinE as (_ & _ & _ & _ & _ & Ht0E & _ & HppE & _).
  rewrite Ho in Hpnth.
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ Hled) as (Hlpk & _).
  pose proof M3 as (_ & HcntM & _).
  (* the granted trace of the loop from the entry, and its bounds *)
  set (x0 := rest_atR (ie_tb E) (ie_text E) (ie_p E)) in *.
  assert (Hx0 : x0 = 123 :: rest_atR (ie_tb E) (ie_text E) (ie_p E + 1))
    by (unfold x0; apply vk_rest_cons; [lia | exact Hpnth]).
  pose proof (M2 []) as HT. rewrite app_nil_r in HT. rewrite Hcont, Ho in HT.
  assert (HGT : forall u r, snd (fst (vrd_jtail (S (ie_d E)) true (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P)
                                (ip_f P) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) [])) = u ++ r ->
            (PjGrammar.calls (ip_tr P ++ u) <= 2 * length x0)%nat /\
            forall pp rr, ip_tr P ++ u = pp ++ rr ->
              PjGrammar.held pp <= 224 * Z.of_nat (length x0) + 512 * Z.of_nat (PjGrammar.MAXD - ie_d E)).
  { intros u r Hur. rewrite Hur in HT. split.
    - pose proof (PjGrammar.G7_4_items prh_jr_strtod (ie_d E) true 123 (rest_atR (ie_tb E) (ie_text E) (ie_p E + 1))
                    (ip_ok P)) as G. rewrite <- Hx0, HT in G. cbn [fst snd] in G.
      rewrite app_assoc, vle_calls_app in G. lia.
    - intros pp rr Hpr. pose proof (PjGrammar.G10_2_items prh_jr_strtod (ie_d E) true 123
        (rest_atR (ie_tb E) (ie_text E) (ie_p E + 1)) (ip_ok P) pp (rr ++ r)) as G.
      rewrite <- Hx0, HT in G. apply G. cbn [fst snd]. rewrite app_assoc, Hpr. symmetry. apply app_assoc. }
  destruct (HGT [] _ eq_refl) as (Hcl0 & Hpre0).
  rewrite app_nil_r in Hcl0, Hpre0.
  assert (HBd : 0 <= 224 * Z.of_nat (length x0) + 512 * Z.of_nat (PjGrammar.MAXD - ie_d E)) by lia.
  assert (Hpk0 : hpeakR (ip_tr P) <= 224 * Z.of_nat (length x0) + 512 * Z.of_nat (PjGrammar.MAXD - ie_d E))
    by (apply vl_hpeak_bound; [exact HBd | exact Hpre0]).
  assert (Hnw : ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P)) < 2 ^ 64) by lia.
  assert (Hcnt' : ip_cnt P = ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P)))
    by (rewrite HcntM; apply Z.mod_small; lia).
  assert (Hcp0 : 0 <= ip_cnt P) by lia.
  assert (HBS : forall lyx Sx, ablocks B lyx Sx = ablocks B (ip_ly P) (ip_S P) -> blocks_bytes Sx = blocks_bytes (ip_S P))
    by (intros lyx Sx Hx; rewrite (vi_blocks_bytes_lsum B lyx Sx), (vi_blocks_bytes_lsum B (ip_ly P) (ip_S P)), Hx;
        reflexivity).
  rewrite Hc2 in HMN2 |- *. apply SRr'_ret.
  split; [|exact HMN2].
  destruct (PjGrammar.scan (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))) as [Q|] eqn:Hsc.
  - destruct (vk_gt_head (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) (ie_tb E)
                (ie_text E) (ip_p P) Q Hp0 Hnth Hsc) as (t' & Ht').
    destruct (HGT [PjGrammar.EAlloc (S Q)] t' Ht') as (Hcl1 & Hpre1).
    assert (Hpk1 : hpeakR (ip_tr P ++ [PjGrammar.EAlloc (S Q)]) <=
                   224 * Z.of_nat (length x0) + 512 * Z.of_nat (PjGrammar.MAXD - ie_d E))
      by (apply vl_hpeak_bound; [exact HBd | exact Hpre1]).
    assert (Hc1 : ip_cnt P + 1 < 2 ^ 64).
    { rewrite vle_calls_app in Hcl1. change (PjGrammar.calls [PjGrammar.EAlloc (S Q)]) with 1%nat in Hcl1. lia. }
    (* the failure index after the granted prefix is the entry's *)
    pose proof M3 as M3g. rewrite M1 in M3g.
    pose proof (vi_lm_granted _ _ _ _ _ _ _ _ _ _ _ _ _ _ M3g (proj1 Hc0) Hnw) as (_ & Hflp).
    destruct HQ as [HQ | [HQ | [HQ | HQ]]].
    + (* the chosen failure *)
      destruct HQ as (Hcf & Hr0 & HHp & Hab & _ & HLED2 & Hin2 & HLV & HXF). subst res.
      exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs2 mem2 md2 (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P ++ [false])
              (ip_tr P ++ [PjGrammar.EFail (S Q)]) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P + 1) SIZE_MAXZ (ip_ran P)).
      split; [reflexivity|]. split; [vk_retcfg|]. split; [reflexivity|]. left.
      match goal with |- vk_retR E ?P2 =>
      refine (vk_after_refuse CTX CTX0 CW E (vk_with P (ms_regs ms) MD1) P2 (STK_parse_string + (ie_e E + 144)) k1 WS1
                [PjGrammar.EFail (S Q)] [false] HEN C1f C2r C3n C4c C5j C6m Hnc Ho HJc2 HWIN2' HP2 HJ2 HWB eq_refl R10'
                Hab eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl _ _ _ HLED2 Hin2 HRL2
                _ _ HHX _ _ _ _ (proj1 Hc0) Hnw _ HK1 _) end.
      * vk_pj. apply vle_fail_chosen; lia.
      * vk_pj. apply vle_lsz_fail.
      * exact (proj1 (proj2 (vle_held_shapes (S Q)))).
      * vk_pj. unfold vc_xfer. rewrite <- (vk_jrs_fail _ Q [] Hsc), <- vk_ps_evs. exact HXF.
      * vk_pj. unfold vc_live. rewrite <- (vk_jrs_fail _ Q [] Hsc), <- vk_ps_evs. exact HLV.
      * right. apply (vc_outc_chosen E _ (PjGrammar.calls (ip_tr P))).
        -- cbn [ip_cnt ip_fail vk_with] in Hcf. lia.
        -- rewrite (vc_gt_split E P HMD), vle_calls_app, Hcont, Ho, Ht'. cbn [PjGrammar.calls PjGrammar.is_call]. lia.
      * (* the callee's part of the injected-reading outcome: the one refused call is the chosen failure, at the
           call's counter (cnt = fail, the counter after the granted prefix) *)
        intros sm' x' os' i' H0' hist' Hp' Hr' Hc' Hw' ii Hii _.
        assert (ii = 0%nat) by (cbn [PjGrammar.calls PjGrammar.is_call] in Hii; lia). subst ii.
        cbn [ip_cnt ip_fail ip_tr vk_with] in Hcf |- *. lia.
      * vk_pj. rewrite (HBS ly2 S2 Hab). pose proof (vk_prh_held0 _ (proj1 (proj2 (vle_held_shapes (S Q))))). lia.
      * vk_pj. change (rest_atR (ie_tb E) (ie_text E) (ie_p E)) with x0. rewrite vle_hpeak_app. cbn [hpeakR PjGrammar.held_ev]. pose proof (vle_held_le_hpeak (ip_tr P)). lia.
      * intros okr. vk_pj. rewrite Hcont, Ho. cbn [app]. eapply vk_K_fail; eassumption.
      * intros okr. vk_pj. cbn [app]. eapply vk_N_fail; eassumption.
    + (* the allocator's refusal: fuzz_malloc's refusal arm's ledger, and the arm's exclusion as the OUTCOME *)
      destruct HQ as (Hcf & Hr0 & HHp & Hab & _ & _ & _ & HEX & HLED2 & Hin2 & HLV & HXF). subst res.
      rewrite Z.mod_small in HLED2 by lia.
      replace (Z.of_nat Q + 1) with (Z.of_nat (S Q)) in HLED2 by lia.
      exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs2 mem2 md2 (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P ++ [false])
              (ip_tr P ++ [PjGrammar.EFail (S Q)]) (ip_D P) (ip_Lam P)
              (Z.max (ip_peak P) (Z.min SIZE_MAXZ (Ledger.lsum (ip_Lam P) + Z.of_nat (S Q)))) (ip_cnt P + 1) (ip_fail P)
              (if Z.of_nat (S Q) <=? ie_most E then 1 else ip_ran P)).
      split; [reflexivity|]. split; [vk_retcfg|]. split; [reflexivity|]. left.
      match goal with |- vk_retR E ?P2 =>
      refine (vk_after_refuse CTX CTX0 CW E (vk_with P (ms_regs ms) MD1) P2 (STK_parse_string + (ie_e E + 144)) k1 WS1
                [PjGrammar.EFail (S Q)] [false] HEN C1f C2r C3n C4c C5j C6m Hnc Ho HJc2 HWIN2' HP2 HJ2 HWB eq_refl R10'
                Hab eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl _ _ _ HLED2 Hin2 HRL2
                _ _ HHX _ _ _ _ (proj1 Hc0) Hnw _ HK1 _) end.
      * vk_pj. rewrite Hcont, Ho, Ht'. apply vle_fail_refused; [lia | lia | lia | lia | lia | reflexivity].
      * vk_pj. apply vle_lsz_fail.
      * exact (proj1 (proj2 (vle_held_shapes (S Q)))).
      * vk_pj. unfold vc_xfer. rewrite <- (vk_jrs_fail _ Q [] Hsc), <- vk_ps_evs. exact HXF.
      * vk_pj. unfold vc_live. rewrite <- (vk_jrs_fail _ Q [] Hsc), <- vk_ps_evs. exact HLV.
      * right. apply (vc_outc_refused E _ (ip_S P) (ip_tr P) (prhPs_evs (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)) [])
                        (PresetReqAt.rd_hevs rest)).
        -- change (rest_atR (ie_tb E) (ie_text E) (ie_p E)) with x0. rewrite Hgt, vk_ps_evs.
           unfold PresetReqAt.rd_hevs. rewrite !flat_map_app. reflexivity.
        -- exact M9.
        -- exact HEX.
      * (* the callee's part of the injected-reading outcome: a chosen failure at the call's counter is this call;
           past it the model's list grants parse_string's one call, so its events there are its all-granted ones
           (vk_ps_prefix, vk_ps_evs_grant), which the arm's exclusion forbids *)
        intros sm' x' os' i' H0' hist' Hp' Hr' Hc' Hw' ii Hii _.
        assert (ii = 0%nat) by (cbn [PjGrammar.calls PjGrammar.is_call] in Hii; lia). subst ii.
        cbn [ip_S ip_cont ip_tr vk_with] in Hp', Hr', Hc', Hw' |- *.
        destruct (Z.eq_dec (ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P))) (ie_fail E)) as [Heq | Hne]; [lia|].
        exfalso. rewrite Hcont, Ho in Hr', Hc'.
        destruct (vk_ps_prefix _ _ _ _ _ _ _ _ _ sm' x' os' i' Hp0 Hnth Hr' Hc') as (Hrs & Hcs).
        rewrite (vrd_okk_split 1 (Z.to_nat (ie_fail E - ie_cnt E) - PjGrammar.calls (ip_tr P)) ltac:(lia)),
          vk_ps_evs_grant in Hrs, Hcs.
        exact (HEX sm' x' os' i' H0' hist' Hp' Hrs Hcs).
      * vk_pj. rewrite (HBS ly2 S2 Hab). pose proof (vk_prh_held0 _ (proj1 (proj2 (vle_held_shapes (S Q))))). lia.
      * vk_pj. change (rest_atR (ie_tb E) (ie_text E) (ie_p E)) with x0. rewrite vle_hpeak_app. cbn [hpeakR PjGrammar.held_ev]. pose proof (vle_held_le_hpeak (ip_tr P)). lia.
      * intros okr. vk_pj. rewrite Hcont, Ho. cbn [app]. eapply vk_K_fail; eassumption.
      * intros okr. vk_pj. cbn [app]. eapply vk_N_fail; eassumption.
    + (* a bad escape: the block taken and given back *)
      destruct HQ as (Hcf & Hr0 & Hdn & HHp & Hab & HLED2 & Hin2 & HLV & HXF). subst res.
      replace (Z.of_nat Q + 1) with (Z.of_nat (S Q)) in HLED2 by lia.
      exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs2 mem2 md2 (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P ++ [true])
              (ip_tr P ++ [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)]) (ip_D P) (ip_Lam P) (Z.max (ip_peak P) (Ledger.lsum (ip_Lam P) + Z.of_nat (S Q))) (ip_cnt P + 1) (ip_fail P) (ip_ran P)).
      split; [reflexivity|]. split; [vk_retcfg|]. split; [reflexivity|]. left.
      match goal with |- vk_retR E ?P2 =>
      refine (vk_after_refuse CTX CTX0 CW E (vk_with P (ms_regs ms) MD1) P2 (STK_parse_string + (ie_e E + 144)) k1 WS1
                [PjGrammar.EAlloc (S Q); PjGrammar.EFree (S Q)] [true] HEN C1f C2r C3n C4c C5j C6m Hnc Ho HJc2 HWIN2' HP2
                HJ2 HWB eq_refl R10'
                Hab eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl _ _ _ HLED2 Hin2 HRL2
                _ _ HHX _ (fun _ _ _ _ _ _ _ _ _ _ => vrd_granted_rep 1 _ _ _) _ _ (proj1 Hc0) Hnw _ HK1 _) end.
      * vk_pj. apply vle_alloc_free; lia.
      * vk_pj. apply vle_lsz_alloc_free.
      * exact (proj1 (proj2 (proj2 (vle_held_shapes (S Q))))).
      * vk_pj. unfold vc_xfer. rewrite <- (vk_jrs_badesc _ Q [] Hsc Hdn), <- vk_ps_evs. exact HXF.
      * vk_pj. unfold vc_live. rewrite <- (vk_jrs_badesc _ Q [] Hsc Hdn), <- vk_ps_evs. exact HLV.
      * left. reflexivity.
      * vk_pj. rewrite (HBS ly2 S2 Hab).
        pose proof (vk_prh_held0 _ (proj1 (proj2 (proj2 (vle_held_shapes (S Q)))))). lia.
      * vk_pj. change (rest_atR (ie_tb E) (ie_text E) (ie_p E)) with x0. rewrite vle_hpeak_app in Hpk1 |- *. cbn [hpeakR PjGrammar.held_ev] in Hpk1 |- *. lia.
      * intros okr. vk_pj. rewrite Hcont, Ho. cbn [app]. eapply vk_K_badesc; eassumption.
      * intros okr. vk_pj. cbn [app]. eapply vk_N_badesc; eassumption.
    + (* the string, in a new block *)
      destruct HQ as (Hcf & Hx4 & Hx16 & s & r & Hdec & HHp & Hab & Hvis & Hcb & HLED2 & Hin2 & HLV & HXF).
      destruct (vk_rest_decode (ie_tb E) (ie_text E) (ip_p P) Q s r Hp0 Hsc Hdec) as (Er & _). subst r.
      rewrite (vk_gtrace_str _ Q s _ Hsc Hdec) in HBB.
      replace (Z.of_nat Q + 1) with (Z.of_nat (S Q)) in HLED2 by lia.
      assert (HXFs : vc_xfer (ip_S P) S2 [PjGrammar.EAlloc (S Q)])
        by (unfold vc_xfer; rewrite <- (vk_jrs_str _ Q s _ [] Hsc Hdec), <- vk_ps_evs; exact HXF).
      assert (HLVs : vc_live (ip_S P) S2 [PjGrammar.EAlloc (S Q)])
        by (unfold vc_live; rewrite <- (vk_jrs_str _ Q s _ [] Hsc Hdec), <- vk_ps_evs; exact HLV).
      assert (HHUs : PresetHullBudget.hull_used (ip_S P) S2 (PresetReqAt.rd_hevs [PjGrammar.EAlloc (S Q)]))
        by (rewrite <- (vk_jrs_str _ Q s _ [] Hsc Hdec), <- vk_ps_evs; exact HHU2).
      exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs2 mem2 md2 (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
              (ip_keys P) (ip_p P + Z.of_nat Q + 2) (ip_acc P) (ip_f P) (vk_kont (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P)
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)) s (rest_atR (ie_tb E) (ie_text E) (ip_p P + Z.of_nat Q + 2))) (ip_ok P ++ [true])
              (ip_tr P ++ [PjGrammar.EAlloc (S Q)]) (ip_D P ++ [(res, Z.of_nat (S Q))]) ((res, Z.of_nat (S Q)) :: ip_Lam P) (Z.max (ip_peak P) (Ledger.lsum (ip_Lam P) + Z.of_nat (S Q))) (ip_cnt P + 1) (ip_fail P) (ip_ran P)).
      split; [reflexivity|]. split; [vk_retcfg|]. split; [reflexivity|]. right. exists res, (Z.of_nat (S Q)), s.
      match goal with |- vk_retK E ?P2 _ _ _ =>
        exact (vk_after_str CTX CTX0 CW E (vk_with P (ms_regs ms) MD1) P2 (STK_parse_string + (ie_e E + 144)) k1 WS1 Q s
                 res HEN C1f C2r C3n C4c C5j C6m Hnc Ho Hcont Hlt Hnth Hsc Hdec HJc2 HWIN2' HP2 HJ2 HWB eq_refl Hcf Hx4
                 Hx16 Hab Hvis Hcb HLED2 Hin2 HRL2 HXFs HLVs HHUs HBB R10' eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HK1) end.
  - (* no closing quote: nothing taken *)
    destruct HQ as (Hr0 & HHp & Hab & HLED2 & Hin2 & HLV & HXF). subst res.
    exists (MkIPos (ip_fx P) ly2 S2 Hp2 W2 regs2 mem2 md2 (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P)
              (ip_keys P) (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P ++ [])
              (ip_tr P ++ []) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)).
    split; [reflexivity|]. split; [vk_retcfg|]. split; [reflexivity|]. left.
    match goal with |- vk_retR E ?P2 =>
      refine (vk_after_refuse CTX CTX0 CW E (vk_with P (ms_regs ms) MD1) P2 (STK_parse_string + (ie_e E + 144)) k1 WS1
                [] [] HEN C1f C2r C3n C4c C5j C6m Hnc Ho HJc2 HWIN2' HP2 HJ2 HWB eq_refl R10'
                Hab eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl _ _ _ HLED2 Hin2 HRL2
                _ _ HHX _ (fun _ _ _ _ _ _ _ _ _ _ => vrd_granted_rep 0 _ _ _) _ _ (proj1 Hc0) Hnw _ HK1 _) end.
    * vk_pj. apply vk_lm_nil; lia.
    * vk_pj. replace (lszR []) with (@nil nat) by reflexivity. rewrite !app_nil_r. apply Permutation_refl.
    * reflexivity.
    * vk_pj. unfold vc_xfer. rewrite <- (vk_jrs_noscan _ [] Hsc), <- vk_ps_evs. exact HXF.
    * vk_pj. unfold vc_live. rewrite <- (vk_jrs_noscan _ [] Hsc), <- vk_ps_evs. exact HLV.
    * left. reflexivity.
    * vk_pj. rewrite (HBS ly2 S2 Hab). pose proof (vk_prh_held0 [] eq_refl). lia.
    * vk_pj. rewrite app_nil_r. exact Hpk0.
    * intros okr. vk_pj. rewrite Hcont, Ho. cbn [app]. eapply vk_K_noscan; eassumption.
    * intros okr. vk_pj. cbn [app]. eapply vk_N_noscan; eassumption.
Qed.


(* ---- 11. C2, rows 149..175: keys[n] := a0 (with its two ASan gates), the NULL test, the cursor gates, p vs end ---- *)
Definition VK_W2_SLOT : nat := 6108%nat.   (* row 176, A 0x87550: the second white-space loop's head *)
Definition VK_C3_SLOT : nat := 6127%nat.   (* row 195, A 0x8759c: the colon test *)

(* atoms 32 / 33: the cursor's p and end; 34 / 35: the node's keys and n words; 36: the slot address keys + 8 n *)
Definition vk_EK (regs : bvmap 5 word) (p e keys n : Z) : env :=
  @Eimg _ A_prog_listing PAI (Ereg regs [w64 p; w64 e; w64 keys; w64 n; w64 (keys + 8 * n)]).
(* s6 = v + 40 and s2 = its shadow address, as expressions over the node atom 20 (s4 = v) *)
Definition vk_shv (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 k) (SLit 3)) (SOff 26 0).
Definition vk_srK : list sv := sr_set (sr_set vk_sr0 22%bv (SOff 20 40)) 18%bv (vk_shv 40).
(* the frame word at sp + 32 holds v + 32 (vrd_iframe's sp0 - 112) *)
Definition vk_fr_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 32 40 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 20 32))].
Definition vk_node_region : YP09.region :=
  YP09.mkRegion (Some 20%nat) 32 48 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 34 0)); YP09.mkChunk 40 (CVal 8 (SOff 35 0))].
Definition vk_slot_region : YP09.region := YP09.mkRegion (Some 36%nat) 0 8 0 8 [].
Definition vk_slot_alias : sv * sv := (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 3)), SOff 36 0).
Definition vk_factsK : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
            (20%nat, mkAF 4096 (2 ^ 47 - 57) 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0); (33%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (34%nat, mkAF 4096 (2 ^ 47) 0); (35%nat, mkAF 0 (2 ^ 54) 0); (36%nat, mkAF 4096 (2 ^ 47 - 8) 0) ]
          [] [vk_slot_alias].
Definition vk_ssK (k : nat) : sstate :=
  mkSS (4 * Z.of_nat k) vk_srK [vk_cur_region false; vk_fr_region; vk_node_region; vk_slot_region] None vk_factsK.
Definition vk_SHK : list shent := [mkSHE 8 0 24; mkSHE 20 0 56; mkSHE 36 0 8].

Lemma vk_U_shv : forall E' v k, ew E' 20 = w64 v -> ew E' 26 = w64 SHADOW_OFF ->
  0 <= v -> 0 <= k -> v + k < 2 ^ 47 ->
  U E' (vk_shv k) = SHADOW_OFF + (v + k) / 8.
Proof.
  intros E' v k H20 H26 Hv Hk Hvk. unfold vk_shv.
  rewrite !U_SAlu, (U_lit E' 3) by lia.
  rewrite U_SOff, H20. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite (U_atom E' 26 SHADOW_OFF H26) by (unfold SHADOW_OFF; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite (zcanon_id (v + k)) by (unfold M64; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= (v + k) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (zcanon_id ((v + k) / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

(* a2 at C2's end (A 0x8751c, a2 := (a0 >> 3) + s10): the shadow address of the key slot, over the slot atom 36 *)
Lemma vk_U_slot_sh : forall E' z, ew E' 36 = w64 z -> ew E' 26 = w64 SHADOW_OFF -> 0 <= z < 2 ^ 47 ->
  U E' (SAlu ALU_ADD (SAlu ALU_SRL (SOff 36 0) (SLit 3)) (SOff 26 0)) = SHADOW_OFF + z / 8.
Proof.
  intros E' z H36 H26 Hz.
  rewrite !U_SAlu, (U_lit E' 3) by lia.
  rewrite U_SOff, H36. unfold w64. rewrite unsigned_lit_small by lia. rewrite ?Z.add_0_r.
  rewrite (U_atom E' 26 SHADOW_OFF H26) by (unfold SHADOW_OFF; lia).
  cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite (zcanon_id z) by (unfold M64; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= z / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (zcanon_id (z / 8)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

Lemma vk_seatK : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q p en sp v keys n (k : nat),
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 23 = w64 (shadow_addr (q + 8)) -> getr regs 27 = w64 (shadow_addr q) ->
  getr regs 2 = w64 sp -> getr regs 20 = w64 v -> getr regs 22 = w64 (v + 40) ->
  getr regs 18 = w64 (shadow_addr (v + 40)) ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  2 ^ 46 <= sp -> sp + 40 <= q -> sp mod 16 = 0 ->
  4096 <= v -> v + 57 <= 2 ^ 47 -> (v + 48 <= sp + 32 \/ sp + 40 <= v + 32) -> (v + 48 <= q \/ q + 24 <= v + 32) ->
  4096 <= keys <= 2 ^ 47 -> 0 <= n <= 2 ^ 54 -> 4096 <= keys + 8 * n -> keys + 8 * n + 8 <= sp ->
  (keys + 8 * n + 8 <= v + 32 \/ v + 48 <= keys + 8 * n) ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  4096 <= p <= 2 ^ 47 - 8 -> 4096 <= en <= 2 ^ 47 - 8 ->
  val_mem SEGS (mrestrict (w_H W) mem) (sp + 32) 8 (v + 32) ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 32) 8 keys -> val_mem SEGS (mrestrict (w_H W) mem) (v + 40) 8 n ->
  rd_rw SEGS (mrestrict (w_H W) mem) (keys + 8 * n) 8 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  (forall x, v <= x < v + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (keys + 8 * n) 8 ->
  (forall x, keys + 8 * n <= x < keys + 8 * n + 8 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  st_ok_pi (fx := fxP) SEGS VAL (vk_EK regs p en keys n) (vk_ssK k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vk_SHK (vk_EK regs p en keys n) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q p en sp v keys n k R8 R26 R23 R27 R2 R20 R22 R18 Hq1 Hq2 Hq8 Hs1 Hsq Hs16 Hv1 Hv2 Hvs Hvq
    Hk1 Hn1 Hsl1 Hsl2 Hslv Vp Ve Hp He Vfr Vkeys Vn Hrw Hraq Hrav Hvsh Hras Hssh.
  set (EK := vk_EK regs p en keys n).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EK j = getr regs r).
  { intros j Hj r Hr. unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E2 : ew EK 2 = w64 sp) by (rewrite (EL 2%nat ltac:(lia) 2%bv eq_refl); exact R2).
  assert (E8 : ew EK 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E20 : ew EK 20 = w64 v) by (rewrite (EL 20%nat ltac:(lia) 20%bv eq_refl); exact R20).
  assert (E26 : ew EK 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew EK 32 = w64 p).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew EK 33 = w64 en).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (E34 : ew EK 34 = w64 keys).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  assert (E35 : ew EK 35 = w64 n).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 3). }
  assert (E36 : ew EK 36 = w64 (keys + 8 * n)).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 4). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (SO : forall j z, ew EK j = w64 z -> 0 <= z < 2 ^ 64 -> forall c, 0 <= z + c < 2 ^ 64 ->
            sv_denot EK (SOff j c) = w64 (z + c)).
  { intros j z Hj Hz c Hc. cbn [sv_denot]. rewrite Hj. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (Uq : U EK (SOff 8 0) = q) by (unfold U; rewrite (SO 8%nat q E8 ltac:(lia) 0 ltac:(lia)), Z.add_0_r;
                                          unfold w64; apply unsigned_lit_small; lia).
  assert (Uv : U EK (SOff 20 0) = v) by (unfold U; rewrite (SO 20%nat v E20 ltac:(lia) 0 ltac:(lia)), Z.add_0_r;
                                           unfold w64; apply unsigned_lit_small; lia).
  assert (Us : U EK (SOff 36 0) = keys + 8 * n) by (unfold U; rewrite (SO 36%nat _ E36 ltac:(lia) 0 ltac:(lia)), Z.add_0_r;
                                                       unfold w64; apply unsigned_lit_small; lia).
  assert (UB : U EK (SOff 26 0) = SHADOW_OFF)
    by (unfold U; rewrite (SO 26%nat SHADOW_OFF E26 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)),
          Z.add_0_r; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (Q23 : getr regs 23 = sv_denot EK (vk_sh_of 8)).
  { rewrite R23. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EK (vk_sh_of 8)).
    rewrite (vk_U_sh EK q 8 E8 E26) by lia. unfold shadow_addr.
    assert (0 <= (q + 8) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity. }
  assert (Q27 : getr regs 27 = sv_denot EK (vk_sh_of 0)).
  { rewrite R27. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EK (vk_sh_of 0)).
    rewrite (vk_U_sh EK q 0 E8 E26) by lia. unfold shadow_addr. rewrite Z.add_0_r.
    assert (0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity. }
  assert (Q22 : getr regs 22 = sv_denot EK (SOff 20 40)) by (rewrite R22, (SO 20%nat v E20 ltac:(lia) 40 ltac:(lia)); reflexivity).
  assert (Q18 : getr regs 18 = sv_denot EK (vk_shv 40)).
  { rewrite R18. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U EK (vk_shv 40)).
    rewrite (vk_U_shv EK v 40 E20 E26) by lia. unfold shadow_addr.
    assert (0 <= (v + 40) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vk_ssK. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vk_srK, vk_sr0.
      apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg;
        [apply regs_ok_Eimg_Ereg | reflexivity | exact Q23] | reflexivity | exact Q27] | reflexivity | exact Q22]
        | reflexivity | exact Q18].
    + reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * unfold region_ok, vk_cur_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E8. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS EK _ q 0 8 (SOff 32 0) p);
             [rewrite (SO 32%nat p E32 ltac:(lia) 0 ltac:(lia)), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
           rewrite Z.add_0_r. exact Vp.
        -- apply (chunk_ok_val SEGS EK _ q 8 8 (SOff 33 0) en);
             [rewrite (SO 33%nat en E33 ltac:(lia) 0 ltac:(lia)), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
           exact Ve.
      * unfold region_ok, vk_fr_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E2. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS EK _ sp 32 8 (SOff 20 32) (v + 32));
          [rewrite (SO 20%nat v E20 ltac:(lia) 32 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact Vfr].
      * unfold region_ok, vk_node_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E20. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        pose proof Vkeys as Vk'. pose proof Vn as Vn'.
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS EK _ v 32 8 (SOff 34 0) keys);
             [rewrite (SO 34%nat keys E34 ltac:(lia) 0 ltac:(lia)), Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact Vkeys].
        -- apply (chunk_ok_val SEGS EK _ v 40 8 (SOff 35 0) n);
             [rewrite (SO 35%nat n E35 ltac:(lia) 0 ltac:(lia)), Z.add_0_r; reflexivity | cbn; lia | cbn; lia | exact Vn].
      * unfold region_ok, vk_slot_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E36. unfold w64. rewrite unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hrw; lia | apply Forall_nil].
    + apply pairwise_disjoint_of_extents. unfold vk_cur_region, vk_fr_region, vk_node_region, vk_slot_region, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite E8, E2, E20, E36. unfold w64. rewrite !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [vk_factsK f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E2, E8, E20, E26, E32, E33, E34, E35, E36. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
        change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
        repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | match goal with |- ?g => idtac "FACTG" g end; fail].
      * cbn [vk_factsK f_alias alias_ok vk_slot_alias]. split; [|exact I].
        apply bv_eq. change (U EK (SAlu ALU_ADD (SOff 34 0) (SAlu ALU_SLL (SOff 35 0) (SLit 3))) = U EK (SOff 36 0)).
        assert (Uk : U EK (SOff 34 0) = keys) by (unfold U; rewrite (SO 34%nat keys E34 ltac:(lia) 0 ltac:(lia)), Z.add_0_r;
                                                    unfold w64; apply unsigned_lit_small; lia).
        assert (Un : U EK (SOff 35 0) = n) by (unfold U; rewrite (SO 35%nat n E35 ltac:(lia) 0 ltac:(lia)), Z.add_0_r;
                                                 unfold w64; apply unsigned_lit_small; lia).
        rewrite !U_SAlu, Uk, Un, (U_lit EK 3), Us by lia. cbn [zalu_raw]. change (Z.land 3 63) with 3.
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
        rewrite (zcanon_id (n * 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
  - unfold sh_ok, vk_SHK. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (shent_ok_of_range SEGS (w_H W) mem EK (SOff 26 0) 8 q 24 q 0 24 Hraq UB Uq); [lia | lia |].
      intros x Hx. unfold SHADOW_OFF in *. lia.
    + apply (shent_ok_of_range SEGS (w_H W) mem EK (SOff 26 0) 20 v 56 v 0 56 Hrav UB Uv); [lia | lia |].
      intros x Hx. apply Hvsh. lia.
    + apply (shent_ok_of_range SEGS (w_H W) mem EK (SOff 26 0) 36 (keys + 8 * n) 8 (keys + 8 * n) 0 8 Hras UB Us);
        [lia | lia |].
      intros x Hx. apply Hssh. lia.
Qed.


(* parse_items' frame [sp0 - 144, sp0) is above alloc_ceiling (fpre's astk_ok and STK_parse_items >= 144) *)
Lemma vk_sp_frame : forall CTX CTX0 CW E, vrd_ient_ok B ARx CTX CTX0 CW E ->
  YM05.alloc_ceiling <= spZ (ie_regs E) - 144 /\ (spZ (ie_regs E) - 144) mod 16 = 0.
Proof.
  intros CTX CTX0 CW E HEN.
  pose proof HEN as ((HAFN & _) & _).
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & _).
  assert (HSTK : 144 <= STK_parse_items (ie_d E)).
  { unfold STK_parse_items. rewrite Hfr144. pose proof (pi_frame_nonneg F_parse_value).
    assert (0 <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
    assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + 144))
      by (apply Z.mul_nonneg_nonneg; lia).
    lia. }
  split; [lia|]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.

(* the state after the key store, before the second white-space loop: vk_retK's facts with keys[n] = x (the kit's cut: its
   the batch kit's layer after the key, as vk_retK's, read by VrdIKeyB's colon test) *)
Definition vk_key (E : vrd_ient) (P : vrd_ipos) (x k : Z) (nm : list Z) : Prop :=
  vrd_iframe E P /\ vrd_iregs B E P /\ vrd_inode E P [(x, k)] /\ vrd_icur B E P /\ vrd_ijrn B ARx SK E P /\
  vrd_imodel E P /\ ip_n P < ip_cap P /\ ie_o E = true /\
  rd_u64 SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ip_keys P + 8 * ip_n P) x /\
  pj_cstrR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) x k nm /\
  prhReader_vis (ip_W P) (ip_mem P) x k /\ 4096 + cf_head <= x /\ x mod 16 = 0 /\
  exists z, ip_cont P = vk_kont (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) z nm
                         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
            PjGrammar.sblock z = Z.to_nat k /\
  ip_cap P = Z.of_nat (PresetReqAt.ncap (S (Z.to_nat (ip_n P)))) /\ vrd_incaps E P /\
  exists af, vrd_iforder E P [(x, k)] af /\
    (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
       vk_jfk (ip_f P) (S (ie_d E)) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af [k + cf_head]
         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr).
(* row 176, the second white-space loop's top: a1 = a4 = p, a3 = end, p < end; a0 = the key slot keys + 8 n and
   a2 = its shadow address, as C2 left them at A 0x87514 / 0x8751c (no instruction from 0x87520 to 0x875c4 writes
   either; REFUSE-B at 0x87754 reads both - A2KeyB's finding, a Theorem Labs lane's approved interface change) *)
Definition vk_w2 (E : vrd_ient) (P : vrd_ipos) (x k : Z) (nm : list Z) : Prop :=
  vk_key E P x k nm /\ getr (ip_regs P) 11 = w64 (ip_p P) /\ getr (ip_regs P) 14 = w64 (ip_p P) /\
  getr (ip_regs P) 13 = w64 (ie_text E + ie_len E) /\
  getr (ip_regs P) 10 = w64 (ip_keys P + 8 * ip_n P) /\ getr (ip_regs P) 12 = w64 (shadow_addr (ip_keys P + 8 * ip_n P)) /\
  ip_p P < ie_text E + ie_len E.
(* row 195, the colon test: a3 = end, a0 / a2 the key slot and its shadow address (as at vk_w2); p = end, or the byte
   at p is not white space *)
Definition vk_c3 (E : vrd_ient) (P : vrd_ipos) (x k : Z) (nm : list Z) : Prop :=
  vk_key E P x k nm /\ getr (ip_regs P) 13 = w64 (ie_text E + ie_len E) /\
  getr (ip_regs P) 10 = w64 (ip_keys P + 8 * ip_n P) /\ getr (ip_regs P) 12 = w64 (shadow_addr (ip_keys P + 8 * ip_n P)) /\
  (ip_p P = ie_text E + ie_len E \/
   (ip_p P < ie_text E + ie_len E /\ exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\
      PjGrammar.ws b = false)).
Definition vk_c2K_post (E : vrd_ient) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P2 x k nm, W2 = ip_W P2 /\
    ((c2 = vrd_cfg VK_W2_SLOT P2 /\ vk_w2 E P2 x k nm) \/ (c2 = vrd_cfg VK_C3_SLOT P2 /\ vk_c3 E P2 x k nm)).
(* the same post with the element count of the reached position (the loop's progress) *)
Definition vk_c2K_postn (E : vrd_ient) (n : Z) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P2 x k nm, W2 = ip_W P2 /\ ip_n P2 = n /\
    ((c2 = vrd_cfg VK_W2_SLOT P2 /\ vk_w2 E P2 x k nm) \/ (c2 = vrd_cfg VK_C3_SLOT P2 /\ vk_c3 E P2 x k nm)).

(* a value the symbolic state holds in a chunk of one of its regions (VrdNum.vrd_val_of_st's form at this image) *)
Lemma vk_val_of_st : forall (fxP : YK11.FPState) E ss ms (H : word -> bool) (b : option nat) lo hi wlo whi cs off
    (n : N) ev v,
  st_ok_pi (fx := fxP) SEGS VAL E ss (restrict H ms) ->
  In (YP09.mkRegion b lo hi wlo whi cs) (ss_mem ss) -> In (YP09.mkChunk off (CVal n ev)) cs ->
  sv_denot E ev = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E b + off) (N.to_nat n) v.
Proof.
  intros fxP E ss ms H b lo hi wlo whi cs off n ev v HS Hr Hc He Hv Hn.
  destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
  apply (val_of_chunk_ok SEGS E _ _ off n ev v); [|exact He|exact Hv|exact Hn].
  apply (region_ok_chunk SEGS E _ (YP09.mkRegion b lo hi wlo whi cs)); [|exact Hc].
  eapply mem_ok_region; [exact HM | exact Hr].
Qed.

(* the live registers after a run over vk_ssK: the atoms are kept, s7 / s11 / s6 / s2 keep their seated expressions *)
Lemma vk_regs_afterK : forall (fxP : YK11.FPState) (H : word -> bool) E' ss ms regs0 extra,
  st_ok_pi (fx := fxP) SEGS VAL E' ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E' ->
  sr_get (ss_regs ss) 23%bv = vk_sh_of 8 -> sr_get (ss_regs ss) 27%bv = vk_sh_of 0 ->
  sr_get (ss_regs ss) 22%bv = SOff 20 40 -> sr_get (ss_regs ss) 18%bv = vk_shv 40 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 19; 20; 21; 24; 25; 26]%bv = true ->
  getr regs0 23 = sv_denot E' (vk_sh_of 8) -> getr regs0 27 = sv_denot E' (vk_sh_of 0) ->
  getr regs0 22 = sv_denot E' (SOff 20 40) -> getr regs0 18 = sv_denot E' (vk_shv 40) ->
  forall r, In r vk_live -> getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fxP H E' ss ms regs0 extra HS HA H23 H27 H22 H18 Hl R23 R27 R22 R18 r Hr.
  pose proof (st_ok_pi_restrict_reg (fx := fxP) H E' ss ms r HS) as Hg.
  assert (HK : forall r', In r' [2; 3; 4; 8; 9; 19; 20; 21; 24; 25; 26]%bv -> getr (ms_regs ms) r' = getr regs0 r')
    by exact (regs_kept_of_st_ok_pi (fx := fxP) E' ss (restrict H ms) regs0 extra
                [2; 3; 4; 8; 9; 19; 20; 21; 24; 25; 26]%bv HS HA Hl).
  unfold vk_live in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ first [ rewrite H23 in Hg; rewrite Hg; symmetry; exact R23
            | rewrite H27 in Hg; rewrite Hg; symmetry; exact R27
            | rewrite H22 in Hg; rewrite Hg; symmetry; exact R22
            | rewrite H18 in Hg; rewrite Hg; symmetry; exact R18
            | apply HK; cbn; tauto ] |]).
  destruct Hr.
Qed.

(* the C2 store's frame: only the slot region has a write window *)
Lemma vk_frame_slot : forall E' rs (m m' : word -> option byte) a0,
  (forall a, in_wrange E' rs a -> a0 <= a < a0 + 8) -> frame_of E' rs m m' ->
  forall y : word, ~ (a0 <= bv_unsigned y < a0 + 8) -> m' y = m y.
Proof. intros E' rs m m' a0 Hw HF y Hy. apply HF. intros Hin. exact (Hy (Hw _ Hin)). Qed.

Ltac vk_awrK E36u Htmp :=
  lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_gen; [reflexivity | cbn [ew ewset Nat.eqb]; exact E36u | intros a Ha; right; right; left; apply Htmp;
    cbn [YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_nil].

(* the composed frame of the C2 runs: raw memory outside the slot is the position's *)
Ltac vk_rawK a0 E36u :=
  intros y Hy;
  repeat match goal with HF : frame_of ?E' ?rs ?m ?m' |- ?m' y = _ =>
    rewrite (vk_frame_slot E' rs m m' a0
               ltac:(let rs' := eval vm_compute in rs in change rs with rs';
                     intros a (r & Hr & Ha); cbn [In] in Hr;
                     repeat (destruct Hr as [<- | Hr];
                       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; cbn [ew ewset Nat.eqb] in Ha;
                        first [lia | rewrite E36u in Ha; lia] |]);
                     destruct Hr) HF y Hy) end;
  reflexivity.

(* The kit's cut: THE BATCH KIT'S LAYER ACROSS A STORE INTO THE KEY SLOT keys[n] (VrdIFd.vrd_k1_keep's twin for a store INTO a block
   the position owns, the keys array). The members' caps read the slot array and the members' blocks, the order list
   also the key slots below n: none is the stored slot. The keep is stated as the two parts a slot store gives
   (VrdSlotStore.vk_slot_store_keep_core's keep of every OTHER block, and the slots below n of the keys array, which a
   store at slot n leaves), with the ledger's NoDup of D separating the keys array from the members' blocks. *)
Lemma vk_k1_slot : forall E P P2 Dx af,
  ip_kids P2 = ip_kids P -> ip_keys P2 = ip_keys P -> ip_n P2 = ip_n P -> ip_cap P2 = ip_cap P ->
  ip_acc P2 = ip_acc P -> ip_D P2 = ip_D P ->
  (forall x k, In (x, k) (ip_D P) -> prh_lin (ip_Lam P2) x k) ->
  List.NoDup (ip_D P) -> ip_n P < ip_cap P -> ie_o E = true ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
    (fun z => exists b, In b (ip_D P) /\ b <> (ip_keys P, 8 * ip_cap P) /\ pj_holdsR b z) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
    (fun z => ip_keys P <= z < ip_keys P + 8 * ip_n P) ->
  vrd_inode E P Dx -> vrd_incaps E P -> vrd_iforder E P Dx af ->
  vrd_incaps E P2 /\ vrd_iforder E P2 Dx af.
Proof.
  intros E P P2 Dx af Ek Ey En Ec Ea ED HLk HNd Hlt Ho HKD HKY HND HNC HFO.
  pose proof HND as (_ & Hnc0 & _ & _ & _ & Hlen & (Di & HDp & Hsub) & _).
  assert (Hkd : In (ip_kids P, 56 * ip_cap P) (ip_D P)).
  { apply (Permutation_in _ (Permutation_sym HDp)). apply in_or_app. right. apply in_or_app. left.
    unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). left. reflexivity. }
  assert (Hkne : (ip_kids P, 56 * ip_cap P) <> (ip_keys P, 8 * ip_cap P)) by (intros H; injection H as _ H; lia).
  (* a block of a split of D beside the extra blocks and the arrays is a block of D other than the keys array *)
  assert (Hrest : forall Dy, Permutation (ip_D P) (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++
                     keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Dy) ->
                  forall b, In b Dy -> In b (ip_D P) /\ b <> (ip_keys P, 8 * ip_cap P)).
  { intros Dy HP b Hb. split.
    - apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hb.
    - intros ->. pose proof (Permutation_NoDup HP HNd) as HN.
      apply NoDup_app_remove_l, NoDup_app_remove_l in HN.
      assert (Ekb : keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) = [(ip_keys P, 8 * ip_cap P)])
        by (unfold keys_blkR; rewrite Ho; destruct (Z.eqb_spec (ip_cap P) 0); [lia | reflexivity]).
      rewrite Ekb in HN. cbn [app] in HN.
      apply (proj1 (List.NoDup_cons_iff _ _)) in HN. exact (proj1 HN Hb). }
  assert (Hkr : forall z, ip_kids P <= z < ip_kids P + 56 * ip_n P ->
                  exists b, In b (ip_D P) /\ b <> (ip_keys P, 8 * ip_cap P) /\ pj_holdsR b z).
  { intros z Hz. exists (ip_kids P, 56 * ip_cap P). split; [exact Hkd|]. split; [exact Hkne|].
    unfold pj_holdsR. cbn [fst snd]. lia. }
  assert (Hdr : forall Dy, Permutation (ip_D P) (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++
                   keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Dy) ->
                forall z, rd_blk Dy z -> exists b, In b (ip_D P) /\ b <> (ip_keys P, 8 * ip_cap P) /\ pj_holdsR b z).
  { intros Dy HP z Hz. unfold rd_blk in Hz. apply Exists_exists in Hz as (b & Hb & Hzb).
    destruct (Hrest Dy HP b Hb) as (HbD & Hbne). exists b. exact (conj HbD (conj Hbne Hzb)). }
  split.
  - unfold vrd_incaps in HNC |- *. rewrite Ea, Ek.
    assert (HK' : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
                    (fun z => ip_kids P <= z < ip_kids P + 56 * Z.of_nat (length (rev (ip_acc P))) \/ rd_blk Di z)).
    { eapply rd_keep_mono; [exact HKD|]. intros z [Hz | Hz].
      - apply Hkr. rewrite length_rev in Hz. lia.
      - exact (Hdr Di HDp z Hz). }
    rewrite Ho in Hsub.
    exact (vrd_ncaps_keep_mems SEGS (rev (ip_acc P)) _ _ _ (ip_kids P) (ip_keys P) Di Hsub HNC HK').
  - intros Hh nn Hnn. rewrite Ea in Hnn.
    destruct (HFO Hh nn Hnn) as (Di' & Facc & HP & HOI & Hm).
    exists Di', Facc. rewrite ED, Ek, Ey, Ec, En. split; [exact HP|]. split; [|exact Hm].
    apply (PRH_PjOrder.pf_oitemsR_frame SEGS nn _ _ _ _ (ie_o E) (ip_kids P) (ip_keys P) (Z.to_nat (ip_n P)) Di' Facc
             HOI).
    + intros x k Hin. exact (HLk x k (proj1 (Hrest Di' HP _ Hin))).
    + intros y Hy'. unfold PRH_PjOrder.pf_ofoot in Hy'. destruct Hy' as [Hy | [(Hks & Hy) | (b & Hb & Hy)]].
      * apply (vrd_agree_of_keep SEGS _ _ _ HKD y). apply Hkr. lia.
      * apply (vrd_agree_of_keep SEGS _ _ _ HKY y). lia.
      * apply (vrd_agree_of_keep SEGS _ _ _ HKD y). destruct (Hrest Di' HP b Hb) as (HbD & Hbne).
        exists b. exact (conj HbD (conj Hbne Hy)).
Qed.

(* ---- the key store's position: vk_retK carried across the store of x into keys[n] ---- *)
Lemma vk_key_after : forall CTX CTX0 CW E P x k nm regs mem' md' k',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_retK E P x k nm ->
  (forall y : word, ~ (ip_keys P + 8 * ip_n P <= bv_unsigned y < ip_keys P + 8 * ip_n P + 8) -> mem' y = ip_mem P y) ->
  val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ip_keys P + 8 * ip_n P) 8 x ->
  (forall r, In r vk_live -> getr regs r = getr (ip_regs P) r) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  vk_key E (vk_move P regs mem' md' k' (ip_p P)) x k nm.
Proof.
  intros CTX CTX0 CW E P x k nm regs mem' md' k' HEN HK Hraw Vx HR HJ'.
  pose proof HK as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & R10 & Hcs & Hvis & Hx4 & Hx16 & Hz).
  pose proof HCU as (Hin & Hraq & Hsrc & Hhome & Hled & Hfrs & Hcnt).
  pose proof HMD as (_ & _ & HLM & _).
  pose proof HJN as ((HAR & _) & _ & _ & _ & _ & HBM & _).
  pose proof HND as (_ & Hnc0 & Hcap & _ & _ & _ & (Di & HPerm & _) & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (@cf_head_nonneg cp) as Hch.
  assert (Hin8 : In (ip_keys P, 8 * ip_cap P)
                   (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
  { apply in_or_app. right. unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia|]. cbn. left. reflexivity. }
  assert (HKm : forall y : word, ~ (ip_keys P + 8 * ip_n P <= bv_unsigned y < ip_keys P + 8 * ip_n P + 8) ->
            mrestrict (w_H (ip_W P)) mem' y = mrestrict (w_H (ip_W P)) (ip_mem P) y)
    by (intros y Hy; unfold mrestrict; rewrite (Hraw y Hy); reflexivity).
  assert (Hsp : spZ regs = spZ (ip_regs P)) by (unfold spZ; rewrite (HR 2%bv ltac:(cbn; tauto)); reflexivity).
  destruct (vk_slot_store_keep_core B ARx SK LAWS HW PST_IMG CTX CTX0 CW E P [(x, k)] regs mem' md' k' (ip_keys P) 8
              Hfr144 Hs0c HEN HFR HND HJN Hin Hraq Hled HLM Hin8 Hnc HKm Hsp HJ')
    as (F' & N' & J' & Pin' & Raq' & Led' & Src' & KeepD).
  destruct (vk_slot_place B ARx SK LAWS HW CTX CTX0 CW E P _ (ip_keys P) 8 Hfr144 HEN HND Hled HJN Hin8 Hnc)
    as (_ & Hpl2 & Hplz & _ & _ & _).
  destruct (vss_blk E P _ (ip_keys P) 8 HND Hnc Hin8) as (_ & _ & HkD).
  assert (Hk4 : 4096 <= ip_keys P < alloc_ceiling)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HkD | unfold pj_holdsR; cbn [fst snd]; lia]).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (_ & Be0 & Bse & _).
  (* the key block is another D block *)
  assert (HNd : List.NoDup (ip_D P)).
  { pose proof HLM as (_ & _ & _ & HPL & _). pose proof Hled as (_ & HNL & _).
    assert (HNL' : List.NoDup (map fst (ip_Lam P))) by (first [exact HNL | apply NoDup_ListNoDup; exact HNL]).
    apply (Permutation_map fst) in HPL. pose proof (Permutation_NoDup HPL HNL') as H. rewrite map_app in H.
    apply NoDup_app_remove_r in H. exact (NoDup_map_inv _ _ H). }
  assert (HxD : In (x, k) (ip_D P)) by (apply (Permutation_in _ (Permutation_sym HPerm)); left; reflexivity).
  assert (Hxne : (x, k) <> (ip_keys P, 8 * ip_cap P)).
  { pose proof (Permutation_NoDup HPerm HNd) as HN2.
    refine (vss_nodup_app _ [(x, k)] _ _ _ HN2 (or_introl eq_refl) _).
    apply in_app_or in Hin8. destruct Hin8 as [Hk8 | Hk8];
      [apply in_or_app; left; exact Hk8 | apply in_or_app; right; apply in_or_app; left; exact Hk8]. }
  pose proof Hcs as (_ & Hsk & _).
  assert (Hxlow : 4096 <= x /\ x + k <= alloc_ceiling).
  { assert (H1 : 4096 <= x < alloc_ceiling)
      by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HxD | unfold pj_holdsR; cbn [fst snd]; lia]).
    assert (H2 : 4096 <= x + k - 1 < alloc_ceiling)
      by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HxD | unfold pj_holdsR; cbn [fst snd]; lia]).
    lia. }
  unfold vk_key. vk_proj.
  split; [exact F'|].
  split.
  { unfold vrd_iregs in *. cbn [ip_regs].
    rewrite !HR by (cbn; tauto). exact HRG. }
  split; [exact N'|].
  split.
  { unfold vrd_icur. cbv zeta.
    split; [exact Pin'|]. split; [exact Raq'|]. split; [exact (Src' Hsrc)|]. split; [exact Hhome|].
    split; [exact Led'|]. split; [exact Hfrs|]. exact Hcnt. }
  split; [exact J'|]. split; [exact HMD|]. split; [exact Hnc|]. split; [exact Ho|].
  split; [split; [lia | exact Vx]|].
  split.
  { eapply pj_cstrR_keep; [exact Hcs | intros H; exact H |].
    eapply rd_keep_mono; [exact KeepD|]. intros zz Hzz. cbv beta in Hzz |- *. exists (x, k).
    split; [exact HxD|]. split; [exact Hxne|]. unfold pj_holdsR. cbn [fst snd]. lia. }
  split.
  { destruct Hvis as (Hra & Hhull). split.
    - apply (vss_keep_ra _ (ip_mem P) mem' _ _ _ _ HKm); [exact Hplz | lia | lia | exact Hra].
    - intros Hk0. apply (vss_keep_hull _ (ip_mem P) mem' _ _ _ _ HKm); [exact Hplz | lia | lia | lia | exact (Hhull Hk0)]. }
  split; [exact Hx4|]. split; [exact Hx16|].
  (* The kit's cut, the batch kit's layer across the store into keys[n] (vk_k1_slot) *)
  destruct Hz as (z & Hc & Hsb & Hcap1 & Hinc & af & HFO & HFL).
  pose proof HLM as (_ & _ & _ & HPL & _).
  destruct (vk_k1_slot E P (vk_move P regs mem' md' k' (ip_p P)) [(x, k)] af eq_refl eq_refl eq_refl eq_refl eq_refl
              eq_refl
              ltac:(intros xx kk Hx; unfold prh_lin; vk_proj; apply (Permutation_in _ (Permutation_sym HPL));
                    apply in_or_app; left; exact Hx)
              HNd Hnc Ho
              ltac:(vk_proj; exact KeepD)
              ltac:(vk_proj; apply (vk_keep_rd _ (ip_mem P) mem' (ip_keys P + 8 * ip_n P) (ip_keys P + 8 * ip_n P + 8)
                                      _ HKm); intros a Ha; lia)
              HND Hinc HFO) as (Hinc' & HFO').
  exists z. split; [exact Hc|]. split; [exact Hsb|]. split; [exact Hcap1|]. split; [exact Hinc'|].
  exists af. split; [exact HFO'|]. exact HFL.
Qed.

(* the model after the key across a white-space byte: vk_kname skips it *)
Lemma vk_kont_ws : forall d n cap1 acc f z nm tb text p b, text <= p ->
  nth_error tb (Z.to_nat (p - text)) = Some b -> PjGrammar.ws b = true ->
  vk_kont d n cap1 acc f z nm (rest_atR tb text p) = vk_kont d n cap1 acc f z nm (rest_atR tb text (p + 1)).
Proof.
  intros d n cap1 acc f z nm tb text p b Hp Hb Hws. rewrite (vk_rest_cons tb text p b Hp Hb).
  unfold vk_kont, vk_kname. cbn [PjGrammar.skip]. rewrite Hws. reflexivity.
Qed.

(* leaving a run of the second white-space loop that stored q->p := p' (p' = p, or p + 1 over a white-space byte):
   vk_key at the moved position - vk_unseat's transport (VrdCurStore.vk_cur_store_keep, the inode [(x, k)]) plus the
   key's facts, which are all below alloc_ceiling (the key block, keys[n]) or shadow bytes, apart from the cursor
   word [q, q + 8) on the stack *)
Lemma vk_unseatK : forall CTX CTX0 CW E P x k nm (regs' : bvmap 5 word) (mem' : word -> option byte) md' k' p',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_key E P x k nm ->
  (forall r, In r vk_live -> getr regs' r = getr (ip_regs P) r) ->
  (forall y : word, ~ (ie_q E <= bv_unsigned y < ie_q E + 8) -> mem' y = ip_mem P y) ->
  val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 8 p' ->
  (forall a, ie_q E <= a < ie_q E + 8 -> writable_at SEGS (mrestrict (w_H (ip_W P)) mem') a) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  (p' = ip_p P \/
   (p' = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\
    exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\ PjGrammar.ws b = true)) ->
  vk_key E (vk_move P regs' mem' md' k' p') x k nm.
Proof.
  intros CTX CTX0 CW E P x k nm regs' mem' md' k' p' HEN HKY HR HKr Vp' Wq HJ' Hp'.
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & Hz).
  pose proof HCU as (Hin & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof HJN as ((HAR & _) & _ & _ & _ & _ & HBM & _).
  pose proof HND as (_ & Hnc0 & Hcap & _ & _ & _ & (Di & HPerm & _) & _).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  destruct (vk_sp_frame CTX CTX0 CW E HEN) as [Hsp1 _].
  destruct (vk_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hpr : ie_text E <= p' <= ie_text E + ie_len E) by (destruct Hp' as [-> | (-> & ? & _)]; lia).
  assert (HK : forall y : word, ~ (ie_q E <= bv_unsigned y < ie_q E + 8) ->
                 mrestrict (w_H (ip_W P)) mem' y = mrestrict (w_H (ip_W P)) (ip_mem P) y)
    by (intros y Hy; unfold mrestrict; rewrite (HKr y Hy); reflexivity).
  assert (HKo : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                  (fun y => ie_q E + 8 <= y < ie_q E + 24 \/ ie_text E <= y < ie_text E + ie_len E)).
  { apply (vk_keep_rd _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) _ HK). intros a Ha. lia. }
  assert (Hpin' : pj_in_okR SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) (ie_text E) (ie_len E) p'
                    (Z.of_nat (ie_d E) + 1) (ie_tb E)).
  { split; [exact Vp'|].
    split; [eapply VrdFrame.val_mem_keep; [exact Ve | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]|].
    split; [eapply VrdFrame.val_mem_keep; [exact Vd | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]|].
    split.
    { intros y Hy. destruct (Z_lt_le_dec y (ie_q E + 8)) as [Hl | Hl]; [apply Wq; lia|].
      apply (proj2 HKo y); [cbn beta; lia | apply Hrw; lia]. }
    split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hpr|]. split; [exact Hlen|].
    split; [|exact (conj Hdisj Hd)].
    eapply VrdFrame.garr8_keep; [exact Hga | eapply VrdFrame.rd_keep_mono; [exact HKo | cbn; intros; lia]]. }
  assert (Hsp' : spZ regs' = spZ (ip_regs P)) by (unfold spZ; rewrite (HR 2%bv ltac:(cbn; tauto)); reflexivity).
  destruct (vk_cur_store_keep B ARx SK LAWS HW PST_IMG
              CTX CTX0 CW E P [(x, k)] regs' mem' md' k' p' (ie_q E) 8 Hfr144 Hs0c HEN HFR HND HCU HJN
              ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros a Ha; exists (ie_q E, ie_q E + 8); split; [left; reflexivity | cbn; lia])
              ltac:(intros a Ha; lia) HK Hsp' HJ' Hpin'
              ltac:(apply vk_rest_len; destruct Hp' as [-> | (-> & _)]; lia))
    as (W1 & W2 & W3 & W4).
  (* the key's bytes and keys[n] are below alloc_ceiling <= q *)
  assert (HKlow : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                    (fun y => 0 <= y < YM05.alloc_ceiling))
    by (apply (vk_keep_rd _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) _ HK); intros a Ha; split; lia).
  assert (Hin8 : In (ip_keys P, 8 * ip_cap P)
                   (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
  { apply in_or_app. right. unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia|]. cbn. left. reflexivity. }
  destruct (vss_blk E P _ (ip_keys P) 8 HND Hnc Hin8) as (_ & _ & HkD).
  assert (Hk1 : 4096 <= ip_keys P)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HkD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hk2 : ip_keys P + 8 * ip_cap P - 1 < YM05.alloc_ceiling)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HkD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (HxD : In (x, k) (ip_D P)) by (apply (Permutation_in _ (Permutation_sym HPerm)); left; reflexivity).
  pose proof Hcs as (_ & Hsk & _).
  assert (Hx1 : 4096 <= x)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HxD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hx2 : x + k - 1 < YM05.alloc_ceiling)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HxD | unfold pj_holdsR; cbn [fst snd]; lia]).
  unfold vk_key. split; [exact W1|]. split.
  { unfold vrd_iregs in *. vk_proj. rewrite !HR by (cbn; tauto). exact HRG. }
  split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
  split.
  { pose proof HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
    unfold vrd_imodel. vk_proj.
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
    split; [|exact (conj M6 (conj M7 M8))].
    pose proof (vk_rest_len (ie_tb E) (ie_text E) (ip_p P) p' ltac:(destruct Hp' as [-> | (-> & _)]; lia)). lia. }
  vk_proj. split; [exact Hnc|]. split; [exact Ho|].
  split.
  { destruct Vx as (Hxr & Vxm). split; [exact Hxr|].
    eapply VrdFrame.val_mem_keep; [exact Vxm|]. eapply VrdFrame.rd_keep_mono; [exact HKlow|]. cbn; intros; nia. }
  split.
  { eapply pj_cstrR_keep; [exact Hcs | intros Hl; exact Hl |].
    eapply VrdFrame.rd_keep_mono; [exact HKlow|]. cbn; intros; lia. }
  split.
  { destruct Hvis as (Hra & Hhull). split.
    - apply (vss_keep_ra _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) x k HK); [right; lia | lia | lia | exact Hra].
    - intros Hk0. apply (vss_keep_hull _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) x k HK);
        [right; lia | lia | lia | lia | exact (Hhull Hk0)]. }
  split; [exact Hx4|]. split; [exact Hx16|].
  (* The kit's cut, the batch kit's layer: the store wrote only the cursor's p word, so every block the position owns (below
     alloc_ceiling) keeps its bytes (VrdIFd.vrd_k1_keep); the free list after the key moves with the cursor over a
     white-space byte as vk_kont does (vk_jfk_ws) *)
  destruct Hz as (z & Hc & Hsb & Hcap1 & Hinc & af & HFO & HFL).
  pose proof HMD as (_ & _ & HLM & _). pose proof HLM as (_ & _ & _ & HPL & _).
  destruct (vrd_k1_keep E P (vk_move P regs' mem' md' k' p') [(x, k)] af eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              ltac:(intros xx kk Hx; unfold prh_lin; vk_proj; apply (Permutation_in _ (Permutation_sym HPL));
                    apply in_or_app; left; exact Hx)
              ltac:(vk_proj; eapply VrdFrame.rd_keep_mono; [exact HKlow|]; intros a Ha;
                    unfold rd_blk in Ha; apply Exists_exists in Ha as (b & Hb & Hab);
                    pose proof (vk_D_low B ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ b a HAR HBM Hb Hab); lia)
              HND Hinc HFO) as (Hinc' & HFO').
  exists z. split.
  { rewrite Hc. destruct Hp' as [-> | (-> & Hlt & b & Hb & Hws)]; [reflexivity|].
    apply (vk_kont_ws _ _ _ _ _ _ _ _ _ _ b); [lia | exact Hb | exact Hws]. }
  split; [exact Hsb|]. split; [exact Hcap1|]. split; [exact Hinc'|].
  exists af. split; [exact HFO'|].
  intros okr. cbn [ip_ok ip_f ip_n ip_cap ip_p]. rewrite (HFL okr).
  destruct Hp' as [-> | (-> & Hlt & b & Hb & Hws)]; [reflexivity|].
  apply (vk_jfk_ws _ _ _ _ _ _ _ _ _ b); [lia | exact Hb | exact Hws].
Qed.

(* ---- 12. C2, rows 149..175, on the KEY arm: keys[n] := x (two ASan gates, the slot by vk_slot_store_keep), the NULL
   test (refuted: x >= 4096), the cursor gates and p vs end, to row 176 (p < end) or row 195 (p = end) ---- *)
Lemma vk_c2K_step_P : forall CTX CTX0 CW E P x k nm (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_retK E P x k nm ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_RET_SLOT P)
    (fun W2 c2 => vk_c2K_postn E (ip_n P) W2 c2 /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P x k nm Pm PLAW HEN HK HPM.
  pose proof HK as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & R10 & Hcs & Hvis & Hx4 & Hx16 & Hz).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ. pose proof HJN as (_ & HJrest).
  pose proof HJN as ((HAR & _) & _ & _ & _ & _ & HBM & _).
  pose proof HBM as (HnotE & _).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & Hhome & Hled & Hfrs & Hcnt).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof Hsrc as (_ & Ht4 & Htl8 & _ & Hrat & _). rewrite Hlen in Htl8.
  pose proof HFR as (Hf0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F17 & _).
  pose proof HND as (Hhdr & Hnc0 & Hcap & Hc0 & Hlin & Hlen' & _ & _ & Hrav & _ & Hrakeys & _).
  pose proof Hhdr as (_ & _ & _ & _ & _ & (_ & Vkeys) & (_ & Vn) & _).
  pose proof HEN as (_ & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hqv & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vk_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  destruct (vk_sp_frame CTX CTX0 CW E HEN) as [Hsp1 Hsp16].
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  assert (Bv56 : ie_v E + 56 <= alloc_ceiling) by (eapply vrd_node_low; eassumption).
  assert (Happv : in_app (ie_v E) 56) by (eapply vrd_node_app; eassumption).
  assert (Hin8 : In (ip_keys P, 8 * ip_cap P)
                   (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
  { apply in_or_app. right. unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia|]. cbn. left. reflexivity. }
  assert (Hslrw : rd_rw SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ip_keys P + 8 * ip_n P) 8)
    by (eapply vk_slot_rw; eassumption).
  destruct (vk_slot_place B ARx SK LAWS HW CTX CTX0 CW E P _ (ip_keys P) 8 Hfr144 HEN HND Hled HJN Hin8 Hnc)
    as (Hpl1 & Hpl2 & Hplz & Hplsh & Hplv & Hplra).
  destruct (vss_blk E P _ (ip_keys P) 8 HND Hnc Hin8) as (_ & HlinK & HkD).
  assert (Hk4 : 4096 <= ip_keys P < alloc_ceiling)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HkD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hslv : ip_keys P + 8 * ip_n P + 8 <= ie_v E + 32 \/ ie_v E + 48 <= ip_keys P + 8 * ip_n P).
  { destruct (Z_lt_le_dec (ip_keys P + 8 * ip_n P) (ie_v E + 32)).
    - destruct (Z_lt_le_dec (ip_keys P + 8 * ip_n P + 8) (ie_v E + 33)); [lia|].
      exfalso. apply (Hplv (ie_v E + 32)); lia.
    - destruct (Z_lt_le_dec (ip_keys P + 8 * ip_n P) (ie_v E + 48)); [|lia].
      exfalso. apply (Hplv (ip_keys P + 8 * ip_n P)); lia. }
  assert (R2 : getr (ip_regs P) 2 = w64 (spZ (ip_regs P))) by (unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Vfr : val_mem SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (spZ (ip_regs P) + 32) 8 (ie_v E + 32))
    by (replace (spZ (ip_regs P) + 32) with (spZ (ie_regs E) - 112) by lia; exact F17).
  destruct (vk_seatK (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) (spZ (ip_regs P))
              (ie_v E) (ip_keys P) (ip_n P) VK_RET_SLOT G8 G26 G23 G27 R2 G20 G22 G18 Hq1 Hq2 Hq8
              ltac:(lia) ltac:(lia) ltac:(rewrite Hf0; exact Hsp16) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(destruct Hqv; [right | left]; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hslv
              Vp Ve ltac:(lia) ltac:(lia) Vfr Vkeys Vn Hslrw Hraq Hrav
              ltac:(intros y Hy; unfold in_app in Happv; unfold SHADOW_OFF, kLowShadowBeg in *; lia)
              Hplra ltac:(intros y Hy Hs; exact (Hplsh y ltac:(lia) ltac:(lia)))) as [HS SHOK].
  set (EK := vk_EK (ip_regs P) (ip_p P) (ie_text E + ie_len E) (ip_keys P) (ip_n P)) in *.
  assert (HEI : img_env VAL A_LIM EK) by (unfold EK, vk_EK; apply Eimg_env).
  assert (E36u : bv_unsigned (ew EK 36) = ip_keys P + 8 * ip_n P).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra (ip_regs P) _ 4).
    unfold w64. apply unsigned_lit_small. lia. }
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hled HlinK) as (HkK & HabK & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  destruct (req_size_pos (8 * ip_cap P + cf_head)) as [_ Hrq]; [lia|].
  assert (Htmp : forall a, ip_keys P + 8 * ip_n P <= a < ip_keys P + 8 * ip_n P + 8 ->
            in_tmp_block (ablocks B (ie_ly E) (ie_S E)) (ablocks B (ip_ly P) (ip_S P)) a).
  { intros a Ha. exists (ip_keys P - cf_head), (8 * ip_cap P + cf_head).
    split; [exact HabK|]. split; [exact (HnotE _ _ HkD)|]. lia. }
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EK j = getr (ip_regs P) r).
  { intros j Hj r Hr. unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ j r Hr). }
  assert (E10 : ew EK 10 = w64 x) by (rewrite (EL 10%nat ltac:(lia) 10%bv eq_refl); exact R10).
  assert (E32 : ew EK 32 = w64 (ip_p P)).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew EK 33 = w64 (ie_text E + ie_len E)).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 1). }
  (* the key slot (atom 36) and s10 at the seat: C2 leaves a0 = the slot and a2 = its shadow address (A 0x87514 /
     0x8751c), which vk_w2 / vk_c3 carry to REFUSE-B *)
  assert (E36 : ew EK 36 = w64 (ip_keys P + 8 * ip_n P)).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 4). }
  assert (E26 : ew EK 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact G26).
  assert (Hsl47 : 0 <= ip_keys P + 8 * ip_n P < 2 ^ 47) by lia.
  assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 (ip_keys P); w64 (ip_n P);
                                              w64 (ip_keys P + 8 * ip_n P)]) EK)
    by (split; [intros j Hj; unfold EK, vk_EK; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 22%bv HS) as R22. cbn [ms_regs restrict mkst] in R22.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 18%bv HS) as R18. cbn [ms_regs restrict mkst] in R18.
  change (sr_get (ss_regs (vk_ssK VK_RET_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
  change (sr_get (ss_regs (vk_ssK VK_RET_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
  change (sr_get (ss_regs (vk_ssK VK_RET_SLOT)) 22%bv) with (SOff 20 40) in R22.
  change (sr_get (ss_regs (vk_ssK VK_RET_SLOT)) 18%bv) with (vk_shv 40) in R18.
  assert (HxD : 4096 <= x < alloc_ceiling).
  { pose proof HND as (_ & _ & _ & _ & _ & _ & (Di & HPerm & _) & _).
    pose proof Hcs as (_ & Hsk & _).
    eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | apply (Permutation_in _ (Permutation_sym HPerm)); left; reflexivity
                                  | unfold pj_holdsR; cbn [fst snd]; lia]. }
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [vk_awrK E36u Htmp|].
  psrr_branch_tok RUN BR HS SHOK vk_Bspan.
  - (* row 167 beqz taken: a1 = x = 0, refuted *)
    exfalso. match goal with Hb : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = true |- _ =>
      rewrite branch_eq_U, (U_SOff E' 10 0), (U_lit E' 0) in Hb by lia; cbn [ew ewset Nat.eqb] in Hb;
      rewrite E10 in Hb; unfold w64 in Hb; rewrite unsigned_lit_small in Hb by lia;
      rewrite Z.add_0_r, zcanon_id in Hb by (unfold M64; lia);
      apply Z.eqb_eq in Hb; lia end.
  - paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [vk_awrK E36u Htmp|].
    psrr_branch_tok RUN BR HS SHOK vk_Bspan.
    + (* row 174 bgeu taken: p >= end, so p = end: to the colon test at row 195 *)
      assert (Hpe : ip_p P = ie_text E + ie_len E).
      { match goal with Hb : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = true |- _ =>
          rewrite branch_geu_U, (U_SOff E' 32 0), (U_SOff E' 33 0) in Hb; cbn [ew ewset Nat.eqb] in Hb;
          rewrite E32, E33 in Hb; unfold w64 in Hb; rewrite !unsigned_lit_small in Hb by lia;
          rewrite !Z.add_0_r, !zcanon_id in Hb by (unfold M64; lia);
          apply Bool.negb_true_iff, Z.ltb_ge in Hb; lia end. }
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_C3_SLOT); [vk_awrK E36u Htmp|].
      lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
        assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 (ip_keys P);
                                                       w64 (ip_n P); w64 (ip_keys P + 8 * ip_n P)]) E2)
          by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros j Hj; cbn [ew ewset];
              repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
        assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
          by (eapply (vk_regs_afterK _ _ _ _ _ _ _ HSe HA2);
              [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity | rewrite R23; reflexivity | rewrite R27; reflexivity
              | rewrite R22; reflexivity | rewrite R18; reflexivity]);
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 13%bv HSe) as R13e;
        cbn [ms_regs restrict] in R13e;
        (lazymatch type of R13e with _ = sv_denot _ (sr_get ?l _) =>
           let v := eval vm_compute in (sr_get l 13%bv) in change (sr_get l 13%bv) with v in R13e end);
        cbn [sv_denot] in R13e; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R13e;
        cbn [ew ewset Nat.eqb] in R13e; rewrite E33 in R13e;
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HSe) as R10k;
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 12%bv HSe) as R12k;
        cbn [ms_regs restrict] in R10k, R12k;
        (lazymatch type of R10k with _ = sv_denot _ (sr_get ?l _) =>
           let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in R10k;
           let v2 := eval vm_compute in (sr_get l 12%bv) in change (sr_get l 12%bv) with v2 in R12k end);
        cbn [sv_denot] in R10k; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R10k;
        cbn [ew ewset Nat.eqb] in R10k; rewrite E36 in R10k;
        assert (R12s : getr (ms_regs ms2) 12 = w64 (shadow_addr (ip_keys P + 8 * ip_n P)))
          by (rewrite R12k; symmetry; apply bv_eq; unfold w64; rewrite Z_to_bv_unsigned;
              fold (U E2 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 36 0) (SLit 3)) (SOff 26 0)));
              rewrite (vk_U_slot_sh E2 (ip_keys P + 8 * ip_n P)
                         ltac:(cbn [ew ewset Nat.eqb]; exact E36) ltac:(cbn [ew ewset Nat.eqb]; exact E26) Hsl47);
              unfold shadow_addr;
              assert (0 <= (ip_keys P + 8 * ip_n P) / 8 < 2 ^ 44)
                by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
              unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
              rewrite Z.mod_small by (unfold SHADOW_OFF; lia); reflexivity);
        assert (Hraw : forall y : word, ~ (ip_keys P + 8 * ip_n P <= bv_unsigned y < ip_keys P + 8 * ip_n P + 8) ->
                  ms_mem ms2 y = ip_mem P y) by (vk_rawK (ip_keys P + 8 * ip_n P) E36u);
        assert (Vx : val_mem SEGS (mrestrict (w_H (ip_W P)) (ms_mem ms2)) (ip_keys P + 8 * ip_n P) 8 x)
          by (replace (ip_keys P + 8 * ip_n P) with (base_val E2 (Some 36%nat) + 0)
                by (cbn [base_val ew ewset Nat.eqb]; rewrite E36u; lia);
              refine (vk_val_of_st _ E2 ss2 ms2 (w_H (ip_W P)) (Some 36%nat) 0 8 0 8
                        [YP09.mkChunk 0 (CVal 8 (SOff 10 0))] 0 8%N (SOff 10 0) x HSe _ _ _ _ _);
              [ vm_compute; repeat (first [left; reflexivity | right]) | left; reflexivity
              | cbn [sv_denot ew ewset Nat.eqb]; rewrite E10; unfold w64; rewrite unsigned_lit_small by lia;
                rewrite Z.add_0_r; reflexivity
              | cbn; lia | cbn; lia ]);
        lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K2 =>
          pose proof (vk_key_after CTX CTX0 CW E P x k nm (ms_regs ms2) (ms_mem ms2) MD K2 HEN HK Hraw Vx HRk
                        (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)) as HKY;
          pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
          exists (vk_move P (ms_regs ms2) (ms_mem ms2) MD K2 (ip_p P)), x, k, nm end
      end.
      split; [reflexivity|]. split; [reflexivity|]. right. split; [unfold vrd_cfg; vk_proj; reflexivity|].
      split; [exact HKY|]. vk_proj. split; [exact R13e|]. split; [exact R10k|]. split; [exact R12s|]. left. exact Hpe.
    + (* row 174 not taken: p < end: rows 175, to the second white-space loop's top *)
      assert (Hpl : ip_p P < ie_text E + ie_len E).
      { match goal with Hb : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = false |- _ =>
          rewrite branch_geu_U, (U_SOff E' 32 0), (U_SOff E' 33 0) in Hb; cbn [ew ewset Nat.eqb] in Hb;
          rewrite E32, E33 in Hb; unfold w64 in Hb; rewrite !unsigned_lit_small in Hb by lia;
          rewrite !Z.add_0_r, !zcanon_id in Hb by (unfold M64; lia);
          apply Bool.negb_false_iff, Z.ltb_lt in Hb; lia end. }
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_W2_SLOT); [vk_awrK E36u Htmp|].
      lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
        assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 (ip_keys P);
                                                       w64 (ip_n P); w64 (ip_keys P + 8 * ip_n P)]) E2)
          by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros j Hj; cbn [ew ewset];
              repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
        assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
          by (eapply (vk_regs_afterK _ _ _ _ _ _ _ HSe HA2);
              [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
              | vm_compute; reflexivity | rewrite R23; reflexivity | rewrite R27; reflexivity
              | rewrite R22; reflexivity | rewrite R18; reflexivity]);
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 13%bv HSe) as R13e;
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HSe) as R11e;
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 14%bv HSe) as R14e;
        cbn [ms_regs restrict] in R13e, R11e, R14e;
        (lazymatch type of R13e with _ = sv_denot _ (sr_get ?l _) =>
           let v := eval vm_compute in (sr_get l 13%bv) in change (sr_get l 13%bv) with v in R13e;
           let v1 := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v1 in R11e;
           let v4 := eval vm_compute in (sr_get l 14%bv) in change (sr_get l 14%bv) with v4 in R14e end);
        cbn [sv_denot] in R13e, R11e, R14e; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R13e, R11e, R14e;
        cbn [ew ewset Nat.eqb] in R13e, R11e, R14e; rewrite E33 in R13e; rewrite E32 in R11e, R14e;
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HSe) as R10k;
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 12%bv HSe) as R12k;
        cbn [ms_regs restrict] in R10k, R12k;
        (lazymatch type of R10k with _ = sv_denot _ (sr_get ?l _) =>
           let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in R10k;
           let v2 := eval vm_compute in (sr_get l 12%bv) in change (sr_get l 12%bv) with v2 in R12k end);
        cbn [sv_denot] in R10k; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R10k;
        cbn [ew ewset Nat.eqb] in R10k; rewrite E36 in R10k;
        assert (R12s : getr (ms_regs ms2) 12 = w64 (shadow_addr (ip_keys P + 8 * ip_n P)))
          by (rewrite R12k; symmetry; apply bv_eq; unfold w64; rewrite Z_to_bv_unsigned;
              fold (U E2 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 36 0) (SLit 3)) (SOff 26 0)));
              rewrite (vk_U_slot_sh E2 (ip_keys P + 8 * ip_n P)
                         ltac:(cbn [ew ewset Nat.eqb]; exact E36) ltac:(cbn [ew ewset Nat.eqb]; exact E26) Hsl47);
              unfold shadow_addr;
              assert (0 <= (ip_keys P + 8 * ip_n P) / 8 < 2 ^ 44)
                by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
              unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
              rewrite Z.mod_small by (unfold SHADOW_OFF; lia); reflexivity);
        assert (Hraw : forall y : word, ~ (ip_keys P + 8 * ip_n P <= bv_unsigned y < ip_keys P + 8 * ip_n P + 8) ->
                  ms_mem ms2 y = ip_mem P y) by (vk_rawK (ip_keys P + 8 * ip_n P) E36u);
        assert (Vx : val_mem SEGS (mrestrict (w_H (ip_W P)) (ms_mem ms2)) (ip_keys P + 8 * ip_n P) 8 x)
          by (replace (ip_keys P + 8 * ip_n P) with (base_val E2 (Some 36%nat) + 0)
                by (cbn [base_val ew ewset Nat.eqb]; rewrite E36u; lia);
              refine (vk_val_of_st _ E2 ss2 ms2 (w_H (ip_W P)) (Some 36%nat) 0 8 0 8
                        [YP09.mkChunk 0 (CVal 8 (SOff 10 0))] 0 8%N (SOff 10 0) x HSe _ _ _ _ _);
              [ vm_compute; repeat (first [left; reflexivity | right]) | left; reflexivity
              | cbn [sv_denot ew ewset Nat.eqb]; rewrite E10; unfold w64; rewrite unsigned_lit_small by lia;
                rewrite Z.add_0_r; reflexivity
              | cbn; lia | cbn; lia ]);
        lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K2 =>
          pose proof (vk_key_after CTX CTX0 CW E P x k nm (ms_regs ms2) (ms_mem ms2) MD K2 HEN HK Hraw Vx HRk
                        (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)) as HKY;
          pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
          exists (vk_move P (ms_regs ms2) (ms_mem ms2) MD K2 (ip_p P)), x, k, nm end
      end.
      split; [reflexivity|]. split; [reflexivity|]. left. split; [unfold vrd_cfg; vk_proj; reflexivity|].
      split; [exact HKY|]. vk_proj.
      split; [exact R11e|]. split; [exact R14e|]. split; [exact R13e|]. split; [exact R10k|].
      split; [exact R12s | exact Hpl].
Qed.


(* ---- the P := True corollaries: the seven segment statements as they stood before the generic-P conversion
   (a Theorem Labs lane's 12:18Z ruling, condition (1)), but for the re-hiding move's conclusion SRr' SEGS RZ_cf, so no
   consumer moves for the conversion. The only statement whose premises
   moved for a TEXT reason is vk_call_step: parse_string's post is now the m-form (fpostWm; at the kit's cut the budgeted
   fpostWbm), which is a change of the
   CALLEE'S TEXT, not of the invariant; its corollary is still provable, because the extra memnorm implication is
   simply dropped here. The kit reader text (A2Step) adds the Section hypothesis HI_head to vk_call_step and the
   element count (ip_n, the loop's progress) to the generic forms' posts; each corollary drops the count. ---- *)
Lemma vk_true_laws : srr_inv_laws SEGS (fun _ => True).
Proof. split; intros; exact I. Qed.
Lemma vk_true_call : srr_inv_call SEGS (fun _ => True).
Proof. intros m m' _ _. exact I. Qed.

Lemma vk_arr : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ielem_a B ARx SK E P -> ie_o E = false ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IELEM_SLOT P)
    (fun W2 c2 => exists P' nm, W2 = ip_W P' /\ c2 = vrd_cfg A_ISLOT_SLOT P' /\ vrd_islot_a B ARx SK E P' nm).
Proof.
  intros CTX CTX0 CW E P HEN HI Ho.
  eapply SRr'_mono; [exact (vk_arr_P CTX CTX0 CW E P _ vk_true_laws HEN HI Ho I)|].
  intros W' c' _ ((P' & nm & HWe & Hc & _ & HS) & _). exists P', nm. exact (conj HWe (conj Hc HS)).
Qed.

Lemma vk_c0 : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ielem_a B ARx SK E P -> ie_o E = true ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IELEM_SLOT P)
    (fun W2 c2 => exists P', W2 = ip_W P' /\
       ((c2 = vrd_cfg VK_W1_SLOT P' /\ vk_w1 E P') \/ (c2 = vrd_cfg VK_C1_SLOT P' /\ vk_c1 E P'))).
Proof.
  intros CTX CTX0 CW E P HEN HI Ho.
  eapply SRr'_mono; [exact (vk_c0_P CTX CTX0 CW E P _ vk_true_laws HEN HI Ho I)|].
  intros W' c' _ ((P' & HWe & _ & HQ) & _). exists P'. exact (conj HWe HQ).
Qed.

Lemma vk_w1_step : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vk_w1 E P ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_W1_SLOT P) (vk_w1_post E P).
Proof.
  intros CTX CTX0 CW E P HEN HW1.
  eapply SRr'_mono; [exact (vk_w1_step_P CTX CTX0 CW E P _ vk_true_laws HEN HW1 I)|].
  intros W' c' _ (H & _). exact H.
Qed.

Lemma vk_w1_loop : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vk_w1 E P ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_W1_SLOT P)
    (fun W2 c2 => exists P', W2 = ip_W P' /\ c2 = vrd_cfg VK_C1_SLOT P' /\ vk_c1 E P').
Proof.
  intros CTX CTX0 CW E P HEN HW1.
  eapply SRr'_mono; [exact (vk_w1_loop_P CTX CTX0 CW E P _ vk_true_laws HEN HW1 I)|].
  intros W' c' _ ((P' & HWe & Hc & _ & HC) & _). exists P'. exact (conj HWe (conj Hc HC)).
Qed.

Lemma vk_c1_step : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vk_c1 E P ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_C1_SLOT P) (vk_c1_post E).
Proof.
  intros CTX CTX0 CW E P HEN HC1.
  eapply SRr'_mono; [exact (vk_c1_step_P CTX CTX0 CW E P _ vk_true_laws HEN HC1 I)|].
  intros W' c' _ ((P' & HWe & _ & HQ) & _). exists P'. exact (conj HWe HQ).
Qed.

Lemma vk_call_step : forall CTX CTX0 CW E P,
  (forall fxP : YK11.FPState, tparse_string_specX (fx := fxP) B ARx SK CTX0 CW) ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_call E P ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_CALL_SLOT P) (vk_ret_post E).
Proof.
  intros CTX CTX0 CW E P HPS HEN HC.
  eapply SRr'_mono; [exact (vk_call_step_P CTX CTX0 CW E P _ vk_true_laws vk_true_call HPS HEN HC I)|].
  intros W' c' _ ((P2 & HWe & Hc & _ & HQ) & _). exists P2. exact (conj HWe (conj Hc HQ)).
Qed.

Lemma vk_c2K_step : forall CTX CTX0 CW E P x k nm, vrd_ient_ok B ARx CTX CTX0 CW E -> vk_retK E P x k nm ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_RET_SLOT P) (vk_c2K_post E).
Proof.
  intros CTX CTX0 CW E P x k nm HEN HK.
  eapply SRr'_mono; [exact (vk_c2K_step_P CTX CTX0 CW E P x k nm _ vk_true_laws HEN HK I)|].
  intros W' c' _ ((P2 & x' & k' & nm' & HWe & _ & HQ) & _). exists P2, x', k', nm'. exact (conj HWe HQ).
Qed.


(* ---- 13. C2 on the REFUSED arm (res = 0): keys[n] := 0 (its two ASan gates), `beqz a1` taken to row 309, s2 := -1,
   the join at row 310: vrd_iexit_a E P' (-1). The slot store by VrdSlotStore.vk_slot_store_keep_core; the fd of the
   refused node by VrdIFd.vrd_inode_fd_core (no vrd_icur / vrd_imodel at a refused string). ---- *)
Definition vk_c2R_post (E : vrd_ient) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P2, W2 = ip_W P2 /\ c2 = vrd_cfg A_IEPI_SLOT P2 /\ vrd_iexit_a B ARx SK E P2 (-1).

Lemma vk_c2R_step_P : forall CTX CTX0 CW E P (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_retR E P ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_RET_SLOT P)
    (fun W2 c2 => vk_c2R_post E W2 c2 /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P Pm PLAW HEN HK HPM.
  pose proof HK as (HFR & HRG & HND & HJN & Hin & Hraq & Hled & HLM & HBB & Hlsum & HRL & HXF & HOC & HLV & HHX & HINJ &
    Hacc & Hjr & Hnc & Ho & R10 & Hinc & af & HFO & HFL).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ. pose proof HJN as (_ & HJrest).
  pose proof HJN as ((HAR & _) & _ & _ & _ & _ & HBM & _).
  pose proof HBM as (HnotE & _).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof HFR as (Hf0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F17 & _).
  pose proof HND as (Hhdr & Hnc0 & Hcap & Hc0 & Hlin & Hlen' & _ & _ & Hrav & _ & Hrakeys & _).
  pose proof Hhdr as (_ & _ & _ & _ & _ & (_ & Vkeys) & (_ & Vn) & _).
  pose proof HEN as (_ & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hqv & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsrc & _).
  pose proof Hsrc as (_ & Ht4 & Htl8 & _ & Hrat & _). rewrite Hlen in Htl8.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vk_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  destruct (vk_sp_frame CTX CTX0 CW E HEN) as [Hsp1 Hsp16].
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  assert (Bv56 : ie_v E + 56 <= alloc_ceiling) by (eapply vrd_node_low; eassumption).
  assert (Happv : in_app (ie_v E) 56) by (eapply vrd_node_app; eassumption).
  assert (Hin8 : In (ip_keys P, 8 * ip_cap P)
                   (kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
  { apply in_or_app. right. unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia|]. cbn. left. reflexivity. }
  assert (Hslrw : rd_rw SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ip_keys P + 8 * ip_n P) 8)
    by (exact (vk_slot_rw_core B ARx SK LAWS HW E P [] (ip_keys P) 8 HND Hled HJN Hin8 Hnc)).
  destruct (vk_slot_place B ARx SK LAWS HW CTX CTX0 CW E P _ (ip_keys P) 8 Hfr144 HEN HND Hled HJN Hin8 Hnc)
    as (Hpl1 & Hpl2 & Hplz & Hplsh & Hplv & Hplra).
  destruct (vss_blk E P _ (ip_keys P) 8 HND Hnc Hin8) as (_ & HlinK & HkD).
  assert (Hk4 : 4096 <= ip_keys P < alloc_ceiling)
    by (eapply (vk_D_low B ARx LAWS); [exact HAR | exact HBM | exact HkD | unfold pj_holdsR; cbn [fst snd]; lia]).
  assert (Hslv : ip_keys P + 8 * ip_n P + 8 <= ie_v E + 32 \/ ie_v E + 48 <= ip_keys P + 8 * ip_n P).
  { destruct (Z_lt_le_dec (ip_keys P + 8 * ip_n P) (ie_v E + 32)).
    - destruct (Z_lt_le_dec (ip_keys P + 8 * ip_n P + 8) (ie_v E + 33)); [lia|].
      exfalso. apply (Hplv (ie_v E + 32)); lia.
    - destruct (Z_lt_le_dec (ip_keys P + 8 * ip_n P) (ie_v E + 48)); [|lia].
      exfalso. apply (Hplv (ip_keys P + 8 * ip_n P)); lia. }
  assert (R2 : getr (ip_regs P) 2 = w64 (spZ (ip_regs P))) by (unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Vfr : val_mem SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (spZ (ip_regs P) + 32) 8 (ie_v E + 32))
    by (replace (spZ (ip_regs P) + 32) with (spZ (ie_regs E) - 112) by lia; exact F17).
  destruct (vk_seatK (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) (spZ (ip_regs P))
              (ie_v E) (ip_keys P) (ip_n P) VK_RET_SLOT G8 G26 G23 G27 R2 G20 G22 G18 Hq1 Hq2 Hq8
              ltac:(lia) ltac:(lia) ltac:(rewrite Hf0; exact Hsp16) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(destruct Hqv; [right | left]; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hslv
              Vp Ve ltac:(lia) ltac:(lia) Vfr Vkeys Vn Hslrw Hraq Hrav
              ltac:(intros y Hy; unfold in_app in Happv; unfold SHADOW_OFF, kLowShadowBeg in *; lia)
              Hplra ltac:(intros y Hy Hs; exact (Hplsh y ltac:(lia) ltac:(lia)))) as [HS SHOK].
  set (EK := vk_EK (ip_regs P) (ip_p P) (ie_text E + ie_len E) (ip_keys P) (ip_n P)) in *.
  assert (HEI : img_env VAL A_LIM EK) by (unfold EK, vk_EK; apply Eimg_env).
  assert (E36u : bv_unsigned (ew EK 36) = ip_keys P + 8 * ip_n P).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra (ip_regs P) _ 4).
    unfold w64. apply unsigned_lit_small. lia. }
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hled HlinK) as (HkK & HabK & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  destruct (req_size_pos (8 * ip_cap P + cf_head)) as [_ Hrq]; [lia|].
  assert (Htmp : forall a, ip_keys P + 8 * ip_n P <= a < ip_keys P + 8 * ip_n P + 8 ->
            in_tmp_block (ablocks B (ie_ly E) (ie_S E)) (ablocks B (ip_ly P) (ip_S P)) a).
  { intros a Ha. exists (ip_keys P - cf_head), (8 * ip_cap P + cf_head).
    split; [exact HabK|]. split; [exact (HnotE _ _ HkD)|]. lia. }
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EK j = getr (ip_regs P) r).
  { intros j Hj r Hr. unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ j r Hr). }
  assert (E10 : ew EK 10 = w64 0) by (rewrite (EL 10%nat ltac:(lia) 10%bv eq_refl); exact R10).
  assert (E32 : ew EK 32 = w64 (ip_p P)).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew EK 33 = w64 (ie_text E + ie_len E)).
  { unfold EK, vk_EK. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 1). }
  assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 (ip_keys P); w64 (ip_n P);
                                              w64 (ip_keys P + 8 * ip_n P)]) EK)
    by (split; [intros j Hj; unfold EK, vk_EK; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 22%bv HS) as R22. cbn [ms_regs restrict mkst] in R22.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 18%bv HS) as R18. cbn [ms_regs restrict mkst] in R18.
  change (sr_get (ss_regs (vk_ssK VK_RET_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
  change (sr_get (ss_regs (vk_ssK VK_RET_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
  change (sr_get (ss_regs (vk_ssK VK_RET_SLOT)) 22%bv) with (SOff 20 40) in R22.
  change (sr_get (ss_regs (vk_ssK VK_RET_SLOT)) 18%bv) with (vk_shv 40) in R18.
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [vk_awrK E36u Htmp|].
  psrr_branch_tok RUN BR HS SHOK vk_Bspan.
  - (* row 167 beqz taken (a1 = 0): row 309 s2 := -1, to the join at row 310 *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat A_IEPI_SLOT); [vk_awrK E36u Htmp|].
    lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
      assert (HA2 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 (ip_keys P);
                                                     w64 (ip_n P); w64 (ip_keys P + 8 * ip_n P)]) E2)
        by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros j Hj; cbn [ew ewset];
            repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity);
      assert (HRk : forall r, In r [2; 3; 4]%bv -> getr (ms_regs ms2) r = getr (ip_regs P) r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi E2 ss2 _ (ip_regs P) _ [2; 3; 4]%bv HSe HA2
                                       ltac:(vm_compute; reflexivity) r Hr) as Hk; cbn [ms_regs restrict] in Hk; exact Hk);
      pose proof (st_ok_pi_restrict_reg _ _ _ _ 18%bv HSe) as R18e;
      cbn [ms_regs restrict] in R18e;
      (lazymatch type of R18e with _ = sv_denot _ (sr_get ?l _) =>
         let v := eval vm_compute in (sr_get l 18%bv) in change (sr_get l 18%bv) with v in R18e end);
      assert (Hraw : forall y : word, ~ (ip_keys P + 8 * ip_n P <= bv_unsigned y < ip_keys P + 8 * ip_n P + 8) ->
                ms_mem ms2 y = ip_mem P y) by (vk_rawK (ip_keys P + 8 * ip_n P) E36u);
      lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K2 =>
        assert (HKm : forall y : word, ~ (ip_keys P + 8 * ip_n P <= bv_unsigned y < ip_keys P + 8 * ip_n P + 8) ->
                  mrestrict (w_H (ip_W P)) (ms_mem ms2) y = mrestrict (w_H (ip_W P)) (ip_mem P) y)
          by (intros y Hy; unfold mrestrict; rewrite (Hraw y Hy); reflexivity);
        assert (Hsp2 : spZ (ms_regs ms2) = spZ (ip_regs P))
          by (unfold spZ; rewrite (HRk 2%bv ltac:(cbn; tauto)); reflexivity);
        destruct (vk_slot_store_keep_core B ARx SK LAWS HW PST_IMG CTX CTX0 CW E P [] (ms_regs ms2) (ms_mem ms2) MD K2
                    (ip_keys P) 8 Hfr144 Hs0c HEN HFR HND HJN Hin Hraq Hled HLM Hin8 Hnc HKm Hsp2
                    (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ))
          as (F' & N' & J' & Pin' & Raq' & Led' & _ & KeepD);
        pose (Pe := vk_move P (ms_regs ms2) (ms_mem ms2) MD K2 (ip_p P));
        pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
        exists (vk_move P (ms_regs ms2) (ms_mem ms2) MD K2 (ip_p P))
      end
    end.
    split; [reflexivity|]. split; [unfold vrd_cfg; vk_proj; reflexivity|].
    unfold vrd_iexit_a. vk_proj.
    split; [exact F'|]. split; [exact J'|].
    split; [rewrite (HRk 3%bv ltac:(cbn; tauto)); exact G3|].
    split; [rewrite (HRk 4%bv ltac:(cbn; tauto)); exact G4|].
    split; [rewrite R18e; first [reflexivity | (apply bv_eq; vm_compute; reflexivity)]|].
    split; [right; reflexivity|]. split; [exact Led'|]. split; [exact HRL|]. split; [exact HXF|]. split; [exact HOC|].
    split; [exact HLM|]. split; [exact HBB|]. split; [exact Hlsum|].
    split; [|split; [exact HLV | split; [exact HHX | exact HINJ]]].
    destruct Hjr as (okr & Hjr). exists [], okr.
    split; [rewrite Hjr; reflexivity|].
    split; [intros H; discriminate H|].
    intros _. pose proof Pin' as (Vp' & Ve' & Vd' & Hrw' & _ & _ & _ & Hpp' & _).
    split; [|split].
    + exists (ip_p P), (Z.of_nat (ie_d E) + 1). split; [exact Hpp'|]. split; [lia|].
      exact (conj Vp' (conj Ve' (conj Vd' Hrw'))).
    + exact (vrd_inode_fd_core B ARx SK LAWS CTX CTX0 CW E _ HEN N' J' Pin' Led' HLM Hacc).
    + (* The kit's cut, the None arm's free order: the order list across the store keys[n] := 0 (vk_k1_slot), the refused
         node's order list at the exit (VrdIFd.vrd_inode_fo_core), and vk_retR's free list *)
      intros Hh n0 Hn0.
      pose proof HLM as (_ & _ & _ & HPL & _).
      assert (HNd : List.NoDup (ip_D P)).
      { pose proof Hled as (_ & HNL & _). pose proof HLM as (_ & _ & _ & HPLm & _).
        assert (HNL' : List.NoDup (map fst (ip_Lam P))) by (first [exact HNL | apply NoDup_ListNoDup; exact HNL]).
        apply (Permutation_map fst) in HPLm. pose proof (Permutation_NoDup HPLm HNL') as H. rewrite map_app in H.
        apply NoDup_app_remove_r in H. exact (NoDup_map_inv _ _ H). }
      destruct (vk_k1_slot E P Pe [] af eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                  ltac:(intros xx kk Hx; unfold prh_lin, Pe; vk_proj; apply (Permutation_in _ (Permutation_sym HPL));
                        apply in_or_app; left; exact Hx)
                  HNd Hnc Ho
                  ltac:(unfold Pe; vk_proj; exact KeepD)
                  ltac:(unfold Pe; vk_proj; apply (vk_keep_rd _ (ip_mem P) _ (ip_keys P + 8 * ip_n P)
                                          (ip_keys P + 8 * ip_n P + 8) _ HKm); intros a Ha; lia)
                  HND Hinc HFO) as (_ & HFOe).
      assert (Hdlt : (ie_d E < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
      destruct n0 as [|nn]; [lia|].
      assert (Hdep : Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) (ip_acc P))
        by (apply (vi_dep_le (ip_acc P) (PjGrammar.MAXD - S (ie_d E)) nn); [lia | exact Hacc]).
      destruct (vrd_inode_fo_core B ARx SK LAWS CTX CTX0 CW E Pe af nn
                  HEN N' J' Led' HLM HFOe Hh Hdep) as (Fo & HFo & HFom).
      exists Fo. split; [exact HFo|]. rewrite HFom, HFL. reflexivity.
  - (* row 167 beqz not taken: a1 = 0, refuted *)
    exfalso. match goal with Hb : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = false |- _ =>
      rewrite branch_eq_U, (U_SOff E' 10 0), (U_lit E' 0) in Hb by lia; cbn [ew ewset Nat.eqb] in Hb;
      rewrite E10 in Hb; unfold w64 in Hb; rewrite unsigned_lit_small in Hb by lia;
      rewrite Z.add_0_r in Hb; cbn in Hb; discriminate Hb end.
Qed.

Lemma vk_c2R_step : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vk_retR E P ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_RET_SLOT P) (vk_c2R_post E).
Proof.
  intros CTX CTX0 CW E P HEN HR.
  eapply SRr'_mono; [exact (vk_c2R_step_P CTX CTX0 CW E P _ vk_true_laws HEN HR I)|].
  intros W' c' _ (H & _). exact H.
Qed.

Ltac vk_leaveK CTX CTX0 CW E P x k nm HEN HH E8u E32 E33 HA R23 R27 HJ HPM p' Hpd :=
  lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
    let HKr := fresh "HKr" in let Vq := fresh "Vq" in let Wq := fresh "Wq" in let HA2 := fresh "HA2" in
    let HRk := fresh "HRk" in let R13e := fresh "R13e" in let HHo := fresh "HH'" in
    let R10x := fresh "R10x" in let R12x := fresh "R12x" in
    assert (HKr : forall xx : word, ~ (ie_q E <= bv_unsigned xx < ie_q E + 8) -> ms_mem ms2 xx = ip_mem P xx)
      by (intros xx Hxx;
          repeat match goal with HF : frame_of _ _ ?m ?m' |- ?m' xx = _ =>
            rewrite (vk_frame_cur _ _ _ (ie_q E) _ _ HF ltac:(cbn [ew ewset Nat.eqb]; exact E8u) xx Hxx) end;
          reflexivity);
    let rs := eval vm_compute in (ss_mem ss2) in
    lazymatch rs with (YP09.mkRegion (Some 8%nat) 0 24 0 8 ?cs) :: _ =>
    lazymatch cs with (YP09.mkChunk 0 (CVal 8 ?e0)) :: _ =>
      destruct (vk_end_cur _ _ E2 ss2 ms2 cs e0 (ie_q E) p' HSe
                  ltac:(change (ss_mem ss2) with rs; left; reflexivity) ltac:(left; reflexivity)
                  ltac:(cbn [ew ewset Nat.eqb]; exact E8u)
                  ltac:(rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E32; unfold w64;
                        rewrite unsigned_lit_small by lia; rewrite ?Z.add_0_r; apply zcanon_id; unfold M64; lia))
        as [Vq Wq]
    end end;
    lazymatch type of HA with env_agree _ ?RX _ =>
    assert (HA2 : env_agree 32 RX E2)
      by (eapply env_agree_trans; [exact HA | split; [|reflexivity]]; intros kk Hkk; cbn [ew ewset];
          repeat match goal with |- context [Nat.eqb ?a ?c] => destruct (Nat.eqb_spec a c); [lia|] end; reflexivity)
    end;
    assert (HRk : forall r, In r vk_live -> getr (ms_regs ms2) r = getr (ip_regs P) r)
      by (eapply (vk_regs_after _ _ _ _ _ _ _ HSe HA2);
          [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
          | rewrite R23; reflexivity | rewrite R27; reflexivity]);
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 13%bv HSe) as R13e;
    cbn [ms_regs restrict] in R13e;
    (lazymatch type of R13e with _ = sv_denot _ (sr_get ?l _) =>
       let v := eval vm_compute in (sr_get l 13%bv) in change (sr_get l 13%bv) with v in R13e end);
    cbn [sv_denot] in R13e; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R13e;
    cbn [ew ewset Nat.eqb] in R13e; rewrite E33 in R13e;
    (* a0 / a2 (the key slot and its shadow address): no row of the loop writes them, so they are the seat's *)
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HSe) as R10x;
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 12%bv HSe) as R12x;
    cbn [ms_regs restrict] in R10x, R12x;
    (lazymatch type of R10x with _ = sv_denot _ (sr_get ?l _) =>
       let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in R10x;
       let v2 := eval vm_compute in (sr_get l 12%bv) in change (sr_get l 12%bv) with v2 in R12x end);
    cbn [sv_denot] in R10x, R12x; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R10x, R12x;
    cbn [ew ewset Nat.eqb] in R10x, R12x;
    cbn [restrict ms_mem] in Vq, Wq;
    lazymatch type of HJ with ajournal_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?MD ?K =>
      pose proof (vk_unseatK CTX CTX0 CW E P x k nm (ms_regs ms2) (ms_mem ms2) MD K p' HEN HH HRk HKr
                    Vq Wq (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HH))))) HJ)
                    Hpd) as HHo;
      pmkst HSe; apply SRr'_ret; split; [|first [exact HPM | (cbn [cfg_ms ms_mem mkst]; exact HPM)]];
      exists (vk_move P (ms_regs ms2) (ms_mem ms2) MD K p')
    end
  end.


(* ---- 14. W2, rows 176..194: the second white-space loop, the W1 shape with a1 / a3 / a4 and the key carried ---- *)
Definition vk_w2_post (E : vrd_ient) (P : vrd_ipos) (x k : Z) (nm : list Z) (W2 : world SEGS) (c2 : config) : Prop :=
  exists P', W2 = ip_W P' /\ ip_n P' = ip_n P /\
    ((c2 = vrd_cfg VK_C3_SLOT P' /\ vk_c3 E P' x k nm) \/
     (c2 = vrd_cfg VK_W2_SLOT P' /\ vk_w2 E P' x k nm /\ ip_p P' = ip_p P + 1)).

Lemma vk_w2_step_P : forall CTX CTX0 CW E P x k nm (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_w2 E P x k nm ->
  Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_W2_SLOT P)
    (fun W2 c2 => vk_w2_post E P x k nm W2 c2 /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P x k nm Pm PLAW HEN HW2 HPM.
  pose proof HW2 as (HKY & R10 & R12 & R11 & RA0 & RA2 & Hpe).
  pose proof HKY as (HFR & HRG & HND & HCU & HJN & HMD & Hnc & Ho & Vx & Hcs & Hvis & Hx4 & Hx16 & Hz).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ. pose proof HJN as (_ & HJrest).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & Hsrc & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hga & Hdisj & Hd).
  pose proof Hsrc as (_ & Ht4 & Htl8 & _ & Hrat & _).
  rewrite Hlen in Htl8.
  pose proof asan_consts as (C1 & _).
  destruct (vk_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  set (j := Z.to_nat (ip_p P - ie_text E)).
  assert (Hj : (j < length (ie_tb E))%nat) by (unfold j; lia).
  set (b := nth j (ie_tb E) 0).
  destruct (Hga j Hj) as [Vb Hb]. fold b in Vb, Hb.
  replace (ie_text E + Z.of_nat j) with (ip_p P) in Vb by (unfold j; lia).
  destruct (vk_seatWg 11%bv 13%bv 14%bv (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) b VK_W2_SLOT
     eq_refl eq_refl eq_refl G8 G26 G23 G27 R10 R11 R12 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Vb Hb ltac:(lia) Hrw Hraq) as [HS SHOK].
  set (EW := vk_EW (ip_regs P) (ip_p P) (ie_text E + ie_len E) b) in *.
  assert (HEI : img_env VAL A_LIM EW) by (unfold EW, vk_EW; apply Eimg_env).
  assert (EL : forall kk, (kk < 32)%nat -> forall r : bv 5, Z.of_nat kk = bv_unsigned r -> ew EW kk = getr (ip_regs P) r).
  { intros kk Hkk r Hr. unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ kk r Hr). }
  (* a0 / a2, the key slot and its shadow address, at the seat (the loop never writes them) *)
  assert (EA0 : ew EW 10 = w64 (ip_keys P + 8 * ip_n P)) by (rewrite (EL 10%nat ltac:(lia) 10%bv eq_refl); exact RA0).
  assert (EA2 : ew EW 12 = w64 (shadow_addr (ip_keys P + 8 * ip_n P)))
    by (rewrite (EL 12%nat ltac:(lia) 12%bv eq_refl); exact RA2).
  assert (E8 : ew EW 8 = w64 (ie_q E)) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact G8).
  assert (E8u : bv_unsigned (ew EW 8) = ie_q E) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (E21 : ew EW 21 = w64 32) by (rewrite (EL 21%nat ltac:(lia) 21%bv eq_refl); exact G21).
  assert (E25 : ew EW 25 = w64 4294977024) by (rewrite (EL 25%nat ltac:(lia) 25%bv eq_refl); exact G25).
  assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact G26).
  assert (E32 : ew EW 32 = w64 (ip_p P)).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew EW 33 = w64 (ie_text E + ie_len E)).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 1). }
  assert (E34 : ew EW 34 = w64 b).
  { unfold EW, vk_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 2). }
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF) by (apply (U_atom EW 26 SHADOW_OFF E26); unfold SHADOW_OFF; lia).
  assert (U32 : U EW (SOff 32 0) = ip_p P) by (apply (U_atom EW 32 (ip_p P) E32); lia).
  assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) EW)
    by (split; [intros kk Hkk; unfold EW, vk_EW; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  change (sr_get (ss_regs (vk_ssWg 11%bv 13%bv 14%bv VK_W2_SLOT)) 23%bv) with (vk_sh_of 8) in R23.
  change (sr_get (ss_regs (vk_ssWg 11%bv 13%bv 14%bv VK_W2_SLOT)) 27%bv) with (vk_sh_of 0) in R27.
  assert (HSTK : 0 <= STK_parse_items (ie_d E)).
  { destruct HEN as ((HAF & _) & _). destruct HAF as (_ & _ & _ & _ & _ & Hstk & _). exact (proj1 (proj2 Hstk)). }
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [ vk_ra_byte Hrat UB U32 | vk_awr E8u HSTK | ].
  match goal with H : frame_of _ _ (ip_mem P) _ |- _ => rename H into HF1 end.
  psrr_branch_tok RUN BR HS SHOK vk_Bspan.
  - (* row 181 taken: 32 < b, so b is not white space: on to row 195 with p *)
    match goal with Hb1 : branch_taken _ (sv_denot ?E' _) _ = true |- _ =>
      assert (Hgt : 32 < b);
      [ assert (F21 : ew E' 21 = Z_to_bv 64 32) by (cbn [ew ewset Nat.eqb]; exact E21);
        assert (F34 : ew E' 34 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E34);
        rewrite branch_ltu_U, (U_atom E' 21 32 F21), (U_atom E' 34 b F34) in Hb1 by lia;
        apply Z.ltb_lt in Hb1; exact Hb1 | ] end.
    assert (Hnws : PjGrammar.ws b = false)
      by (unfold PjGrammar.ws; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_C3_SLOT); [vk_awr E8u HSTK|].
    assert (Hpd : ip_p P = ip_p P \/ (ip_p P = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\ exists b0, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b0 /\ PjGrammar.ws b0 = true)) by (left; reflexivity).
    vk_leaveK CTX CTX0 CW E P x k nm HEN HKY E8u E32 E33 HA R23 R27 HJ HPM (ip_p P) Hpd.
    split; [reflexivity|]. split; [reflexivity|]. left. split; [unfold vrd_cfg; vk_proj; reflexivity|].
    split; [exact HH'|]. split; [exact R13e|]. split; [exact (eq_trans R10x EA0)|]. split; [exact (eq_trans R12x EA2)|].
    right. vk_proj. split; [lia|]. exists b.
    split; [unfold b; apply nth_error_nth'; exact Hj | exact Hnws].
  - (* row 181 not taken: b <= 32 *)
    match goal with Hb1 : branch_taken _ (sv_denot ?E' _) _ = false |- _ =>
      assert (Hle : b <= 32);
      [ assert (F21 : ew E' 21 = Z_to_bv 64 32) by (cbn [ew ewset Nat.eqb]; exact E21);
        assert (F34 : ew E' 34 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E34);
        rewrite branch_ltu_U, (U_atom E' 21 32 F21), (U_atom E' 34 b F34) in Hb1 by lia;
        apply Z.ltb_ge in Hb1; exact Hb1 | ] end.
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [vk_awr E8u HSTK|].
    psrr_branch_tok RUN BR HS SHOK vk_Bspan.
    + (* row 184 taken: the mask bit is 0, so b is not white space: on to row 195 with p *)
      match goal with Hb2 : branch_taken _ (sv_denot ?E' _) _ = true |- _ =>
        assert (Hnws : PjGrammar.ws b = false);
        [ assert (F25 : ew E' 25 = Z_to_bv 64 VrdPro.vrd_ws_mask) by (cbn [ew ewset Nat.eqb]; exact E25);
          assert (F34 : ew E' 34 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E34);
          rewrite branch_eq_U, (vk_mask_U E' b F25 F34 ltac:(lia)), (U_lit E' 0) in Hb2 by lia;
          destruct (PjGrammar.ws b); [discriminate Hb2 | reflexivity] | ] end.
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_C3_SLOT); [vk_awr E8u HSTK|].
      assert (Hpd : ip_p P = ip_p P \/ (ip_p P = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\ exists b0, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b0 /\ PjGrammar.ws b0 = true)) by (left; reflexivity).
      vk_leaveK CTX CTX0 CW E P x k nm HEN HKY E8u E32 E33 HA R23 R27 HJ HPM (ip_p P) Hpd.
      split; [reflexivity|]. split; [reflexivity|]. left. split; [unfold vrd_cfg; vk_proj; reflexivity|].
      split; [exact HH'|]. split; [exact R13e|]. split; [exact (eq_trans R10x EA0)|].
      split; [exact (eq_trans R12x EA2)|]. right. vk_proj. split; [lia|]. exists b.
      split; [unfold b; apply nth_error_nth'; exact Hj | exact Hnws].
    + (* row 184 not taken: b is white space; rows 185..190 store q->p := p + 1 and compare it with end *)
      match goal with Hb2 : branch_taken _ (sv_denot ?E' _) _ = false |- _ =>
        assert (Hws : PjGrammar.ws b = true);
        [ assert (F25 : ew E' 25 = Z_to_bv 64 VrdPro.vrd_ws_mask) by (cbn [ew ewset Nat.eqb]; exact E25);
          assert (F34 : ew E' 34 = Z_to_bv 64 b) by (cbn [ew ewset Nat.eqb]; exact E34);
          rewrite branch_eq_U, (vk_mask_U E' b F25 F34 ltac:(lia)), (U_lit E' 0) in Hb2 by lia;
          destruct (PjGrammar.ws b); [reflexivity | discriminate Hb2] | ] end.
      assert (Hnth : nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b)
        by (unfold b; apply nth_error_nth'; exact Hj).
      paj_run_tok_x_inv RUN HS HJ SHOK HPM vk_Bspan; [vk_awr E8u HSTK|].
      match goal with Hb3 : branch_taken _ (sv_denot ?E' _) (sv_denot ?E' _) = _ |- _ => idtac end.
      psrr_branch_tok RUN BR HS SHOK vk_Bspan.
      * (* row 190 taken: p + 1 <> end: back to row 176 with p + 1 *)
        match goal with Hb3 : branch_taken _ (sv_denot ?E' _) _ = true |- _ =>
          assert (Hne : ip_p P + 1 <> ie_text E + ie_len E);
          [ rewrite branch_ne_U in Hb3;
            rewrite (U_SOff E' 32 1), (U_SOff E' 33 0) in Hb3; cbn [ew ewset Nat.eqb] in Hb3;
            rewrite E32, E33 in Hb3; unfold w64 in Hb3; rewrite !unsigned_lit_small in Hb3 by lia;
            rewrite !zcanon_id in Hb3 by (unfold M64; lia); rewrite Z.add_0_r in Hb3;
            apply Bool.negb_true_iff, Z.eqb_neq in Hb3; exact Hb3 | ] end.
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_W2_SLOT); [vk_awr E8u HSTK|].
        lazymatch goal with HSe : st_ok_pi _ _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
          assert (D32 : sv_denot E2 (SOff 32 1) = Z_to_bv 64 (ip_p P + 1));
          [ rewrite <- (Z_to_bv_bv_unsigned _ (sv_denot E2 (SOff 32 1))); f_equal;
            change (bv_unsigned (sv_denot E2 (SOff 32 1))) with (U E2 (SOff 32 1));
            rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia;
            apply zcanon_id; unfold M64; lia |];
          pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HSe) as R10e;
          pose proof (st_ok_pi_restrict_reg _ _ _ _ 14%bv HSe) as R12e;
          cbn [ms_regs restrict] in R10e, R12e;
          (lazymatch type of R10e with _ = sv_denot _ (sr_get ?l _) =>
             let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in R10e;
             let v := eval vm_compute in (sr_get l 14%bv) in change (sr_get l 14%bv) with v in R12e end);
          rewrite D32 in R10e, R12e
        end.
        assert (Hpd : ip_p P + 1 = ip_p P \/ (ip_p P + 1 = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\ exists b0, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b0 /\ PjGrammar.ws b0 = true))
          by (right; split; [reflexivity | split; [exact Hpe | exists b; split; [exact Hnth | exact Hws]]]).
        vk_leaveK CTX CTX0 CW E P x k nm HEN HKY E8u E32 E33 HA R23 R27 HJ HPM (ip_p P + 1) Hpd.
        split; [reflexivity|]. split; [reflexivity|]. right. split; [unfold vrd_cfg; vk_proj; reflexivity|].
        split; [|vk_proj; reflexivity].
        split; [exact HH'|]. vk_proj. split; [exact R10e|]. split; [exact R12e|]. split; [exact R13e|].
        split; [exact (eq_trans R10x EA0)|]. split; [exact (eq_trans R12x EA2)|]. lia.
      * (* row 190 not taken: p + 1 = end: row 191 jumps to row 195 *)
        match goal with Hb3 : branch_taken _ (sv_denot ?E' _) _ = false |- _ =>
          assert (Heq : ip_p P + 1 = ie_text E + ie_len E);
          [ rewrite branch_ne_U in Hb3;
            rewrite (U_SOff E' 32 1), (U_SOff E' 33 0) in Hb3; cbn [ew ewset Nat.eqb] in Hb3;
            rewrite E32, E33 in Hb3; unfold w64 in Hb3; rewrite !unsigned_lit_small in Hb3 by lia;
            rewrite !zcanon_id in Hb3 by (unfold M64; lia); rewrite Z.add_0_r in Hb3;
            apply Bool.negb_false_iff, Z.eqb_eq in Hb3; exact Hb3 | ] end.
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vk_Bspan (4 * Z.of_nat VK_C3_SLOT); [vk_awr E8u HSTK|].
        assert (Hpd : ip_p P + 1 = ip_p P \/ (ip_p P + 1 = ip_p P + 1 /\ ip_p P < ie_text E + ie_len E /\ exists b0, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b0 /\ PjGrammar.ws b0 = true))
          by (right; split; [reflexivity | split; [exact Hpe | exists b; split; [exact Hnth | exact Hws]]]).
        vk_leaveK CTX CTX0 CW E P x k nm HEN HKY E8u E32 E33 HA R23 R27 HJ HPM (ip_p P + 1) Hpd.
        split; [reflexivity|]. split; [reflexivity|]. left. split; [unfold vrd_cfg; vk_proj; reflexivity|].
        split; [exact HH'|]. split; [exact R13e|]. split; [exact (eq_trans R10x EA0)|].
        split; [exact (eq_trans R12x EA2)|]. left. vk_proj. exact Heq.
Qed.

(* the second white-space loop, rows 176..194, by the loop rule with measure end - p *)
Lemma vk_w2_loop_P : forall CTX CTX0 CW E P x k nm (Pm : (word -> option byte) -> Prop), srr_inv_laws SEGS Pm ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_w2 E P x k nm -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_W2_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg VK_C3_SLOT P' /\ ip_n P' = ip_n P /\ vk_c3 E P' x k nm)
                  /\ Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P x k nm Pm PLAW HEN HW2 HPM.
  apply (SRr'_loopZ SEGS YGcfRehidePost.RZ_cf vrd_ipos (fun z => ie_text E + ie_len E - ip_p z)
           (fun z W c => W = ip_W z /\ c = vrd_cfg VK_W2_SLOT z /\ vk_w2 E z x k nm /\ Pm (ip_mem z) /\ ip_n z = ip_n P)
           (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg VK_C3_SLOT P' /\ ip_n P' = ip_n P /\ vk_c3 E P' x k nm)
                         /\ Pm (ms_mem (cfg_ms c2))))
    with (x := P); [|auto].
  intros z W c (-> & -> & Hz & HPz & Hnz).
  eapply SRr'_mono; [exact (vk_w2_step_P CTX CTX0 CW E z x k nm Pm PLAW HEN Hz HPz)|].
  intros W' c' _ ((P' & -> & Hn' & [(-> & HC) | (-> & HW' & Hp)]) & HPc).
  - left. split; [exists P'; split; [reflexivity|]; split; [reflexivity|]; split; [congruence | exact HC] | exact HPc].
  - right. exists P'. split.
    + destruct HW' as (_ & _ & _ & _ & _ & _ & Hlt). destruct Hz as (_ & _ & _ & _ & _ & _ & Hlt0). lia.
    + split; [reflexivity|]. split; [reflexivity|]. split; [exact HW'|].
      cbn [vrd_cfg cfg_ms ms_mem] in HPc. split; [exact HPc | congruence].
Qed.

Lemma vk_w2_loop : forall CTX CTX0 CW E P x k nm, vrd_ient_ok B ARx CTX CTX0 CW E -> vk_w2 E P x k nm ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg VK_W2_SLOT P)
    (fun W2 c2 => exists P', W2 = ip_W P' /\ c2 = vrd_cfg VK_C3_SLOT P' /\ vk_c3 E P' x k nm).
Proof.
  intros CTX CTX0 CW E P x k nm HEN HW2.
  eapply SRr'_mono; [exact (vk_w2_loop_P CTX CTX0 CW E P x k nm _ vk_true_laws HEN HW2 I)|].
  intros W' c' _ ((P' & HWe & Hc & _ & HC) & _). exists P'. exact (conj HWe (conj Hc HC)).
Qed.

(* ---- CHECK 1 OF VERIFY 21:4xZ for the changed shared texts vk_w2 / vk_c3 (the a0 / a2 conjuncts of 1c1be792c3b4,
   which A2KeyB's VrdIKeyB.v consumes): the two register conjuncts make neither text vacuous. Any position that
   satisfies the text as it stood before the change (the interface c9912d86b33f: the premises below) gives, with a0 / a2
   set to the key slot and its shadow address and NOTHING else changed, a position of the new text - no other conjunct
   reads a0 or a2 (vk_live omits them; vk_unseatK moves vk_key). ---- *)
Definition vk_regs_slot (P : vrd_ipos) : bvmap 5 word :=
  regupd (regupd (ip_regs P) 10%bv (w64 (ip_keys P + 8 * ip_n P))) 12%bv
    (w64 (shadow_addr (ip_keys P + 8 * ip_n P))).

Ltac vk_bvne := let H := fresh "H" in intros H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.

Lemma vk_regs_slot_get : forall P,
  (forall r, In r vk_live -> getr (vk_regs_slot P) r = getr (ip_regs P) r) /\
  getr (vk_regs_slot P) 11 = getr (ip_regs P) 11 /\ getr (vk_regs_slot P) 13 = getr (ip_regs P) 13 /\
  getr (vk_regs_slot P) 14 = getr (ip_regs P) 14 /\
  getr (vk_regs_slot P) 10 = w64 (ip_keys P + 8 * ip_n P) /\
  getr (vk_regs_slot P) 12 = w64 (shadow_addr (ip_keys P + 8 * ip_n P)).
Proof.
  intros P. unfold vk_regs_slot.
  split; [|split; [|split; [|split; [|split]]]].
  - intros r Hr. unfold vk_live in Hr.
    repeat (destruct Hr as [<- | Hr]; [rewrite !getr_other by vk_bvne; reflexivity |]). destruct Hr.
  - rewrite !getr_other by vk_bvne. reflexivity.
  - rewrite !getr_other by vk_bvne. reflexivity.
  - rewrite !getr_other by vk_bvne. reflexivity.
  - rewrite getr_other by vk_bvne. rewrite getr_same by vk_bvne. reflexivity.
  - rewrite getr_same by vk_bvne. reflexivity.
Qed.

Lemma vk_key_regs_slot : forall CTX CTX0 CW E P x k nm,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_key E P x k nm ->
  vk_key E (vk_move P (vk_regs_slot P) (ip_mem P) (ip_md P) (ip_k P) (ip_p P)) x k nm.
Proof.
  intros CTX CTX0 CW E P x k nm HEN HKY.
  pose proof HKY as (_ & _ & _ & HCU & HJN & _).
  pose proof HCU as (Hin & _).
  pose proof Hin as (Vp & _ & _ & Hrw & _).
  pose proof HJN as (HJ & _).
  exact (vk_unseatK CTX CTX0 CW E P x k nm (vk_regs_slot P) (ip_mem P) (ip_md P) (ip_k P) (ip_p P) HEN HKY
           (proj1 (vk_regs_slot_get P)) (fun _ _ => eq_refl) Vp (fun a Ha => Hrw a ltac:(lia)) HJ (or_introl eq_refl)).
Qed.

Lemma vk_w2_sat : forall CTX CTX0 CW E P x k nm,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_key E P x k nm ->
  getr (ip_regs P) 11 = w64 (ip_p P) -> getr (ip_regs P) 14 = w64 (ip_p P) ->
  getr (ip_regs P) 13 = w64 (ie_text E + ie_len E) -> ip_p P < ie_text E + ie_len E ->
  vk_w2 E (vk_move P (vk_regs_slot P) (ip_mem P) (ip_md P) (ip_k P) (ip_p P)) x k nm.
Proof.
  intros CTX CTX0 CW E P x k nm HEN HKY R11 R14 R13 Hpe.
  pose proof (vk_regs_slot_get P) as (_ & G11 & G13 & G14 & G10 & G12).
  split; [exact (vk_key_regs_slot CTX CTX0 CW E P x k nm HEN HKY)|].
  vk_proj. rewrite G11, G14, G13. exact (conj R11 (conj R14 (conj R13 (conj G10 (conj G12 Hpe))))).
Qed.

Lemma vk_c3_sat : forall CTX CTX0 CW E P x k nm,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vk_key E P x k nm ->
  getr (ip_regs P) 13 = w64 (ie_text E + ie_len E) ->
  (ip_p P = ie_text E + ie_len E \/
   (ip_p P < ie_text E + ie_len E /\ exists b, nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some b /\
      PjGrammar.ws b = false)) ->
  vk_c3 E (vk_move P (vk_regs_slot P) (ip_mem P) (ip_md P) (ip_k P) (ip_p P)) x k nm.
Proof.
  intros CTX CTX0 CW E P x k nm HEN HKY R13 Hp.
  pose proof (vk_regs_slot_get P) as (_ & _ & G13 & _ & G10 & G12).
  split; [exact (vk_key_regs_slot CTX CTX0 CW E P x k nm HEN HKY)|].
  vk_proj. rewrite G13. exact (conj R13 (conj G10 (conj G12 Hp))).
Qed.

End K.
