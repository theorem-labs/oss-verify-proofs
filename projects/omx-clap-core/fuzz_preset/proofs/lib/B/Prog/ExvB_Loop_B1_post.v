(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rests on memnorm only as EXB's exv_rm keep, carried across the runs (YC1fPx.v _inv runners, ExvB_Loop_exw.v's
   exvl_P) into KIT_RUNs (old-pin kit 4f18c75d4900); not on tex_word_specX. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan), ex_value, segment CL, piece B1 (the item): the part AFTER
   the nested call, from its return site B 0x83c98 (exv_pc 0x76c) to the cut LS (B 0x83ca0, exv_pc 0x774) or to the exit
   CX (B 0x83fa8, exv_pc 0xa7c). ExvB_Loop_B1.v makes the call and closes the piece with these two lemmas.
   THE CODE (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, rows 477-478,
   530-531): `li s5, -1`; `bnez a0, 0x83d6c`; at 0x83d6c `ld s8, 120(s1)` (the frame back in s8) and `j 0x83fa8`.
   No store, no UBSan check, no shadow check. THE RUN: one symbolic run of the listing engine (YC80x / YC1fPx over
   YCbqG's ajournal_x) from a state seated at the return site, a0 pinned to the callee's result (0: to LS; -1: to CX),
   the slot 120(s1) a read-only region holding the frame (atom 32); EXBs across it by KIT_RUNs (nothing is written),
   s8 back at the frame by KIT_EXB_OF_S.
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 0x76c, 0x774, 0xa7c (DERIVED: B 0x83c98 / 0x83ca0 / 0x83fa8 minus B's ex_value entry, the internal file neutral_dis.py);
   120, 128 (LENGTH: the frame-pointer spill slot of B's code, 120(s1), and its end); 8, 160, 40, 36 (LENGTH: a word,
   the end of the spill area 8 .. 152(s1) + 8, struct ex and its last field's end); 2, 3, 4, 8, 9, 10, 18, 19, 21, 22,
   23, 24, 25, 26, 27 (WORD: register numbers); 32 (DERIVED: the engine's first extra atom); 288, 304 (LENGTH: ex_value's
   frame and its 32-alignment slack); 2 ^ 47, 2 ^ 64 (LENGTH: address-space bounds); 0, -1 (WORD: the callee's
   results). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit ExvB_Loop_Stmt ExvB_Open_kt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_exw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the pcs, as byte offsets from the listing's base (DERIVED: B_prog_sigma AS_ex_value - B_prog_base + off) ---- *)
Definition EXB1_PC2 : Z := B_prog_sigma AS_ex_value - B_prog_base + 0x76c.
Definition EXB1_PC3 : Z := B_prog_sigma AS_ex_value - B_prog_base + 0x774.
Definition EXB1_PC4 : Z := B_prog_sigma AS_ex_value - B_prog_base + 0xa7c.

(* ---- the symbolic state at the return site: registers as atoms, a0 pinned to r, the slot 120(s1) read-only ---- *)
Definition exb1_Bx : sv := SLit 0.
Definition exb1_Bspan : Z * Z := (0, 0).
Definition exb1_SH : list shent := [].
Definition exb1_regions2 : smem :=
  [ YP09.mkRegion (Some 9%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32%nat 0))] ].
Definition ss_exb1_2 (r : Z) : sstate :=
  mkSS EXB1_PC2 (sr_set sr_atoms 10%bv (SLit r)) exb1_regions2 None (mkFacts [] [] []).
Section e. Context {rc : YM05.RunCeil}.
Definition exb1_E2 (regs : bvmap 5 word) (F : Z) : env := @Eimg _ B_prog_listing PI_prog_B (Ereg regs [w64 F]).

Lemma exb1_E_reg : forall regs extra (r : bv 5) n, Z.of_nat n = bv_unsigned r ->
  ew (@Eimg _ B_prog_listing PI_prog_B (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra r n Hn. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma exb1_E_x : forall regs w, ew (@Eimg _ B_prog_listing PI_prog_B (Ereg regs [w])) 32 = w.
Proof. intros regs w. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs [w] 0). Qed.
Lemma exb1_agree : forall regs extra, env_agree 32 (Ereg regs extra) (@Eimg _ B_prog_listing PI_prog_B (Ereg regs extra)).
Proof. intros regs extra. split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
End e.

(* the read-only region writes nothing: the run keeps every byte *)
Lemma exb1_fr_ro : forall {rc : YM05.RunCeil} E (H : word -> bool) (m m' : word -> option byte),
  frame_of E exb1_regions2 (mrestrict H m) (mrestrict H m') ->
  (forall a, aview rsegs H m' a = aview rsegs H m a) /\ (forall a, apresent H m a -> apresent H m' a).
Proof.
intros rc E H m m' HFr.
assert (HN : forall x, ~ in_wrange E exb1_regions2 x).
{ intros x (rg & Hin & Hr). destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia. }
split.
- intros a. apply aview_eq_of. apply HFr. apply HN.
- intros a (Hh & b & Hb). split; [exact Hh|]. exists b.
  pose proof (HFr (Z_to_bv 64 a) (HN _)) as E1. unfold mrestrict in E1. rewrite Hh in E1. rewrite E1. exact Hb.
Qed.

(* ---- bytes kept: a value, the cursor, the spills ---- *)
Section kp. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Lemma exb1_val_kept : forall (W W' : world rsegs) (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview rsegs (w_H W') m' x = aview rsegs (w_H W) m x) ->
  val_mem rsegs (rdW W m) a n v -> val_mem rsegs (rdW W' m') a n v.
Proof.
intros W W' m m' a n v HE Hv kk Hk.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W') m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|]. apply HE. lia.
Qed.
Lemma exb1_cur_kept : forall (W W' : world rsegs) (m m' : word -> option byte) q p e dep scr dl,
  (forall x, q <= x < q + 40 -> aview rsegs (w_H W') m' x = aview rsegs (w_H W) m x) ->
  prhex_cur W m q p e dep scr dl -> prhex_cur W' m' q p e dep scr dl.
Proof.
intros W W' m m' q p e dep scr dl HK (V1 & V2 & V3 & V4 & V5).
refine (conj (exb1_val_kept _ _ _ _ _ _ _ _ V1) (conj (exb1_val_kept _ _ _ _ _ _ _ _ V2)
  (conj (exb1_val_kept _ _ _ _ _ _ _ _ V3) (conj (exb1_val_kept _ _ _ _ _ _ _ _ V4)
  (exb1_val_kept _ _ _ _ _ _ _ _ V5))))); intros x Hx; apply HK; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia.
Qed.
Lemma exb1_spill_kept : forall E (W W' : world rsegs) (m m' : word -> option byte) o v,
  (forall x, exv_s1 E + 8 <= x < exv_s1 E + 160 -> aview rsegs (w_H W') m' x = aview rsegs (w_H W) m x) ->
  8 <= o <= 152 -> exv_spill E W m o v -> exv_spill E W' m' o v.
Proof.
intros E W W' m m' o v HK Ho H. unfold exv_spill in *. apply (exb1_val_kept W W' m m' _ 8 v); [|exact H].
intros x Hx. apply HK. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
Qed.
Lemma exb1_spills_kept : forall E (W W' : world rsegs) (m m' : word -> option byte) ly ly' pos c vv i,
  (forall x, exv_s1 E + 8 <= x < exv_s1 E + 160 -> aview rsegs (w_H W') m' x = aview rsegs (w_H W) m x) ->
  frame_addr ly' 1 pos = frame_addr ly 1 pos ->
  exv_spills E W m ly pos c vv i -> exv_spills E W' m' ly' pos c vv i.
Proof.
intros E W W' m m' ly ly' pos c vv i HK Hfa
  (S152 & S88 & S56 & S48 & S40 & S80 & S24 & S16 & S72 & S8 & S32 & S136 & S112 & S128 & S64 & S104 & S96 & S120 & S144).
unfold exv_spills. rewrite Hfa.
refine (conj (exb1_spill_kept E W W' m m' _ _ HK _ S152) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S88)
  (conj (exb1_spill_kept E W W' m m' _ _ HK _ S56) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S48)
  (conj (exb1_spill_kept E W W' m m' _ _ HK _ S40) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S80)
  (conj (exb1_spill_kept E W W' m m' _ _ HK _ S24) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S16)
  (conj (exb1_spill_kept E W W' m m' _ _ HK _ S72) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S8)
  (conj (exb1_spill_kept E W W' m m' _ _ HK _ S32) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S136)
  (conj (exb1_spill_kept E W W' m m' _ _ HK _ S112) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S128)
  (conj (exb1_spill_kept E W W' m m' _ _ HK _ S64) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S104)
  (conj (exb1_spill_kept E W W' m m' _ _ HK _ S96) (conj (exb1_spill_kept E W W' m m' _ _ HK _ S120)
  (exb1_spill_kept E W W' m m' _ _ HK _ S144)))))))))))))))))));
  lia.
Qed.
End kp.

(* ---- the geometry every state with EXB has: the entry sp, the frame base s1, the stack need ---- *)
Lemma exb1_stk_S : forall n, STK_ex_value (PI := prh_img_B) (S n) = STK_ex_value (PI := prh_img_B) n + 304.
Proof.
intros n. unfold STK_ex_value. change (@pi_frame prh_img_B F_ex_value) with 304. rewrite !Nat2Z.inj_succ. lia.
Qed.
Lemma exb1_stk_ge : forall n, 304 <= STK_ex_value (PI := prh_img_B) n.
Proof.
intros n. unfold STK_ex_value. change (@pi_frame prh_img_B F_ex_value) with 304.
assert (Hz : forall l, 0 <= zmaxl l) by (induction l as [|a l IH]; cbn [zmaxl fold_right]; [lia|]; unfold zmaxl in IH; lia).
pose proof (Hz [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]). lia.
Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Lemma exb1_geom : forall E lyc Sc Hpc (Wc : world rsegs) memc mdc k pos,
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc mdc k ->
  fwin (PA := PI_prog_B) (e_ly E) (e_W E) (e_regs E) (e_mem E) (e_d E) ->
  exv_sp E mod 16 = 0 /\ 0 <= e_d E /\ e_d E mod 16 = 0 /\ alloc_ceiling + exv_STK E <= exv_sp E /\
  exv_sp E + e_d E <= 2 ^ 47 /\ exv_sp E - 304 <= exv_s1 E <= exv_sp E - 288 /\ exv_s1 E mod 32 = 0 /\
  304 <= exv_STK E /\ ly_F lyc = ly_F (e_ly E) /\ ly_stk_hi lyc = ly_stk_hi (e_ly E) /\
  exv_sp E + e_d E <= ly_stk_hi (e_ly E).
Proof.
intros E lyc Sc Hpc Wc memc mdc k pos HJ (Hd0 & Hd16 & _ & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Jastk & _ & _).
destruct Jastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & _ & Ehi & _).
pose proof (exb1_stk_ge (e_n E)) as HS. unfold exv_STK in *.
pose proof (exv_s1_le E) as ((S1a & S1b) & S1m).
assert (Hsp : exv_sp E mod 16 = 0).
{ rewrite Zplus_mod in Hal. rewrite Hd16, Z.add_0_r, Z.mod_mod in Hal by lia. exact Hal. }
assert (Hs1 : exv_sp E - 304 <= exv_s1 E).
{ unfold exv_s1. rewrite exv_land32. pose proof (Z.mod_pos_bound (exv_sp E - 288) 32 ltac:(lia)).
  assert ((exv_sp E - 288) mod 32 <= 16); [|lia].
  rewrite Zminus_mod. replace (exv_sp E mod 32) with (exv_sp E mod 16 + 16 * ((exv_sp E / 16) mod 2)).
  - rewrite Hsp. change (288 mod 32) with 0. rewrite Z.sub_0_r, Z.add_0_l.
    pose proof (Z.mod_pos_bound (exv_sp E / 16) 2 ltac:(lia)).
    rewrite Z.mod_small; lia.
  - pose proof (Z.div_mod (exv_sp E) 16 ltac:(lia)). pose proof (Z.div_mod (exv_sp E / 16) 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound (exv_sp E / 16) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (exv_sp E) 16 ltac:(lia)).
    rewrite (Z.mod_unique (exv_sp E) 32 ((exv_sp E / 16) / 2) (exv_sp E mod 16 + 16 * ((exv_sp E / 16) mod 2))); lia. }
repeat split; try lia; assumption.
Qed.
End g.

(* ---- the return-site seat ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Lemma exb1_seat2 : forall (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (r s1 F : Z),
  getr regs 10 = w64 r -> getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 128 <= 2 ^ 64 -> 0 <= F < 2 ^ 64 ->
  val_mem rsegs (rdW W mem) (s1 + 120) 8 F ->
  st_ok_pi rsegs VAL (exb1_E2 regs F) (ss_exb1_2 r)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + EXB1_PC2)) mem (seg_rom rsegs)))
  /\ sh_ok rsegs exb1_Bx exb1_SH (exb1_E2 regs F) (rdW W mem).
Proof.
intros W regs mem r s1 F H10 H9 Hs0 Hs1 HF HV.
rewrite restrict_mkst_fx.
assert (U9 : bv_unsigned (ew (exb1_E2 regs F) 9) = s1).
{ unfold exb1_E2. rewrite (exb1_E_reg regs _ 9%bv 9) by reflexivity. rewrite H9. unfold w64.
  apply unsigned_lit_small. lia. }
split.
- unfold ss_exb1_2. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  + apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite H10. reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ s1 120 8 (SOff 32%nat 0) F); [ | exact HF | lia | exact HV ].
    cbn [sv_denot]. unfold exb1_E2. rewrite exb1_E_x. unfold w64. rewrite Z.add_0_r, unsigned_lit_small by lia.
    reflexivity.
  + cbn. tauto.
  + split; [exact I | split; exact I].
- unfold sh_ok, exb1_SH. apply Forall_nil.
Qed.
End s.

(* ---- the two continuations, at any float state ---- *)
Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Hypothesis KEXB : forall fx : YK11.FPState, KIT_EXB_OF_S (fx := fx) B ARx SK.

Section f. Context {fx : YK11.FPState}.

Ltac exb1_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* a0 = 0: `li s5, -1`, `bnez a0` not taken, at LS (B 0x83ca0) *)
Lemma exb1_post_ls : forall n m, CUT_LS (fx := fx) B ARx SK n m ->
  forall E ly2 S2 Hp2 (W2 : world rsegs) (regs2 : bvmap 5 word) mem2 md2 k pos (c : Z) (i cap : nat)
    (acc : list (list Z * PjTree.jv)) (ip2 vv dl : Z) (nm : list Z) (u : PjTree.jv),
  e_n E = n -> EXV_PRE B ARx E -> EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> length acc = i ->
  prhex_cur W2 mem2 (e_q E) (e_x0 E + ip2) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dl ->
  0 <= ip2 <= exv_len E -> (dl = 0 \/ dl = 1) -> Z.of_nat i < ip2 -> exv_len E - ip2 < m ->
  exv_V E =
    match PjGrammar.skip (skipn (Z.to_nat ip2) (e_x E)) with
    | c0 :: r1 =>
      if c0 =? 44 then exv_L (S (Z.to_nat (e_dep E))) (c =? 123) (S i) (exv_cap i cap) ((nm, u) :: acc) r1
      else if c0 =? PjGrammar.closer (c =? 123) then Some (PjGrammar.mk (c =? 123) (rev ((nm, u) :: acc)), r1)
      else None
    | [] => None
    end ->
  exv_dif E (c =? 123) vv dl ((nm, u) :: acc) ->
  getr regs2 10 = w64 0 ->
  getr regs2 27 = w64 c -> getr regs2 22 = w64 (shadow_addr (e_q E + 8)) -> getr regs2 23 = w64 (e_q E + 8) ->
  exv_spills E W2 mem2 ly2 pos c vv i ->
  SRr rsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + EXB1_PC2)) mem2 (seg_rom rsegs)) md2) (EXV_POST B ARx SK E).
Proof.
intros n m HL E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos c i cap acc ip2 vv dl nm u
  Hn HPRE HBs Hi1 Hc Hc2 Hdep Hacc Hcur Hip Hdl Hii Hm HV Hdif H10 H27 H22 H23 HSP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof HBs as (regs0 & HB0 & HR0).
pose proof HB0 as HB0'. unfold EXB in HB0'. cbv zeta in HB0'.
destruct HB0' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _ & _ & R2 & R8 & R9 & _).
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPwin & _).
destruct (exb1_geom B ARx SK E ly2 S2 Hp2 W2 mem2 md2 k pos HJ HPwin)
  as (Gsp & Gd0 & Gd16 & Gceil & G47 & (Gs1a & Gs1b) & Gs1m & GSTK & GF & Ghi & Gtop).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x rsegs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 1 pos HAR Hin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
assert (R9' : getr regs2 9 = w64 (exv_s1 E)).
{ rewrite (HR0 9%bv); [exact R9|]. intros X. apply (f_equal bv_unsigned) in X. vm_compute in X. discriminate X. }
pose proof HSP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S120 & _).
unfold exv_spill in S120.
destruct (exb1_seat2 (fx := fx) W2 regs2 mem2 0 (exv_s1 E) (frame_addr ly2 1 pos) H10 R9' ltac:(lia) ltac:(lia)
  ltac:(lia) S120) as [HS SHOK].
remember (exb1_E2 regs2 (frame_addr ly2 1 pos)) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs2 [w64 (frame_addr ly2 1 pos)]) Ev) by (rewrite HEv; apply exb1_agree).
pose (RUNTO := paj_run_to_x_inv (fx := fx) (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B PST ARx (eh_laws B ARx SK HYP)
  (exvl_P (e_mem E)) (exvl_PLAW (e_mem E))).
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM exb1_Bspan EXB1_PC3;
  [unfold ss_exb1_2, exb1_regions2; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
pmkst HS.
destruct (exb1_fr_ro Ev (w_H W2) mem2 (ms_mem ms) HFr) as [FK FP].
assert (RK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 22; 23; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs2 r).
{ intros r Hr. exact (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) Ev _ (restrict (w_H W2) ms) regs2 _
    [2; 3; 4; 8; 9; 18; 19; 22; 23; 25; 26; 27]%bv
    HS HAG ltac:(vm_compute; reflexivity) r Hr). }
prreg HS (21%bv : bv 5) R21.

lazymatch goal with |- context [Z_to_bv 64 (?b + ?kk)] =>
  replace (Z_to_bv 64 (b + kk)) with (w64 (exv_pc 0x774)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
refine (HL E ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) _ k pos c i cap acc ip2 vv dl nm u Hn HPRE _ Hi1 Hc Hc2 Hdep Hacc
  _ Hip Hdl Hii Hm HV Hdif _ _ _ _ _).
- apply (KRUN fx E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos (ms_regs ms) (ms_mem ms) _ HPRE HBs HJ).
  + intros a _ _ _ _. apply FK.
  + exact FP.
  + exact HPM.
  + intros r Hr Hn24. apply RK. unfold exv_bregs in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; try exb1_in. exfalso. exact (Hn24 eq_refl).
- exact (exb1_cur_kept W2 W2 mem2 (ms_mem ms) _ _ _ _ _ _ (fun x _ => FK x) Hcur).
- rewrite R21. unfold w64. apply bv_eq. vm_compute. reflexivity.
- rewrite RK by exb1_in. exact H27.
- rewrite RK by exb1_in. exact H22.
- rewrite RK by exb1_in. exact H23.
- exact (exb1_spills_kept E W2 W2 mem2 (ms_mem ms) ly2 ly2 pos c vv i (fun x _ => FK x) eq_refl HSP).
Qed.

(* a0 = -1: `li s5, -1`, `bnez a0` taken, `ld s8, 120(s1)`, `j`, at CX (B 0x83fa8) *)
Lemma exb1_post_cx : forall n, CUT_CX (fx := fx) B ARx SK n ->
  forall E ly2 S2 Hp2 (W2 : world rsegs) (regs2 : bvmap 5 word) mem2 md2 k pos,
  e_n E = n -> EXV_PRE B ARx E -> EXBs (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos ->
  EXV_RES E W2 mem2 (-1) -> getr regs2 10 = w64 (-1) ->
  exv_spill E W2 mem2 120 (frame_addr ly2 1 pos) ->
  SRr rsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + EXB1_PC2)) mem2 (seg_rom rsegs)) md2) (EXV_POST B ARx SK E).
Proof.
intros n HX E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos Hn HPRE HBs HRES H10 S120.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof HBs as (regs0 & HB0 & HR0).
pose proof HB0 as HB0'. unfold EXB in HB0'. cbv zeta in HB0'.
destruct HB0' as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _ & _ & R2 & R8 & R9 & _).
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPwin & _).
destruct (exb1_geom B ARx SK E ly2 S2 Hp2 W2 mem2 md2 k pos HJ HPwin)
  as (Gsp & Gd0 & Gd16 & Gceil & G47 & (Gs1a & Gs1b) & Gs1m & GSTK & GF & Ghi & Gtop).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x rsegs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 1 pos HAR Hin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
assert (R9' : getr regs2 9 = w64 (exv_s1 E)).
{ rewrite (HR0 9%bv); [exact R9|]. intros X. apply (f_equal bv_unsigned) in X. vm_compute in X. discriminate X. }
unfold exv_spill in S120.
destruct (exb1_seat2 (fx := fx) W2 regs2 mem2 (-1) (exv_s1 E) (frame_addr ly2 1 pos) H10 R9' ltac:(lia) ltac:(lia)
  ltac:(lia) S120) as [HS SHOK].
remember (exb1_E2 regs2 (frame_addr ly2 1 pos)) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs2 [w64 (frame_addr ly2 1 pos)]) Ev) by (rewrite HEv; apply exb1_agree).
assert (E32 : ew Ev 32 = w64 (frame_addr ly2 1 pos)) by (rewrite HEv; apply exb1_E_x).
pose (RUNTO := paj_run_to_x_inv (fx := fx) (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B PST ARx (eh_laws B ARx SK HYP)
  (exvl_P (e_mem E)) (exvl_PLAW (e_mem E))).
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM exb1_Bspan EXB1_PC4;
  [unfold ss_exb1_2, exb1_regions2; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
pmkst HS.
destruct (exb1_fr_ro Ev (w_H W2) mem2 (ms_mem ms) HFr) as [FK FP].
assert (RK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 25; 26]%bv -> getr (ms_regs ms) r = getr regs2 r).
{ intros r Hr. exact (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) Ev _ (restrict (w_H W2) ms) regs2 _
    [2; 3; 4; 8; 9; 18; 19; 25; 26]%bv
    HS HAG ltac:(vm_compute; reflexivity) r Hr). }
prreg HS (21%bv : bv 5) R21. prreg HS (24%bv : bv 5) R24.

lazymatch goal with |- context [Z_to_bv 64 (?b + ?kk)] =>
  replace (Z_to_bv 64 (b + kk)) with (w64 (exv_pc 0xa7c)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
lazymatch goal with |- SRr _ _ (mkCfg _ ?md3) _ =>
  refine (HX E ly2 S2 Hp2 W2 (ms_regs ms) (ms_mem ms) md3 k pos (-1) Hn HPRE _ _ _) end.
- apply (KEXB fx). 2:{ rewrite R24. exact E32. }
  apply (KRUN fx E ly2 S2 Hp2 W2 regs2 mem2 md2 k pos (ms_regs ms) (ms_mem ms) _ HPRE HBs HJ).
  + intros a _ _ _ _. apply FK.
  + exact FP.
  + exact HPM.
  + intros r Hr Hn24. apply RK. unfold exv_bregs in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; try exb1_in. exfalso. exact (Hn24 eq_refl).
- rewrite R21. unfold w64. apply bv_eq. vm_compute. reflexivity.
- destruct HRES as (p' & dep' & dl' & Hc & Hdl & HM). exists p', dep', dl'. split; [|exact (conj Hdl HM)].
  exact (exb1_cur_kept W2 W2 mem2 (ms_mem ms) _ _ _ _ _ _ (fun x _ => FK x) Hc).
Qed.

End f.
End p.
