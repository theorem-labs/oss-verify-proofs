(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound 2026-10-29 onto the old-pin kit of record (4f18c75d4900: PRH_Base ee6c7a38d6b6, PRH_FnEx
   ff16e926fb9e; base 88c5348fe7fc): memnorm carried from the entry memory as P m := memnorm (e_mem E) -> memnorm m
   (YSRrMemnorm.v), through the engine's _inv runners and the callees' m-form keeps (ex_string's fpostWm, strcmp's
   aj_strcmp_at_xrom); ex_string's Q has S' = S (exv_room Sc S2 by exv_room_refl); fpre's raZ < alloc_ceiling at the
   ex_string call from the jal's return pc. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value, segment C1 DISP, the STRING ARM (lane ExvDisp, sub-lane ExvDispStr): EXVD_STR of
   lib/B/Prog/ExvB_Disp_arms.v, from B 0x836fc (exv_pc 0x1d0) to the exit cut CUT_CX (B 0x83fa8, exv_pc 0xa7c):
       if (ex_string (in)) return -1;
       if (v && (v->type != PJ_STR || strcmp (v->str, in->scratch))) in->differs = 1;
       return 0;
   (fuzz_preset.c :318-321, read for the meaning only; no plain lemma cited, no lib/Prog file Required).
   Instructions walked (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s:118-154, 625-626; never a raw
   disassembly), engine YC1fPx paj_run_x_inv / paj_run_to_x_inv over B_prog_listing:
     0x836fc mv a0,s3; 0x83700 jal ex_string       the call (YCbqGcallW aj_call_xW_sp, text eh_string)
     0x83704 bnez a0 -> 0x83fa8                    r = -1 (ex_string refused)
     0x83708 ld a0,152(s1); 0x8370c beqz a0 -> 0x83ee8 (li s5,0; j 0x83fa8)   v = NULL
     0x83710 andi a2,a0,7; bnez -> 0x8407c unimp   UBSan alignment of v: NOT taken (v mod 8 = 0, a fact)
     0x83718 shadow of v; bnez -> 0x84118          ASan: NOT taken (v's 56 bytes addressable, shent)
     0x83728 lw a2,0(a0); li a1,4; bne -> 0x8376c  v->type
     0x83734 shadow of v + 16, 0x83748 shadow of q + 24 (bnez -> 0x8424c / 0x84250 reports: NOT taken, shents)
     0x8375c ld a0,16(v); ld a1,24(q); jal __wrap_strcmp   (YGcallMxmn aj_strcmp_at_xrom, text eh_strcmp)
     0x83768 beqz a0 -> 0x83ee8                    equal strings
     0x8376c shadow of q + 32 (bnez -> 0x8413c: NOT taken, shent); li s5,0; li a1,1; sw a1,32(q); j 0x83fa8
   Each straight-line stretch is one engine run from a fresh symbolic state built from EXB (the cut invariant);
   EXB at the next state comes from ExvOpen's exv_kt (after a stretch or strcmp; its memnorm premise from the _inv
   runner's P or strcmp's keep) or from ExvLoop's exv_kit_call (KIT_EXB_CALL, after ex_string; the call's chain,
   read-only view and scratch destination are exv_kit_chain, exv_kit_rodata, exv_kit_wdest). The ASan report calls
   and the UBSan trap are shown unreachable inside the runs (sh_obls = [],
   measured: every shadow branch is decided by the shents of q (EXB's range_addressable q 40) and of v
   (prhex_tree's range_addressable v 56), the trap by v's alignment fact).
   Rule 24: proves no function (kind: segment lemma). Numerals: as lib/B/Prog/ExvB_Disp_str_k.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YK06 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMx YGcallMxmn YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Open_kt ExvB_Open_sh ExvB_Loop_kit ExvB_Loop_kitP ExvB_Loop_kitQ ExvB_Disp_arms ExvB_Disp_str_k.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
(* the call kit's ExvB_Loop_kitQ.v Requires image A's listing instances: image B's are taken here, and passed
   explicitly in every statement *)
#[local] Existing Instance PI_prog_B.
#[local] Existing Instance PL_prog_B.

(* the goal's pc, as the symbolic run leaves it, written as exv_pc *)
Ltac exvs_pc_to off :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 ?pc) _ _; cfg_model := _ |} _ =>
    replace pc with (exv_pc off) by (vm_compute; reflexivity) end.

Section s. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

Section f. Context {fx : YK11.FPState}.
Variable n : nat.
Hypothesis CX : CUT_CX B ARx SK n.
Let LAWS := eh_laws B ARx SK HYP.
(* the engine runners carrying P m := memnorm m0 -> memnorm m (m0 the entry memory; YSRrMemnorm.v's laws) *)
Let RUNm (m0 : word -> option byte) := @paj_run_x_inv fx rc SK B_prog_listing PL_prog_B PI_prog_B B prh_pst ARx _ LAWS
  (fun m => YAkMemnorm.memnorm rsegs m0 -> YAkMemnorm.memnorm rsegs m)
  (YSRrMemnorm.srr_inv_laws_imp rsegs (YAkMemnorm.memnorm rsegs) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs)).
Let RUNTOm (m0 : word -> option byte) := @paj_run_to_x_inv fx rc SK B_prog_listing PL_prog_B PI_prog_B B prh_pst ARx _
  LAWS (fun m => YAkMemnorm.memnorm rsegs m0 -> YAkMemnorm.memnorm rsegs m)
  (YSRrMemnorm.srr_inv_laws_imp rsegs (YAkMemnorm.memnorm rsegs) m0 (YSRrMemnorm.srr_inv_laws_memnorm_k rsegs)).
Let BR := @paj_branch fx rc B_prog_listing PI_prog_B.
(* the shared kits at this fx, cited with HYP: ExvOpen's exv_kt (with the memnorm keep after the presence-growth
   premise) and ExvLoop's exv_kit_call (KIT_EXB_CALL with exv_room Sc S2 and the memnorm keep), their rebound texts *)
Let KTX := exv_kt (fx := fx) B ARx SK HYP.
Let KCX := exv_kit_call B ARx SK HYP fx.
(* the call kit's other three proofs at this fx (ExvB_Loop_kitQ.v), whichever of them rest on EXV_HYP *)
Ltac exvs_kq KCH KR KW :=
  assert (KCH : KIT_CALL_CHAIN (fx := fx) B ARx SK)
    by first [exact (exv_kit_chain B ARx SK HYP fx) | exact (exv_kit_chain B ARx SK fx)];
  assert (KR : KIT_RODATA (fx := fx) B ARx SK)
    by first [exact (exv_kit_rodata B ARx SK HYP fx) | exact (exv_kit_rodata B ARx SK fx)];
  assert (KW : KIT_WDEST (fx := fx) B ARx SK)
    by first [exact (exv_kit_wdest B ARx SK HYP fx) | exact (exv_kit_wdest B ARx SK fx)].

(* the exit: EXB after a stretch writing only the frame window and the FP cursor cells (exv_kt), then CUT_CX *)
Lemma exvs_cx : forall E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k' r,
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
     ~ (inFP (exv_FP E) a /\ e_q E <= a < e_q E + 40) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r EXVS_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 21 = w64 r -> EXV_RES E Wc memc' r ->
  SRr rsegs Wc (mkCfg (YK11.mkst regs' (Z_to_bv 64 (exv_pc 0xa7c)) memc' (YK11.seg_rom rsegs)) mdc')
    (EXV_POST B ARx SK E).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k' r HEn HP HB HJ HK HG HMN HR H21 HRES.
exact (CX E lyc Sc Hpc Wc regs' memc' mdc' k' pos r HEn HP
  (KTX E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' k' HP HB HJ HK HG HMN HR) H21 HRES).
Qed.

(* B 0x83704 with a0 = -1 (ex_string refused): bnez a0 -> 0x83fa8, s5 = -1 kept *)
Lemma exvs_none : forall E lyc Sc Hpc Wc regs memc mdc k pos,
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> exv_V E = None ->
  prhex_cur (PA := PI_prog_B) Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  getr regs 10 = w64 (-1) -> getr regs 21 = w64 (-1) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x1d8) regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos HEn HP HB HV HC H10 H21.
pose proof HB as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose (RUN := RUNm (e_mem E)). pose (RUNTO := RUNTOm (e_mem E)).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDEP & _ & HDL & _).
remember (Eimg (PI := PI_prog_B) (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env B_prog_val A_LIM E0) by (subst E0; exact (Eimg_env (L := B_prog_listing) (PI := PI_prog_B) _)).
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (subst E0; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi rsegs B_prog_val E0
  (mkSS (EXVS0 + 0x1d8) (sr_set sr_atoms 10%bv (SLit (2 ^ 64 - 1))) [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 (B_prog_val A_TEXT + (EXVS0 + 0x1d8))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (L := B_prog_listing) (PI := PI_prog_B)).
  - apply regs_ok_pin; [subst E0; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite H10. apply bv_eq. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok rsegs EXVS_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
clear HE0.
unfold cfg_at, w64. rewrite exvs_pc_eq.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVS_Bspan (EXVS0 + 0xa7c).
{ apply awr_ok_nil. }
assert (MEQ : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (rr & Hin & _). exact (in_nil Hin). }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 21; 24; 25; 26]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
pmkst HS. exvs_pc_to 0xa7c.
apply (exvs_cx E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k (-1) HEn HP HB HJ).
- intros a _ _ _. apply MEQ.
- intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
- exact HPM.
- intros r Hr. apply HK. unfold EXVS_KEPT in Hr. cbn [In] in Hr |- *. tauto.
- rewrite (HK 21%bv ltac:(cbn [In]; tauto)). exact H21.
- apply (exvs_res_none E Wc (ms_mem ms) (exv_i1 E) (e_dl E) HV).
  + exact (exvs_cur_eq Wc memc (ms_mem ms) _ _ _ _ _ _ HC (fun a _ => MEQ a)).
  + pose proof (exvd_i1_range E). zl.
  + exact HDL.
  + zl.
Qed.

(* B 0x83704 with a0 = 0 and v = NULL: ld a0,152(s1); beqz -> 0x83ee8: li s5,0; j 0x83fa8 *)
Lemma exvs_z0 : forall E lyc Sc Hpc Wc regs memc mdc k pos u rest,
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> exv_V E = Some (u, rest) ->
  e_v E = 0 ->
  prhex_cur (PA := PI_prog_B) Wc memc (e_q E) (e_x0 E + (exv_len E - Z.of_nat (length rest))) (e_x0 E + exv_len E)
    (e_dep E) (e_scr E)
    (e_dl E) ->
  getr regs 10 = w64 0 -> exv_spill E Wc memc 152 (e_v E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x1d8) regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos u rest HEn HP HB HV Hv0 HC H10 HSP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose (RUN := RUNm (e_mem E)). pose (RUNTO := RUNTOm (e_mem E)).
pose proof (exvs_geom B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 &
  G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDEP & _ & HDL & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & _).
remember (Eimg (PI := PI_prog_B) (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env B_prog_val A_LIM E0) by (subst E0; exact (Eimg_env (L := B_prog_listing) (PI := PI_prog_B) _)).
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (subst E0; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : ew E0 9 = getr regs 9)
  by (subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (U9 : bv_unsigned (ew E0 9) = exv_s1 E) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; zl).
assert (HS : st_ok_pi rsegs B_prog_val E0
  (mkSS (EXVS0 + 0x1d8) (sr_set sr_atoms 10%bv (SLit 0))
    [YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SLit 0))]] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 3)] [] []))
  (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 (B_prog_val A_TEXT + (EXVS0 + 0x1d8))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (L := B_prog_listing) (PI := PI_prog_B)).
  - apply regs_ok_pin; [subst E0; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. exact H10.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [zl|]. split; [zl|]. split; [intros o Ho; zl|]. constructor; [|constructor].
    apply (chunk_ok_val rsegs E0 _ (exv_s1 E) 152 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    unfold exv_spill in HSP. rewrite Hv0 in HSP. exact HSP.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 3) with 8.
    split; [split; [split; [zl | split; [zl | lia]] | exact I] | split; exact I]. }
assert (SHOK : sh_ok rsegs EXVS_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
clear HE0.
unfold cfg_at, w64. rewrite exvs_pc_eq.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVS_Bspan (EXVS0 + 0xa7c).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (MEQ : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (rr & Hin & Hr). cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (21%bv : bv 5) R21.
pmkst HS. exvs_pc_to 0xa7c.
apply (exvs_cx E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k 0 HEn HP HB HJ).
- intros a _ _ _. apply MEQ.
- intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
- exact HPM.
- exact HK.
- rewrite R21. reflexivity.
- apply (exvs_res_ok E Wc (ms_mem ms) u rest (e_dl E) HV).
  + exact (exvs_cur_eq Wc memc (ms_mem ms) _ _ _ _ _ _ HC (fun a _ => MEQ a)).
  + exact HDL.
  + split; [intros H; left; exact H | intros [H | [H _]]; [exact H | exfalso; exact (H Hv0)]].
Qed.

(* the low atoms of the image environment are the registers *)
Lemma exvs_ew : forall (regs : bvmap 5 word) extra (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r ->
  ew (Eimg (PI := PI_prog_B) (Ereg regs extra)) m = getr regs r.
Proof.
intros regs extra m r H. pose proof (bv_unsigned_in_range 5 r) as R. unfold bv_modulus in R. cbn in R.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs extra m r H).
Qed.
Lemma exvs_ewx : forall (regs : bvmap 5 word) extra j, (32 + j < A_TEXT)%nat ->
  ew (Eimg (PI := PI_prog_B) (Ereg regs extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j H. rewrite Eimg_low by exact H. apply ew_Ereg_extra. Qed.

(* B 0x8376c: in->differs = 1 (shadow of q + 32: NOT taken), li s5,0; j 0x83fa8 *)
Lemma exvs_dif : forall E lyc Sc Hpc Wc regs memc mdc k pos u rest,
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> exv_V E = Some (u, rest) ->
  e_v E <> 0 -> e_t E <> u ->
  prhex_cur (PA := PI_prog_B) Wc memc (e_q E) (e_x0 E + (exv_len E - Z.of_nat (length rest))) (e_x0 E + exv_len E)
    (e_dep E) (e_scr E)
    (e_dl E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x240) regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos u rest HEn HP HB HV Hv0 Ht HC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose (RUN := RUNm (e_mem E)). pose (RUNTO := RUNTOm (e_mem E)).
pose proof (exvs_geom B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 &
  G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & _ & _ & _ & _ & _ & _
  & _ & _ & _ & HQR & _).
remember (Eimg (PI := PI_prog_B) (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env B_prog_val A_LIM E0) by (subst E0; exact (Eimg_env (L := B_prog_listing) (PI := PI_prog_B) _)).
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (subst E0; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E19 : ew E0 19 = Z_to_bv 64 (e_q E)) by (subst E0; rewrite (exvs_ew regs [] 19 19%bv eq_refl); exact R19).
assert (E25 : ew E0 25 = Z_to_bv 64 SHADOW_OFF) by (subst E0; rewrite (exvs_ew regs [] 25 25%bv eq_refl); exact R25).
assert (U19 : bv_unsigned (ew E0 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; zl).
assert (U25 : bv_unsigned (ew E0 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi rsegs B_prog_val E0
  (mkSS (EXVS0 + 0x240) sr_atoms [YP09.mkRegion (Some 19%nat) 0 40 32 36 []] None
    (mkFacts [(19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
  (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 (B_prog_val A_TEXT + (EXVS0 + 0x240))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (L := B_prog_listing) (PI := PI_prog_B)).
  - subst E0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
    split; [zl|]. split; [zl|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply G18. zl.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U19, U25. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    repeat split; zl. }
assert (HBx : U E0 EXVS_Bx = SHADOW_OFF) by (unfold EXVS_Bx; apply (U_atom E0 25 SHADOW_OFF E25); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok rsegs EXVS_Bx [mkSHE 19 0 40] E0 (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc E0 EXVS_Bx 19 (e_q E) 40 (e_q E) 0 40 HQR HBx);
    [apply (U_atom E0 19 (e_q E) E19); zl | lia | lia |].
  intros x Hx. change (Z.min 0 40) with 0 in Hx. change (Z.max 0 40) with 40 in Hx. unfold SHADOW_OFF. zl. }
clear HE0.
unfold cfg_at, w64. rewrite exvs_pc_eq.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVS_Bspan (EXVS0 + 0xa7c).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
  apply awr_ok_cons_gen with (k := 19%nat) (b := e_q E); [reflexivity | exact U19 | | apply awr_ok_nil].
  cbn [r_wlo r_whi YP09.r_wlo YP09.r_whi]. intros a Ha. left. zl. }
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (e_q E + 32 <= a < e_q E + 36) ->
  aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
{ intros a Ha0 Ha. apply aview_eq_of. apply HFr. intros (rr & Hin & Hr). cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U19 in Hr.
  rewrite unsigned_lit_small in Hr by lia. apply Ha. lia. }
pose proof (exvs_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exvs_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SLit 1) 1 RQ U19
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VQ.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (21%bv : bv 5) R21.
pmkst HS. exvs_pc_to 0xa7c.
apply (exvs_cx E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k 0 HEn HP HB HJ).
- intros a Ha0 _ Hn. apply KEPT; [exact Ha0|]. intros Ha. apply Hn. split; [|zl].
  exists (e_q E + 32, e_q E + 36). split; [unfold exv_FP; cbn [In]; tauto | cbn [fst snd]; lia].
- intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
- exact HPM.
- exact HK.
- rewrite R21. reflexivity.
- apply (exvs_res_ok E Wc (ms_mem ms) u rest 1 HV).
  + apply (exvs_cur_keep Wc memc (ms_mem ms) _ _ _ _ _ _ 1 HC); [intros a Ha; apply KEPT; zl | exact VQ].
  + right; reflexivity.
  + split; [intros _; right; split; assumption | intros _; reflexivity].
Qed.

(* B 0x83768, after strcmp: beqz a0 -> 0x83ee8 (li s5,0; j 0x83fa8), else on to 0x8376c *)
Lemma exvs_s3 : forall E lyc Sc Hpc Wc regs memc mdc k pos u rest,
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> exv_V E = Some (u, rest) ->
  e_v E <> 0 ->
  prhex_cur (PA := PI_prog_B) Wc memc (e_q E) (e_x0 E + (exv_len E - Z.of_nat (length rest))) (e_x0 E + exv_len E)
    (e_dep E) (e_scr E)
    (e_dl E) ->
  (getr regs 10 = w64 0 -> e_t E = u) -> (getr regs 10 <> w64 0 -> e_t E <> u) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x23c) regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos u rest HEn HP HB HV Hv0 HC Heq Hne.
pose proof HB as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose (RUN := RUNm (e_mem E)). pose (RUNTO := RUNTOm (e_mem E)).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDL & _).
remember (Eimg (PI := PI_prog_B) (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env B_prog_val A_LIM E0) by (subst E0; exact (Eimg_env (L := B_prog_listing) (PI := PI_prog_B) _)).
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (subst E0; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E0 10 = Z_to_bv 64 (bv_unsigned (getr regs 10)))
  by (subst E0; rewrite (exvs_ew regs [] 10 10%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (bv_unsigned_in_range 64 (getr regs 10)) as R10. unfold bv_modulus in R10. cbn in R10.
assert (HS : st_ok_pi rsegs B_prog_val E0 (mkSS (EXVS0 + 0x23c) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 (B_prog_val A_TEXT + (EXVS0 + 0x23c))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (L := B_prog_listing) (PI := PI_prog_B)).
  - subst E0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok rsegs EXVS_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
clear HE0.
unfold cfg_at, w64. rewrite exvs_pc_eq.
paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVS_Bspan.
{ apply awr_ok_nil. }
assert (MEQ1 : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (rr & Hin & _). exact (in_nil Hin). }
rename HG into HG1. rename ms into ms1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK EXVS_Bspan.
- (* a0 = 0: equal strings *)
  rewrite branch_eq_U, (U_atom _ 10 _ E10 R10), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (H0 : getr regs 10 = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
  specialize (Heq H0).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVS_Bspan (EXVS0 + 0xa7c).
  { apply awr_ok_nil. }
  assert (MEQ : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
  { intros a. rewrite <- (MEQ1 a). apply aview_eq_of. apply HFr. intros (rr & Hin & _). exact (in_nil Hin). }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (21%bv : bv 5) R21.
  pmkst HS. exvs_pc_to 0xa7c.
  apply (exvs_cx E lyc Sc Hpc Wc regs memc mdc k pos _ _ _ k 0 HEn HP HB HJ).
  + intros a _ _ _. apply MEQ.
  + intros a Ha. exact (apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG1 Ha)).
  + exact HPM.
  + exact HK.
  + rewrite R21. reflexivity.
  + apply (exvs_res_ok E Wc (ms_mem ms) u rest (e_dl E) HV).
    * exact (exvs_cur_eq Wc memc (ms_mem ms) _ _ _ _ _ _ HC (fun a _ => MEQ a)).
    * exact HDL.
    * split; [intros H; left; exact H | intros [H | [_ H]]; [exact H | exfalso; exact (H Heq)]].
- (* a0 <> 0: the strings differ *)
  rewrite branch_eq_U, (U_atom _ 10 _ E10 R10), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  assert (H0 : getr regs 10 <> w64 0).
  { intros H. apply Hc. rewrite H. reflexivity. }
  specialize (Hne H0).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVS_Bspan (EXVS0 + 0x240).
  { apply awr_ok_nil. }
  assert (MEQ : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
  { intros a. rewrite <- (MEQ1 a). apply aview_eq_of. apply HFr. intros (rr & Hin & _). exact (in_nil Hin). }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  pose proof (KTX E lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms) (ms_mem ms) _ k HP HB HJ
    (fun a _ _ _ => MEQ a) (fun a Ha => apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG1 Ha)) HPM HK) as HB2.
  pmkst HS. exvs_pc_to 0x240.
  apply (exvs_dif E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ k pos u rest HEn HP HB2 HV Hv0 Hne).
  exact (exvs_cur_eq Wc memc (ms_mem ms) _ _ _ _ _ _ HC (fun a _ => MEQ a)).
Qed.

(* a stretch over read-only regions writes nothing *)
Ltac exvs_ro HFr :=
  apply HFr; let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (rr & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia |]);
  destruct Hin.

(* B 0x83704 with a0 = 0 and v a node: v's alignment (UBSan) and shadow (ASan) checks, v->type, and for a string node
   the shadows of v + 16 and q + 24 and the call of __wrap_strcmp (v->str, in->scratch) *)
Lemma exvs_zv : forall E lyc Sc Hpc Wc regs memc mdc k pos s rest,
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_V E = Some (PjTree.JStr s, rest) -> e_v E <> 0 ->
  prhex_cur (PA := PI_prog_B) Wc memc (e_q E) (e_x0 E + (exv_len E - Z.of_nat (length rest))) (e_x0 E + exv_len E)
    (e_dep E) (e_scr E)
    (e_dl E) ->
  bytes_at (PA := PI_prog_B) Wc memc (e_scr E) (s ++ [0]) -> Forall (fun b => b <> 0) s -> Z.of_nat (length s) < exv_len E ->
  getr regs 10 = w64 0 -> exv_spill E Wc memc 152 (e_v E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x1d8) regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos s rest HEn HP HB HV Hv0 HC HBS HNZ HLS H10 HSP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose (RUN := RUNm (e_mem E)). pose (RUNTO := RUNTOm (e_mem E)).
pose proof (exvs_geom B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 &
  G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof (exvs_v_rng B ARx SK HYP E lyc Sc Hpc Wc regs memc mdc k pos HP HB Hv0) as (V1 & V2 & V3 & V4).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & _ & _ & _ &
  _ & _ & HWD & HSB & HQR & HTREE).
destruct HTREE as [Hv | (Hnd & Hhome & Hra & Hhull)]; [exfalso; exact (Hv0 Hv)|].
destruct (exvs_node_hdr _ _ _ _ _ Hnd) as (num & str & kids & keys & nn & cap & HH & HM).
pose proof HH as ((Hv8 & _) & (Hty0 & Hty) & _ & (Hstr0 & Hstr) & _).
pose proof (exvs_tag_range (e_t E)) as HTR.
pose proof HWD as (W1 & W2 & _).
pose proof HC as (_ & _ & _ & HC4 & _).
pose proof (V4 (e_v E) ltac:(lia)) as (F1 & F2). pose proof (V4 (e_v E + 23) ltac:(lia)) as (F3 & F4).
set (extra := [Z_to_bv 64 (e_v E); Z_to_bv 64 (PjTree.tag (e_t E)); Z_to_bv 64 str; Z_to_bv 64 (e_scr E)]).
remember (Eimg (PI := PI_prog_B) (Ereg regs extra)) as E0 eqn:HE0.
assert (HEI : img_env B_prog_val A_LIM E0) by (subst E0; exact (Eimg_env (L := B_prog_listing) (PI := PI_prog_B) _)).
assert (HAE : env_agree 32 (Ereg regs extra) E0)
  by (subst E0; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : ew E0 9 = Z_to_bv 64 (exv_s1 E)) by (subst E0; rewrite (exvs_ew regs extra 9 9%bv eq_refl); exact R9).
assert (E19 : ew E0 19 = Z_to_bv 64 (e_q E)) by (subst E0; rewrite (exvs_ew regs extra 19 19%bv eq_refl); exact R19).
assert (E25 : ew E0 25 = Z_to_bv 64 SHADOW_OFF) by (subst E0; rewrite (exvs_ew regs extra 25 25%bv eq_refl); exact R25).
assert (E32 : ew E0 32 = Z_to_bv 64 (e_v E)) by (subst E0; exact (exvs_ewx regs extra 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E0 33 = Z_to_bv 64 (PjTree.tag (e_t E)))
  by (subst E0; exact (exvs_ewx regs extra 1 ltac:(unfold A_TEXT; lia))).
assert (E34 : ew E0 34 = Z_to_bv 64 str) by (subst E0; exact (exvs_ewx regs extra 2 ltac:(unfold A_TEXT; lia))).
assert (E35 : ew E0 35 = Z_to_bv 64 (e_scr E)) by (subst E0; exact (exvs_ewx regs extra 3 ltac:(unfold A_TEXT; lia))).
assert (U9 : bv_unsigned (ew E0 9) = exv_s1 E) by (rewrite E9; apply unsigned_lit_small; zl).
assert (U19 : bv_unsigned (ew E0 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; zl).
assert (U25 : bv_unsigned (ew E0 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E0 32) = e_v E) by (rewrite E32; apply unsigned_lit_small; zl).
assert (U33 : bv_unsigned (ew E0 33) = PjTree.tag (e_t E)) by (rewrite E33; apply unsigned_lit_small; zl).
assert (DV : forall j w, ew E0 j = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> sv_denot E0 (SOff j 0) = Z_to_bv 64 w).
{ intros j w Hj Hw. cbn [sv_denot]. rewrite Hj, unsigned_lit_small by exact Hw. rewrite Z.add_0_r. reflexivity. }
assert (HS : st_ok_pi rsegs B_prog_val E0
  (mkSS (EXVS0 + 0x1d8) (sr_set sr_atoms 10%bv (SLit 0))
    [YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff 32 0))];
     YP09.mkRegion (Some 32%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))];
     YP09.mkRegion (Some 19%nat) 0 40 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 35 0))]] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 3); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3);
              (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 (2 ^ 47 - 56) 3); (33%nat, mkAF 0 6 0)] [] []))
  (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 (B_prog_val A_TEXT + (EXVS0 + 0x1d8))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (L := B_prog_listing) (PI := PI_prog_B)).
  - apply regs_ok_pin; [subst E0; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. exact H10.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [zl|]. split; [zl|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E0 _ (exv_s1 E) 152 8 (SOff 32 0) (e_v E)); [apply DV; [exact E32 | zl] | cbn; zl | cbn; lia |].
      exact HSP.
    + rewrite U32. split; [zl|]. split; [zl|]. split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs E0 _ (e_v E) 0 4 (SOff 33 0) (PjTree.tag (e_t E))); [apply DV; [exact E33 | zl] | cbn; zl | cbn; lia |].
        rewrite Z.add_0_r. exact Hty.
      * apply (chunk_ok_val rsegs E0 _ (e_v E) 16 8 (SOff 34 0) str); [apply DV; [exact E34 | zl] | cbn; zl | cbn; lia |].
        exact Hstr.
    + rewrite U19. split; [zl|]. split; [zl|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val rsegs E0 _ (e_q E) 24 8 (SOff 35 0) (e_scr E)); [apply DV; [exact E35 | zl] | cbn; zl | cbn; lia |].
      exact HC4.
  - apply pairwise_disjoint_of_extents. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; zl.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U9, U19, U25, U32, U33. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    repeat split; zl. }
assert (HBx : U E0 EXVS_Bx = SHADOW_OFF) by (unfold EXVS_Bx; apply (U_atom E0 25 SHADOW_OFF E25); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok rsegs EXVS_Bx [mkSHE 32 0 56; mkSHE 19 0 40] E0 (mrestrict (w_H Wc) memc)).
{ constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H Wc) memc E0 EXVS_Bx 32 (e_v E) 56 (e_v E) 0 56 Hra HBx);
      [apply (U_atom E0 32 (e_v E) E32); zl | lia | lia |].
    intros x Hx. change (Z.min 0 56) with 0 in Hx. change (Z.max 0 56) with 56 in Hx. apply V3. lia.
  - apply (shent_ok_of_range rsegs (w_H Wc) memc E0 EXVS_Bx 19 (e_q E) 40 (e_q E) 0 40 HQR HBx);
      [apply (U_atom E0 19 (e_q E) E19); zl | lia | lia |].
    intros x Hx. change (Z.min 0 40) with 0 in Hx. change (Z.max 0 40) with 40 in Hx. unfold SHADOW_OFF. zl. }
clear HE0.
unfold cfg_at, w64. rewrite exvs_pc_eq.
paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVS_Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (MEQ1 : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a)
  by (intros a; apply aview_eq_of; exvs_ro HFr).
rename HG into HG1. rename ms into ms1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK EXVS_Bspan.
- (* v->type <> PJ_STR: in->differs = 1 *)
  rewrite branch_ne_U, (U_atom _ 33 _ E33 ltac:(zl)), U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EXVS_Bspan (EXVS0 + 0x240).
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
      change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  assert (MEQ : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a)
    by (intros a; rewrite <- (MEQ1 a); apply aview_eq_of; exvs_ro HFr).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs extra [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  pose proof (KTX E lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms) (ms_mem ms) _ k HP HB HJ
    (fun a _ _ _ => MEQ a) (fun a Ha => apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG1 Ha)) HPM HK) as HB2.
  pmkst HS. exvs_pc_to 0x240.
  apply (exvs_dif E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ k pos (PjTree.JStr s) rest HEn HP HB2 HV Hv0).
  + intros Et. apply Hc. rewrite Et. reflexivity.
  + exact (exvs_cur_eq Wc memc (ms_mem ms) _ _ _ _ _ _ HC (fun a _ => MEQ a)).
- (* v->type = PJ_STR: strcmp (v->str, in->scratch) *)
  rewrite branch_ne_U, (U_atom _ 33 _ E33 ltac:(zl)), U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  destruct (exvs_tag4 (e_t E) Hc) as (s' & Et).
  destruct (HM s' Et) as (kk & (HLk & Hkk & H32s & HF0 & HG0)).
  paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVS_Bspan.
  { lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
      change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  assert (MEQ : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a)
    by (intros a; rewrite <- (MEQ1 a); apply aview_eq_of; exvs_ro HFr).
  pose proof (regs_kept_of_st_ok _ _ _ _ regs extra [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (1%bv : bv 5) R1.
  rewrite E34 in R10. rewrite E35 in R11.
  pose proof (KTX E lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms) (ms_mem ms) _ k HP HB HJ
    (fun a _ _ _ => MEQ a) (fun a Ha => apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG1 Ha)) HPM HK) as HBc.
  pose proof HBc as HBc0. unfold EXB in HBc0. cbv zeta in HBc0.
  destruct HBc0 as (HJc & _ & _ & _ & _ & _ & _ & HLEDc & _ & R2c & _).
  pose proof HJc as (HARc & _).
  exvs_kq KCH KR KW.
  destruct (KR E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ k pos HP HBc) as (HROM & _).
  (* the two operands *)
  pose proof HLEDc as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
  destruct (HBL (str, kk) HLk) as (_ & Hblk & Hhp & _ & _). cbn [fst snd] in Hblk, Hhp.
  pose proof (@cf_head_nonneg cp) as CH0.
  assert (GX : garr8 rsegs (mrestrict (w_H Wc) (ms_mem ms)) str (s' ++ [0]))
    by (eapply exk_garr8_kept; [|exact HG0]; intros a _; apply MEQ).
  assert (GY : garr8 rsegs (mrestrict (w_H Wc) (ms_mem ms)) (e_scr E) (s ++ [0]))
    by (eapply exk_garr8_kept; [|exact HBS]; intros a _; apply MEQ).
  assert (FX : Forall (fun c => c <> 0) s') by (eapply Forall_impl; [|exact HF0]; intros c Hc'; cbv beta in *; zl).
  destruct (exvs_blk_op B ARx SK HYP _ _ _ _ _ _ (str - cf_head) (kk + cf_head) str s' HARc Hblk ltac:(lia) ltac:(lia)
    GX FX) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
  pose proof HSB as (b2 & m2 & Hin2 & Hb2 & Hm2 & Hhd2).
  assert (Hin2c : In (b2, m2) (ablocks B lyc Sc)) by exact Hin2.
  destruct (exvs_blk_op B ARx SK HYP _ _ _ _ _ _ b2 m2 (e_scr E) s HARc Hin2c Hb2 ltac:(lia) GY HNZ)
    as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7).
  destruct (exv_sh_lam B ARx SK HYP lyc Sc Hpc Wc (ms_mem ms) _ (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
    str kk str (Z.of_nat (length s') + 1) HARc HLEDc HLk ltac:(lia) ltac:(lia) ltac:(lia)) as (XS1 & XS2).
  destruct (exv_sh_blk B ARx SK HYP lyc Sc Hpc Wc (ms_mem ms) _ (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
    (e_scr E) (Z.of_nat (length s) + 1) HARc HLEDc
    ltac:(exists b2, m2; split; [exact Hin2 | split; [exact Hb2 | split; [lia | exact Hhd2]]]) ltac:(lia))
    as (YS1 & YS2).
  assert (Usp : spZ (ms_regs ms) = exv_s1 E)
    by (unfold spZ; rewrite R2c; unfold w64; apply unsigned_lit_small; zl).
  pmkst HS.
  eapply SRr_bind.
  { eapply (YGcallMxmn.aj_strcmp_at_xrom (SK := SK) rsegs B prh_pst ARx B_prog_relro_lo B_prog_relro_hi LAWS B_prog_segs_low
      (B_prog_sigma AS___wrap_strcmp) (eh_strcmp B ARx SK HYP fx) Wc (ms_regs ms) (ms_mem ms)
      (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
      [(1, pos)] lyc Sc Hpc _ k str (e_scr E) (Z.of_nat (length s')) (Z.of_nat (length s))
      (exv_s1 E - (exv_sp E + e_d E)) (getr (ms_regs ms) 1) HJ R10 R11).
    all: try (rewrite ?Usp; zl).
    - rewrite (HK 3%bv ltac:(cbn; tauto)). exact R3.
    - rewrite (HK 4%bv ltac:(cbn; tauto)). exact R4.
    - reflexivity.
    - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - exact X5.
    - exact Y5.
    - intros a Ha. split; [apply X6; lia | rewrite Usp; zl].
    - intros a Ha. split; [apply Y6; lia | rewrite Usp; zl].
    - exact X4.
    - exact Y4.
    - exact XS1.
    - exact XS2.
    - exact YS1.
    - exact YS2.
    - exact X7.
    - exact Y7.
    - exact HROM. }
  cbv beta. intros Wx c2 _ (-> & regs2 & mem2 & md2 & vr & -> & HJ2 & HP2 & H10' & Hcmp & HWIN & HPRES2 & HKP).
  assert (MEQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (exv_s1 E - 2 * ESTACK <= a < exv_s1 E) ->
    aview rsegs (w_H Wc) mem2 a = aview rsegs (w_H Wc) memc a).
  { intros a Ha Hn. rewrite <- (MEQ a). apply HWIN; [exact Ha|]. intros Hw. apply Hn. zl. }
  pose proof (KTX E lyc Sc Hpc Wc regs memc mdc k pos regs2 mem2 md2 k HP HB HJ2
    (fun a Ha Hn _ => MEQ2 a Ha ltac:(intros Hw; apply Hn; zl))
    (fun a Ha => HPRES2 a (apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG1 Ha)))
    (fun H0 => HKP (HPM H0))
    (fun r Hr => eq_trans (exvs_aregs_kept _ _ HP2 r Hr) (HK r Hr))) as HB3.
  rewrite R1. exvs_pc_to 0x23c.
  apply (exvs_s3 E lyc Sc Hpc Wc regs2 mem2 md2 k pos (PjTree.JStr s) rest HEn HP HB3 HV Hv0).
  + apply (exvs_cur_eq Wc memc mem2 _ _ _ _ _ _ HC). intros a Ha. apply MEQ2; zl.
  + intros H0. rewrite H10' in H0. apply Hcmp in H0. destruct H0 as (Hkk' & Hby).
    rewrite Et. f_equal. apply (exvs_eq_bytes Wc (ms_mem ms) str (e_scr E) s' s GX GY); [lia | exact Hby].
  + intros Hn Ht. apply Hn. rewrite H10'. apply Hcmp. rewrite Et in Ht. injection Ht as <-.
    split; [reflexivity|]. intros i Hi.
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (exvs_av_garr8 (w_H Wc) (ms_mem ms) str (s' ++ [0]) (Z.to_nat i) GX) by (rewrite length_app; cbn; lia).
    rewrite (exvs_av_garr8 (w_H Wc) (ms_mem ms) (e_scr E) (s' ++ [0]) (Z.to_nat i) GY) by (rewrite length_app; cbn; lia).
    reflexivity.
Qed.

(* B 0x836fc: mv a0,s3; jal ex_string (the text, eh_string), then the three continuations at B 0x83704 *)
Lemma exvs_entry : forall E lyc Sc Hpc Wc regs memc mdc k pos,
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  prhex_cur (PA := PI_prog_B) Wc memc (e_q E) (e_x0 E + exv_i1 E) (e_x0 E + exv_len E) (e_dep E) (e_scr E) (e_dl E) ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = 34 ->
  getr regs 21 = w64 (-1) -> exv_spill E Wc memc 152 (e_v E) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x1d0) regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros E lyc Sc Hpc Wc regs memc mdc k pos HEn HP HB HC Hi1 Hq H21 HSP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HJ & _ & _ & _ & _ & _ & (_ & HPM) & _).
pose (RUN := RUNm (e_mem E)). pose (RUNTO := RUNTOm (e_mem E)).
pose proof (exvs_geom B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos HP HB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 &
  G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof (exvd_i1_range E) as HI1.
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLEN & HI0 & HDEP & _ & HDL & _ & _ & HSX & HSQ & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & HFZ & _ & _ & _ & _ & _ & R2 & R8 & R9 & _ & _ & _ & _ & R19 & R3 & R4 & _).
pose proof HC as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof (exvd_V_at E ltac:(zl) Hi1) as HV0. rewrite Hq, exvd_V_str in HV0.
change (S (Z.to_nat (exv_i1 E))) with (Nat.succ (Z.to_nat (exv_i1 E))) in HV0.
remember (Eimg (PI := PI_prog_B) (Ereg regs [])) as E0 eqn:HE0.
assert (HEI : img_env B_prog_val A_LIM E0) by (subst E0; exact (Eimg_env (L := B_prog_listing) (PI := PI_prog_B) _)).
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (subst E0; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E19 : ew E0 19 = Z_to_bv 64 (e_q E)) by (subst E0; rewrite (exvs_ew regs [] 19 19%bv eq_refl); exact R19).
assert (HS : st_ok_pi rsegs B_prog_val E0 (mkSS (EXVS0 + 0x1d0) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (YK11.mkst regs (Z_to_bv 64 (B_prog_val A_TEXT + (EXVS0 + 0x1d0))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (pa_entry_st_ok_full (L := B_prog_listing) (PI := PI_prog_B)).
  - subst E0. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok rsegs EXVS_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
clear HE0.
unfold cfg_at, w64. rewrite exvs_pc_eq.
paj_run_tok_x_inv RUN HS HJ SHOK HPM EXVS_Bspan.
{ apply awr_ok_nil. }
assert (MEQ : forall a, aview rsegs (w_H Wc) (ms_mem ms) a = aview rsegs (w_H Wc) memc a).
{ intros a. apply aview_eq_of. apply HFr. intros (rr & Hin & _). exact (in_nil Hin). }
pose proof (regs_kept_of_st_ok _ _ _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 21; 24; 25; 26]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. rewrite E19 in R10.
assert (R2' : getr (ms_regs ms) 2 = w64 (exv_s1 E)) by (rewrite (HK 2%bv ltac:(cbn [In]; tauto)); exact R2).
assert (R8' : getr (ms_regs ms) 8 = w64 (exv_sp E)) by (rewrite (HK 8%bv ltac:(cbn [In]; tauto)); exact R8).
assert (Usp : spZ (ms_regs ms) = exv_s1 E) by (unfold spZ; rewrite R2'; unfold w64; apply unsigned_lit_small; zl).
assert (Us0 : s0Z (ms_regs ms) = exv_sp E) by (unfold s0Z; rewrite R8'; unfold w64; apply unsigned_lit_small; zl).
pose proof (KTX E lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms) (ms_mem ms) _ k HP HB HJ
  (fun a _ _ _ => MEQ a) (fun a Ha => apresent_grows _ _ _ a HG Ha) HPM
  (fun r Hr => HK r ltac:(cbn [In] in Hr |- *; tauto))) as HBc.
pose proof HBc as HBc0. unfold EXB in HBc0. cbv zeta in HBc0.
destruct HBc0 as (_ & _ & _ & _ & _ & _ & _ & HLEDc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HSRCc & HINBc & _ & HSBc & _ & _).
exvs_kq KCH KR KW.
destruct (KCH E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ k pos (ms_regs ms) HP HBc R2' R8') as (ch1 & Hch1 & _).
destruct (KR E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ k pos HP HBc) as (Hrod & _).
pose proof (KW E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ k pos (ms_regs ms) STK_ex_string
  HP HBc R2' G15 ltac:(zl)) as HWD.
assert (HFP1 : forall a, inFP [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8)] a -> inFP (exv_FP E) a).
{ intros a (r & Hr & Ha). exists r. split; [|exact Ha]. unfold exv_FP. cbn [In] in Hr |- *.
  destruct Hr as [<- | [<- | []]]; tauto. }
eapply SRr_bind.
{ eapply (aj_call_xW_sp (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low Wc E0 _ ms
    (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    [(1, pos)] lyc Sc Hpc _ k STK_ex_string (exv_sp E + e_d E - exv_s1 E)
    [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8)] (exv_s1 E - (exv_sp E + e_d E))
    (getr (ms_regs ms) 1) ch1 _ HS eq_refl HJ).
  - rewrite Usp. ring.
  - zl.
  - zl.
  - exact G15.
  - zl.
  - zl.
  - zl.
  - zl.
  - rewrite (HK 3%bv ltac:(cbn [In]; tauto)). exact R3.
  - rewrite (HK 4%bv ltac:(cbn [In]; tauto)). exact R4.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite R1. apply Z.leb_le. vm_compute. reflexivity.
  - replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) by ring. rewrite Us0. exact Hch1.
  - intros HAF HWIN. cbn [ss_pc setpc].
    refine (eh_string B ARx SK HYP fx lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 (e_q E) (e_x0 E) (exv_i1 E)
      (e_scr E) (exv_sp E + e_d E - exv_s1 E) (e_x E) (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + split; [exact HAF|]. split; [exact Hrod|]. split; [rewrite Usp; zl|].
      (* fpre's raZ < alloc_ceiling: the return pc is the listing literal B_prog_val A_TEXT + 0x1ec *)
      assert (HRA : bv_unsigned (getr (ms_regs ms) 1) < 2 ^ 40) by (rewrite R1; apply Z.ltb_lt; vm_compute; reflexivity).
      split; [unfold raZ; zl | exact HFZ].
    + exact R10.
    + eapply exk_val_kept; [|exact CC1]. intros x Hx. apply MEQ.
    + eapply exk_val_kept; [|exact CC2]. intros x Hx. apply MEQ.
    + eapply exk_val_kept; [|exact CC4]. intros x Hx. apply MEQ.
    + exact G12.
    + rewrite Usp. zl.
    + rewrite Usp. zl.
    + exact HWIN.
    + exact HSRCc.
    + apply HINBc. zl.
    + exact HLEN.
    + unfold exv_len in *. zl.
    + exact HWD.
    + exact HSBc.
    + exact HSX.
    + exact HSQ.
    + exact HLEDc.
  - intros a (r & Hr & Ha). left. exists r. split; [|exact Ha]. unfold exv_FP. cbn [In] in Hr |- *.
    destruct Hr as [<- | [<- | []]]; tauto. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HP2 & HQ).
destruct HQ as ((HRM & HHp & HSS & HAB & HLED2 & HM) & HKP).
replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)) + (exv_sp E + e_d E - exv_s1 E)) with (exv_sp E + e_d E)
  in HJ1 by ring.
assert (HX' : forall a, exv_s1 E <= a < exv_sp E + e_d E ->
  ~ inFP [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8)] a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) (ms_mem ms) a).
{ intros a Ha Hn. apply HX; [zl | exact Hn]. }
destruct (KCX E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ k pos fx
  [(e_scr E, e_scr E + exv_len E + 1); (e_q E, e_q E + 8)] (STK_ex_string + (exv_sp E + e_d E - exv_s1 E))
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HP HBc HFP1 HJ2 HJ1 HX' (exvs_aregs_kept _ _ HP2) (fun r _ => eq_refl) HFZ
  (exv_room_eq Sc Sc S2 (exv_room_refl Sc) HSS) (fun H0 => HKP (HPM H0)) HHp HAB HLED2) as (HB2 & HKEEP).
(* the cursor's bytes after q + 8 and the spill 152(s1) are kept by the call *)
assert (WIN : forall a, e_q E + 8 <= a < e_q E + 40 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros a Ha. rewrite <- (MEQ a). apply HX'; [zl|]. intros (r & Hr & Hra). cbn [In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra; zl. }
assert (SP2 : exv_spill E W2 mem2 152 (e_v E)).
{ eapply exvs_vm2; [|exact HSP]. intros z Hz. cbn in Hz. rewrite (HKEEP z ltac:(zl)). apply MEQ. }
rewrite R1. exvs_pc_to 0x1d8.
revert HM. destruct (fst (fst (PjGrammar.jr_string (skipn (Nat.succ (Z.to_nat (exv_i1 E))) (e_x E)) [])))
  as [[s rest] |] eqn:HJS; intros HM; try rewrite HJS in HV0; cbv iota beta in HV0.
- (* ex_string read the string s *)
  destruct HM as (H10' & (c & Hsc & Hrest & Vq) & HBS2).
  destruct (exvs_string_dec _ _ _ HJS) as (c' & Hsc' & _ & Hcl & Hsl & Hnz).
  rewrite Hsc in Hsc'. injection Hsc' as <-.
  rewrite length_skipn in Hcl.
  assert (HPV : exv_len E - Z.of_nat (length rest) = exv_i1 E + Z.of_nat c + 2).
  { rewrite Hrest, !length_skipn. try unfold Nat.succ in *. unfold exv_len in *. zl. }
  assert (HLS : Z.of_nat (length s) < exv_len E) by (try unfold Nat.succ in *; unfold exv_len in *; zl).
  assert (CUR2 : prhex_cur (PA := PI_prog_B) W2 mem2 (e_q E) (e_x0 E + (exv_len E - Z.of_nat (length rest)))
    (e_x0 E + exv_len E)
    (e_dep E) (e_scr E) (e_dl E)).
  { apply (exvs_cur2 Wc W2 memc mem2 _ _ _ _ _ _ _ HC); [|exact WIN].
    rewrite HPV. replace (e_x0 E + (exv_i1 E + Z.of_nat c + 2)) with (e_x0 E + exv_i1 E + Z.of_nat c + 2) by ring.
    exact Vq. }
  destruct (Z.eq_dec (e_v E) 0) as [Hv0 | Hv0].
  + exact (exvs_z0 E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos (PjTree.JStr s) rest HEn HP HB2 HV0 Hv0 CUR2 H10' SP2).
  + exact (exvs_zv E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos s rest HEn HP HB2 HV0 Hv0 CUR2 HBS2 Hnz HLS H10' SP2).
- (* ex_string refused: in->p unchanged *)
  destruct HM as (H10' & HQS).
  apply (exvs_none E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos HEn HP HB2 HV0).
  + apply (exvs_cur2 Wc W2 memc mem2 _ _ _ _ _ _ _ HC); [|exact WIN].
    eapply exvs_vm2; [|exact CC1]. intros z Hz. cbn in Hz.
    etransitivity; [exact (HQS z ltac:(lia)) | apply MEQ].
  + exact H10'.
  + rewrite (exvs_aregs21 _ _ HP2), (HK 21%bv ltac:(cbn [In]; tauto)). exact H21.
Qed.
End f.

(* EXVD_STR: the string arm, from B 0x836fc to the exit cut, given CUT_CX at every float state *)
Lemma exvd_str_holds : forall n, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, EXVD_STR (fx := fx) B ARx SK n.
Proof.
intros n HCX fx. unfold EXVD_STR.
intros E lyc Sc Hpc Wc regs memc mdc k pos HEn HP HB HC Hi1 Hq H21 HSP.
exact (exvs_entry (fx := fx) n (HCX fx) E lyc Sc Hpc Wc regs memc mdc k pos HEn HP HB HC Hi1 Hq H21 HSP).
Qed.
End s.

Print Assumptions exvd_str_holds.

