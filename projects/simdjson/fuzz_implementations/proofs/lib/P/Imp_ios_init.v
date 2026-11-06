(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Export Layout.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_loc_get0 Pj_os_kit Exit Imp_ios_defs Imp_ios_iface
  Imp_iosbase F_uselocale F_cxa_guard F_cxa_atexit Imp_ios_sb Imp_ios_imbue.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.
Ltac retpc_lit := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n : word) by (apply bv_eq; vm_compute; reflexivity) end.

Definition F_DOIOSINIT : Z := 0x7b370.
Definition DOIOS_DEPTH : Z := 704.

Definition ios_cells64 : list cell := skipn 8 ios_cells.

Definition doiosinit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (canary : word) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(bv_unsigned sp + -704, bv_unsigned sp); (0xe7e78, 0xe85d8); (0xe85d8, 0xe9488); (0xe9d68, 0xe9d70)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (IOS + 64) ios_cells64
    /\ LOCB m' /\ locx m'
    /\ rw_cells psegs m' 0xe9d68 [C8 (Z_to_bv 64 0x10a060)]
    /\ ssp_cells m' canary.

Lemma doiosinit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (canary : word) (cdt thr sec : byte) (tm1 : word),
  stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - DOIOS_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^62) ->
  rw_cells psegs m (IOS + 64) [CB 1888 (repeat (Z_to_bv 8 0) 1888)] ->
  LOC0 m ->
  ios_img_facts m ->
  rw_cells psegs m 0x10a028 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells psegs m 0x10a100 [C4 (Z_to_bv 64 0)] ->
  rw_cells psegs m 0xe9d68 [C8 (Z_to_bv 64 0x10a060)] ->
  ssp_cells m canary ->
  tp = Z_to_bv 64 RTP ->
  mem_inv psegs m ->
  evt psegs (doiosinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_DOIOSINIT) fc None m (seg_rom psegs)).
Proof.
  intros until tm1. intros ST LO GLO SPHI IOSB L0 IMG LCH LK TPL SSP TPE MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_DOIOSINIT, DOIOS_DEPTH, GLOBALS_TOP, IOS in *. change (949816 + 64)%Z with 949880%Z in IOSB.
  destruct IMG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  destruct SSP as [SG SC]. unfold got_ssp, ssp_guard in SG, SC.
  pose proof (munch_refl [(bv_unsigned sp + -704, bv_unsigned sp); (0xe7e78, 0xe85d8); (0xe85d8, 0xe9488); (0xe9d68, 0xe9d70)]%Z m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  unfold LOC0, loc0_cells in L0.

  retype IOSB
    [CB 96 (repeat (Z_to_bv 8 0) 96); CB 96 (repeat (Z_to_bv 8 0) 96); CB 96 (repeat (Z_to_bv 8 0) 96); CB 96 (repeat (Z_to_bv 8 0) 96);
     CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 48 (repeat (Z_to_bv 8 0) 48); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4); CB 1 (repeat (Z_to_bv 8 0) 1); CB 1 (repeat (Z_to_bv 8 0) 1); CB 6 (repeat (Z_to_bv 8 0) 6);
     CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 48 (repeat (Z_to_bv 8 0) 48); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4); CB 1 (repeat (Z_to_bv 8 0) 1); CB 1 (repeat (Z_to_bv 8 0) 1); CB 6 (repeat (Z_to_bv 8 0) 6);
     CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 128 (repeat (Z_to_bv 8 0) 128); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 128 (repeat (Z_to_bv 8 0) 128); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 128 (repeat (Z_to_bv 8 0) 128); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4);
     CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 128 (repeat (Z_to_bv 8 0) 128); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 128 (repeat (Z_to_bv 8 0) 128); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 128 (repeat (Z_to_bv 8 0) 128); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4);
     CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 128 (repeat (Z_to_bv 8 0) 128); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4);
     CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 128 (repeat (Z_to_bv 8 0) 128); CB 8 (repeat (Z_to_bv 8 0) 8); CB 4 (repeat (Z_to_bv 8 0) 4); CB 4 (repeat (Z_to_bv 8 0) 4)].
  takeZ IOSB 1%nat 949976%Z SBCOUT. takeZ IOSB 1%nat 950072%Z SBCERR. takeZ IOSB 1%nat 950168%Z SBWCOUT. takeZ IOSB 1%nat 950264%Z SBWCERR. takeZ IOSB 11%nat 950368%Z SBCIN. takeZ IOSB 11%nat 950472%Z SBWCIN. takeZ IOSB 6%nat 950632%Z OCOUT. takeZ IOSB 6%nat 950792%Z OWCOUT. takeZ IOSB 6%nat 950952%Z OCERR. takeZ IOSB 6%nat 951112%Z OWCERR. takeZ IOSB 6%nat 951272%Z OCLOG. takeZ IOSB 6%nat 951432%Z OWCLOG. takeZ IOSB 7%nat 951600%Z OCIN. rename IOSB into OWCIN.
  carve_frame 96%nat ST.
  do 11 lstep.
  lstep. lstep. lstep. lstep.
  lstep. lstep.
  lstep. lstep.

  lstep.
  lstep. lstep. lstep.
  lstep.
  takeZ SBCIN 1%nat 950272%Z CINV. takeZ SBCIN 1%nat 950280%Z CINL.
  pose proof (proj1 (rw_cells_app psegs _ _ [C1 cdt; C1 thr; C1 sec] [C1 (Z_to_bv 8 0); C4 tm1]) LCH) as LCH3. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LCH3.
  pose proof (proj1 (proj1 (rw_cells_app psegs _ _ [C1 (Z_to_bv 8 0)] [C4 tm1]) (proj2 (proj1 (rw_cells_app psegs _ _ [C1 cdt; C1 thr; C1 sec] [C1 (Z_to_bv 8 0); C4 tm1]) LCH)))) as NL.
  lazymatch type of NL with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in NL end.
  call_sp (locale_ctor_spec0S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950272%Z _ canary);
    [exact ST | lia | lia | lia | exact L0 | exact CINL | lia | lia | exact SG | exact SC | exact NL | exact LK | assumption |].

  match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : LOCB _ |- _ => rename H into LBm end.
  match goal with H : locx _ |- _ => rename H into LX end.
  match goal with H : rw_cells psegs _ 950272 [C8 (Z_to_bv 64 0xe8bd8)] |- _ => rename H into CINL end.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp + -704, bv_unsigned sp); (0xe7e78, 0xe85d8); (0xe9d68, 0xe9d70)]%Z mm) as MU2;
    pose proof (wmono_refl psegs mm) as WM2 end.
  destruct LX as ((LX1 & LX2 & LX3) & LX4 & LX5 & LX6). unfold LOC_CVC, LOC_CVW, LOC_IDC, LOC_IDW, LOC_FAC4, VT_CVC, VT_CVW, CLOC in LX1, LX2, LX3, LX4, LX5, LX6.
  Ltac locx_now X1 X2 X3 X4 X5 X6 := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LX : locx mm) by (exact (conj (conj X1 (conj X2 X3)) (conj X4 (conj X5 X6)))) end.
  lstep.
  lstep. lstep. lstep.
  lstep.
  lstep. lstep. lstep.
  lstep.
  lstep. lstep. lstep.
  lstep.
  lstep.
  lstep.
  lstep. lstep.
  lstep.

  lazymatch goal with FRx : rw_cells _ _ _ (CB 16 ?jj :: ?post) |- _ =>
    apply (rw_cells_split_CB psegs _ _ [] 16 jj post [8; 8]%nat) in FRx; [|reflexivity]; cbn [mk_CB_cells app] in FRx; forget_junk FRx;
    takeZ FRx 1%nat (bv_unsigned sp + -88)%Z J0; takeZ FRx 1%nat (bv_unsigned sp + -80)%Z SLT; rename FRx into FSV end.
  call_sp (locale_copy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp + -88)%Z 950272%Z _); [exact CINL | exact SLT | lia | lia | lia | assumption |].
  try clear SLT. match goal with H : rw_cells psegs _ (bv_unsigned sp + -88) [C8 _] |- _ => rename H into SLT end.
  lstep. lstep.
  lstep. lstep.
  lstep.

  takeZ SBCIN 7%nat 950336%Z CINF. takeZ SBCIN 1%nat 950344%Z C72. takeZ SBCIN 1%nat 950352%Z CINST. takeZ SBCIN 1%nat 950356%Z C88.
  takeZ SBCIN 2%nat 950361%Z CINLC. takeZ SBCIN 1%nat 950362%Z C97.
  cells_sub G13 5%nat 1%nat 0xd6670%Z GIDC.
  locb_now LBm MU2 WM2. locx_now LX1 LX2 LX3 LX4 LX5 LX6.
  call_sp (imbue_c_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950264%Z (bv_unsigned sp + -88)%Z _ _ _);
    [exact ST | lia | unfold GLOBALS_TOP; lia | lia | exact LB | exact LX | exact SLT | lia | lia | exact C72 | exact C88 | exact C97 | lia | lia
    | exact GIDC | lia | exact G8 | unfold VTS_CVC_ENC; lia | exact TPE | exact TPL | assumption |].
  clear LB LX.
  match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 957800 _ |- _ => rename H into TPL end.
  Ltac norm_addr H := lazymatch type of H with rw_cells _ _ ?A _ => let v := eval vm_compute in A in change A with v in H end.
  match goal with H : rw_cells psegs _ (950264 + 72) _ |- _ => norm_addr H; unfold LOC_CVC in H; rename H into CINCV end.
  match goal with H : rw_cells psegs _ (950264 + 88) _ |- _ => norm_addr H; rename H into CINENC end.
  match goal with H : rw_cells psegs _ (950264 + 97) _ |- _ => norm_addr H; rename H into CINNC end.
  lstep. lstep.
  name_sp sp (-96)%Z.
  eapply evt_cut; [eapply locale_dtor_spec; [exact SLT| lia| assumption]|]. intros ms' (u0 & u1 & ->). try retpc_lit. unname_sp.

  lstep. lstep. lstep. lstep.
  lstep. lstep. lstep. lstep.
  lstep. lstep. lstep.
  lstep.

  takeZ OCIN 2%nat 951448%Z CINHD. takeZ OCIN 4%nat 951584%Z CINB.
  retype CINB [C8 (Z_to_bv 64 0xd3ca8); CB 128 (repeat (Z_to_bv 8 0) 128)].
  locb_now LBm MU2 WM2.
  call_sp (ios_base_init_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 951448%Z 950264%Z (Z_to_bv 64 0xd3ca8));
    [exact ST | lia | lia | exact LB | exact CINB | lia | lia | lia | lia | assumption |].
  clear LB. try clear CINB. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 951448 (iosb_cellsZ _ _) |- _ => rename H into CINB; unfold iosb_cellsZ, LOC_IMP in CINB; cbn [Z.ltb Z.b2z] in CINB end.

  lstep. lstep. lstep.
  lstep.
  lstep. lstep.
  lstep. lstep. lstep. lstep.
  lstep.
  cells_sub G8 1%nat 1%nat 0xd47e0%Z GNC.
  retype SBCOUT [CB 89 (repeat (Z_to_bv 8 0) 89); CB 7 (repeat (Z_to_bv 8 0) 7)]. takeZ SBCOUT 1%nat 949969%Z SBCOUT89.
  locb_now LBm MU2 WM2. locx_now LX1 LX2 LX3 LX4 LX5 LX6.
  call_sp (sbc_ctor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 949880%Z RSTDOUT 949828%Z _ _);
    [exact ST | lia | unfold GLOBALS_TOP; lia | lia | exact LB | exact LX | exact SBCOUT89 | exact SBCOUT | lia | lia | exact G12 | exact GIDC | exact GNC
    | unfold GOT_SBVT; lia | unfold GOT_IDC; lia | unfold VTS_CVC_NOCONV; lia | lia | lia | assumption |].
  clear LB LX. try clear SBCOUT89. try clear SBCOUT. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 949880 (sb_obj_cells _ _ _ _ _ ++ _) |- _ => rename H into COUTSB; unfold sb_obj_cells, LOC_IMP in COUTSB; cbn [app] in COUTSB end.
  lstep. lstep. lstep. lstep.
  lstep. lstep. lstep.
  lstep. lstep. lstep. lstep.
  takeZ OCOUT 1%nat 950480%Z COUTV. takeZ OCOUT 4%nat 950616%Z COUTB.
  retype COUTB [C8 (Z_to_bv 64 867576); CB 128 (repeat (Z_to_bv 8 0) 128)].
  locb_now LBm MU2 WM2.
  call_sp (ios_base_init_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950480%Z 949880%Z (Z_to_bv 64 867576));
    [exact ST | lia | lia | exact LB | exact COUTB | lia | lia | lia | lia | assumption |].
  clear LB. try clear COUTB. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 950480 (iosb_cellsZ _ _) |- _ => rename H into COUTB; unfold iosb_cellsZ, LOC_IMP in COUTB; cbn [Z.ltb Z.b2z] in COUTB end.

  lstep. lstep. lstep.
  lstep. lstep.
  lstep. lstep. lstep. lstep. lstep.
  retype SBCERR [CB 89 (repeat (Z_to_bv 8 0) 89); CB 7 (repeat (Z_to_bv 8 0) 7)]. takeZ SBCERR 1%nat 950065%Z SBCERR89.
  locb_now LBm MU2 WM2. locx_now LX1 LX2 LX3 LX4 LX5 LX6.
  call_sp (sbc_ctor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 949976%Z RSTDERR 949836%Z _ _);
    [exact ST | lia | unfold GLOBALS_TOP; lia | lia | exact LB | exact LX | exact SBCERR89 | exact SBCERR | lia | lia | exact G12 | exact GIDC | exact GNC
    | unfold GOT_SBVT; lia | unfold GOT_IDC; lia | unfold VTS_CVC_NOCONV; lia | lia | lia | assumption |].
  clear LB LX. try clear SBCERR89. try clear SBCERR. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 949976 (sb_obj_cells _ _ _ _ _ ++ _) |- _ => rename H into CERRSB; unfold sb_obj_cells, LOC_IMP in CERRSB; cbn [app] in CERRSB end.
  lstep. lstep. lstep.
  lstep. lstep. lstep. lstep.
  takeZ OCERR 1%nat 950800%Z CERRV. takeZ OCERR 4%nat 950936%Z CERRB.
  retype CERRB [C8 (Z_to_bv 64 867576); CB 128 (repeat (Z_to_bv 8 0) 128)].
  locb_now LBm MU2 WM2.
  call_sp (ios_base_init_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950800%Z 949976%Z (Z_to_bv 64 867576));
    [exact ST | lia | lia | exact LB | exact CERRB | lia | lia | lia | lia | assumption |].
  clear LB. try clear CERRB. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 950800 (iosb_cellsZ _ _) |- _ => rename H into CERRB; unfold iosb_cellsZ, LOC_IMP in CERRB; cbn [Z.ltb Z.b2z] in CERRB end.
  lstep. lstep.
  lstep. lstep.
  lstep. lstep. lstep.
  lstep.
  lstep. lstep. lstep.
  lstep. lstep. lstep.
  takeZ OCLOG 1%nat 951120%Z CLOGV. takeZ OCLOG 4%nat 951256%Z CLOGB.
  retype CLOGB [C8 (Z_to_bv 64 867576); CB 128 (repeat (Z_to_bv 8 0) 128)].
  locb_now LBm MU2 WM2.
  call_sp (ios_base_init_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 951120%Z 949976%Z (Z_to_bv 64 867576));
    [exact ST | lia | lia | exact LB | exact CLOGB | lia | lia | lia | lia | assumption |].
  clear LB. try clear CLOGB. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 951120 (iosb_cellsZ _ _) |- _ => rename H into CLOGB; unfold iosb_cellsZ, LOC_IMP in CLOGB; cbn [Z.ltb Z.b2z] in CLOGB end.

  lstep.
  lstep. lstep.
  lstep. lstep. lstep. lstep. lstep.
  lstep.
  lstep. lstep. lstep.
  lstep. lstep. lstep. lstep.
  lstep.
  lstep. lstep. lstep.
  lstep. lstep.
  lstep. lstep. lstep.
  lstep.
  takeZ SBWCIN 1%nat 950376%Z WCINV. takeZ SBWCIN 1%nat 950384%Z WCINL.
  locb_now LBm MU2 WM2.
  call_sp (locale_ctor_specS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950376%Z _);
    [exact ST | lia | lia | exact LB | exact WCINL | lia | lia | lia | assumption |].
  clear LB. try clear WCINL. try clear POST. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 950376 [C8 (Z_to_bv 64 0xe8bd8)] |- _ => rename H into WCINL end.

  lstep.
  lstep. lstep. lstep.
  lstep.
  lstep. lstep.
  lstep.
  lstep. lstep. lstep.
  lstep.
  lstep.
  lstep.
  lstep. lstep.
  lstep.
  destruct (rw_cells_forget psegs _ _ _ SLT) as [jslt SLT']. clear SLT. cbn [cells_size csize Nat.add] in SLT'.
  call_sp (locale_copy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (bv_unsigned sp + -88)%Z 950376%Z _); [exact WCINL | exact SLT' | lia | lia | lia | assumption |].
  try clear SLT'. match goal with H : rw_cells psegs _ (bv_unsigned sp + -88) [C8 _] |- _ => rename H into SLT end.
  lstep. lstep.
  lstep. lstep.
  lstep.
  takeZ SBWCIN 7%nat 950440%Z WCINF. takeZ SBWCIN 1%nat 950448%Z W72. takeZ SBWCIN 1%nat 950456%Z WCINST. takeZ SBWCIN 1%nat 950460%Z W88.
  takeZ SBWCIN 2%nat 950465%Z WCINLC. takeZ SBWCIN 1%nat 950466%Z W97.
  cells_sub G13 7%nat 1%nat 0xd6680%Z GIDW.
  locb_now LBm MU2 WM2. locx_now LX1 LX2 LX3 LX4 LX5 LX6.
  call_sp (imbue_w_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950368%Z (bv_unsigned sp + -88)%Z _ _ _);
    [exact ST | lia | unfold GLOBALS_TOP; lia | lia | exact LB | exact LX | exact SLT | lia | lia | exact W72 | exact W88 | exact W97 | lia | lia
    | exact GIDW | lia | exact G7 | unfold VTS_CVW_ENC; lia | exact TPE | exact TPL | assumption |].
  clear LB LX. try clear TPL. try clear W72; try clear W88; try clear W97.
  match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 957800 _ |- _ => rename H into TPL end.
  match goal with H : rw_cells psegs _ (950368 + 72) _ |- _ => norm_addr H; unfold LOC_CVW in H; rename H into WCINCV end.
  match goal with H : rw_cells psegs _ (950368 + 88) _ |- _ => norm_addr H; rename H into WCINENC end.
  match goal with H : rw_cells psegs _ (950368 + 97) _ |- _ => norm_addr H; rename H into WCINNC end.
  lstep. lstep.
  name_sp sp (-96)%Z.
  eapply evt_cut; [eapply locale_dtor_spec; [exact SLT| lia| assumption]|]. intros ms' (u2 & u3 & ->). try retpc_lit. unname_sp.

  lstep. lstep. lstep. lstep.
  lstep. lstep. lstep. lstep.
  lstep. lstep. lstep.
  lstep.
  takeZ OWCIN 2%nat 951616%Z WCINHD. takeZ OWCIN 4%nat 951752%Z WCINB.
  retype WCINB [C8 (Z_to_bv 64 867784); CB 128 (repeat (Z_to_bv 8 0) 128)].
  locb_now LBm MU2 WM2.
  call_sp (ios_base_init_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 951616%Z 950368%Z (Z_to_bv 64 867784));
    [exact ST | lia | lia | exact LB | exact WCINB | lia | lia | lia | lia | assumption |].
  clear LB. try clear WCINB. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 951616 (iosb_cellsZ _ _) |- _ => rename H into WCINB; unfold iosb_cellsZ, LOC_IMP in WCINB; cbn [Z.ltb Z.b2z] in WCINB end.

  lstep.
  lstep. lstep.
  lstep. lstep. lstep. lstep.
  lstep.
  cells_sub G7 1%nat 1%nat 0xd4530%Z GWNC. cells_sub G13 2%nat 1%nat 0xd6658%Z GWV.
  retype SBWCOUT [CB 89 (repeat (Z_to_bv 8 0) 89); CB 7 (repeat (Z_to_bv 8 0) 7)]. takeZ SBWCOUT 1%nat 950161%Z SBWCOUT89.
  locb_now LBm MU2 WM2. locx_now LX1 LX2 LX3 LX4 LX5 LX6.
  call_sp (sbw_ctor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950072%Z RSTDOUT 949852%Z _ _);
    [exact ST | lia | unfold GLOBALS_TOP; lia | lia | exact LB | exact LX | exact SBWCOUT89 | exact SBWCOUT | lia | lia | exact GWV | exact GIDW | exact GWNC
    | unfold GOT_WSBVT; lia | unfold GOT_IDW; lia | unfold VTS_CVW_NOCONV; lia | lia | lia | assumption |].
  clear LB LX. try clear SBWCOUT89. try clear SBWCOUT. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 950072 (sb_obj_cells _ _ _ _ _ ++ _) |- _ => rename H into WCOUTSB; unfold sb_obj_cells, LOC_IMP in WCOUTSB; cbn [app] in WCOUTSB end.
  lstep. lstep. lstep. lstep.
  lstep. lstep. lstep.
  lstep. lstep. lstep. lstep.
  takeZ OWCOUT 1%nat 950640%Z WCOUTV. takeZ OWCOUT 4%nat 950776%Z WCOUTB.
  retype WCOUTB [C8 (Z_to_bv 64 867864); CB 128 (repeat (Z_to_bv 8 0) 128)].
  locb_now LBm MU2 WM2.
  call_sp (ios_base_init_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950640%Z 950072%Z (Z_to_bv 64 867864));
    [exact ST | lia | lia | exact LB | exact WCOUTB | lia | lia | lia | lia | assumption |].
  clear LB. try clear WCOUTB. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 950640 (iosb_cellsZ _ _) |- _ => rename H into WCOUTB; unfold iosb_cellsZ, LOC_IMP in WCOUTB; cbn [Z.ltb Z.b2z] in WCOUTB end.

  lstep. lstep.
  lstep. lstep. lstep. lstep. lstep.
  retype SBWCERR [CB 89 (repeat (Z_to_bv 8 0) 89); CB 7 (repeat (Z_to_bv 8 0) 7)]. takeZ SBWCERR 1%nat 950257%Z SBWCERR89.
  locb_now LBm MU2 WM2. locx_now LX1 LX2 LX3 LX4 LX5 LX6.
  call_sp (sbw_ctor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950168%Z RSTDERR 949860%Z _ _);
    [exact ST | lia | unfold GLOBALS_TOP; lia | lia | exact LB | exact LX | exact SBWCERR89 | exact SBWCERR | lia | lia | exact GWV | exact GIDW | exact GWNC
    | unfold GOT_WSBVT; lia | unfold GOT_IDW; lia | unfold VTS_CVW_NOCONV; lia | lia | lia | assumption |].
  clear LB LX. try clear SBWCERR89. try clear SBWCERR. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 950168 (sb_obj_cells _ _ _ _ _ ++ _) |- _ => rename H into WCERRSB; unfold sb_obj_cells, LOC_IMP in WCERRSB; cbn [app] in WCERRSB end.
  lstep. lstep. lstep.
  lstep. lstep. lstep. lstep.
  takeZ OWCERR 1%nat 950960%Z WCERRV. takeZ OWCERR 4%nat 951096%Z WCERRB.
  retype WCERRB [C8 (Z_to_bv 64 867864); CB 128 (repeat (Z_to_bv 8 0) 128)].
  locb_now LBm MU2 WM2.
  call_sp (ios_base_init_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 950960%Z 950168%Z (Z_to_bv 64 867864));
    [exact ST | lia | lia | exact LB | exact WCERRB | lia | lia | lia | lia | assumption |].
  clear LB. try clear WCERRB. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 950960 (iosb_cellsZ _ _) |- _ => rename H into WCERRB; unfold iosb_cellsZ, LOC_IMP in WCERRB; cbn [Z.ltb Z.b2z] in WCERRB end.
  lstep. lstep.
  lstep. lstep.
  lstep. lstep. lstep.
  lstep.
  lstep. lstep. lstep.
  lstep. lstep. lstep.
  takeZ OWCLOG 1%nat 951280%Z WCLOGV. takeZ OWCLOG 4%nat 951416%Z WCLOGB.
  retype WCLOGB [C8 (Z_to_bv 64 867864); CB 128 (repeat (Z_to_bv 8 0) 128)].
  locb_now LBm MU2 WM2.
  call_sp (ios_base_init_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo 951280%Z 950168%Z (Z_to_bv 64 867864));
    [exact ST | lia | lia | exact LB | exact WCLOGB | lia | lia | lia | lia | assumption |].
  clear LB. try clear WCLOGB. match goal with H : stk psegs _ lo _ |- _ => rename H into ST end.
  match goal with H : rw_cells psegs _ 951280 (iosb_cellsZ _ _) |- _ => rename H into WCLOGB; unfold iosb_cellsZ, LOC_IMP in WCLOGB; cbn [Z.ltb Z.b2z] in WCLOGB end.

  lstep.
  lstep. lstep.
  lstep. lstep. lstep. lstep. lstep.
  lstep.
  lstep. lstep. lstep.
  lstep. lstep. lstep.
  lstep. lstep. lstep.

  do 10 lstep.
  lstep.

  glueZ SLT FSV. glueZ J0 SLT. release_frame J0 ST (bv_unsigned sp).
  lstep.
  locb_now LBm MU2 WM2. locx_now LX1 LX2 LX3 LX4 LX5 LX6.

  glueZ COUTSB CERRSB. glueZ COUTSB WCOUTSB. glueZ COUTSB WCERRSB. glueZ COUTSB CINV. glueZ COUTSB CINL. glueZ COUTSB CINF. glueZ COUTSB CINCV. glueZ COUTSB CINST. glueZ COUTSB CINENC. glueZ COUTSB CINLC. glueZ COUTSB CINNC. glueZ COUTSB SBCIN. glueZ COUTSB WCINV. glueZ COUTSB WCINL. glueZ COUTSB WCINF. glueZ COUTSB WCINCV. glueZ COUTSB WCINST. glueZ COUTSB WCINENC. glueZ COUTSB WCINLC. glueZ COUTSB WCINNC. glueZ COUTSB SBWCIN. glueZ COUTSB COUTV. glueZ COUTSB COUTB. glueZ COUTSB OCOUT. glueZ COUTSB WCOUTV. glueZ COUTSB WCOUTB. glueZ COUTSB OWCOUT. glueZ COUTSB CERRV. glueZ COUTSB CERRB. glueZ COUTSB OCERR. glueZ COUTSB WCERRV. glueZ COUTSB WCERRB. glueZ COUTSB OWCERR. glueZ COUTSB CLOGV. glueZ COUTSB CLOGB. glueZ COUTSB OCLOG. glueZ COUTSB WCLOGV. glueZ COUTSB WCLOGB. glueZ COUTSB OWCLOG. glueZ COUTSB CINHD. glueZ COUTSB CINB. glueZ COUTSB OCIN. glueZ COUTSB WCINHD. glueZ COUTSB WCINB. glueZ COUTSB OWCIN.

  let cs64 := eval cbv in ios_cells64 in
  lazymatch type of COUTSB with rw_cells _ _ _ ?cs => let n := eval vm_compute in (length cs) in retype_at COUTSB 0%nat n cs64 end;
  change cs64 with ios_cells64 in COUTSB.
  apply evt_done. unfold doiosinit_post. sys_finish.
  split; assumption.
Qed.
