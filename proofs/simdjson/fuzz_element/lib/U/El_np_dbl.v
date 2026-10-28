(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import SoftFloat FmtFp FmtFpDig FmtFpTail FmtFp6 FmtFpNf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memcmp Pj_steps Pj_loc_defs Pj_loc_kit Pj_os_defs Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Printf_lib Printf_mlib F_printf_iface F_vsnprintf Printf_pieces Printf_sn F_fmt_fp_sn El_snl El_fmt_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_os_defs El_ins_iface El_os_xsputn El_os_pad El_np_wgi El_np_wgf.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.
Ltac lit_reg e := let v := eval vm_compute in e in replace e with v by (vm_compute; reflexivity).
Ltac lit_words := repeat match goal with |- context [zext 64 ?x] =>
  let v := eval vm_compute in (bv_unsigned (zext 64 x)) in
  replace (zext 64 x) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end.

Notation NPD_DEPTH := 6176%Z (only parsing).
Definition FMT_g : list Z := [37; 46; 42; 103; 0]%Z.

Lemma OUTFP_sn_g : forall y txt n, fmt_fp_total [] y 0 6 0 CHR_g = Some (txt, n) -> zlength txt = n -> (0 <= n <= 80)%Z ->
  OUTFP_sn y 0 6 0 CHR_g [] = ITree.Ret (Exc.Ok (n, txt)).
Proof.
  intros y txt n HF HL HN. unfold OUTFP_sn. rewrite (mbind_eq mget _ [] [] []) by reflexivity.
  rewrite HF. unfold SN_CAP. rewrite HL. change (zlength (@nil Z)) with 0%Z.
  replace ((0 <=? n) && (n <=? 80))%Z with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
  rewrite (mbind_eq (mput txt) _ [] tt txt) by reflexivity. reflexivity.
Qed.

Lemma printf_model_g : forall y txt n, fmt_fp_total [] y 0 6 0 CHR_g = Some (txt, n) -> zlength txt = n -> (0 <= n <= 80)%Z ->
  printf_model OUT_sn OUTFP_sn FMT_g [PA_i 6; PA_g y] [] = ITree.Ret (Exc.Ok (n, txt)).
Proof.
  intros y txt n HF HL HN.
  unfold printf_model, FMT_g. lazy -[OUTFP_sn OUT_sn mbind mret munr].
  rewrite (mbind_eq (OUT_sn []) _ [] tt []) by (apply OUT_sn_eq; discriminate).
  rewrite (mbind_mbind_eq (OUTFP_sn y 0 6 0 103) _ _ [] n txt) by (apply OUTFP_sn_g; assumption).
  change ((cnt <- (if ((n <? 0) || (PrintfModel.INT_MAX - 0 <? n))%Z then munr else mret (0 + n)%Z) ;; mret cnt) txt = ITree.Ret (Exc.Ok (n, txt))).
  replace ((n <? 0) || (PrintfModel.INT_MAX - 0 <? n))%Z with false
    by (symmetry; apply orb_false_intro; apply Z.ltb_ge; unfold PrintfModel.INT_MAX; lia).
  rewrite mbind_mret. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma fpcalls_g : forall d, fpcalls_sn_ok FMT_g [PA_i 6; PA_g (f128_of_d d)].
Proof.
  intros d. unfold fpcalls_sn_ok. intros. lazy -[fpcall_stmt SINK_sn TOPOK_sn OUTFP_sn SN_CAP f128_of_d].
  apply Forall_cons; [| apply Forall_nil]. apply sn_fpcall; lia.
Qed.

Lemma gchb_zb : forall txt, Forall noxc txt -> Forall gchb (zb txt).
Proof.
  intros txt H. unfold zb. apply Forall_map. eapply Forall_impl; [|exact H].
  intros c [Rc Hc]. unfold gchb. rewrite Z_to_bv_small; [exact Hc|]. unfold bv_modulus. cbn. lia.
Qed.

Definition np_d_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo OS fill : Z) (j148 j284 : list byte) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) pb (pp ep : Z) dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168); (0xef558, 0xef558 + 8)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k)
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells usegs m' OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) /\ PUTINV OS pp ep
    /\ rw_cells usegs m' (OS + 136) (ios_cellsX OS 0xd6928 0x1002 0 fill j148 j284)
    /\ rw_cells usegs m' 0xef558 [C8 (Z_to_bv 64 0x10f850)]
    /\ LOCB m'.

Definition np_d_stmt_if (P : word -> Prop) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill pp ep : Z) (dw pb : word) (dum j148 j284 : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - NPD_DEPTH)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  tp = Z_to_bv 64 (0xef558 + 48) ->
  rw_cells usegs m OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep ->
  rw_cells usegs m (OS + 136) (ios_cellsX OS 0xd6928 0x1002 0 fill j148 j284) ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z ->
  (0 <= fill < 256)%Z -> reg_get F (Z_to_bv 5 10) = dw -> P dw ->
  rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] -> ssp_cells m canary -> frm0 fc ->
  LOCB m -> el_dcc m -> mem_inv usegs m ->
  evt usegs (np_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS fill j148 j284 canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_NP_D) fc None m (seg_rom usegs)).

Definition DFIN (dw : word) : Prop := dword_fin (bv_unsigned dw).
Definition np_d_stmt : Prop := np_d_stmt_if (fun _ => True).

Local Ltac dlia := first [lia | left; lia | right; lia | right; left; lia | right; right; lia].

Theorem np_d_proof : np_d_stmt.
Proof.
  unfold np_d_stmt, np_d_stmt_if. intros until canary. intros ST LO LOLO SPH TP SB PI IOS RO RO2 AL8 RF HDW FIN TPC SSP FRM LB DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (bv_unsigned_in_range 64 dw) as RDW. unfold bv_modulus in RDW. cbn in RDW.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168); (0xef558, 0xef558 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cells in LBC.
  unfold sb_cells in SB. unfold ios_cellsX in IOS.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

  assert (RL : ro_cells usegs m 0x10e76 [CB 1 [Z_to_bv 8 0]])
    by (apply (ro_cells_image usegs m 0x10e76 [Z_to_bv 8 0] MI); [vm_compute; reflexivity | lia | cbn; lia]).
  do 3 lstep.
  carve_frame 240%nat ST.
  do 14 lstep.
  do 3 lstep.
  lstep.
  lit_words.
  do 3 lstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 136 ?x :: _) => set (jq := x) in FR; clearbody jq end.
  retype_at FR 1%nat 1%nat [CB 8 [Z_to_bv 8 37; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  lstep.
  replace (zx32 (Z_to_bv 64 4098)) with (Z_to_bv 64 4098) in * by (apply bv_eq; vm_compute; reflexivity).
  lit_reg (bv_unsigned (Z_to_bv 64 4098) ≪ 52)%Z.
  if_false.
  do 2 lstep.
  lstep.
  if_false.
  do 3 lstep.
  lstep.
  if_true.
  do 6 lstep.
  lstep.
  lit_words.
  lstep.
  lstep.
  if_false.
  do 5 lstep.
  lstep.
  if_false.
  lstep.
  lstep.
  if_true.
  lstep.
  lstep.
  if_true.
  lstep.
  if_true.
  lstep.
  lstep.
  do 2 lstep.
  do 2 lstep.
  lstep.
  if_false.
  lstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 96 ?x :: _) => set (jl := x) in FR; clearbody jl end.
  lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: CB 32 ?x :: _) => set (jn := x) in FR; clearbody jn end.
  retype_at FR 3%nat 5%nat [CB 8 [Z_to_bv 8 37; Z_to_bv 8 46; Z_to_bv 8 42; Z_to_bv 8 103; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  retype_at IOS 3%nat 1%nat [C4 (Z_to_bv 64 6); C4 (Z_to_bv 64 0)].
  lstep.
  replace (sx32 (Z_to_bv 64 6)) with (Z_to_bv 64 6) by (vm_compute; reflexivity).
  retype_at IOS 3%nat 2%nat [C8 (Z_to_bv 64 6)].
  do 5 lstep.
  lstep.

  takeZ FR 2%nat (bv_unsigned sp + -136)%Z FRA.
  takeZ FR 1%nat (bv_unsigned sp + -104)%Z NARC. takeZ FR 1%nat (bv_unsigned sp + -96)%Z FMT8.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_cut3 mm (bv_unsigned sp + -136)%Z 32 jn 2 30 ltac:(lia) ltac:(lia) ltac:(lia) NARC) as (jg & jnar & j0 & GAP & NAR & _) end.
  clear NARC. change (Z.to_nat 2) with 2%nat in GAP. change (Z.to_nat 30) with 30%nat in NAR.
  replace (bv_unsigned sp + -136 + 2)%Z with (bv_unsigned sp + -134)%Z in NAR by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (FMTB : bytes_at usegs mm (bv_unsigned sp + -104) (zb FMT_g)) end.
  { pose proof (rw_cells_bytes_at _ _ _ _ FMT8) as B. cbn [cells_bytes cbytes app] in B.
    pose proof (bytes_at_sub _ _ _ 0 5 B ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as B5. cbv [firstn skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in B5.
    replace (bv_unsigned sp + -104 + 0)%Z with (bv_unsigned sp + -104)%Z in B5 by lia. exact B5. }

  destruct (fmt_fp_total_g6 (bv_unsigned dw)) as (txt & nc & HF & HL & HNC & HG).
  pose proof (printf_model_g _ _ _ HF HL ltac:(lia)) as MODEL.
  call_sp (snl_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fc _
             (bv_unsigned sp + -134)%Z 30%Z 0x22008%Z (bv_unsigned sp + -104)%Z 30%nat jnar FMT_g [PA_i 6; PA_g (f128_of_d (bv_unsigned dw))] lo canary nc txt);
    [ reflexivity | reflexivity | reflexivity | reflexivity | exact TP | lia | exact TPC | exact NAR | exact FMTB
    | unfold FMT_g; repeat (apply Forall_cons; [lia|]); apply Forall_nil
    | vm_compute; reflexivity
    | intros m_; cbn [args_ok arg_ok]; split; [split; [lia | rewrite unsigned_lit by lia; reflexivity] | split; [rewrite <- HDW; reflexivity | exact I]]
    | exact MODEL
    | apply fpcalls_g
    | rewrite <- (Nat2Z.id (length txt)); change (Z.of_nat (length txt)) with (zlength txt); rewrite HL; lia | lia | lia | exact ST | lia | unfold GLOBALS_TOP; lia | lia
    | split; [exact SSP1 | exact SSP2] | assumption | exact FRM
    | lia | change (zlength FMT_g) with 5%Z; lia | change (zlength FMT_g) with 5%Z; lia | lia | lia | ].
  rename PC into FRM1. rename PC0 into FOK. rename PC1 into ST. rename PC2 into SSP. rename PC3 into NARO. rename POST into TPC1. rename MI0 into MI.
  clear SSP1 SSP2 MODEL FMTB. destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  do 2 lstep.
  rewrite lts_small by lia. replace (29 <? nc)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. try if_true.
  do 4 lstep.
  lit_words. replace (zx32 (Z_to_bv 64 4098)) with (Z_to_bv 64 4098) in * by (apply bv_eq; vm_compute; reflexivity).
  do 5 lstep.
  lit_reg (Z.land (bv_unsigned (Z_to_bv 64 4098)) 176)%Z.
  if_false.
  lstep.
  lstep.
  if_true.
  lstep.
  do 2 lstep.
  bru true.
  do 4 lstep.
  lstep.
  carve_frame 16%nat ST.
  do 9 lstep.
  if_true.
  do 4 lstep.
  release_frame FR0 ST (bv_unsigned sp + -240)%Z.

  apply (rw_cells_split_CB usegs _ _ [CB 8 (firstn 8 jl); C8 (Z_to_bv 64 EL_IMP)] 80 (skipn 16 jl) [C8 (Z_to_bv 64 (bv_unsigned sp + -134))] [8; 8; 7; 57]%nat) in FRA; [|reflexivity].
  cbn [mk_CB_cells app] in FRA. forget_junk FRA.
  takeZ FRA 1%nat (bv_unsigned sp + -232)%Z F0. takeZ FRA 1%nat (bv_unsigned sp + -224)%Z PLOC.
  takeZ FRA 1%nat (bv_unsigned sp + -216)%Z POE. takeZ FRA 1%nat (bv_unsigned sp + -208)%Z POP.
  takeZ FRA 1%nat (bv_unsigned sp + -201)%Z GAP7. takeZ FRA 1%nat (bv_unsigned sp + -144)%Z OBUF. rename FRA into NBP.

  apply (rw_cells_split_CB usegs _ _ [] 30 _ [] [Z.to_nat nc; Z.to_nat (30 - nc)]%nat) in NARO; [|cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in NARO.
  assert (LZT : length (zb txt) = Z.to_nat nc) by (unfold zb; rewrite length_map; unfold zlength in HL; lia).
  rewrite firstn_app, LZT, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in NARO by lia.
  destruct (rw_cells_split_n usegs _ _ _ 1 (bv_unsigned sp + -134 + nc)%Z NARO ltac:(cbn [firstn cells_size csize]; lia)) as [SRC NREST]. clear NARO.
  cbn [firstn skipn] in SRC, NREST. forget_junk NREST.
  do 7 lstep.
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ ?fcx _ _ _) =>
  call_sp (wgf_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fcx _ lo
             (bv_unsigned sp + -134)%Z (bv_unsigned sp + -134)%Z (bv_unsigned sp + -134 + nc)%Z (bv_unsigned sp + -201)%Z 57%Z
             (bv_unsigned sp + -216)%Z (bv_unsigned sp + -224)%Z (bv_unsigned sp + -232)%Z (zb txt) _ _ _) end;
    [ exact ST | lia | lia
    | replace (bv_unsigned sp + -134 + nc - (bv_unsigned sp + -134))%Z with nc by lia; exact SRC
    | apply gchb_zb; exact HG
    | lia | lia | lia | exact OBUF | exact POP | exact POE | exact PLOC
    | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia
    | dlia | dlia | dlia | dlia | dlia | dlia
    | do 15 eexists; exact LBC
    | exact DCC' || (split; [exact VT | split; [exact WS | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]])
    | assumption | ].
  rename MI0 into MI. rename PC into ST. rename PC0 into OBUF. rename PC1 into POP. rename PC2 into POE. rename POST into LB.
  destruct LB as (k1 & k2 & k3 & k4 & k5 & k6 & k7 & k8 & k9 & k10 & k11 & k12 & k13 & k14 & k15 & LBC2). unfold locb_cells in LBC2.
  do 2 lstep.
  lstep.
  if_true.
  do 6 lstep.
  lstep.
  lazymatch type of OBUF with rw_cells _ ?mm _ [CB _ ?jb] =>
    assert (LJB : length jb = 57%nat) by (destruct OBUF as [[[LJ _] _] _]; exact LJ);
    pose proof (rw_cells_bytes_at _ _ _ _ OBUF) as OBB; cbn [cells_bytes cbytes app] in OBB; rewrite app_nil_r in OBB;
    pose proof (bytes_at_sub mm _ _ 0 nc OBB ltac:(lia) ltac:(lia) ltac:(rewrite LJB; lia)) as OBS;
    replace (bv_unsigned sp + -201 + 0)%Z with (bv_unsigned sp + -201)%Z in OBS by lia; clear OBB end.
  call_sp (os_pad_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo OS (bv_unsigned sp + -201)%Z
             (bv_unsigned sp + -134 + nc - (bv_unsigned sp + -134))%Z (bv_unsigned sp + -134 - (bv_unsigned sp + -134))%Z 0%Z 0x1002%Z fill pp ep);
    [ exact ST | lia | lia | exact SB | exact PI | exact IOS | lia | lia | exact AL8 | exact OBS | rewrite firstn_length_le by (rewrite length_skipn, LJB; lia); lia
    | lia | lia | lia | dlia | lia | lia | lia | exact VT | assumption | ].
  try clear OBS. rename MI0 into MI. rename PC into ST. rename PC0 into SB. rename PC1 into PI'. rename POST into IOS.
  lstep.
  lstep.
  if_true.
  lstep.
  if_true.
  do 15 lstep.

  change (Z.to_nat 57) with 57%nat in OBUF.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (rw_cells_glue usegs mm _ _ _ _ SRC NREST ltac:(cbn [cells_size csize]; lia)) as NARB;
    destruct (rw_cells_forget usegs mm _ _ NARB) as [jnar2 NAR2]; clear NARB SRC NREST end.
  cbn [cells_size csize app] in NAR2.
  replace (Z.to_nat nc + (Z.to_nat (30 - nc) + 0))%nat with 30%nat in NAR2
    by (rewrite Nat.add_0_r, <- Z2Nat.inj_add by lia; replace (nc + (30 - nc))%Z with 30%Z by lia; reflexivity).
  glueZ F0 PLOC. glueZ F0 POE. glueZ F0 POP. glueZ F0 GAP7. glueZ F0 OBUF. glueZ F0 NBP. glueZ F0 GAP. glueZ F0 NAR2. glueZ F0 FMT8. glueZ F0 FR.
  release_frame F0 ST (bv_unsigned sp).
  unfold np_d_post. sys_finish.
  -
    intros k Hk. destruct (Z.eq_dec (bv_unsigned k) 8) as [E8|N8].
    + replace k with (Z_to_bv 5 8 : reg) by (apply bv_eq; rewrite E8; reflexivity). apply freg_get_same. reflexivity.
    + rewrite freg_get_other; [| apply (proj2 (Z.eqb_neq _ _)); apply not_eq_sym; exact N8].
      rewrite (FOK k Hk). rewrite freg_get_other; [reflexivity | apply (proj2 (Z.eqb_neq _ _)); apply not_eq_sym; exact N8].
  - split; [exact SSP1 | exact SSP2].
  - exact SB.
  - exact PI'.
  - do 15 eexists; exact LBC2.
Qed.
