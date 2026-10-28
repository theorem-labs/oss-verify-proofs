(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memcmp Pj_steps Pj_loc_defs Pj_loc_kit Pj_os_defs Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Printf_lib Printf_mlib F_printf_iface F_vsnprintf Printf_pieces Printf_sn El_snl El_fmt_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import El_os_defs El_os_xsputn El_os_pad El_np_wgi.
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

Notation NP_DEPTH := 6096%Z (only parsing).

Lemma printf_model_lu : forall u, (0 <= u < 2^64)%Z ->
  printf_model OUT_sn OUTFP_sn FMT_lu [PA_z u] [] = ITree.Ret (Exc.Ok (ulen u, concat (upieces u))).
Proof.
  intros u Hu. pose proof (ulen_bound u).
  rewrite (printf_model_sn FMT_lu [PA_z u] ([] :: upieces u) (ulen u) (printf_pieces_lu u Hu)); cbn [concat app].
  - reflexivity.
  - change (concat ([] :: upieces u)) with (concat (upieces u)). rewrite concat_upieces. unfold SN_CAP. lia.
Qed.

Definition np_ul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
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

Definition np_ul_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill u pp ep : Z) (pb : word) (dum j148 j284 : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - NP_DEPTH)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  tp = Z_to_bv 64 (0xef558 + 48) ->
  rw_cells usegs m OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep ->
  rw_cells usegs m (OS + 136) (ios_cellsX OS 0xd6928 0x1002 0 fill j148 j284) ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z ->
  (0 <= fill < 256)%Z -> (0 <= u < 2^64)%Z ->
  rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] -> ssp_cells m canary -> frm0 fc ->
  LOCB m -> el_dcc m -> mem_inv usegs m ->
  evt usegs (np_ul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS fill j148 j284 canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 u) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_NP_UL) fc None m (seg_rom usegs)).

Theorem np_ul_proof : np_ul_stmt.
Proof.
  unfold np_ul_stmt. intros until canary. intros ST LO LOLO SPH TP SB PI IOS RO RO2 AL8 RF RU TPC SSP FRM LB DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168); (0xef558, 0xef558 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cells in LBC.
  unfold sb_cells in SB. unfold ios_cellsX in IOS.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

  assert (RL : ro_cells usegs m 0x11640 [CB 2 [Z_to_bv 8 108; Z_to_bv 8 0]])
    by (apply (ro_cells_image usegs m 0x11640 [Z_to_bv 8 108; Z_to_bv 8 0] MI); [vm_compute; reflexivity | lia | cbn; lia]).
  do 3 lstep.
  carve_frame 160%nat ST.
  do 12 lstep.
  lstep.
  replace (sx32 (Z_to_bv 64 4098)) with (Z_to_bv 64 4098) by (vm_compute; reflexivity).
  do 3 lstep.
  retype_at FR 1%nat 1%nat [CB 8 [Z_to_bv 8 37; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  lstep.
  if_false.
  do 2 lstep.
  lit_words.
  lstep.
  if_false.
  do 2 lstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 96 ?x :: _) => set (jq := x) in FR; clearbody jq end.
  lstep.
  lit_words.
  do 3 lstep.
  lstep.
  if_false.
  do 2 lstep.
  lstep.
  if_false.
  lstep.
  lstep.
  if_true.
  lstep.
  lstep.
  do 3 lstep.
  lstep.
  lstep.
  if_false.
  do 6 lstep.
  lstep.

  retype_at FR 1%nat 4%nat [CB 8 [Z_to_bv 8 37; Z_to_bv 8 108; Z_to_bv 8 117; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  takeZ FR 1%nat (bv_unsigned sp + -64)%Z FRA. takeZ FR 1%nat (bv_unsigned sp + -56)%Z FMT8.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_cut3 mm (bv_unsigned sp + -160)%Z 96 jq 72 24 ltac:(lia) ltac:(lia) ltac:(lia) FRA) as (jl & jn & j0 & LOCALS & NAR & _) end.
  clear FRA. change (Z.to_nat 72) with 72%nat in LOCALS. change (Z.to_nat 24) with 24%nat in NAR.
  replace (bv_unsigned sp + -160 + 72)%Z with (bv_unsigned sp + -88)%Z in NAR by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (FMTB : bytes_at usegs mm (bv_unsigned sp + -64) (zb FMT_lu)) end.
  { pose proof (rw_cells_bytes_at' _ _ _ _ FMT8) as B. cbn [cells_bytes cbytes app] in B.
    pose proof (bytes_at_sub _ _ _ 0 4 B ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as B4. cbv [firstn skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in B4.
    replace (bv_unsigned sp + -64 + 0)%Z with (bv_unsigned sp + -64)%Z in B4 by lia. exact B4. }
  pose proof (printf_model_lu u RU) as MODEL. pose proof (ulen_bound u) as UL. pose proof (concat_upieces u) as CU.
  call_sp (snl_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _
             (bv_unsigned sp + -88)%Z 24%Z 0x22008%Z (bv_unsigned sp + -64)%Z 24%nat jn FMT_lu [PA_z u] lo canary (ulen u) (concat (upieces u)));
    [ reflexivity | reflexivity | reflexivity | reflexivity | exact TP | lia | exact TPC | exact NAR | exact FMTB
    | unfold FMT_lu; repeat (apply Forall_cons; [lia|]); apply Forall_nil
    | apply pass1_ok_lu
    | intros m'; cbn [args_ok arg_ok]; split; [apply unsigned_lit; lia | exact I]
    | exact MODEL
    | apply fpcalls_sn_ok_nil; apply fp_calls_lu
    | unfold zlength in CU; lia | lia | lia | exact ST | lia | unfold GLOBALS_TOP; lia | lia | split; [exact SSP1 | exact SSP2] | assumption | exact FRM
    | lia | change (zlength FMT_lu) with 4%Z; lia | change (zlength FMT_lu) with 4%Z; lia | lia | lia | ].
  rename PC into FRM'. rename PC0 into FOK. rename PC1 into ST. rename PC2 into SSP'. rename PC3 into NAR'. rename POST into TPC'.
  clear SSP1 SSP2 MODEL. destruct SSP' as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  lstep.
  lit_words.
  do 4 lstep.
  lstep.
  if_false.
  lstep.
  lstep.
  if_true.
  lstep.
  do 2 lstep.
  lstep.
  carve_frame 16%nat ST.
  do 9 lstep.
  if_true.
  do 4 lstep.
  release_frame FR0 ST (bv_unsigned sp + -160)%Z.

  apply (rw_cells_split_CB usegs _ _ [C8 (Z_to_bv 64 EL_IMP)] 64 (skipn 8 jl) [] [8; 8; 3; 45]%nat) in LOCALS; [|reflexivity].
  cbn [mk_CB_cells app] in LOCALS. forget_junk LOCALS.
  takeZ LOCALS 1%nat (bv_unsigned sp + -152)%Z PLOC. takeZ LOCALS 1%nat (bv_unsigned sp + -144)%Z POE.
  takeZ LOCALS 1%nat (bv_unsigned sp + -136)%Z POP. takeZ LOCALS 1%nat (bv_unsigned sp + -133)%Z GAP. rename LOCALS into OBUF.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_prefix mm (bv_unsigned sp + -88)%Z 24 _ (bv_unsigned sp + -88 + ulen u - (bv_unsigned sp + -88))%Z NAR' ltac:(lia) ltac:(cbn; lia)) as [src SRCN] end.
  do 7 lstep.
  lstep.
  set (E2 := (bv_unsigned sp + -160)%Z) in |- *. unfold E2 at 2.
  call_sp (wgi_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo
             (bv_unsigned sp + -88)%Z (bv_unsigned sp + -88)%Z (bv_unsigned sp + -88 + ulen u)%Z (bv_unsigned sp + -133)%Z 45%Z
             (bv_unsigned sp + -144)%Z (bv_unsigned sp + -152)%Z E2);
    [ exact ST | lia | lia | exact SRCN | lia | lia | exact OBUF | exact POP | exact POE | exact PLOC
    | lia | lia | lia | lia | lia | lia | lia | lia | subst E2; lia | subst E2; lia | lia | lia | lia | lia
    | do 15 eexists; exact LBC
    | split; [exact VT | split; [exact WS | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]
    | assumption | ].
  subst E2. clear SRCN.
  rename PC into ST. rename PC0 into OBUF. rename PC1 into POP. rename PC2 into POE. rename POST into LB.
  destruct LB as (l1' & l2' & l3' & l4' & l5' & l6' & l7' & l8' & l9' & l10' & l11' & l12' & l13' & l14' & l15' & LBC'). unfold locb_cells in LBC'.
  do 2 lstep.
  lstep.
  if_true.
  do 6 lstep.
  lstep.
  lazymatch type of OBUF with rw_cells _ ?mm _ [CB _ ?jb] =>
    assert (LJB : length jb = 45%nat) by (destruct OBUF as [[[LJ _] _] _]; exact LJ);
    pose proof (rw_cells_bytes_at _ _ _ _ OBUF) as OBB; cbn [cells_bytes cbytes app] in OBB; rewrite app_nil_r in OBB;
    pose proof (bytes_at_sub mm _ _ 0 (bv_unsigned sp + -88 + ulen u - (bv_unsigned sp + -88))%Z OBB ltac:(lia) ltac:(lia) ltac:(rewrite LJB; lia)) as OBS;
    replace (bv_unsigned sp + -133 + 0)%Z with (bv_unsigned sp + -133)%Z in OBS by lia; clear OBB end.
  call_sp (os_pad_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo OS (bv_unsigned sp + -133)%Z
             (bv_unsigned sp + -88 + ulen u - (bv_unsigned sp + -88))%Z (bv_unsigned sp + -88 - (bv_unsigned sp + -88))%Z 0%Z 0x1002%Z fill pp ep);
    [ exact ST | lia | lia | exact SB | exact PI | exact IOS | lia | lia | exact AL8 | exact OBS | rewrite firstn_length_le by (rewrite length_skipn, LJB; lia); lia
    | lia | lia | lia | lia | lia | lia | lia | exact VT | assumption | ].
  try clear OBS. rename PC into ST. rename PC0 into SB. rename PC1 into PI'. rename POST into IOS.
  do 9 lstep.

  change (Z.to_nat 45) with 45%nat in OBUF.
  glueZ PLOC POE. glueZ PLOC POP. glueZ PLOC GAP. glueZ PLOC OBUF. glueZ PLOC NAR'. glueZ PLOC FMT8. glueZ PLOC FR.
  release_frame PLOC ST (bv_unsigned sp).
  unfold np_ul_post. sys_finish; [split; [exact SSP1 | exact SSP2] | exact SB | exact PI' | do 15 eexists; exact LBC'].
Qed.

Definition FLX (hex : bool) : Z := if hex then 0x1008 else 0x1002.
Definition WX (hex : bool) : Z := if hex then 4 else 0.
Definition CCX (hex : bool) : Z := if hex then 120 else 100.
Definition FMTX (hex : bool) : list Z := if hex then FMT_lx else FMT_ld.
Definition ARGX (hex : bool) (v : Z) : list parg := if hex then [PA_z v] else [PA_l v].
Definition LENX (hex : bool) (v : Z) : Z := if hex then xlen v else llen v.
Definition OUTX (hex : bool) (v : Z) : list Z := if hex then concat (xpieces v) else concat (lpieces v).
Definition VOK (hex : bool) (v : Z) : Prop := if hex then (0 <= v < 2^64)%Z else (-2^63 <= v < 2^63)%Z.

Lemma concat_lpieces : forall v, zlength (concat (lpieces v)) = llen v.
Proof.
  intros v. unfold lpieces, llen. destruct (v =? 0); [reflexivity|]. destruct (v <? 0); cbn [concat app]; rewrite ?app_nil_r; [|reflexivity].
  unfold zlength. cbn [length]. lia.
Qed.
Lemma llen_bound : forall v, (-2^63 <= v < 2^63)%Z -> (1 <= llen v <= 21)%Z.
Proof.
  intros v Hv. unfold llen. pose proof (dec_digits_zlength (labs v)). destruct (Z.eqb_spec v 0) as [->|NZ]; [lia|].
  pose proof (labs_range v Hv). assert (NE0 : labs v <> 0%Z) by (unfold labs; destruct (Z.ltb_spec v 0); lia).
  pose proof (dec_digits_nz (labs v) ltac:(lia)) as NE.
  destruct (dec_digits (labs v)); [contradiction | unfold zlength in *; cbn in *; destruct (v <? 0); lia].
Qed.
Lemma LENX_facts : forall hex v, VOK hex v -> (1 <= LENX hex v <= 21)%Z /\ zlength (OUTX hex v) = LENX hex v.
Proof.
  intros [|] v Hv; unfold VOK, LENX, OUTX in *.
  - split; [pose proof (xlen_bound v); lia | apply concat_xpieces].
  - split; [apply llen_bound; exact Hv | apply concat_lpieces].
Qed.
Lemma printf_model_lX : forall hex v, VOK hex v ->
  printf_model OUT_sn OUTFP_sn (FMTX hex) (ARGX hex v) [] = ITree.Ret (Exc.Ok (LENX hex v, OUTX hex v)).
Proof.
  intros hex v Hv. destruct (LENX_facts hex v Hv) as [LB CL]. destruct hex; unfold VOK, FMTX, ARGX, LENX, OUTX in *.
  - rewrite (printf_model_sn FMT_lx [PA_z v] ([] :: xpieces v) (xlen v) (printf_pieces_lx v Hv)); [reflexivity|].
    change (concat ([] :: xpieces v)) with (concat (xpieces v)). rewrite CL. unfold SN_CAP. lia.
  - rewrite (printf_model_sn FMT_ld [PA_l v] ([] :: lpieces v) (llen v) (printf_pieces_ld v Hv)); [reflexivity|].
    change (concat ([] :: lpieces v)) with (concat (lpieces v)). rewrite CL. unfold SN_CAP. lia.
Qed.

Ltac join_reg k v pcj :=
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let R' := eval cbv beta iota delta [tset] in (tset p v R) in
    apply (evt_cut segs (fun ms => ms = MS R' F (Z_to_bv 64 pcj) fc rv m ro))
  end.

Definition np_l_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo OS FL W fill : Z) (j148 j284 : list byte) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) pb (pp ep : Z) dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168); (0xef558, 0xef558 + 8)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k)
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells usegs m' OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) /\ PUTINV OS pp ep
    /\ rw_cells usegs m' (OS + 136) (ios_cellsX OS 0xd6928 FL 0 fill j148 j284)
    /\ rw_cells usegs m' 0xef558 [C8 (Z_to_bv 64 0x10f850)]
    /\ LOCB m'.

Definition np_l_stmt : Prop :=
  forall (hex : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill v pp ep : Z) (pb : word) (dum j148 j284 : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - NP_DEPTH)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  tp = Z_to_bv 64 (0xef558 + 48) ->
  rw_cells usegs m OS (sb_cells pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep ->
  rw_cells usegs m (OS + 136) (ios_cellsX OS 0xd6928 (FLX hex) (WX hex) fill j148 j284) ->
  (bv_unsigned sp <= OS)%Z -> (OS + 288 < 2^62)%Z -> (OS mod 8 = 0)%Z ->
  (0 <= fill < 256)%Z -> VOK hex v ->
  rw_cells usegs m 0xef558 [C8 (Z_to_bv 64 0x10f850)] -> ssp_cells m canary -> frm0 fc ->
  LOCB m -> el_dcc m -> mem_inv usegs m ->
  evt usegs (np_l_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo OS (FLX hex) (WX hex) fill j148 j284 canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 v) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_NP_L) fc None m (seg_rom usegs)).

Theorem np_l_proof : np_l_stmt.
Proof.
  unfold np_l_stmt. intros until canary. intros ST LO LOLO SPH TP SB PI IOS RO RO2 AL8 RF RV TPC SSP FRM LB DCC MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (RPP : (0 <= pp < 2^62 /\ 0 <= ep < 2^62)%Z) by (destruct PI as [[-> ->]|[-> ?]]; lia).
  pose proof (munch_refl [(lo, bv_unsigned sp); (OS + 40, OS + 128); (OS + 160, OS + 168); (0xef558, 0xef558 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cells in LBC.
  unfold sb_cells in SB. unfold ios_cellsX in IOS.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  assert (RL : ro_cells usegs m 0x11640 [CB 2 [Z_to_bv 8 108; Z_to_bv 8 0]])
    by (apply (ro_cells_image usegs m 0x11640 [Z_to_bv 8 108; Z_to_bv 8 0] MI); [vm_compute; reflexivity | lia | cbn; lia]).

  pose proof (printf_model_lX hex v RV) as MODEL. destruct (LENX_facts hex v RV) as [UL CU].
  assert (PASS1 : pass1_ok (FMTX hex) = true) by (destruct hex; vm_compute; reflexivity).
  assert (FPC : fpcalls_sn_ok (FMTX hex) (ARGX hex v)) by (apply fpcalls_sn_ok_nil; destruct hex; vm_compute; reflexivity).
  assert (LF4 : zlength (FMTX hex) = 4%Z) by (destruct hex; reflexivity).
  assert (FALL : Forall (fun c => 0 <= c < 256)%Z (FMTX hex)) by (destruct hex; unfold FMTX, FMT_lx, FMT_ld; repeat (apply Forall_cons; [lia|]); apply Forall_nil).
  assert (ARGOK : forall m' (w5 : word), args_ok 0 0 0 m' lo (bv_unsigned sp + -160 - 80) 0 [Z_to_bv 64 v; w5; a6; a7] (ARGX hex v)).
  { intros m' w5. unfold VOK in RV. destruct hex; cbn [ARGX args_ok arg_ok]; (split; [|exact I]).
    - apply unsigned_lit; lia.
    - split; [lia|]. apply unsigned_lit_wrap. }
  assert (FLR : (0 <= FLX hex < 2^31)%Z) by (destruct hex; cbv; split; congruence).
  assert (WR : (0 <= WX hex <= 4)%Z) by (destruct hex; cbv; split; congruence).
  assert (ZBF : zb (FMTX hex) = [Z_to_bv 8 37; Z_to_bv 8 108; Z_to_bv 8 (CCX hex); Z_to_bv 8 0]) by (destruct hex; reflexivity).
  set (fmt := FMTX hex) in *. set (args := ARGX hex v) in *. set (len := LENX hex v) in *. set (outb := OUTX hex v) in *.
  set (Wv := WX hex) in *. set (FLv := FLX hex) in *.
  do 3 lstep.
  carve_frame 160%nat ST.
  do 12 lstep.
  lstep.
  replace (sx32 (Z_to_bv 64 FLv)) with (Z_to_bv 64 FLv)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  do 2 lstep.
  retype_at FR 1%nat 1%nat [CB 8 [Z_to_bv 8 37; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  do 2 lstep.
  lstep.
  br_is true ltac:(subst FLv; destruct hex; vm_compute; reflexivity).
  lstep.
  lstep.
  br_is true ltac:(subst FLv; destruct hex; vm_compute; reflexivity).
  lstep.
  lit_words.
  lstep.
  if_false.
  do 2 lstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 96 ?x :: _) => set (jq := x) in FR; clearbody jq end.
  lstep.
  lit_words.
  do 3 lstep.
  lstep.
  if_false.
  do 2 lstep.
  lstep.
  br_is false ltac:(subst FLv; destruct hex; vm_compute; reflexivity).
  lstep.
  lstep.

  join_reg 10%Z (Z_to_bv 64 (CCX hex)) 0x8db68%Z.
  { subst FLv. destruct hex.
    - bru false. do 4 lstep.
      match goal with |- context [Z_to_bv 64 (?e + 120)%Z] => lit_reg (e + 120)%Z end.
      lstep.
      apply evt_done. reflexivity.
    - bru true. lstep.
      apply evt_done. reflexivity. }
  intros ms' ->.
  lstep.
  sbZ.
  do 3 lstep.
  lstep.
  lstep.
  if_false.
  do 6 lstep.
  lstep.

  retype_at FR 1%nat 4%nat [CB 8 [Z_to_bv 8 37; Z_to_bv 8 108; Z_to_bv 8 (CCX hex); Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
  takeZ FR 1%nat (bv_unsigned sp + -64)%Z FRA. takeZ FR 1%nat (bv_unsigned sp + -56)%Z FMT8.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_cut3 mm (bv_unsigned sp + -160)%Z 96 jq 72 24 ltac:(lia) ltac:(lia) ltac:(lia) FRA) as (jl & jn & j0 & LOCALS & NAR & _) end.
  clear FRA. change (Z.to_nat 72) with 72%nat in LOCALS. change (Z.to_nat 24) with 24%nat in NAR.
  replace (bv_unsigned sp + -160 + 72)%Z with (bv_unsigned sp + -88)%Z in NAR by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (FMTB : bytes_at usegs mm (bv_unsigned sp + -64) (zb fmt)) end.
  { pose proof (rw_cells_bytes_at' _ _ _ _ FMT8) as B. cbn [cells_bytes cbytes app] in B.
    pose proof (bytes_at_sub _ _ _ 0 4 B ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as B4. cbv [firstn skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in B4.
    replace (bv_unsigned sp + -64 + 0)%Z with (bv_unsigned sp + -64)%Z in B4 by lia. rewrite ZBF. exact B4. }
  call_sp (snl_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _
             (bv_unsigned sp + -88)%Z 24%Z 0x22008%Z (bv_unsigned sp + -64)%Z 24%nat jn fmt args lo canary len outb);
    [ reflexivity | reflexivity | reflexivity | reflexivity | exact TP | lia | exact TPC | exact NAR | exact FMTB
    | exact FALL
    | exact PASS1
    | intros mq; apply ARGOK
    | exact MODEL
    | exact FPC
    | unfold zlength in CU; lia | lia | lia | exact ST | lia | unfold GLOBALS_TOP; lia | lia | split; [exact SSP1 | exact SSP2] | assumption | exact FRM
    | lia | rewrite LF4; lia | rewrite LF4; lia | lia | lia | ].
  rename PC into FRM'. rename PC0 into FOK. rename PC1 into ST. rename PC2 into SSP'. rename PC3 into NAR'. rename POST into TPC'.
  clear SSP1 SSP2 MODEL. destruct SSP' as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  lstep.
  lit_words.
  do 4 lstep.
  lstep.
  br_is false ltac:(subst FLv; destruct hex; vm_compute; reflexivity).
  lstep.
  lstep.
  br_is true ltac:(subst FLv; destruct hex; vm_compute; reflexivity).
  lstep.
  do 2 lstep.
  lstep.
  carve_frame 16%nat ST.
  do 9 lstep.
  if_true.
  do 4 lstep.
  release_frame FR0 ST (bv_unsigned sp + -160)%Z.

  apply (rw_cells_split_CB usegs _ _ [C8 (Z_to_bv 64 EL_IMP)] 64 (skipn 8 jl) [] [8; 8; 3; 45]%nat) in LOCALS; [|reflexivity].
  cbn [mk_CB_cells app] in LOCALS. forget_junk LOCALS.
  takeZ LOCALS 1%nat (bv_unsigned sp + -152)%Z PLOC. takeZ LOCALS 1%nat (bv_unsigned sp + -144)%Z POE.
  takeZ LOCALS 1%nat (bv_unsigned sp + -136)%Z POP. takeZ LOCALS 1%nat (bv_unsigned sp + -133)%Z GAP. rename LOCALS into OBUF.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (rw_cells_CB_prefix mm (bv_unsigned sp + -88)%Z 24 _ (bv_unsigned sp + -88 + len - (bv_unsigned sp + -88))%Z NAR' ltac:(lia) ltac:(cbn; lia)) as [src SRCN] end.
  do 7 lstep.
  lstep.
  set (E2 := (bv_unsigned sp + -160)%Z) in |- *. unfold E2 at 2.
  call_sp (wgi_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo
             (bv_unsigned sp + -88)%Z (bv_unsigned sp + -88)%Z (bv_unsigned sp + -88 + len)%Z (bv_unsigned sp + -133)%Z 45%Z
             (bv_unsigned sp + -144)%Z (bv_unsigned sp + -152)%Z E2);
    [ exact ST | lia | lia | exact SRCN | lia | lia | exact OBUF | exact POP | exact POE | exact PLOC
    | lia | lia | lia | lia | lia | lia | lia | lia | subst E2; lia | subst E2; lia | lia | lia | lia | lia
    | do 15 eexists; exact LBC
    | split; [exact VT | split; [exact WS | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]
    | assumption | ].
  subst E2. clear SRCN.
  rename PC into ST. rename PC0 into OBUF. rename PC1 into POP. rename PC2 into POE. rename POST into LB.
  destruct LB as (l1' & l2' & l3' & l4' & l5' & l6' & l7' & l8' & l9' & l10' & l11' & l12' & l13' & l14' & l15' & LBC'). unfold locb_cells in LBC'.
  do 2 lstep.
  lstep.
  if_true.
  do 6 lstep.
  lstep.
  lazymatch type of OBUF with rw_cells _ ?mm _ [CB _ ?jb] =>
    assert (LJB : length jb = 45%nat) by (destruct OBUF as [[[LJ _] _] _]; exact LJ);
    pose proof (rw_cells_bytes_at _ _ _ _ OBUF) as OBB; cbn [cells_bytes cbytes app] in OBB; rewrite app_nil_r in OBB;
    pose proof (bytes_at_sub mm _ _ 0 (bv_unsigned sp + -88 + len - (bv_unsigned sp + -88))%Z OBB ltac:(lia) ltac:(lia) ltac:(rewrite LJB; lia)) as OBS;
    replace (bv_unsigned sp + -133 + 0)%Z with (bv_unsigned sp + -133)%Z in OBS by lia; clear OBB end.
  call_sp (os_pad_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo OS (bv_unsigned sp + -133)%Z
             (bv_unsigned sp + -88 + len - (bv_unsigned sp + -88))%Z (bv_unsigned sp + -88 - (bv_unsigned sp + -88))%Z Wv FLv fill pp ep);
    [ exact ST | lia | lia | exact SB | exact PI | exact IOS | lia | lia | exact AL8 | exact OBS | rewrite firstn_length_le by (rewrite length_skipn, LJB; lia); lia
    | lia | lia | lia | lia | lia | lia | lia | exact VT | assumption | ].
  try clear OBS. rename PC into ST. rename PC0 into SB. rename PC1 into PI'. rename POST into IOS.
  do 9 lstep.

  change (Z.to_nat 45) with 45%nat in OBUF.
  glueZ PLOC POE. glueZ PLOC POP. glueZ PLOC GAP. glueZ PLOC OBUF. glueZ PLOC NAR'. glueZ PLOC FMT8. glueZ PLOC FR.
  release_frame PLOC ST (bv_unsigned sp).
  unfold np_l_post. subst fmt args len outb Wv FLv. sys_finish; [split; [exact SSP1 | exact SSP2] | exact SB | exact PI' | do 15 eexists; exact LBC'].
Qed.
