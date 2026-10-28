(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image RzCPS FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export FX_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Printf_mlib F_printf_iface F_vsnprintf Printf_pieces Printf_sn El_fmt_facts.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_m2s I_consts I_qck D_kit D_clx RT_iface RT_iface2 RT_iface3 F_achk Fe_icalls Fe_printf_iface Fe_vsnprintf I_pchead I_vprintfw I_pcfmt6 I_vfsn6 I_vsn6 Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_defsA Pj_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import El_snlA El_np_wgiA El_os_xsputnLA El_os_padA El_os_padWA El_ins_ifaceA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
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

Notation NP_DEPTH := 10608%Z (only parsing).

Lemma printf_model_lu : forall u, (0 <= u < 2^64)%Z ->
  printf_model OUT_sn OUTFP_sn FMT_lu [PA_z u] [] = ITree.Ret (Exc.Ok (ulen u, concat (upieces u))).
Proof.
  intros u Hu. pose proof (ulen_bound u). pose proof (concat_upieces u) as CU.
  pose proof (printf_model_sn FMT_lu [PA_z u] ([] :: upieces u) (ulen u) (printf_pieces_lu u Hu)) as X.
  cbn [concat app] in X. change (concat ([] :: upieces u)) with (concat (upieces u)) in *.
  specialize (X ltac:(rewrite CU; unfold F_printf_iface.SN_CAP; lia)). exact X.
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
  - pose proof (printf_model_sn FMT_lx [PA_z v] ([] :: xpieces v) (xlen v) (printf_pieces_lx v Hv)) as X.
    change (concat ([] :: xpieces v)) with (concat (xpieces v)) in *. specialize (X ltac:(rewrite CL; unfold F_printf_iface.SN_CAP; lia)). exact X.
  - pose proof (printf_model_sn FMT_ld [PA_l v] ([] :: lpieces v) (llen v) (printf_pieces_ld v Hv)) as X.
    change (concat ([] :: lpieces v)) with (concat (lpieces v)) in *. specialize (X ltac:(rewrite CL; unfold F_printf_iface.SN_CAP; lia)). exact X.
Qed.

Ltac join_reg k v pcj :=
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let R' := eval cbv beta iota delta [tset] in (tset p v R) in
    apply (evt_cut segs (fun ms => ms = MS R' F (Z_to_bv 64 pcj) fc rv m ro))
  end.

Definition np_afacts (lo q : Z) (m : mem) : Prop :=
  ictx m /\ (forall p n', lo <= p -> p + n' <= q -> chkr m p n')%Z /\ rod_chk m /\ rod_chk_fp m /\ ifx_real m /\ pctx m /\ pfcells6 m.
Definition np_zone (x : Z) : Prop := ((x < 0x6abdb8 \/ 0x6abdc0 <= x < 0x6ce000) \/ (SHADOW_LO <= x < SHADOW_HI))%Z.

Lemma np_afacts_munch : forall W lo q lo' q' m m', np_afacts lo q m -> munch W m m' -> wmono bsegs m m' -> (lo <= lo')%Z -> (q' <= q)%Z ->
  (forall x, np_zone x -> outside W x) -> np_afacts lo' q' m'.
Proof.
  intros W lo q lo' q' m m' (IC & STKC & (R1 & R2 & R3) & (F1 & F2 & F3 & F4 & F5 & F6) & IFX & PC & (PF & RV)) MU WM Hlo Hq HW.
  assert (SH : forall x, (SHADOW_LO <= x < SHADOW_HI)%Z -> outside W x) by (intros x Hx; apply HW; right; exact Hx).
  assert (LOWZ : forall x, (x < 0x6abdb8)%Z -> outside W x) by (intros x Hx; apply HW; left; left; exact Hx).
  Local Ltac ck H MU SH := apply (chkr_munch _ _ _ _ _ H MU SH).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (ictx_munch W m m' IC MU WM). intros x Hx. apply LOWZ. cbn [in_rl ICR] in Hx. lia.
  - intros p n' Hp Hn. apply (chkr_munch W m m' p n' (STKC p n' ltac:(lia) ltac:(lia)) MU SH).
  - split; [ck R1 MU SH| split; [ck R2 MU SH| ck R3 MU SH]].
  - split; [ck F1 MU SH| split; [ck F2 MU SH| split; [ck F3 MU SH| split; [ck F4 MU SH| split; [ck F5 MU SH| ck F6 MU SH]]]]].
  - apply (ro_cells_agree bsegs m m' _ _ IFX). apply (agree_of_munch W m m' _ MU). intros x Hx. apply LOWZ. cbn [cells_size csize Nat.add] in Hx. lia.
  - apply (pctx_munch W m m' PC MU WM). intros x Hx. apply LOWZ. unfold in_PCR in Hx. lia.
  - split.
    + apply (pfcells_munch W m m' PF MU WM). intros x Hx. apply LOWZ. unfold in_PFR in Hx. lia.
    + apply (ro_cells_agree bsegs m m' _ _ RV). apply (agree_of_munch W m m' _ MU). intros x Hx. apply LOWZ. cbn [cells_size csize Nat.add] in Hx. lia.
Qed.

Lemma pcok2_l : forall c (a : parg) m slots A VA lo r o,
  (c = 100 \/ c = 117 \/ c = 120)%Z ->
  printf_model OUT_sn OUTFP_sn [37; 108; c; 0]%Z [a] [] = ITree.Ret (Exc.Ok (r, o)) -> (0 <= r)%Z -> r = zlength o -> (r < 2^31 - 1)%Z ->
  (0 <= VA)%Z -> (VA + 16 < 2^63)%Z -> pctx m -> pfcells6 m ->
  PCOK2_el [37; 108; c; 0]%Z [a] slots A VA lo m.
Proof.
  intros c a m slots A VA lo r o Hc MODEL R0 RL RH V0 V1 PC PF. split.
  - split; [exists [37; 108; c]%Z; split; [left; exists c; split; [exact Hc| reflexivity]| reflexivity]|].
    split; [exact V0|]. split; [exact V1|]. split; [exact PC| exact PF].
  - intros r' o' E. rewrite MODEL in E. injection E as <- <-. lia.
Qed.

Definition np1_post (RET : Z) (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo OS fill LEN : Z) (canary ra s0 s1 s2 s3 s4 s5 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (ob jf : list byte) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 fill) (Z_to_bv 64 (OS + 136))
                  (Z_to_bv 64 OS) (Z_to_bv 64 (bv_unsigned sp + -133)) (Z_to_bv 64 (bv_unsigned sp + -133)) (Z_to_bv 64 (bv_unsigned sp + -133 + LEN))
                  (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) a6 a7
                  (Z_to_bv 64 OS) (Z_to_bv 64 (bv_unsigned sp + -88 + LEN)) (Z_to_bv 64 (bv_unsigned sp + -88)) (Z_to_bv 64 0x6aa7f0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (Z_to_bv 64 0xb19a4) fc' None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (0x6abdb8, 0x6abdb8 + 8)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k)
    /\ stk bsegs m' lo (bv_unsigned sp + -160)
    /\ ssp_cells m' canary
    /\ rw_cells bsegs m' 0x6abdb8 [C8 (Z_to_bv 64 0x6cc0b0)] /\ LOCBA m'
    /\ (0 <= LEN <= 21)%Z /\ length ob = Z.to_nat LEN /\ bytes_at bsegs m' (bv_unsigned sp + -133) ob
    /\ rw_cells bsegs m' (bv_unsigned sp + -160) [CB 104 jf]
    /\ rw_cells bsegs m' (bv_unsigned sp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition np_ul_seg1_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill u : Z) (j148 j284 : list byte) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - NP_DEPTH)%Z -> (0x6ce000 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  tp = Z_to_bv 64 (0x6abdb8 + 48) ->
  rw_cells bsegs m (OS + 136) (ios_cellsX OS 0x168e58 0x1002 0 fill j148 j284) ->
  (0x6ce000 <= OS)%Z -> (OS + 288 <= lo)%Z ->
  (0 <= fill < 256)%Z -> (0 <= u < 2^64)%Z ->
  rw_cells bsegs m 0x6abdb8 [C8 (Z_to_bv 64 0x6cc0b0)] -> ssp_cells m canary -> frm0 fc ->
  LOCBA m -> el_dccA m -> mem_inv bsegs m ->
  (bv_unsigned sp mod 16 = 0)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> np_afacts lo (bv_unsigned sp) m ->
  evt bsegs (np1_post 0x11d6dc sp gp tp s6 s7 s8 s9 s10 s11 F lo OS fill (ulen u) canary ra s0 s1 s2 s3 s4 s5 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 u) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_NP_UL) fc None m (seg_rom bsegs)).

Section Seg1.
Hypothesis RIP : rip_stmt.

Theorem np_ul_seg1 : np_ul_seg1_stmt.
Proof using RIP.
  unfold np_ul_seg1_stmt. intros until canary. intros ST LO LOLO SPH TP IOS OLO RO RF RU TPC SSP FRM LB DCC MI SP16 HSH AF0.
  assert (SP16' : ((bv_unsigned sp + -160) mod 16 = 0)%Z) by (clear - SP16; Z.div_mod_to_equations; lia).
  assert (ZONE : forall x, np_zone x -> outside [(lo, bv_unsigned sp); (0x6abdb8, 0x6abdb8 + 8)]%Z x).
  { intros x Hx. unfold np_zone, SHADOW_LO, SHADOW_HI, kHighShadowEnd in *. cbn [outside]. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(lo, bv_unsigned sp); (0x6abdb8, 0x6abdb8 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & WS2 & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  unfold ios_cellsX in IOS.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.

  assert (RL : ro_cells bsegs m 0x1741a [CB 2 [Z_to_bv 8 108; Z_to_bv 8 0]])
    by (apply (ro_cells_image bsegs m 0x1741a [Z_to_bv 8 108; Z_to_bv 8 0] MI); [vm_compute; reflexivity | lia | cbn; lia]).
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
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (FMTB : bytes_at bsegs mm (bv_unsigned sp + -64) (zb FMT_lu)) end.
  { pose proof (rw_cells_bytes_at' _ _ _ _ FMT8) as B. cbn [cells_bytes cbytes app] in B.
    pose proof (bytes_at_sub _ _ _ 0 4 B ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as B4. cbv [firstn skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in B4.
    replace (bv_unsigned sp + -64 + 0)%Z with (bv_unsigned sp + -64)%Z in B4 by lia. exact B4. }
  pose proof (printf_model_lu u RU) as MODEL. pose proof (ulen_bound u) as UL. pose proof (concat_upieces u) as CU.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (np_afacts_munch _ lo (bv_unsigned sp) lo (bv_unsigned sp) m mm AF0 MU WM ltac:(lia) ltac:(lia) ZONE) as (IC1 & STKC1 & ROD1 & RODFP1 & IFX1 & PCTX1 & PF1) end.
  call_sp (snl_proof RIP PCOK2_el (ivsn_proof RIP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _
             (bv_unsigned sp + -88)%Z 24%Z 0x33380%Z (bv_unsigned sp + -64)%Z 24%nat jn FMT_lu [PA_z u] lo canary (ulen u) (concat (upieces u)));
    [ reflexivity | reflexivity | reflexivity | reflexivity | exact TP | lia | exact TPC | exact NAR | exact FMTB
    | unfold FMT_lu; repeat (apply Forall_cons; [lia|]); apply Forall_nil
    | apply pass1_ok_lu
    | intros m'; cbn [args_ok arg_ok]; split; [apply unsigned_lit; lia | exact I]
    | exact MODEL
    | apply fpcalls_sn_ok_nil; apply fp_calls_lu
    | unfold zlength in CU; lia | lia | lia | exact ST | lia | unfold GLOBALS_TOP; lia | lia | split; [exact SSP1 | exact SSP2] | assumption | exact FRM
    | lia | change (zlength FMT_lu) with 4%Z; lia | change (zlength FMT_lu) with 4%Z; lia | lia | lia
    | lia | exact SP16' | exact HSH | exact IC1
    | intros p n' Hp Hn; apply STKC1; lia
    | apply STKC1; [lia| change (zlength FMT_lu) with 4%Z; lia]
    | exact ROD1
    | apply STKC1; [lia| unfold zlength in CU |- *; lia]
    | right; unfold SHADOW_HI, kHighShadowEnd in *; lia
    | exact RODFP1 | exact IFX1
    | intros m' MU' WM'; apply (pcok2_l 117 (PA_z u) m' _ _ _ lo (ulen u) (concat (upieces u))); [lia| exact MODEL| lia| unfold zlength in CU |- *; lia| lia| lia| lia| |];
      [ apply (pctx_munch _ _ m' PCTX1 MU' WM'); intros x Hx; unfold in_PCR in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia
      | destruct PF1 as [PF1a PF1b]; split;
        [ apply (pfcells_munch _ _ m' PF1a MU' WM'); intros x Hx; unfold in_PFR in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia
        | apply (ro_cells_agree bsegs _ m' _ _ PF1b); apply (agree_of_munch _ _ m' _ MU'); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia ] ]
    | ].
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

  apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 EL_IMP)] 64 (skipn 8 jl) [] [8; 8; 3; 45]%nat) in LOCALS; [|reflexivity].
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
    | split; [exact VT | split; [exact WS | split; [exact WS2 | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]]
    | assumption | ].
  subst E2. clear SRCN.
  rename PC into ST. rename PC0 into OBUF. rename PC1 into POP. rename PC2 into POE. rename POST into LB.
  destruct LB as (l1' & l2' & l3' & l4' & l5' & l6' & l7' & l8' & l9' & l10' & l11' & l12' & l13' & l14' & l15' & LBC'). unfold locb_cellsA, PJ_LOC_LO_A in LBC'.
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

  replace (bv_unsigned sp + -133 + (bv_unsigned sp + -88 - (bv_unsigned sp + -88)))%Z with (bv_unsigned sp + -133)%Z by lia.
  replace (bv_unsigned sp + -133 + (bv_unsigned sp + -88 + ulen u - (bv_unsigned sp + -88)))%Z with (bv_unsigned sp + -133 + ulen u)%Z by lia.
  replace (bv_unsigned sp + -88 + ulen u - (bv_unsigned sp + -88))%Z with (ulen u) in OBS by lia.
  lazymatch type of OBS with context [skipn (Z.to_nat 0) ?l] => change (skipn (Z.to_nat 0) l) with l in OBS end.
  change (Z.to_nat 45) with 45%nat in OBUF.
  glueZ PLOC POE. glueZ PLOC POP. glueZ PLOC GAP. glueZ PLOC OBUF. glueZ PLOC NAR'. glueZ PLOC FMT8.
  destruct (rw_cells_forget bsegs _ _ _ PLOC) as [jf JF]. cbn [cells_size csize Nat.add] in JF.
  apply evt_done. unfold np1_post.
  do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST|]. split; [split; [exact SSP1| exact SSP2]|].
  split; [exact TPC'|]. split; [do 15 eexists; exact LBC'|].
  split; [lia|]. split; [| split; [exact OBS| split; [exact JF| exact FR]]].
  rewrite firstn_length_le by (rewrite LJB; lia). lia.
Qed.
End Seg1.

Definition np_l_seg1_stmt : Prop :=
  forall (hex : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS fill v : Z) (j148 j284 : list byte) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - NP_DEPTH)%Z -> (0x6ce000 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  tp = Z_to_bv 64 (0x6abdb8 + 48) ->
  rw_cells bsegs m (OS + 136) (ios_cellsX OS 0x168e58 (FLX hex) (WX hex) fill j148 j284) ->
  (0x6ce000 <= OS)%Z -> (OS + 288 <= lo)%Z ->
  (0 <= fill < 256)%Z -> VOK hex v ->
  rw_cells bsegs m 0x6abdb8 [C8 (Z_to_bv 64 0x6cc0b0)] -> ssp_cells m canary -> frm0 fc ->
  LOCBA m -> el_dccA m -> mem_inv bsegs m ->
  (bv_unsigned sp mod 16 = 0)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> np_afacts lo (bv_unsigned sp) m ->
  evt bsegs (np1_post 0x11d1a8 sp gp tp s6 s7 s8 s9 s10 s11 F lo OS fill (LENX hex v) canary ra s0 s1 s2 s3 s4 s5 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 v) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_NP_L) fc None m (seg_rom bsegs)).

Definition ARG1 (hex : bool) (v : Z) : parg := if hex then PA_z v else PA_l v.
Lemma FMTX_eq : forall hex, FMTX hex = [37; 108; CCX hex; 0]%Z. Proof. intros [|]; reflexivity. Qed.
Lemma ARGX_eq : forall hex v, ARGX hex v = [ARG1 hex v]. Proof. intros [|] v; reflexivity. Qed.

Section Seg1L.
Hypothesis RIP : rip_stmt.

Theorem np_l_seg1 : np_l_seg1_stmt.
Proof using RIP.
  unfold np_l_seg1_stmt. intros until canary. intros ST LO LOLO SPH TP IOS OLO RO RF RV TPC SSP FRM LB DCC MI SP16 HSH AF0.
  assert (SP16' : ((bv_unsigned sp + -160) mod 16 = 0)%Z) by (clear - SP16; Z.div_mod_to_equations; lia).
  assert (ZONE : forall x, np_zone x -> outside [(lo, bv_unsigned sp); (0x6abdb8, 0x6abdb8 + 8)]%Z x).
  { intros x Hx. unfold np_zone, SHADOW_LO, SHADOW_HI, kHighShadowEnd in *. cbn [outside]. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(lo, bv_unsigned sp); (0x6abdb8, 0x6abdb8 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof DCC as DCC'. destruct DCC as (VT & WS & WS2 & NPT & NPV & GNP & GCT).
  destruct LB as (l1 & l2 & l3 & l4 & l5 & l6 & l7 & l8 & l9 & l10 & l11 & l12 & l13 & l14 & l15 & LBC). unfold locb_cellsA, PJ_LOC_LO_A in LBC.
  unfold ios_cellsX in IOS.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  assert (RL : ro_cells bsegs m 0x1741a [CB 2 [Z_to_bv 8 108; Z_to_bv 8 0]])
    by (apply (ro_cells_image bsegs m 0x1741a [Z_to_bv 8 108; Z_to_bv 8 0] MI); [vm_compute; reflexivity | lia | cbn; lia]).

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

  join_reg 10%Z (Z_to_bv 64 (CCX hex)) 0x11d09c%Z.
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
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (FMTB : bytes_at bsegs mm (bv_unsigned sp + -64) (zb fmt)) end.
  { pose proof (rw_cells_bytes_at' _ _ _ _ FMT8) as B. cbn [cells_bytes cbytes app] in B.
    pose proof (bytes_at_sub _ _ _ 0 4 B ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as B4. cbv [firstn skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in B4.
    replace (bv_unsigned sp + -64 + 0)%Z with (bv_unsigned sp + -64)%Z in B4 by lia. rewrite ZBF. exact B4. }

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (np_afacts_munch _ lo (bv_unsigned sp) lo (bv_unsigned sp) m mm AF0 MU WM ltac:(lia) ltac:(lia) ZONE) as (IC1 & STKC1 & ROD1 & RODFP1 & IFX1 & PCTX1 & PF1) end.
  call_sp (snl_proof RIP PCOK2_el (ivsn_proof RIP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _
             (bv_unsigned sp + -88)%Z 24%Z 0x33380%Z (bv_unsigned sp + -64)%Z 24%nat jn fmt args lo canary len outb);
    [ reflexivity | reflexivity | reflexivity | reflexivity | exact TP | lia | exact TPC | exact NAR | exact FMTB
    | exact FALL
    | exact PASS1
    | intros mq; apply ARGOK
    | exact MODEL
    | exact FPC
    | unfold zlength in CU; lia | lia | lia | exact ST | lia | unfold GLOBALS_TOP; lia | lia | split; [exact SSP1 | exact SSP2] | assumption | exact FRM
    | lia | rewrite LF4; lia | rewrite LF4; lia | lia | lia
    | lia | exact SP16' | exact HSH | exact IC1
    | intros p n' Hp Hn; apply STKC1; lia
    | apply STKC1; [lia| rewrite LF4; lia]
    | exact ROD1
    | apply STKC1; [lia| unfold zlength in CU |- *; lia]
    | right; unfold SHADOW_HI, kHighShadowEnd in *; lia
    | exact RODFP1 | exact IFX1
    | intros m' MU' WM'; subst fmt args; rewrite FMTX_eq, ARGX_eq; apply (pcok2_l (CCX hex) (ARG1 hex v) m' _ _ _ lo len outb); [destruct hex; cbv; lia| rewrite <- FMTX_eq, <- ARGX_eq; exact MODEL| lia| unfold zlength in CU |- *; lia| lia| lia| lia| |];
      [ apply (pctx_munch _ _ m' PCTX1 MU' WM'); intros x Hx; unfold in_PCR in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia
      | destruct PF1 as [PF1a PF1b]; split;
        [ apply (pfcells_munch _ _ m' PF1a MU' WM'); intros x Hx; unfold in_PFR in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia
        | apply (ro_cells_agree bsegs _ m' _ _ PF1b); apply (agree_of_munch _ _ m' _ MU'); intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbn [outside]; unfold kHighShadowEnd in *; lia ] ]
    | ].
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

  apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 EL_IMP)] 64 (skipn 8 jl) [] [8; 8; 3; 45]%nat) in LOCALS; [|reflexivity].
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
    | split; [exact VT | split; [exact WS | split; [exact WS2 | split; [exact NPT | split; [exact NPV | split; [exact GNP | exact GCT]]]]]]
    | assumption | ].
  subst E2. clear SRCN.
  rename PC into ST. rename PC0 into OBUF. rename PC1 into POP. rename PC2 into POE. rename POST into LB.
  destruct LB as (l1' & l2' & l3' & l4' & l5' & l6' & l7' & l8' & l9' & l10' & l11' & l12' & l13' & l14' & l15' & LBC'). unfold locb_cellsA, PJ_LOC_LO_A in LBC'.
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

  replace (bv_unsigned sp + -133 + (bv_unsigned sp + -88 - (bv_unsigned sp + -88)))%Z with (bv_unsigned sp + -133)%Z by lia.
  replace (bv_unsigned sp + -133 + (bv_unsigned sp + -88 + len - (bv_unsigned sp + -88)))%Z with (bv_unsigned sp + -133 + len)%Z by lia.
  replace (bv_unsigned sp + -88 + len - (bv_unsigned sp + -88))%Z with (len) in OBS by lia.
  lazymatch type of OBS with context [skipn (Z.to_nat 0) ?l] => change (skipn (Z.to_nat 0) l) with l in OBS end.
  change (Z.to_nat 45) with 45%nat in OBUF.
  glueZ PLOC POE. glueZ PLOC POP. glueZ PLOC GAP. glueZ PLOC OBUF. glueZ PLOC NAR'. glueZ PLOC FMT8.
  destruct (rw_cells_forget bsegs _ _ _ PLOC) as [jf JF]. cbn [cells_size csize Nat.add] in JF.
  apply evt_done. unfold np1_post.
  do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST|]. split; [split; [exact SSP1| exact SSP2]|].
  split; [exact TPC'|]. split; [do 15 eexists; exact LBC'|].
  split; [lia|]. split; [| split; [exact OBS| split; [exact JF| exact FR]]].
  rewrite firstn_length_le by (rewrite LJB; lia). lia.
Qed.
End Seg1L.

Lemma np_seg2 : forall (RET q : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xs0 xs1 xs2 xs3 xs4 xs5 : word)
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (jf : list byte),
  (RET = 0x11d6dc \/ RET = 0x11d1a8)%Z ->
  stk bsegs m lo (q + -160) -> (lo <= q + -160)%Z -> (q <= 2^47)%Z ->
  rw_cells bsegs m (q + -160) [CB 104 jf] ->
  rw_cells bsegs m (q + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms' => ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom bsegs)
                       /\ stk bsegs m lo q)
      (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 (q + -160)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
               xs2 xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RET) fc None m (seg_rom bsegs)).
Proof.
  intros until jf. intros HR ST LO1 SPH JF FR MI.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as (? & ? & _); lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 (q + -160)) = (q + -160)%Z) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(lo, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct HR as [-> | ->]; do 9 lstep; glueZ JF FR; release_frame JF ST q; apply evt_done; (split; [| exact ST]);
    f_equal; f_equal; apply bv_eq; rewrite ?unsigned_lit by lia; lia.
Qed.

Section Stmt.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Definition EL_NP_STACK_A : Z := 10672 + RT_STACK.

Definition np_cpsA (ENTRY FL W : Z) (VOKP : Z -> Prop) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO fill v : Z) (kO : nat) (pb : word) (pp ep : Z) (dum j148 j284 : list byte)
         (ra gp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> (fO <= OS)%Z -> (OS + 288 <= fO + fs_size kO - 8)%Z -> (OS mod 16 = 0)%Z ->
  rw_cells bsegs m OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep ->
  rw_cells bsegs m (OS + 128) [C8 (Z_to_bv 64 0x168e30)] -> rw_cells bsegs m (OS + 136) (ios_cellsX OS 0x168e58 FL W fill j148 j284) ->
  bytes_at bsegs m (shad OS) (repeat z8 36) -> (0 <= fill < 256)%Z -> VOKP v ->
  el_tploc m -> io_ssp m -> frm0 fc -> LOCBA m ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z -> (lo + EL_NP_STACK_A <= q)%Z ->
  (q + 16 <= USTACK_TOP)%Z -> (q mod 16 = 0)%Z ->
  (Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT)%Z -> (1 <= rt_credit RT Σ)%Z ->
  (forall (Σ' : rts RT) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m' (pb' : word) (pp' ep' : Z) (dum' : list byte),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rw_cells bsegs m' OS (sb_cellsX pb' (Z_to_bv 64 pp') (Z_to_bv 64 ep') dum') -> PUTINV OS pp' ep' ->
     rw_cells bsegs m' (OS + 128) [C8 (Z_to_bv 64 0x168e30)] -> rw_cells bsegs m' (OS + 136) (ios_cellsX OS 0x168e58 FL 0 fill j148 j284) ->
     bytes_at bsegs m' (shad OS) (repeat z8 36) -> el_tploc m' -> LOCBA m' -> frm0 fc' ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> (rt_credit RT Σ - 1 <= rt_credit RT Σ')%Z ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS + 40, OS + 128); (OS + 160, OS + 168); (0x6abdb8, 0x6abdb8 + 8)]%Z m m' ->
     aevt RT PMc Σ' K (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0' t1' t2' s0 s1 (Z_to_bv 64 OS) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 OS) (Z_to_bv 64 (OS + 136)) (Z_to_bv 64 fill) (Z_to_bv 64 v) a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).
Definition np_ul_cpsA : Prop := np_cpsA EL_NP_UL 0x1002 0 (fun v => 0 <= v < 2^64)%Z.
Definition np_l_cpsA : Prop := np_cpsA EL_NP_L 0x1002 0 (fun v => -2^63 <= v < 2^63)%Z.

Definition np_lx_cpsA : Prop := np_cpsA EL_NP_L 0x1008 4 (fun v => 0 <= v < 256)%Z.
End Stmt.

Section Lift.
Local Open Scope Z_scope.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RIP : rip_stmt.
Hypothesis AF_IC : forall Σ m, ART RT Σ m -> ictx m.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> (0 < n)%Z -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.

Hypothesis AF_NP : forall Σ m, ART RT Σ m -> rod_chk m /\ rod_chk_fp m /\ ifx_real m /\ pctx m /\ pfcells6 m.
Local Notation PAD := (padX_okA RT AF RC RC2 PMc FDO MST RIP AF_IC AF_SHW DCC).
Local Notation PADW := (padW_okA RT AF RC RC2 PMc FDO MST RIP AF_IC AF_SHW DCC).

Lemma xlen_byte : forall u, (0 <= u < 256)%Z -> (xlen u <= 2)%Z.
Proof.
  intros u Hu. assert (E : forallb (fun k => xlen (Z.of_nat k) <=? 2)%Z (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E (Z.to_nat u) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in E by lia. apply Z.leb_le. exact E.
Qed.

Local Ltac ul := unfold EL_NP_STACK_A, EL_PAD_STACK_A, EL_PADW_STACK_A, EL_XSPUTN_DEPTH, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd, SHADOW_LO, SHADOW_HI in *; lia.

Lemma stk_chkr : forall Σ m lo q, ART RT Σ m -> (rt_sp0 RT Σ - STACK_WIN + 64 <= lo)%Z -> (q + 16 <= USTACK_TOP)%Z ->
  forall p n', (lo <= p)%Z -> (p + n' <= q)%Z -> chkr m p n'.
Proof using AF AF_SHW.
  intros Σ m lo q ART0 LOW QT p n' Hp Hn. pose proof (af_sp0_range RT AF Σ m ART0) as R1. pose proof (af_sp0_win RT AF Σ m ART0) as R2.
  unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *.
  destruct (Z_lt_le_dec 0 n') as [NP|NN].
  - apply (chkr_of RT AF_SHW Σ m p n' ART0); [clear - LOW QT Hp Hn R1 R2 NP; lia| apply (af_acc_stack RT AF Σ m p n' ART0); clear - LOW QT Hp Hn R1 R2 NP; unfold STACK_WIN, USTACK_TOP; lia
      | right; right; left; clear - LOW QT Hp Hn R1 R2 NP; unfold STACK_WIN, USTACK_TOP; lia].
  - split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd, kHighShadowEnd. right.
    clear - LOW QT Hp Hn R1 R2 NN. lia.
Qed.

Theorem np_ul_okA : np_ul_cpsA RT PMc.
Proof using AF RC RC2 FDO MST RIP AF_IC AF_SHW DCC AF_NP.
  unfold np_ul_cpsA, np_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SB PI V128 IOS SHZ RF RV TPC SSP FRM LB ART0 MI ST LOW LOR SPT Q32 FRB CRB HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as (? & ? & _); lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; ul).
  destruct SSP as (canary & SSP1 & SSP2).

  destruct (stk_split bsegs m lo (lo + 64)%Z q ST ltac:(ul)) as [STlo ST64].
  assert (AFX : np_afacts (lo + 64)%Z q m).
  { destruct (AF_NP Σ m ART0) as (R1 & R2 & R3 & R4 & R5). split; [exact (AF_IC Σ m ART0)|]. split; [| split; [exact R1| split; [exact R2| split; [exact R3| split; [exact R4| exact R5]]]]].
    apply (stk_chkr Σ m (lo + 64)%Z q ART0 ltac:(ul) ltac:(ul)). }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (np_ul_seg1 RIP ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (lo + 64)%Z OS fill v j148 j284 canary);
      rewrite ?EQ; first [exact ST64| exact IOS| exact RF| exact RV| unfold VOK; clear - RV; lia| exact TPC| split; [exact SSP1| exact SSP2]| exact FRM| exact LB| exact (DCC Σ m ART0)| exact MI| exact AFX| reflexivity| ul| idtac].
    all: clear - Q32; Z.div_mod_to_equations; lia. }
  cbv beta. intros ms1 PO. unfold np1_post in PO. rewrite !EQ in PO.
  destruct PO as (x5 & x6 & x7 & x16 & x17 & x28 & x29 & x30 & x31 & F1 & fc1 & ob & jf & m1 & -> & MU1 & WM1 & MI1 & FRM1 & FOK1 & ST1 & SSP' & TPC1 & LB1 & LEN & LOB & OBS & JF1 & FR1).
  apply evt_done.

  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (lo + 64)%Z ART0 ltac:(ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
    split; [intros Hr; apply Ha; left; ul|]. split; [| exact I]. intros Hr. apply Ha. right; left. apply client_static_intro. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> (x < lo + 64 \/ q <= x) /\ ~ (0x6abdb8 <= x < 0x6abdc0))%Z -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. destruct (HP _ Ha) as [H1 H2]. cbn [outside]. split; [lia| split; [lia| exact I]]. }
  assert (OSLO : (OS + 288 <= lo)%Z) by (clear - FHI FTOP LOW; ul).
  assert (SB1 : rw_cells bsegs m1 OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum)).
  { eapply rw_cells_agree_nw; [exact SB|]. apply AG1. intros x Hx. cbn [sb_cellsX cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (IOS1 : rw_cells bsegs m1 (OS + 136) (ios_cellsX OS 0x168e58 0x1002 0 fill j148 j284)).
  { eapply rw_cells_agree_nw; [exact IOS|]. apply AG1. intros x Hx. cbn [ios_cellsX cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (SHZ1 : bytes_at bsegs m1 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHZ|]. apply AG1. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. unfold SEGTOP_A in FSEG. split; [| Z.div_mod_to_equations; lia].
    left. clear - Hx FLO FHI FTOP LOW SP0W F0. unfold STACK_WIN in *. Z.div_mod_to_equations. lia. }

  pose proof IOS1 as IOSc. unfold ios_cellsX in IOSc. takeZ IOSc 4%nat (OS + 160)%Z IOSa. takeZ IOSc 1%nat (OS + 168)%Z WID1. rename IOSc into IOSb.
  assert (V1 : rw_cells bsegs m1 (OS + 128) [C8 (Z_to_bv 64 0x168e30)]).
  { eapply rw_cells_agree_nw; [exact V128|]. apply AG1. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (HULL1 : os_hullA m1 OS).
  { split; [| exact SHZ1]. pose proof SB1 as SBc. unfold sb_cellsX in SBc. pose proof IOS1 as IOSc. unfold ios_cellsX in IOSc. pose proof V1 as V1c.
    glueZ SBc V1c. glueZ SBc IOSc. destruct (rw_cells_forget bsegs m1 OS _ SBc) as (bo & Hb). exists bo. exact Hb. }

  assert (ST1f : stk bsegs m1 lo (q + -160)).
  { apply (stk_merge bsegs m1 lo (lo + 64) (q + -160)); [| exact ST1| ul].
    eapply stk_agree_nw; [exact STlo|]. apply AG1. intros x Hx. cbv beta in Hx. clear - Hx SP0W LOW. unfold STACK_WIN in *. lia. }
  eapply (PAD Σ K OS (q + -133)%Z (ulen v) (ulen v) (q + -160)%Z lo fO fill pp ep kO pb dum ob);
    [exact FDO| exact MST| exact INF| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16
    | exact SB1| exact PI| exact WID1| exact HULL1
    | exact OBS| lia| lia| lia| ul
    | apply (af_acc_stack RT AF Σ m1 _ _ ART1); ul
    | right; left; ul
    | right; ul
    | lia
    | exact ART1| exact MI1| exact ST1f| ul| ul| ul| clear - Q32; Z.div_mod_to_equations; lia
    | exact FRB| exact CRB|].
  intros Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 m2 pb' pp' ep' dum' ART2 MI2 ST2 HULL2 SB2 PI2 WID2 LV2 FRS2 SP2 CR2 PRES2.
  rewrite (ret_pc_even 0x11d6dc) by lia.

  assert (AG2 : forall P : Z -> Prop,
            (forall x, P x -> ((q + -160 <= x < q) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ (x = 0x6abdb8 \/ 0x6abdb8 < x < 0x6abdc0) \/ (OS <= x < OS + 40) \/ (OS + 128 <= x < OS + 160) \/ (OS + 168 <= x < OS + 288))%Z) ->
            agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2.
    - destruct (HP _ Ha) as [H|[H|[H|[H|[H|H]]]]].
      + left. ul.
      + right; left. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H. lia.
      + right; left. apply client_static_intro. lia.
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
    - pose proof (HP _ Ha) as H. clear - H OSLO LOR FSEG FLO. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, EL_NP_STACK_A, RT_STACK, SEGTOP_A in *. split; [lia| split; [lia| exact I]]. }
  assert (JF2 : rw_cells bsegs m2 (q + -160) [CB 104 jf]) by (eapply rw_cells_agree_nw; [exact JF1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (FR2 : rw_cells bsegs m2 (q + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_agree_nw; [exact FR1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (V2 : rw_cells bsegs m2 (OS + 128) [C8 (Z_to_bv 64 0x168e30)]) by (eapply rw_cells_agree_nw; [exact V1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  lazymatch type of IOSa with rw_cells _ _ _ ?cs => assert (IOSa2 : rw_cells bsegs m2 (OS + 136) cs) by (eapply rw_cells_agree_nw; [exact IOSa|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  lazymatch type of IOSb with rw_cells _ _ _ ?cs => assert (IOSb2 : rw_cells bsegs m2 (OS + 168) cs) by (eapply rw_cells_agree_nw; [exact IOSb|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  assert (TPC2 : el_tploc m2) by (eapply rw_cells_agree_nw; [exact TPC1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (LB2 : LOCBA m2) by (apply (LOCBA_agree m1 m2 LB1); apply AG2; intros x Hx; lia).
  pose proof IOSa2 as IOS2. glueZ IOS2 WID2. glueZ IOS2 IOSb2. change (rw_cells bsegs m2 (OS + 136) (ios_cellsX OS 0x168e58 0x1002 0 fill j148 j284)) in IOS2.
  destruct HULL2 as [_ SHZ2].

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (np_seg2 0x11d6dc q ra gp (Z_to_bv 64 TPV_A) y0 y1 y2 s0 s1 (Z_to_bv 64 OS) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
              _ _ _ _ _ _ F2 fc1 m2 lo jf); [first [left; reflexivity| right; reflexivity]| exact ST2| ul| ul| exact JF2| exact FR2| exact MI2]. }
  cbv beta. intros ms3 [-> ST3]. apply evt_done.
  assert (SB2x : rw_cells bsegs m2 OS (sb_cellsX pb' (Z_to_bv 64 pp') (Z_to_bv 64 ep') dum')) by (unfold sb_cellsX; exact SB2).
  eapply (HK Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 fc1 m2 pb' pp' ep' dum' ART2 MI2 ST3 SB2x PI2 V2 IOS2 SHZ2 TPC2 LB2 FRM1 LV2 FRS2 SP2);
    [clear - CR2; lia|].

  intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2 & Ho3 & _).
  rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]| cbn [outside]; split; [exact Ho1| split; [exact Ho2| exact I]]].
  apply MU1. cbn [outside]. split; [| split; [exact Ho3| exact I]]. intros Hr. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul.
Qed.
Theorem np_l_okA : np_l_cpsA RT PMc.
Proof using AF RC RC2 FDO MST RIP AF_IC AF_SHW DCC AF_NP.
  unfold np_l_cpsA, np_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SB PI V128 IOS SHZ RF RV TPC SSP FRM LB ART0 MI ST LOW LOR SPT Q32 FRB CRB HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as (? & ? & _); lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; ul).
  destruct SSP as (canary & SSP1 & SSP2).

  destruct (stk_split bsegs m lo (lo + 64)%Z q ST ltac:(ul)) as [STlo ST64].
  assert (AFX : np_afacts (lo + 64)%Z q m).
  { destruct (AF_NP Σ m ART0) as (R1 & R2 & R3 & R4 & R5). split; [exact (AF_IC Σ m ART0)|]. split; [| split; [exact R1| split; [exact R2| split; [exact R3| split; [exact R4| exact R5]]]]].
    apply (stk_chkr Σ m (lo + 64)%Z q ART0 ltac:(ul) ltac:(ul)). }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (np_l_seg1 RIP false ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (lo + 64)%Z OS fill v j148 j284 canary);
      rewrite ?EQ; first [exact ST64| exact IOS| exact RF| exact RV| unfold VOK; clear - RV; lia| exact TPC| split; [exact SSP1| exact SSP2]| exact FRM| exact LB| exact (DCC Σ m ART0)| exact MI| exact AFX| reflexivity| ul| idtac].
    all: clear - Q32; Z.div_mod_to_equations; lia. }
  cbv beta. intros ms1 PO. unfold np1_post in PO. rewrite !EQ in PO.
  destruct PO as (x5 & x6 & x7 & x16 & x17 & x28 & x29 & x30 & x31 & F1 & fc1 & ob & jf & m1 & -> & MU1 & WM1 & MI1 & FRM1 & FOK1 & ST1 & SSP' & TPC1 & LB1 & LEN & LOB & OBS & JF1 & FR1).
  apply evt_done.

  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (lo + 64)%Z ART0 ltac:(ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
    split; [intros Hr; apply Ha; left; ul|]. split; [| exact I]. intros Hr. apply Ha. right; left. apply client_static_intro. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> (x < lo + 64 \/ q <= x) /\ ~ (0x6abdb8 <= x < 0x6abdc0))%Z -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. destruct (HP _ Ha) as [H1 H2]. cbn [outside]. split; [lia| split; [lia| exact I]]. }
  assert (OSLO : (OS + 288 <= lo)%Z) by (clear - FHI FTOP LOW; ul).
  assert (SB1 : rw_cells bsegs m1 OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum)).
  { eapply rw_cells_agree_nw; [exact SB|]. apply AG1. intros x Hx. cbn [sb_cellsX cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (IOS1 : rw_cells bsegs m1 (OS + 136) (ios_cellsX OS 0x168e58 0x1002 0 fill j148 j284)).
  { eapply rw_cells_agree_nw; [exact IOS|]. apply AG1. intros x Hx. cbn [ios_cellsX cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (SHZ1 : bytes_at bsegs m1 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHZ|]. apply AG1. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. unfold SEGTOP_A in FSEG. split; [| Z.div_mod_to_equations; lia].
    left. clear - Hx FLO FHI FTOP LOW SP0W F0. unfold STACK_WIN in *. Z.div_mod_to_equations. lia. }

  pose proof IOS1 as IOSc. unfold ios_cellsX in IOSc. takeZ IOSc 4%nat (OS + 160)%Z IOSa. takeZ IOSc 1%nat (OS + 168)%Z WID1. rename IOSc into IOSb.
  assert (V1 : rw_cells bsegs m1 (OS + 128) [C8 (Z_to_bv 64 0x168e30)]).
  { eapply rw_cells_agree_nw; [exact V128|]. apply AG1. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (HULL1 : os_hullA m1 OS).
  { split; [| exact SHZ1]. pose proof SB1 as SBc. unfold sb_cellsX in SBc. pose proof IOS1 as IOSc. unfold ios_cellsX in IOSc. pose proof V1 as V1c.
    glueZ SBc V1c. glueZ SBc IOSc. destruct (rw_cells_forget bsegs m1 OS _ SBc) as (bo & Hb). exists bo. exact Hb. }

  assert (ST1f : stk bsegs m1 lo (q + -160)).
  { apply (stk_merge bsegs m1 lo (lo + 64) (q + -160)); [| exact ST1| ul].
    eapply stk_agree_nw; [exact STlo|]. apply AG1. intros x Hx. cbv beta in Hx. clear - Hx SP0W LOW. unfold STACK_WIN in *. lia. }
  eapply (PAD Σ K OS (q + -133)%Z (LENX false v) (LENX false v) (q + -160)%Z lo fO fill pp ep kO pb dum ob);
    [exact FDO| exact MST| exact INF| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16
    | exact SB1| exact PI| exact WID1| exact HULL1
    | exact OBS| lia| lia| lia| ul
    | apply (af_acc_stack RT AF Σ m1 _ _ ART1); ul
    | right; left; ul
    | right; ul
    | lia
    | exact ART1| exact MI1| exact ST1f| ul| ul| ul| clear - Q32; Z.div_mod_to_equations; lia
    | exact FRB| exact CRB|].
  intros Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 m2 pb' pp' ep' dum' ART2 MI2 ST2 HULL2 SB2 PI2 WID2 LV2 FRS2 SP2 CR2 PRES2.
  rewrite (ret_pc_even 0x11d1a8) by lia.

  assert (AG2 : forall P : Z -> Prop,
            (forall x, P x -> ((q + -160 <= x < q) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ (x = 0x6abdb8 \/ 0x6abdb8 < x < 0x6abdc0) \/ (OS <= x < OS + 40) \/ (OS + 128 <= x < OS + 160) \/ (OS + 168 <= x < OS + 288))%Z) ->
            agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2.
    - destruct (HP _ Ha) as [H|[H|[H|[H|[H|H]]]]].
      + left. ul.
      + right; left. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H. lia.
      + right; left. apply client_static_intro. lia.
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
    - pose proof (HP _ Ha) as H. clear - H OSLO LOR FSEG FLO. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, EL_NP_STACK_A, RT_STACK, SEGTOP_A in *. split; [lia| split; [lia| exact I]]. }
  assert (JF2 : rw_cells bsegs m2 (q + -160) [CB 104 jf]) by (eapply rw_cells_agree_nw; [exact JF1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (FR2 : rw_cells bsegs m2 (q + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_agree_nw; [exact FR1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (V2 : rw_cells bsegs m2 (OS + 128) [C8 (Z_to_bv 64 0x168e30)]) by (eapply rw_cells_agree_nw; [exact V1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  lazymatch type of IOSa with rw_cells _ _ _ ?cs => assert (IOSa2 : rw_cells bsegs m2 (OS + 136) cs) by (eapply rw_cells_agree_nw; [exact IOSa|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  lazymatch type of IOSb with rw_cells _ _ _ ?cs => assert (IOSb2 : rw_cells bsegs m2 (OS + 168) cs) by (eapply rw_cells_agree_nw; [exact IOSb|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  assert (TPC2 : el_tploc m2) by (eapply rw_cells_agree_nw; [exact TPC1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (LB2 : LOCBA m2) by (apply (LOCBA_agree m1 m2 LB1); apply AG2; intros x Hx; lia).
  pose proof IOSa2 as IOS2. glueZ IOS2 WID2. glueZ IOS2 IOSb2. change (rw_cells bsegs m2 (OS + 136) (ios_cellsX OS 0x168e58 0x1002 0 fill j148 j284)) in IOS2.
  destruct HULL2 as [_ SHZ2].

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (np_seg2 0x11d1a8 q ra gp (Z_to_bv 64 TPV_A) y0 y1 y2 s0 s1 (Z_to_bv 64 OS) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
              _ _ _ _ _ _ F2 fc1 m2 lo jf); [first [left; reflexivity| right; reflexivity]| exact ST2| ul| ul| exact JF2| exact FR2| exact MI2]. }
  cbv beta. intros ms3 [-> ST3]. apply evt_done.
  assert (SB2x : rw_cells bsegs m2 OS (sb_cellsX pb' (Z_to_bv 64 pp') (Z_to_bv 64 ep') dum')) by (unfold sb_cellsX; exact SB2).
  eapply (HK Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 fc1 m2 pb' pp' ep' dum' ART2 MI2 ST3 SB2x PI2 V2 IOS2 SHZ2 TPC2 LB2 FRM1 LV2 FRS2 SP2);
    [clear - CR2; lia|].

  intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2 & Ho3 & _).
  rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]| cbn [outside]; split; [exact Ho1| split; [exact Ho2| exact I]]].
  apply MU1. cbn [outside]. split; [| split; [exact Ho3| exact I]]. intros Hr. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul.
Qed.
Theorem np_lx_okA : np_lx_cpsA RT PMc.
Proof using AF RC RC2 FDO MST RIP AF_IC AF_SHW DCC AF_NP.
  unfold np_lx_cpsA, np_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SB PI V128 IOS SHZ RF RV TPC SSP FRM LB ART0 MI ST LOW LOR SPT Q32 FRB CRB HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as (? & ? & _); lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; ul).
  destruct SSP as (canary & SSP1 & SSP2).

  destruct (stk_split bsegs m lo (lo + 64)%Z q ST ltac:(ul)) as [STlo ST64].
  assert (AFX : np_afacts (lo + 64)%Z q m).
  { destruct (AF_NP Σ m ART0) as (R1 & R2 & R3 & R4 & R5). split; [exact (AF_IC Σ m ART0)|]. split; [| split; [exact R1| split; [exact R2| split; [exact R3| split; [exact R4| exact R5]]]]].
    apply (stk_chkr Σ m (lo + 64)%Z q ART0 ltac:(ul) ltac:(ul)). }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (np_l_seg1 RIP true ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (lo + 64)%Z OS fill v j148 j284 canary);
      rewrite ?EQ; first [exact ST64| exact IOS| exact RF| exact RV| unfold VOK; clear - RV; lia| exact TPC| split; [exact SSP1| exact SSP2]| exact FRM| exact LB| exact (DCC Σ m ART0)| exact MI| exact AFX| reflexivity| ul| idtac].
    all: clear - Q32; Z.div_mod_to_equations; lia. }
  cbv beta. intros ms1 PO. unfold np1_post in PO. rewrite !EQ in PO.
  destruct PO as (x5 & x6 & x7 & x16 & x17 & x28 & x29 & x30 & x31 & F1 & fc1 & ob & jf & m1 & -> & MU1 & WM1 & MI1 & FRM1 & FOK1 & ST1 & SSP' & TPC1 & LB1 & LEN & LOB & OBS & JF1 & FR1).
  apply evt_done.

  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (lo + 64)%Z ART0 ltac:(ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
    split; [intros Hr; apply Ha; left; ul|]. split; [| exact I]. intros Hr. apply Ha. right; left. apply client_static_intro. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> (x < lo + 64 \/ q <= x) /\ ~ (0x6abdb8 <= x < 0x6abdc0))%Z -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. destruct (HP _ Ha) as [H1 H2]. cbn [outside]. split; [lia| split; [lia| exact I]]. }
  assert (OSLO : (OS + 288 <= lo)%Z) by (clear - FHI FTOP LOW; ul).
  assert (SB1 : rw_cells bsegs m1 OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum)).
  { eapply rw_cells_agree_nw; [exact SB|]. apply AG1. intros x Hx. cbn [sb_cellsX cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (IOS1 : rw_cells bsegs m1 (OS + 136) (ios_cellsX OS 0x168e58 0x1008 4 fill j148 j284)).
  { eapply rw_cells_agree_nw; [exact IOS|]. apply AG1. intros x Hx. cbn [ios_cellsX cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (SHZ1 : bytes_at bsegs m1 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHZ|]. apply AG1. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in Hx. unfold SEGTOP_A in FSEG. split; [| Z.div_mod_to_equations; lia].
    left. clear - Hx FLO FHI FTOP LOW SP0W F0. unfold STACK_WIN in *. Z.div_mod_to_equations. lia. }

  pose proof IOS1 as IOSc. unfold ios_cellsX in IOSc. takeZ IOSc 4%nat (OS + 160)%Z IOSa. takeZ IOSc 1%nat (OS + 168)%Z WID1. rename IOSc into IOSb.
  assert (V1 : rw_cells bsegs m1 (OS + 128) [C8 (Z_to_bv 64 0x168e30)]).
  { eapply rw_cells_agree_nw; [exact V128|]. apply AG1. intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold SEGTOP_A in FSEG. lia. }
  assert (HULL1 : os_hullA m1 OS).
  { split; [| exact SHZ1]. pose proof SB1 as SBc. unfold sb_cellsX in SBc. pose proof IOS1 as IOSc. unfold ios_cellsX in IOSc. pose proof V1 as V1c.
    glueZ SBc V1c. glueZ SBc IOSc. destruct (rw_cells_forget bsegs m1 OS _ SBc) as (bo & Hb). exists bo. exact Hb. }

  assert (ST1f : stk bsegs m1 lo (q + -160)).
  { apply (stk_merge bsegs m1 lo (lo + 64) (q + -160)); [| exact ST1| ul].
    eapply stk_agree_nw; [exact STlo|]. apply AG1. intros x Hx. cbv beta in Hx. clear - Hx SP0W LOW. unfold STACK_WIN in *. lia. }
  eapply (PADW Σ K OS (q + -133)%Z (LENX true v) (LENX true v) (q + -160)%Z lo fO fill 4 pp ep kO pb dum ob);
    [exact FDO| exact MST| exact INF| exact FLO| rewrite <- EFSZ; exact FHI| exact AL16
    | exact SB1| exact PI| exact WID1| exact HULL1
    | exact OBS| lia| lia| lia| ul
    | apply (af_acc_stack RT AF Σ m1 _ _ ART1); ul
    | right; left; ul
    | right; ul
    | lia
    | unfold LENX; pose proof (xlen_bound v); lia| unfold LENX; pose proof (xlen_byte v ltac:(exact RV)); lia| lia
    | exact ART1| exact MI1| exact ST1f| ul| ul| ul| clear - Q32; Z.div_mod_to_equations; lia
    | exact FRB| exact CRB|].
  intros Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 m2 pb' pp' ep' dum' ART2 MI2 ST2 HULL2 SB2 PI2 WID2 LV2 FRS2 SP2 CR2 PRES2.
  rewrite (ret_pc_even 0x11d1a8) by lia.

  assert (AG2 : forall P : Z -> Prop,
            (forall x, P x -> ((q + -160 <= x < q) \/ (PJ_LOC_LO_A <= x < PJ_LOC_HI_A) \/ (x = 0x6abdb8 \/ 0x6abdb8 < x < 0x6abdc0) \/ (OS <= x < OS + 40) \/ (OS + 128 <= x < OS + 160) \/ (OS + 168 <= x < OS + 288))%Z) ->
            agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2.
    - destruct (HP _ Ha) as [H|[H|[H|[H|[H|H]]]]].
      + left. ul.
      + right; left. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in H. lia.
      + right; left. apply client_static_intro. lia.
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
      + right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
    - pose proof (HP _ Ha) as H. clear - H OSLO LOR FSEG FLO. cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A, EL_NP_STACK_A, RT_STACK, SEGTOP_A in *. split; [lia| split; [lia| exact I]]. }
  assert (JF2 : rw_cells bsegs m2 (q + -160) [CB 104 jf]) by (eapply rw_cells_agree_nw; [exact JF1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (FR2 : rw_cells bsegs m2 (q + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_agree_nw; [exact FR1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (V2 : rw_cells bsegs m2 (OS + 128) [C8 (Z_to_bv 64 0x168e30)]) by (eapply rw_cells_agree_nw; [exact V1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  lazymatch type of IOSa with rw_cells _ _ _ ?cs => assert (IOSa2 : rw_cells bsegs m2 (OS + 136) cs) by (eapply rw_cells_agree_nw; [exact IOSa|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  lazymatch type of IOSb with rw_cells _ _ _ ?cs => assert (IOSb2 : rw_cells bsegs m2 (OS + 168) cs) by (eapply rw_cells_agree_nw; [exact IOSb|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
  assert (TPC2 : el_tploc m2) by (eapply rw_cells_agree_nw; [exact TPC1|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
  assert (LB2 : LOCBA m2) by (apply (LOCBA_agree m1 m2 LB1); apply AG2; intros x Hx; lia).
  pose proof IOSa2 as IOS2. glueZ IOS2 WID2. glueZ IOS2 IOSb2. change (rw_cells bsegs m2 (OS + 136) (ios_cellsX OS 0x168e58 0x1008 0 fill j148 j284)) in IOS2.
  destruct HULL2 as [_ SHZ2].

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { eapply (np_seg2 0x11d1a8 q ra gp (Z_to_bv 64 TPV_A) y0 y1 y2 s0 s1 (Z_to_bv 64 OS) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
              _ _ _ _ _ _ F2 fc1 m2 lo jf); [first [left; reflexivity| right; reflexivity]| exact ST2| ul| ul| exact JF2| exact FR2| exact MI2]. }
  cbv beta. intros ms3 [-> ST3]. apply evt_done.
  assert (SB2x : rw_cells bsegs m2 OS (sb_cellsX pb' (Z_to_bv 64 pp') (Z_to_bv 64 ep') dum')) by (unfold sb_cellsX; exact SB2).
  eapply (HK Σ2 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F2 fc1 m2 pb' pp' ep' dum' ART2 MI2 ST3 SB2x PI2 V2 IOS2 SHZ2 TPC2 LB2 FRM1 LV2 FRS2 SP2);
    [clear - CR2; lia|].

  intros a Ha Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2 & Ho3 & _).
  rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]| cbn [outside]; split; [exact Ho1| split; [exact Ho2| exact I]]].
  apply MU1. cbn [outside]. split; [| split; [exact Ho3| exact I]]. intros Hr. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul.
Qed.
End Lift.
