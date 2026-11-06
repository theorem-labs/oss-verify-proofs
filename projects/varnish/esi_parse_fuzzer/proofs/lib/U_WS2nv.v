(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World U_Img ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lit32 K :=
  repeat match type of K with
  | context [bv_unsigned (zx32 (Z_to_bv 64 ?z))] =>
      let v := eval vm_compute in (bv_unsigned (zx32 (Z_to_bv 64 z))) in
      change (bv_unsigned (zx32 (Z_to_bv 64 z))) with v in K
  | context [bv_unsigned (sx32 (Z_to_bv 64 ?z))] =>
      let v := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
      change (bv_unsigned (sx32 (Z_to_bv 64 z))) with v in K
  | context [bv_signed (zx32 (Z_to_bv 64 ?z))] =>
      let v := eval vm_compute in (bv_signed (zx32 (Z_to_bv 64 z))) in
      change (bv_signed (zx32 (Z_to_bv 64 z))) with v in K
  | context [bv_signed (sx32 (Z_to_bv 64 ?z))] =>
      let v := eval vm_compute in (bv_signed (sx32 (Z_to_bv 64 z))) in
      change (bv_signed (sx32 (Z_to_bv 64 z))) with v in K
  end.
(* [comment removed for export] *)
Ltac is_zlit v := lazymatch v with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_bits K :=
  repeat match type of K with
  | context [Z.land ?a ?b] => let v := eval vm_compute in (Z.land a b) in is_zlit v; change (Z.land a b) with v in K
  | context [Z.lor ?a ?b] => let v := eval vm_compute in (Z.lor a b) in is_zlit v; change (Z.lor a b) with v in K
  | context [Z.shiftl ?a ?b] => let v := eval vm_compute in (Z.shiftl a b) in is_zlit v; change (Z.shiftl a b) with v in K
  | context [Z.shiftr ?a ?b] => let v := eval vm_compute in (Z.shiftr a b) in is_zlit v; change (Z.shiftr a b) with v in K
  end.
Ltac kill K := exfalso; lit32 K; fold_bits K; first [ klia K | unsign K; klia K | dead K ].

(* [comment removed for export] *)
Ltac kill_align K G16 :=
  exfalso; apply K; apply land7_of_mod8; [lia|];
  first [ apply align_mod8_of16; [exact G16| reflexivity]
        | apply mod8_of_mod16; assumption
        | apply mod8_of_mod16; apply align16_add; [assumption| reflexivity] ].

Definition ws_emu_entry : Z := 0x18698.
Definition WS_Assert_entry : Z := 0x182d4.
Definition WS_MarkOverflow_entry : Z := 0x19ecc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ws_emu_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (WE : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 WE) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma ws_emu_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (WS : Z) (w : ws_rec) (e : wsemu_rec),
    a0 = Z_to_bv 64 WS ->
    rw_cells rsegs m WS (ws_cells w) -> length (ws_id w) = 4%nat ->
    rw_cells rsegs m (ws_s w) (wsemu_cells e) ->
    WS mod 8 = 0 -> ws_s w mod 8 = 0 -> 4096 <= WS -> 4096 <= ws_s w ->
    mem_inv rsegs m ->
    evt rsegs (ws_emu_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (ws_s w) m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ws_emu_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until e. intros A0 WSC IDL WEC WS8 WE8 WSlo WElo MI.
  rewrite A0. unfold ws_emu_entry.
  pose proof (rw_cells_bound _ _ _ _ WSC) as WSB. rewrite (ws_cells_size w IDL) in WSB.
  pose proof (rw_cells_bound _ _ _ _ WEC) as WEB. cbn [cells_size csize Nat.add wsemu_cells] in WEB.
  unfold ws_cells in WSC. unfold wsemu_cells in WEC.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  zstep. if_cases K1; zify_cond K1. { kill K1. } clear K1.
  zstep. zstep. if_cases K2; zify_cond K2. { exfalso. apply K2. apply land7_of_mod8; [lia| exact WS8]. } clear K2.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K3; zify_cond K3. { kill K3. } clear K3.
  zstep. zstep. if_cases K4; zify_cond K4. { exfalso. apply K4. apply land7_of_mod8; [lia| exact WE8]. } clear K4.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. if_cases K5; zify_cond K5. { kill K5. } clear K5.
  zstep.
  apply evt_done. unfold ws_emu_post.
  do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition ws_state {AI : AllocSpec LayoutPU} (H : henv) (m : mem) (E : option (AS * Z * Z)) : Prop :=
  match E with
  | None => ws0_obj LayoutPU H m
  | Some (A, wa, vep) => ws1_obj LayoutPU H A m wa vep /\ 4096 <= wa /\ wa + 40 <= alloc_ceiling /\ 4096 <= vep /\ vep < 2^64 /\ wa mod 16 = 0
  end.

End CEIL.

Definition WS_Assert_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Section Assert.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma WS_Assert_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (H : henv) (E : option (AS * Z * Z)) (lo : Z),
      a0 = Z_to_bv 64 (h_ws H) ->
      ws_state H m E ->
      glob_ok LayoutPU VIU H m -> henv_geom H -> img_okU m ->
      bv_unsigned sp <= h_sp H ->
      stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs m ->
      evt rsegs (WS_Assert_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 WS_Assert_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. intros A0 WSX GLOB HG IMG SPH ST LO CEIL MI.
    rewrite A0. unfold WS_Assert_entry.
    pose proof alloc_ceiling_val as ACV.
    (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (Ews : h_ws H = h_sp H + 1080) by reflexivity.
    assert (Ewb : h_wsbuf H = h_sp H + 16) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (WS8 : (h_sp H + 1080) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    assert (WE8 : (h_sp H + 16) mod 8 = 0) by (apply align_mod8_of16; [exact G16| reflexivity]).
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]). rewrite EBSS in BSS. cbn [vi_bss VIU al_segs LayoutPU] in BSS.
    cbn [al_segs LayoutPU] in CP.
    (first [ dand5 IMG as _ _ _ GCP _ | destruct IMG as (_ & _ & _ & GCP & _) ]). unfold GOT_cp in GCP.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    destruct E as [[[A wa] vep]|].
    - (* [comment removed for export] *)
      (first [ dand6 WSX as WS1 WAlo WAhi VEPlo VEPhi WA16 | destruct WSX as (WS1 & WAlo & WAhi & VEPlo & VEPhi & WA16) ]).
      (first [ dex2 WS1 as id pad; dand7 WS1 as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WS1 as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WS1 as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]).
      cbn [al_segs LayoutPU] in WSC, WEC, WAC.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS1 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
      rewrite Ews in WSC. rewrite Ewb in WSC, WEC, WAC. rewrite Ews.
      carve_frame 16%nat ST.
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| exact WS8]. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| exact WE8]. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. apply K. apply land7_of_mod8; [lia|]. replace (h_sp H + 16 + 1016) with (h_sp H + 16 + 8 * 127) by lia. apply align_mod8_of16; [exact G16| reflexivity]. }
      clear K.
      (* [comment removed for export] *)
      zstep. zstep.
      call_lit (ws_emu_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1080)
              (WSR id (h_sp H + 16) 0 0 (h_sp H + 16 + 1016)) (WER 1016 0 wa (wa + 24))) by (idtac;
        lazymatch goal with
        | |- rw_cells _ _ _ (ws_cells _) => exact WSC
        | |- rw_cells _ _ _ (wsemu_cells _) => exact WEC
        | |- length _ = _ => exact IDL
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => reflexivity
        | |- _ => cbn [ws_s]; first [exact WS8 | exact WE8 | lia]
        end).
      cbn [ws_s].
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| exact WE8]. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      (* [comment removed for export] *)
      do 14 zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| apply mod8_of_mod16; exact WA16]. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. if_cases K; zify_cond K. { kill K. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. zstep. zstep.
      try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold WS_Assert_post.
      do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
    - (* [comment removed for export] *)
      (first [ dex1 WSX as id; dand3 WSX as IDOK WSC WEC | dand4 WSX as id IDOK WSC WEC | destruct WSX as (id & IDOK & WSC & WEC) ]).
      cbn [al_segs LayoutPU] in WSC, WEC.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      rewrite Ews in WSC. rewrite Ewb in WSC, WEC. rewrite Ews.
      carve_frame 16%nat ST.
      zstep. zstep. zstep. zstep.
      zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| exact WS8]. } clear K.
      zstep. zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| exact WE8]. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K.
      { exfalso. apply K. apply land7_of_mod8; [lia|]. replace (h_sp H + 16 + 1016) with (h_sp H + 16 + 8 * 127) by lia. apply align_mod8_of16; [exact G16| reflexivity]. }
      clear K.
      zstep. zstep.
      call_lit (ws_emu_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h_sp H + 1080)
              (WSR id (h_sp H + 16) 0 0 (h_sp H + 16 + 1016)) (WER 1016 0 0 (h_sp H + 16 + 16))) by (idtac;
        lazymatch goal with
        | |- rw_cells _ _ _ (ws_cells _) => exact WSC
        | |- rw_cells _ _ _ (wsemu_cells _) => exact WEC
        | |- length _ = _ => exact IDL
        | |- mem_inv _ _ => assumption
        | |- @eq word _ _ => reflexivity
        | |- _ => cbn [ws_s]; first [exact WS8 | exact WE8 | lia]
        end).
      cbn [ws_s].
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { exfalso. apply K. apply land7_of_mod8; [lia| exact WE8]. } clear K.
      zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K; zify_cond K. 2:{ kill K. } clear K.
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep.
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K. { kill K. } clear K.
      zstep. zstep. zstep. zstep.
      try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold WS_Assert_post.
      do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  Qed.
End Assert.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition WS_MarkOverflow_post {AI : AllocSpec LayoutPU} (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (H : henv) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(h_ws H, h_ws H + 40)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ ws0_obj LayoutPU H m'.

End CEIL2.

Section MarkOverflow.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  (* [comment removed for export] *)
End MarkOverflow.

