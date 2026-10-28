(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Pj_steps Pj_loc_defs Pj_loc_get Pj_os_defs Pj_os_dtor Sj_h_kit Atp_h_defs El_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition osd_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo OS : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 64, q); (OS, OS + 8); (OS + 136, OS + 144)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ (exists jk : list byte, rw_cells usegs m' OS [CB 288 jk]).

Lemma osd_spec : ios_dtor_stmt ->
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (q lo OS : Z) (pb pp ep : word) (fill : Z) (dum j148 j284 : list byte),
    stk usegs m lo q -> lo <= q - 64 -> GLOBALS_TOP <= lo -> q <= OS -> OS + 288 < 2 ^ 62 ->
    rw_cells usegs m OS (os_cells OS pb pp ep fill dum j148 j284) ->
    rw_cells usegs m PJ_GOT_VT [C8 (wz PJ_IOS_VT); C8 (wz PJ_SB_VT)] -> mem_inv usegs m ->
    evt usegs (osd_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 EL_OSDTOR) fc None m (seg_rom usegs)).
Proof.
  intros IOSD. intros until j284. intros ST LO GLO QOS OSH OSC GOT MI.
  unfold GLOBALS_TOP, EL_OSDTOR in *. unfold MallocRep.wz in GOT.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 64, q); (OS, OS + 8); (OS + 136, OS + 144)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

  unfold os_cells in OSC.
  destruct (proj1 (rw_cells_app usegs m OS (sb_cells pb pp ep dum) _) OSC) as [SB REST]. cbn [sb_cells cells_size csize Nat.add length] in REST.
  destruct (proj1 (rw_cells_app usegs m _ [_] _) REST) as [OVP IOS]. cbn [cells_size csize Nat.add] in IOS. clear OSC REST.
  replace (OS + Z.of_nat 128) with (OS + 128) in OVP, IOS by lia. replace (OS + 128 + Z.of_nat 8) with (OS + 136) in IOS by lia.
  unfold sb_cells in SB.

  step. carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
  hstep. hstep.

  step. step. step. step. step. step.
  eapply evt_cut; [eapply os_base_dtor_spec; assumption|]. cbv beta. intros ms1 ->.
  replace (ret_pc (Z_to_bv 64 0x3df64)) with (Z_to_bv 64 0x3df64) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  step. step. step. hstep.

  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with H : rw_cells usegs mx OS _ |- _ => rename H into SB1 end end.
  destruct (proj1 (rw_cells_app usegs _ OS [_] _) SB1) as [_ SBL]. cbn [cells_size csize Nat.add] in SBL.
  destruct (proj1 (rw_cells_app usegs _ _ [_] _) SBL) as [LOCC _]. replace (OS + Z.of_nat 8) with (OS + 8) in LOCC by lia. clear SBL.
  eapply evt_cut; [eapply (locale_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (OS + 8)); [exact LOCC| lia| assumption]|].
  cbv beta. intros ms2 (a0' & a1' & ->).
  replace (ret_pc (Z_to_bv 64 0x3df7c)) with (Z_to_bv 64 0x3df7c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

  step. step. step. step. release_frame FR ST q. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  assert (U : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply evt_mono; [eapply (IOSD ra (Z_to_bv 64 q)) with (lo := lo) (OS := OS); rewrite ?U; try eassumption; try lia|].
    intros ms' P. exact P. }
  cbv beta. intros ms' PO. unfold ios_dtor_post in PO. rewrite U in PO.
  destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & IOS4).

  pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
  lazymatch goal with H : rw_cells usegs m3 OS _ |- _ => rename H into SB3 end.
  lazymatch goal with H : rw_cells usegs m3 (OS + 128) _ |- _ => rename H into OVP3 end.
  apply (rw_cells_agree _ _ _ _ _ AG4) in SB3; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
  apply (rw_cells_agree _ _ _ _ _ AG4) in OVP3; [| intros a Ha; cbn in Ha; cbn [outside]; lia].
  unfold ios_cells in IOS4.
  pose proof (rw_cells_join _ _ _ _ _ SB3 OVP3 ltac:(cbn [cells_size csize Nat.add]; lia)) as J1.
  pose proof (rw_cells_join _ _ _ _ _ J1 IOS4 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
  destruct (rw_cells_forget _ _ _ _ J2) as [jk OSJ]. cbn [cells_size csize Nat.add] in OSJ.
  apply evt_done. unfold osd_post. do 15 eexists. exists m4. split; [reflexivity|].
  split; [| split; [| split; [exact MI4| split; [exact ST4| exists jk; exact OSJ]]]].
  - eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU4]]; unfold sub_fp; cbn [outside]; intros x Hx; lia.
  - eapply wmono_trans; [exact WM| exact WM4].
Qed.
End WithCeiling0.
