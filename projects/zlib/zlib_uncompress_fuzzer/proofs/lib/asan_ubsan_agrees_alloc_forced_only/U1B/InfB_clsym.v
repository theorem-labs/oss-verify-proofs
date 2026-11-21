(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfPure_w7e InfAGlue_w7 InfAGlue_w7b InfPure_table InfPure_itab InfPure_lenlens InfPure_codelens UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull InfB_w6base InfB_w6kit InfB_w6garm InfB_cldone_base InfB_clbase InfB_clbase2 InfB_w7tab16 InfB_clreg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04 InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation CLH cx ly N := (clhead_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLR cx ly N := (clres_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLP cx ly pc N := (clrep_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh pc N).
  Notation CLD cx ly := (cldone_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).

  Lemma cl_res : forall (N : nat) (cx : ictx) (ly : ilay),
    CLH cx ly N -> CLD cx ly -> CLP cx ly 0x8f878 N -> CLP cx ly 0x8f7fc N -> CLP cx ly 0x8f8f4 N -> CLR cx ly N.
  Proof.
    intros N cx ly HEAD DONE H16 H17 H18. unfold clres_stmt, CLRES_MS. intros until B. intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HC HBE HH HB40 HBX.
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & LC0 & LB1 & LB15 & NX0 & NX1 & TOK & RLF & RCF).
    assert (CB15 : forall i, 0 <= i < 2 ^ t_lb st -> 1 <= code_bits (rdc cf (CDyn 0) i) <= 15 /\ 2 ^ t_lb st <= t_nx st).
    { intros i Hi. destruct (ctab_bits cf (t_lb st) (t_nx st) i TOK Hi) as (A & C). unfold rdc. rewrite Z.add_0_l. split; [lia| exact C]. }
    pose proof (buf_ok_pulled _ _ _ _ ci H B SI HC HBE HH HB40) as BUF.
    revert HEAD DONE H16 H17 H18. inf_arm_open_s. intros HEAD DONE H16 H17 H18.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    assert (IDX0 : 0 <= H mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB1; lia).
    destruct (CB15 _ IDX0) as (CBE & NXR).
    assert (IND0 : 0 <= H mod 2 ^ lb < nx) by (clear - IDX0 NXR; lia).
    remember (H mod 2 ^ lb) as i0 eqn:EI0. apply w7hide_in in EI0.
    assert (RDR : 0 <= rdc cf (CDyn 0) i0 < 4294967296) by (unfold rdc; apply RCF; clear - IND0 NX1; unfold N_CODES; lia).
    pose proof (code_val_range (rdc cf (CDyn 0) i0)) as CVR.
    set (c0 := rdc cf (CDyn 0) i0) in *.
    eapply (cl_res_a RNG POST) with (c := c0); [exact RDR| intros KV x10'| intros KV x10'].
    -
      eapply (cl_sym_g RNG POST) with (hb := code_bits c0); [clear - CBE; lia|]. intros x11'.
      zs. zs.
      eapply (cl_sym_b1 RNG POST) with (j := shave); [clear - SH0 SH1 NL2 ND2; lia|].
      zs. zs.
      eapply (cl_sym_b2 RNG POST) with (j := shave); [clear - SH0 SH1 NL2 ND2; lia|].
      zs. rewrite (lnot64 (S + 168)) by (clear - S1 S2 ATB; lia).
      eapply (cl_sym_b3 RNG POST) with (LA := S + 168) (j := shave); [clear - S1 S2 ATB; lia| clear - SH0 SH1 NL2 ND2; lia|].
      zs. zs. setreg 11 (Z_to_bv 64 (S + 168 + 2 * shave)) ltac:(f_equal; clear; lia).
      lazymatch type of MU with munch _ _ ?mc =>
        pose proof (shadow_bytes_munch _ _ mc _ _ _ SHS MU DJS) as SHS1;
        pose proof (tab_sh0 mc S 897 (S + 168 + 2 * shave) SHS1 S8 ltac:(clear - SH0 SH1 NL2 ND2; lia) ltac:(clear - S1; lia)) as RDS3;
        pose proof (tab_sh_acc RNG S 897 (S + 168 + 2 * shave) RSS S8 ltac:(clear - SH0 SH1 NL2 ND2; lia) ltac:(clear - S1; lia)) as ACS3
      end.
      zs. zs. zs. zs.
      eapply (cl_sym_drop RNG POST) with (H := H) (B := B) (c := c0); [exact RDR| exact CBE| exact HH| exact HBX| exact HB40|].
      zs.
      set (val := code_val c0) in *. set (hb := code_bits c0) in *.
      lazymatch type of LENS with f16arr _ ?mc _ _ _ =>
        assert (SOK : store_ok bsegs mc (Z_to_bv 64 (S + 168 + 2 * shave)) 2 = true)
          by (eapply (f16arr_store_ok bsegs mc (S + 168) 320 lf shave); [exact LENS| clear - SH0 SH1 NL2 ND2; lia| reflexivity]);
        zstep;
        pose proof (f16arr_write bsegs mc (S + 168) 320 lf shave (Z_to_bv 64 val) val LENS ltac:(clear - SH0 SH1 NL2 ND2; lia) eq_refl) as LENS'
      end.
      store_done.
      zs. zs. zs.
      pose proof (lens_rng_upd lf shave val RLF ltac:(clear - CVR; subst val; lia)) as RLF'.
      pose proof (lens15_upd lf shave val L15 ltac:(clear - KV; subst val; lia)) as L15'.
      pose proof (buf_ok_drop _ _ ci H B hb BUF ltac:(clear - CBE HBX; subst hb; lia)) as BUF'.
      destruct (sinv_clb _ _ lf cf ci (H / 2 ^ hb) (B - hb) (shave + 1) (fupd lf shave val) SI MODE BUF' ltac:(clear - SH0; lia) ltac:(clear - HJN; gcbn; lia) RLF' L15') as (SI' & ME').
      unfold st_cl in SI', ME'. gcbn. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI', ME'.
      zs. zbr0 KJ.
      + eapply (HEAD (IST mode last flags ci cout (H / 2 ^ hb) (B - hb) out ret len offset extra lc dc lb db ncode nlen ndist (shave + 1) nx whave wnext) (fupd lf shave val) cf wf fo);
          [clear - HN HJN; gcbn; lia| clear - KJ; gcbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI'| exact ARR| inf_vis_close| inf_hid_close
          | eapply KALL_mono; [| exact KA]; exact ME'].
      + zs.
        eapply (DONE (IST mode last flags ci cout (H / 2 ^ hb) (B - hb) out ret len offset extra lc dc lb db ncode nlen ndist (shave + 1) nx whave wnext) (fupd lf shave val) cf wf fo);
          [exact CTX0| exact PAYR| exact PLEN| exact MODE| clear - KJ; gcbn; lia| exact SI'| exact ARR| inf_vis_close| inf_hid_close
          | eapply KALL_mono; [| exact KA]; exact ME'].
    -
      eapply (cl_rep_disp RNG POST) with (v := code_val c0) (B := B); [clear - KV CVR; lia| clear - BUF; unfold buf_ok in BUF; lia| intros K16 x22'| intros K17 x22'| intros K18 x22'].
      + apply w7hide_out in EI0.
        eapply (H16 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B c0);
          [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
          | exact HC| exact HBE| exact HH| exact HB40| exact RDR| exact CBE| exact HBX].
      + apply w7hide_out in EI0.
        eapply (H17 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B c0);
          [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
          | exact HC| exact HBE| exact HH| exact HB40| exact RDR| exact CBE| exact HBX].
      + apply w7hide_out in EI0.
        eapply (H18 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B c0);
          [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
          | exact HC| exact HBE| exact HH| exact HB40| exact RDR| exact CBE| exact HBX].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
