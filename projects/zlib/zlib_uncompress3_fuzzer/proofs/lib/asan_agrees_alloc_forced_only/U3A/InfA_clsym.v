(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfPure_w7e InfAGlue_w7 InfAGlue_w7b InfPure_table InfPure_lenlens InfPure_codelens.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull InfA_w6base InfA_w6kit InfA_cldone_base InfA_clbase InfA_clbase2 InfA_clreg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
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
  Notation CLN cx ly N := (clnext_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLP cx ly pc N := (clrep_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh pc N).
  Notation CLD cx ly := (cldone_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).

  Lemma cl_next : forall (N : nat) (cx : ictx) (ly : ilay), CLH cx ly N -> CLD cx ly -> CLN cx ly N.
  Proof.
    intros N cx ly HEAD DONE. unfold clnext_stmt, CLNEXT_MS. intros until m. intros HN CTX PAYR PLEN MODE SI ARR VIS HID KA.
    revert HEAD DONE. inf_arm_open. intros HEAD DONE.
    zs. zs. zs. zbr0 KJ.
    - eapply (HEAD (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact HN| clear - KJ; gcbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA].
    - zs.
      eapply (DONE (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| clear - KJ; gcbn; lia| exact SI| exact ARR| exact VISf| exact HID| exact KA].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
  Lemma cl_res : forall (N : nat) (cx : ictx) (ly : ilay),
    CLN cx ly N -> CLP cx ly 0x8f740 N -> CLP cx ly 0x8f6d8 N -> CLP cx ly 0x8f7a8 N -> CLR cx ly N. (* the 1.4 repeat-16 / repeat-18 entries; the mover had left COPY-region pcs *)
  Proof.
    intros N cx ly HNEXT H16 H17 H18. unfold clres_stmt, CLRES_MS. intros until B. intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HC HBE HH HB40 HBX.
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & LC0 & LB1 & LB15 & NX0 & NX1 & TOK & RLF & RCF).
    assert (CB15 : forall i, 0 <= i < 2 ^ t_lb st -> 1 <= code_bits (rdc cf (CDyn 0) i) <= 15 /\ 2 ^ t_lb st <= t_nx st).
    { intros i Hi. destruct (ctab_bits cf (t_lb st) (t_nx st) i TOK Hi) as (A & C). unfold rdc. rewrite Z.add_0_l. split; [lia| exact C]. }
    pose proof (buf_ok_pulled _ _ _ _ ci H B SI HC HBE HH HB40) as BUF.
    revert HNEXT H16 H17 H18. inf_arm_open. intros HNEXT H16 H17 H18.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    assert (IDX0 : 0 <= H mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB1; lia).
    destruct (CB15 _ IDX0) as (CBE & NXR).
    assert (IND0 : 0 <= H mod 2 ^ lb < nx) by (clear - IDX0 NXR; lia).
    remember (H mod 2 ^ lb) as i0 eqn:EI0. apply w7hide_in in EI0.
    pose proof (dtab_dyn m S cf 0 nx CODES RCF ltac:(clear; lia) NX0 ltac:(clear - NX1; lia)) as DT.
    replace (S + 1384 + 4 * 0) with (S + 1384) in DT by (clear; lia).
    destruct (DT i0 IND0) as (RDR & RD0 & RD1 & RD2).
    pose proof (code_val_range (rdc cf (CDyn 0) i0)) as CVR.
    set (hb := code_bits (rdc cf (CDyn 0) i0)) in *. set (val := code_val (rdc cf (CDyn 0) i0)) in *.
    eapply (cl_vaddr RNG POST) with (TA := S + 1384) (i := i0); [clear - IND0 NX1; lia| clear - S1 S2 ATB; lia|].
    pose proof (tab_sh0 m S 897 (S + 1384 + 4 * i0 + 2) SHS S8 ltac:(clear - IND0 NX1; lia) ltac:(clear - S1; lia)) as RDS.
    pose proof (tab_sh_acc RNG S 897 (S + 1384 + 4 * i0 + 2) RSS S8 ltac:(clear - IND0 NX1; lia) ltac:(clear - S1; lia)) as ACS.
    zs. zs. zs. zs.
    zs. rewrite (zx16_small val) by (exact CVR).
    zs. zs. zbr0 KV.
    -
      zs. zs. zbr0 K16.
      +
        eapply (H16 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B hb);
          [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
          | exact HC| exact HBE| exact HH| exact HB40| exact CBE| exact HBX].
      + zs. zs. zbr0 K17.
        *
          eapply (H18 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B hb);
            [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
            | exact HC| exact HBE| exact HH| exact HB40| exact CBE| exact HBX].
        *
          eapply (H17 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B hb);
            [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
            | exact HC| exact HBE| exact HH| exact HB40| exact CBE| exact HBX].
    -
      zs. zs.
      eapply (cl_sym_a RNG POST) with (j := shave); [clear - SH0 SH1 NL2 ND2; lia|].
      zs. zs.
      eapply (cl_sym_b RNG POST) with (j := shave); [clear - SH0 SH1 NL2 ND2; lia|].
      zs. zs.
      lazymatch type of MU with munch _ _ ?mc =>
        pose proof (shadow_bytes_munch _ _ mc _ _ _ SHS MU DJS) as SHS1;
        pose proof (tab_sh0 mc S 897 (S + 168 + 2 * shave) SHS1 S8 ltac:(clear - SH0 SH1 NL2 ND2; lia) ltac:(clear - S1; lia)) as RDS3;
        pose proof (tab_sh_acc RNG S 897 (S + 168 + 2 * shave) RSS S8 ltac:(clear - SH0 SH1 NL2 ND2; lia) ltac:(clear - S1; lia)) as ACS3
      end.
      zs. zs. zs. zs.
      eapply (cl_drop RNG POST) with (H := H) (B := B) (hb := hb); [exact HH| clear - CBE HBX; lia| exact HB40|].
      lazymatch type of LENS with f16arr _ ?mc _ _ _ =>
        assert (SOK : store_ok asegs mc (Z_to_bv 64 (S + 168 + 2 * shave)) 2 = true)
          by (eapply (f16arr_store_ok asegs mc (S + 168) 320 lf shave); [exact LENS| clear - SH0 SH1 NL2 ND2; lia| reflexivity]);
        zstep;
        pose proof (f16arr_write asegs mc (S + 168) 320 lf shave (Z_to_bv 64 val) val LENS ltac:(clear - SH0 SH1 NL2 ND2; lia) eq_refl) as LENS'
      end.
      store_done.
      zs. zs.
      pose proof (lens_rng_upd lf shave val RLF ltac:(clear - CVR; lia)) as RLF'.
      pose proof (lens15_upd lf shave val L15 ltac:(clear - KV; lia)) as L15'.
      pose proof (buf_ok_drop _ _ ci H B hb BUF ltac:(clear - CBE HBX; lia)) as BUF'.
      destruct (sinv_clb _ _ lf cf ci (H / 2 ^ hb) (B - hb) (shave + 1) (fupd lf shave val) SI MODE BUF' ltac:(clear - SH0; lia) ltac:(clear - HJN; gcbn; lia) RLF' L15') as (SI' & ME').
      unfold st_cl in SI', ME'. gcbn. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI', ME'.
      eapply (HNEXT (IST mode last flags ci cout (H / 2 ^ hb) (B - hb) out ret len offset extra lc dc lb db ncode nlen ndist (shave + 1) nx whave wnext) (fupd lf shave val) cf wf fo);
        [clear - HN HJN; gcbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI'| exact ARR| inf_vis_close| inf_hid_close
        | eapply KALL_mono; [| exact KA]; exact ME'].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the free v0 / v16 VIS words *)
  Qed.
End S.
End CANSEC1.
