(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfB_w7base InfB_w6base U2BIface_fit2_draft InfB_itcall InfB_llpost.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.U1B Require Import U2BKit U2BKit_p04 InfBTraps InfB_w6base InfB_w6garm.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* zlib 1.4 stores the codes pointer into distcode
     as well as lencode (inflate.c l.820; combined image 0x8f470 sd t0,0(a4)), so the state handed to inflate_table has
     dc = CDyn 0. st_dc0 / sinv_dc0 carry sinv across that store (in LENLENS no clause of sinv reads dc beyond its
     range). *)
  Definition st_dc0 (st : ist) : ist :=
    IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
        (t_length st) (t_offset st) (t_extra st) (t_lc st) (CDyn 0) (t_lb st) (t_db st)
        (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

  Lemma sinv_dc0 : forall cx st lf cf, sinv cx st lf cf -> t_mode st = LENLENS -> sinv cx (st_dc0 st) lf cf.
  Proof.
    intros cx st lf cf (R & W & P & Mo) Hm.
    destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    cbn in Hm. subst mode. unfold sinv, st_dc0.
    split; [| split; [exact W| split; [exact P|]]].
    - unfold IDefs.RNG in *. cbv zeta in *. cbn in *.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      repeat match goal with |- _ /\ _ => split end; try assumption; cbv [N_CODES]; lia.
    - unfold MODE in *. cbn in *. destruct Mo as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
      split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
      split; [intros C; exfalso; unfold codes_liveP in C; cbv [LEN_ LIT LENLENS] in C; lia|].
      split; [exact M6|]. split; [exact M7|]. split; [exact M8|]. split; [exact M9| exact M10].
  Qed.

  (* [U14B] A2 2026-11-12: ll_call re-stated at its 1.4 pc 0x8f438, the join of the fill path (0x8f434) and the no-fill
     path (0x8f380 bltu a0,a6,0x8f438). There t0 = codes (S + 1384; 0x8f37c ld t0,88(s1)), a4 = &distcode (S + 128;
     0x8f378 / 0x8f434 ld a4,208(s1)), s6 = bits (0x8f358 mv s6,t0); a3 = &next, a0 = &lencode and a2 = &lenbits are
     loaded after the join (0x8f438, 0x8f448, 0x8f464). Then next := distcode := lencode := codes, lenbits := 7, and the
     CODES call 0x8f4bc (ra = 0x8f4c0) -> ll_post. 1.3.1 entered at 0x8ef00 with t0 = bits, t1 = codes, a3 = &next,
     a4 = &lenbits and stored next and lencode only. *)
  Lemma ll_call : forall (cx : ictx) (ly : ilay) (st : ist) (cs : Z) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x6 x7 x10 x11 x12 x13 x15 x16 x17 x26 x28 x29 x30 x31 : word) (m : amem),
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f54c CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> t_shave st = 19 -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 x11 x12 x13 (Z_to_bv 64 (c_p cx + 128)) x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x26 (Z_to_bv 64 (c_q cx + t_cin st))
               (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x8f428) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ENV HCL CTX PAYR PLEN MODE SH19 SI ARR VIS HID KA.
    pose proof (ll_itc cx st lf cf wf SI MODE SH19 (proj1 ARR)) as ITC.
    pose proof (sinv_dc0 cx st lf cf SI MODE) as SI0.
    pose proof (proj1 SI0) as RNG0.
    destruct (ex_intro (fun r0 => r0 = resA CODES lf 0 19 0 7 cf wf) _ eq_refl) as [r ER].
    destruct (ll_bridge lf cf wf r ITC ER) as (BOK & BFS & RT & RW & RB & RX).
    inf_arm_open_s. subst shave.
    zrung [0x96a34].
    replace (S + 1384) with (S + 1384 + 4 * 0) in SSC by lia.
    eapply (inf_itcall AI rng_fs L RNG stA LB LBc m0 payload POST (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
              (IST mode last flags cs cout hold bits out ret len offset extra (CDyn 0) (CDyn 0) 7 db ncode nlen ndist 19 0 whave wnext) lf cf wf fo fw)
      with (isd := false) (ty := InflateState.CODES) (lens_ofs := 0) (codes := 19) (bits := 7) (RA := 0x8f4b0) (r := r);
      [exact ENV| exact CTX0| inf_vis_close| inf_hid_close| exact PLEN| reflexivity| exact ITC| exact ER| reflexivity| lia| reflexivity| reflexivity
      | reflexivity| icx_cbn; f_equal; lia| reflexivity| reflexivity| reflexivity| reflexivity| ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' VIS' HID' RET.
    eapply (ll_post AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6341056 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
              (st_itab (IST mode last flags cin cout hold bits out ret len offset extra (CDyn 0) (CDyn 0) 7 db ncode nlen ndist 19 0 whave wnext) false (it_bits r) (it_table r))
              cs lf (arr_get (it_tbl r)) (arr_get (it_work r)) fo);
      [exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE
      | exact (rng_ll_after _ _ lf cf (arr_get (it_tbl r)) (it_bits r) (it_table r) RNG0 RB RX RT)
      | split; [exact RW| exact (proj2 ARR)]| exact VIS'| exact HID'| exact KA| exact RET| | ].
    - intros E0. destruct (BOK E0) as (TOK & B15 & TX).
      pose proof (sinv_ll_ct _ _ lf cf (arr_get (it_tbl r)) (it_bits r) (it_table r) SI0 MODE ltac:(clear - B15; lia) ltac:(clear - B15; lia)
                    ltac:(clear - TX; lia) ltac:(clear - TX; lia) TOK RT) as (SI1 & ME1).
      split; [exact SI1| exact (Z.lt_le_incl _ _ ME1)].
    - intros NE. destruct (BFS NE) as (ET & EBt). rewrite ET, EBt.
      pose proof (sinv_ll_bad _ _ lf cf (arr_get (it_tbl r)) (it_ret r mod 18446744073709551616) SI0 MODE
                    ltac:(apply Z.mod_pos_bound; reflexivity) RT) as (SI1 & ME1).
      split; [exact SI1| exact ME1].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
