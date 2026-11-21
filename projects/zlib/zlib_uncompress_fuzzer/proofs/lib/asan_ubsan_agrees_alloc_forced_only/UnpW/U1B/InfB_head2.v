(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfAGlue_w7 InfPure InfPure_w7 InfPure_head.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface U2BCall InfBBase InfBKit AdlUBIface InfB_head.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

(* [comment removed for export] *)
Ltac ck_join2 n1 n2 okpc :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      let p1 := eval vm_compute in (bv_key (Z_to_bv 5 n1)) in
      let p2 := eval vm_compute in (bv_key (Z_to_bv 5 n2)) in
      let H := fresh "CONT" in
      enough (H : forall y1 y2 : word, evtF segs RNG Q (MS (tset p1 y1 (tset p2 y2 R)) F (Z_to_bv 64 okpc) fc rv m ro));
      [ | let y1 := fresh "y" in let y2 := fresh "y" in intros y1 y2;
          let g := lazymatch goal with |- ?g => g end in
          let g' := eval cbv beta iota delta [tset mkR] in g in change g' ]
  end.
Ltac ck_doneJ2 n1 n2 okpc :=
  repeat (lazymatch goal with
          | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              let b := eval vm_compute in (Z.eqb pc okpc) in
              lazymatch b with false => zstep | true => fail end
          end);
  lazymatch goal with
  | CONT : forall y1 y2 : word, evtF _ _ _ _ |- _ => let v1 := reg_val n1 in let v2 := reg_val n2 in exact (CONT v1 v2)
  end.
Ltac ck_branchJ2 U1 U2 JOIN CK :=
  ck_join2 U1 U2 JOIN;
  [ let K := fresh "K" in let K2 := fresh "K2" in
    zstep; if_cases K; zify_cond K;
    try (ck_doneJ2 U1 U2 JOIN);
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
            end);
    if_cases K2;
    first [ exfalso; zify_lts K2; clear - CK K K2; Z.div_mod_to_equations; lia
          | ck_doneJ2 U1 U2 JOIN ]
  | try clear CK ].   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).
  Hypothesis ADLN : adler32_null_stmtU.

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).

  (* [comment removed for export] *)
  Lemma head_loop : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x7 x10 x14 x19 x22 x23 x26 x28 x30 x31 : word) (m : amem) (ci H B : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = HEAD -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_n cx - ci < Z.of_nat N ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> B < 16 -> 0 <= H < 2 ^ B ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 (Z_to_bv 64 (t_bits st)) x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               x10 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 B) (Z_to_bv 64 5) x14 (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 B) (Z_to_bv 64 (c_n cx - t_cin st))
               (Z_to_bv 64 (l_Zs ly)) x19 x22 (Z_to_bv 64 H) (Z_to_bv 64 2147450880) x26
               x23 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_n cx - ci)) x28 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) x30 x31)
          FR (Z_to_bv 64 0x8e304) fc None m (seg_rom bsegs)).
  Proof.
    induction N as [|N IH]; intros until B; intros CTX PAYR PLEN MODE SI ARR VIS HID KA HN HC HBE HB16 HH; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open.
    assert (B0 : 0 <= B) by lia.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    zs. (* [comment removed for export] *) zbr0 KH.
    - (* [comment removed for export] *)
      destruct (unp_check_mu bsegs _ _ _ _ _ (D + ci) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
      zrung [0x8e32c].
      zs. (* [comment removed for export] *) rewrite sxb_sval.
      ck_branchJ 5 0x8e334 CK.
      pose proof (pay_read bsegs _ D payload ci PAYB ltac:(lia)) as RDP. fold (bz payload ci) in RDP.
      pose proof (bz_range payload ci PAYR) as BZR.
      zs. zs. cbv beta. rewrite (bz_val payload ci PAYR).
      Time zrung [0x8e360].
      rewrite (pull_hold H (bz payload ci) B) by lia.
      pose proof (pull_bound H B (bz payload ci) ltac:(lia) ltac:(lia) BZR) as PB.
      replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
      zs. (* [comment removed for export] *) zbr0 KB2.
      + (* [comment removed for export] *)
        eapply (IH (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (ci + 1) (H + bz payload ci * 2 ^ B) (B + 8));
          [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
      + (* [comment removed for export] *)
        zs.
        eapply (head_main AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh ADLN
                  (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (ci + 1) (H + bz payload ci * 2 ^ B) (B + 8));
          [exact CTX0| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    - (* [comment removed for export] *)
      Time zrung [0x93534].
      assert (ECI : ci = n) by lia. subst ci.
      replace ((n - cin) ≪ 3 + bits) with B by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; lia).
      lazymatch goal with HF : rw_cells bsegs _ SPA _ |- _ =>
        replace (D + cin + (n - cin) mod 4294967296) with (D + n) in HF by (rewrite Z.mod_small by lia; lia) end.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Theorem head_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8e2bc HEAD.
  Proof.
    intros cx ly. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    inf_arm_open.
    Time zrung [0x8e2e4].
    zs. (* [comment removed for export] *) zbr KB16.
    - (* [comment removed for export] *)
      Time zrung [0x8e304].
      eapply (head_loop (Z.to_nat (n - cin + 1)) (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m cin hold bits);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    - (* [comment removed for export] *)
      Time zrung [0x8ff38].
      eapply (head_main AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh ADLN
                (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m cin hold bits);
        [exact CTX0| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
  Qed.
End S.
End CANSEC1.
