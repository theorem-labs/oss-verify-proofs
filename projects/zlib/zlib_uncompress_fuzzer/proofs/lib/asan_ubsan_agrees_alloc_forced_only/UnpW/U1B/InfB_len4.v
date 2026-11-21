(* reloc-zl14c *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfPure_w7h InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull InfB_w7lenr InfB_len2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation LXB cx ly := (LXB_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).
  Notation LXZ cx ly := (LXZ_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  (* [comment removed for export] *)
  Definition L_E3 (cx : ictx) (ly : ilay) (st : ist) (c1 c2 A5 S6 : Z) (x5 x6 x7 x10 x11 x13 x16 x17 x19 x21 x23 x28 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11
            (Z_to_bv 64 c2) x13 (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 A5) x16 x17
            (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880) (Z_to_bv 64 S6)
            x23 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (Z.shiftr c2 8)) x28 (Z_to_bv 64 (Z.shiftr c1 8)) (Z_to_bv 64 (code_bits c1)) x31)
       FR (Z_to_bv 64 0x918a0) fc None m (seg_rom bsegs).

  Lemma l_fin2 : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits was pad : word)
      (x5 x6 x7 x10 x11 x13 x16 x17 x19 x21 x23 x28 x31 : word) (m : amem) (c1 c2 A5 S6 : Z),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 7164) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits (Z_to_bv 64 0) was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    0 <= c1 < 4294967296 -> 0 <= c2 < 4294967296 -> 1 <= code_bits c1 <= 15 -> 1 <= code_bits c2 <= 15 -> code_bits c1 + code_bits c2 <= t_bits st ->
    A5 - S6 = t_bits st - code_bits c1 ->
    ((code_op c2 = 0 /\ code_val c2 < 256) \/ (16 <= code_op c2 <= 21 /\ 3 <= code_val c2 /\ code_val c2 + 2 ^ (code_op c2 - 16) - 1 <= 258) \/ (Z.land (code_op c2) 64 <> 0 /\ Z.land (code_op c2) 16 = 0)) ->
    evtF bsegs RNG POST (L_E3 cx ly st c1 c2 A5 S6 x5 x6 x7 x10 x11 x13 x16 x17 x19 x21 x23 x28 x31 m).
  Proof.
    intros until S6. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA HC1 HC2 HB1 HB2 HBB HAS HTERM.
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (cw_land31 c1 ltac:(lia)) as L31.
    unfold L_E3.
    remember (code_bits c1) as rb eqn:ERB.
    inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    pose proof (drop_bound hold bits rb ltac:(lia) ltac:(lia)) as DB.
    zrung [0x918b4]. change (Z.land c2 255) with (code_op c2).
    eapply (len_drop2 RNG POST) with (c1 := c1) (A5 := A5) (S6 := S6) (H := hold); [clear - HOLD0 P40; lia| exact HC1| rewrite <- ERB; clear - HB1; lia| clear - HAS HBB HB2 HB1 BITS0; lia|].
    rewrite <- ERB.
    replace (A5 - S6) with (bits - rb) by (clear - HAS; lia).
    zrung [0x918c8].
    destruct (sinv_pull _ _ lf cf cin (hold / 2 ^ rb) (bits - rb) SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & ME1).
    st_norm SI1. st_norm ME1.
    eapply (l_term AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
              (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout (hold / 2 ^ rb) (bits - rb) out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo) with (c := c2) (bk := rb);
      [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI1| exact ARR| inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; exact ME1| | | | | ];
      first [exact HTERM | clear - HC2 HB1 HB2 HBB; gcbn; lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
