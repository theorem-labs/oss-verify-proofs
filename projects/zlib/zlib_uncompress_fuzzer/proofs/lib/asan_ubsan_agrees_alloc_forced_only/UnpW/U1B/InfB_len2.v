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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7tab16 InfB_w7pull.
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
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* [comment removed for export] *)
  Definition LXB_STMT (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_extra st <> 0 ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x8e3e4 st x6 x7 x10 x11 x12 (Z_to_bv 64 (t_extra st)) x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).
  Definition LXZ_STMT (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 v328 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 v328 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF bsegs RNG POST (GARM_MS cx ly gp tp FR fc 0x919a4 st x6 x7 x10 x11 x12 x13 x14 x16 x19 x21 x22 x23 x26 x28 x29 x30 x31 m).

  (* [comment removed for export] *)
  Lemma l_term : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v24 v240 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits was pad : word)
      (x5 x6 x7 x10 x11 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) (m : amem) (c bk : Z),
    LXB_STMT cx ly -> LXZ_STMT cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 v16 v24 v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 7164) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits (Z_to_bv 64 bk) was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    0 <= c < 4294967296 -> 1 <= code_bits c <= t_bits st -> code_bits c <= 15 -> 0 <= bk <= 15 ->
    ((code_op c = 0 /\ code_val c < 256) \/ (16 <= code_op c <= 21 /\ 3 <= code_val c /\ code_val c + 2 ^ (code_op c - 16) - 1 <= 258) \/ (Z.land (code_op c) 64 <> 0 /\ Z.land (code_op c) 16 = 0)) ->
    evtF bsegs RNG POST
      (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) x10 x11
               (Z_to_bv 64 c) (Z_to_bv 64 (code_op c)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (t_bits st)) x16 x17
               (Z_to_bv 64 (l_Zs ly)) x19 x21 (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880) x22
               x23 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (Z.shiftr c 8)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x918c8) fc None m (seg_rom bsegs)).
  Proof.
    intros until bk. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA HCR HHB HB15 HBK HTERM.
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    pose proof (code_op_range c) as OPR. pose proof (code_val_range c) as VALR.
    pose proof (cw_land192 c ltac:(lia)) as L192. pose proof (cw_land63 c ltac:(lia)) as L63. pose proof (cw_mod64 c ltac:(lia)) as M64.
    set (hb := code_bits c) in *.
    inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    pose proof (drop_bound hold bits hb ltac:(lia) ltac:(lia)) as DB.
    destruct (sinv_pull _ _ lf cf cin (hold / 2 ^ hb) (bits - hb) SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & ME1).
    zs. rewrite L192.
    zrung [0x918f0]. rewrite L63.
    zrung [0x9192c]. rewrite (code_word_val c HCR).
    zs. rewrite M64. rewrite (Z.shiftr_div_pow2 hold hb) by lia.
    zrung [0x91940].
    set (val := code_val c) in *. set (op := code_op c) in *.
    zs. zbr0 KLIT.
    - (* [comment removed for export] *)
      destruct HTERM as [(OP0 & VAL0)|[(OP1 & _)|(O64 & _)]]; [| exfalso; lia | exfalso; rewrite KLIT in O64; apply O64; reflexivity].
      zrung [0x8e260].
      pose proof (sinv_len_set _ _ lf cf LIT val SI1 MODE ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
      st_norm SI1. st_norm ME1. st_norm SI2. subst mode.
      eapply (KD (IST LIT last flags cin cout (hold / 2 ^ hb) (bits - hb) out ret val offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI2| clear - ME1 HHB; unfold meas, Wm in *; icx_cbn; change (rank LIT) with 13; change (rank LEN) with 18 in *; lia| exact ARR| change LIT with 16205; inf_vis_close| inf_hid_close].
    - (* [comment removed for export] *)
      zrung [0x91948]. zs. zbr0 KEOB.
      + (* [comment removed for export] *)
        zrung [0x8e260].
        pose proof (sinv_len_set _ _ lf cf TYPE val SI1 MODE ltac:(right; right; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
        st_norm SI1. st_norm ME1. st_norm SI2. subst mode.
        eapply (KD (IST TYPE last flags cin cout (hold / 2 ^ hb) (bits - hb) out ret val offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
          [exact SI2| clear - ME1 HHB; unfold meas, Wm in *; icx_cbn; change (rank TYPE) with 24; change (rank LEN) with 18 in *; lia| exact ARR| change TYPE with 16191; inf_vis_close| inf_hid_close].
      + (* [comment removed for export] *)
        zrung [0x91950]. zs. zbr0 KINV.
        * (* [comment removed for export] *)
          zrung [0x8e260].
          pose proof (sinv_len_set _ _ lf cf LEN val SI1 MODE ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
          pose proof (sinv_bad_ofP _ _ lf cf SI2) as SIB.
          pose proof (meas_bad_ofP (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) (st_le (st_pull (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) cin (hold / 2 ^ hb) (bits - hb)) LEN val extra)) as MEB.
          st_norm SI1. st_norm ME1. st_norm SI2. unfold bad_ofP in SIB, MEB. st_norm SIB. st_norm MEB. subst mode. change (rank LEN) with 18 in *.
          eapply (KD (IST BAD last flags cin cout (hold / 2 ^ hb) (bits - hb) out ret val offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
            [exact SIB| clear - ME1 MEB HHB; unfold meas, Wm in *; icx_cbn; lia| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close].
        * (* [comment removed for export] *)
          destruct HTERM as [(OP0 & _)|[(OP1 & VAL1 & VAL2)|(O64 & _)]]; [exfalso; lia| | exfalso; lia].
          destruct (op_len_tests op OP1) as (_ & _ & L15).
          pose proof (pow2_le_15 (op - 16) ltac:(lia)) as PX.
          zrung [0x91970].
          rewrite L15 in *.
          zrung [0x9199c].
          destruct (sinv_to_lenext _ _ lf cf val (op - 16) SI1 MODE ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (SI2 & ME2).
          st_norm SI1. st_norm ME1. st_norm SI2. st_norm ME2.
          zs. zbr0 KX0.
          -- (* [comment removed for export] *)
             eapply (HLXZ (IST LENEXT last flags cin cout (hold / 2 ^ hb) (bits - hb) out ret val offset (op - 16) lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
               [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change LENEXT with 16201; inf_vis_close_bk ltac:(unfold back_ok; cbn [t_mode]; split; intros E; [eexists; split; [reflexivity| clear - HBK HB15 HHB; lia]| exfalso; lazy in E; discriminate E])| inf_hid_close| eapply KALL_mono; [| exact KA]; lia].
          -- (* [comment removed for export] *)
             zs.
             eapply (HLXB (IST LENEXT last flags cin cout (hold / 2 ^ hb) (bits - hb) out ret val offset (op - 16) lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
               [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change LENEXT with 16201; inf_vis_close_bk ltac:(unfold back_ok; cbn [t_mode]; split; intros E; [eexists; split; [reflexivity| clear - HBK HB15 HHB; lia]| exfalso; lazy in E; discriminate E])| inf_hid_close| eapply KALL_mono; [| exact KA]; lia| icx_cbn; lia].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder of KDISP / LXB_STMT / LXZ_STMT at 1.4 (InfBBase's inf_locals no longer holds it) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Time Qed.
End S.
End CANSEC1.
