(* reloc-zl14c 8c6420f86207abb2b2e19b6505549155 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* [comment removed for export] *)
  (* [U14] the 1.3.1 register homes of LXB_STMT, l_term moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  Definition LXB_STMT (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (xr x1 x6 x11 x12 x14 x15 x16 x17 x27 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_extra st <> 0 ->
    evtF asegs RNG POST
      (MS (mkR xr (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 8)) x6 x27 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 x12 (Z_to_bv 64 (t_extra st)) x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x1 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 7164)) (Z_to_bv 64 (c_n cx - t_cin st))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_p cx + 108)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 56)))
          FR (Z_to_bv 64 0x8e490) fc None m (seg_rom asegs)).
  Definition LXZ_STMT (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (xr x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 x27 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENEXT -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    x1 = Z_to_bv 64 (c_p cx + 8) ->
    evtF asegs RNG POST (GARMF_MS cx ly gp tp FR fc 0x911d8 st xr x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 x27 m).

  (* [comment removed for export] *)
  (* [U14] the 1.3.1 register homes of l_term moved to 1.4 by tools/regmap_text_gr.py (ra>t2 t2>t6 s4>s10 s5>s9 s6>ra s7>s11 s8>s4 s9>s7 s10>s5 s11>s8 t3>t4 t4>t5 t5>s6 t6>t3) *)
  (* [U14] the 1.3.1 register homes of l_term moved to 1.4 by tools/regmap_text_gr.py (s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>s6) *)
  (* [U14] s7 = S+116 (&state->extra) in l_term, from the g27 probe Pg27len2: 1.4 writes extra through s7 at 0x90dfc (sw a3,0(s7)) after its shadow check at 0x90de4 *)
  Lemma l_term : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x12 x16 x17 x19 x22 : word) (m : amem) (op val hb ci H B : Z),
    LXB_STMT cx ly -> LXZ_STMT cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= ci <= c_n cx -> 1 <= hb <= B -> B <= 40 -> 0 <= H < 2 ^ B -> B <= 8 * ci -> 8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
    0 <= op < 256 -> 0 <= val < 65536 ->
    ((op = 0 /\ val < 256) \/ (16 <= op <= 21 /\ 3 <= val /\ val + 2 ^ (op - 16) - 1 <= 258) \/ (Z.land op 64 <> 0 /\ Z.land op 16 = 0)) ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 val) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 op) x12 (Z_to_bv 64 hb) (Z_to_bv 64 (Z.shiftr (c_p cx + 7164) 3 + 2147450880)) (Z_to_bv 64 B) x16 x17
               (Z_to_bv 64 (l_Zs ly)) x19 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 7164)) (Z_to_bv 64 (c_n cx - ci)) (* [U14] an earlier development run 2026-11-11 23:4xZ: s6 is free at 0x90d90 (left via 0x90c24, the arm's word via 0x90d14) *)
               (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_p cx + 108)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 56)))
          FR (Z_to_bv 64 0x91148) fc None m (seg_rom asegs)).
  Proof.
    intros until B. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA HC HHB HB40 HH HBC HW HOP HVAL HTERM.
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    pose proof (drop_bound H B hb ltac:(lia) HH) as DB.
    destruct (sinv_pull _ _ lf cf ci (H / 2 ^ hb) (B - hb) SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & ME1).
    zrunb [0x91174].
    zs. rewrite (srl_div H hb) by lia.
    zrunb [0x91180].
    zs. zbr0 KLIT.
    - (* [comment removed for export] *)
      destruct HTERM as [(OP0 & VAL0)|[(OP1 & _)|(O64 & _)]]; [| exfalso; lia | exfalso; subst op; apply O64; reflexivity].
      zrunb [0x8e2ec].
      pose proof (sinv_len_set _ _ lf cf LIT val SI1 MODE ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
      st_norm SI1. st_norm ME1. st_norm SI2. subst mode.
      eapply (KD (IST LIT last flags ci cout (H / 2 ^ hb) (B - hb) out ret val offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI2| clear - ME1 HHB; unfold meas, Wm in *; icx_cbn; change (rank LIT) with 13; change (rank LEN) with 18 in *; lia| exact ARR| change LIT with 16205; inf_vis_close| inf_hid_close].
    - (* [comment removed for export] *)
      zs. zs. zs. zbr0 KEOB.
      + (* [comment removed for export] *)
        zrunb [0x8e2ec].
        pose proof (sinv_len_set _ _ lf cf TYPE val SI1 MODE ltac:(right; right; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
        st_norm SI1. st_norm ME1. st_norm SI2. subst mode.
        eapply (KD (IST TYPE last flags ci cout (H / 2 ^ hb) (B - hb) out ret val offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
          [exact SI2| clear - ME1 HHB HW; unfold meas, Wm in *; icx_cbn; change (rank TYPE) with 24; change (rank LEN) with 18 in *; lia| exact ARR| change TYPE with 16191; inf_vis_close| inf_hid_close].
      + (* [comment removed for export] *)
        zs. zs. zbr0 KINV.
        * (* [comment removed for export] *)
          zrunb [0x91934].
          pose proof (sinv_len_set _ _ lf cf LEN val SI1 MODE ltac:(left; reflexivity) ltac:(lia) ltac:(lia)) as SI2.
          pose proof (sinv_bad_ofP _ _ lf cf SI2) as SIB.
          pose proof (meas_bad_ofP (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (st_le (st_pull (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ci (H / 2 ^ hb) (B - hb)) LEN val extra)) as MEB.
          st_norm SI1. st_norm ME1. st_norm SI2. unfold bad_ofP in SIB, MEB. st_norm SIB. st_norm MEB. subst mode. change (rank LEN) with 18 in *.
          eapply (KB (IST LEN last flags ci cout (H / 2 ^ hb) (B - hb) out ret val offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
            [exact SIB| clear - ME1 MEB HHB; unfold bad_of, meas, Wm in *; icx_cbn; lia| exact ARR| change LEN with 16200; inf_vis_close| inf_hid_close].
        * (* [comment removed for export] *)
          destruct HTERM as [(OP0 & _)|[(OP1 & VAL1 & VAL2)|(O64 & _)]]; [exfalso; lia| | exfalso; lia].
          destruct (op_len_tests op OP1) as (_ & _ & L15).
          pose proof (pow2_le_15 (op - 16) ltac:(lia)) as PX.
          zrunb [0x911b0].
          rewrite ?L15 in *. (* [U14] an earlier development run 2026-11-11: 1.4 may take the mask after this stop *)
          zrunb [0x911d0]. rewrite ?L15 in *.
          destruct (sinv_to_lenext _ _ lf cf val (op - 16) SI1 MODE ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (SI2 & ME2).
          st_norm SI1. st_norm ME1. st_norm SI2. st_norm ME2.
          zs. zbr0 KX0.
          -- (* [comment removed for export] *)
             eapply (HLXZ (IST LENEXT last flags ci cout (H / 2 ^ hb) (B - hb) out ret val offset (op - 16) lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
               [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change LENEXT with 16201; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia| reflexivity].
          -- (* [comment removed for export] *)
             zs.
             eapply (HLXB (IST LENEXT last flags ci cout (H / 2 ^ hb) (B - hb) out ret val offset (op - 16) lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
               [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI2| exact ARR| change LENEXT with 16201; inf_vis_close| inf_hid_close| eapply KALL_mono; [| exact KA]; lia| icx_cbn; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
