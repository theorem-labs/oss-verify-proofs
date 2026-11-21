(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfAGlue_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import InfA_w7six InfA_w7pull InfA_dist1 InfA_dist2 InfA_dist3 InfA_dist4.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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

  Notation DXS cx ly := (DX_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  (* [comment removed for export] *)
  Notation SIX val rb op H := (H mod 2 ^ (rb + op) / 2 ^ rb + val).

  (* [comment removed for export] *)
  (* [U14] the 1.3.1 register homes of D_L2 moved to 1.4 by tools/regmap_text_gr.py (t2>s6 s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  (* [U14] D_L2 restated from the 1.4 second-level pull loop (0x91008..0x9108c): t2 = t4 = B (bit counts), t3 = the second-level mask, s3 = bits, s6 = left (0x90ff8), s10 = next, s11 = have, t6 = S+108; t5 is a temporary *)
  Definition D_L2 (cx : ictx) (ly : ilay) (st : ist) (TA : Z) (rd : Z -> Z) (op val rb ci0 B0 ci H B : Z) (x30 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_n cx - ci0)) (Z_to_bv 64 val) (Z_to_bv 64 B) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (TA + 4 * SIX val rb op H)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (code_bits (rd (SIX val rb op H)))) (Z_to_bv 64 B0) (Z_to_bv 64 TA) (Z_to_bv 64 rb) (Z_to_bv 64 (c_q cx + ci0))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
            (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 7164)) (Z_to_bv 64 (c_n cx - ci))
            (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (2 ^ (rb + op) - 1)) (Z_to_bv 64 B) x30
            (Z_to_bv 64 (c_p cx + 56)))
       FR (Z_to_bv 64 0x91070) fc None m (seg_rom asegs).

  Lemma d_loop2 : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x30 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (op val rb ci0 B0 ci H B : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dtab m TA nd rd ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    1 <= rb <= 15 -> 1 <= op -> op <= 15 - rb -> 0 <= val -> val + 2 ^ op <= nd -> nd <= 65536 ->
    (forall j, 0 <= j < 2 ^ op -> code_bits (rd (j + val)) <= 15) ->
    (forall ci' H' B' x5 x6 x12 x14 x15 x17 x28 x29 x30', t_cin st <= ci' <= c_n cx -> B' = t_bits st + 8 * (ci' - t_cin st) -> 0 <= H' < 2 ^ B' ->
       rb + code_bits (rd (SIX val rb op H')) <= B' -> B' <= 40 ->
       evtF asegs RNG POST (D_E3 gp tp FR fc cx ly st TA (SIX val rb op H') (code_bits (rd (SIX val rb op H'))) rb ci' H' B' x5 x6 x12 x14 x15 x17 x28 x29 x30' m)) ->
    c_n cx - ci < Z.of_nat N ->
    t_cin st <= ci0 -> ci0 <= ci <= c_n cx -> B0 = t_bits st + 8 * (ci0 - t_cin st) -> B = B0 + 8 * (ci - ci0) -> 0 <= H < 2 ^ B -> B < rb + code_bits (rd (SIX val rb op H)) ->
    evtF asegs RNG POST (D_L2 cx ly st TA rd op val rb ci0 B0 ci H B x30 m).
  Proof.
    induction N as [|N IH]; intros until B; intros CTX PAYR PLEN MODE SI ARR VIS HID KA DT SBT XT8 XT0 XTL XTH RXT RTA TAP TAH RB15 OP1 OP15 V0 VND ND16 CB15 KE3 HN HC0 HC HB0 HBE HH HBX; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    unfold D_E3 in KE3. unfold D_L2.
    pose proof (proj1 (proj1 SI)) as CIN0.
    inf_arm_open.
    (* [comment removed for export] *)
    assert (CBE : code_bits (rd (SIX val rb op H)) <= 15) by (apply CB15; apply sidx_range; lia).
    set (hb0 := code_bits (rd (SIX val rb op H))) in *. set (ea0 := TA + 4 * SIX val rb op H) in *. clearbody hb0 ea0.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (pow2_le_15 (rb + op) ltac:(lia)) as P15. pose proof (pow2_le_15 rb ltac:(lia)) as PRB.
    zs. zbr0 KH.
    - (* [comment removed for export] *)
      assert (CIR : 0 <= ci < n) by (clear - CIN0 HC0 HC KH; lia).
      destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
      zs. zs. zs. rewrite sxb_sval.
      ck_branchJc 13 0x91088 CK.
      zs. cbv beta. rewrite (bz_val payload ci PAYR).
      zs. zs.
      rewrite (pull_hold H (bz payload ci) B) by lia.
      pose proof (pull_bound H B (bz payload ci) ltac:(lia) ltac:(lia) BZR) as PB.
      set (H1 := H + bz payload ci * 2 ^ B) in *.
      assert (PB64 : 0 <= H1 < 18446744073709551616) by (pose proof (pow2_le_40 (B + 8) ltac:(lia)); lia).
      eapply (six_b RNG POST) with (H := H1) (rb := rb) (op := op) (val := val) (TA := TA); [lia| lia| lia| lia| lia| lia|].
      assert (JND : 0 <= SIX val rb op H1 < nd) by (pose proof (sidx_range rb op H1 ltac:(lia) ltac:(lia)); lia).
      assert (CBE1 : code_bits (rd (SIX val rb op H1)) <= 15) by (apply CB15; apply sidx_range; lia).
      remember (SIX val rb op H1) as I1 eqn:EI1. apply w7hide_in in EI1.
      destruct (DT I1 JND) as (RDR & RD0 & RD1 & RD2).
      pose proof (tab_sh0 m XT NS (TA + 4 * I1 + 1) SBT XT8 ltac:(lia) ltac:(lia)) as RDS.
      pose proof (tab_sh_acc RNG XT NS (TA + 4 * I1 + 1) RXT XT8 ltac:(lia) ltac:(lia)) as ACS.
      zs. zs. zs. zs. zs. zs.
      cbv beta.
      rewrite u8_lit by (apply code_bits_range).
      pose proof (code_bits_range (rd I1)) as CBR1.
      set (hb1 := code_bits (rd I1)) in *.
      zrunb [0x910e0].
      replace (D + ci + 1) with (D + (ci + 1)) by lia. replace (n - ci + -1) with (n - (ci + 1)) by lia.
      zs. zbr0 KB2.
      + (* [comment removed for export] *)
        apply w7hide_out in EI1. subst hb1 I1.
        eapply (IH (ICX u S D n 6335616 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd op val rb ci0 B0 (ci + 1) H1 (B + 8));
          [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
          | exact RB15| exact OP1| exact OP15| exact V0| exact VND| exact ND16| exact CB15| exact KE3| | | | | | | ]; icx_cbn; lia.
      + (* [comment removed for export] *)
        zs.
        apply w7hide_out in EI1. subst hb1 I1.
        eapply (KE3 (ci + 1) H1 (B + 8)); icx_cbn; lia.
    - (* [comment removed for export] *)
      zrunb [0x92598].
      assert (ECI : ci = n) by lia. subst ci.
      replace (Z.shiftl (n - ci0) 3 + B0) with B by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (D + ci0 + (n - ci0) mod 4294967296) with (D + n) by (rewrite Z.mod_small by lia; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(icx_cbn; lia)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| exact HID].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] a worker: the v240 vestige binder *)
  Time Qed.
  (* [comment removed for export] *)
  Lemma d_sub : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x7 x13 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (op val rb ci H B : Z),
    DXS cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = DIST -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dtab m TA nd rd ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> rb <= B -> B <= 40 ->
    1 <= rb <= 15 -> 1 <= op -> op <= 15 - rb -> 0 <= val -> val + 2 ^ op <= nd -> nd <= 65536 ->
    (forall j, 0 <= j < 2 ^ op -> term_ok DISTS (15 - rb) (rd (val + j)) = true) ->
    evtF asegs RNG POST (D_E2 gp tp FR fc cx ly st TA op val rb ci H B x7 x13 m).
  Proof.
    intros until B. intros HDX CTX PAYR PLEN MODE SI ARR VIS HID KA DT SBT XT8 XT0 XTL XTH RXT RTA TAP TAH HC HBE HH HRB HB40 RB15 OP1 OP15 V0 VND ND16 SUB.
    assert (SUBJ : forall j, 0 <= j < 2 ^ op -> term_ok DISTS (15 - rb) (rd (j + val)) = true) by (intros j Hj; replace (j + val) with (val + j) by lia; apply SUB; exact Hj).
    assert (CB15 : forall j, 0 <= j < 2 ^ op -> code_bits (rd (j + val)) <= 15) by (intros j Hj; destruct (term_dists _ _ (SUBJ j Hj)) as (TB & _); lia).
    (* [comment removed for export] *)
    assert (KE3 : forall ci' H' B' x5 x6 x12 x14 x15 x17 x28 x29 x30', t_cin st <= ci' <= c_n cx -> B' = t_bits st + 8 * (ci' - t_cin st) -> 0 <= H' < 2 ^ B' ->
       rb + code_bits (rd (SIX val rb op H')) <= B' -> B' <= 40 ->
       evtF asegs RNG POST (D_E3 gp tp FR fc cx ly st TA (SIX val rb op H') (code_bits (rd (SIX val rb op H'))) rb ci' H' B' x5 x6 x12 x14 x15 x17 x28 x29 x30' m)).
    { intros ci' H' B' x5 x6 x12 x14 x15 x17 x28 x29 x30' HC' HBE' HH' HBB' HB40'.
      pose proof (sidx_range rb op H' ltac:(lia) ltac:(lia)) as JR'.
      destruct (term_dists _ _ (SUBJ _ JR')) as (_ & TCASE).
      pose proof (proj1 SI) as RN0. unfold IDefs.RNG in RN0. destruct RN0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BLE & _).
      eapply (d_fin2 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly st lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x5 x6 x12 x14 x15 x17 x28 x29 x30' m TA nd XT NS rd (SIX val rb op H') rb ci' H' B');
        [exact HDX| exact CTX| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VIS| exact HID| exact KA| exact DT| | exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
        | exact HC'| exact RB15| exact HBB'| exact HB40'| exact HH'| | | exact TCASE]; lia. }
    unfold D_E2.
    inf_arm_open.
    pose proof (pow2_le_40 B ltac:(lia)) as P40. pose proof (pow2_le_15 (rb + op) ltac:(lia)) as P15. pose proof (pow2_le_15 rb ltac:(lia)) as PRB.
    eapply (six_a RNG POST) with (H := H) (rb := rb) (op := op) (val := val) (TA := TA); [lia| lia| lia| lia| lia| lia|].
    assert (JND : 0 <= SIX val rb op H < nd) by (pose proof (sidx_range rb op H ltac:(lia) ltac:(lia)); lia).
    assert (CBE0 : code_bits (rd (SIX val rb op H)) <= 15) by (apply CB15; apply sidx_range; lia).
    remember (SIX val rb op H) as I0 eqn:EI0. apply w7hide_in in EI0.
    destruct (DT I0 JND) as (RDR & RD0 & RD1 & RD2).
    pose proof (tab_sh0 m XT NS (TA + 4 * I0 + 1) SBT XT8 ltac:(lia) ltac:(lia)) as RDS.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * I0 + 1) RXT XT8 ltac:(lia) ltac:(lia)) as ACS.
    zs. zs. zs. zs. zs. zs.
    cbv beta.
    rewrite u8_lit by (apply code_bits_range).
    pose proof (code_bits_range (rd I0)) as CBR0.
    set (hb0 := code_bits (rd I0)) in *.
    zs. zs. zbr0 KNP.
    - (* [comment removed for export] *)
      zrunb [0x9111c].
      apply w7hide_out in EI0. subst hb0 I0.
      eapply (KE3 ci H B); icx_cbn; lia.
    - (* [comment removed for export] *)
      zrunb [0x91070].
      apply w7hide_out in EI0. subst hb0 I0.
      eapply (d_loop2 (Datatypes.S (Z.to_nat (n - ci))) (ICX u S D n 6335616 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m TA nd XT NS rd op val rb ci B ci H B);
        [exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact DT| exact SBT| exact XT8| exact XT0| exact XTL| exact XTH| exact RXT| exact RTA| exact TAP| exact TAH
        | exact RB15| exact OP1| exact OP15| exact V0| exact VND| exact ND16| exact CB15| exact KE3| | | | | | | ]; icx_cbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] a worker: the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
