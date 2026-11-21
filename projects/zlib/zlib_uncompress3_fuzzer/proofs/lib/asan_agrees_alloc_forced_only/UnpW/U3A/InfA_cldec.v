(* reloc-zl14c de9886d3d77306979db03078737dbb26 *)
(* [U14] inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfPure_w7e InfAGlue_w7 InfAGlue_w7b InfPure_table InfPure_codelens.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull InfA_w6base InfA_w6kit InfA_cldone_base InfA_clbase InfA_clreg.
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
  Notation CLH cx ly N := (clhead_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLR cx ly N := (clres_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).

  (* [comment removed for export] *)
  (* [U14] the decode loop head at 1.4's 0x8f20c (bnez s11): t1 = t5 = B, t2 = the input left
     at entry, a1 = the next_in shadow cursor, t3 = next_in at entry, s3 = bits, s4 = hold, s11 = the input left; next_in
     itself lives in frame slot 496 (reloaded into s7 and stored back every byte, 0x8f5a4 / 0x8f5d8) *)
  Definition CLDEC_MS (cx : ictx) (ly : ilay) (st : ist) (ci H B : Z) (x13 x22 x23 x29 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 B) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (t_nlen st)) x13 (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880))
            (Z_to_bv 64 (t_nlen st + t_ndist st)) (Z_to_bv 64 (c_p cx + 1384)) (Z_to_bv 64 (t_shave st))
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
            x22 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 (Z_to_bv 64 (c_n cx - ci))
            (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + t_cin st)) x29 (Z_to_bv 64 B) x31)
       FR (Z_to_bv 64 0x8f554) fc None m (seg_rom asegs).

  Lemma cl_decode : forall (M N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x13 x22 x23 x29 x31 : word) (m : amem) (ci H B : Z),
    CLR cx ly N ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3))
        v240 (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (c_q cx + ci)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_n cx - ci < Z.of_nat M ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B < code_bits (rdc cf (CDyn 0) (H mod 2 ^ t_lb st)) ->
    evtF asegs RNG POST (CLDEC_MS cx ly st ci H B x13 x22 x23 x29 x31 m).
  Proof.
    induction M as [|M IH]; intros until B; intros HRES HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HM HC HBE HH HBX; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & LC0 & LB1 & LB15 & NX0 & NX1 & TOK & RLF & RCF).
    assert (CB15 : forall i, 0 <= i < 2 ^ t_lb st -> 1 <= code_bits (rdc cf (CDyn 0) i) <= 15 /\ 2 ^ t_lb st <= t_nx st).
    { intros i Hi. destruct (ctab_bits cf (t_lb st) (t_nx st) i TOK Hi) as (A & C). unfold rdc. rewrite Z.add_0_l. split; [lia| exact C]. }
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold CLDEC_MS.
    revert IH HRES. inf_arm_open. intros IH HRES.
    pose proof (pow2_le_15 lb ltac:(clear - LB1 LB15; lia)) as P15.
    assert (IDX0 : 0 <= H mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB1; lia).
    destruct (CB15 _ IDX0) as (CBE & NXR).
    set (hb0 := code_bits (rdc cf (CDyn 0) (H mod 2 ^ lb))) in *. clearbody hb0.
    pose proof (pow2_le_40 B ltac:(clear - HBX CBE HBE HC BITS0; lia)) as P40.
    zs. zbr0 KH.
    2: { (* [comment removed for export] *)
      zrunb [0x928f8].
      assert (ECI : ci = n) by (clear - KH HC; lia). subst ci.
      replace (Z.shiftl (n - cin) 3 + bits) with B by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear - HBE; lia).
      replace (D + cin + (n - cin) mod 4294967296) with (D + n) by (rewrite Z.mod_small by (clear - NR HC CIN0; lia); clear; lia).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; clear; lia).
      assert (SPF : cin <= n /\ n <= n /\ 0 <= B /\ B <= 40 /\ 0 <= H /\ H < 2 ^ B /\ B <= 8 * n /\ 8 * (n - n) + B <= 8 * (n - cin) + bits) by (clear - CIN0 CINN BITS0 BLE HC HBE HH HBX CBE; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(gcbn; tauto) ltac:(gcbn; tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(gcbn; tauto) ltac:(gcbn; tauto)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| exact HID]. }
    (* [comment removed for export] *)
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    assert (CIR : 0 <= ci < n) by (clear - CIN0 HC KH; lia).
    destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJc 29 0x8f56c CK. (* [U14] an earlier development run 2026-11-11: 1.4's partial check rejoins at 0x8f224 (ld s7,496(s1)) *)
    zs. zs. cbv beta. rewrite (bz_val payload ci PAYR).
    eapply (cl_pull_idx RNG POST) with (H := H) (B := B) (c := bz payload ci) (lb := lb) (TA := S + 1384);
      [exact BZR| clear - HBX CBE HBE HC BITS0; lia| exact HH| clear - LB1 LB15; lia| clear - S1 S2 ATB; lia|].
    pose proof (pull_bound H B (bz payload ci) ltac:(clear - HBE HC BITS0; lia) ltac:(clear - HH; lia) BZR) as PB.
    set (H1 := H + bz payload ci * 2 ^ B) in *.
    assert (IDX1 : 0 <= H1 mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB1; lia).
    destruct (CB15 _ IDX1) as (CBE1 & _).
    assert (IND1 : 0 <= H1 mod 2 ^ lb < nx) by (clear - IDX1 NXR; lia).
    remember (H1 mod 2 ^ lb) as i1 eqn:EI1. apply w7hide_in in EI1.
    pose proof (dtab_dyn m S cf 0 nx CODES RCF ltac:(clear; lia) NX0 ltac:(clear - NX1; lia)) as DT.
    replace (S + 1384 + 4 * 0) with (S + 1384) in DT by (clear; lia).
    destruct (DT i1 IND1) as (RDR & RD0 & RD1 & RD2).
    pose proof (tab_sh0 m S 897 (S + 1384 + 4 * i1 + 1) SHS S8 ltac:(clear - IND1 NX1; lia) ltac:(clear - S1; lia)) as RDS.
    pose proof (tab_sh_acc RNG S 897 (S + 1384 + 4 * i1 + 1) RSS S8 ltac:(clear - IND1 NX1; lia) ltac:(clear - S1; lia)) as ACS.
    zs. zs. zs. zs. zs. zs. (* [U14] an earlier development run 2026-11-11: 0x8f244 srl / add / lb / bnez on the old memory, then 1.4 bumps next_in and stores it to slot 496 (0x8f254 / 0x8f258) before the lbu *)
    pose proof (dtab_dyn _ S cf 0 nx CODES RCF ltac:(clear; lia) NX0 ltac:(clear - NX1; lia)) as DT1.
    replace (S + 1384 + 4 * 0) with (S + 1384) in DT1 by (clear; lia).
    destruct (DT1 i1 IND1) as (_ & _ & RD11 & _). (* the code_bits byte at +1, on the stored memory *)
    zs.
    cbv beta. rewrite u8_lit by (apply code_bits_range).
    pose proof (code_bits_range (rdc cf (CDyn 0) i1)) as CBR1.
    set (hb1 := code_bits (rdc cf (CDyn 0) i1)) in *.
    eapply (cl_dec_adv RNG POST) with (D := D) (n := n) (ci := ci) (B := B);
      [clear - HBX CBE HBE HC BITS0; lia| exact CIR| clear - NR; lia| clear - D1 DL2 ATB NR; lia|].
    replace (D + ci + 1) with (D + (ci + 1)) in * by (clear; lia). (* [U14] an earlier development run 2026-11-12: in * also reaches the slot-496 cell stored at 0x8f258 *)
    zs. zs. zbr0 KB2.
    - (* [comment removed for export] *)
      apply w7hide_out in EI1. subst hb1 i1.
      eapply (IH N (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ci + 1) H1 (B + 8));
        [exact HRES| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA
        | | | | | ]; clear - HM HC CIR HBE PB KB2 HBX CBE; gcbn; lia.
    - (* [comment removed for export] *)
      zrunb [0x8f5f0].
      apply w7hide_out in EI1. subst hb1 i1.
      eapply (HRES (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ci + 1) H1 (B + 8));
        [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA
        | | | | | ]; clear - HC CIR HBE PB KB2 HBX CBE; gcbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Qed.
  (* [comment removed for export] *)
  Lemma cl_head : forall (N : nat) (cx : ictx) (ly : ilay), CLR cx ly N -> CLH cx ly (S N).
  Proof.
    intros N cx ly HRES. unfold clhead_stmt, CLHEAD_MS. intros until m. intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA.
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & LC0 & LB1 & LB15 & NX0 & NX1 & TOK & RLF & RCF).
    assert (CB15 : forall i, 0 <= i < 2 ^ t_lb st -> 1 <= code_bits (rdc cf (CDyn 0) i) <= 15 /\ 2 ^ t_lb st <= t_nx st).
    { intros i Hi. destruct (ctab_bits cf (t_lb st) (t_nx st) i TOK Hi) as (A & C). unfold rdc. rewrite Z.add_0_l. split; [lia| exact C]. }
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    revert HRES. inf_arm_open. intros HRES.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    pose proof (pow2_le_15 lb ltac:(clear - LB1 LB15; lia)) as P15.
    pose proof (pow2_le_40 bits ltac:(clear - BITS0; lia)) as P40.
    eapply (cl_idx_a RNG POST) with (H := hold) (lb := lb) (TA := S + 1384);
      [clear - HOLD0 P40; lia| clear - LB1 LB15; lia| clear - S1 S2 ATB; lia|].
    assert (IDX0 : 0 <= hold mod 2 ^ lb < 2 ^ lb) by (apply mod_pow2_bound; clear - LB1; lia).
    destruct (CB15 _ IDX0) as (CBE & NXR).
    assert (IND0 : 0 <= hold mod 2 ^ lb < nx) by (clear - IDX0 NXR; lia).
    remember (hold mod 2 ^ lb) as i0 eqn:EI0. apply w7hide_in in EI0.
    pose proof (dtab_dyn m S cf 0 nx CODES RCF ltac:(clear; lia) NX0 ltac:(clear - NX1; lia)) as DT.
    replace (S + 1384 + 4 * 0) with (S + 1384) in DT by (clear; lia).
    destruct (DT i0 IND0) as (RDR & RD0 & RD1 & RD2).
    pose proof (tab_sh0 m S 897 (S + 1384 + 4 * i0 + 1) SHS S8 ltac:(clear - IND0 NX1; lia) ltac:(clear - S1; lia)) as RDS.
    pose proof (tab_sh_acc RNG S 897 (S + 1384 + 4 * i0 + 1) RSS S8 ltac:(clear - IND0 NX1; lia) ltac:(clear - S1; lia)) as ACS.
    zs. zs. zs. zs. zs.
    cbv beta. rewrite u8_lit by (apply code_bits_range).
    pose proof (code_bits_range (rdc cf (CDyn 0) i0)) as CBR0.
    set (hb0 := code_bits (rdc cf (CDyn 0) i0)) in *.
    zs. zbr0 KB0.
    - (* [comment removed for export] *)
      zrunb [0x8f5f0].
      apply w7hide_out in EI0. subst hb0 i0.
      eapply (HRES (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits); (* [U14] an earlier development run 2026-11-11: 1.4 stores next_in to slot 496 on both exits (0x8f294 / 0x8f208) *)
        [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA
        | | | | | ]; clear - CIN0 CINN HOLD0 BITS0 KB0; gcbn; lia.
    - (* [comment removed for export] *)
      zrunb [0x8f554].
      apply w7hide_out in EI0. subst hb0 i0.
      eapply (cl_decode (Datatypes.S (Z.to_nat (n - cin))) N (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
        [exact HRES| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA
        | | | | | ]; clear - CIN0 CINN HOLD0 KB0; gcbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
