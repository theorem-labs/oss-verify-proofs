(* reloc-zl14c faefe45076aa68270fa9fb5970ac660c *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfPure_w7e InfAGlue_w7 InfAGlue_w7b InfPure_table InfPure_lenlens InfPure_codelens InfPure_codelens2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull InfA_w6base InfA_w6kit InfA_cldone_base InfA_clbase InfA_clbase2 InfA_clreg.
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
  Notation CLK cx ly N := (clchk_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLP cx ly pc N := (clrep_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh pc N).

  (* [comment removed for export] *)
  (* [U14] the repeat-16 tail at 1.4's 0x8f488 (sd t6,496(s1)): t6 = next_in, which the pull loop keeps in t4 / t6 and stores only here, so the VIS next cell is free on entry *)
  Definition CLX16_MS (cx : ictx) (ly : ilay) (st : ist) (ci H B hb : Z) (x7 x11 x19 x22 x23 x28 x29 : word) (m : amem) : machine_state :=
    (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 B) x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
             (Z_to_bv 64 (l_F0 ly)) x11 (Z_to_bv 64 (t_nlen st)) (Z_to_bv 64 hb) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_nlen st + t_ndist st)) (Z_to_bv 64 (c_p cx + 1384))
             (Z_to_bv 64 (t_shave st))
             (Z_to_bv 64 (l_Zs ly)) x19 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
             x22 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 (Z_to_bv 64 (c_n cx - ci))
             (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) x28 x29 (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) (Z_to_bv 64 (c_q cx + ci)))
        FR (Z_to_bv 64 0x8f7d0) fc None m (seg_rom asegs)).

  Lemma cl_x16_chk : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x7 x11 x19 x22 x23 x28 x29 : word) (m : amem) (ci H B hb : Z),
    CLK cx ly N ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3))
        v240 (Z_to_bv 64 (c_osz cx - t_cout st)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> B <= 40 -> 1 <= hb <= 15 -> hb + 2 <= B ->
    evtF asegs RNG POST (CLX16_MS cx ly st ci H B hb x7 x11 x19 x22 x23 x28 x29 m).
  Proof.
    intros until hb. intros HCHK HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HC HBE HH HB40 HHB HNB.
    pose proof KA as (KD & KB & KL & KLV).
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & _ & _ & _ & _ & _ & _ & RLF & _).
    pose proof (buf_ok_pulled _ _ _ _ ci H B SI HC HBE HH HB40) as BUF.
    pose proof (buf_ok_drop _ _ ci H B hb BUF ltac:(clear - HHB HNB; lia)) as BUF1.
    pose proof (buf_ok_drop _ _ ci (H / 2 ^ hb) (B - hb) 2 BUF1 ltac:(clear - HHB HNB; lia)) as BUF2.
    change (2 ^ 2) with 4 in BUF2.
    pose proof (Z.mod_pos_bound (H / 2 ^ hb) 4 ltac:(clear; lia)) as CPR.
    destruct (sinv_cl_bad _ _ _ _ ci (H / 2 ^ hb) (B - hb) SI MODE BUF1) as (SIB & MEB).
    pose proof BUF1 as (_ & _ & _ & B1H & H1L & H1H & _).
    unfold CLX16_MS.
    revert HCHK. inf_arm_open. intros HCHK.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    zs. (* [U14] an earlier development run 2026-11-11: sd t6,496(s1) *)
    eapply (cl_x16a RNG POST) with (H := H) (B := B) (hb := hb); [exact HH| clear - HHB HNB; lia| exact HB40|].
    zs. zbr0 KZ.
    2: { (* [comment removed for export] *)
      zrunb [0x8e2ec].
      unfold bad_ofP, st_cl in SIB, MEB.
      cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SIB, MEB.
      eapply (KD (IST BAD last flags ci cout (H / 2 ^ hb) (B - hb) out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SIB| exact MEB| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close]. }
    eapply (cl_x16b RNG POST) with (j := shave); [clear - KZ SH0 SH1 NL2 ND2; lia|].
    zs. zs.
    lazymatch type of MU with munch _ _ ?mc =>   (* [U14] an earlier development run 2026-11-11: the memory after 0x8f488's sd t6,496(s1) *)
      pose proof (shadow_bytes_munch _ _ mc _ _ _ SHS MU DJS) as SHS1;
      pose proof (tab_sh0 mc S 897 (S + 168 + 2 * (shave - 1)) SHS1 S8 ltac:(clear - KZ SH0 SH1 NL2 ND2; lia) ltac:(clear - S1; lia)) as RDS
    end.
    pose proof (tab_sh_acc RNG S 897 (S + 168 + 2 * (shave - 1)) RSS S8 ltac:(clear - KZ SH0 SH1 NL2 ND2; lia) ltac:(clear - S1; lia)) as ACS.
    pose proof (f16arr_read asegs _ (S + 168) 320 lf (shave - 1) _ LENS ltac:(clear - KZ SH0 SH1 NL2 ND2; lia) eq_refl) as RDL.
    pose proof (RLF (shave - 1) ltac:(clear - KZ SH0 SH1 NL2 ND2; lia)) as RL1.
    pose proof (L15 (shave - 1) ltac:(clear - KZ SH0; gcbn; lia)) as RL2.
    zs. zs. zs. zs. zs.
    zs. rewrite (zx16_small (lf (shave - 1))) by (exact RL1).
    eapply (cl_x16c RNG POST) with (H := H / 2 ^ hb) (B := B - hb); [clear - H1L H1H; lia| clear - HNB B1H; lia|].
    eapply (HCHK (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ci (H / 2 ^ hb / 4) (B - hb - 2) (H / 2 ^ hb mod 4 + 3) (lf (shave - 1)));
      [exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| exact BUF2
      | clear - CPR; lia| clear - RL1 RL2; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Qed.

  (* [comment removed for export] *)
  (* [U14] the repeat-16 pull loop head at 1.4's 0x8f3a4 (bnez s11): t4 = next_in (kept in a register, slot 496 is stale), a1 = its shadow cursor, t1 = t3 = B, t2 = hb + 2 *)
  Definition CLPULL16_MS (cx : ictx) (ly : ilay) (st : ist) (ci H B hb : Z) (x19 x22 x23 x31 : word) (m : amem) : machine_state :=
    (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 B) (Z_to_bv 64 (hb + 2)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
             (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (t_nlen st)) (Z_to_bv 64 hb) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (t_nlen st + t_ndist st)) (Z_to_bv 64 (c_p cx + 1384))
             (Z_to_bv 64 (t_shave st))
             (Z_to_bv 64 (l_Zs ly)) x19 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
             x22 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 (Z_to_bv 64 (c_n cx - ci))
             (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 B) (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) x31)
        FR (Z_to_bv 64 0x8f6ec) fc None m (seg_rom asegs)).

  Lemma cl_pull16 : forall (M N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x19 x22 x23 x31 : word) (m : amem) (ci H B hb : Z),
    CLK cx ly N ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat -> t_shave st < t_nlen st + t_ndist st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3))
        v240 (Z_to_bv 64 (c_osz cx - t_cout st)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    c_n cx - ci < Z.of_nat M ->
    t_cin st <= ci <= c_n cx -> B = t_bits st + 8 * (ci - t_cin st) -> 0 <= H < 2 ^ B -> 1 <= hb <= 15 -> B < hb + 2 ->
    evtF asegs RNG POST (CLPULL16_MS cx ly st ci H B hb x19 x22 x23 x31 m).
  Proof.
    induction M as [|M IH]; intros until hb; intros HCHK HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HM HC HBE HH HHB HBX; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    unfold CLPULL16_MS.
    revert IH HCHK. inf_arm_open. intros IH HCHK.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    pose proof (pow2_le_40 B ltac:(clear - HBX HHB HBE HC BITS0; lia)) as P40.
    zs. zbr0 KH.
    2: { (* [comment removed for export] *)
      zrunb [0x928f8].
      assert (ECI : ci = n) by (clear - KH HC; lia). subst ci.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (n - n)) by (f_equal; clear; lia).
      assert (SPF : cin <= n /\ n <= n /\ 0 <= B /\ B <= 40 /\ 0 <= H /\ H < 2 ^ B /\ B <= 8 * n /\ 8 * (n - n) + B <= 8 * (n - cin) + bits) by (clear - CIN0 CINN BITS0 BLE HC HBE HH HBX HHB; lia).
      destruct (sinv_pull _ _ lf cf n H B SI ltac:(gcbn; tauto) ltac:(gcbn; tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(tauto) ltac:(gcbn; tauto) ltac:(gcbn; tauto)) as (SI1 & _).
      st_norm SI1.
      eapply (KLV (IST mode last flags n cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI1| exact ARR| inf_vis_close| exact HID]. }
    assert (CIR : 0 <= ci < n) by (clear - CIN0 HC KH; lia).
    destruct (pull_facts RNG _ m m D n payload ci UNP MU DJP RD RSD PAYB PAYR PLEN D16 D1 CIR) as (b & RDB & CK & ACP & RDP & ACB & BZR).
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJc 31 0x8f704 CK. (* [U14] an earlier development run 2026-11-11: 1.4's shadow check 0x8f3ac srl / add / lb, bnez; the partial check rejoins at 0x8f3bc *)
    zs. cbv beta. rewrite (bz_val payload ci PAYR).
    eapply (cl_padv16 RNG POST) with (D := D) (n := n) (ci := ci) (H := H) (B := B) (c := bz payload ci);
      [exact BZR| clear - HBX HHB HBE HC BITS0; lia| exact HH| exact CIR| clear - NR; lia| clear - D1 DL2 ATB NR; lia|].
    pose proof (pull_bound H B (bz payload ci) ltac:(clear - HBE HC BITS0; lia) ltac:(clear - HH; lia) BZR) as PB.
    set (H1 := H + bz payload ci * 2 ^ B) in *.
    zs. zs. zbr0 KB2. (* [U14] an earlier development run 2026-11-11: ld t5,448(s1) at 0x8f3e0, then bltu t3,t2 *)
    - (* [comment removed for export] *)
      eapply (IH N (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (ci + 1) H1 (B + 8) hb);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | | | | | exact HHB| ]; clear - HM HC CIR HBE PB KB2 HBX HHB; gcbn; lia.
    - zs.
      eapply (cl_x16_chk N (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m (ci + 1) H1 (B + 8) hb);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | | | | | exact HHB| ]; clear - HC CIR HBE PB KB2 HBX HHB; gcbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Qed.

  (* [comment removed for export] *)
  Lemma cl_rep16 : forall (N : nat) (cx : ictx) (ly : ilay), CLK cx ly N -> CLP cx ly 0x8f6d8 N.
  Proof.
    intros N cx ly HCHK. unfold clrep_stmt, CLREP_MS. intros until hb. intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA HC HBE HH HB40 HHB HBX.
    pose proof (sinv_bits_facts _ _ _ _ SI) as (CIN0 & CINN & BITS0 & BLE & HOLD0).
    revert HCHK. inf_arm_open. intros HCHK.
    zs. zs. zbr0 KNB.
    - (* [comment removed for export] *)
      zs. (* [U14] an earlier development run 2026-11-11: ld t6,496(s1) at 0x8f484 *)
      eapply (cl_x16_chk N (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B hb);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | exact HC| exact HBE| exact HH| exact HB40| exact HHB| clear - KNB; lia].
    - zs. zs. zs.
      eapply (cl_pull16 (Datatypes.S (Z.to_nat (n - ci))) N (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m ci H B hb);
        [exact HCHK| exact HN| exact HJN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA
        | clear - HC; gcbn; lia| exact HC| exact HBE| exact HH| exact HHB| clear - KNB; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
