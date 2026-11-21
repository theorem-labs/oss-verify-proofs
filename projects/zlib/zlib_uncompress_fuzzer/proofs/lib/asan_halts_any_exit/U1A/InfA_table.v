(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
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

  (* the 1.3.1 register homes of table_loop, table_tail moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  Lemma table_tail : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x5 x6 x11 x12 x13 x14 x15 x16 x17 x27 : word) (m : amem) (cin1 hold1 bits1 : Z),
    GARM cx ly 0x8e7ac LENLENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = TABLE -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 14 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 bits1) (Z_to_bv 64 hold1) (Z_to_bv 64 2147450880)
               x1 x27 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8e6e4) fc None m (seg_rom asegs)).
  Proof.
    intros until bits1. intros HLL CTX PAYR PLEN MODE SI ARR VIS HID (KD & KB & KL) HC HB HH HBC HW.
    inf_arm_open.
    pose proof (pow2_le_40 bits1 ltac:(lia)) as P40.
    assert (HU : 0 <= hold1 < 18446744073709551616) by lia.
    zrunb [0x8e700]. rewrite land31_mod by lia.
    pose proof (mod_range hold1 32 ltac:(lia)) as RNL. pose proof (mod_range (hold1 / 32) 32 ltac:(lia)) as RND. pose proof (mod_range (hold1 / 1024) 16 ltac:(lia)) as RNC.
    remember (hold1 mod 32) as nl eqn:ENL. remember ((hold1 / 32) mod 32) as nd eqn:END. remember ((hold1 / 1024) mod 16) as nc eqn:ENC.
    zs. zs.
    zrunb [0x8e728]. rewrite bits_54_59 by lia. rewrite <- END.
    zs. zs.
    zrunb [0x8e754]. rewrite bits_50_60 by lia. rewrite <- ENC.
    zs. zs.
    zs. zs.
    replace (bits1 + -14) with (bits1 - 14) by lia. rewrite (Z.shiftr_div_pow2 hold1 14) by lia.
    Local Ltac table_bad KB SI MODE HC HB HH HBC HW ARR nc nl nd :=
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        lazymatch type of HH with 0 <= ?h1 < 2 ^ ?b1 => lazymatch type of HC with _ <= ?c1 <= _ =>
          let SI' := fresh "SI'" in let ME' := fresh "ME'" in
          destruct (sinv_tb_bad cx0 st0 lf0 cf0 c1 h1 b1 (nc + 4) (nl + 257) (nd + 1) SI MODE ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HBC HW
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (SI' & ME');
          unfold st_tb, bad_ofP in SI', ME'; icx_cbn
        end end end.
    zs. zbr0 KNL.
    (* at 1.4 both range checks branch on the in-range side (probe PgCsTable: `bltu nd, 30`),
       so zbr0's first goals are the in-range paths *)
    2: { zrunb [0x915bc].
      table_bad KB SI MODE HC HB HH HBC HW ARR nc nl nd.
      eapply (KB (IST mode last flags cin1 cout (hold1 / 2 ^ 14) (bits1 - 14) out ret len offset extra lc dc lb db (nc + 4) (nl + 257) (nd + 1) shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| inf_vis_close| inf_hid_close]. }
    - zrunb [0x8e7ac; 0x915bc]. zbr0 KND.
      2: { zrunb [0x915bc].
        table_bad KB SI MODE HC HB HH HBC HW ARR nc nl nd.
        eapply (KB (IST mode last flags cin1 cout (hold1 / 2 ^ 14) (bits1 - 14) out ret len offset extra lc dc lb db (nc + 4) (nl + 257) (nd + 1) shave nx whave wnext) lf cf wf fo);
          [exact SI'| exact ME'| exact ARR| inf_vis_close| inf_hid_close]. }
      +
        zrunb [0x8e7ac].
        lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
          destruct (sinv_tb cx0 st0 lf0 cf0 cin1 hold1 bits1 (nc + 4) (nl + 257) (nd + 1) SI MODE ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HBC HW
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (SI' & ME') end.
        unfold st_tb in SI', ME'. icx_cbn.
        eapply (HLL (IST LENLENS last flags cin1 cout (hold1 / 2 ^ 14) (bits1 - 14) out ret len offset extra lc dc lb db (nc + 4) (nl + 257) (nd + 1) 0 nx whave wnext) lf cf wf fo);
          [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change LENLENS with 16197; inf_vis_close| inf_hid_close| eapply KALL_mono; [| split; [exact KD| split; [exact KB| exact KL]]]; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.


  Lemma table_loop : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x5 x6 x12 x15 x16 x17 x27 : word) (m : amem) (cin1 hold1 bits1 : Z),
    (Z.to_nat (14 - bits1) <= N)%nat ->
    GARM cx ly 0x8e7ac LENLENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = TABLE -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 0 <= bits1 < 14 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + cin1)) x12 (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 bits1) x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 bits1) (Z_to_bv 64 hold1) (Z_to_bv 64 2147450880)
               x1 x27 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8e078) fc None m (seg_rom asegs)).
  Proof.
    induction N as [|N IH]; intros until bits1; intros HN HLL CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW; [lia|].
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open.
    assert (P14 : 2 ^ bits1 <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
    zs. zbr0 KH0.
    2: {
      zrunb [0x9266c].
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        destruct (sinv_pull cx0 st0 lf0 cf0 cin1 hold1 bits1 SI ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HBC ltac:(icx_cbn; lia)) as (SI' & _) end.
      unfold st_pull in SI'. icx_cbn.
      eapply (KLV (IST mode last flags cin1 cout hold1 bits1 out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI'| exact ARR| inf_vis_close| inf_hid_close]. }
    destruct (unp_check_mu asegs _ _ _ _ _ (D + cin1) 1 UNP MU DJP ltac:(lia) ltac:(lia) ltac:(lia) (mod8_room1 _)) as (b & RDB & CK).
    zs. zs. zs. zs. rewrite sxb_sval.
    ck_branchJ 15 0x8e094 CK.
    pose proof (pay_read asegs _ D payload cin1 PAYB ltac:(lia)) as RDP. fold (bz payload cin1) in RDP.
    pose proof (bz_range payload cin1 PAYR) as BZR.
    zs. zs. cbv beta. rewrite (bz_val payload cin1 PAYR).
    zrunb [0x8e0bc].
    setreg 20 (Z_to_bv 64 (hold1 + bz payload cin1 * 2 ^ bits1)) ltac:(rewrite pull_hold by lia; reflexivity).
    replace (D + cin1 + 1) with (D + (cin1 + 1)) by lia. replace (n - cin1 + -1) with (n - (cin1 + 1)) by lia.
    pose proof (pullbyte_bound hold1 bits1 (bz payload cin1) ltac:(lia) ltac:(lia) BZR) as PB.
    zs. zbr0 KAG.
    -
      eapply (IH (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cin1 + 1) (hold1 + bz payload cin1 * 2 ^ bits1) (bits1 + 8));
        [lia| exact HLL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    - zs.
      eapply (table_tail (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cin1 + 1) (hold1 + bz payload cin1 * 2 ^ bits1) (bits1 + 8));
        [exact HLL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Theorem table_garm : forall cx ly, GARM cx ly 0x8e7ac LENLENS -> GARM cx ly 0x8e064 TABLE.
  Proof.
    intros cx ly HLL. unfold garm_stmtA, GARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    inf_arm_open.
    pose proof (pow2_le_40 bits ltac:(lia)) as P40.
    zs. zs. zbr0 KB14.
    - eapply (table_tail (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
        [exact HLL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    - zs. zs. zs.
      eapply (table_loop (Z.to_nat (14 - bits)) (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                 (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cin hold bits);
        [lia| exact HLL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| | | | | ]; icx_cbn; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

End S.
End CANSEC1.
