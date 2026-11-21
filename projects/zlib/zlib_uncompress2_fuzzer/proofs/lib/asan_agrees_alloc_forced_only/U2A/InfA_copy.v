(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit I_asan_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AObj U2AClient U2AStore U2AIface InfABase InfAKit InfAGlue InfPure InfPure_type InfPure_stored InfAGlue_p04 U2ABlob U2ACall U2AGlue UwAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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

  (* the 1.3.1 register homes of copy_body, copy_tail moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  (* the 1.3.1 register homes of copy_tail moved to 1.4 by tools/regmap_text_gr.py (ra>t2 t2>t6 s4>s10 s5>s9 s6>ra s7>s11 s8>s4 s9>s7 s10>s5 s11>s8 t3>t4 t4>t5 t5>s6 t6>t3) *)
  (* the 1.3.1 register homes of copy_tail moved to 1.4 by tools/regmap_text_gr.py (ra>t5 t2>ra s4>s8 s5>s6 s6>s10 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  (* copy_tail restated from copy_body's state at 0x8efa0 (g27 goal probe PgGoalsCopy1): s7 = -3 (ARM; 1.4 reloads s7 from slot 424 before the call), s10 = next (the memcpy source, mv a1,s10), t5 = (S+8)sh; slot 504 holds (S+108)sh, stored at 0x8ef80 / 0x8ef94 and read back after the call *)
  (* slot 496 (next) is free at 0x8efa0: copy_body does not store it on the copy path, and copy_tail stores it after the call (0x8efd8) *)
  Lemma copy_tail : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x11 x12 x13 x14 x15 x16 x17 : word) (m : amem) (copy : Z),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = COPY -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3 + 2147450880)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    1 <= copy <= t_length st -> copy <= c_n cx - t_cin st -> copy <= c_osz cx - t_cout st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               (Z_to_bv 64 copy) (Z_to_bv 64 (-3)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8efd0) fc None m (seg_rom asegs)).
  Proof.
    intros until copy. intros CTX PAYR PLEN MODE SI ARR VIS HID KA HC1 HC2 HC3.
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    pose proof (copy_len_bound _ _ _ _ SI (or_intror MODE)) as HL16.
    inf_arm_open. subst mode.
    destruct (pay_out_sep _ _ _ _ _ CTX0) as (cOD & COD0 & COD1 & COD2). cbn [c_q c_n] in COD1, COD2.
    clear R13.
    pose proof CTX0 as (_ & _ & (psx & _ & PDX) & _). cbn [c_p c_q c_n] in PDX.
    destruct PDX as [(pd & PDI & _ & _)|(N0 & _)]; [| exfalso; lia].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH PDI) as (_ & (PBK & _) & RDB & _ & _ & _ & _ & (RLO & RHI & RL1 & RL2 & RL3 & RL4 & RL5 & RL6)).
    pose proof (ablk_lin _ _ PBK) as (PK1 & PK2 & PK3 & PK4). unfold AIMG_HI in PK1.
    destruct (blk_hull m RNG D n RLO RHI PBK ltac:(lia) RL1 RL2 RL3 RL4 RL5 RL6) as (PHULL & RPH & WPH).
    set (PLO := D / 64 * 64) in *. set (PHI := (D + n + 63) / 64 * 64) in *. clearbody PLO PHI. clear RL1 RL2 RL3 RL4 RL5 RL6.
    pose proof (wr_at_of_shadow_bytes asegs _ _ _ _ SHO) as WRO.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as ART. unfold artcells in ART. destruct ART as (_ & GOT & RIC & REAL & SHB & _ & INI & LAY & _).
    zrunb [0x8efec].
    rewrite (Z.mod_small copy 4294967296) by lia.
    destruct (bytes_at_mid asegs _ D _ (Z.to_nat cin) (Z.to_nat copy) PAYB ltac:(rewrite length_map; lia)) as (SRC & SRCL).
    rewrite Z2Nat.id in SRC by lia.
    destruct (out_open asegs _ _ _ _ cout copy OUT ltac:(lia) ltac:(lia) ltac:(lia)) as (b1 & b2 & b3 & B1 & B2 & B3). clear OUT.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (UNPc : unpoisoned mc (D + cin) (D + cin + copy))
        by (eapply unpoisoned_sub; [eapply unpoisoned_munch; [exact UNP| exact MU| exact DJP]| lia| lia]);
      assert (SHOc : shadow_bytes mc (Z.shiftr 6336320 3 + 2147450880) (Z.shiftr 6336320 3 + 2147450880 + 32768) (fun _ => 0))
        by exact (sh0_mu _ _ _ _ _ SHO MU DJO) end.
    zs.
    callq (asan_memcpy_callz PLO PHI 6336320 (6336320 + 262144) RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- bytes_at _ _ _ _ => exact SRC
         | |- length _ = _ => exact SRCL
         | |- rw_cells _ _ _ [CB _ _] => exact B2
         | |- stk _ _ _ _ => exact STK
         | |- mem_inv _ _ => exact MI
         | |- rt_got _ => exact GOT | |- rt_got_ric _ => exact RIC | |- rt_shbase _ => exact SHB
         | |- rt_inited _ => exact INI | |- rt_layout _ => exact LAY | |- rt_real_mem _ => exact REAL
         | |- app_blk _ _ => first [ eapply ablk_app_blk; [eapply ablk_sub; [exact PBK| lia| lia]| lia] | unfold app_blk, KLOW, KHIGH, KEND; lia ]
         | |- unpoisoned _ _ _ => first [ exact UNPc | eapply (unp_of_sh0 _ 6336320 32768); [exact SHOc| reflexivity| lia| lia| lia| lia| lia] ]
         | |- wr_at _ _ (shad _) _ =>
             first [ exact WPH | eapply wr_at_transport; [exact WPH| exact WM]
                   | rewrite !shadE;
                     replace (Z.shiftr (6336320 + 262144) 3 + 2147450880 - (Z.shiftr 6336320 3 + 2147450880)) with 32768 by (vm_compute; reflexivity);
                     replace (Z.shiftr 6336320 3 + 2147450880 + 32768 - (Z.shiftr 6336320 3 + 2147450880)) with 32768 in WRO by (vm_compute; reflexivity);
                     exact WRO ]
         | |- rng _ (shad _) _ =>
             first [ exact RPH
                   | rewrite !shadE;
                     replace (Z.shiftr (6336320 + 262144) 3 + 2147450880 - (Z.shiftr 6336320 3 + 2147450880)) with 32768 by (vm_compute; reflexivity);
                     replace (Z.shiftr 6336320 3 + 2147450880) with 2148242920 by (vm_compute; reflexivity);
                     eapply rng_sub'; [exact RISH| lia] ]
         | |- rng _ 65536 _ => exact RI
         | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia] | eapply rng_sub'; [exact RDB| lia] | eapply rng_sub'; [exact ROB| lia] ]
         | |- _ /\ _ => first [ repeat split; first [reflexivity| lia] | destruct PHULL as (H1 & H2 & H3 & H4 & H5 & H6); repeat split; first [lia| exact H3| exact H4] ]
         | |- _ \/ _ => lia
         | |- _ <= _ => first [ lia | unfold KHIGH, KEND in *; lia ]
         | |- _ < _ => lia
         end.
    destruct (out_close asegs _ 6336320 osz cout copy _ _ _ ltac:(lia) ltac:(lia) ltac:(lia) B1 PC0 B3) as (fo' & OUT' & FOR').
    clear B1 B3 PC0 SRC SRCL.
    zrunb [0x8e210].
    rewrite (Z.mod_small copy 4294967296) in * by lia.
    replace (6336320 + cout + copy) with (6336320 + (cout + copy)) in * by lia.
    replace (D + cin + copy) with (D + (cin + copy)) in * by lia.
    replace (n - cin - copy) with (n - (cin + copy)) by lia. replace (osz - cout - copy) with (osz - (cout + copy)) by lia.
    assert (SI' : sinv (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc)
                       (set_st (IST COPY last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY (cin + copy) (cout + copy) hold bits (len - copy)) lf cf).
    { apply sinv_set; [exact SI| exact HFL| reflexivity| right; right; right; left; reflexivity| intros _; icx_cbn; lia
                       | icx_cbn; lia| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| unfold Wm; icx_cbn; lia]. }
    assert (ME' : meas (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc)
                       (set_st (IST COPY last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY (cin + copy) (cout + copy) hold bits (len - copy))
                  < meas (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (IST COPY last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
    { apply meas_set. left. unfold Wm; icx_cbn. lia. }
    eapply (KD (set_st (IST COPY last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY (cin + copy) (cout + copy) hold bits (len - copy)) lf cf wf fo');
      [exact SI'| exact ME'| destruct ARR as [AW _]; split; [exact AW| intros i _; apply FOR']| unfold set_st; inf_vis_close| inf_hid_close].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Lemma copy_body : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = COPY -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m ->
    KALLB cx ly (meas cx st) ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 (Z_to_bv 64 (c_p cx + 56)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
               (Z_to_bv 64 (l_F0 ly)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               (* s6 is free at 1.4 (InfABase's ARM_MS); the head shadow lives in frame slot 504 *)
               x22 (Z_to_bv 64 (-3)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880))
               (Z_to_bv 64 (c_p cx + 108)))
          FR (Z_to_bv 64 0x8ef88) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof KA as (KD & KB & KL & KLV).
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    pose proof (copy_len_bound _ _ _ _ SI (or_intror MODE)) as HL16.
    inf_arm_open. subst mode.
    clear R13.
    zrunb [0x8efa0].
    zs. zbr0 KLEN0.
    {
      zrunb [0x8e210].
      assert (SI' : sinv (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc)
                         (set_st (IST COPY last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE cin cout hold bits len) lf cf).
      { apply sinv_set; [exact SI| exact HFL| reflexivity| left; reflexivity| intros [X|X]; cbv in X; discriminate X
                         | icx_cbn; lia| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| unfold Wm; icx_cbn; lia]. }
      assert (ME' : meas (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc)
                         (set_st (IST COPY last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE cin cout hold bits len)
                    < meas (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (IST COPY last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
      { apply meas_set. right. split; [unfold Wm; icx_cbn; lia| vm_compute; reflexivity]. }
      eapply (KD (set_st (IST COPY last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) TYPE cin cout hold bits len) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change TYPE with 16191; unfold set_st; inf_vis_close| inf_hid_close]. }
    Local Ltac to_tailE KA CTX0 PAYR PLEN SI ARR cpy lyv :=
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        lazymatch type of ARR with inf_arr_ok _ ?wf0 ?fo0 =>
          let CT := fresh "CT" in
          pose proof (copy_tail cx0 lyv st0 lf0 cf0 wf0 fo0) as CT;
          cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_cin t_cout t_hold t_bits t_length] in CT;
          eapply CT with (copy := cpy);
            [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA
            | icx_cbn; lia| icx_cbn; lia| icx_cbn; lia] end end.
    Local Ltac to_leaveE KLV SI ARR :=
      zrunb [0x92900];
      lazymatch type of SI with sinv ?cx0 ?st0 ?lf0 ?cf0 =>
        lazymatch type of ARR with inf_arr_ok _ ?wf0 ?fo0 =>
          eapply (KLV st0 (t_ret st0) lf0 cf0 wf0 fo0); [exact SI| exact ARR| inf_vis_close| inf_hid_close] end end.
    zs. zbr0 K1.
    -
      zs. zbr0 K2.
      +
        zrunb [0x8efd0]. to_tailE KA CTX0 PAYR PLEN SI ARR len (ILAY SP SPA Zs F0 lo).
      +
        zrunb [0x8efc8]. zs. zbr0 K3.
        * to_tailE KA CTX0 PAYR PLEN SI ARR (osz - cout) (ILAY SP SPA Zs F0 lo).
        * to_leaveE KLV SI ARR.
    -
      zrunb [0x8efac]. zs. zbr0 K2.
      +
        zrunb [0x8efc8]. zs. zbr0 K3.
        * to_tailE KA CTX0 PAYR PLEN SI ARR (osz - cout) (ILAY SP SPA Zs F0 lo).
        * to_leaveE KLV SI ARR.
      + zs. zs. zbr0 K3. (* 1.4 stores slot 504 at 0x8ef80 before the bnez s6 at 0x8ef84 (probe Pg29copyK3) *)
        * to_tailE KA CTX0 PAYR PLEN SI ARR (n - cin) (ILAY SP SPA Zs F0 lo).
        * to_leaveE KLV SI ARR.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Theorem copy_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8ef88 COPY.
  Proof.
    intros cx ly. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    eapply copy_body; eassumption.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  Theorem copy__arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8ef70 COPY_.
  Proof.
    intros cx ly. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite MODE; cbv; discriminate) ltac:(rewrite MODE; cbv; discriminate)) as HFL.
    pose proof (copy_len_bound _ _ _ _ SI (or_introl MODE)) as HL16.
    inf_arm_open. subst mode.
    clear R13.
    zrunb [0x8ef88].
    assert (SI' : sinv (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc)
                       (set_st (IST COPY_ last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin cout hold bits len) lf cf).
    { apply sinv_set; [exact SI| exact HFL| reflexivity| right; right; right; left; reflexivity| intros _; icx_cbn; lia
                       | icx_cbn; lia| icx_cbn; lia| lia| lia| lia| icx_cbn; lia| unfold Wm; icx_cbn; lia]. }
    assert (ME' : meas (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc)
                       (set_st (IST COPY_ last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin cout hold bits len)
                  < meas (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (IST COPY_ last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)).
    { apply meas_set. right. split; [unfold Wm; icx_cbn; lia| vm_compute; reflexivity]. }
    pose proof (copy_body (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                  (set_st (IST COPY_ last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) COPY cin cout hold bits len) lf cf wf fo) as CB.
    unfold set_st in CB. cbn [c_u c_p c_q c_n c_ob c_osz c_w l_SP l_SPA l_Zs l_F0 l_lo t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                               t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in CB.
    eapply CB; [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change COPY with 16195; inf_vis_close| inf_hid_close|].
    eapply KALL_mono; [| exact KA].
    unfold set_st in ME'. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
                               t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in ME'.
    apply Z.lt_le_incl. exact ME'.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
