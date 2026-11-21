(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_lenlens ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base InfA_w6base InfA_w6kit U2AIface_fit2_draft InfA_itcall InfA_llcall InfA_llfill.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Lemma drop3_bound : forall H B, 0 <= H < 2 ^ B -> 3 <= B -> 0 <= H / 8 < 2 ^ (B - 3).
  Proof.
    intros H B HH HB. assert (E : 2 ^ B = 8 * 2 ^ (B - 3)) by (change 8 with (2 ^ 3); rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2 ^ (B - 3)) by (apply Z.pow_pos_nonneg; lia).
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.

  (* the 1.4 read-loop head 0x8eb38 (li a2,2).  ra = &mode (S+8), t1 = &have, t2 =
     lens (S+168, slot 400 at 0x8eb08), a0 = F0, a1 = a4 = &order[have] (141376 = 0x22840), a3 = ncode, a5 = ncode -
     have, a6 = have + 1, s7 = (S+156)sh (0x8eaf8); s3 = bits, s4 = hold, s10 = next_in, s11 = the input left; t3 =
     S+28, t4 = left, t5 = (S+8)sh as GARM leaves them (the LEAVE exit at 0x8eb44 needs ra a0 t3 t4 t5).  Slot 496 is
     stale (1.4 pulls in s10; 1.3.1 kept next_in in slot 496), so vnext is free. *)
  Definition LLHEAD (N : nat) (cx : ictx) (ly : ilay) : Prop :=
    forall (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 vnext v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x12 x17 x22 x31 : word) (m : amem),
    (Z.to_nat (t_ncode st - t_shave st) <= N)%nat -> t_shave st < t_ncode st ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 (Z_to_bv 64 (c_p cx + 156)) (Z_to_bv 64 (c_p cx + 168)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (141376 + 2 * t_shave st)) x12 (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (141376 + 2 * t_shave st)) (Z_to_bv 64 (t_ncode st - t_shave st))
               (Z_to_bv 64 (t_shave st + 1)) x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) x31)
          FR (Z_to_bv 64 0x8eb68) fc None m (seg_rom asegs)).

  (* the 1.4 body 0x8eb70, after the pull (or with bits >= 3 already): s3 = bits1, s4 =
     hold1, s10 = next_in + cin1, s11 = the input left. *)
  Lemma ll_body : forall (N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x12 x17 x22 x31 : word) (m : amem) (cin1 hold1 bits1 : Z),
    LLHEAD N cx ly -> (Z.to_nat (t_ncode st - t_shave st) <= S N)%nat -> t_shave st < t_ncode st ->
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f4cc CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    t_cin st <= cin1 <= c_n cx -> 3 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
    8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
    evtF asegs RNG POST
      (MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 (Z_to_bv 64 (c_p cx + 156)) (Z_to_bv 64 (c_p cx + 168)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (141376 + 2 * t_shave st)) x12 (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (141376 + 2 * t_shave st)) (Z_to_bv 64 (t_ncode st - t_shave st))
               (Z_to_bv 64 (t_shave st + 1)) x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 bits1) (Z_to_bv 64 hold1) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
               (Z_to_bv 64 (c_q cx + cin1)) (Z_to_bv 64 (c_n cx - cin1)) (Z_to_bv 64 (c_p cx + 28)) (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 8) 3 + 2147450880)) x31)
          FR (Z_to_bv 64 0x8eba0) fc None m (seg_rom asegs)).
  Proof.
    intros until bits1. intros HEAD HN HJN ENV HCL CTX PAYR PLEN MODE SI ARR VIS HID KA HC HB HH HBC HW.
    destruct (ll_mode_facts _ _ _ _ SI MODE) as (NC1 & NC2 & SH0 & SH1 & L7 & RLF).
    pose proof (order_f_range (t_shave st) ltac:(lia)) as ORJ.
    pose proof (drop3_bound hold1 bits1 HH ltac:(lia)) as D3.
    inf_arm_open.
    pose proof (pow2_le_40 bits1 ltac:(lia)) as P40.
    zs. zs.
    zs.
    lazymatch type of MU with munch _ _ ?mc =>
      pose proof (shadow_bytes_munch _ _ mc _ _ _ SHOR MU DJOR) as SHOR1; pose proof (shadow_bytes_munch _ _ mc _ _ _ SHO6 MU DJO6) as SHO61;
      destruct (order_check mc shave SHOR1 SHO61 ltac:(lia)) as (b & RDB & CK);
      pose proof (order_read mc shave _ MI ltac:(lia) eq_refl) as RDO
    end.
    zs. zs. zs. rewrite sxb_sval.
    ck_branchJ 17 0x8ebbc CK.
    zs. rewrite (zx16_small (order_f shave)) by lia. clear RDO RDB.
    zs. setreg 12 (Z_to_bv 64 (2 * order_f shave)) ltac:(rewrite shl1_2x; reflexivity).
    zs. zs. zs. zs. zs.   (* 1.4 keeps lens in t2, so no `ld a7,408(s1)` (1.3.1 had six steps here) *)
    zs. setreg 17 (Z_to_bv 64 (hold1 mod 8)) ltac:(rewrite land7_mod by lia; reflexivity).
    zs. setreg 20 (Z_to_bv 64 (hold1 / 8)) ltac:(rewrite Z.shiftr_div_pow2 by lia; reflexivity).   (* [U14] hold is s4 at 1.4 *)
    zs. zs. zs. zs.
    pose proof (Z.mod_pos_bound hold1 8 ltac:(lia)) as RV.
    lazymatch type of LENS with f16arr _ ?mc _ _ _ =>
      assert (SOK : store_ok asegs mc (Z_to_bv 64 (S + 168 + 2 * order_f shave)) 2 = true)
        by (eapply (f16arr_store_ok asegs mc (S + 168) 320 lf (order_f shave)); [exact LENS| lia| reflexivity]);
      zstep;
      pose proof (f16arr_write asegs mc (S + 168) 320 lf (order_f shave) (Z_to_bv 64 (hold1 mod 8)) (hold1 mod 8) LENS ltac:(lia) eq_refl) as LENS'
    end.
    store_done.
    pose proof (lens_rng_upd lf (order_f shave) (hold1 mod 8) RLF ltac:(lia)) as RLF'.
    pose proof (lens7_upd lf shave (hold1 mod 8) L7 ltac:(lia)) as L7'.
    destruct (sinv_ll _ _ lf cf cin1 (hold1 / 8) (bits1 - 3) (shave + 1) (fupd lf (order_f shave) (hold1 mod 8)) SI MODE
                ltac:(icx_cbn; lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(lia) RLF' L7') as (SI' & ME').
    unfold st_ll in SI', ME'. icx_cbn.
    zs. zs. zbr0 KJ.
    -
      replace (ncode - shave + -1) with (ncode - (shave + 1)) by lia. replace (bits1 + -3) with (bits1 - 3) by lia.
      replace (141376 + 2 * shave + 2) with (141376 + 2 * (shave + 1)) by lia. replace (shave + 2) with (shave + 1 + 1) by lia.
      eapply (HEAD (IST mode last flags cin1 cout (hold1 / 8) (bits1 - 3) out ret len offset extra lc dc lb db ncode nlen ndist (shave + 1) nx whave wnext)
                   (fupd lf (order_f shave) (hold1 mod 8)) cf wf fo);
        [icx_cbn; lia| icx_cbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI'| exact ARR| inf_vis_close| inf_hid_close
        | eapply KALL_mono; [| exact KA]; exact ME'].
    -
      zs. zs.
      setreg 16 (Z_to_bv 64 (shave + 1)) ltac:(f_equal; lia). replace (bits1 + -3) with (bits1 - 3) by lia.
      eapply (ll_fill AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin1 cout (hold1 / 8) (bits1 - 3) out ret len offset extra lc dc lb db ncode nlen ndist (shave + 1) nx whave wnext)
                (fupd lf (order_f shave) (hold1 mod 8)) cf wf fo);
        [exact ENV| exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI'| exact ARR| inf_vis_close| inf_hid_close
        | eapply KALL_mono; [| exact KA]; exact ME'].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
