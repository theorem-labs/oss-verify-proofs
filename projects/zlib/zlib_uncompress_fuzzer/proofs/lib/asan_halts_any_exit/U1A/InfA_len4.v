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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import InfA_len2.
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

  Notation LXB cx ly := (LXB_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).
  Notation LXZ cx ly := (LXZ_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  (* L_E3 moved to the 1.4 homes from the 1.4 code into 0x90d30 (probe Pg28len4 showed the 1.3.1 homes): s4 = hold, s5 = SHB, s6 = left (mv s6,t4 at 0x90c24), s7 = S+116, s10 = next, s11 = have, t3 = B; the x27 parameter now names s3 *)
  Definition L_E3 (cx : ictx) (ly : ilay) (st : ist) (TA i2 hb2 rb ci H B : Z) (x5 x6 x7 x12 x15 x16 x27 x29 x30 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 (c_p cx + 8)) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
            (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (TA + 4 * i2)) x12 (Z_to_bv 64 hb2) (Z_to_bv 64 (Z.shiftr (c_p cx + 7164) 3 + 2147450880)) x15 x16 (Z_to_bv 64 rb)
            (Z_to_bv 64 (l_Zs ly)) x27 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
            (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (c_p cx + 116)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly))
            (Z_to_bv 64 (c_q cx + ci)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 B) x29 x30 x31)
       FR (Z_to_bv 64 0x90d80) fc None m (seg_rom asegs).

  Lemma l_fin2 : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x12 x15 x16 x27 x29 x30 x31 : word) (m : amem) (TA nd XT NS : Z) (rd : Z -> Z) (i2 rb ci H B : Z),
    LXB cx ly -> LXZ cx ly ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LEN -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m -> HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    dtab m TA nd rd -> 0 <= i2 < nd ->
    shadow_bytes m (Z.shiftr XT 3 + 2147450880) (Z.shiftr XT 3 + 2147450880 + NS) (fun _ => 0) -> XT mod 8 = 0 -> 0 <= XT -> XT <= TA -> TA + 4 * nd <= XT + 8 * NS ->
    rng RNG (Z.shiftr XT 3 + 2147450880) NS -> rng RNG TA (4 * nd) -> 0 < TA -> TA + 4 * nd < 140737488355328 ->
    t_cin st <= ci <= c_n cx -> 1 <= rb <= 15 -> 1 <= code_bits (rd i2) -> rb + code_bits (rd i2) <= B -> B <= 40 -> 0 <= H < 2 ^ B -> B <= 8 * ci -> 8 * (c_n cx - ci) + B <= 8 * (c_n cx - t_cin st) + t_bits st ->
    ((code_op (rd i2) = 0 /\ code_val (rd i2) < 256) \/ (16 <= code_op (rd i2) <= 21 /\ 3 <= code_val (rd i2) /\ code_val (rd i2) + 2 ^ (code_op (rd i2) - 16) - 1 <= 258)
     \/ (Z.land (code_op (rd i2)) 64 <> 0 /\ Z.land (code_op (rd i2)) 16 = 0)) ->
    evtF asegs RNG POST (L_E3 cx ly st TA i2 (code_bits (rd i2)) rb ci H B x5 x6 x7 x12 x15 x16 x27 x29 x30 x31 m).
  Proof.
    intros until B. intros HLXB HLXZ CTX PAYR PLEN MODE SI ARR VIS HID KA DT HI2 SBT XT8 XT0 XTL XTH RXT RTA TAP TAH HC HRB HB1 HBB HB40 HH HBC HW HTERM.
    unfold L_E3.
    inf_arm_open.
    set (e := rd i2) in *.
    destruct (DT i2 ltac:(lia)) as (RDR & RD0 & RD1 & RD2). fold e in RD0, RD1, RD2, RDR.
    pose proof (code_op_range e) as OPR. pose proof (code_val_range e) as VALR. pose proof (code_bits_range e) as BITR.
    pose proof (tab_sh0 m XT NS (TA + 4 * i2 + 2) SBT XT8 ltac:(lia) ltac:(lia)) as RDS2.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * i2 + 2) RXT XT8 ltac:(lia) ltac:(lia)) as ACS2.
    pose proof (tab_sh0 m XT NS (TA + 4 * i2) SBT XT8 ltac:(lia) ltac:(lia)) as RDS0.
    pose proof (tab_sh_acc RNG XT NS (TA + 4 * i2) RXT XT8 ltac:(lia) ltac:(lia)) as ACS0.
    pose proof (pow2_le_40 B ltac:(lia)) as P40.
    pose proof (drop_bound H B rb ltac:(lia) HH) as DB.
    zrunb [0x90da4].
    zs. cbv beta. rewrite (zx16_small (code_val e)) by lia.
    zrunb [0x90dc0]. zs. cbv beta. rewrite (u8_lit (code_op e)) by lia.
    zrunb [0x90dd0].
    rewrite (srl_div H rb) by lia.
    zrunb [0x90de0].
    eapply (l_term AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh
              (ICX u S D n 6335680 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo) (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (code_op e) (code_val e) (code_bits e) ci (H / 2 ^ rb) (B - rb)); (* l_term binds s6 (x22) for s7 (x27) *)
      [exact HLXB| exact HLXZ| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close| inf_hid_close| exact KA| | | | | | | | | ];
      first [exact HTERM | clear - HC HRB HB1 HBB HB40 HH HBC HW DB OPR VALR BITR; gcbn; lia].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
