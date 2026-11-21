(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AArr U2AObj U2AIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition L_DISP : Z := 0x8e210.
Definition L_BADMODE : Z := 0x91850.
Definition L_LEAVE_LD : Z := 0x92664.
Definition L_LEAVE : Z := 0x92900.
Definition L_MEM : Z := 0x928bc.
Definition L_EPI : Z := 0x92c2c.
Definition A_LENFIX : Z := 0x24860.
Definition A_DISTFIX : Z := 0x25260.
Definition A_ORDER : Z := 0x22840.

Record ilay := ILAY { l_SP : Z; l_SPA : Z; l_Zs : Z; l_F0 : Z; l_lo : Z }.

Definition cp_addrA (S : Z) (cp : codeptr) : Z :=
  match cp with CDyn ofs => S + 1384 + 4 * ofs | CLenfix => A_LENFIX | CDistfix => A_DISTFIX end.

Section CANSEC1. Context {rc : runConstT}.

Definition inf_locals (S Zs F0 : Z) (v0 v8 v16 v240 vret vin vout vput vnext v504 j512 j520 : word) : list cell :=
  [C8 v0;
   C8 (Z_to_bv 64 (Zs + 32));
   C8 (Z_to_bv 64 (S + 32));
   C8 (Z_to_bv 64 (S + 68));
   C8 (Z_to_bv 64 (S + 680));
   C8 (Z_to_bv 64 (S + 88));
   C8 (Z_to_bv 64 (S + 80));
   C8 (Z_to_bv 64 (F0 + 32));
   C8 (Z_to_bv 64 (S + 7168));
   C8 (Z_to_bv 64 S);
   C8 (Z_to_bv 64 (S + 1384));
   C8 (Z_to_bv 64 (S + 808));
   C8 (Z_to_bv 64 (S + 160));
   C8 (Z_to_bv 64 (S + 24));
   C8 v8;
   C8 (Z_to_bv 64 (S + 140));
   C8 (Z_to_bv 64 (S + 144));
   C8 (Z_to_bv 64 (S + 152));
   C8 (Z_to_bv 64 (S + 148));
   C8 (Z_to_bv 64 (S + 76));
   C8 (Z_to_bv 64 (S + 7160));
   C8 (Z_to_bv 64 18446744073709551611);
   C8 (Z_to_bv 64 (S + 136));
   C8 (Z_to_bv 64 (S + 120));
   C8 (Z_to_bv 64 (S + 128));
   C8 (Z_to_bv 64 (S + 112));
   C8 (Z_to_bv 64 (S + 156));
   C8 (Z_to_bv 64 (S + 116));
   C8 (Z_to_bv 64 (Zs + 48));
   C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 (S + 7164));
   C8 (Z_to_bv 64 (S + 72));
   C8 (Z_to_bv 64 (Zs + 40));
   C8 (Z_to_bv 64 (S + 96));
   C8 (Z_to_bv 64 (Zs + 24));
   C8 (Z_to_bv 64 (Zs + 8));
   C8 vret;
   C8 (Z_to_bv 64 (S + 48));
   C8 (Z_to_bv 64 (Z.shiftr (Zs + 32) 3 + 2147450880));
   C8 (Z_to_bv 64 (Z.shiftr (Zs + 8) 3 + 2147450880));
   C8 (Z_to_bv 64 (Z.shiftr (S + 96) 3 + 2147450880));
   C8 (Z_to_bv 64 (Z.shiftr Zs 3 + 2147450880));
   C8 vin;
   C8 (Z_to_bv 64 (Zs + 96));
   C8 (Z_to_bv 64 (S + 12));
   C8 (Z_to_bv 64 (Z.shiftr (Zs + 24) 3 + 2147450880));
   C8 (Z_to_bv 64 (Z.shiftr (S + 104) 3 + 2147450880));
   C8 (Z_to_bv 64 (S + 104));
   C8 (Z_to_bv 64 (S + 16));
   C8 (Z_to_bv 64 (S + 40));
   C8 (Z_to_bv 64 (S + 168));
   C8 (Z_to_bv 64 (S + 8));
   C8 (Z_to_bv 64 (F0));
   C8 vput;
   C8 vout;
   C8 (Z_to_bv 64 18446744073709535436);
   C8 (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880));
   C8 (Z_to_bv 64 (S + 28));
   C8 (Z_to_bv 64 (S + 108));
   C8 (Z_to_bv 64 16209);
   C8 (Z_to_bv 64 (S + 56));
   C8 v16;
   C8 vnext;
   C8 v504;
   C8 j512;
   C8 j520;
   C8 (Z_to_bv 64 (F0))].


Section Act.
Variables (cx : ictx) (ly : ilay).
Notation S := (c_p cx).   Notation D := (c_q cx).   Notation n := (c_n cx).
Notation OB := (c_ob cx). Notation osz := (c_osz cx). Notation Wd := (c_w cx).
Notation SP := (l_SP ly). Notation SPA := (l_SPA ly). Notation Zs := (l_Zs ly). Notation F0 := (l_F0 ly). Notation lo := (l_lo ly).

Definition inf_W : list (Z * Z) := [(lo, SPA + 536); (Zs, Zs + 112); (S, S + 7176); (OB, OB + osz)].

Definition inf_vis (st : ist) (lf cf wf fo : Z -> Z) (payload : list Z) (v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (m : amem) : Prop :=
     rw_cells asegs m SPA (inf_locals S Zs F0 v0 v8 v16 v240 (Z_to_bv 64 (t_ret st)) (Z_to_bv 64 (n - c_cin0 cx)) (Z_to_bv 64 (t_out st))
                                        (Z_to_bv 64 (OB + t_cout st)) vnext v504 j512 j520)
  /\ rw_cells asegs m Zs (strm_cells zni zai zti zno zao zto zmsg (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) zopq zdt zadl zres zp1 zp2 zp3)
  /\ rw_cells asegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 (t_mode st)) (Z_to_bv 64 (t_last st)) (Z_to_bv 64 5) havedict
                                       (Z_to_bv 64 (t_flags st)) dmax check total (Z_to_bv 64 0) (Z_to_bv 64 15) (Z_to_bv 64 (wsz cx))
                                       (Z_to_bv 64 (t_whave st)) (Z_to_bv 64 (t_wnext st)) (Z_to_bv 64 Wd) shold sbits
                                       (Z_to_bv 64 (t_length st)) (Z_to_bv 64 (t_offset st)) (Z_to_bv 64 (t_extra st))
                                       (Z_to_bv 64 (cp_addrA S (t_lc st))) (Z_to_bv 64 (cp_addrA S (t_dc st)))
                                       (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (t_db st)) (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (t_nlen st))
                                       (Z_to_bv 64 (t_ndist st)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (S + 1384 + 4 * t_nx st)))
  /\ f16arr asegs m (S + 168) 320 lf /\ f16arr asegs m (S + 808) 288 wf /\ f32arr asegs m (S + 1384) 1444 cf
  /\ rw_cells asegs m (S + 7160) (itail_cells (Z_to_bv 64 1) back was pad)
  /\ f8arr asegs m OB (Z.to_nat osz) fo
  /\ bytes_at asegs m D (map (Z_to_bv 8) payload)
  /\ stk asegs m lo SPA /\ mem_inv asegs m
  /\ t_mode st <> MEM.

Definition inf_saved (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) : list cell :=
  [C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0].

Section Hid.
Variable AI : AMallocIface.
Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).

Definition inf_WR : list (Z * Z) := [(Zs, Zs + 112); (S, S + 7176); (OB, OB + osz); (Wd, Wd + 32768); (0, 32768)].

Definition inf_hid (LBc : list ablock) (m0 : amem) (fw : Z -> Z) (saved : list cell) (fk : list cell) (fksh : list cell) (m : amem) : Prop :=
     AHEAP AI L RNG stA LB m
  /\ shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)
  /\ shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)
  /\ shadow_bytes m (Z.shiftr OB 3 + 2147450880) (Z.shiftr OB 3 + 2147450880 + 32768) (fun _ => 0)
  /\ (Wd <> 0 -> shadow_bytes m (Z.shiftr Wd 3 + 2147450880) (Z.shiftr Wd 3 + 2147450880 + 4096) (fun _ => 0)
                 /\ f8arr asegs m Wd (Z.to_nat 32768) fw)
  /\ unpoisoned m D (D + n)
  /\ rw_cells asegs m (SP + -104) saved /\ cells_size saved = 104%nat
  /\ rw_cells asegs m F0 fk /\ cells_size fk = 64%nat
  /\ rw_cells asegs m (Z.shiftr F0 3 + 2147450880) fksh /\ cells_size fksh = 8%nat
  /\ (forall b, In b LBc -> In b LB) /\ client_agree AI LBc SP inf_WR m0 m
  /\ shadow_bytes m 2147469580 2147469836 (fun _ => 0) /\ shadow_bytes m 2147469900 2147469916 (fun _ => 0)
  /\ shadow_bytes m 2147468552 2147468556 (fun _ => 0) /\ shadow_bytes m 2147468556 2147468557 (fun _ => 6)
  /\ shadow_bytes m 2147469532 2147469539 (fun _ => 0) /\ shadow_bytes m 2147469539 2147469540 (fun _ => 6)
  /\ shadow_bytes m 2147469544 2147469551 (fun _ => 0) /\ shadow_bytes m 2147469551 2147469552 (fun _ => 6)
  /\ shadow_bytes m 2147469556 2147469564 (fun _ => 0) /\ shadow_bytes m 2147469568 2147469576 (fun _ => 0)
  /\ stk asegs m (SPA + 536) (SP + -104)
  /\ (exists obr, rw_cells asegs m (OB + osz) [CB (Z.to_nat (262144 - osz)) obr])
  /\ wr_at asegs m (Z.shiftr Zs 3 + 2147450880 - 4) 32.

Definition inf_ctx : Prop :=
     S mod 16 = 0 /\ ablk S (S + 7176)
  /\ (exists ps, In (HB ps S 7176) LB /\ ((exists pd, In (HB pd D n) LB /\ 0 < n /\ pd <> ps) \/ (n = 0 /\ D = 0x60af20)))
  /\ (exists Fu, strm_home LB Fu Zs) /\ rng RNG Zs 112 /\ rng RNG (Z.shiftr Zs 3 + 2147450880) 14
  /\ In (mkABlock (ABFake 0) F0 64) LB /\ F0 mod 64 = 0 /\ ablk F0 (F0 + 64)
  /\ rng RNG S 7176 /\ rng RNG (Z.shiftr S 3 + 2147450880) 897
  /\ OB = A_OUTBUF /\ 1 <= osz <= 262144 /\ (exists iv, In iv (aci AI) /\ fst iv <= OB /\ OB + 262144 <= snd iv)
  /\ rng RNG OB 262144 /\ rng RNG (Z.shiftr OB 3 + 2147450880) 32768
  /\ (Wd = 0 \/ (Wd mod 16 = 0 /\ ablk Wd (Wd + 32768) /\ (exists pw, In (HB pw Wd 32768) LB)
                 /\ rng RNG Wd 32768 /\ rng RNG (Z.shiftr Wd 3 + 2147450880) 4096))
  /\ 1 <= D /\ 0 <= n < 67108864 /\ (D mod 16 = 0) /\ rng RNG D n /\ rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1)
  /\ ATOP + 4096 <= lo /\ lo + 8192 <= SPA /\ SP - 656 <= SPA <= SP - 640 /\ SPA mod 32 = 0 /\ SP mod 16 = 0 /\ SP + 16 < KEND
  /\ rng RNG lo (SP - lo) /\ rng_aimg RNG /\ rng_aimg_sh RNG
  /\ rng RNG (Z.shiftr Zs 3 + 2147450880 - 4) 32
  /\ (exists iv, In iv (aci AI) /\ fst iv <= 141376 /\ 152288 <= snd iv)
  /\ (exists iv, In iv (aci AI) /\ fst iv <= 149216 /\ 149568 <= snd iv)
  /\ (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)).
End Hid.

Section MSs.
Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
Definition DISP_MS (st : ist) (x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 : word) (m : amem) : machine_state :=
  (MS (mkR (Z_to_bv 64 (S + 8)) (Z_to_bv 64 SPA) gp tp x5 x6 (Z_to_bv 64 (S + 56)) (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 F0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 Zs) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880) x22 x23 (Z_to_bv 64 (Z.shiftr F0 3 + 2147450880)) (Z_to_bv 64 F0)
             x26 (Z_to_bv 64 (n - t_cin st)) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (osz - t_cout st)) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880)) (Z_to_bv 64 (S + 108)))
        FR (Z_to_bv 64 L_DISP) fc None m (seg_rom asegs)).
Definition ARM_MS (pc : Z) (st : ist) (x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 : word) (m : amem) : machine_state :=
  (MS (mkR (Z_to_bv 64 (S + 8)) (Z_to_bv 64 SPA) gp tp x5 x6 (Z_to_bv 64 (S + 56)) (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 F0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 Zs) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (-3)) (Z_to_bv 64 (Z.shiftr F0 3 + 2147450880)) (Z_to_bv 64 F0)
             (Z_to_bv 64 (D + t_cin st)) (Z_to_bv 64 (n - t_cin st)) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (osz - t_cout st)) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880)) (Z_to_bv 64 (S + 108)))
        FR (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
Definition LEAVE_MS (pc : Z) (st : ist) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x31 : word) (m : amem) : machine_state :=
  (MS (mkR (Z_to_bv 64 (S + 8)) (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 F0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 Zs) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880) x22 x23 (Z_to_bv 64 (Z.shiftr F0 3 + 2147450880)) (Z_to_bv 64 F0)
             (Z_to_bv 64 (D + t_cin st)) (Z_to_bv 64 (n - t_cin st)) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (osz - t_cout st)) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880)) x31)
        FR (Z_to_bv 64 pc) fc None m (seg_rom asegs)).
End MSs.

Section K.
Variable AI : AMallocIface.
Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

Definition inf_arr_ok (wf fo : Z -> Z) : Prop :=
  (forall i, 0 <= i < 288 -> 0 <= wf i < 65536) /\ (forall i, 0 <= i < osz -> 0 <= fo i < 256).

Definition KDISP (B : Z) : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v240 v504 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 : word) (m : amem),
    sinv cx st lf cf -> meas cx st < B -> inf_arr_ok wf fo ->
    inf_vis st lf cf wf fo payload v0 v8 v16 v240 v504 (Z_to_bv 64 (D + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    evtF asegs RNG POST (DISP_MS gp tp FR fc st x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 m).

Definition bad_of (st : ist) : ist :=
  IST BAD (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
      (t_length st) (t_offset st) (t_extra st) (t_lc st) (t_dc st) (t_lb st) (t_db st)
      (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Definition KBADMODE (B : Z) : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v240 v504 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 : word) (m : amem),
    sinv cx (bad_of st) lf cf -> meas cx (bad_of st) < B -> inf_arr_ok wf fo ->
    inf_vis st lf cf wf fo payload v0 v8 v16 v240 v504 (Z_to_bv 64 (D + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    evtF asegs RNG POST (MS (mkR (Z_to_bv 64 (S + 8)) (Z_to_bv 64 SPA) gp tp x5 x6 (Z_to_bv 64 (S + 56)) (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 F0) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 Zs) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880) x22 x23 (Z_to_bv 64 (Z.shiftr F0 3 + 2147450880)) (Z_to_bv 64 F0)
             x26 (Z_to_bv 64 (n - t_cin st)) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 (osz - t_cout st)) (Z_to_bv 64 (Z.shiftr (S + 8) 3 + 2147450880)) (Z_to_bv 64 (S + 108)))
        FR (Z_to_bv 64 L_BADMODE) fc None m (seg_rom asegs)).

Definition KLEAVE_LD : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x31 : word) (m : amem),
    sinv cx st lf cf -> inf_arr_ok wf fo ->
    inf_vis st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    evtF asegs RNG POST (LEAVE_MS gp tp FR fc L_LEAVE_LD st x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x31 m).

Definition KLEAVE : Prop :=
  forall (st : ist) (rv : Z) (lf cf wf fo : Z -> Z) (v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x31 : word) (m : amem),
    sinv cx st lf cf -> inf_arr_ok wf fo ->
    inf_vis st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    evtF asegs RNG POST (LEAVE_MS gp tp FR fc L_LEAVE st x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 (Z_to_bv 64 rv) x31 m).

Definition KALL (B : Z) : Prop := KDISP B /\ KBADMODE B /\ KLEAVE_LD /\ KLEAVE.

Lemma KALL_mono : forall B B', B' <= B -> KALL B -> KALL B'.
Proof.
  intros B B' HB (KD & KB & KL). split; [| split; [| exact KL]].
  - intros until m. intros SI ME. apply KD; [exact SI| lia].
  - intros until m. intros SI ME. apply KB; [exact SI| lia].
Qed.

Definition arm_stmtA (Lb X : Z) : Prop :=
  forall (st : ist) (lf cf wf fo : Z -> Z) (v0 v8 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word) (x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 : word) (m : amem),
    inf_ctx AI RNG LB ->
    Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = n ->
    t_mode st = X -> sinv cx st lf cf -> inf_arr_ok wf fo ->
    inf_vis st lf cf wf fo payload v0 v8 (Z_to_bv 64 (Z.shiftr (S + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (S + 56) 3)) (Z_to_bv 64 (D + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    inf_hid AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    KALL (meas cx st) ->
    evtF asegs RNG POST (ARM_MS gp tp FR fc Lb st x5 x6 x11 x12 x13 x14 x15 x16 x17 x22 m).
End K.
End Act.
End CANSEC1.

