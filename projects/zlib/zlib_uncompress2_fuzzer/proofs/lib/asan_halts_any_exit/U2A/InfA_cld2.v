(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_cld InfAGlue_w7 ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base InfA_w6base InfA_w7pull U2AIface_fit2_draft InfA_itcall InfA_garmc InfA_cld1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
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
  Notation GARMC cx ly Lb X := (garmc_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* the LENS return at 1.4.  rv = 0: 0x8f944 -> 0x8ff54 (distcode := next,
     distbits := 6, shadow checks through s6 = (S+160)sh, slot 504 = (S+148)sh and s10 = (S+152)sh; nlen by lwu at
     0x8ffc4) -> the DISTS call 0x8ffe8 (ra = 0x8ffec) -> cld_post2.  rv <> 0: 0x8f948 (ret := rv, msg := .str.12,
     reload a0 ra t5 t4 t3 t6 t2) -> BADMODE 0x91820.  VIS as CLDONE leaves it: slot 112 = left, slot 504 =
     (S+148)sh, slot 496 = next; slot 488 = (S+108)>>3 (never written by the codelens arm). *)
  Lemma cld_post1 : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v240 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) (m : amem) (rv B : Z) (r2 : Z * arr * Z * Z * arr),
    itcall_env AI rng_fs L RNG LB tp ly -> GARMC cx ly 0x90be0 LEN_ ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> IDefs.RNG cx st lf cf -> inf_arr_ok cx wf fo -> t_nlen st <= 286 -> t_ndist st <= 30 ->
    VIS cx ly st lf cf wf fo v0 (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) (Z_to_bv 64 (c_q cx + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly B ->
    (rv = 0 \/ rv = 1 \/ rv = -1) ->
    (rv <> 0 -> sinv cx (bad_of (st_ret st (rv mod 18446744073709551616))) lf cf /\ meas cx (bad_of (st_ret st (rv mod 18446744073709551616))) < B) ->
    (rv = 0 -> itc DISTS lf (t_nlen st) (t_ndist st) (t_nx st) 6 cf wf /\ r2 = resA DISTS lf (t_nlen st) (t_ndist st) (t_nx st) 6 cf wf
               /\ IDefs.RNG cx (st_itab (st_pre2 st) true (it_bits r2) (it_table r2)) lf (arr_get (it_tbl r2))
               /\ (forall i, 0 <= i < 288 -> 0 <= arr_get (it_work r2) i < 65536)
               /\ (it_ret r2 = 0 -> sinv cx (st_len_ (st_itab (st_pre2 st) true (it_bits r2) (it_table r2))) lf (arr_get (it_tbl r2))
                                    /\ meas cx (st_len_ (st_itab (st_pre2 st) true (it_bits r2) (it_table r2))) <= B)
               /\ (it_ret r2 <> 0 -> sinv cx (st_badr (st_itab (st_pre2 st) true (it_bits r2) (it_table r2)) (it_ret r2 mod 18446744073709551616)) lf (arr_get (it_tbl r2))
                                     /\ meas cx (st_badr (st_itab (st_pre2 st) true (it_bits r2) (it_table r2)) (it_ret r2 mod 18446744073709551616)) < B)) ->
    evtF asegs RNG POST (CLD_RET gp tp FR fc cx ly st 0x8f974 rv x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 m).
  Proof.
    intros until r2. intros ENV HLEN_ CTX PAYR PLEN MODE RN0 ARR NL286 ND30 VIS HID KA RET HBAD HOK.
    pose proof KA as (KD & KB & KL & KLV).
    unfold CLD_RET.
    revert HOK. inf_arm_open_rn. intros HOK. subst mode.
    destruct RET as [E|[E|E]]; subst rv.
    -
      destruct (HOK eq_refl) as (ITC2 & ER2 & RN2 & RW2 & HOK2 & HBAD2). clear HOK HBAD.
      Time zrunb [0x95b30].
      eapply (inf_itcall AI rng_fs L RNG stA LB LBc m0 payload POST (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST CODELENS last flags cin cout hold bits out ret len offset extra lc (CDyn nx) lb 6 ncode nlen ndist shave nx whave wnext) lf cf wf fo fw)
        with (isd := true) (ty := InflateState.DISTS) (lens_ofs := nlen) (codes := ndist) (bits := 6) (RA := 0x9001c) (r := r2);
        [exact ENV| exact CTX0| inf_vis_close| inf_hid_close| exact PLEN| reflexivity| exact ITC2| exact ER2| reflexivity| lia| reflexivity| reflexivity
        | reflexivity| icx_cbn; rewrite (zx32_small nlen) by (clear - R21; lia); rewrite unsigned_lit by (clear - R21; lia);
          f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia| reflexivity| reflexivity| reflexivity| reflexivity| ].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' VIS' HID' RET2.
      eapply (cld_post2 AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6336320 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (st_itab (IST CODELENS last flags cin cout hold bits out ret len offset extra lc (CDyn nx) lb 6 ncode nlen ndist shave nx whave wnext) true (it_bits r2) (it_table r2))
                lf (arr_get (it_tbl r2)) (arr_get (it_work r2)) fo);
        [exact HLEN_| exact CTX0| exact PAYR| exact PLEN| reflexivity| exact RN2| split; [exact RW2| exact (proj2 ARR)]| exact VIS'| exact HID'
        | split; [exact KD| split; [exact KB| split; [exact KL| exact KLV]]]| exact RET2| exact HOK2| exact HBAD2].
    -
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change (1 mod 18446744073709551616) with 1 in SI', ME'. unfold st_ret, bad_of in SI', ME'. icx_cbn.
      Time zrunb [0x91850].
      eapply (KB (IST CODELENS last flags cin cout hold bits out 1 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change CODELENS with 16198; inf_vis_close| inf_hid_close].
    -
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change ((-1) mod 18446744073709551616) with 18446744073709551615 in SI', ME'. unfold st_ret, bad_of in SI', ME'. icx_cbn.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; reflexivity).
      Time zrunb [0x91850].
      eapply (KB (IST CODELENS last flags cin cout hold bits out 18446744073709551615 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change CODELENS with 16198; inf_vis_close| inf_hid_close].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* the v240 vestige binders (KB's, KD's) *)
  Time Qed.
End S.
End CANSEC1.
