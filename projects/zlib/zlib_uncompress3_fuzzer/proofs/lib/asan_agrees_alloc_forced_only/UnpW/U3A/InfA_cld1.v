(* reloc-zl14c 535b47af8d597a5cb7b0569166841b7b *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_cld.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base InfA_w6base InfA_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import InfA_garmc.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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
  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  Notation GARM cx ly Lb X := (garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation GARMC cx ly Lb X := (garmc_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* [U14] CLD_RET re-derived from the 1.4 listing.  It is the state at the return of
     either inflate_table call of the codelens DONE block (LENS 0x8fa0c -> 0x8fa10, DISTS 0x900b4 -> 0x900b8).  The
     callee-saved registers are as CLDONE_MS (0x8f958) leaves them, with s6 = (S+160)sh set at 0x8f9a8 and s10 =
     (S+152)sh; the path 0x90020 .. 0x900b4 writes no s register.  ra = the return address, a0 = the return value, and
     the caller-saved registers are free (inf_itcall frees them). *)
  Definition CLD_RET (cx : ictx) (ly : ilay) (st : ist) (RA rv : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) (m : amem) : machine_state :=
    MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
            (Z_to_bv 64 (Z.shiftr (c_p cx + 160) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) x23 (Z_to_bv 64 (c_n cx - t_cin st))
            (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) x28 x29 x30 x31)
       FR (Z_to_bv 64 RA) fc None m (seg_rom asegs).

  (* [U14] an earlier development run: the DISTS return.  rv = 0: 0x8fd38 -> 0x908b4 (ret := 0, mode := LEN_, reload ra a0 t3 t4 t5 t6
     s10) -> 0x90c7c, the LEN_ arm, NOT reloading t2 and leaving slot 504 = the codelens arm's (S+148)sh: hence
     GARMC (InfA_garmc), not GARM.  rv <> 0: 0x900bc (ret := rv, msg := .str.13, mode := BAD) -> 0x91a90 (reload t4 t3
     t6 t2) -> DISP 0x8e2ac.  VIS: slot 112 (v8) = left (t4 is reloaded from it), slot 488 (v16) = (S+108)>>3 (the
     codelens arm never writes it, and LEN reads it), slot 496 (vnext) = next (s10 is reloaded from it). *)
  Lemma cld_post2 : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z) (v0 v240 v504 j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) (m : amem) (rv B : Z),
    garmcf_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x90cb0 LEN_ ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> IDefs.RNG cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v504 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (c_osz cx - t_cout st)) (Z_to_bv 64 (c_q cx + t_cin st)) j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly B ->
    (rv = 0 \/ rv = 1 \/ rv = -1) ->
    (rv = 0 -> sinv cx (st_len_ st) lf cf /\ meas cx (st_len_ st) <= B) ->
    (rv <> 0 -> sinv cx (st_badr st (rv mod 18446744073709551616)) lf cf /\ meas cx (st_badr st (rv mod 18446744073709551616)) < B) ->
    evtF asegs RNG POST (CLD_RET cx ly st 0x900f0 rv x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 m).
  Proof.
    intros until B. intros HLEN_ CTX PAYR PLEN MODE RN0 ARR VIS HID KA RET HOK HBAD.
    pose proof KA as (KD & KB & KL & KLV).
    unfold CLD_RET.
    inf_arm_open_rn. subst mode.
    destruct RET as [E|[E|E]]; subst rv.
    - (* [comment removed for export] *)
      destruct (HOK eq_refl) as (SI' & ME'). unfold st_len_ in SI', ME'. icx_cbn.
      Time zrunb [0x90cb0].
      eapply (HLEN_ (IST LEN_ last flags cin cout hold bits out 0 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change LEN_ with 16199; inf_vis_close| inf_hid_close
        | eapply KALL_mono; [| split; [exact KD| split; [exact KB| split; [exact KL| exact KLV]]]]; exact ME'].
    - (* [comment removed for export] *)
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change (1 mod 18446744073709551616) with 1 in SI', ME'. unfold st_badr in SI', ME'. icx_cbn.
      Time zrunb [0x8e2ec].
      eapply (KD (IST BAD last flags cin cout hold bits out 1 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close].
    - (* [comment removed for export] *)
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change ((-1) mod 18446744073709551616) with 18446744073709551615 in SI', ME'. unfold st_badr in SI', ME'. icx_cbn.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; reflexivity).
      Time zrunb [0x8e2ec].
      eapply (KD (IST BAD last flags cin cout hold bits out 18446744073709551615 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Time Qed.
End S.
End CANSEC1.
