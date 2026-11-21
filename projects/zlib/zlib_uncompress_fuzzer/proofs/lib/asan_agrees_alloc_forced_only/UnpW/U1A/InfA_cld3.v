(* reloc-zl14c *)
(* [U14] inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab InfPure_cld InfAGlue_w7 ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base InfA_w6base InfA_w7pull U2AIface_fit2_draft InfA_itcall InfA_cldone_base InfA_garmc InfA_cld1 InfA_cld2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
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

  (* [U14] the 1.4 DONE block.  0x8f5d8: mode is not BAD (reload t4 t3 t2) -> 0x8f61c
     lhu lens[256] -> beqz: = 0 -> 0x8fb08 (msg := .str.11) -> BADMODE 0x9156c; <> 0 -> next := lencode := codes,
     lenbits := 9 -> the LENS call 0x8f68c (ra = 0x8f690) -> cld_post1.  Needs CLDONE with t6 = S+108 and slot 488 =
     (S+108)>>3 (cldone_base p1). *)
  Theorem cldone_thm : forall cx ly, itcall_env AI rng_fs L RNG LB tp ly -> garmcf_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x90950 LEN_ ->
    cldone_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh.
  Proof.
    intros cx ly ENV HLEN_. unfold cldone_stmtA, CLDONE_MS. intros until m. intros CTX PAYR PLEN MODE SHV SI ARR VIS HID KA.
    pose proof KA as (KD & KB & KL & KLV).
    (* [comment removed for export] *)
    destruct (ex_intro (fun r0 => r0 = resA InflateState.LENS lf 0 (t_nlen st) 0 9 cf wf) _ eq_refl) as [r1 ER1].
    destruct (ex_intro (fun r0 => r0 = resA DISTS lf (t_nlen st) (t_ndist st) (it_table r1) 6 (arr_get (it_tbl r1)) (arr_get (it_work r1))) _ eq_refl) as [r2 ER2].
    pose proof (cl_exits cx st lf cf wf r1 r2 SI MODE SHV (proj1 ARR) ER1 ER2) as EX. cbv zeta in EX.
    destruct EX as (ITC1 & RN1 & RW1 & NL & ND & HBAD1 & HOK1).
    pose proof (sinv_bad_ofP _ _ lf cf SI) as SIB. pose proof (meas_bad_ofP cx st) as MEB. rewrite MODE in MEB. change (rank CODELENS) with 20 in MEB.
    revert ITC1 RN1 RW1 HBAD1 HOK1 ER1 ER2 SIB MEB.
    inf_arm_open. intros ITC1 RN1 RW1 HBAD1 HOK1 ER1 ER2 SIB MEB. subst mode.
    change CODELENS with 16198 in SSC.
    Time zrunb [0x8f604].
    pose proof (f16arr_read asegs _ (S + 168) 320 lf 256 (Z_to_bv 64 (S + 680)) LENS ltac:(clear; lia) ltac:(unfold wa; f_equal; clear; lia)) as RD256.
    pose proof (rng_acc_litZ RNG S 7176 (S + 680) 2%nat 2 RS eq_refl ltac:(clear; lia) ltac:(clear; lia)) as AC256.
    pose proof (R30 256 ltac:(unfold N_LENS; clear; lia)) as LF256.
    zs. cbv beta. rewrite (zx16_small (lf 256)) by (clear - LF256; lia).
    zs. zbr0 K256.
    - (* [comment removed for export] *)
      Time zrunb [0x915d4].
      unfold bad_ofP in SIB, MEB. st_norm SIB. st_norm MEB.
      eapply (KB (IST CODELENS last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SIB| unfold bad_of; icx_cbn; clear - MEB; lia| exact ARR| change CODELENS with 16198; inf_vis_close| inf_hid_close].
    - (* [comment removed for export] *)
      Time zrunb [0x95884].
      replace (S + 1384) with (S + 1384 + 4 * 0) in SSC by (clear; lia).
      eapply (inf_itcall AI rng_fs L RNG stA LB LBc m0 payload POST (ICX u S D n 6335616 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST CODELENS last flags cin cout hold bits out ret len offset extra (CDyn 0) dc 9 db ncode nlen ndist shave 0 whave wnext) lf cf wf fo fw)
        with (isd := false) (ty := InflateState.LENS) (lens_ofs := 0) (codes := nlen) (bits := 9) (RA := 0x8f678) (r := r1);
        [exact ENV| exact CTX0| change CODELENS with 16198; inf_vis_close| inf_hid_close| exact PLEN| reflexivity| exact ITC1| exact ER1| reflexivity| lia| reflexivity| reflexivity
        | reflexivity| icx_cbn; f_equal; lia| reflexivity| reflexivity| reflexivity| reflexivity| ].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' VIS' HID' RET1.
      eapply (cld_post1 AI rng_fs L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6335616 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (st_itab (IST CODELENS last flags cin cout hold bits out ret len offset extra (CDyn 0) dc 9 db ncode nlen ndist shave 0 whave wnext) false (it_bits r1) (it_table r1))
                lf (arr_get (it_tbl r1)) (arr_get (it_work r1)) fo) with (B := meas (ICX u S D n 6335616 osz Wd cin0 cout0 W0 K0 zc) (IST CODELENS last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) (r2 := r2);
        [exact ENV| exact HLEN_| exact CTX0| exact PAYR| exact PLEN| reflexivity| exact RN1| split; [exact RW1| exact (proj2 ARR)]| exact NL| exact ND| exact VIS'| exact HID'
        | split; [exact KD| split; [exact KB| split; [exact KL| exact KLV]]]| exact RET1| exact HBAD1| ].
      intros E0. destruct (HOK1 E0) as (ITC2 & RN2 & RW2 & HOK2 & HBAD2).
      split; [exact ITC2|]. split; [exact ER2|]. split; [exact RN2|]. split; [exact RW2|]. split; [exact HOK2| exact HBAD2].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] a worker: the v240 vestige binders *)
  Time Qed.
End S.
End CANSEC1.
