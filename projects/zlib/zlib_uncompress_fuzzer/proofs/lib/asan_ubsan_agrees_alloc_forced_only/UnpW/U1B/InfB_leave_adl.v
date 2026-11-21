(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface U2BCall InfBBase InfBKit AdlUBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

(* [comment removed for export] *)
Lemma seq_split_nth : forall (a k : nat), seq a (S k) = a :: seq (S a) k. Proof. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.

Lemma f8arr_sub_bytes : forall m A n f (a k : nat), f8arr bsegs m A n f -> (a + k <= n)%nat ->
  bytes_at bsegs m (A + Z.of_nat a) (map (Z_to_bv 8) (map (fun i => f (Z.of_nat i)) (seq a k))).
Proof.
  intros m A n f a k [(H0 & H1 & HB) _] Hk. rewrite length_map, length_seq in H1.
  split; [lia|]. split; [rewrite !length_map, length_seq; lia|].
  intros i Hi. rewrite !length_map, length_seq in Hi.
  replace (A + Z.of_nat a + Z.of_nat i) with (A + Z.of_nat (a + i)) by lia.
  rewrite (HB (a + i)%nat) by (rewrite length_map, length_seq; lia).
  rewrite !nth_error_map. rewrite !nth_error_seq.
  destruct (Nat.ltb_spec (a + i) n) as [X|X]; [| lia]. destruct (Nat.ltb_spec i k) as [Y|Y]; [| lia]. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Definition adl_postz (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (res : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPV - 176, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV.

Lemma adler32_callz : adler32_stmtU ->
  forall (lo : Z) (bs : list Z) (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV adler A v : Z),
  0 <= SPV < 2^64 ->
  mem_inv bsegs m ->
  stk bsegs m lo SPV -> lo <= SPV - 176 -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  0 <= adler < 2^64 -> 1 <= A -> A + Z.of_nat (length bs) <= lo ->
  0 <= v < 2^64 -> v mod 2^32 = Z.of_nat (length bs) ->
  bytes_at bsegs m A (map (Z_to_bv 8) bs) -> Forall (fun b => 0 <= b < 256) bs ->
  unpoisoned m A (A + Z.of_nat (length bs)) ->
  rng RNG A (Z.of_nat (length bs)) ->
  (A < A + Z.of_nat (length bs) -> rng RNG (shad A) (shad (A + Z.of_nat (length bs) - 1) + 1 - shad A)) ->
  rng_aimg RNG -> rng RNG lo (SPV - lo) ->
  evtF bsegs RNG (adl_postz ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 adler) (Z_to_bv 64 A) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 A_ADLER32) fc None m (seg_rom bsegs)).
Proof.
  intros ADL. intros until v. intros RS. intros.
  eapply evtF_mono; [eapply (ADL RNG _ (Z_to_bv 64 SPV) _ _ _ _ _ _ _ (Z_to_bv 64 adler) (Z_to_bv 64 A) (Z_to_bv 64 v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo adler A v bs);
                     rewrite ?unsigned_lit by lia; try eassumption; reflexivity|].
  cbv beta. unfold adl_postU, adl_postz, ADL_STACK. rewrite !unsigned_lit by lia. intros ms' PO. exact PO.
Qed.

Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).
  Hypothesis ADL : adler32_stmtU.

  (* W03 UNPATCHED: the check update of the leave (wrap bit 4 set, out <> 0), from 0x93738 (after
     the totals, the fall-through of the out test at 0x93734): adler32 over the out bytes just written (flags is 0),
     then the stores of state->check and strm->adler; it ends at 0x9382c (the data_type block, InfB_fin's
     inf_retrule), the continuation K. At 0x93738: a1 = out (zero extended), a2 = out (the adler32 length),
     s3 = avail_in, s4 = avail_out (both loaded back by the totals), s2 = strm, s6 = the shadow base, s9 / s10 = the
     fake frame shadow / the fake frame, s11 = the return code. s0 (x8) is passed through to the epilogue. On the
     way: s5 is reloaded (the shadow of state->bits) and ra is reloaded (the fake frame). *)
  Lemma inf_leave_adl : forall (cx : ictx) (ly : ilay) (st : ist) (rv : Z) (lf cf wf fo : Z -> Z)
      (v0 v8 v16 v24 v240 v328 v512 j544 j552 zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
      (x1 x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x21 x23 x24 x28 x29 x30 x31 : word) (m : amem),
    inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx ->
    sinv cx st lf cf -> inf_arr_ok cx wf fo -> 0 <= rv < 18446744073709551616 ->
    t_out st <> c_osz cx - t_cout st ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
            (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
            zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    (forall (zadl' check' : word) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y24 y28 y29 y30 y31 : word) (m1 : amem),
       inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v24 v240 v328 v512 j544 j552
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (c_n cx - t_cin st)) zti (Z_to_bv 64 (c_ob cx + t_cout st)) (Z_to_bv 64 (c_osz cx - t_cout st))
               zto zmsg zopq zdt zadl' zres zp1 zp2 zp3 havedict dmax check' total (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st)) back was pad m1 ->
       inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m1 ->
       evtF bsegs RNG POST
         (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp y5 y6 y7 x8 (Z_to_bv 64 (l_SPA ly)) y10
                  y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_osz cx - t_cout st))
                  (Z_to_bv 64 (Z.shiftr (c_p cx + 104) 3 + 2147450880)) (Z_to_bv 64 2147450880) y23 y24
                  (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 rv) y28 y29 y30 y31)
             FR (Z_to_bv 64 0x9382c) fc None m1 (seg_rom bsegs))) ->
    evtF bsegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (l_SPA ly)) x10
               (Z_to_bv 64 ((t_out st - (c_osz cx - t_cout st)) mod 4294967296)) (Z_to_bv 64 (t_out st - (c_osz cx - t_cout st)))
               x13 x14 x15 x16 x17 (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (c_n cx - t_cin st)) (Z_to_bv 64 (c_osz cx - t_cout st))
               x21 (Z_to_bv 64 2147450880) x23 x24
               (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 rv) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x93738) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros CTX PLEN SI ARR RRV KOUT VIS HID K.
    pose proof HID as (AH0 & _). pose proof (AI_rtcells AI _ _ _ _ _ AH0) as ART. unfold artcells in ART.
    destruct ART as (_ & RTG & _ & _ & RTS & _).
    inf_arm_open.
    assert (FL0 : flags = 0).
    { pose proof SI as (_ & _ & PR & MO). destruct MO as (_ & MFL & _). destruct PR as (_ & _ & P3).
      cbn [c_osz c_cout0 t_mode t_flags t_cout t_out] in MFL, P3.
      destruct (Z.eq_dec flags (-1)) as [E|E]; [exfalso; destruct (MFL E) as (_ & C0); lia| unfold hid in *; lia]. }   (* [comment removed for export] *)
    pose proof (proj2 ARR) as ARO. cbn [c_osz] in ARO.
    Time zrung [0x937e4].
    pose proof (bv_unsigned_in_range 64 check) as RCHK. unfold bv_modulus in RCHK.
    lazymatch goal with H : f8arr bsegs ?mx 6341120 _ fo |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (f8arr_sub_bytes mx 6341120 (Z.to_nat osz) fo (Z.to_nat (cout - (out - (osz - cout)))) (Z.to_nat (out - (osz - cout))) H ltac:(lia)) as BUF end.
    replace (6341120 + Z.of_nat (Z.to_nat (cout - (out - (osz - cout))))) with (6341120 + (cout - (out - (osz - cout)))) in BUF by lia.
    set (bs := map (fun i => fo (Z.of_nat i)) (seq (Z.to_nat (cout - (out - (osz - cout)))) (Z.to_nat (out - (osz - cout))))) in *.
    assert (BL : Z.of_nat (length bs) = out - (osz - cout)) by (subst bs; rewrite length_map, length_seq; lia).
    assert (BR : Forall (fun b => 0 <= b < 256) bs).
    { subst bs. apply Forall_forall. intros b Hb. apply in_map_iff in Hb. destruct Hb as (i & <- & Hi). apply in_seq in Hi. apply ARO. lia. }
    clearbody bs.
    assert (ODR : 0 < out - (osz - cout) <= cout /\ cout <= osz /\ osz <= 262144) by lia.
    zs. (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (6341120 + (cout - (out - (osz - cout))))) ltac:(rewrite Z.mod_small by lia; f_equal; lia).
    setreg 10 (Z_to_bv 64 (bv_unsigned check)) ltac:(apply Z_to_bv_bv_unsigned).
    callq (adler32_callz ADL lo bs RNG).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- bytes_at _ _ _ _ => exact BUF
         | |- Forall _ _ => exact BR
         | |- stk _ _ _ _ => eassumption
         | |- mem_inv _ _ => eassumption
         | |- rw_cells _ _ _ _ => eassumption
         | |- rng_aimg _ => exact RI
         | |- unpoisoned _ _ _ => rewrite BL; eapply (unp_of_sh0 _ 6341120 32768); [exact (sh0_mu _ _ _ _ _ SHO MU DJO)| reflexivity| lia| lia| lia| lia| lia]
         | |- rng _ ?l _ => first [ constr_eq l lo; eapply rng_sub'; [exact RSTK| lia] | rewrite BL; eapply rng_sub'; [exact ROB| lia] ]
         | |- _ -> rng _ _ _ => intros _; rewrite BL; eapply rng_sub'; [exact ROBS|]; rewrite !shad_div; unfold ASHOFF;
                                rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - ODR; Z.div_mod_to_equations; lia
         | |- _ => first [ rewrite BL; unfold KHIGH; lia | unfold KHIGH; lia | rewrite BL; apply Z.mod_small; lia ]
         end.
    Time zrung [0x9382c].
    eapply K; [inf_vis_close| inf_hid_close].
    Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
