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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_w7d InfPure_w7e InfAGlue_w7 InfAGlue_w7b InfPure_table InfPure_itab InfPure_lenlens InfPure_codelens InfPure_codelens2 UbFit2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit InfBTables InfB_w7base InfB_w7tab InfB_w7pull InfB_w6base InfB_w6kit InfB_w6garm InfB_cldone_base InfB_clbase InfB_clbase2 InfB_w7tab16 InfB_clreg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit U2BKit_p04. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import InfBTraps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ub_is_trap pc ::= ub_in_traps inf_traps pc.
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
  Notation VISB cx ly st cs B lf cf wf fo v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly (st_cin st cs) lf cf wf fo payload v0
        (Z_to_bv 64 (Z.shiftr (c_p cx + 152) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 148) 3 + 2147450880)) v8 (Z_to_bv 64 (t_nlen st))
        (Z_to_bv 64 B) (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation CLH cx ly N := (clhead_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLK cx ly N := (clchk_stmt cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh N).
  Notation CLD cx ly := (cldone_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).

  (* [comment removed for export] *)
  Definition CLFILL_MS (cx : ictx) (ly : ilay) (st : ist) (ci H k c rl : Z) (x6 x11 x19 x22 x23 x26 x29 x31 : word) (m : amem) : machine_state :=
    (MS (mkR (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (l_SPA ly)) gp tp (Z_to_bv 64 (c_p cx + 1384)) x6 (Z_to_bv 64 (2 ^ t_lb st - 1)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly))
             (Z_to_bv 64 (c_p cx + 156)) x19 (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 c) (Z_to_bv 64 320)
             (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 k) (Z_to_bv 64 (t_nlen st + t_ndist st))
             (Z_to_bv 64 (l_Zs ly)) x11 x23 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
             x22 x26 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_n cx - ci)) (Z_to_bv 64 (c_q cx + ci)) x29 (Z_to_bv 64 rl) x31)
        FR (Z_to_bv 64 0x8fa70) fc None m (seg_rom bsegs)).

  Lemma cl_fill : forall (C N : nat) (cx : ictx) (ly : ilay) (st : ist) (lf0 lf cf wf fo : Z -> Z)
      (v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x6 x11 x19 x22 x23 x26 x29 x31 : word) (m : amem) (cs ci H B k c rl : Z),
    CLH cx ly N -> CLD cx ly ->
    (Z.to_nat (t_nlen st + t_ndist st - t_shave st) <= S N)%nat ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = CODELENS -> sinv cx st lf0 cf -> inf_arr_ok cx wf fo ->
    VISB cx ly st cs B lf cf wf fo v0 v8 j544 j552 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    buf_ok cx st ci H B -> 0 <= rl <= 15 ->
    (Z.to_nat c <= C)%nat -> 1 <= c -> t_shave st <= k -> k + c <= t_nlen st + t_ndist st ->
    (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> (forall i, 0 <= i < k -> lf i <= 15) ->
    evtF bsegs RNG POST (CLFILL_MS cx ly st ci H k c rl x6 x11 x19 x22 x23 x26 x29 x31 m).
  Proof.
    induction C as [|C IH]; intros until rl; intros HEAD DONE HN CTX PAYR PLEN MODE SI ARR VIS HID KA BUF HLEN HC HC1 HK HKC RLF L15; [lia|].
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold CLFILL_MS.
    assert (RNH : IDefs.RNG cx st lf0 cf) by (exact (proj1 SI)).
    revert IH HEAD DONE. inf_arm_open_sn. intros IH HEAD DONE.
    match goal with HA : _ <= ATOP <= _ |- _ => rename HA into ATB end.
    eapply (cl_fill_g RNG POST) with (k := k); [clear - SH0 HK HKC HC1 NL2 ND2; lia|].
    zs. rewrite (lnot64 (S + 168)) by (clear - S1 S2 ATB; lia).
    eapply (cl_fill_g2 RNG POST) with (LA := S + 168) (k2 := 2 * k); [clear - S1 S2 ATB; lia| clear - SH0 HK HKC HC1 NL2 ND2; lia|].
    zs. zs. setreg 11 (Z_to_bv 64 (S + 168 + 2 * k)) ltac:(f_equal; clear; lia).
    pose proof (tab_sh0 m S 897 (S + 168 + 2 * k) SHS S8 ltac:(clear - SH0 HK HKC HC1 NL2 ND2; lia) ltac:(clear - S1; lia)) as RDS.
    pose proof (tab_sh_acc RNG S 897 (S + 168 + 2 * k) RSS S8 ltac:(clear - SH0 HK HKC HC1 NL2 ND2; lia) ltac:(clear - S1; lia)) as ACS.
    zs. zs. zs. zs.
    zs.
    assert (SOK : store_ok bsegs m (Z_to_bv 64 (S + 168 + 2 * k)) 2 = true)
      by (eapply (f16arr_store_ok bsegs m (S + 168) 320 lf k); [exact LENS| clear - SH0 HK HKC HC1 NL2 ND2; lia| reflexivity]).
    zstep.
    pose proof (f16arr_write bsegs m (S + 168) 320 lf k (Z_to_bv 64 rl) rl LENS ltac:(clear - SH0 HK HKC HC1 NL2 ND2; lia) eq_refl) as LENS'.
    store_done.
    pose proof (lens_rng_upd lf k rl RLF ltac:(clear - HLEN; lia)) as RLF'.
    pose proof (lens15_upd lf k rl L15 ltac:(clear - HLEN; lia)) as L15'.
    zs. zs. zbr0 KC.
    - (* [comment removed for export] *)
      replace (c + -1) with (c - 1) by (clear; lia).
      eapply (IH N (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf0 (fupd lf k rl) cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cs ci H B (k + 1) (c - 1) rl);
        [exact HEAD| exact DONE| exact HN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| inf_vis_close_sn| inf_hid_close| exact KA| exact BUF| exact HLEN
        | clear - HC KC HC1; lia| clear - KC HC1; lia| clear - HK; gcbn; lia| clear - HKC; gcbn; lia| exact RLF'| exact L15'].
    - (* [comment removed for export] *)
      zs.
      zs. zs. zs. zs. zs.
      destruct (sinv_clb _ _ lf0 cf ci H B (k + 1) (fupd lf k rl) SI MODE BUF ltac:(clear - SH0 HK; gcbn; lia) ltac:(clear - HKC KC HC1; gcbn; lia) RLF' L15') as (SI' & ME').
      unfold st_cl in SI', ME'. cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SI', ME'.
      zs. zbr0 KJ.
      + eapply (HEAD (IST mode last flags ci cout H B out ret len offset extra lc dc lb db ncode nlen ndist (k + 1) nx whave wnext) (fupd lf k rl) cf wf fo);
          [clear - HN HK; gcbn; lia| clear - KJ; gcbn; lia| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI'| exact ARR| inf_vis_close| inf_hid_close
          | eapply KALL_mono; [| exact KA]; exact ME'].
      + zs.
        eapply (DONE (IST mode last flags ci cout H B out ret len offset extra lc dc lb db ncode nlen ndist (k + 1) nx whave wnext) (fupd lf k rl) cf wf fo);
          [exact CTX0| exact PAYR| exact PLEN| exact MODE| clear - KJ; gcbn; lia| exact SI'| exact ARR| inf_vis_close| inf_hid_close
          | eapply KALL_mono; [| exact KA]; exact ME'].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  Lemma cl_chk : forall (N : nat) (cx : ictx) (ly : ilay), CLH cx ly N -> CLD cx ly -> CLK cx ly N.
  Proof.
    intros N cx ly HEAD DONE. unfold clchk_stmt, CLCHK_MS. intros until rl. intros HN HJN CTX PAYR PLEN MODE SI ARR VIS HID KA BUF HCP HRL.
    pose proof KA as (KD & KB & KL & KLV).
    destruct (cl_facts _ _ _ _ SI MODE) as (NL1 & NL2 & ND1 & ND2 & SH0 & SH1 & L15 & _ & _ & _ & _ & _ & _ & RLF & _).
    destruct (sinv_cl_bad _ _ _ _ ci H B SI MODE BUF) as (SIB & MEB).
    revert HEAD DONE. inf_arm_open_s. intros HEAD DONE.
    eapply (cl_chk_a RNG POST) with (cp := copy) (j := shave) (T := nlen + ndist);
      [clear - HCP; lia| clear - SH0 SH1 NL2 ND2; lia| clear - NL1 NL2 ND1 ND2; lia| intros KK| intros KK x11'].
    - (* [comment removed for export] *)
      zs.
      eapply (cl_chk_b RNG POST) with (j := shave); [clear - SH0 SH1 NL2 ND2; lia|].
      eapply (cl_fill (Z.to_nat copy) N (ICX u S D n 6341120 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
                (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf lf cf wf fo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cs ci H B shave copy rl);
        [exact HEAD| exact DONE| exact HN| exact CTX0| exact PAYR| exact PLEN| exact MODE| exact SI| exact ARR| exact VISf| exact HID| exact KA| exact BUF| exact HRL
        | clear; lia| clear - HCP; lia| clear; gcbn; lia| clear - KK; gcbn; lia| exact RLF| exact L15].
    - (* [comment removed for export] *)
      zrung [0x8e260].
      unfold bad_ofP, st_cl in SIB, MEB.
      cbn [t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in SIB, MEB.
      eapply (KD (IST BAD last flags ci cout H B out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SIB| exact MEB| exact ARR| change BAD with 16209; inf_vis_close| inf_hid_close].
    (* [U14B] A2 2026-11-12: v24 is a vestige binder at 1.4 (InfBBase's inf_locals no longer holds it), so eapply leaves
       it as a shelved word; any value does (G's U1A cure for v240) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
