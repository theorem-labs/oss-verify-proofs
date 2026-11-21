(* reloc-zl14c 05b1efb0e356fa4743192f59cee7f872 *)
(* [U14] inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base InfA_w6base U2AIface_fit2_draft InfA_itcall InfA_llpost.
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
  Variable rng_fs : alayout -> footprint -> Prop.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation VIS cx ly st lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m :=
    (inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m).
  Notation HIDm cx ly m := (inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m).
  Notation GARM2 cx ly Lb X := (garm2_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* [U14] 1.4 stores the codes pointer into distcode as well as lencode (0x8f018), so the
     state handed to inflate_table has dc = CDyn 0.  st_dc0 / sinv_dc0 carry sinv across that store (in LENLENS no
     clause of sinv reads dc beyond its range). *)
  Definition st_dc0 (st : ist) : ist :=
    IST (t_mode st) (t_last st) (t_flags st) (t_cin st) (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st)
        (t_length st) (t_offset st) (t_extra st) (t_lc st) (CDyn 0) (t_lb st) (t_db st)
        (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).

  Lemma sinv_dc0 : forall cx st lf cf, sinv cx st lf cf -> t_mode st = LENLENS -> sinv cx (st_dc0 st) lf cf.
  Proof.
    intros cx st lf cf (R & W & P & Mo) Hm.
    destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
    cbn in Hm. subst mode. unfold sinv, st_dc0.
    split; [| split; [exact W| split; [exact P|]]].
    - unfold IDefs.RNG in *. cbv zeta in *. cbn in *.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      repeat match goal with |- _ /\ _ => split end; try assumption; cbv [N_CODES]; lia.
    - unfold MODE in *. cbn in *. destruct Mo as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
      split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
      split; [intros C; exfalso; unfold codes_liveP in C; cbv [LEN_ LIT LENLENS] in C; lia|].
      split; [exact M6|]. split; [exact M7|]. split; [exact M8|]. split; [exact M9| exact M10].
  Qed.

  (* [U14] ll_call re-stated at its 1.4 pc 0x8efec, the join of the fill / no-fill paths.
     a0 = &distcode (S+128), a1 = &lencode (S+120), a3 = &next (S+160), t0 = codes (S+1384), t2 = lens (S+168) were
     loaded at 0x8f2a8 .. 0x8f2b8 (a0 / a1 again at 0x8f364 / 0x8f2f8 on the fill path).  s7 = (S+156)sh (the have
     shadow, set at 0x8eaf8), t4 = left (moved to s6 at 0x8f3b0), s10 = next_in.  Slot 496 is stale in LENLENS (it
     pulls bytes in s10), so vnext is free.  Then next := lencode := distcode := codes, lenbits := 7, and the CODES
     call 0x8f3e8 (ra = 0x8f3ec) -> ll_post. *)
  Lemma ll_call : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x1 x6 x12 x14 x15 x16 x17 x22 x28 x30 x31 : word) (m : amem),
    itcall_env AI rng_fs L RNG LB tp ly -> GARM2 cx ly 0x8f464 CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> t_shave st = 19 -> sinv cx st lf cf -> inf_arr_ok cx wf fo ->
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly (meas cx st) ->
    evtF asegs RNG POST
      (MS (mkR x1 (Z_to_bv 64 (l_SPA ly)) gp tp x28 x6 (Z_to_bv 64 (c_p cx + 168)) (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 (c_p cx + 128))
               (Z_to_bv 64 (c_p cx + 120)) x12 (Z_to_bv 64 (c_p cx + 160)) (Z_to_bv 64 (c_p cx + 136)) x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (c_n cx - t_cin st))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (l_F0 ly)) (Z_to_bv 64 (c_p cx + 1384)) x14 x30 x31)
          FR (Z_to_bv 64 0x8f344) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros ENV HCL CTX PAYR PLEN MODE SH19 SI ARR VIS HID KA.
    pose proof (ll_itc cx st lf cf wf SI MODE SH19 (proj1 ARR)) as ITC.
    pose proof (sinv_dc0 cx st lf cf SI MODE) as SI0.
    pose proof (proj1 SI0) as RNG0.
    (* [comment removed for export] *)
    destruct (ex_intro (fun r0 => r0 = resA CODES lf 0 19 0 7 cf wf) _ eq_refl) as [r ER].
    destruct (ll_bridge lf cf wf r ITC ER) as (BOK & BFS & RT & RW & RB & RX).
    inf_arm_open. subst shave.
    zrunb [0x95be4].
    replace (S + 1384) with (S + 1384 + 4 * 0) in SSC by lia.
    eapply (inf_itcall AI rng_fs L RNG stA LB LBc m0 payload POST (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
              (IST mode last flags cin cout hold bits out ret len offset extra (CDyn 0) (CDyn 0) 7 db ncode nlen ndist 19 0 whave wnext) lf cf wf fo fw)
      with (isd := false) (ty := InflateState.CODES) (lens_ofs := 0) (codes := 19) (bits := 7) (RA := 0x8f3bc) (r := r);
      [exact ENV| exact CTX0| inf_vis_close| inf_hid_close| exact PLEN| reflexivity| exact ITC| exact ER| reflexivity| lia| reflexivity| reflexivity
      | reflexivity| icx_cbn; f_equal; lia| reflexivity| reflexivity| reflexivity| reflexivity| ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' VIS' HID' RET.
    eapply (ll_post AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh (ICX u S D n 6336512 osz Wd cin0 cout0 W0 K0 zc) (ILAY SP SPA Zs F0 lo)
              (st_itab (IST mode last flags cin cout hold bits out ret len offset extra (CDyn 0) (CDyn 0) 7 db ncode nlen ndist 19 0 whave wnext) false (it_bits r) (it_table r))
              lf (arr_get (it_tbl r)) (arr_get (it_work r)) fo);
      [exact HCL| exact CTX0| exact PAYR| exact PLEN| exact MODE
      | exact (rng_ll_after _ _ lf cf (arr_get (it_tbl r)) (it_bits r) (it_table r) RNG0 RB RX RT)
      | split; [exact RW| exact (proj2 ARR)]| exact VIS'| exact HID'| exact KA| exact RET| | ].
    - intros E0. destruct (BOK E0) as (TOK & B15 & TX).
      pose proof (sinv_ll_ct _ _ lf cf (arr_get (it_tbl r)) (it_bits r) (it_table r) SI0 MODE ltac:(clear - B15; lia) ltac:(clear - B15; lia)
                    ltac:(clear - TX; lia) ltac:(clear - TX; lia) TOK RT) as (SI1 & ME1).
      split; [exact SI1| exact (Z.lt_le_incl _ _ ME1)].
    - intros NE. destruct (BFS NE) as (ET & EBt). rewrite ET, EBt.
      pose proof (sinv_ll_bad _ _ lf cf (arr_get (it_tbl r)) (it_ret r mod 18446744073709551616) SI0 MODE
                    ltac:(apply Z.mod_pos_bound; reflexivity) RT) as (SI1 & ME1).
      split; [exact SI1| exact ME1].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
