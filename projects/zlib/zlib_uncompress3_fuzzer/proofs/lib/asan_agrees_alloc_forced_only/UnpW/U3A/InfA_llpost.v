(* reloc-zl14c ed1caf05f723b59c1e2f005bcfb76e4f *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_type InfPure_w7 InfPure_table InfPure_itab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfA_w7base InfA_w6base.
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

  (* [U14] the 1.3.1 register homes of ll_post moved to 1.4 by tools/regmap_text_gr.py (ra>s6 t2>ra s4>s8 s5>s10 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s7 t3>t6 t4>t3 t5>t4 t6>t2) *)
  (* [U14] the 1.3.1 register homes of ll_post moved to 1.4 by tools/regmap_text_gr.py (ra>t2 t2>t6 s4>s10 s5>s9 s6>ra s7>s11 s8>s4 s9>s7 s10>s5 s11>s8 t3>t4 t4>t5 t5>s6 t6>t3) *)
  (* [U14] the 1.3.1 register homes of ll_post moved to 1.4 by tools/regmap_text_gr.py (ra>t2 t2>ra s4>s8 s5>s7 s6>t5 s7>s9 s8>s11 s9>s5 s10>s4 s11>s6 t4>s10 t5>t4) *)
  Lemma ll_post : forall (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo : Z -> Z)
      (v0 v8 v240 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (m : amem) (rv B : Z),
    GARM2 cx ly 0x8f464 CODELENS ->
    inf_ctx cx ly AI RNG LB -> Forall (fun c => 0 <= c < 256) payload -> Z.of_nat (length payload) = c_n cx ->
    t_mode st = LENLENS -> IDefs.RNG cx st lf cf -> inf_arr_ok cx wf fo ->
    (* [U14] an earlier development run, PROPOSED: slot 496 (vnext) is free.  LENLENS pulls input bytes in s10 and never stores slot 496
       (only DISP's value is there); both paths here store s10 into it (0x8ec58, 0x8f49c) before anything reads it. *)
    VIS cx ly st lf cf wf fo v0 v8 (Z_to_bv 64 (Z.shiftr (c_p cx + 108) 3)) v240 (Z_to_bv 64 (Z.shiftr (c_p cx + 56) 3)) vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad m ->
    HIDm cx ly m -> KALLB cx ly B ->
    (rv = 0 \/ rv = 1 \/ rv = -1) ->
    (rv = 0 -> sinv cx (st_llok st) lf cf /\ meas cx (st_llok st) <= B) ->
    (rv <> 0 -> sinv cx (bad_of (st_ret st (rv mod 18446744073709551616))) lf cf /\ meas cx (bad_of (st_ret st (rv mod 18446744073709551616))) < B) ->
    evtF asegs RNG POST
      (* [U14] right after inflate_table returns (0x8f06c): ra is the return pc, t2 is free, and 1.4 keeps
         next_in in s10 across the call (GARM2_MS needs it; probe PgCsLlpost) *)
      (MS (mkR (Z_to_bv 64 0x8f3bc) (Z_to_bv 64 (l_SPA ly)) gp tp x5 x6 x7 (Z_to_bv 64 (l_SP ly)) (Z_to_bv 64 (l_SPA ly)) (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_bits st)) (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 2147450880)
               x22 (Z_to_bv 64 (Z.shiftr (l_F0 ly) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (c_p cx + 156) 3 + 2147450880)) (Z_to_bv 64 (c_n cx - t_cin st))
               (Z_to_bv 64 (c_q cx + t_cin st)) (Z_to_bv 64 (l_F0 ly)) x31 x29 x30 x28)
          FR (Z_to_bv 64 0x8f3bc) fc None m (seg_rom asegs)).
      (* [U14] PROPOSED (for an earlier development run): t5 is free here.  inflate_table clobbers it (inf_itcall
         frees t5'), and both paths reload it before use (0x8f40c, 0x8f464).  With t5 pinned no caller could apply this. *)
  Proof.
    intros until B. intros HCL CTX PAYR PLEN MODE RN0 ARR VIS HID KA RET HOK HBAD.
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open_rn.
    destruct RET as [E|[E|E]]; subst rv.
    - (* [comment removed for export] *)
      destruct (HOK eq_refl) as (SI' & ME'). unfold st_llok in SI', ME'. icx_cbn.
      zrunb [0x8f464].
      eapply (HCL (IST CODELENS last flags cin cout hold bits out 0 len offset extra lc dc lb db ncode nlen ndist 0 nx whave wnext) lf cf wf fo);
        [exact CTX0| exact PAYR| exact PLEN| reflexivity| exact SI'| exact ARR| change CODELENS with 16198; inf_vis_close| inf_hid_close
        | eapply KALL_mono; [| split; [exact KD| split; [exact KB| split; [exact KL| exact KLV]]]]; exact ME'].
    - (* [comment removed for export] *)
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change (1 mod 18446744073709551616) with 1 in SI', ME'. unfold st_ret, bad_of in SI', ME'. icx_cbn.
      zrunb [0x91934].
      eapply (KB (IST mode last flags cin cout hold bits out 1 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| inf_vis_close| inf_hid_close].
    - (* [comment removed for export] *)
      destruct (HBAD ltac:(lia)) as (SI' & ME'). change ((-1) mod 18446744073709551616) with 18446744073709551615 in SI', ME'. unfold st_ret, bad_of in SI', ME'. icx_cbn.
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; reflexivity).
      zrunb [0x91934].
      eapply (KB (IST mode last flags cin cout hold bits out 18446744073709551615 len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) lf cf wf fo);
        [exact SI'| exact ME'| exact ARR| inf_vis_close| inf_hid_close].
    Unshelve. all: try exact (Z_to_bv 64 0).   (* [U14] an earlier development run: the v240 vestige binder *)
  Qed.
End S.
End CANSEC1.
