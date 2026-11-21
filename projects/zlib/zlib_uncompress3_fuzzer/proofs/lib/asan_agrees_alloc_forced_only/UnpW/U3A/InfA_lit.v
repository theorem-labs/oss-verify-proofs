(* reloc-zl14c 367058b1d1f3b36ea193f44aa9e29f9b *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfAGlue_p04.
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

  Theorem lit_arm : forall cx ly, arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh 0x8e828 LIT.
  Proof.
    intros cx ly. unfold arm_stmtA, ARM_MS. intros until m. intros CTX PAYR PLEN MODE SI ARR VIS HID KA.
    pose proof KA as (KD & KB & KL & KLV).
    inf_arm_open.
    destruct (pay_out_sep _ _ _ _ _ CTX0) as (cOD & COD0 & COD1 & COD2). cbn [c_q c_n] in COD1, COD2.
    clear R13.
    zs. zs. zs. zbr0 KLEFT.
    2: { (* [comment removed for export] *)
      zrunb [0x928f8].
      eapply (KLV (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) ret lf cf wf fo);
        [exact SI| exact ARR| (unfold inf_vis, inf_locals, strm_cells, istate_cells, itail_cells; cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext l_SP l_SPA l_Zs l_F0 l_lo];
                               replace (osz - cout) with 0 by lia; do 10 (split; [eassumption|]); split; [eassumption|]; inf_mode_ne)| inf_hid_close]. }
    zrunb [0x8e864].
    (* [comment removed for export] *)
    assert (SOK : store_ok asegs m (Z_to_bv 64 (6336512 + cout)) 1 = true)
      by (eapply (f8arr_store_ok asegs m 6336512 (Z.to_nat osz) fo cout); [exact OUT| lia| reflexivity]).
    zstep.
    destruct (out_write asegs m 6336512 (Z.to_nat osz) fo cout (le1 (sx32 (Z_to_bv 64 len))) OUT ltac:(lia) (length_le1 _)) as (fo' & OUT' & FOR').
    store_done.
    zrunb [0x8e2ec].
    destruct (sinv_upd _ _ _ _ LEN 1 len SI (or_intror MODE) ltac:(lia) ltac:(icx_cbn; lia) ltac:(lia) ltac:(icx_cbn; lia) (or_intror eq_refl)) as (SI' & ME').
    replace (6336512 + cout + 1) with (6336512 + (cout + 1)) in * by lia. replace (osz - cout + -1) with (osz - (cout + 1)) in * by lia.
    eapply (KD (st_upd (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) LEN 1 len) lf cf wf fo');
      [exact SI'| exact ME'| destruct ARR as [AW _]; split; [exact AW| intros i _; apply FOR']| change LEN with 16200; unfold st_upd; inf_vis_close| inf_hid_close].
    (* [U14] v240 is a vestige binder of KDISP at 1.4 (InfABase's inf_locals no longer holds it), so
       eapply leaves it as a shelved word; any value does *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.
End S.
End CANSEC1.
