(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 755 of its 803 lines of code are new or changed and 963 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F4.v 2d4003b98bbc (the blob this tree had at release c5e779efe8c) (seg_F4_d64, F4.v:3246-3611).
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   There is NO constr_eq pin of a run against F4.v, because F4.v states NO run lemma for the entry cut 0x81dfc: its
   three runs are the evt argument of Tac_slot.sl_run inside the one Hat proof seg_F4_d64 (the short arm at
   F4.v:3318-3336, the byte-12 = 136 arm at :3395-3467, the byte-12 <> 136 arm at :3536-3575), so there is no
   F4.<r> constant to pin against (the case of Seg/F27F.v and Seg/F10F.v). In place of that pin (rule of
   a Theorem Labs lane, 04:23Z) seg_F4_d64_of_F re-proves F4.seg_F4_d64's statement by F4.v's own script with each run bullet
   replaced by this file's corollary, and seg_F4_d64_of_F_verbatim checks by constr_eq that its type is the type of
   F4.seg_F4_d64 over the same Section variables. Each extracted run is also pinned against its own corollary
   (<r>_of_F_is_extracted, for the two arms whose premises bound every address).
   Mechanical re-cut and re-run (a Theorem Labs lane, 04:26Z); input to the ported walk only. *)

(* The three runs of seg_F4_d64 (F4.v:3248), from the entry cut 0x81dfc, in three forms.
   (1) f4_d64_short_run / f4_d64_136_run / f4_d64_n136_run: the evt fact seg_F4_d64's script hands to sl_run for
       that arm (the UL engine's Exec.evt, the premise of Tac_slot.sl_run), from the same start state
       `MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)` to the same post K,
       proved by the arm's run bullet of F4.v verbatim, in F4.v's own environment (F4.v:3139-3141: the UL Tac and
       Bytes imported, then YK11).
   (2) <r>_F: the same run re-stepped with lib.Lib StepF as an ExecF.evtF under a universally quantified footprint
       RNG, one ExecF.rng premise per region the run reads or writes (F4d64F.rng.tsv), by the same script.
   (3) <r>_of_F: the statement of (1) re-derived from (2) at ExecF.RNG_all. On the two long arms the run's own
       premises bound every address it touches (0 <= A1 < 2 ^ 64, A1 + 248 / A1 + 208 <= 2 ^ 64, 0 <= phi,
       phi + L <= A1, the bytes_at bounds of the shadow and record bytes), so the corollary is the extracted
       statement itself. The short arm carries only `rg regs 9 A1` and the store_ok fact, which bound nothing, so
       its corollary is f4_d64_short_run_of_F_bounded (the statement plus `0 <= A1 + 200` and
       `A1 + 200 + 8 <= 2 ^ 64`) and f4_d64_short_run_of_F_bounded_shape shows that this is all it adds.
   (4) seg_F4_d64_of_F: F4.seg_F4_d64 from (3), see the Section S below; seg_F4_d64_of_F_verbatim is its pin.
   Abstraction map (ghost term of the script -> plain variable): t_k (g_in g) j -> k ; flen g j -> L ; Asp (the
     spill base, F4.v:3276) -> A1 ; nth 12 / nth 13 (t_g (g_in g) j) cp_z -> b12 / b13 ; cp_v (t_g (g_in g) j) 12 /
     13 (by delta bv_unsigned of those bytes) -> bv_unsigned b12 / bv_unsigned b13 ; b2z (t_8819 (g_in g) j) -> e.
     The carried facts the bullets read are the premises, under the script's names: Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 (the
     register slots, in f4_subst_slot form), HAspR, Hflen0, Hshort / Hlong, Hv12r Hv13r, Hsa12 Hsa13,
     H12eq / H12ne, H8819, HS200, HSTK, Hsh12 Hsh13, Hb12 Hb13. The script's lia calls draw on Hphitop
     (phi + AC.a_size (flen g j) <= Asp), Hasz (flen g j <= AC.a_size (flen g j)), Hp4096 (4096 <= phi) and FRA's
     frame bounds (A + 416 <= g_S g < APPMEM_END); they enter as the consequences the bullets use:
     `phi + L <= A1`, `0 <= phi`, `A1 + 248 <= 2 ^ 64` (136 arm) / `A1 + 208 <= 2 ^ 64` (n136 arm).
   Name changes (same term after delta, no new reasoning): f4_subst_slot is F4.v:211's Section-local Ltac (same
     body); in (2) f4F_mkR_of_expand is F4.f4_mkR_of_expandu over lib.Lib's mkR (the register map StepF reads),
     f4F_zxb_equ is F4.f4_zxb_equ over lib.Lib's zxb and f4F_seqzu is F4.f4_seqzu over lib.Lib's
     PropExec.v_sltiu (the ones StepF's lbu / seqz put in the goal); f4d64F_ul_of_lib is Seg/F10F.v's
     f10F_ul_of_lib. Everything else in (2) is the script of (1). In (4) the five F4.v lemmas that take Section
     variables (f4_law_blocks, f4_spill_stk, f4_fra_spill, f4_keep1, f4_pf_sp) are Local Abbreviations of the same
    constants applied to this file's Section S variables; and its four `cbn [inside]` (F4.v's text) are written
    `cbn [LFr.inside]`, the constant `About inside` names in this file's context (lib.Lib.Frame.inside), because
    `inside` is also defined in lib/Reusable/YO0f.v and lib/A/Reusable/YO0f.v, both in the closure (ctrlgate
    dcb362e1c42f DUP finding, 07:05Z). F4.v itself is unchanged apart from comment text. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F4.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module ULE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.
Module ULMemF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module ULFrF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.

(* F4.v:211 f4_subst_slot (a Section-local Ltac there, so not exported): the same body. *)
Ltac f4_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Section RunUL.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.
(* F4.v:3139-3141: the UL engine, imported for this Section as F4.v imports it for the rest of its Section S. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Tac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Bytes.
Import YK11.
Open Scope Z_scope.

(* ---- (1) The short arm (F4.v:3317-3336, len <= 49): `bgeu a0,s2` taken, exit 0x81e88. ---- *)
Lemma f4_d64_short_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 : Z),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L ->
  0 <= L -> L <= 49 ->
  store_ok rsegs mem (wa (A1 + 200)) 8 = true ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81e88 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem mem (wa (A1 + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 Ha0 Hs9 Hr9 Hs2 Hflen0 Hshort HS200.
  rewrite f4_mkR_of_expandu.
  f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
  (* 0x81dfc mv s8,a0 ; 0x81e00 li a0,49 ; 0x81e04 sd s9,200(s1) ; 0x81e08 bgeu a0,s2 : taken *)
  step. step. step. step.
  rewrite (rc_ltu_lit64 49 L) by lia.
  replace (49 <? L) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [negb]. cbv iota.
  finish.
  all: simp_regs; try reflexivity.
Qed.

(* ---- (1) The byte-12 = 136 arm (F4.v:3390-3467): the instrumented checks of phi+12 and phi+13, the spill
   [s1+240] and the jump to 0x81ea8. ---- *)
Lemma f4_d64_136_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 e : Z) (b12 b13 : byte),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L -> rg regs 23 phi -> rg regs 26 ASAN_K ->
  0 <= A1 < 2 ^ 64 -> A1 + 248 <= 2 ^ 64 -> 0 <= phi -> phi + L <= A1 -> L > 49 ->
  0 <= bv_unsigned b12 < 256 -> 0 <= bv_unsigned b13 < 256 ->
  Z.shiftr (phi + 12) 3 + ASAN_K + 1 <= A1 + 200 -> Z.shiftr (phi + 13) 3 + ASAN_K + 1 <= A1 + 200 ->
  bv_unsigned b12 = 136 -> e = (if bv_unsigned b13 =? 25 then 1 else 0) ->
  store_ok rsegs mem (wa (A1 + 200)) 8 = true -> stk rsegs mem (A1 + 200) (A1 + 248) ->
  bytes_at rsegs mem (Z.shiftr (phi + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (Z.shiftr (phi + 13) 3 + ASAN_K) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (phi + 12) [b12] -> bytes_at rsegs mem (phi + 13) [b13] ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81ea8 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
        getr R 25 = getr regs 25 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem (write_to_mem mem (wa (A1 + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                 (wa (A1 + 240)) (le8 (Z_to_bv 64 e))))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 e b12 b13 Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 HAspR HA248 Hphi0 Hphitop Hlong Hv12r Hv13r
    Hsa12 Hsa13 H12eq H8819 HS200 HSTK Hsh12 Hsh13 Hb12 Hb13.
  rewrite f4_mkR_of_expandu.
  f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
  f4_subst_slot Hs7. f4_subst_slot Hr26.
  (* 0x81dfc mv s8,a0 ; 0x81e00 li a0,49 ; 0x81e04 sd s9,200(s1) ; 0x81e08 bgeu a0,s2 : not taken *)
  step. step. step. step.
  rewrite (rc_ltu_lit64 49 L) by lia.
  replace (49 <? L) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  lazymatch goal with
  | |- _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RD12s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 12) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hsh12 | left; lia ]);
    assert (RD13s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 13) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hsh13 | left; lia ]);
    assert (RD12 : ov_read_bytes rsegs mm (wa (phi + 12)) 1
                     = Some [b12])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hb12 | left; lia ]);
    assert (RD13 : ov_read_bytes rsegs mm (wa (phi + 13)) 1
                     = Some [b13])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hb13 | left; lia ]);
    assert (HS240 : store_ok rsegs mm (wa (A1 + 240)) 8 = true)
      by (apply (f4_store_ok_stku mem mm (A1 + 200) (A1 + 248) (A1 + 240) 8%nat HSTK);
            [ apply wmono_write; apply wmono_refl | lia | lia | lia | lia ])
  end.
  (* 0x81e0c addi a0,s7,12 ; 0x81e10 srli a1,a0,3 ; 0x81e14 add a1,a1,s10 *)
  step. rewrite ?(MState.unsigned_lit phi) by lia.
  step. step. rewrite ?(MState.unsigned_lit (phi + 12)) by lia.
  (* 0x81e18 lb a1,0(a1) : the shadow byte is 0 ; 0x81e1c bnez a1 : not taken *)
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. if_false.
  (* 0x81e20 lbu a0,0(a0) ; 0x81e24 li a1,136 ; 0x81e28 bne a0,a1 : not taken *)
  step. step. step.
  rewrite (f4_zxb_equ b12 (bv_unsigned b12)) by reflexivity.
  rewrite (f4_eqb_lit (bv_unsigned b12) 136) by lia.
  replace (bv_unsigned b12 =? 136) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
  cbn [negb]. cbv iota.
  (* 0x81e2c addi a0,s7,13 ; 0x81e30 srli a1,a0,3 ; 0x81e34 add a1,a1,s10 *)
  step. rewrite ?(MState.unsigned_lit phi) by lia.
  step. step. rewrite ?(MState.unsigned_lit (phi + 13)) by lia.
  (* 0x81e38 lb a1,0(a1) : the shadow byte is 0 ; 0x81e3c bnez a1 : not taken *)
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. if_false.
  (* 0x81e40 lbu a0,0(a0) ; 0x81e44 addi a0,a0,-25 ; 0x81e48 seqz a0,a0 *)
  step.
  rewrite (f4_zxb_equ b13 (bv_unsigned b13)) by reflexivity.
  step. rewrite ?(MState.unsigned_lit (bv_unsigned b13)) by lia.
  step. rewrite f4_seqzu.
  rewrite ?(MState.unsigned_lit_wrap (bv_unsigned b13 - 25)).
  (* 0x81e4c sd a0,240(s1) ; 0x81e50 j 81e10 *)
  step. step.
  finish.
  all: simp_regs; try reflexivity.
  rewrite H8819. do 3 f_equal.
  rewrite <- (f4_sub25 (bv_unsigned b13)) by lia.
  rewrite MState.unsigned_lit_wrap. reflexivity.
Qed.

(* ---- (1) The byte-12 <> 136 arm (F4.v:3531-3575): `bne a0,a1` taken, exit 0x81ea4. ---- *)
Lemma f4_d64_n136_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 : Z) (b12 : byte),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L -> rg regs 23 phi -> rg regs 26 ASAN_K ->
  0 <= A1 < 2 ^ 64 -> A1 + 208 <= 2 ^ 64 -> 0 <= phi -> phi + L <= A1 -> L > 49 ->
  0 <= bv_unsigned b12 < 256 ->
  Z.shiftr (phi + 12) 3 + ASAN_K + 1 <= A1 + 200 ->
  bv_unsigned b12 <> 136 ->
  store_ok rsegs mem (wa (A1 + 200)) 8 = true ->
  bytes_at rsegs mem (Z.shiftr (phi + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (phi + 12) [b12] ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81ea4 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
        getr R 25 = getr regs 25 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem mem (wa (A1 + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 b12 Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 HAspR HA208 Hphi0 Hphitop Hlong Hv12r
    Hsa12 H12ne HS200 Hsh12 Hb12.
  rewrite f4_mkR_of_expandu.
  f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
  f4_subst_slot Hs7. f4_subst_slot Hr26.
  step. step. step. step.
  rewrite (rc_ltu_lit64 49 L) by lia.
  replace (49 <? L) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  lazymatch goal with
  | |- _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RD12s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 12) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hsh12 | left; lia ]);
    assert (RD12 : ov_read_bytes rsegs mm (wa (phi + 12)) 1
                     = Some [b12])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hb12 | left; lia ])
  end.
  step. rewrite ?(MState.unsigned_lit phi) by lia.
  step. step. rewrite ?(MState.unsigned_lit (phi + 12)) by lia.
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. if_false.
  step. step. step.
  rewrite (f4_zxb_equ b12 (bv_unsigned b12)) by reflexivity.
  rewrite (f4_eqb_lit (bv_unsigned b12) 136) by lia.
  replace (bv_unsigned b12 =? 136) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
  cbn [negb]. cbv iota.
  finish.
  all: simp_regs; try reflexivity.
Qed.

End RunUL.

Section RunF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow the evt engines'. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Import YK11.
Open Scope Z_scope.

(* F4.f4_mkR_of_expandu over lib.Lib's mkR (the register map StepF's simp_regs reads). *)
Lemma f4F_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* F4.f4_zxb_equ over lib.Lib's zxb (the one StepF's lbu puts in the goal). *)
Lemma f4F_zxb_equ : forall (b : byte) x, x = bv_unsigned b -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.zxb b = Z_to_bv 64 x.
Proof. exact f4_zxb_equ. Qed.

(* F4.f4_seqzu over lib.Lib's PropExec.v_sltiu (the one StepF's seqz puts in the goal). *)
Lemma f4F_seqzu : forall w : word, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.v_sltiu w 1 = Z_to_bv 64 (if bv_unsigned w =? 0 then 1 else 0).
Proof. exact f4_seqzu. Qed.

(* ---- (2) The short arm: writes the spill [A1+200, A1+208). ---- *)
Lemma f4_d64_short_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 : Z) (RNG : ExecF.footprint),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L ->
  0 <= L -> L <= 49 ->
  store_ok rsegs mem (ULMemF.wa (A1 + 200)) 8 = true ->
  ExecF.rng RNG (A1 + 200) 8 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81e88 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem mem (ULMemF.wa (A1 + 200)) (ULMemF.le8 (Z_to_bv 64 (phi + 18)))))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 RNG Ha0 Hs9 Hr9 Hs2 Hflen0 Hshort HS200 R200.
  rewrite f4F_mkR_of_expand.
  f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
  (* 0x81dfc mv s8,a0 ; 0x81e00 li a0,49 ; 0x81e04 sd s9,200(s1) ; 0x81e08 bgeu a0,s2 : taken *)
  step. step. step. step.
  rewrite (rc_ltu_lit64 49 L) by lia.
  replace (49 <? L) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [negb]. cbv iota.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.finish.
  all: OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.simp_regs; try reflexivity.
Qed.

(* ---- (2) The 136 arm: writes the spills [A1+200, +8) and [A1+240, +8); reads the shadow bytes of phi+12 and
   phi+13 (both 0: the slow paths 0x82a2c / 0x82a98 and the error calls are not reached) and the record bytes
   phi+12 and phi+13. ---- *)
Lemma f4_d64_136_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 e : Z) (b12 b13 : byte) (RNG : ExecF.footprint),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L -> rg regs 23 phi -> rg regs 26 ASAN_K ->
  0 <= A1 < 2 ^ 64 -> A1 + 248 <= 2 ^ 64 -> 0 <= phi -> phi + L <= A1 -> L > 49 ->
  0 <= bv_unsigned b12 < 256 -> 0 <= bv_unsigned b13 < 256 ->
  Z.shiftr (phi + 12) 3 + ASAN_K + 1 <= A1 + 200 -> Z.shiftr (phi + 13) 3 + ASAN_K + 1 <= A1 + 200 ->
  bv_unsigned b12 = 136 -> e = (if bv_unsigned b13 =? 25 then 1 else 0) ->
  store_ok rsegs mem (ULMemF.wa (A1 + 200)) 8 = true -> ULFrF.stk rsegs mem (A1 + 200) (A1 + 248) ->
  ULMemF.bytes_at rsegs mem (Z.shiftr (phi + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
  ULMemF.bytes_at rsegs mem (Z.shiftr (phi + 13) 3 + ASAN_K) [Z_to_bv 8 0] ->
  ULMemF.bytes_at rsegs mem (phi + 12) [b12] -> ULMemF.bytes_at rsegs mem (phi + 13) [b13] ->
  ExecF.rng RNG (A1 + 200) 8 -> ExecF.rng RNG (A1 + 240) 8 ->
  ExecF.rng RNG (Z.shiftr (phi + 12) 3 + ASAN_K) 1 -> ExecF.rng RNG (phi + 12) 1 ->
  ExecF.rng RNG (Z.shiftr (phi + 13) 3 + ASAN_K) 1 -> ExecF.rng RNG (phi + 13) 1 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81ea8 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
        getr R 25 = getr regs 25 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem (write_to_mem mem (ULMemF.wa (A1 + 200)) (ULMemF.le8 (Z_to_bv 64 (phi + 18))))
                 (ULMemF.wa (A1 + 240)) (ULMemF.le8 (Z_to_bv 64 e))))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 e b12 b13 RNG Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 HAspR HA248 Hphi0 Hphitop Hlong Hv12r Hv13r
    Hsa12 Hsa13 H12eq H8819 HS200 HSTK Hsh12 Hsh13 Hb12 Hb13 R200 R240 Rsh12 R12 Rsh13 R13.
  rewrite f4F_mkR_of_expand.
  f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
  f4_subst_slot Hs7. f4_subst_slot Hr26.
  (* 0x81dfc mv s8,a0 ; 0x81e00 li a0,49 ; 0x81e04 sd s9,200(s1) ; 0x81e08 bgeu a0,s2 : not taken *)
  step. step. step. step.
  rewrite (rc_ltu_lit64 49 L) by lia.
  replace (49 <? L) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  lazymatch goal with
  | |- _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RD12s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 12) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hsh12 | left; lia ]);
    assert (RD13s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 13) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hsh13 | left; lia ]);
    assert (RD12 : ov_read_bytes rsegs mm (wa (phi + 12)) 1
                     = Some [b12])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hb12 | left; lia ]);
    assert (RD13 : ov_read_bytes rsegs mm (wa (phi + 13)) 1
                     = Some [b13])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hb13 | left; lia ]);
    assert (HS240 : store_ok rsegs mm (wa (A1 + 240)) 8 = true)
      by (apply (f4_store_ok_stku mem mm (A1 + 200) (A1 + 248) (A1 + 240) 8%nat HSTK);
            [ apply wmono_write; apply wmono_refl | lia | lia | lia | lia ])
  end.
  (* 0x81e0c addi a0,s7,12 ; 0x81e10 srli a1,a0,3 ; 0x81e14 add a1,a1,s10 *)
  step. rewrite ?(MState.unsigned_lit phi) by lia.
  step. step. rewrite ?(MState.unsigned_lit (phi + 12)) by lia.
  (* 0x81e18 lb a1,0(a1) : the shadow byte is 0 ; 0x81e1c bnez a1 : not taken *)
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.if_false.
  (* 0x81e20 lbu a0,0(a0) ; 0x81e24 li a1,136 ; 0x81e28 bne a0,a1 : not taken *)
  step. step. step.
  rewrite (f4F_zxb_equ b12 (bv_unsigned b12)) by reflexivity.
  rewrite (f4_eqb_lit (bv_unsigned b12) 136) by lia.
  replace (bv_unsigned b12 =? 136) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
  cbn [negb]. cbv iota.
  (* 0x81e2c addi a0,s7,13 ; 0x81e30 srli a1,a0,3 ; 0x81e34 add a1,a1,s10 *)
  step. rewrite ?(MState.unsigned_lit phi) by lia.
  step. step. rewrite ?(MState.unsigned_lit (phi + 13)) by lia.
  (* 0x81e38 lb a1,0(a1) : the shadow byte is 0 ; 0x81e3c bnez a1 : not taken *)
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.if_false.
  (* 0x81e40 lbu a0,0(a0) ; 0x81e44 addi a0,a0,-25 ; 0x81e48 seqz a0,a0 *)
  step.
  rewrite (f4F_zxb_equ b13 (bv_unsigned b13)) by reflexivity.
  step. rewrite ?(MState.unsigned_lit (bv_unsigned b13)) by lia.
  step. rewrite f4F_seqzu.
  rewrite ?(MState.unsigned_lit_wrap (bv_unsigned b13 - 25)).
  (* 0x81e4c sd a0,240(s1) ; 0x81e50 j 81e10 *)
  step. step.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.finish.
  all: OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.simp_regs; try reflexivity.
  rewrite H8819. do 3 f_equal.
  rewrite <- (f4_sub25 (bv_unsigned b13)) by lia.
  rewrite MState.unsigned_lit_wrap. reflexivity.
Qed.

(* ---- (2) The n136 arm: writes the spill [A1+200, +8); reads the shadow byte of phi+12 and the record byte
   phi+12. ---- *)
Lemma f4_d64_n136_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 : Z) (b12 : byte) (RNG : ExecF.footprint),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L -> rg regs 23 phi -> rg regs 26 ASAN_K ->
  0 <= A1 < 2 ^ 64 -> A1 + 208 <= 2 ^ 64 -> 0 <= phi -> phi + L <= A1 -> L > 49 ->
  0 <= bv_unsigned b12 < 256 ->
  Z.shiftr (phi + 12) 3 + ASAN_K + 1 <= A1 + 200 ->
  bv_unsigned b12 <> 136 ->
  store_ok rsegs mem (ULMemF.wa (A1 + 200)) 8 = true ->
  ULMemF.bytes_at rsegs mem (Z.shiftr (phi + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
  ULMemF.bytes_at rsegs mem (phi + 12) [b12] ->
  ExecF.rng RNG (A1 + 200) 8 ->
  ExecF.rng RNG (Z.shiftr (phi + 12) 3 + ASAN_K) 1 -> ExecF.rng RNG (phi + 12) 1 ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81ea4 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
        getr R 25 = getr regs 25 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem mem (ULMemF.wa (A1 + 200)) (ULMemF.le8 (Z_to_bv 64 (phi + 18)))))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 b12 RNG Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 HAspR HA208 Hphi0 Hphitop Hlong Hv12r
    Hsa12 H12ne HS200 Hsh12 Hb12 R200 Rsh12 R12.
  rewrite f4F_mkR_of_expand.
  f4_subst_slot Ha0. f4_subst_slot Hs9. f4_subst_slot Hr9. f4_subst_slot Hs2.
  f4_subst_slot Hs7. f4_subst_slot Hr26.
  step. step. step. step.
  rewrite (rc_ltu_lit64 49 L) by lia.
  replace (49 <? L) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  lazymatch goal with
  | |- _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RD12s : ov_read_bytes rsegs mm (wa (Z.shiftr (phi + 12) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hsh12 | left; lia ]);
    assert (RD12 : ov_read_bytes rsegs mm (wa (phi + 12)) 1
                     = Some [b12])
      by (apply f4_rd1u; apply (f4_ba_keep1u mem _ _ _ _ 8);
            [ rewrite length_le8; reflexivity | lia | lia | exact Hb12 | left; lia ])
  end.
  step. rewrite ?(MState.unsigned_lit phi) by lia.
  step. step. rewrite ?(MState.unsigned_lit (phi + 12)) by lia.
  step.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  step. OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.if_false.
  step. step. step.
  rewrite (f4F_zxb_equ b12 (bv_unsigned b12)) by reflexivity.
  rewrite (f4_eqb_lit (bv_unsigned b12) 136) by lia.
  replace (bv_unsigned b12 =? 136) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
  cbn [negb]. cbv iota.
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.finish.
  all: OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.simp_regs; try reflexivity.
Qed.

End RunF.

Section RunOf.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.
(* The extracted statements' environment again (F4.v:3139-3141), so each corollary reads as its extracted run. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Tac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Bytes.
Import YK11.
Open Scope Z_scope.

(* Seg/F10F.v's f10F_ul_of_lib: the UL engine's evt from the lib.Lib one (both are msteps of
   `ms_svc_pending ms = None /\ step = MachineOk ms'`); the same statement and proof. *)
Lemma f4d64F_ul_of_lib : forall Q ms, LE.evt rsegs Q ms -> ULE.evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [clear HQ|exact HQ].
  induction H as [s|s s1 s2 Hs _ IH]; [apply ULE.msteps_refl|].
  eapply ULE.msteps_cons; [exact Hs | exact IH].
Qed.

(* ---- (3) The corollaries at ExecF.RNG_all. ---- *)
Lemma f4_d64_short_run_of_F_bounded : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 : Z),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L ->
  0 <= L -> L <= 49 ->
  store_ok rsegs mem (wa (A1 + 200)) 8 = true ->
  0 <= A1 + 200 -> A1 + 200 + 8 <= 2 ^ 64 ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81e88 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem mem (wa (A1 + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 Ha0 Hs9 Hr9 Hs2 Hflen0 Hshort HS200 B0 B1.
  apply f4d64F_ul_of_lib, (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f4_d64_short_run_F regs mem k phi L A1 ExecF.RNG_all); try assumption.
  apply ExecF.rng_all; lia.
Qed.

Lemma f4_d64_136_run_of_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 e : Z) (b12 b13 : byte),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L -> rg regs 23 phi -> rg regs 26 ASAN_K ->
  0 <= A1 < 2 ^ 64 -> A1 + 248 <= 2 ^ 64 -> 0 <= phi -> phi + L <= A1 -> L > 49 ->
  0 <= bv_unsigned b12 < 256 -> 0 <= bv_unsigned b13 < 256 ->
  Z.shiftr (phi + 12) 3 + ASAN_K + 1 <= A1 + 200 -> Z.shiftr (phi + 13) 3 + ASAN_K + 1 <= A1 + 200 ->
  bv_unsigned b12 = 136 -> e = (if bv_unsigned b13 =? 25 then 1 else 0) ->
  store_ok rsegs mem (wa (A1 + 200)) 8 = true -> stk rsegs mem (A1 + 200) (A1 + 248) ->
  bytes_at rsegs mem (Z.shiftr (phi + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (Z.shiftr (phi + 13) 3 + ASAN_K) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (phi + 12) [b12] -> bytes_at rsegs mem (phi + 13) [b13] ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81ea8 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
        getr R 25 = getr regs 25 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem (write_to_mem mem (wa (A1 + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                 (wa (A1 + 240)) (le8 (Z_to_bv 64 e))))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 e b12 b13 Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 HAspR HA248 Hphi0 Hphitop Hlong Hv12r Hv13r
    Hsa12 Hsa13 H12eq H8819 HS200 HSTK Hsh12 Hsh13 Hb12 Hb13.
  pose proof Hsh12 as (B0 & B1 & _). pose proof Hsh13 as (B2 & B3 & _).
  pose proof Hb12 as (B4 & B5 & _). pose proof Hb13 as (B6 & B7 & _).
  cbn [length] in B1, B3, B5, B7.
  apply f4d64F_ul_of_lib, (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f4_d64_136_run_F regs mem k phi L A1 e b12 b13 ExecF.RNG_all); try assumption;
    apply ExecF.rng_all; lia.
Qed.

Lemma f4_d64_n136_run_of_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 : Z) (b12 : byte),
  rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L -> rg regs 23 phi -> rg regs 26 ASAN_K ->
  0 <= A1 < 2 ^ 64 -> A1 + 208 <= 2 ^ 64 -> 0 <= phi -> phi + L <= A1 -> L > 49 ->
  0 <= bv_unsigned b12 < 256 ->
  Z.shiftr (phi + 12) 3 + ASAN_K + 1 <= A1 + 200 ->
  bv_unsigned b12 <> 136 ->
  store_ok rsegs mem (wa (A1 + 200)) 8 = true ->
  bytes_at rsegs mem (Z.shiftr (phi + 12) 3 + ASAN_K) [Z_to_bv 8 0] ->
  bytes_at rsegs mem (phi + 12) [b12] ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81ea4 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
        getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
        getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
        getr R 25 = getr regs 25 /\
        getr R 24 = Z_to_bv 64 k /\
        mem' = write_to_mem mem (wa (A1 + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros regs mem k phi L A1 b12 Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 HAspR HA208 Hphi0 Hphitop Hlong Hv12r
    Hsa12 H12ne HS200 Hsh12 Hb12.
  pose proof Hsh12 as (B0 & B1 & _). pose proof Hb12 as (B4 & B5 & _).
  cbn [length] in B1, B5.
  apply f4d64F_ul_of_lib, (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f4_d64_n136_run_F regs mem k phi L A1 b12 ExecF.RNG_all); try assumption;
    apply ExecF.rng_all; lia.
Qed.

(* The shape check: the bounded corollary is the extracted short run plus its two bound premises, and nothing
   else -- from the extracted statement the bounded one follows by dropping them. *)
Lemma f4_d64_short_run_of_F_bounded_shape :
  (forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 : Z),
   rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L ->
   0 <= L -> L <= 49 ->
   store_ok rsegs mem (wa (A1 + 200)) 8 = true ->
   evt rsegs
     (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
        (pc' = Z_to_bv 64 0x81e88 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
         getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\
         getr R 24 = Z_to_bv 64 k /\
         mem' = write_to_mem mem (wa (A1 + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
     (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs))) ->
  (forall (regs : bvmap 5 word) (mem : word -> option byte) (k phi L A1 : Z),
   rg regs 10 k -> rg regs 25 (phi + 18) -> rg regs 9 A1 -> rg regs 18 L ->
   0 <= L -> L <= 49 ->
   store_ok rsegs mem (wa (A1 + 200)) 8 = true ->
   0 <= A1 + 200 -> A1 + 200 + 8 <= 2 ^ 64 ->
   evt rsegs
     (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
        (pc' = Z_to_bv 64 0x81e88 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
         getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\
         getr R 24 = Z_to_bv 64 k /\
         mem' = write_to_mem mem (wa (A1 + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
     (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81dfc) fp_csr None mem (seg_rom rsegs))).
Proof.
  intros H. intros. eapply H; eassumption.
Qed.

End RunOf.

(* The two plain corollaries are the extracted statements themselves: their types are syntactically the types of
   f4_d64_136_run / f4_d64_n136_run (the runs extracted from seg_F4_d64 above). *)
Example f4_d64_136_run_of_F_is_extracted : True.
Proof.
  let A := type of @f4_d64_136_run_of_F in let B := type of @f4_d64_136_run in constr_eq A B; exact I.
Qed.
Example f4_d64_n136_run_of_F_is_extracted : True.
Proof.
  let A := type of @f4_d64_n136_run_of_F in let B := type of @f4_d64_n136_run in constr_eq A B; exact I.
Qed.

(* ---- (4) F4.seg_F4_d64 re-proved from the corollaries (rule of a Theorem Labs lane, 04:23Z: no run pin is possible, so
   the segment's own cut lemma is derived from them). The Section has F4.v Section S's declarations (F4.v:58-66)
   verbatim, and F4.v:3139-3141's imports. seg_F4_d64_of_F has F4.seg_F4_d64's statement, and its proof is F4.v's
   own script (F4.v:3253-3611) with each sl_run run bullet (F4.v:3328-3336, 3407-3467, 3547-3575) replaced by an
   `exact` of the corollary above; every other line is F4.v's. F4.v's Section-local names that take Section
   variables are the same constants applied to this Section's variables (the five Local Abbreviations below). ---- *)
Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract (lib/A/Prog/reac_ctrl_parse_c.v), a Section Hypothesis. *)
Hypothesis HPARSE : reac_ctrl_parse_contract.

Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Tac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Bytes.
Import YK11.
Open Scope Z_scope.

Local Abbreviation f4_law_blocks := (@F4.f4_law_blocks rc APIf).
Local Abbreviation f4_spill_stk := (@F4.f4_spill_stk rc B APIf SH SK ra).
Local Abbreviation f4_fra_spill := (@F4.f4_fra_spill fx LS rc B APIf SH SK ra empty FF).
Local Abbreviation f4_keep1 := (@F4.f4_keep1 rc B APIf SH SK ra).
Local Abbreviation f4_pf_sp := (@F4.f4_pf_sp rc B APIf SH SK ra).

Lemma seg_F4_d64_of_F : forall j,
  Hat B APIf ra (Inv_A81e88_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81ea4_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81ea8_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81dfc_at B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j Hdf0 He0c He10 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & _ & Ha0 & Hs9 & Hs6 & Hu32 & HID & HPF)).
  subst c. rewrite SEGS.
  pose proof HC as HC0.
  destruct HC0 as (Hs7 & Hs2 & (A & H9 & HA & _) & HPH & _ & _ & _).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshq & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = Asp).
  { apply f4_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A.
  pose proof HHB as (Hphinz & HAd).
  pose proof HAd as (Had0 & Had1 & Had2 & _).
  assert (HIn : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  destruct (f4_law_blocks _ mem md phi (AC.a_size (flen g j)) HAH HIn) as (Hp16 & Hp4096 & Hpstk & _).
  pose proof (f4_flen_nn g j) as Hflen0.
  assert (Hasz : flen g j <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hphitop : phi + AC.a_size (flen g j) <= Asp) by lia.
  (* the two spill cells are byte-backed: they lie inside the 416-byte save area *)
  pose proof (f4_spill_stk g fr _ regs mem md Asp (Asp + 200) (Asp + 248) HFRA Hr9 HAspR
                ltac:(lia) ltac:(lia) ltac:(lia)) as HSTK.
  assert (HS200 : store_ok rsegs mem (wa (Asp + 200)) 8 = true).
  { apply (f4_store_ok_stku mem mem (Asp + 200) (Asp + 248) (Asp + 200) 8%nat HSTK (wmono_refl rsegs mem)); lia. }
  (* the exits' common part, after a write confined to the two spill words *)
  assert (REB : forall (regs' : bvmap 5 word) (mem' : word -> option byte) md',
    Frame.munch (f4_Wsp Asp) mem mem' -> Frame.wmono rsegs mem mem' ->
    stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) -> AsanLift.mat_le md md' ->
    getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
    getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
    getr regs' 26 = getr regs 26 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
    getr regs' 23 = getr regs 23 ->
    FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md' /\
    ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md' /\
    HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\
    b5_C g j phi fr regs' mem' /\ IDj g fr j mem' /\ u32 mem' (fr + 176) (t_k (g_in g) j) /\
    b5_PF g j phi fr regs' mem').
  { intros regs' mem' md' MU WM HWIN Hmat E2 E3 E4 E8 E9 E19 E26 E18 E21 E23.
    destruct (f4_fra_spill g fr _ regs regs' mem mem' md md' Asp HFRA HENT Hr9 HAspR MU WM HWIN Hmat
                E2 E3 E4 E8 E9 E19 E26) as (HFRA' & HENT').
    destruct (f4_keep1 g j phi fr Asp regs regs' mem mem' md HFRA HHB HFLSI HLK HC HID Hr9 HAspR MU WM
                E2 E9 E18 E21 E23) as (HHB' & HFLSI' & HLK' & HC' & HID').
    split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact HHB'|]. split; [exact HFLSI'|].
    split; [exact HLK'|]. split; [exact HC'|]. split; [exact HID'|].
    split.
    { apply (f4_u32_keep (f4_Wsp Asp) mem mem' (fr + 176) _ Hu32 MU).
      intros x Hx. unfold f4_Wsp. cbn [Frame.outside]. repeat split; try exact I; lia. }
    exact (f4_pf_sp g j phi fr Asp regs regs' mem mem' md HFRA HPF Hr9 HAspR MU E9). }
  destruct (Z_le_gt_dec (flen g j) 49) as [Hshort|Hlong].
  - (* ---- the short arm (len <= 49): `bgeu a0,s2` taken, exit 0x81e88 ---- *)
    apply (sl_run regs (Z_to_bv 64 0x81dfc) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x81e88 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
         getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\
         getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\
         mem' = write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
      (Post B APIf ra g)).
    + exact Hhalt.
    + (* F4.v:3328-3336, the run: f4_d64_short_run_of_F_bounded (this file) at k := t_k (g_in g) j,
         L := flen g j, A1 := Asp *)
      exact (f4_d64_short_run_of_F_bounded regs mem (t_k (g_in g) j) phi (flen g j) Asp
               Ha0 Hs9 Hr9 Hs2 Hflen0 Hshort HS200 ltac:(lia) ltac:(lia)).
    + intros R pc' mem' regs' md'
        (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24 & Hmem) Hreg Hmat.
      subst pc' mem'.
      assert (MU : Frame.munch (f4_Wsp Asp) mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))).
      { unfold f4_Wsp. apply (munch_write _ mem mem (Asp + 200) (le8 (Z_to_bv 64 (phi + 18))));
          [ apply munch_refl | lia | rewrite length_le8; lia
          | rewrite length_le8; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.inside]; left; lia ]. }
      assert (WM : Frame.wmono rsegs mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
        by (apply wmono_write; apply wmono_refl).
      assert (HWIN : stk rsegs (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                       (g_S g - AF.SLOT_STACK) (g_S g))
        by (apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]).
      destruct (REB regs' _ md' MU WM HWIN Hmat
                  ltac:(rewrite Hreg; exact HR2) ltac:(rewrite Hreg; exact HR3) ltac:(rewrite Hreg; exact HR4)
                  ltac:(rewrite Hreg; exact HR8) ltac:(rewrite Hreg; exact HR9) ltac:(rewrite Hreg; exact HR19)
                  ltac:(rewrite Hreg; exact HR26) ltac:(rewrite Hreg; exact HR18) ltac:(rewrite Hreg; exact HR21)
                  ltac:(rewrite Hreg; exact HR23))
        as (RFRA & RENT & RHB & RFLSI & RLK & RC & RID & Ru32 & RPF).
      rewrite <- SEGS. apply Hdf0.
      exists phi, regs', (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18)))), md', fr.
      split; [reflexivity|].
      split; [exact RFRA|]. split; [exact RENT|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact RHB|]. split; [exact RFLSI|].
      split; [exact RLK|]. split; [exact RC|].
      split; [lia|].
      split; [unfold rg; rewrite Hreg, HR24; reflexivity|].
      split; [exact Ru32|]. split; [exact RID|].
      (* b5_F17: the word 0x81e04 just stored at [A + 200] *)
      split; [|exact RPF].
      exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|]. split; [exact HAspR|].
      unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
  - (* ---- the long arm (50 <= len): the instrumented checks of the bytes phi+12 and phi+13 ---- *)
    assert (Hbig : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; unfold flen in Hlong; lia).
    destruct HPH as (HPHb & _ & _).
    pose proof (HPHb ltac:(lia)) as HGbytes.
    pose proof (Hs6 ltac:(lia)) as Hs6'.
    assert (Hglen : length (t_g (g_in g) j) = 50%nat) by (unfold t_g; apply fr50_length).
    assert (Hsh12 : bytes_at rsegs mem (Z.shiftr (phi + 12) 3 + ASAN_K) [Z_to_bv 8 0])
      by (apply (f4_sh_at mem phi (flen g j) 12 HAd); lia).
    assert (Hsh13 : bytes_at rsegs mem (Z.shiftr (phi + 13) 3 + ASAN_K) [Z_to_bv 8 0])
      by (apply (f4_sh_at mem phi (flen g j) 13 HAd); lia).
    pose proof (f4_ba_nth mem phi (t_g (g_in g) j) 12 HGbytes ltac:(rewrite Hglen; lia)) as Hb12.
    pose proof (f4_ba_nth mem phi (t_g (g_in g) j) 13 HGbytes ltac:(rewrite Hglen; lia)) as Hb13.
    change (Z.of_nat 12) with 12 in Hb12. change (Z.of_nat 13) with 13 in Hb13.
    assert (Hv12r : 0 <= cp_v (t_g (g_in g) j) 12 < 256) by (apply f4_byte_range).
    assert (Hv13r : 0 <= cp_v (t_g (g_in g) j) 13 < 256) by (apply f4_byte_range).
    (* The shadow bytes of phi+12 / phi+13 lie below the spill word (they are below HIGHMEM_BEG <= A).
       lia cannot see through Z.shiftr, so the two bounds are established here. *)
    assert (Hsa12 : Z.shiftr (phi + 12) 3 + ASAN_K + 1 <= Asp + 200).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    assert (Hsa13 : Z.shiftr (phi + 13) 3 + ASAN_K + 1 <= Asp + 200).
    { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
    destruct (Z.eq_dec (cp_v (t_g (g_in g) j) 12) 136) as [H12eq|H12ne].
    + (* byte 12 is 136: the check of byte 13, the spill [s1+240] and the jump to 0x81ea8 *)
      assert (H8819 : b2z (t_8819 (g_in g) j) = (if cp_v (t_g (g_in g) j) 13 =? 25 then 1 else 0)).
      { unfold b2z, t_8819. rewrite Hbig.
        replace (cp_v (t_g (g_in g) j) 12 =? 0x88) with true by (symmetry; apply Z.eqb_eq; exact H12eq).
        cbn [andb]. change 0x19 with 25. destruct (cp_v (t_g (g_in g) j) 13 =? 25); reflexivity. }
      apply (sl_run regs (Z_to_bv 64 0x81dfc) mem md
        (fun R pc' mem' => pc' = Z_to_bv 64 0x81ea8 /\
           getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
           getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
           getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
           getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
           getr R 25 = getr regs 25 /\
           getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\
           mem' = write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                    (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))))
        (Post B APIf ra g)).
      * exact Hhalt.
      * (* F4.v:3407-3467, the run: f4_d64_136_run_of_F (this file) at k := t_k (g_in g) j, L := flen g j,
           A1 := Asp, e := b2z (t_8819 (g_in g) j), b12 / b13 := nth 12 / nth 13 (t_g (g_in g) j) cp_z *)
        exact (f4_d64_136_run_of_F regs mem (t_k (g_in g) j) phi (flen g j) Asp (b2z (t_8819 (g_in g) j))
                 (nth 12 (t_g (g_in g) j) cp_z) (nth 13 (t_g (g_in g) j) cp_z)
                 Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 HAspR ltac:(lia) ltac:(lia) ltac:(lia) Hlong Hv12r Hv13r
                 Hsa12 Hsa13 H12eq H8819 HS200 HSTK Hsh12 Hsh13 Hb12 Hb13).
      * intros R pc' mem' regs' md'
          (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR22 & HR25 & HR24 & Hmem)
          Hreg Hmat.
        subst pc' mem'.
        assert (MU1 : Frame.munch (f4_Wsp Asp) mem
                        (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))).
        { unfold f4_Wsp. apply (munch_write _ mem mem (Asp + 200) (le8 (Z_to_bv 64 (phi + 18))));
            [ apply munch_refl | lia | rewrite length_le8; lia
            | rewrite length_le8; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.inside]; left; lia ]. }
        assert (MU : Frame.munch (f4_Wsp Asp) mem
                       (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                          (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))))).
        { unfold f4_Wsp in *.
          apply (munch_write _ mem _ (Asp + 240) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))));
            [ exact MU1 | lia | rewrite length_le8; lia
            | rewrite length_le8; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.inside]; right; left; lia ]. }
        assert (WM : Frame.wmono rsegs mem
                       (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                          (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j))))))
          by (apply wmono_write; apply wmono_write; apply wmono_refl).
        assert (HWIN : stk rsegs
                         (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                            (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))))
                         (g_S g - AF.SLOT_STACK) (g_S g)).
        { apply stk_write; [apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]
                           | lia | rewrite length_le8; lia]. }
        assert (Hq240 : q64 (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                               (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j)))))
                          (Asp + 240) (b2z (t_8819 (g_in g) j))).
        { unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
        destruct (REB regs' _ md' MU WM HWIN Hmat
                    ltac:(rewrite Hreg; exact HR2) ltac:(rewrite Hreg; exact HR3) ltac:(rewrite Hreg; exact HR4)
                    ltac:(rewrite Hreg; exact HR8) ltac:(rewrite Hreg; exact HR9) ltac:(rewrite Hreg; exact HR19)
                    ltac:(rewrite Hreg; exact HR26) ltac:(rewrite Hreg; exact HR18)
                    ltac:(rewrite Hreg; exact HR21) ltac:(rewrite Hreg; exact HR23))
          as (RFRA & RENT & RHB & RFLSI & RLK & RC & RID & Ru32 & RPF).
        rewrite <- SEGS. apply He10.
        exists phi, regs',
          (write_to_mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
             (wa (Asp + 240)) (le8 (Z_to_bv 64 (b2z (t_8819 (g_in g) j))))), md', fr.
        split; [reflexivity|].
        split; [exact RFRA|]. split; [exact RENT|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact RHB|]. split; [exact RFLSI|].
        split; [exact RLK|]. split; [exact RC|].
        split; [lia|].
        split; [unfold rg in *; rewrite Hreg, HR22; exact Hs6'|].
        split; [unfold rg; rewrite Hreg, HR24; reflexivity|].
        split; [unfold rg in *; rewrite Hreg, HR25; exact Hs9|].
        split.
        { exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|].
          split; [exact HAspR | exact Hq240]. }
        split; [exact Ru32|]. split; [exact RID|].
        (* b5_F17: the word 0x81e04 stored at [A + 200], which the 0x81e4c store misses *)
        split.
        { exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|]. split; [exact HAspR|].
          unfold q64. apply bytes_at_write_other;
            [ apply bytes_at_write_same; [lia | rewrite length_le8; lia] | lia | rewrite length_le8; lia
            | rewrite !length_le8; lia ]. }
        (* b5_W240: the word 0x81e4c just stored at [A + 240], b2z (t_8819 j) *)
        split; [|exact RPF].
        exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|]. split; [exact HAspR|].
        exists (b2z (t_8819 (g_in g) j)). split; [exact Hq240|].
        destruct (t_8819 (g_in g) j); cbv [b2z]; repeat split; intros; try lia; discriminate.
    + (* byte 12 is not 136: `bne a0,a1` taken, exit 0x81ea4 *)
      assert (H8819f : t_8819 (g_in g) j = false).
      { unfold t_8819.
        replace (cp_v (t_g (g_in g) j) 12 =? 0x88) with false by (symmetry; apply Z.eqb_neq; exact H12ne).
        rewrite andb_false_r. rewrite andb_false_l. reflexivity. }
      apply (sl_run regs (Z_to_bv 64 0x81dfc) mem md
        (fun R pc' mem' => pc' = Z_to_bv 64 0x81ea4 /\
           getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
           getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
           getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
           getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 22 = getr regs 22 /\
           getr R 25 = getr regs 25 /\
           getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\
           mem' = write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
        (Post B APIf ra g)).
      * exact Hhalt.
      * (* F4.v:3547-3575, the run: f4_d64_n136_run_of_F (this file) at k := t_k (g_in g) j, L := flen g j,
           A1 := Asp, b12 := nth 12 (t_g (g_in g) j) cp_z *)
        exact (f4_d64_n136_run_of_F regs mem (t_k (g_in g) j) phi (flen g j) Asp (nth 12 (t_g (g_in g) j) cp_z)
                 Ha0 Hs9 Hr9 Hs2 Hs7 Hr26 HAspR ltac:(lia) ltac:(lia) ltac:(lia) Hlong Hv12r
                 Hsa12 H12ne HS200 Hsh12 Hb12).
      * intros R pc' mem' regs' md'
          (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR22 & HR25 & HR24 & Hmem)
          Hreg Hmat.
        subst pc' mem'.
        assert (MU : Frame.munch (f4_Wsp Asp) mem
                       (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))).
        { unfold f4_Wsp. apply (munch_write _ mem mem (Asp + 200) (le8 (Z_to_bv 64 (phi + 18))));
            [ apply munch_refl | lia | rewrite length_le8; lia
            | rewrite length_le8; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.inside]; left; lia ]. }
        assert (WM : Frame.wmono rsegs mem (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18)))))
          by (apply wmono_write; apply wmono_refl).
        assert (HWIN : stk rsegs (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18))))
                         (g_S g - AF.SLOT_STACK) (g_S g))
          by (apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]).
        destruct (REB regs' _ md' MU WM HWIN Hmat
                    ltac:(rewrite Hreg; exact HR2) ltac:(rewrite Hreg; exact HR3) ltac:(rewrite Hreg; exact HR4)
                    ltac:(rewrite Hreg; exact HR8) ltac:(rewrite Hreg; exact HR9) ltac:(rewrite Hreg; exact HR19)
                    ltac:(rewrite Hreg; exact HR26) ltac:(rewrite Hreg; exact HR18)
                    ltac:(rewrite Hreg; exact HR21) ltac:(rewrite Hreg; exact HR23))
          as (RFRA & RENT & RHB & RFLSI & RLK & RC & RID & Ru32 & RPF).
        rewrite <- SEGS. apply He0c.
        exists phi, regs', (write_to_mem mem (wa (Asp + 200)) (le8 (Z_to_bv 64 (phi + 18)))), md', fr.
        split; [reflexivity|].
        split; [exact RFRA|]. split; [exact RENT|].
        split; [exact Hgn|]. split; [exact Hj|]. split; [exact RHB|]. split; [exact RFLSI|].
        split; [exact RLK|]. split; [exact RC|].
        split; [lia|].
        split; [unfold rg in *; rewrite Hreg, HR22; exact Hs6'|].
        split; [unfold rg; rewrite Hreg, HR24; reflexivity|].
        split; [unfold rg in *; rewrite Hreg, HR25; exact Hs9|].
        split; [exact H8819f|]. split; [exact Ru32|]. split; [exact RID|].
        (* b5_F17: the word 0x81e04 just stored at [A + 200] *)
        split; [|exact RPF].
        exists Asp. split; [unfold rg in *; rewrite Hreg, HR9; exact Hr9|]. split; [exact HAspR|].
        unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(* The pin: seg_F4_d64_of_F's type is F4.seg_F4_d64's, both read over this Section's variables. *)
Example seg_F4_d64_of_F_verbatim : True.
Proof.
  let T1 := type of seg_F4_d64_of_F in
  let T2 := type of (@F4.seg_F4_d64 fx LS rc B APIf SH SK ra empty FF) in
  constr_eq T1 T2; exact I.
Qed.

End S.
