(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2170 of its 2292 lines of code are new or changed and 889 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R9.v; 667 of its 885 lines of code are new or changed and 2074 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/R9.v 149252a8846b (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives R9.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of R9.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) twins of the three run lemmas of Seg/R9.v (r9_st :1065, r9_call :1258, r9_calln :1322, the
   lines of row S_R9 (segment-runs-A.tsv (a working note, not in this delivery))): the same runs, with the same
   post-state predicate, re-stepped with lib.Lib StepF as an ExecF.evtF under a universally quantified footprint
   RNG, with one plain ExecF.rng premise per region the run itself reads or writes, appended after the lemma's own
   premises; the regions of the callee reac_ctrl_parse are its own, and are passed through its footprint contract
   reac_ctrl_parse_contract_F (lib/A/Prog/reac_ctrl_parse_c.v:304) in the place where R9.v's Section hypothesis
   PARSE takes the plain reac_ctrl_parse_contract. Two of that contract's footprint premises are forall-memory
   forms (rng_bytes RNG, and the thread-cell premise quantified over DT TS C T DB k): they are passed through
   UNCHANGED, as the spec's callee rule says. R9.v itself is unchanged apart from comment text. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcSynth RcSynthLib RcFinLib RcLay
  RcIdentModel RcFrag RcReply reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs Tac_fsfree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
(* The segment file itself, and the evtF form of MemNorm.evt_normalize that r9_calln's script needs. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R9.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT.
(* Last but YK11: StepF's step (evtF goals) shadows Step's (evt goals); rng_bytes is a lib.Lib leaf over ExecF. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
(* Restore YK11.getr and YK11's segment names, as R9.v and Seg/F5F.v do. *)
Import YK11.
Open Scope Z_scope.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LFr (lib.Lib's Frame). *)
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

Section RunF.
Context {fx : YK11.FPState}.

(* R9.r9_sokb with the evtF goal shape (the one helper name the template shows must change): the store_ok fact of
   the one-byte store at b, from the wr_at fact W of the five-byte frame-shadow window. *)
Ltac r9F_sokb W b n :=
  match goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa b) n = true)
        by (eapply (r9_sok_at mm _ _ n b); [repeat apply wr_at_write; exact W | lia | lia])
  end.

(* ---- r9_st (R9.v:1065): the five one-byte stores of the frame shadow [S(fr) + 296, S(fr) + 301) and the li at
   0x81668 (0x81658 -> 0x81670). The run's only accesses are those five stores, so its footprint is the one region
   its own wr_at premise names. ---- *)
Lemma r9_st_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr : Z),
    0 <= Sfr fr -> Sfr fr + 301 <= 2 ^ 64 ->
    wr_at rsegs m (Sfr fr + 296) 5 ->
    ExecF.rng RNG (Sfr fr + 296) 5 ->
    ExecF.evtF rsegs RNG
      (fun ms => exists (m2 : word -> option byte),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 4) t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81670) fc None m2 (seg_rom rsegs) /\
         LFr.munch (r9_Wsh fr) m m2 /\ LFr.wmono rsegs m m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 296) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81658) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m fr HSfr0 HSfrhi Wsh Rsh.
  r9F_sokb Wsh (Sfr fr + 296) 1%nat. step.
  r9F_sokb Wsh (Sfr fr + 297) 1%nat. step.
  r9F_sokb Wsh (Sfr fr + 298) 1%nat. step.
  r9F_sokb Wsh (Sfr fr + 299) 1%nat. step.
  (* 0x81668 li s11,4 ; 0x8166c sb s11,300(s3) *)
  step.
  r9F_sokb Wsh (Sfr fr + 300) 1%nat. step.
  apply ExecF.evtF_done. eexists.
  split; [reflexivity|].
  split.
  { unfold r9_Wsh.
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl. }
  split.
  { do 5 apply wmono_write. apply wmono_refl. }
  split.
  { intros lo hi Hs. do 5 (apply stk_write; [ | lia | simpl_sizes; lia ]). exact Hs. }
  apply r9_bytes_cons.
  { rewrite <- r9_le1_0. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 296 + 1) with (Sfr fr + 297) by lia.
  apply r9_bytes_cons.
  { rewrite <- r9_le1_0. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 297 + 1) with (Sfr fr + 298) by lia.
  apply r9_bytes_cons.
  { rewrite <- r9_le1_0. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 298 + 1) with (Sfr fr + 299) by lia.
  apply r9_bytes_cons.
  { rewrite <- r9_le1_0. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 299 + 1) with (Sfr fr + 300) by lia.
  rewrite <- r9_le1_4. r9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
Qed.

(* R9.r9_st's statement, re-derived from r9_st_F at RNG_all (the one rng premise by rng_all, its bounds from the
   lemma's own two bounds on S(fr)). *)
Lemma r9_st_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr : Z),
    0 <= Sfr fr -> Sfr fr + 301 <= 2 ^ 64 ->
    wr_at rsegs m (Sfr fr + 296) 5 ->
    LE.evt rsegs
      (fun ms => exists (m2 : word -> option byte),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 4) t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81670) fc None m2 (seg_rom rsegs) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch (r9_Wsh fr) m m2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs m m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 296) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81658) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m fr HSfr0 HSfrhi Wsh.
  eapply ExecF.evtF_evt,
    (r9_st_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 Fr fc m fr HSfr0 HSfrhi Wsh).
  apply ExecF.rng_all; lia.
Qed.

(* ---- The call of reac_ctrl_parse, taken through its FOOTPRINT contract in the place where R9.v's Section
   hypothesis PARSE takes the plain one. ---- *)
Section WithParseF.
Hypothesis PARSE_F : reac_ctrl_parse_contract_F.

(* r9_call (R9.v:1258): 0x81670 mv a0,s8 ; 0x81674 mv a1,s2 ; 0x81678 ld a2,56(s1) ; 0x8167c jal reac_ctrl_parse.
   The segment's own access is the 8-byte spill load at A + 56 (its ov_read_bytes premise names it); every other
   region is the callee's, and is handed to reac_ctrl_parse_contract_F at this call's arguments. The two o-guarded
   footprint premises of that contract are given plain here, because this lemma carries o <> 0 as a premise. *)
Lemma r9_call_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: the segment's own spill load, then the callee's regions (reac_ctrl_parse_contract_F) *)
    ExecF.rng RNG (A + 56) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    ExecF.rng RNG o 36 ->
    ExecF.rng RNG (sh_lo o) (sh_len o 36) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f n o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    Rld Rbytes Rimg Rwin Rwins Rf Rfs Ro Ros Rbc Rbcs Rhdr Rfw Rtls.
  (* the spill base does not wrap: solve_accs needs it for the ld at s1 + 56 *)
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  (* the two o-guarded premises of the callee contract, from this lemma's o <> 0 *)
  assert (Hocellg : o <> 0 ->
            o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
            (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o))
    by (intros _; exact Hocell).
  assert (Hoag : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o))
    by (intros _; split; [exact Hoaddr|]; split; [exact Hoapp | exact HoCF]).
  assert (Rog : o <> 0 -> ExecF.rng RNG o 36) by (intros _; exact Ro).
  assert (Rosg : o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) by (intros _; exact Ros).
  (* 0x81670 mv a0,s8 ; 0x81674 mv a1,s2 ; 0x81678 ld a2,56(s1) ; 0x8167c jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof PARSE_F as HP. unfold reac_ctrl_parse_contract_F, REAC_CTRL_PARSE in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (f := f) (n := n) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try lia; try assumption. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Hflag & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81680)) with (Z_to_bv 64 0x81680)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

(* r9_calln (R9.v:1322): the same run on the real memory, through MemNormF.evtF_normalize_ro (the evtF form of
   MemNorm.evt_normalize, lib/A/MemNormF.v:147 - the one helper name the re-run changes). The footprint premises
   are r9_call_F's; the thread-cell premise is stated at m, and crosses to the normalized memory by r9_tls_rel,
   exactly as the plain premise HTLS does in R9.v's script. *)
Lemma r9_calln_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: the segment's own spill load, then the callee's regions (reac_ctrl_parse_contract_F) *)
    ExecF.rng RNG (A + 56) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    ExecF.rng RNG o 36 ->
    ExecF.rng RNG (sh_lo o) (sh_len o 36) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD
    Ho4 Hocell Howin Hofo HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    Rld Rbytes Rimg Rwin Rwins Rf Rfs Ro Ros Rbc Rbcs Rhdr Rfw Rtls.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := r9_call_F RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f n o S FS bs junk Hf Hn ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (r9_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL
                ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST) as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC Hbig).
  specialize (HC ltac:(intros i Hi; rewrite <- (mrd_rel rsegs m m0 _ REL); exact (HRD i Hi))).
  specialize (HC ltac:(split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | r9_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply r9_ro_gt; cbn in Hi; lia
    | split; [exact Howin | exact Hofo]])).
  specialize (HC (r9_cells_rel m m0 REL HAC) (r9_shrw_rel m m0 REL HSW) HHI HAPP
                 (r9_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros H50; exact (r9_addr_rel m m0 _ _ REL (HFA H50)))).
  specialize (HC (r9_addr_rel m m0 _ _ REL Hoaddr) Hoapp HoCF).
  specialize (HC (r9_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL)
                 ltac:(r9_ba_rel REL)).
  specialize (HC (r9_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS;
                       exact (proj2 (r9_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  specialize (HC Rld Rbytes Rimg Rwin Rwins Rf Rfs Ro Ros Rbc Rbcs Rhdr Rfw).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply Rtls;
                       exact (proj2 (r9_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  pose proof (MemNormF.evtF_normalize_ro RNG _ _ Fr _ fc None m (seg_rom rsegs) HRO HC) as HN.
  eapply ExecF.evtF_mono; [exact HN|].
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes,
    EFc, ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0)|].
  split; [exact (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0)|].
  split; [exact Hro'|].
  split; [exact (r9_stk_back m' m0' _ _ HR' ST0)|].
  split.
  { destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | r9_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  split; [exact (r9_shrw_back m' m0' HR' SW0)|].
  split; [exact (r9_addr_back m' m0' _ _ HR' AD0)|].
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  split.
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (r9_stk_back m' m0' _ _ HR' P5). }
  exact (proj2 (r9_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.

(* R9.r9_call's statement after its callee premise, re-derived from r9_call_F at RNG_all. Every rng premise is
   rng_all: the bounds are the lemma's own (A + 64 <= 2^64; the window, f, o, BC and FS bounds the plain premises
   carry), and the two quantified premises hold at RNG_all because RNG_all admits every access. *)
Lemma r9_call_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f n o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof Hocell as (Ho4 & Ho36 & Hocl & Howin & Hofo).
  pose proof (eq_refl : REAC_CTRL_PARSE_K = 8800) as HK.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  pose proof Hoaddr as (Hoa0 & _ & Hoa2 & _).
  pose proof HBC as (Hbc0 & _ & Hbc2 & _).
  pose proof HWA as (Hwa0 & _ & Hwa2 & _).
  eapply ExecF.evtF_evt,
    (r9_call_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
       t3 t4 t5 t6 Fr fc m A f n o S FS bs junk); try assumption.
  - (* the spill cell [A + 56] this segment reads *) apply ExecF.rng_all; lia.
  (* the callee's own footprint premises, by the discharge script of
     reac_ctrl_parse_contract_of_F (lib/A/Prog/reac_ctrl_parse_c.v:391) *)
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; rewrite ?E0; lia.
  - apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

(* R9.r9_calln's statement after its callee premise, re-derived from r9_calln_F at RNG_all, by the same rng_all
   discharges as r9_call_of_F. *)
Lemma r9_calln_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD
    Ho4 Hocell Howin Hofo HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof (eq_refl : REAC_CTRL_PARSE_K = 8800) as HK.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  pose proof Hoaddr as (Hoa0 & _ & Hoa2 & _).
  pose proof HBC as (Hbc0 & _ & Hbc2 & _).
  pose proof HWA as (Hwa0 & _ & Hwa2 & _).
  eapply ExecF.evtF_evt,
    (r9_calln_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
       t3 t4 t5 t6 Fr fc m A f n o S FS bs junk); try assumption.
  - (* the spill cell [A + 56] this segment reads *) apply ExecF.rng_all; lia.
  (* the callee's own footprint premises, by the discharge script of
     reac_ctrl_parse_contract_of_F (lib/A/Prog/reac_ctrl_parse_c.v:391) *)
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; rewrite ?E0; lia.
  - apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

End WithParseF.

(* ---- Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery)): the _on twins. The runs above take
   the callee contract, so they stay as they are, with their own proofs; the twins are new. The callee enters through
   reac_ctrl_parse_contract_F_on (lib/A/Prog/reac_ctrl_parse_c.v, a Theorem Labs lane 1af1d87305a), cited as a hypothesis, the
   Section Hypothesis PARSE_F_on. R = reac_ctrl_parse_shadow_R f n o S FS: the callee's own region at this call's
   arguments. The segment's own steps (0x81670 mv, mv, ld a2,56(s1), jal) read and store no shadow byte. The post
   `shadow_rw m'` becomes the form's `forall P, shadow_rw_on P m -> shadow_rw_on P m'`. The memory transports
   r9_shrw_rel / r9_shrw_back (R9.v) are replaced by A.ShadowRwOnT.shadow_rw_on_rel / shadow_rw_on_of_rel. ---- *)
Section WithParseF_on.
Hypothesis PARSE_F_on : reac_ctrl_parse_contract_F_on.

Lemma r9_call_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: the segment's own spill load, then the callee's regions (reac_ctrl_parse_contract_F_on) *)
    ExecF.rng RNG (A + 56) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    ExecF.rng RNG o 36 ->
    ExecF.rng RNG (sh_lo o) (sh_len o 36) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f n o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    Rld Rbytes Rimg Rwin Rwins Rf Rfs Ro Ros Rbc Rbcs Rhdr Rfw Rtls.
  (* the spill base does not wrap: solve_accs needs it for the ld at s1 + 56 *)
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit; lia).
  (* the two o-guarded premises of the callee contract, from this lemma's o <> 0 *)
  assert (Hocellg : o <> 0 ->
            o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
            (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o))
    by (intros _; exact Hocell).
  assert (Hoag : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o))
    by (intros _; split; [exact Hoaddr|]; split; [exact Hoapp | exact HoCF]).
  assert (Rog : o <> 0 -> ExecF.rng RNG o 36) by (intros _; exact Ro).
  assert (Rosg : o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) by (intros _; exact Ros).
  (* 0x81670 mv a0,s8 ; 0x81674 mv a1,s2 ; 0x81678 ld a2,56(s1) ; 0x8167c jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof PARSE_F_on as HP. unfold reac_ctrl_parse_contract_F_on, REAC_CTRL_PARSE in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (f := f) (n := n) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try lia; try assumption. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Hflag & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81680)) with (Z_to_bv 64 0x81680)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

Lemma r9_calln_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: the segment's own spill load, then the callee's regions (reac_ctrl_parse_contract_F_on) *)
    ExecF.rng RNG (A + 56) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    ExecF.rng RNG o 36 ->
    ExecF.rng RNG (sh_lo o) (sh_len o 36) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD
    Ho4 Hocell Howin Hofo HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    Rld Rbytes Rimg Rwin Rwins Rf Rfs Ro Ros Rbc Rbcs Rhdr Rfw Rtls.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := r9_call_F_on RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f n o S FS bs junk Hf Hn ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (r9_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL
                ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST) as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC Hbig).
  specialize (HC ltac:(intros i Hi; rewrite <- (mrd_rel rsegs m m0 _ REL); exact (HRD i Hi))).
  specialize (HC ltac:(split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | r9_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply r9_ro_gt; cbn in Hi; lia
    | split; [exact Howin | exact Hofo]])).
  specialize (HC (r9_cells_rel m m0 REL HAC) (A.ShadowRwOnT.shadow_rw_on_rel _ m m0 REL HSW) HHI HAPP
                 (r9_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros H50; exact (r9_addr_rel m m0 _ _ REL (HFA H50)))).
  specialize (HC (r9_addr_rel m m0 _ _ REL Hoaddr) Hoapp HoCF).
  specialize (HC (r9_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL) ltac:(r9_ba_rel REL)
                 ltac:(r9_ba_rel REL)).
  specialize (HC (r9_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS;
                       exact (proj2 (r9_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  specialize (HC Rld Rbytes Rimg Rwin Rwins Rf Rfs Ro Ros Rbc Rbcs Rhdr Rfw).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply Rtls;
                       exact (proj2 (r9_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  pose proof (MemNormF.evtF_normalize_ro RNG _ _ Fr _ fc None m (seg_rom rsegs) HRO HC) as HN.
  eapply ExecF.evtF_mono; [exact HN|].
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes,
    EFc, ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0)|].
  split; [exact (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0)|].
  split; [exact Hro'|].
  split; [exact (r9_stk_back m' m0' _ _ HR' ST0)|].
  split.
  { destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | r9_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  split; [exact (fun P HP => A.ShadowRwOnT.shadow_rw_on_of_rel P m' m0' HR'
                       (SW0 P (A.ShadowRwOnT.shadow_rw_on_rel P m m0 REL HP)))|].
  split; [exact (r9_addr_back m' m0' _ _ HR' AD0)|].
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  split.
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (r9_stk_back m' m0' _ _ HR' P5). }
  exact (proj2 (r9_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.

Lemma r9_call_of_F_on :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f n o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof Hocell as (Ho4 & Ho36 & Hocl & Howin & Hofo).
  pose proof (eq_refl : REAC_CTRL_PARSE_K = 8800) as HK.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  pose proof Hoaddr as (Hoa0 & _ & Hoa2 & _).
  pose proof HBC as (Hbc0 & _ & Hbc2 & _).
  pose proof HWA as (Hwa0 & _ & Hwa2 & _).
  eapply ExecF.evtF_evt,
    (r9_call_F_on ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
       t3 t4 t5 t6 Fr fc m A f n o S FS bs junk); try assumption.
  - (* the spill cell [A + 56] this segment reads *) apply ExecF.rng_all; lia.
  (* the callee's own footprint premises, by the discharge script of
     reac_ctrl_parse_contract_of_F (lib/A/Prog/reac_ctrl_parse_c.v:391) *)
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; rewrite ?E0; lia.
  - apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

Lemma r9_calln_of_F_on :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f n o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 64 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= n -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81680) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse n bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81680) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse n bs))] /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 n) s3i s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81670) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f n o S FS bs junk Hf Hn Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD
    Ho4 Hocell Howin Hofo HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof (eq_refl : REAC_CTRL_PARSE_K = 8800) as HK.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  pose proof Hoaddr as (Hoa0 & _ & Hoa2 & _).
  pose proof HBC as (Hbc0 & _ & Hbc2 & _).
  pose proof HWA as (Hwa0 & _ & Hwa2 & _).
  eapply ExecF.evtF_evt,
    (r9_calln_F_on ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s7 s9 s10 s11
       t3 t4 t5 t6 Fr fc m A f n o S FS bs junk); try assumption.
  - (* the spill cell [A + 56] this segment reads *) apply ExecF.rng_all; lia.
  (* the callee's own footprint premises, by the discharge script of
     reac_ctrl_parse_contract_of_F (lib/A/Prog/reac_ctrl_parse_c.v:391) *)
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; rewrite ?E0; lia.
  - apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

End WithParseF_on.

(* ---- The pins. r9_st has no callee premise, so its corollary states R9.r9_st's type term for term. r9_call and
   r9_calln state the owner's text after the owner's first premise, the plain reac_ctrl_parse_contract (R9.v
   Section S, Hypothesis PARSE); each corollary carries the footprint contract in that place (constr_eq is
   syntactic, not up to conversion). ---- *)
Example r9_st_of_F_verbatim : True.
Proof.
  let a := type of R9.r9_st in let b := type of r9_st_of_F in constr_eq a b.
  exact I.
Qed.

Example r9_call_of_F_verbatim : True.
Proof.
  lazymatch type of R9.r9_call with ?P -> ?A =>
    constr_eq P reac_ctrl_parse_contract;
    lazymatch type of r9_call_of_F with ?Q -> ?B =>
      constr_eq Q reac_ctrl_parse_contract_F; constr_eq A B
    end
  end.
  exact I.
Qed.

Example r9_calln_of_F_verbatim : True.
Proof.
  lazymatch type of R9.r9_calln with ?P -> ?A =>
    constr_eq P reac_ctrl_parse_contract;
    lazymatch type of r9_calln_of_F with ?Q -> ?B =>
      constr_eq Q reac_ctrl_parse_contract_F; constr_eq A B
    end
  end.
  exact I.
Qed.

End RunF.
