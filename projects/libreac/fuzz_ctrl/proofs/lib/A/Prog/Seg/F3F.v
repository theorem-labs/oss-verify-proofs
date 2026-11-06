(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 823 of its 864 lines of code are new or changed and 970 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F3.v 7267394c6d6f (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F3.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F3.<r> (for the two call lemmas, after replacing the callee contract by its _F form, which is the
   only difference). Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of F3.v's three run lemmas (f3_st :963, f3_call :1021, f3_calln :1083 of the source blob),
   in a Section with F3.v's Section S declarations, so each twin discharges over the same variables.
   Regions, from the lemmas' own premises only:
     f3_st   : the five frame shadow bytes [Sfr fr + 22, Sfr fr + 27) that its wr_at premise names;
     f3_call : the prologue spill [A + 248, A + 256) that its ov_read_bytes premise names, then the footprint
       premises of the callee contract reac_ctrl_parse_contract_F (lib/A/Prog/reac_ctrl_parse_c.v:303), passed
       through unchanged and in the contract's own order. Two of them are forall-memory forms (rng_bytes RNG and
       the asan_tls_cells clause); they are passed through unchanged, as the spec allows;
     f3_calln: the same, at the caller's own memory (the twin runs f3_call_F on the normalized memory and comes
       back by MemNormF.evtF_normalize_ro, the footprint twin of MemNorm.evt_normalize).
   The callee contract is taken as the Section Hypothesis HPARSEF : reac_ctrl_parse_contract_F, in the same
   position as F3.v's HPARSE : reac_ctrl_parse_contract. F3.v is unchanged apart from comment text. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs F1 F2 F3.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnT.
(* Last but YK11: StepF's step / finish (evtF goals) shadow the evt engine's; RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
(* The core copy an _F statement names (a Theorem Labs lane 08:56Z rule): LFr (lib.Lib's Frame). *)
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* F3.f3_sokb over StepF's evtF goals (the one helper name the form makes us change); its body is F3's. *)
Ltac f3F_sokb W b n :=
  match goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa b) n = true)
        by (eapply (f3_sok_at mm _ _ n b); [repeat apply wr_at_write; exact W | lia | lia])
  end.

(* F3.v's Section S starts at its line 43, so its Ltac definitions are section-local and not exported: these are
   the same bodies, under the same names, for this file. *)
Ltac f3_bw :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

Ltac f3_ba_rel R :=
  first [ apply (proj1 (bytes_at_rel rsegs _ _ _ _ R)); assumption
        | apply (proj2 (bytes_at_rel rsegs _ _ _ _ R)); assumption ].

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract in its footprint form, in HPARSE's position (F3.v Section S). *)
Hypothesis HPARSEF : reac_ctrl_parse_contract_F.

(* ---- 0x81dd0-0x81de8: s9 = s7 + 18 and the five frame shadow bytes. ---- *)
Lemma f3_st_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9i s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr phi : Z),
    0 <= fr -> 0 <= Sfr fr -> 0 <= phi < 2 ^ 64 -> Sfr fr + 27 <= 2 ^ 64 ->
    wr_at rsegs m (Sfr fr + 22) 5 ->
    ExecF.rng RNG (Sfr fr + 22) 5 ->
    ExecF.evtF rsegs RNG
      (fun ms => exists (m2 : word -> option byte) (a0' : word),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1i a2i a3 a4 a5 a6 a7 s2i
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 (Z_to_bv 64 (phi + 18)) s10 s11 t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81dec) fc None m2 (seg_rom rsegs) /\
         LFr.munch (f3_Wsh fr) m m2 /\ LFr.wmono rsegs m m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9i s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dd0) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9i s10 s11 t3 t4 t5 t6
    Fr fc m fr phi Hfr0 HSfr0 Hphi HSfrhi Wsh Rsh.
  (* the same region as Rsh, in the address form the code computes it (sb zero,22(s3) .. sb a0,26(s3)) *)
  assert (Rsh' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 (Sfr fr)) + 22) 5)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact Rsh).
  (* 0x81dd0 addi s9,s7,18 *)
  step.
  (* 0x81dd4 sb zero,22(s3) .. 0x81de0 sb zero,25(s3) *)
  f3F_sokb Wsh (Sfr fr + 22) 1%nat. step.
  f3F_sokb Wsh (Sfr fr + 23) 1%nat. step.
  f3F_sokb Wsh (Sfr fr + 24) 1%nat. step.
  f3F_sokb Wsh (Sfr fr + 25) 1%nat. step.
  (* 0x81de4 li a0,4 ; 0x81de8 sb a0,26(s3) *)
  step.
  f3F_sokb Wsh (Sfr fr + 26) 1%nat. step.
  apply ExecF.evtF_done.
  eexists. eexists.
  split; [reflexivity|].
  split.
  { unfold f3_Wsh.
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl. }
  split.
  { do 5 apply wmono_write. apply wmono_refl. }
  split.
  { intros lo hi Hs. do 5 (apply stk_write; [ | lia | simpl_sizes; lia ]). exact Hs. }
  apply f3_bytes_cons.
  { rewrite <- f3_le1_0. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 22 + 1) with (Sfr fr + 23) by lia.
  apply f3_bytes_cons.
  { rewrite <- f3_le1_0. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 23 + 1) with (Sfr fr + 24) by lia.
  apply f3_bytes_cons.
  { rewrite <- f3_le1_0. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 24 + 1) with (Sfr fr + 25) by lia.
  apply f3_bytes_cons.
  { rewrite <- f3_le1_0. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 25 + 1) with (Sfr fr + 26) by lia.
  rewrite <- f3_le1_4. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
Qed.

(* ---- 0x81dec-0x81df8 and the call, on a memory where mem_inv holds (the normalized one). ---- *)
Lemma f3_call_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= N -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: the caller's own spill read, then the callee contract's premises, unchanged *)
    ExecF.rng RNG (A + 248) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= N -> ExecF.rng RNG f 50) ->
    (50 <= N -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    (o <> 0 -> ExecF.rng RNG o 36) ->
    (o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f N o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS
    R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW RTLS.
  (* the same region as R248, in the address form the code computes it (ld a2,248(s1)) *)
  assert (R248' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 248) 8)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact R248).
  (* 0x81dec mv a0,s7 ; 0x81df0 mv a1,s2 ; 0x81df4 ld a2,248(s1) ; 0x81df8 jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof HPARSEF as HP. unfold reac_ctrl_parse_contract_F, REAC_CTRL_PARSE in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (RNG := RNG) (f := f) (n := N) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try assumption; try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81dfc)) with (Z_to_bv 64 0x81dfc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

(* ---- The same run on the real memory: f3_call_F on the normalized memory, back by
   MemNormF.evtF_normalize_ro (the footprint twin of MemNorm.evt_normalize). ---- *)
Lemma f3_calln_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= N -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: as f3_call_F's, at the caller's own memory *)
    ExecF.rng RNG (A + 248) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= N -> ExecF.rng RNG f 50) ->
    (50 <= N -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    (o <> 0 -> ExecF.rng RNG o 36) ->
    (o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD Ho4 Hocell
    Howin Howf HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW RTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := f3_call_F RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f N o S FS bs junk Hf HN ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (f3_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST)
    as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC Hbig).
  specialize (HC ltac:(intros i Hi; rewrite <- (mrd_rel rsegs m m0 _ REL); exact (HRD i Hi))).
  specialize (HC ltac:(intros _; split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | f3_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply f3_ro_gt; cbn in Hi; lia
    | split; [exact Howin | exact Howf]])).
  specialize (HC (f3_cells_rel m m0 REL HAC) (f3_shrw_rel m m0 REL HSW) HHI HAPP (f3_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros Hb; exact (f3_addr_rel m m0 _ _ REL (HFA Hb)))).
  specialize (HC ltac:(intros _; split; [exact (f3_addr_rel m m0 _ _ REL Hoaddr) | split; [exact Hoapp | exact HoCF]])).
  specialize (HC (f3_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL)
                 ltac:(f3_ba_rel REL)).
  specialize (HC (f3_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS; exact (proj2 (f3_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  (* the footprint premises: the same regions; only the thread-cell clause reads memory, and it moves by f3_tls_rel *)
  specialize (HC R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW).
  specialize (HC ltac:(intros DT TS C T DB k HT0;
    exact (RTLS DT TS C T DB k (proj2 (f3_tls_rel m m0 _ DT TS C T DB k REL) HT0)))).
  eapply ExecF.evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ Fr _ fc None m (seg_rom rsegs) HRO). exact HC. }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes, EFc,
    ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0)|].
  split; [exact (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0)|].
  split; [exact Hro'|].
  split; [exact (f3_stk_back m' m0' _ _ HR' ST0)|].
  split.
  { destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | f3_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  split; [exact (f3_shrw_back m' m0' HR' SW0)|].
  split; [exact (f3_addr_back m' m0' _ _ HR' AD0)|].
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  split.
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (f3_stk_back m' m0' _ _ HR' P5). }
  exact (proj2 (f3_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.

(* ---- F3.v's three statements as corollaries at RNG_all. The rng premises are discharged exactly as
   reac_ctrl_parse_c.v's reac_ctrl_parse_contract_of_F discharges the contract's own. ---- *)

Lemma f3_st_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9i s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr phi : Z),
    0 <= fr -> 0 <= Sfr fr -> 0 <= phi < 2 ^ 64 -> Sfr fr + 27 <= 2 ^ 64 ->
    wr_at rsegs m (Sfr fr + 22) 5 ->
    LE.evt rsegs
      (fun ms => exists (m2 : word -> option byte) (a0' : word),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1i a2i a3 a4 a5 a6 a7 s2i
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 (Z_to_bv 64 (phi + 18)) s10 s11 t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81dec) fc None m2 (seg_rom rsegs) /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch (f3_Wsh fr) m m2 /\
         OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs m m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9i s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dd0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9i s10 s11 t3 t4 t5 t6
    Fr fc m fr phi Hfr0 HSfr0 Hphi HSfrhi Wsh.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f3_st_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9i s10 s11
           t3 t4 t5 t6 Fr fc m fr phi); try assumption.
  apply ExecF.rng_all; lia.
Qed.

Lemma f3_call_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= N -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f N o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS.
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
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f3_call_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A f N o S FS bs junk); try assumption.
  - (* the spill read [A + 248, A + 256) *) apply ExecF.rng_all; lia.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* o *) intros Ho0. destruct (Hocell Ho0) as (_ & Ho1 & _). apply ExecF.rng_all; lia.
  - intros Ho0. destruct (Hocell Ho0) as (_ & Ho1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

Lemma f3_calln_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= N -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD Ho4 Hocell
    Howin Howf HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
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
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f3_calln_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A f N o S FS bs junk); try assumption.
  - (* the spill read [A + 248, A + 256) *) apply ExecF.rng_all; lia.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* o *) intros _. apply ExecF.rng_all; lia.
  - intros _. apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

End S.

(* ---- Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery)): the _on twins. The runs above take
   the callee contract, so they stay as they are, with their own proofs; the twins are new. The callee enters through
   reac_ctrl_parse_contract_F_on (lib/A/Prog/reac_ctrl_parse_c.v, a Theorem Labs lane 1af1d87305a), cited as a hypothesis, the
   Section Hypothesis HPARSEF_on. R = reac_ctrl_parse_shadow_R f N o S FS: the callee's own region at this call's
   arguments. The segment's own steps (0x81dec mv, mv, ld a2,248(s1), jal) read and store no shadow byte. The post
   `shadow_rw m'` becomes the form's `forall P, shadow_rw_on P m -> shadow_rw_on P m'`. The memory transports
   f3_shrw_rel / f3_shrw_back (F3.v) are replaced by A.ShadowRwOnT.shadow_rw_on_rel / shadow_rw_on_of_rel. ---- *)
Section S_on.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract in its route (C) footprint form, in HPARSEF's position. *)
Hypothesis HPARSEF_on : reac_ctrl_parse_contract_F_on.

Lemma f3_call_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= N -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_parse_shadow_R f N o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: the caller's own spill read, then the callee contract's premises, unchanged *)
    ExecF.rng RNG (A + 248) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= N -> ExecF.rng RNG f 50) ->
    (50 <= N -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    (o <> 0 -> ExecF.rng RNG o 36) ->
    (o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f N o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS
    R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW RTLS.
  (* the same region as R248, in the address form the code computes it (ld a2,248(s1)) *)
  assert (R248' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 248) 8)
    by (rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia; exact R248).
  (* 0x81dec mv a0,s7 ; 0x81df0 mv a1,s2 ; 0x81df4 ld a2,248(s1) ; 0x81df8 jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof HPARSEF_on as HP. unfold reac_ctrl_parse_contract_F_on, REAC_CTRL_PARSE in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (RNG := RNG) (f := f) (n := N) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try assumption; try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81dfc)) with (Z_to_bv 64 0x81dfc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

Lemma f3_calln_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= N -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_parse_shadow_R f N o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: as f3_call_F_on's, at the caller's own memory *)
    ExecF.rng RNG (A + 248) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= N -> ExecF.rng RNG f 50) ->
    (50 <= N -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    (o <> 0 -> ExecF.rng RNG o 36) ->
    (o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD Ho4 Hocell
    Howin Howf HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW RTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := f3_call_F_on RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f N o S FS bs junk Hf HN ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (f3_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST)
    as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC Hbig).
  specialize (HC ltac:(intros i Hi; rewrite <- (mrd_rel rsegs m m0 _ REL); exact (HRD i Hi))).
  specialize (HC ltac:(intros _; split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | f3_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply f3_ro_gt; cbn in Hi; lia
    | split; [exact Howin | exact Howf]])).
  specialize (HC (f3_cells_rel m m0 REL HAC) (A.ShadowRwOnT.shadow_rw_on_rel _ m m0 REL HSW) HHI HAPP
                 (f3_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros Hb; exact (f3_addr_rel m m0 _ _ REL (HFA Hb)))).
  specialize (HC ltac:(intros _; split; [exact (f3_addr_rel m m0 _ _ REL Hoaddr) | split; [exact Hoapp | exact HoCF]])).
  specialize (HC (f3_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL)
                 ltac:(f3_ba_rel REL)).
  specialize (HC (f3_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS; exact (proj2 (f3_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  (* the footprint premises: the same regions; only the thread-cell clause reads memory, and it moves by f3_tls_rel *)
  specialize (HC R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW).
  specialize (HC ltac:(intros DT TS C T DB k HT0;
    exact (RTLS DT TS C T DB k (proj2 (f3_tls_rel m m0 _ DT TS C T DB k REL) HT0)))).
  eapply ExecF.evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ Fr _ fc None m (seg_rom rsegs) HRO). exact HC. }
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes, EFc,
    ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0)|].
  split; [exact (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0)|].
  split; [exact Hro'|].
  split; [exact (f3_stk_back m' m0' _ _ HR' ST0)|].
  split.
  { destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | f3_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  split; [exact (fun P HP => A.ShadowRwOnT.shadow_rw_on_of_rel P m' m0' HR'
                       (SW0 P (A.ShadowRwOnT.shadow_rw_on_rel P m m0 REL HP)))|].
  split; [exact (f3_addr_back m' m0' _ _ HR' AD0)|].
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  split.
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (f3_stk_back m' m0' _ _ HR' P5). }
  exact (proj2 (f3_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.

Lemma f3_call_of_F_on :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= N -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_parse_shadow_R f N o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f N o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS.
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
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f3_call_F_on ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A f N o S FS bs junk); try assumption.
  - (* the spill read [A + 248, A + 256) *) apply ExecF.rng_all; lia.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* o *) intros Ho0. destruct (Hocell Ho0) as (_ & Ho1 & _). apply ExecF.rng_all; lia.
  - intros Ho0. destruct (Hocell Ho0) as (_ & Ho1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

Lemma f3_calln_of_F_on :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= N -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_parse_shadow_R f N o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD Ho4 Hocell
    Howin Howf HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
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
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f3_calln_F_on ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A f N o S FS bs junk); try assumption.
  - (* the spill read [A + 248, A + 256) *) apply ExecF.rng_all; lia.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hbig H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* o *) intros _. apply ExecF.rng_all; lia.
  - intros _. apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

End S_on.

(* ---- The pins. f3_st_of_F is F3.f3_st's text, term for term. The two call corollaries differ from F3's lemmas
   in one subterm only: the callee contract premise, which names the _F form; the context pattern replaces that one
   occurrence and then compares the whole type (section binders included) by constr_eq. ---- *)

Example f3_st_of_F_verbatim : True.
Proof. let A := type of F3.f3_st in let B := type of f3_st_of_F in constr_eq A B; exact I. Qed.

Example f3_call_of_F_verbatim : True.
Proof.
  let A := type of F3.f3_call in let B := type of f3_call_of_F in
  lazymatch B with
  | context C [reac_ctrl_parse_contract_F] =>
      let B' := context C [reac_ctrl_parse_contract] in constr_eq A B'
  end.
  exact I.
Qed.

Example f3_calln_of_F_verbatim : True.
Proof.
  let A := type of F3.f3_calln in let B := type of f3_calln_of_F in
  lazymatch B with
  | context C [reac_ctrl_parse_contract_F] =>
      let B' := context C [reac_ctrl_parse_contract] in constr_eq A B'
  end.
  exact I.
Qed.
