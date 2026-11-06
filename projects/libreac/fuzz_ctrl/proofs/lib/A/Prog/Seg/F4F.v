(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 487 of its 518 lines of code are new or changed and 980 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F4.v 2d4003b98bbc (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F4.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F4.<r> (for the two call lemmas, after replacing the callee contract by its _F form, which is the
   only difference). Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of F4.v's three run lemmas (f4_dbc_st :1332, f4_dbc_call :2183, f4_dbc_calln :2246 of the
   source blob), in a Section with F4.v's Section S declarations, so each twin discharges over the same variables.
   Regions, from the lemmas' own premises only:
     f4_dbc_st    : the spill word [A + 200, A + 208) and the five frame shadow bytes [Sfr fr + 22, Sfr fr + 27),
       the two regions its two wr_at premises name;
     f4_dbc_call  : the prologue spill read [A + 248, A + 256) its ov_read_bytes premise names, then the footprint
       premises of reac_ctrl_parse_contract_F (lib/A/Prog/reac_ctrl_parse_c.v:303), passed through unchanged and in
       the contract's own order (two of them, rng_bytes RNG and the asan_tls_cells clause, are forall-memory forms;
       they are passed through unchanged, as the spec allows);
     f4_dbc_calln : the same, at the caller's own memory (the twin runs f4_dbc_call_F on the normalized memory and
       comes back by MemNormF.evtF_normalize_ro, the footprint twin of MemNorm.evt_normalize).
   The callee contract is taken as the Section Hypothesis HPARSEF : reac_ctrl_parse_contract_F, in the same
   position as F4.v's HPARSE : reac_ctrl_parse_contract. F4.v is unchanged apart from comment text. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Last but YK11: StepF's step / finish (evtF goals) shadow the evt engine's; RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.

(* F4.v's two proof tactics over StepF's evtF goals (the helper names the form makes us change); the bodies are
   F4.v's, and f4_sok_at is F4's own lemma. *)
Ltac f4F_sokb W b n :=
  match goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa b) n = true)
        by (eapply (f4_sok_at mm _ _ n b); [repeat apply wr_at_write; exact W | lia | lia])
  end.

Ltac f4F_bw :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

(* F4.v's Section S starts at its line 58, so its Ltac definitions are section-local and not exported: this is the
   same body, under the same name, for this file. *)
Ltac f4_ba_rel R :=
  first [ apply (proj1 (bytes_at_rel rsegs _ _ _ _ R)); assumption
        | apply (proj2 (bytes_at_rel rsegs _ _ _ _ R)); assumption ].

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract in its footprint form, in HPARSE's position (F4.v Section S). *)
Hypothesis HPARSEF : reac_ctrl_parse_contract_F.

(* ---- 0x81e54-0x81e70: the spill of s7 + 18 to [s1 + 200] and the five frame shadow bytes. ---- *)
Lemma f4_dbc_st_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr phi : Z),
    0 <= A -> A + 208 <= 2 ^ 64 -> 0 <= fr -> 0 <= Sfr fr -> 0 <= phi < 2 ^ 64 ->
    Sfr fr + 27 <= 2 ^ 64 -> Sfr fr + 27 <= A + 200 ->
    wr_at rsegs m (A + 200) 8 -> wr_at rsegs m (Sfr fr + 22) 5 ->
    ExecF.rng RNG (A + 200) 8 -> ExecF.rng RNG (Sfr fr + 22) 5 ->
    ExecF.evtF rsegs RNG
      (fun ms => exists (m1 m2 : word -> option byte) (a0' : word),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0' a1i a2i a3 a4 a5 a6 a7 s2i
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81e74) fc None m2 (seg_rom rsegs) /\
         Frame.munch [(A + 200, A + 208)] m m1 /\ Frame.wmono rsegs m m1 /\
         Frame.munch (f4_Wsh fr) m1 m2 /\ Frame.wmono rsegs m1 m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m1 lo hi) /\
         (forall lo hi, stk rsegs m1 lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] /\
         q64 m2 (A + 200) (phi + 18))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7 s2i
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e54) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A fr phi HA0 HAhi Hfr0 HSfr0 Hphi HSfrhi HSA Wa Wsh Ra Rsh.
  (* the same two regions, in the address forms the code computes them (sd a0,200(s1) / sb _,22..26(s3)) *)
  assert (Ra' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 200) 8)
    by (rewrite MState.unsigned_lit by lia; exact Ra).
  assert (Rsh' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 (Sfr fr)) + 22) 5)
    by (rewrite MState.unsigned_lit by lia; exact Rsh).
  (* 0x81e54 addi a0,s7,18 ; 0x81e58 sd a0,200(s1) *)
  step.
  f4F_sokb Wa (A + 200) 8%nat. step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MU1 : Frame.munch [(A + 200, A + 208)] m mm)
        by (apply (munch_write _ m m (A + 200));
            [apply munch_refl | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; left; lia]);
      assert (WM1 : Frame.wmono rsegs m mm) by (apply wmono_write; apply wmono_refl);
      assert (ST1 : forall lo hi, stk rsegs m lo hi -> stk rsegs mm lo hi)
        by (intros lo hi Hs; apply stk_write; [exact Hs | lia | simpl_sizes; lia]);
      assert (HQ1 : q64 mm (A + 200) (phi + 18))
        by (unfold q64;
            lazymatch mm with
            | write_to_mem _ _ ?bs =>
                replace bs with (le8 (Z_to_bv 64 (phi + 18)));
                [ apply bytes_at_write_same; [lia | simpl_sizes; lia]
                | first [ reflexivity
                        | (rewrite (MState.unsigned_lit phi) by lia; reflexivity)
                        | (unfold PropExec.v_addi; rewrite (MState.unsigned_lit phi) by lia; reflexivity) ] ]
            end)
  end.
  (* 0x81e5c sb zero,22(s3) .. 0x81e68 sb zero,25(s3) *)
  f4F_sokb Wsh (Sfr fr + 22) 1%nat. step.
  f4F_sokb Wsh (Sfr fr + 23) 1%nat. step.
  f4F_sokb Wsh (Sfr fr + 24) 1%nat. step.
  f4F_sokb Wsh (Sfr fr + 25) 1%nat. step.
  (* 0x81e6c li a0,4 ; 0x81e70 sb a0,26(s3) *)
  step.
  f4F_sokb Wsh (Sfr fr + 26) 1%nat. step.
  apply ExecF.evtF_done.
  eexists. eexists. eexists.
  split; [reflexivity|].
  split; [exact MU1|].
  split; [exact WM1|].
  split.
  { unfold f4_Wsh.
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl. }
  split.
  { do 5 apply wmono_write. apply wmono_refl. }
  split; [exact ST1|].
  split.
  { intros lo hi Hs. do 5 (apply stk_write; [ | lia | simpl_sizes; lia ]). exact Hs. }
  split; [| unfold q64 in HQ1 |- *; f4F_bw; exact HQ1].
  apply f4_bytes_cons.
  { rewrite <- f4_le1_0. f4F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 22 + 1) with (Sfr fr + 23) by lia.
  apply f4_bytes_cons.
  { rewrite <- f4_le1_0. f4F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 23 + 1) with (Sfr fr + 24) by lia.
  apply f4_bytes_cons.
  { rewrite <- f4_le1_0. f4F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 24 + 1) with (Sfr fr + 25) by lia.
  apply f4_bytes_cons.
  { rewrite <- f4_le1_0. f4F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 25 + 1) with (Sfr fr + 26) by lia.
  rewrite <- f4_le1_4. f4F_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
Qed.

(* ---- 0x81e74-0x81e80 and the call, on a memory where mem_inv holds (the normalized one). ---- *)
Lemma f4_dbc_call_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= 0 -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd 0 bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= 0 -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= 0 -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: the caller's own spill read, then the callee contract's premises, unchanged *)
    ExecF.rng RNG (A + 248) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= 0 -> ExecF.rng RNG f 50) ->
    (50 <= 0 -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
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
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f 0 o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS
    R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW RTLS.
  (* the same region as R248, in the address form the code computes it (ld a2,248(s1)) *)
  assert (R248' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 248) 8)
    by (rewrite MState.unsigned_lit by lia; exact R248).
  (* 0x81e74 mv a0,s7 ; 0x81e78 li a1,0 ; 0x81e7c ld a2,248(s1) ; 0x81e80 jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof HPARSEF as HP. unfold reac_ctrl_parse_contract_F, REAC_CTRL_PARSE in HP.
  eapply ExecF.evtF_cut.
  { eapply HP with (RNG := RNG) (f := f) (n := 0) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try assumption; try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81e84)) with (Z_to_bv 64 0x81e84)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply ExecF.evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

(* ---- The same run on the real memory, by MemNormF.evtF_normalize_ro. ---- *)
Lemma f4_dbc_calln_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint: as f4_dbc_call_F's, at the caller's own memory *)
    ExecF.rng RNG (A + 248) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= 0 -> ExecF.rng RNG f 50) ->
    (50 <= 0 -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
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
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Ho4 Hocell Howin
    HAC HSW HHI HAPP HWA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS
    R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW RTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := f4_dbc_call_F RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f o S FS bs junk Hf ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (f4_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST)
    as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC ltac:(intros Hb; exfalso; lia)).
  specialize (HC ltac:(intros i Hi; change (cp_rd 0 bs) with (@nil nat) in Hi; destruct Hi)).
  specialize (HC ltac:(intros _; split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | f4_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply f4_ro_gt; cbn in Hi; lia
    | split; [exact Howin | intros Hb; exfalso; lia]])).
  specialize (HC (f4_cells_rel m m0 REL HAC) (f4_shrw_rel m m0 REL HSW) HHI HAPP (f4_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros Hb; exfalso; lia)).
  specialize (HC ltac:(intros _; split; [exact (f4_addr_rel m m0 _ _ REL Hoaddr) | split; [exact Hoapp | exact HoCF]])).
  specialize (HC (f4_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL) ltac:(f4_ba_rel REL)
                 ltac:(f4_ba_rel REL)).
  specialize (HC (f4_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS; exact (proj2 (f4_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  (* the footprint premises: the same regions; only the thread-cell clause reads memory, and it moves by f4_tls_rel *)
  specialize (HC R248 RB RI RW RWs RF RFs RO ROs RBC RBCs RFS RFW).
  specialize (HC ltac:(intros DT TS C T DB k HT0;
    exact (RTLS DT TS C T DB k (proj2 (f4_tls_rel m m0 _ DT TS C T DB k REL) HT0)))).
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
  split; [exact (f4_stk_back m' m0' _ _ HR' ST0)|].
  split.
  { destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | f4_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  split; [exact (f4_shrw_back m' m0' HR' SW0)|].
  split; [exact (f4_addr_back m' m0' _ _ HR' AD0)|].
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  split.
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (f4_stk_back m' m0' _ _ HR' P5). }
  exact (proj2 (f4_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.

(* ---- F4.v's three statements as corollaries at RNG_all. ---- *)

Lemma f4_dbc_st_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr phi : Z),
    0 <= A -> A + 208 <= 2 ^ 64 -> 0 <= fr -> 0 <= Sfr fr -> 0 <= phi < 2 ^ 64 ->
    Sfr fr + 27 <= 2 ^ 64 -> Sfr fr + 27 <= A + 200 ->
    wr_at rsegs m (A + 200) 8 -> wr_at rsegs m (Sfr fr + 22) 5 ->
    LE.evt rsegs
      (fun ms => exists (m1 m2 : word -> option byte) (a0' : word),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0' a1i a2i a3 a4 a5 a6 a7 s2i
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81e74) fc None m2 (seg_rom rsegs) /\
         Frame.munch [(A + 200, A + 208)] m m1 /\ Frame.wmono rsegs m m1 /\
         Frame.munch (f4_Wsh fr) m1 m2 /\ Frame.wmono rsegs m1 m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m1 lo hi) /\
         (forall lo hi, stk rsegs m1 lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] /\
         q64 m2 (A + 200) (phi + 18))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7 s2i
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e54) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A fr phi HA0 HAhi Hfr0 HSfr0 Hphi HSfrhi HSA Wa Wsh.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f4_dbc_st_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A fr phi); try assumption; apply ExecF.rng_all; lia.
Qed.

Lemma f4_dbc_call_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= 0 -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd 0 bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= 0 -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= 0 -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f 0 o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
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
  apply (f4_dbc_call_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10
           s11 t3 t4 t5 t6 Fr fc m A f o S FS bs junk); try assumption.
  - (* the spill read [A + 248, A + 256) *) apply ExecF.rng_all; lia.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f: vacuous at n = 0 *) intros H50. exfalso. lia.
  - intros H50. exfalso. lia.
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

Lemma f4_dbc_calln_of_F :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f 0 o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81e84) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse 0 bs))) a1' a2' a3' a4' a5' a6' a7'
                       s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81e84) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse 0 bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               s2i s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81e74) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f o S FS bs junk Hf Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Ho4 Hocell Howin
    HAC HSW HHI HAPP HWA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
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
  apply (f4_dbc_calln_F ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s2i s3i s4 s5 s6 s8 s9 s10
           s11 t3 t4 t5 t6 Fr fc m A f o S FS bs junk); try assumption.
  - (* the spill read [A + 248, A + 256) *) apply ExecF.rng_all; lia.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f: vacuous at n = 0 *) intros H50. exfalso. lia.
  - intros H50. exfalso. lia.
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

(* ---- The pins. f4_dbc_st_of_F is F4.f4_dbc_st's text, term for term. The two call corollaries differ from F4's
   lemmas in one subterm only: the callee contract premise, which names the _F form. ---- *)

Example f4_dbc_st_of_F_verbatim : True.
Proof. let A := type of F4.f4_dbc_st in let B := type of f4_dbc_st_of_F in constr_eq A B; exact I. Qed.

Example f4_dbc_call_of_F_verbatim : True.
Proof.
  let A := type of F4.f4_dbc_call in let B := type of f4_dbc_call_of_F in
  lazymatch B with
  | context C [reac_ctrl_parse_contract_F] =>
      let B' := context C [reac_ctrl_parse_contract] in constr_eq A B'
  end.
  exact I.
Qed.

Example f4_dbc_calln_of_F_verbatim : True.
Proof.
  let A := type of F4.f4_dbc_calln in let B := type of f4_dbc_calln_of_F in
  lazymatch B with
  | context C [reac_ctrl_parse_contract_F] =>
      let B' := context C [reac_ctrl_parse_contract] in constr_eq A B'
  end.
  exact I.
Qed.
