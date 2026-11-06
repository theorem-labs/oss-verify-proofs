(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 700 of its 746 lines of code are new or changed and 885 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase3SegA.v; 408 of its 467 lines of code are new or changed and 687 lines of the source are left out. *)
(* Case 3 of the B walk of LLVMFuzzerTestOneInput (fuzz_boxreg.asan-ubsan), segment D: from the point C3_FREE
   (0x808b0) to the cut LI_K (0x80b08); BoxBLxCase3Defs.v holds the points.
   The code (offsets from 0x7ffac):
   - 0x808b0 .. 0x808b4: `mv a0, s3` and free (name) (YC5d.v afree04_rule through YC85.v afree04_sub). The return
     address 0x808b8 = BASE + 0x90c is LX_FSITES' first site. The name block (q, |nm| + 1) is the last block of the
     point and not one of the caller's blocks, so the rule's footprint premise is vacuous;
   - 0x808b8 .. 0x808c0: s8 = renamed as an unsigned 32-bit value (slli / srli 32), then the jump to 0x80b08.
   free's post splits the blocks around the freed one (l1 ++ (q, n) :: l2). AR keeps the blocks pairwise disjoint
   (YCbq.v sep_blocks_pos), so the freed block occurs once: it is the last entry, and the blocks left are the
   caller's and the registry (lblk). The landing takes the registry's new bytes from c3_set_name_inv.
   The engine runs on small symbolic states (the registers as atoms, no region; BoxBLxCase2.v's form). The point's
   memory facts are kept across free by its acall_kept: the stack at or above sp1, the input block, the frame and
   its shadow, and the registry lie apart from the freed name block. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo BoxTailVis.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBReadName BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase3Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* 0x808b8: back from free (LX_FSITES' first site). *)
Definition C3D_RET : Z := 0x90c.
(* The shadow base as the engine's shadow tokens see it (no token is used: the segment reads no memory). *)
Definition C3DSB : Z := 0x7fff8000.
Definition C3DBx : sv := SLit C3DSB.
Definition C3Dspan : Z * Z := (C3DSB, C3DSB + 2 ^ 44 - 1).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS : AR_laws SEGS B := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

Lemma c3d_ewR : forall (regs : bvmap 5 word) extra n (rr : bv 5),
  Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs extra)) n = getr regs rr.
Proof.
  intros regs extra n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma c3d_rdword_keep : forall (rd rd' : reader) a v,
  (forall z, 0 <= z < 8 -> rd' (a + z) = rd (a + z)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk H. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.

(* A small symbolic state: the registers as atoms 0 .. 31, no region, no fact. *)
Lemma c3d_seat : forall (W : world SEGS) (regs : bvmap 5 word) m pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
  intros W regs m pc. rewrite restrict_mkst_fx.
  apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | exact (conj I (conj I I))].
Qed.

(* A run with no region writes no byte. *)
Lemma c3d_frame_nil : forall E m m', frame_of E [] m m' -> forall x, m' x = m x.
Proof. intros E m m' HF x. apply HF. intros (rg & Hin & _). destruct Hin. Qed.

(* s8 at 0x808bc: renamed (-1 .. 4) as an unsigned 32-bit value. *)
Lemma c3d_u32 : forall x, -1 <= x < 5 ->
  alu64 ALU_SRL (alu64 ALU_SLL (w64 x) (Z_to_bv 64 32)) (Z_to_bv 64 32) = w64 (x mod 2 ^ 32).
Proof.
  intros x Hx. assert (Hc : x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma c3d_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia].
  destruct Ha as [x ->]. destruct Hb as [y ->]. apply Z.mod_divide; [lia|]. exists (2 * x - y). lia.
Qed.

Lemma c3d_mod8 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
  intros a Ha. apply Z.mod_divide in Ha; [|lia]. destruct Ha as [x ->].
  apply Z.mod_divide; [lia|]. exists (2 * x). lia.
Qed.

(* ---- the segment: the point's data ---- *)
Section c.
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Variable cx : lxcx.
Variables fp k acc : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable pos : nat.
Variables r fab op idxb q : Z.
Variables bs nm : list byte.
Hypothesis HB : lx_base B MT cx.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HMO : mo_le MT (lc_S cx) S3 acc.
Hypothesis HK : lx_from B MT POST (LI_K B MT i).
Hypothesis Hi : (i < 64)%nat.
Hypothesis Hk : k <= 2 + 2 * Z.of_nat i.
Hypothesis Hacc : acc <= LX_A1 MT + Z.of_nat i * LX_AI MT + mo_malloc MT (c3_nlen nm + 1).
Hypothesis HBL : ablocks B ly3 S3 = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG); (q, c3_nlen nm + 1)].
Hypothesis Hnl : c3_nlen nm <= 47.
Hypothesis HINV : Boxreg.boxreg_inv bs.
Hypothesis HFAB : Boxreg.bx_fabric bs = fab.

(* The registry's bytes after set_name, and the renamed row (-1 for none). *)
Definition c3d_bsc : list byte := tbreac_boxreg_set_name_bytes bs (c3_sext8 idxb) (c3_sel_s op nm).
Definition c3d_ren : Z := c3_ren (c3_sext8 idxb) (Boxreg.bx_n bs).

(* The memory facts LI_K needs, at any world (free may change the world). *)
Definition c3d_cms (m : word -> option byte) : machine_state := mkst (lc_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).
Definition c3d_mem (W : world SEGS) (m : word -> option byte) : Prop :=
  lsaved cx W (c3d_cms m) /\ lshadow cx fp W (c3d_cms m) LSH_iter /\
  rdword (aview SEGS (w_H W) m) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) /\
  lslot cx W (c3d_cms m) 0x10 (lF cx fp) /\ lslot cx W (c3d_cms m) 0x18 (lF cx fp) /\
  lslot cx W (c3d_cms m) 0x80 (lF cx fp) /\
  garr8 SEGS (mrestrict (w_H W) m) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) /\
  lreg W (c3d_cms m) r c3d_bsc /\ lprev cx fp W (c3d_cms m) bs /\ lcur cx W (c3d_cms m) pos /\
  lslots_loop cx fp W (c3d_cms m) r fab /\ lslot cx W (c3d_cms m) 0x58 (Z.of_nat i).
(* The bytes those facts speak about. *)
Definition c3d_at (a : Z) : Prop :=
  lsp1 cx <= a < 2 ^ 64 \/ lc_p cx <= a < lc_p cx + lc_n cx \/ lF cx fp <= a < lF cx fp + 512 \/
  lSH cx fp <= a < lSH cx fp + 64 \/ r <= a < r + 288.

Lemma c3d_mem_keep : forall W m W' m', c3d_mem W m ->
  (forall a, c3d_at a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) -> c3d_mem W' m'.
Proof.
  intros W m W' m' (SV & SH & FL & S10 & S18 & S80 & GI & RG & PV & CUR & SL & S58) KP.
  pose proof (lx_sp_facts B MT cx HB) as (Hs16 & Hs0 & Hs47 & Hs1 & Hs32).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by reflexivity.
  assert (KS : forall off v, 0 <= off -> off <= 0x90 -> lslot cx W (c3d_cms m) off v -> lslot cx W' (c3d_cms m') off v).
  { intros off v H0 H1 H. unfold lslot, lview in *. cbn [c3d_cms ms_mem mkst] in *.
    eapply (c3d_rdword_keep _ _ _ v); [|exact H]. intros z Hz. apply KP. left. lia. }
  unfold c3d_mem.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - destruct SV as (Sra & Sj). unfold lsaved, lview in *. cbn [c3d_cms ms_mem mkst] in *. split.
    + eapply (c3d_rdword_keep _ _ _ _); [|exact Sra]. intros z Hz. apply KP. left. lia.
    + intros j Hj. eapply (c3d_rdword_keep _ _ _ _); [|exact (Sj j Hj)]. intros z Hz. apply KP. left. lia.
  - intros z Hz. unfold lview in *. cbn [c3d_cms ms_mem mkst] in *. rewrite KP; [exact (SH z Hz)|].
    right; right; right; left. assert (Z.of_nat (length LSH_iter) = 52) by reflexivity. lia.
  - rewrite Hfb in *. eapply (c3d_rdword_keep _ _ _ _); [|exact FL]. intros z Hz. apply KP. right; right; left. lia.
  - apply KS; [lia | lia | exact S10].
  - apply KS; [lia | lia | exact S18].
  - apply KS; [lia | lia | exact S80].
  - apply (garr8_frame SEGS _ _ _ _ GI). intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview SEGS).
    apply KP. right; left. unfold lc_n. lia.
  - intros z Hz. unfold lview in *. cbn [c3d_cms ms_mem mkst] in *. rewrite KP; [exact (RG z Hz)|].
    right; right; right; right. unfold LX_REG in Hz. lia.
  - intros z Hz. unfold lview in *. cbn [c3d_cms ms_mem mkst] in *. rewrite KP; [exact (PV z Hz)|].
    right; right; left. unfold LX_REG in Hz. lia.
  - destruct CUR as (Hp & C88 & C90). split; [exact Hp|]. split; apply KS; first [lia | assumption].
  - destruct SL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78). repeat split; apply KS; first [lia | assumption].
  - apply KS; [lia | lia | exact S58].
Qed.

Lemma c3d_mem_same : forall W m m', c3d_mem W m -> (forall x, m' x = m x) -> c3d_mem W m'.
Proof.
  intros W m m' H E. apply (c3d_mem_keep W m W m' H). intros a _. unfold aview, mbyte, mrestrict. rewrite E. reflexivity.
Qed.

(* The registers every point of the segment keeps. *)
Definition c3d_regs (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lsp1 cx) /\ getr regs 8 = w64 (lsp0 cx) /\ getr regs 9 = w64 (lsp1 cx) /\
  getr regs 3 = getr (lc_regs cx) 3 /\ getr regs 4 = getr (lc_regs cx) 4 /\
  getr regs 18 = w64 SHADOW_OFF /\ getr regs 22 = w64 (lSH cx fp) /\
  getr regs 20 = w64 r /\ getr regs 21 = w64 (lF cx fp + 64) /\ getr regs 27 = w64 fab.

Lemma c3d_regs_same : forall regs regs',
  (forall n, In n [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] -> getr regs' (Z_to_bv 5 n) = getr regs (Z_to_bv 5 n)) ->
  c3d_regs regs -> c3d_regs regs'.
Proof.
  intros regs regs' K (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27). unfold c3d_regs.
  split; [etransitivity; [exact (K 2 ltac:(repeat (first [left; reflexivity | right]))) | exact G2]|].
  split; [etransitivity; [exact (K 8 ltac:(repeat (first [left; reflexivity | right]))) | exact G8]|].
  split; [etransitivity; [exact (K 9 ltac:(repeat (first [left; reflexivity | right]))) | exact G9]|].
  split; [etransitivity; [exact (K 3 ltac:(repeat (first [left; reflexivity | right]))) | exact G3]|].
  split; [etransitivity; [exact (K 4 ltac:(repeat (first [left; reflexivity | right]))) | exact G4]|].
  split; [etransitivity; [exact (K 18 ltac:(repeat (first [left; reflexivity | right]))) | exact G18]|].
  split; [etransitivity; [exact (K 22 ltac:(repeat (first [left; reflexivity | right]))) | exact G22]|].
  split; [etransitivity; [exact (K 20 ltac:(repeat (first [left; reflexivity | right]))) | exact G20]|].
  split; [etransitivity; [exact (K 21 ltac:(repeat (first [left; reflexivity | right]))) | exact G21]|].
  etransitivity; [exact (K 27 ltac:(repeat (first [left; reflexivity | right]))) | exact G27].
Qed.

Lemma c3d_regs_pres : forall regs regs', aregs_preserved regs regs' -> c3d_regs regs -> c3d_regs regs'.
Proof.
  intros regs regs' HP. apply c3d_regs_same. intros n Hn. apply HP. unfold acallee_saved.
  cbv [In] in Hn. lia.
Qed.

Lemma c3d_regs_run : forall (W : world SEGS) regs extra ss (ms : machine_state),
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) ss (restrict (w_H W) ms) ->
  forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) = true ->
  c3d_regs regs -> c3d_regs (ms_regs ms).
Proof.
  intros W regs extra ss ms HS Hl. apply c3d_regs_same. intros n Hn.
  apply (regs_kept_of_st_ok_pi _ ss (restrict (w_H W) ms) regs extra
           (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) HS); [| exact Hl | apply in_map; exact Hn].
  split; [intros z Hz; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma c3d_regs_call : forall (W : world SEGS) regs extra ss (ms : machine_state),
  st_ok SEGS (Eimg (Ereg regs extra)) ss (restrict (w_H W) ms) ->
  forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) = true ->
  c3d_regs regs -> c3d_regs (ms_regs ms).
Proof.
  intros W regs extra ss ms HS Hl. apply c3d_regs_same. intros n Hn.
  pose proof (regs_kept_of_st_ok SEGS _ ss (restrict (w_H W) ms) regs extra
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) HS) as K.
  cbn [restrict ms_regs] in K. apply K; [| exact Hl | apply in_map; exact Hn].
  split; [intros z Hz; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* ---- K (0x80b08): the cut's predicate (c3_set_name_inv gives the registry's checks and lkept) ---- *)
Lemma c3d_K : forall (W2 : world SEGS) ly2 S2 regs m md2 acc2,
  c3d_regs regs -> getr regs 24 = w64 (c3d_ren mod 2 ^ 32) -> c3d_mem W2 m ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly2 S2 W2 m md2 (k + 1) ->
  frames S2 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S2 acc2 -> acc2 <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT ->
  lblk B cx ly2 S2 r ->
  SRr SEGS W2 (mkCfg (mkst regs (Z_to_bv 64 (BASE + LP_K)) m (seg_rom SEGS)) md2) (POST cx).
Proof.
  intros W2 ly2 S2 regs m md2 acc2 (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27) G24
    (SV & SH & FL & S10 & S18 & S80 & GI & RG & PV & CUR & SL & S58) HJ2 HFR2 HMO2 Hacc2 HBLK2.
  pose proof (c3_set_name_inv bs (c3_sext8 idxb) (c3_sel_s op nm) HINV) as HSN. cbv zeta in HSN.
  destruct HSN as (HI' & HF' & HKP & HR).
  apply (HK cx fp (k + 1) acc2 ly2 S2 W2 (mkst regs (Z_to_bv 64 (BASE + LP_K)) m (seg_rom SEGS)) md2 HB HJ2 HFR2 HMO2).
  exists pos, r, fab, c3d_ren, bs, c3d_bsc.
  split.
  { unfold lx_body. do 6 (split; [reflexivity|]).
    split; [exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 G22))))))|].
    split; [exact SV|]. split; [exact SH|]. split; [exact FL|].
    split; [exact S10|]. split; [exact S18|]. split; [exact S80 | exact GI]. }
  split; [exact Hi|]. split; [lia|]. split; [exact Hacc2|].
  split; [exact HBLK2|]. split; [exact PV|]. split; [exact HINV|]. split; [exact HFAB|].
  split; [exact RG|]. split; [exact HI'|]. split; [unfold c3d_bsc; rewrite HF'; exact HFAB|]. split; [exact HKP|].
  split; [exact HR|]. split; [exact CUR|]. split; [exact SL|]. split; [exact S58|].
  split; [exact G20|]. split; [exact G21|]. split; [exact G24 | exact G27].
Qed.

(* ---- 0x808b8 .. 0x80b08: s8 = renamed as an unsigned 32-bit value, the jump to K ---- *)
Lemma c3d_ret : forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2 acc2,
  c3d_regs regs2 -> getr regs2 23 = w64 c3d_ren -> c3d_mem W2 mem2 ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly2 S2 W2 mem2 md2 (k + 1) ->
  frames S2 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S2 acc2 -> acc2 <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT ->
  lblk B cx ly2 S2 r ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + C3D_RET)) mem2 (seg_rom SEGS)) md2) (POST cx).
Proof.
  intros W2 ly2 S2 regs2 mem2 md2 acc2 GR G23 HM HJ HFR2 HMO2 Hacc2 HBLK2.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (c3d_seat W2 regs2 mem2 C3D_RET) as HS.
  assert (SHOK : sh_ok SEGS C3DBx [] (Eimg (Ereg regs2 [])) (mrestrict (w_H W2) mem2)) by constructor.
  remember (Eimg (Ereg regs2 [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (F23 : ew E 23 = w64 c3d_ren) by (subst E; rewrite (c3d_ewR regs2 [] 23 23%bv eq_refl); exact G23).
  (* 0x808b8 slli s7; 0x808bc srli s8; 0x808c0 j 0x80b08: the run writes no byte *)
  paj_run_to_tok RUNTO HS HJ SHOK C3Dspan LP_K; [apply awr_ok_nil |].
  cbn [ss_mem] in HF.
  pose proof (c3d_mem_same W2 mem2 (ms_mem ms) HM (c3d_frame_nil E mem2 (ms_mem ms) HF)) as HMn.
  pmkst HS. prreg HS (24%bv : bv 5) R24.
  rewrite HE in HS.
  assert (Hren : -1 <= c3d_ren < 5).
  { pose proof HINV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
    pose proof (c3_set_name_inv bs (c3_sext8 idxb) (c3_sel_s op nm) HINV) as HSN. cbv zeta in HSN.
    destruct HSN as (_ & _ & _ & HR). unfold c3d_ren. lia. }
  eapply (c3d_K W2 ly2 S2 (ms_regs ms) (ms_mem ms) _ acc2).
  - exact (c3d_regs_run W2 _ _ _ _ HS eq_refl GR).
  - rewrite R24, F23. exact (c3d_u32 c3d_ren Hren).
  - exact HMn.
  - exact HJ.
  - exact HFR2.
  - exact HMO2.
  - exact Hacc2.
  - exact HBLK2.
Qed.

(* The frame's address and range at the point's layout (BoxBLxSeat.v lx_frame_addr_eq, lx_F_facts). *)
Hypothesis HFeq : frame_addr ly3 LX_CID fp = lF cx fp.
Hypothesis HFG : 4096 <= lF cx fp /\ lF cx fp + 512 <= alloc_ceiling /\ in_app (lF cx fp) 512.

(* The name block is not one of the caller's: the point's blocks are the caller's with the registry and the name
   block added once (AR's separation of distinct positions). *)
Lemma c3d_q_fresh : forall (W : world SEGS) m md, AR SEGS B ly3 S3 W m md ->
  ~ In (q, c3_nlen nm + 1) (ablocks B (lc_ly cx) (lc_S cx)).
Proof.
  intros W m md HAR Hin. apply in_split in Hin as (l1 & l2 & E1).
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W m md (q, c3_nlen nm + 1) (q, c3_nlen nm + 1) l1
    (l2 ++ [(r, LX_REG)]) [] HAR) as Hd.
  rewrite HBL, E1 in Hd. specialize (Hd ltac:(rewrite <- !app_assoc; reflexivity)).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
  rewrite c3_req in Hd by (unfold c3_nlen; lia). unfold c3_nlen in Hd. lia.
Qed.

(* free's split of the blocks around the name block: the block occurs once, so it is the last entry, and the blocks
   left are the caller's and the registry. *)
Lemma c3d_last : forall (W : world SEGS) m md l1 l2, AR SEGS B ly3 S3 W m md ->
  ablocks B ly3 S3 = l1 ++ (q, c3_nlen nm + 1) :: l2 ->
  l1 ++ l2 = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG)].
Proof.
  intros W m md l1 l2 HAR E.
  set (x := (q, c3_nlen nm + 1)) in *. set (L0 := ablocks B (lc_ly cx) (lc_S cx)) in *.
  rewrite HBL in E.
  induction l2 as [|y l2' _] using rev_ind.
  - assert (E' : (L0 ++ [(r, LX_REG)]) ++ [x] = l1 ++ [x]) by (rewrite <- app_assoc; exact E).
    apply app_inj_tail in E' as [E'' _]. rewrite app_nil_r. symmetry. exact E''.
  - exfalso.
    assert (E' : (L0 ++ [(r, LX_REG)]) ++ [x] = (l1 ++ x :: l2') ++ [y]) by (rewrite <- !app_assoc; exact E).
    apply app_inj_tail in E' as [E1 E2]. subst y.
    pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W m md x x l1 l2' [] HAR) as Hd.
    assert (Hb : ablocks B ly3 S3 = l1 ++ x :: l2' ++ x :: []).
    { rewrite HBL. fold L0. fold x.
      replace (L0 ++ [(r, LX_REG); x]) with ((L0 ++ [(r, LX_REG)]) ++ [x]) by (rewrite <- app_assoc; reflexivity).
      rewrite E1. rewrite <- app_assoc. reflexivity. }
    specialize (Hd Hb). subst x. unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
    rewrite c3_req in Hd by (unfold c3_nlen; lia). unfold c3_nlen in Hd. lia.
Qed.

(* The call chain free gets at sp1 (lx_achain at the point's layout). *)
Lemma c3d_achain : forall (W : world SEGS) m md, c3d_mem W m ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W m md k ->
  achain ly3 (aview SEGS (w_H W) m) (lsp1 cx) (lsp0 cx) (lch cx).
Proof.
  intros W m md (SV & _) HJ.
  pose proof HB as ((HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof (lx_sp_facts B MT cx HB) as (Hs16 & Hs0 & Hs47 & Hs1 & Hs32). pose proof asan_consts as (C1 & _).
  destruct SV as (Sra & Sj). unfold lview in Sra, Sj. cbn [c3d_cms ms_mem mkst] in Sra, Sj.
  apply (achain_ly_top (lc_ly cx) ly3 _ _ _ _ Etop).
  eapply lx_achain.
  - exact Hch.
  - unfold lsp0 in *. lia.
  - unfold lsp0 in *. lia.
  - exact (c3d_mod8 _ Hs16).
  - exact Hra4.
  - intros a Ha. apply F1; [lia | unfold LX_STK; lia].
  - exact Sra.
  - pose proof (Sj 0 ltac:(lia)) as S0. rewrite Z.mul_0_r, Z.sub_0_r in S0. rewrite S0. reflexivity.
  - lia.
Qed.

(* free's acall_kept keeps every byte the point's facts speak about: none of them lies in the freed name block
   (the stack at or above sp1 is above free's stack window; the input block, the registry and the frame are apart
   from the name block; the frame's shadow is not application memory). *)
Lemma c3d_keep_free : forall (W W2 : world SEGS) memT mem2 md slo shi,
  AR SEGS B ly3 S3 W memT md -> shi <= lsp1 cx ->
  acall_kept SEGS B ly3 S3 W memT W2 mem2 slo shi (fun a => q <= a < q + req_size (c3_nlen nm + 1)) ->
  forall a, c3d_at a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memT a.
Proof.
  intros W W2 memT mem2 md slo shi HAR Hshi (K1 & K2 & _ & K4 & _) a Ha.
  pose proof (lx_sp_facts B MT cx HB) as (Hs16 & Hs0 & Hs47 & Hs1 & Hs32).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HFG as (HF0 & HF1 & HFapp).
  assert (Hqin : In (q, c3_nlen nm + 1) (ablocks B ly3 S3))
    by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
  assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hn0 : 0 <= c3_nlen nm) by (unfold c3_nlen; lia).
  assert (Hrq : req_size (c3_nlen nm + 1) = c3_nlen nm + 1) by (apply c3_req; lia).
  rewrite Hrq in K2, K4.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q (c3_nlen nm + 1) HAR Hqin) as (_ & Hq4096 & Hqc & Hqia & _).
  rewrite Hrq in Hqc, Hqia.
  destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]].
  - apply K1; lia.
  - pose proof HB as (_ & _ & _ & Hpn & _).
    destruct Hpn as [Hn | (Hnpos & Hin0)]; [unfold lc_n in *; lia|].
    assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; left; exact Hin0).
    assert (Hne : (lc_p cx, lc_n cx) <> (q, c3_nlen nm + 1)).
    { intros E. rewrite E in Hin0. exact (c3d_q_fresh W memT md HAR Hin0). }
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W memT md _ _ _ _ HAR Hin3 Hqin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, (c3_req (lc_n cx)) in Hd by lia.
    replace a with (lc_p cx + (a - lc_p cx)) by lia.
    apply (K2 (lc_p cx) (lc_n cx) (a - lc_p cx) Hin3); [rewrite c3_req by lia; lia | lia].
  - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W memT md q (c3_nlen nm + 1) LX_CID fp HAR Hqin Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, HFeq in Hd. change (fs_frame_bytes LX_CID) with 512 in Hd.
    apply (K4 LX_CID fp a Hfin); [|lia].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFeq. change (fs_frame_bytes LX_CID) with 512. lia.
  - apply (K4 LX_CID fp a Hfin).
    + right. unfold in_zr. cbn [fst snd]. rewrite HFeq. change (fs_frame_bytes LX_CID / 8) with 64. exact Ha.
    + intros Hqa. assert (HSHe : lSH cx fp = 2147450880 + lF cx fp / 8) by reflexivity.
      apply (fshadow_not_app (lF cx fp) 64 q (c3_nlen nm + 1) a HF0 ltac:(lia) Hqia ltac:(lia) Hqa).
  - assert (Hne : (r, LX_REG) <> (q, c3_nlen nm + 1)).
    { intros E. injection E as _ E. unfold LX_REG in E. lia. }
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W memT md _ _ _ _ HAR Hrin Hqin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. change (req_size LX_REG) with 288 in Hd.
    replace a with (r + (a - r)) by lia.
    apply (K2 r LX_REG (a - r) Hrin); [change (req_size LX_REG) with 288; lia | lia].
Qed.

(* ---- 0x808b0 .. 0x808b4: a0 = s3 = the name block, free (name) ---- *)
Lemma c3d_main : forall (W3 : world SEGS) (ms3 : machine_state) md3,
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  lx_body cx fp LP_FREE W3 ms3 LSH_iter ->
  lreg W3 ms3 r c3d_bsc -> lprev cx fp W3 ms3 bs -> lcur cx W3 ms3 pos -> lslots_loop cx fp W3 ms3 r fab ->
  lslot cx W3 ms3 0x58 (Z.of_nat i) ->
  getr (ms_regs ms3) 19 = w64 q -> getr (ms_regs ms3) 20 = w64 r -> getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) ->
  getr (ms_regs ms3) 23 = w64 c3d_ren -> getr (ms_regs ms3) 27 = w64 fab ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros W3 ms3 md3 HJ HBODY RG PV CUR SL S58 G19 G20 G21 G23 G27.
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G22) & SV & SH & FL
    & S10 & S18 & S80 & GI).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof (lx_sp_facts B MT cx HB) as (Hs16 & Hs0 & Hs47 & Hs1 & Hs32).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & Hpn & _ & Hfr0 & Hev & Hlive & _ & MOK & HNEED & HTR).
  pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
  pose proof (lh_tl _ _ HY) as TL. pose proof (lh_mtl _ _ HY) as MTL. pose proof (lh_free _ _ HY) as AFREE.
  pose proof (pa_B_ok (L := boxb_listing)) as (HB0 & HB1 & HB4).
  assert (GR : c3d_regs (ms_regs ms3)) by (repeat split; assumption).
  assert (HM : c3d_mem W3 (ms_mem ms3))
    by exact (conj SV (conj SH (conj FL (conj S10 (conj S18 (conj S80 (conj GI (conj RG (conj PV (conj CUR
      (conj SL S58))))))))))).
  assert (Hms : restrict (w_H W3) ms3 =
    mkst (ms_regs ms3) (Z_to_bv 64 (BASE + LP_FREE)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
    subst. reflexivity. }
  pose proof (c3d_seat W3 (ms_regs ms3) (ms_mem ms3) LP_FREE) as HS.
  rewrite restrict_mkst_fx, <- Hms in HS.
  assert (SHOK : sh_ok SEGS C3DBx [] (Eimg (Ereg (ms_regs ms3) [])) (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (F19 : ew E 19 = w64 q) by (subst E; rewrite (c3d_ewR _ [] 19 19%bv eq_refl); exact G19).
  assert (F23 : ew E 23 = w64 c3d_ren) by (subst E; rewrite (c3d_ewR _ [] 23 23%bv eq_refl); exact G23).
  (* 0x808b0 mv a0, s3; 0x808b4 jal free: the engine stops at free's entry, the run writes no byte *)
  paj_run_tok RUN HS HJ SHOK C3Dspan; [apply awr_ok_nil |].
  cbn [ss_mem] in HF.
  pose proof (c3d_mem_same W3 (ms_mem ms3) (ms_mem ms) HM (c3d_frame_nil E _ _ HF)) as HMc.
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _).
  pmkst HS. rewrite (pal_free B TL).
  prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (23%bv : bv 5) Rs7.
  rewrite HE in HS.
  pose proof (c3d_regs_call W3 _ _ _ _ HS eq_refl GR) as GRT.
  pose proof GRT as (T2 & T8 & T9 & T3 & T4 & _).
  pose proof (pa_base_lo (L := boxb_listing)) as HBlo.
  assert (Has : ASTACK = 16384) by reflexivity.
  assert (Qsp : spZ (ms_regs ms) = lsp0 cx + (lsp1 cx - lsp0 cx))
    by (unfold spZ; rewrite T2; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (Hqin : In (q, c3_nlen nm + 1) (ablocks B ly3 S3))
    by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
  assert (Hm48 : mo_malloc MT (c3_nlen nm + 1) <= mo_malloc MT 48)
    by (apply (mo_malloc_mono MT MTL); unfold c3_nlen in *; lia).
  assert (Hai : 0 <= LX_AI MT)
    by (unfold LX_AI; pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)); pose proof (mo_free_nonneg MT MTL); lia).
  assert (Hacc1 : acc + mo_free MT <= LX_A1 MT + (Z.of_nat i + 1) * LX_AI MT) by (unfold LX_AI in *; lia).
  assert (Hm64 : (Z.of_nat i + 1) * LX_AI MT <= 64 * LX_AI MT) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (Hneed1 : acc + mo_free MT <= lc_T cx)
    by (unfold LX_NEED in HNEED; pose proof (mo_free_nonneg MT MTL); lia).
  eapply SRr_bind.
  { eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE W3 (ms_regs ms) (ms_mem ms) LX_STK (lsp0 cx) []
      (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k q (c3_nlen nm + 1)
      (lsp1 cx - lsp0 cx) (Z_to_bv 64 (BASE + C3D_RET)) (lch cx) HJ).
    - exact Hqin.
    - rewrite Ra0. exact F19.
    - exact Qsp.
    - exact (c3d_mod16 _ _ Hs32 Hs16).
    - lia.
    - rewrite Has. unfold LX_STK. lia.
    - rewrite T3. exact Hgp.
    - rewrite T4. exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [unfold C3D_RET; lia | reflexivity].
    - unfold LX_EV in Hev. lia.
    - apply (achain_chain_pre ly3 _ (lsp1 cx) (lsp0 cx)).
      + exact (c3d_achain W3 (ms_mem ms) _ HMc HJ).
      + rewrite Qsp. lia.
      + unfold s0Z. rewrite T8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + unfold raZ. rewrite Rra, unsigned_lit_small by lia. lia.
    - apply HTR. right. split; [reflexivity|]. unfold raZ. rewrite Rra, unsigned_lit_small by lia.
      replace (BASE + 2316 - BASE) with 2316 by lia. unfold LX_FSITES. left. reflexivity.
    - intros Hin. exfalso. exact (c3d_q_fresh W3 (ms_mem ms) _ HAR3 Hin).
    - apply (mok_station MT (lc_S cx) S3 (lc_T cx) acc (mo_free MT) MTL MOK HMO (mo_free_nonneg MT MTL)).
      exact Hneed1. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl1 & Ebl2) & Hfrs2 & HK2
    & MLE2 & _).
  apply (c3d_ret W2 ly2 S2 regs2 mem2 md2 (acc + mo_free MT)).
  - exact (c3d_regs_pres _ _ HP2 GRT).
  - transitivity (getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | rewrite Rs7; exact F23].
  - apply (c3d_mem_keep W3 (ms_mem ms) W2 mem2 HMc).
    apply (c3d_keep_free W3 W2 (ms_mem ms) mem2 _ (lsp0 cx + (lsp1 cx - lsp0 cx) - ASTACK)
      (lsp0 cx + (lsp1 cx - lsp0 cx)) HAR3); [lia | exact HK2].
  - exact HJ2.
  - rewrite Hfrs2. exact HFR.
  - exact (mle_station MT _ _ _ acc (mo_free MT) MTL HMO MLE2).
  - exact Hacc1.
  - unfold lblk. rewrite Ebl2. exact (c3d_last W3 (ms_mem ms) _ l1 l2 HAR3 Ebl1).
Qed.

End c.

(* ---- the segment ---- *)
Theorem c3_segD : forall POST, c3_segD_ok B MT POST.
Proof.
  intros POST i HK cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (pos & r & fab & op & idxb & q & bs & nm & HBODY & Hidxb & G19 & G23).
  destruct HBODY as (HLB & Hi & Hk & Hacc & HBL & Hq4096 & Hnl & HNM & RG & HINV & HFAB & PV & Hop3 & Hop
    & CUR & SL & S58 & G20 & G21 & G26 & G27).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as HFeq.
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HF1 & HFapp & _).
  exact (c3d_main POST i cx fp k acc ly3 S3 pos r fab op idxb q bs nm HB HFR HMO HK Hi Hk Hacc HBL Hnl HINV HFAB
    HFeq (conj HF0 (conj HF1 HFapp)) W3 ms3 md3 HJ HLB RG PV CUR SL S58 G19 G20 G21 G23 G27).
Qed.

End a.
