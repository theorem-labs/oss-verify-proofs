(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 700 of its 746 lines of code are new or changed and 885 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase3SegA.v; 765 of its 825 lines of code are new or changed and 686 lines of the source are left out. *)
(* Case 3 of the B walk of fuzz_boxreg.asan-ubsan's LLVMFuzzerTestOneInput, segment C: from the point C3_SN
   (0x80850, reac_boxreg_set_name has returned) to the point C3_FREE (0x808b0, the renaming is decided and the two
   paths meet); BoxBLxCase3Defs.v holds the points and the call premises.
   The code (offsets from 0x7ffac in the listing):
   - 0x80850 .. 0x80864: renamed = 0 <= idx < n ? idx : -1, as the compiler writes it (slti / not / slt / and /
     addi / or); its value is LLVMFuzzerTestOneInput_case3.c3_ren (c3_ren_val, of the plain walk);
   - 0x80868: renamed < 0 goes straight to 0x808b0;
   - 0x80870 and 0x80884: the two UBSan checks of r->box[idx] (idx <= 4, and r + 56 idx does not wrap), whose trap
     branches (0x80fac, `unimp`) are refuted from 0 <= idx < n and boxreg_inv's n <= 5;
   - 0x8088c .. 0x808a4: strncmp (r->box[idx].name, op & 8 ? "" : name, 31) (lib/B/Rt/StrncmpDefB.v
     abstrncmp_realizes); the abort after a nonzero answer (0x808ac) is refuted with BoxBLxCase3Defs.v's
     c3_set_name_fld (the field holds firstn 31 s and its NUL) and c3_strn_eq.
   The segment writes no byte of the walk's memory: only the interceptor writes, inside [sp1 - 2 * ESTACK, sp1).
   The engine runs on small symbolic states, one per straight-line run (the shape BoxBLxCase2.v measured). *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo BoxTailVis.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBReadName BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase3Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd printf_facts_c read_name_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

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
Let BR := paj_branch (PI := PI).
(* ---- small facts, in the shape BoxBLxCase2.v measured: one small symbolic state per straight-line run ---- *)
Lemma c3_ewR : forall (regs : bvmap 5 word) extra n (rr : bv 5),
  Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs extra)) n = getr regs rr.
Proof.
intros regs extra n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma c3_rdword_keep : forall (rd rd' : reader) a v,
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk H. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.

Lemma c3_rdword_range : forall (H : word -> bool) mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hr. unfold rdword in Hr.
repeat match type of Hr with context [aview SEGS H mem ?x] =>
  let b := fresh "b" in let Eb := fresh "Eb" in
  destruct (aview SEGS H mem x) as [b|] eqn:Eb; [|discriminate Hr];
  destruct (aview_byte SEGS H mem x b Eb) as (? & _ & _ & ?) end.
injection Hr as <-. lia.
Qed.

Lemma c3_img_atom : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = w64 (VAL n).
Proof. intros E n HE Hn. unfold w64. rewrite <- (HE n Hn). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma c3_mod8 : forall a q, a mod q = 0 -> q mod 8 = 0 -> 0 < q -> a mod 8 = 0.
Proof.
intros a q Ha Hq Hq0. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hq; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [x Hx]. destruct Hq as [y Hy]. exists (x * y). lia.
Qed.

Lemma c3_U_atom : forall E n z, ew E n = w64 z -> U E (SOff n 0) = z mod 2 ^ 64.
Proof.
intros E n z H. rewrite U_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_mod. lia.
Qed.

Lemma c3_U_lit : forall E x, U E (SLit x) = x mod 2 ^ 64.
Proof. intros E x. rewrite U_SLit. reflexivity. Qed.

Lemma c3_U_reg : forall E n w, ew E n = w -> U E (SOff n 0) = bv_unsigned w.
Proof.
intros E n w H. rewrite U_SOff, H, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 w) as R.
change (bv_modulus 64) with (2 ^ 64) in R. unfold M64. lia.
Qed.

Lemma c3_swrap : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations. lia.
Qed.

Lemma c3_S_atom : forall E n z, ew E n = w64 z -> - 2 ^ 63 <= z < 2 ^ 63 -> Sg E (SOff n 0) = z.
Proof.
intros E n z H Hz. rewrite S_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned. rewrite bv_swrap_wrap.
apply c3_swrap. exact Hz.
Qed.

Lemma c3_den0 : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. Qed.

Lemma c3_denv : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma c3_blt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.

(* The shadow base as the engine's tokens see it (no shadow token is used in this segment). *)
Definition C3SB : Z := 0x7fff8000.
Definition C3Bx : sv := SLit C3SB.
Definition C3span : Z * Z := (C3SB, C3SB + 2 ^ 44 - 1).
Section c.
(* ---- the point C3_SN's data (0x80850): the cut's witnesses, fixed for the whole segment ---- *)
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Variable cx : lxcx.
Variables fp k acc : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable pos : nat.
Variables r fab op idxb q : Z.
Variables bs nm : list byte.
Hypothesis HB : lx_base B MT cx.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HMO : mo_le MT (lc_S cx) S3 acc.
Hypothesis HNEXT : lx_from B MT POST (C3_FREE B MT i).
Hypothesis Hi : (i < 64)%nat.
Hypothesis Hk : k <= 2 + 2 * Z.of_nat i.
Hypothesis Hacc : acc <= LX_A1 MT + Z.of_nat i * LX_AI MT + mo_malloc MT (c3_nlen nm + 1).
Hypothesis HBLK : ablocks B ly3 S3 = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG); (q, c3_nlen nm + 1)].
Hypothesis Hq0 : 4096 <= q.
Hypothesis Hnm : c3_nlen nm <= 47.
Hypothesis HINV : Boxreg.boxreg_inv bs.
Hypothesis HFAB : Boxreg.bx_fabric bs = fab.
Hypothesis Hop3 : Z.land op 3 = 3.
Hypothesis Hop : 0 <= op < 256.
Hypothesis Hidxb : 0 <= idxb < 256.
(* The geometry: the two stack pointers, the frame F, the registry, the name block and the input block (from
   lx_base and AR at the cut; none of them moves in this segment, which writes no byte of them). *)
Hypothesis HGsp : lsp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= lsp0 cx <= 2 ^ 47 /\
  lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0.
Hypothesis HGF : 4096 <= lF cx fp /\ lF cx fp + 512 <= alloc_ceiling /\ lF cx fp mod 64 = 0 /\
  in_app (lF cx fp) 512 /\ frame_addr ly3 LX_CID fp = lF cx fp.
Hypothesis HGr : r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ In (r, LX_REG) (ablocks B ly3 S3) /\
  in_app r 288.
Hypothesis HGq : In (q, c3_nlen nm + 1) (ablocks B ly3 S3) /\ q + c3_nlen nm + 1 <= alloc_ceiling.
Hypothesis HGin : lc_n cx = 0 \/ (0 < lc_n cx /\ 4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling).

(* The string set_name wrote into the row's name field, the row it renamed, and the registry's bytes after it. *)
#[local] Notation SSTR := (c3_sel_s op nm).
#[local] Notation BSC := (tbreac_boxreg_set_name_bytes bs (c3_sext8 idxb) (c3_sel_s op nm)).
#[local] Notation XI := (c3_sext8 idxb).
#[local] Notation NN := (Boxreg.bx_n bs).

Definition cms (m : word -> option byte) : machine_state := mkst (lc_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).

(* What C3_body says about the memory (it is the same at C3_SN and at C3_FREE: the segment writes no byte of it). *)
Definition c3_mem (m : word -> option byte) : Prop :=
  lsaved cx W3 (cms m) /\ lshadow cx fp W3 (cms m) LSH_iter /\
  rdword (aview SEGS (w_H W3) m) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) /\
  lslot cx W3 (cms m) 0x10 (lF cx fp) /\ lslot cx W3 (cms m) 0x18 (lF cx fp) /\
  lslot cx W3 (cms m) 0x80 (lF cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) m) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) /\
  (forall j, 0 <= j <= c3_nlen nm ->
     aview SEGS (w_H W3) m (q + j) = Some (bv_unsigned (nth (Z.to_nat j) (nm ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) /\
  lreg W3 (cms m) r BSC /\ lprev cx fp W3 (cms m) bs /\
  lcur cx W3 (cms m) pos /\ lslots_loop cx fp W3 (cms m) r fab /\ lslot cx W3 (cms m) 0x58 (Z.of_nat i).

(* The bytes those facts speak about. Every one of them lies at or above sp1, or below the allocator's ceiling;
   the only writer of the segment, the strncmp interceptor, writes inside [sp1 - 2 * ESTACK, sp1). *)
Definition c3_at (a : Z) : Prop :=
  lsp1 cx <= a < 2 ^ 64 \/ lc_p cx <= a < lc_p cx + lc_n cx \/ lF cx fp <= a < lF cx fp + 512 \/
  lSH cx fp <= a < lSH cx fp + 64 \/ r <= a < r + 288 \/ q <= a <= q + c3_nlen nm.

Definition c3_J (m : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m md k.

(* The registers every point of the segment keeps (s11 = fab is reloaded at 0x808a8, s7 changes at 0x80864). *)
Definition c3_regs (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lsp1 cx) /\ getr regs 8 = w64 (lsp0 cx) /\ getr regs 9 = w64 (lsp1 cx) /\
  getr regs 3 = getr (lc_regs cx) 3 /\ getr regs 4 = getr (lc_regs cx) 4 /\
  getr regs 18 = w64 SHADOW_OFF /\ getr regs 22 = w64 (lSH cx fp) /\
  getr regs 19 = w64 q /\ getr regs 20 = w64 r /\ getr regs 21 = w64 (lF cx fp + 64) /\
  getr regs 26 = w64 NN.

Lemma c3_ar : forall m md, c3_J m md -> AR SEGS B ly3 S3 W3 m md.
Proof. intros m md HJ. exact (proj1 HJ). Qed.

(* The frame's shadow lies below the allocator's ceiling and apart from the frame. *)
Lemma c3_SH : lSH cx fp = SHADOW_OFF + lF cx fp / 8 /\ 0 <= lF cx fp / 8 /\ lSH cx fp + 64 <= alloc_ceiling /\
  (lF cx fp + 512 <= SHADOW_OFF \/ lSH cx fp + 64 <= lF cx fp).
Proof.
pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _). pose proof asan_consts as (C1 & _).
assert (E : lSH cx fp = SHADOW_OFF + lF cx fp / 8) by reflexivity.
assert (D0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
assert (D1 : 8 * (lF cx fp / 8) <= lF cx fp) by (apply Z.mul_div_le; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold SHADOW_OFF in *.
split; [exact E|]. split; [exact D0|].
destruct HFapp as [_ [Hlo | [Hhi1 Hhi2]]].
- assert (lF cx fp / 8 <= 268430848) by (apply Z.div_le_upper_bound; lia). split; [lia|]. left. lia.
- assert (lF cx fp / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). split; [lia|]. right. lia.
Qed.

Lemma c3_at_rng : forall a, c3_at a -> 0 <= a < 2 ^ 64 /\ (a + 8192 < lsp1 cx \/ lsp1 cx <= a).
Proof.
intros a Ha. pose proof HGsp as (_ & Hs0 & Hs1 & _). pose proof HGF as (HF0 & HF1 & _).
pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof HGq as (_ & Hq1).
pose proof c3_SH as (ESH & D0 & HSH1 & _). pose proof asan_consts as (C1 & _).
unfold c3_at in Ha. unfold SHADOW_OFF in ESH. unfold c3_nlen in *.
destruct HGin as [Hn0 | (Hn1 & Hp0 & Hp1)];
  destruct Ha as [H|[H|[H|[H|[H|H]]]]]; split; unfold lc_n in *; lia.
Qed.
(* The facts of c3_mem are reads at c3_at addresses: a change outside them keeps every one. *)
Lemma c3_mem_keep : forall m m', c3_mem m ->
  (forall a, c3_at a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) -> c3_mem m'.
Proof.
intros m m' (SV & SH & FL & S10 & S18 & S80 & GI & QB & RG & PV & CUR & SL & S58) KP.
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _).
pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof HGq as (_ & Hq1).
pose proof c3_SH as (ESH & D0 & HSH1 & HSH2). pose proof asan_consts as (C1 & _).
assert (Hfb : fs_frame_bytes LX_CID = 512) by reflexivity.
assert (KS : forall off v, 0 <= off -> off + 8 <= 0x98 -> lslot cx W3 (cms m) off v -> lslot cx W3 (cms m') off v).
{ intros off v H0 H1 H. unfold lslot, lview in *. cbn [cms ms_mem mkst] in *.
  eapply (c3_rdword_keep _ _ _ v); [|exact H]. intros z Hz. apply KP. left. lia. }
unfold c3_mem. cbn [cms ms_mem mkst] in *.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]].
- destruct SV as (Sra & Sj). unfold lsaved, lview in *. cbn [ms_mem mkst] in *. split.
  + eapply (c3_rdword_keep _ _ _ _); [|exact Sra]. intros z Hz. apply KP. left. lia.
  + intros j Hj. eapply (c3_rdword_keep _ _ _ _); [|exact (Sj j Hj)]. intros z Hz. apply KP. left. lia.
- intros z Hz. unfold lview in *. cbn [ms_mem mkst] in *. rewrite KP; [exact (SH z Hz)|].
  right; right; right; left. assert (Z.of_nat (length LSH_iter) = 52) by reflexivity. lia.
- rewrite Hfb in *. eapply (c3_rdword_keep _ _ _ _); [|exact FL]. intros z Hz.
  apply KP. right; right; left. lia.
- apply KS; [lia | lia | exact S10].
- apply KS; [lia | lia | exact S18].
- apply KS; [lia | lia | exact S80].
- apply (garr8_frame SEGS _ _ _ _ GI). intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview SEGS).
  apply KP. right; left. unfold lc_n in *. lia.
- intros j Hj. rewrite KP; [exact (QB j Hj)|]. right; right; right; right; right. lia.
- intros z Hz. unfold lreg, lview in *. cbn [ms_mem mkst] in *. rewrite KP; [exact (RG z Hz)|].
  right; right; right; right; left. unfold LX_REG in Hz. lia.
- intros z Hz. unfold lprev, lview in *. cbn [ms_mem mkst] in *. rewrite KP; [exact (PV z Hz)|].
  right; right; left. unfold LX_REG in Hz. lia.
- destruct CUR as (Hp & C88 & C90). split; [exact Hp|]. split; apply KS; first [lia | assumption].
- destruct SL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
  repeat split; apply KS; first [lia | assumption].
- apply KS; [lia | lia | exact S58].
Qed.

(* A run that wrote nothing keeps the memory. *)
Lemma c3_mem_same : forall m m', c3_mem m -> (forall x, m' x = m x) -> c3_mem m'.
Proof.
intros m m' H E. apply (c3_mem_keep m m' H). intros a _. unfold aview, mbyte, mrestrict. rewrite E. reflexivity.
Qed.
(* ---- the registers across a run and across a call ---- *)
Lemma c3_regs_same : forall regs regs',
  (forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26] -> getr regs' (Z_to_bv 5 n) = getr regs (Z_to_bv 5 n)) ->
  c3_regs regs -> c3_regs regs'.
Proof.
intros regs regs' K (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G19 & G20 & G21 & G26). unfold c3_regs.
split; [etransitivity; [exact (K 2 ltac:(repeat (first [left; reflexivity | right]))) | exact G2]|].
split; [etransitivity; [exact (K 8 ltac:(repeat (first [left; reflexivity | right]))) | exact G8]|].
split; [etransitivity; [exact (K 9 ltac:(repeat (first [left; reflexivity | right]))) | exact G9]|].
split; [etransitivity; [exact (K 3 ltac:(repeat (first [left; reflexivity | right]))) | exact G3]|].
split; [etransitivity; [exact (K 4 ltac:(repeat (first [left; reflexivity | right]))) | exact G4]|].
split; [etransitivity; [exact (K 18 ltac:(repeat (first [left; reflexivity | right]))) | exact G18]|].
split; [etransitivity; [exact (K 22 ltac:(repeat (first [left; reflexivity | right]))) | exact G22]|].
split; [etransitivity; [exact (K 19 ltac:(repeat (first [left; reflexivity | right]))) | exact G19]|].
split; [etransitivity; [exact (K 20 ltac:(repeat (first [left; reflexivity | right]))) | exact G20]|].
split; [etransitivity; [exact (K 21 ltac:(repeat (first [left; reflexivity | right]))) | exact G21]|].
etransitivity; [exact (K 26 ltac:(repeat (first [left; reflexivity | right]))) | exact G26].
Qed.

Lemma c3_regs_pres : forall regs regs', aregs_preserved regs regs' -> c3_regs regs -> c3_regs regs'.
Proof.
intros regs regs' HP. apply c3_regs_same. intros n Hn. apply HP. unfold acallee_saved. cbv [In] in Hn. lia.
Qed.

Lemma c3_regs_run : forall regs extra ss (ms : machine_state),
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) ss (restrict (w_H W3) ms) ->
  forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26]) = true ->
  c3_regs regs -> c3_regs (ms_regs ms).
Proof.
intros regs extra ss ms HS Hl. apply c3_regs_same. intros n Hn.
apply (regs_kept_of_st_ok_pi _ ss (restrict (w_H W3) ms) regs extra
  (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26]) HS); [| exact Hl | apply in_map; exact Hn].
split; [intros z Hz; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma c3_regs_call : forall regs extra ss (ms : machine_state),
  st_ok SEGS (Eimg (Ereg regs extra)) ss (restrict (w_H W3) ms) ->
  forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26]) = true ->
  c3_regs regs -> c3_regs (ms_regs ms).
Proof.
intros regs extra ss ms HS Hl. apply c3_regs_same. intros n Hn.
pose proof (regs_kept_of_st_ok SEGS _ ss (restrict (w_H W3) ms) regs extra
  (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26]) HS) as K.
cbn [restrict ms_regs] in K. apply K; [| exact Hl | apply in_map; exact Hn].
split; [intros z Hz; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* A small symbolic state: the registers as atoms 0 .. 31 (and `extra` from 32 on), the regions rs. *)
Lemma c3_seat : forall (regs : bvmap 5 word) extra m pc rs G,
  regions_wf rs = true -> Forall (region_ok SEGS (Eimg (Ereg regs extra)) (mrestrict (w_H W3) m)) rs ->
  pairwise_disjoint (Eimg (Ereg regs extra)) rs -> facts_ok (Eimg (Ereg regs extra)) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) (mkSS pc sr_atoms rs None G)
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
intros regs extra m pc rs G Hwf Hok Hd HG. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hok | exact Hd | exact HG].
Qed.

(* A run whose regions are all read-only writes no byte. *)
Lemma c3_frame_ro : forall E rs m m', forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs = true ->
  frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (rg & Hin & Ha).
rewrite forallb_forall in Hro. specialize (Hro rg Hin). apply Z.leb_le in Hro. lia.
Qed.

Ltac c3_ro HM :=
  lazymatch type of HM with c3_mem ?m0 =>
  match goal with HF : frame_of _ ?rs m0 ?m1 |- _ =>
    let H := fresh "HM" in
    pose proof (c3_mem_same m0 m1 HM (c3_frame_ro _ rs m0 m1 eq_refl HF)) as H; clear HM; rename H into HM
  end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* A read-only spill slot of the machine frame, at the atom of s1 (= sp1). *)
Definition c3_rs (off : Z) (e : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 e)].

Lemma c3_rs_ok : forall E m off e v, bv_unsigned (ew E 9) = lsp1 cx ->
  lslot cx W3 (cms m) off v -> sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= off -> off + 8 <= 0x98 ->
  region_ok SEGS E (mrestrict (w_H W3) m) (c3_rs off e).
Proof.
intros E m off e v H9 Hs He Hv H0 H1. pose proof HGsp as (_ & Hs0 & Hs1 & _).
unfold region_ok, c3_rs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (lsp1 cx) off 8 e v He); [cbn; lia | cbn; lia |].
apply (val_mem_of_rdword SEGS (w_H W3) m). exact Hs.
Qed.

(* The fact on sp1 the engine's loads at s1 use. *)
Definition C3_AF9 : nat * afact := (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5).
Lemma c3_af9 : forall E, bv_unsigned (ew E 9) = lsp1 cx -> afact_ok E (fst C3_AF9) (snd C3_AF9).
Proof.
intros E H9. pose proof HGsp as (_ & Hs0 & Hs1 & Hs32). pose proof asan_consts as (C1 & _).
unfold afact_ok, C3_AF9. cbn [fst snd af_lo af_hi af_al2]. rewrite H9. change (2 ^ 5) with 32.
split; [lia|]. split; [exact Hs32 | lia].
Qed.
(* ---- the point C3_FREE (0x808b0): the segment's landing ---- *)
Lemma c3_FREE_pt : forall regs m md,
  c3_regs regs -> getr regs 23 = w64 (c3_ren XI NN) -> getr regs 27 = w64 fab ->
  c3_mem m -> c3_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + LP_FREE)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G19 & G20 & G21 & G26) G23 G27
  (SV & SH & FL & S10 & S18 & S80 & GI & QB & RG & PV & CUR & SL & S58) HJ.
apply (HNEXT cx fp k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + LP_FREE)) m (seg_rom SEGS)) md HB HJ HFR HMO).
exists pos, r, fab, op, idxb, q, bs, nm.
split; [|split; [exact Hidxb|]; split; [exact G19 | exact G23]].
unfold C3_body.
split.
{ unfold lx_body. do 6 (split; [reflexivity|]).
  split; [exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 G22))))))|].
  split; [exact SV|]. split; [exact SH|]. split; [exact FL|].
  split; [exact S10|]. split; [exact S18|]. split; [exact S80 | exact GI]. }
split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|].
split; [exact HBLK|]. split; [exact Hq0|]. split; [exact Hnm|].
split; [exact QB|].
split; [exact RG|]. split; [exact HINV|]. split; [exact HFAB|]. split; [exact PV|].
split; [exact Hop3|]. split; [exact Hop|].
split; [exact CUR|]. split; [exact SL|]. split; [exact S58|].
split; [exact G20|]. split; [exact G21|]. split; [exact G26 | exact G27].
Qed.
Definition C3_RET : Z := 0x8fc.


Lemma c3_RET_pt : forall regs m md,
  c3_regs regs -> getr regs 23 = w64 XI -> 0 <= XI < NN -> bv_unsigned (getr regs 10) = 0 ->
  c3_mem m -> c3_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C3_RET)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md GR G23 HX G10 HM HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G19 & G20 & G21 & G26).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SL & _).
pose proof SL as (_ & _ & S30 & _).
assert (Hfab : 0 <= fab < 2 ^ 64) by exact (c3_rdword_range _ _ _ _ S30).
set (ex := [w64 fab]).
set (E := Eimg (Ereg regs ex)).
assert (EX : forall j, (j < 1)%nat -> ew E (32 + j) = nth j ex (w64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs ex j)).
assert (F32 : ew E 32 = w64 fab) by exact (EX 0%nat ltac:(lia)).
assert (U9 : bv_unsigned (ew E 9) = lsp1 cx)
  by (unfold E; rewrite (c3_ewR regs ex 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (F10 : ew E 10 = getr regs 10) by (unfold E; exact (c3_ewR regs ex 10 10%bv eq_refl)).
assert (F23 : ew E 23 = w64 XI) by (unfold E; rewrite (c3_ewR regs ex 23 23%bv eq_refl); exact G23).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HE : E = Eimg (Ereg regs ex)) by reflexivity.
clearbody E ex.
assert (HS : st_ok_pi SEGS VAL E (mkSS C3_RET sr_atoms [c3_rs 0x30 (SOff 32 0)] None (mkFacts [C3_AF9] [] []))
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + C3_RET)) m (seg_rom SEGS)))).
{ rewrite HE. apply c3_seat; [vm_compute; reflexivity | | | ]; rewrite <- HE.
  - constructor; [|constructor].
    apply (c3_rs_ok E m 0x30 (SOff 32 0) fab U9 S30 (c3_den0 E 32 _ F32) Hfab); lia.
  - unfold c3_rs. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. tauto.
  - split; [cbn [f_atoms atoms_ok]; split; [exact (c3_af9 E U9) | exact I] | split; exact I]. }
assert (SHOK : sh_ok SEGS C3Bx [] E (mrestrict (w_H W3) m)) by constructor.
unfold c3_J in HJ.
paj_run_tok RUN HS HJ SHOK C3span; [awr_ok_tac |]. c3_ro HM.
(* bnez a0 (0x808ac): a nonzero strncmp aborts *)
psrr_branch_tok RUN BR HS SHOK C3span; rewrite branch_ne_U, (c3_U_reg E 10 _ F10), c3_U_lit, G10 in Hc.
{ vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK C3span LP_FREE; [awr_ok_tac |]. c3_ro HM.
pmkst HS.
prreg HS (23%bv : bv 5) R23. prreg HS (27%bv : bv 5) R27.
rewrite HE in HS.
apply (c3_FREE_pt _ _ _ (c3_regs_run _ _ _ _ HS eq_refl GR)).
- rewrite R23, F23. unfold c3_ren, LLVMFuzzerTestOneInput_case3.c3_ren.
  replace (0 <=? XI) with true by (symmetry; apply Z.leb_le; lia).
  replace (XI <? NN) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- rewrite R27, F32. reflexivity.
- exact HM.
- exact HJ.
Qed.
Lemma c3_o16 : (lsp1 cx - lsp0 cx) mod 16 = 0.
Proof.
pose proof HGsp as (Hs16 & _ & _ & Hs32).
apply Z.mod_divide in Hs16; [|lia]. apply Z.mod_divide in Hs32; [|lia]. apply Z.mod_divide; [lia|].
destruct Hs16 as [x Hx]. destruct Hs32 as [y Hy]. exists (2 * y - x). lia.
Qed.

Lemma c3_gptp : getr (lc_regs cx) 3 = w64 (as_gp B) /\ getr (lc_regs cx) 4 = w64 (as_tp B).
Proof. pose proof HB as ((_ & _ & _ & Hgp & Htp & _) & _). split; assumption. Qed.

(* The read-only data as the cut's journal keeps it. *)
Lemma c3_rodata : forall m md, c3_J m md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) m).
Proof.
intros m md HJ. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
exact (lx_arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO).
Qed.

(* ---- the strncmp interceptor (lib/B/Rt/StrncmpDefB.v abstrncmp_realizes, through the cut's journal) ----
   The two read-only premises of the contract that no cut, AR or journal gives are discharged HERE, in one place
   (the two lines marked (PREMISE)).
   - The FROZEN walk interface (pa ce9883a29ab, on this branch) states them as a Theorem Labs lane's `abfm_rom_viewN W mem`
     and `abfm_rom_viewO W mem`: rom_viewN is lx_base's arodata_okP read at a read-only byte that is no
     allocator-owned static and no errno byte (the journal keeps it: c3_rodata), and rom_viewO comes from AR at the
     call and BLxLib's blx_pinned (every owned read-only byte is a const cell carrying the image's word). *)
Lemma c3_strncmp_call : forall (regsT : bvmap 5 word) memT mdT x y (l1 l2 : list Z) raw,
  c3_J memT mdT -> c3_regs regsT -> c3_mem memT ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 31 -> getr regsT 1 = raw ->
  YK0s.ret_ok raw ->
  abfm_cstr_ok SEGS W3 memT x l1 -> abfm_cstr_ok SEGS W3 memT y l2 ->
  (forall (regs2 : bvmap 5 word) mem2 md2, c3_J mem2 md2 -> aregs_preserved regsT regs2 -> c3_mem mem2 ->
     (bv_unsigned (getr regs2 10) = 0 <-> abfm_strn_eq 31 l1 l2) ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) (POST cx)) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_strncmp)) memT (seg_rom SEGS)) mdT)
    (POST cx).
Proof.
intros regsT memT mdT x y l1 l2 raw HJ GR HM H10 H11 H12 Hra Hraw HX HY2 KONT.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & _).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof asan_consts as (C1 & _).
pose proof c3_gptp as (Hgp & Htp).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & HSTAT & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HB as ((_ & _ & _ & _ & _ & Hstk & _) & _ & _ & _ & _ & Hfr0 & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _). fold (lsp0 cx) in Hslo, Hshi.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : spZ regsT = lsp0 cx + (lsp1 cx - lsp0 cx)).
{ unfold spZ. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hsp1 : spZ regsT = lsp1 cx) by lia.
assert (HPRE : abfm_ecall_pre_k SEGS B ABFM_STK_RT_STR ly3 S3 W3 regsT memT mdT).
{ split.
  { eapply (ecall_pre_at SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
      [(LX_CID, fp)] ly3 S3 W3 memT mdT k regsT (lsp1 cx - lsp0 cx) HJ Hsp c3_o16 ltac:(lia)
      ltac:(unfold LX_STK; rewrite Hes; lia));
      [rewrite Hra; exact Hraw | rewrite G3; exact Hgp | rewrite G4; exact Htp]. }
  unfold ABFM_STK_RT_STR, ASAN_CEIL. rewrite Eslo, Hes, Hsp1. unfold LX_STK in Hslo.
  split; [lia|]. split; [lia|].
  intros a Ha. apply HPRES. unfold LX_STK. lia. }
eapply SRr_bind.
{ exact (lh_strncmp B MT HY ly3 S3 W3 regsT memT mdT x y 31 l1 l2 HPRE
    (* (PREMISE) rom_viewN: lx_base's arodata_okP, which the cut's journal keeps *)
    (lx_rom_viewN B W3 memT (c3_rodata memT mdT HJ))
    (* (PREMISE) rom_viewO: AR at the call and BLxLib's blx_pinned *)
    (lx_rom_viewO B ly3 S3 W3 memT mdT (blx_pinned B (lh_glob B MT HY)) HAR)
    H10 H11 H12 ltac:(lia) HX HY2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hmat & Hv10 & Hv & Hcmp & Hfr & Hpres2).
assert (HJ2 : c3_J mem2 md2).
{ unfold c3_J.
  eapply (ajournal_after_write SEGS B LAWS pa_segs_low LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx)
    (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 W3 memT mdT k mem2 md2
    (fun a => spZ regsT - ABFM_STK_RT_STR <= a < spZ regsT) S3 [(LX_CID, fp)] HJ).
  - intros a Ha Hna. exact (Hfr a Ha Hna).
  - exact Hpres2.
  - exact Hmat.
  - intros a Ha. left. left. unfold ABFM_STK_RT_STR in Ha. rewrite Hsp1, Hes in Ha. unfold LX_STK. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - rewrite HFR, Hfr0. reflexivity.
  - exact HQT. }
assert (HM2 : c3_mem mem2).
{ apply (c3_mem_keep memT mem2 HM). intros a Ha. destruct (c3_at_rng a Ha) as [Hr Hw].
  apply Hfr; [exact Hr|]. unfold ABFM_STK_RT_STR. rewrite Hsp1, Hes. lia. }
replace (cfg_at SEGS (raZ regsT) regs2 mem2 md2) with (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2)
  by (unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
apply (KONT regs2 mem2 md2 HJ2 HP HM2).
rewrite Hv10. unfold w64. rewrite unsigned_lit_small by lia.
change (Z.to_nat 31) with 31%nat in Hcmp. exact Hcmp.
Qed.
(* ---- the image's globals the segment reads: "" (A_OBJ 5), strncmp's second string when op & 8 <> 0 ---- *)
Lemma c3_gshadow : forall g sz m md, In (g, sz) LX_GLOBS -> c3_J m md ->
  aview SEGS (w_H W3) m (shadow_addr (VAL (A_OBJ g))) = Some sz.
Proof.
intros g sz m md Hin HJ. destruct (c3_ar m md HJ) as (M & _).
pose proof (am_const _ _ _ _ M) as C. rewrite Forall_forall in C.
assert (Hc : In (z1 (ANum (shadow_addr (VAL (A_OBJ g)))) sz) (as_const B ly3)).
{ apply (blx_cells B (lh_glob B MT HY) ly3). unfold lx_glob_cells. apply in_flat_map.
  exists (g, sz). split; [exact Hin|]. cbn [fst snd]. left. reflexivity. }
assert (Hsz : 0 <= sz < 256)
  by (cbv [LX_GLOBS In] in Hin; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]); destruct Hin).
specialize (C _ Hc). unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. rewrite C. f_equal.
unfold le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. exact Hsz.
Qed.

Lemma c3_gra : forall g sz m md, In (g, sz) LX_GLOBS -> 0 <= sz < 8 -> c3_J m md ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (VAL (A_OBJ g)) sz.
Proof.
intros g sz m md Hin Hsz HJ. apply range_addressable_partial; [exact (c3_gshadow g sz m md Hin HJ) | | exact Hsz].
apply (c3_mod8 _ 32); [exact (blx_al B (lh_glob B MT HY) (g, sz) Hin) | reflexivity | lia].
Qed.

Lemma c3_ghull : forall g sz m md, In (g, sz) LX_GLOBS -> 0 < sz -> c3_J m md ->
  shadow_hull_vis (aview SEGS (w_H W3) m) (VAL (A_OBJ g)) sz.
Proof.
intros g sz m md Hin Hsz HJ. destruct (blx_marg B (lh_glob B MT HY) (g, sz) Hin) as [M1 M2]. cbn [fst snd] in *.
eapply ro_hull; [exact (blx_isv B (lh_glob B MT HY)) | exact (c3_ar m md HJ) | exact Hsz | exact M1 | exact M2].
Qed.
Lemma c3_empty_ok : forall m md, c3_J m md -> abfm_cstr_ok SEGS W3 m (VAL (A_OBJ 5)) [].
Proof.
intros m md HJ.
pose proof (lh_glob B MT HY) as GL. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hg : In (5%nat, 1) LX_GLOBS) by (unfold LX_GLOBS; cbn [In]; tauto).
pose proof (blx_al B GL _ Hg) as Hal. pose proof (blx_marg B GL _ Hg) as Hmg. cbn [fst snd] in Hal, Hmg.
pose proof (lx_rom_viewN B W3 m (c3_rodata m md HJ)) as HRVN.
pose proof (blx_rom_bytes B GL (5%nat, [0]) ltac:(unfold LX_GLOB_BYTES; cbn [In]; tauto)) as Hrb.
cbn [fst snd] in Hrb.
pose proof (proj2 (proj1 (blx_rom_strs B GL))) as Hstr.
set (p := VAL (A_OBJ 5)) in *.
assert (Hp8 : p mod 8 = 0) by (apply (c3_mod8 _ 32); [exact Hal | reflexivity | lia]).
assert (Hb0 : aview SEGS (w_H W3) m p = Some 0).
{ destruct (Hrb 0 ltac:(cbn; lia)) as (Hrom & Ho & He & Hv). rewrite Z.add_0_r in Hrom, Ho, He, Hv.
  rewrite (HRVN _ Hrom Ho He), Hv. reflexivity. }
unfold IMG_HI in Hmg.
destruct (c3_val_mem1 W3 m p 0 Hb0) as [Hvm Hr].
split; [split|].
- intros j Hj. cbn [app length] in Hj |- *. destruct j as [|j]; [|exfalso; lia].
  cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. split; [exact Hvm | lia].
- apply Forall_nil.
- cbn [length Z.of_nat].
  split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
  split; [unfold amem_range, kLowMemEnd; left; lia|].
  split; [exact (c3_gra 5 1 m md Hg ltac:(lia) HJ)|].
  split; [exact (c3_ghull 5 1 m md Hg ltac:(lia) HJ)|].
  intros a Ha. rewrite Z.add_0_r, Hp8, Z.sub_0_r in Ha.
  destruct (Hstr a) as (Hrom & Hsr).
  { unfold absn_word_end. cbn [length Z.of_nat]. rewrite Z.add_0_r, Hp8, Z.sub_0_r. lia. }
  exact (lx_aview_some _ _ a Hsr).
Qed.
Lemma c3_NN : 0 <= NN <= 5.
Proof. pose proof HINV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1. exact HB1. Qed.

Lemma c3_sstr_pos : Forall (fun c => 0 < c < 256) (c3_sel_s op nm).
Proof.
unfold c3_sel_s. destruct (Z.land op 8 =? 0); [apply c3_cstr_pos | apply Forall_nil].
Qed.
Lemma c3_fldb : forall j, 0 <= nth j (firstn 31 (c3_sel_s op nm) ++ [0]) 0 < 256.
Proof.
intros j. pose proof c3_sstr_pos as HP. rewrite Forall_forall in HP.
destruct (Nat.lt_ge_cases j (length (firstn 31 (c3_sel_s op nm)))) as [Hj | Hj].
- rewrite app_nth1 by exact Hj.
  assert (H1 : In (nth j (firstn 31 (c3_sel_s op nm)) 0) (firstn 31 (c3_sel_s op nm))) by (apply nth_In; exact Hj).
  assert (H2 : In (nth j (firstn 31 (c3_sel_s op nm)) 0)
                  (firstn 31 (c3_sel_s op nm) ++ skipn 31 (c3_sel_s op nm))) by (apply in_or_app; left; exact H1).
  rewrite firstn_skipn in H2. specialize (HP _ H2). lia.
- rewrite app_nth2 by exact Hj.
  destruct (j - length (firstn 31 (c3_sel_s op nm)))%nat as [|u];
    [cbn [nth]; lia | rewrite nth_overflow by (cbn [length]; lia); lia].
Qed.

Lemma c3_fld_ok : forall m md, c3_J m md -> c3_mem m -> 0 <= XI < NN ->
  abfm_cstr_ok SEGS W3 m (r + 56 * XI + 24) (firstn 31 (c3_sel_s op nm)).
Proof.
intros m md HJ HM HX. pose proof c3_NN as HN.
pose proof HGr as (_ & _ & _ & HRIN & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & RG & _).
unfold lreg, lview in RG. cbn [cms ms_mem mkst] in RG.
apply (c3_cstr_ok_fld B MT HY ly3 S3 W3 m md r XI (c3_sel_s op nm) (c3_ar m md HJ) HRIN ltac:(lia) c3_sstr_pos).
- intros j Hj.
  assert (Hlen : (length (firstn 31 (c3_sel_s op nm) ++ [0%Z]) <= 32)%nat)
    by (rewrite length_app, length_firstn; cbn [length]; lia).
  replace (r + 56 * XI + 24 + Z.of_nat j) with (r + (56 * XI + 24 + Z.of_nat j)) by lia.
  rewrite RG by (unfold LX_REG; lia).
  replace (Z.to_nat (56 * XI + 24 + Z.of_nat j)) with (Z.to_nat (56 * XI + 24) + j)%nat by lia.
  rewrite (c3_set_name_fld bs XI (c3_sel_s op nm) j HINV ltac:(lia) Hj).
  pose proof (c3_fldb j) as Hb. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. lia.
- intros z Hz. rewrite RG by exact Hz. discriminate.
Qed.

Lemma c3_name_ok_q : forall m md, c3_J m md -> c3_mem m -> Z.land op 8 = 0 ->
  abfm_cstr_ok SEGS W3 m q (c3_sel_s op nm).
Proof.
intros m md HJ HM H8.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & QB & _).
pose proof HGq as (HQIN & _).
unfold c3_sel_s. replace (Z.land op 8 =? 0) with true by (symmetry; apply Z.eqb_eq; exact H8).
exact (c3_cstr_ok_name B MT HY ly3 S3 W3 m md q nm (c3_ar m md HJ) HQIN Hnm QB).
Qed.
Lemma c3_land8 : Z.land op 8 = 0 \/ Z.land op 8 = 8.
Proof.
assert (H : forallb (fun z => (Z.land z 8 =? 0) || (Z.land z 8 =? 8)) (map Z.of_nat (seq 0 256)) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in H.
assert (Hin : In op (map Z.of_nat (seq 0 256)))
  by (apply in_map_iff; exists (Z.to_nat op); split; [lia|]; apply in_seq; lia).
specialize (H _ Hin). apply orb_true_iff in H. destruct H as [H | H]; [left | right]; apply Z.eqb_eq; exact H.
Qed.
Lemma c3_U_off : forall E n z c, ew E n = w64 z -> 0 <= z < 2 ^ 64 -> U E (SOff n c) = (z + c) mod 2 ^ 64.
Proof.
intros E n z c H Hz. rewrite U_SOff, H. unfold w64. rewrite unsigned_lit_small by lia. unfold zcanon, M64. reflexivity.
Qed.

(* a0 at the jal of 0x808a4: r + 56 idx + 24, the renamed row's name field, as the engine leaves it. *)
Lemma c3_a0 : forall E z, ew E 20 = w64 r -> ew E 24 = w64 z -> 0 <= z <= 4 ->
  alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned (ew E 20) + 24)) (mul_div M_MUL (ew E 24) (Z_to_bv 64 56)) =
  w64 (r + 56 * z + 24).
Proof.
intros E z H20 H24 Hz. pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof asan_consts as (C1 & _).
assert (D : alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned (ew E 20) + 24)) (mul_div M_MUL (ew E 24) (Z_to_bv 64 56)) =
  sv_denot E (SAlu ALU_ADD (SOff 20 24) (SMd M_MUL (SOff 24 0) (SLit 56))))
  by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rewrite D, denot_lit_U, U_SAlu, U_SMd, (c3_U_off E 20 r 24 H20 ltac:(lia)), (c3_U_atom E 24 z H24), c3_U_lit.
cbn [zalu_raw zmd_raw]. rewrite (Z.mod_small z), (Z.mod_small 56), (Z.mod_small (r + 24)) by lia.
unfold zcanon, M64. rewrite (Z.mod_small (z * 56)) by lia. rewrite (Z.mod_small (r + 24 + z * 56)) by lia.
unfold w64. f_equal. lia.
Qed.
Definition C3_P1 : Z := 0x8bc.


Lemma c3_P1_pt : forall regs m md,
  c3_regs regs -> getr regs 23 = w64 (c3_ren XI NN) -> getr regs 24 = w64 idxb ->
  getr regs 25 = w64 (Z.land op 8) -> getr regs 27 = w64 fab ->
  c3_mem m -> c3_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C3_P1)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md GR G23 G24 G25 G27 HM HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G19 & G20 & G21 & G26).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGr as (Hr16 & Hr0 & Hr1 & HRIN & _).
pose proof asan_consts as (C1 & _). pose proof c3_NN as HN.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SL & _).
pose proof SL as (_ & _ & _ & _ & _ & _ & S70 & _).
assert (Hren : c3_ren XI NN = -1 \/ (0 <= XI < NN /\ c3_ren XI NN = XI /\ XI = idxb)).
{ unfold c3_ren, LLVMFuzzerTestOneInput_case3.c3_ren, c3_sext8 in *.
  destruct (Z.ltb_spec idxb 128) as [Hlt | Hge].
  - destruct (Z.leb_spec 0 idxb) as [A | A]; [|lia].
    destruct (Z.ltb_spec idxb NN) as [Hb | Hb]; cbn [andb]; [right; split; [lia|]; split; reflexivity | left; reflexivity].
  - replace (0 <=? idxb - 256) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb]. left. reflexivity. }
set (ex := [w64 (2 ^ 64 - 1 - r)]).
set (E := Eimg (Ereg regs ex)).
assert (EX : forall j, (j < 1)%nat -> ew E (32 + j) = nth j ex (w64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs ex j)).
assert (F32 : ew E 32 = w64 (2 ^ 64 - 1 - r)) by exact (EX 0%nat ltac:(lia)).
assert (U9 : bv_unsigned (ew E 9) = lsp1 cx)
  by (unfold E; rewrite (c3_ewR regs ex 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (F19 : ew E 19 = w64 q) by (unfold E; rewrite (c3_ewR regs ex 19 19%bv eq_refl); exact G19).
assert (F20 : ew E 20 = w64 r) by (unfold E; rewrite (c3_ewR regs ex 20 20%bv eq_refl); exact G20).
assert (F23 : ew E 23 = w64 (c3_ren XI NN)) by (unfold E; rewrite (c3_ewR regs ex 23 23%bv eq_refl); exact G23).
assert (F24 : ew E 24 = w64 idxb) by (unfold E; rewrite (c3_ewR regs ex 24 24%bv eq_refl); exact G24).
assert (F25 : ew E 25 = w64 (Z.land op 8)) by (unfold E; rewrite (c3_ewR regs ex 25 25%bv eq_refl); exact G25).
assert (F27 : ew E 27 = w64 fab) by (unfold E; rewrite (c3_ewR regs ex 27 27%bv eq_refl); exact G27).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HE : E = Eimg (Ereg regs ex)) by reflexivity.
clearbody E ex.
assert (HS : st_ok_pi SEGS VAL E (mkSS C3_P1 sr_atoms [c3_rs 0x70 (SOff 32 0)] None (mkFacts [C3_AF9] [] []))
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + C3_P1)) m (seg_rom SEGS)))).
{ rewrite HE. apply c3_seat; [vm_compute; reflexivity | | | ]; rewrite <- HE.
  - constructor; [|constructor].
    apply (c3_rs_ok E m 0x70 (SOff 32 0) (2 ^ 64 - 1 - r) U9 S70 (c3_den0 E 32 _ F32)); lia.
  - unfold c3_rs. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. tauto.
  - split; [cbn [f_atoms atoms_ok]; split; [exact (c3_af9 E U9) | exact I] | split; exact I]. }
assert (SHOK : sh_ok SEGS C3Bx [] E (mrestrict (w_H W3) m)) by constructor.
unfold c3_J in HJ.
(* bltz s7 (0x80868): no row renamed -> 0x808b0 *)
psrr_branch_tok RUN BR HS SHOK C3span;
  rewrite c3_blt, (c3_S_atom E 23 _ F23), S_SLit in Hc by (destruct Hren as [-> | (? & -> & _)]; lia);
  change (bv_swrap 64 0) with 0 in Hc.
- apply Z.ltb_lt in Hc.
  assert (Hm1 : c3_ren XI NN = -1) by (destruct Hren as [H | (? & H & _)]; lia). clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK C3span LP_FREE; [awr_ok_tac |]. c3_ro HM.
  pmkst HS. prreg HS (23%bv : bv 5) R23. prreg HS (27%bv : bv 5) R27. rewrite HE in HS.
  apply (c3_FREE_pt _ _ _ (c3_regs_run _ _ _ _ HS eq_refl GR));
    [rewrite R23; exact F23 | rewrite R27; exact F27 | exact HM | exact HJ].
- apply Z.ltb_ge in Hc.
  destruct Hren as [Hm1 | (HX & Hre & Hxi)]; [lia|]. clear Hc.
  assert (Hidx4 : 0 <= idxb <= 4) by lia.
  paj_run_tok RUN HS HJ SHOK C3span; [awr_ok_tac |]. c3_ro HM.
  psrr_branch_tok RUN BR HS SHOK C3span.

  + rewrite branch_ltu_U, c3_U_lit, (c3_U_atom E 24 _ F24) in Hc.
    rewrite !Z.mod_small in Hc by lia. exfalso. apply Z.ltb_lt in Hc. lia.
  + rewrite branch_ltu_U, c3_U_lit, (c3_U_atom E 24 _ F24) in Hc.
    rewrite !Z.mod_small in Hc by lia. apply Z.ltb_ge in Hc. clear Hc.
    paj_run_tok RUN HS HJ SHOK C3span; [awr_ok_tac |]. c3_ro HM.
    psrr_branch_tok RUN BR HS SHOK C3span.

    * rewrite branch_ltu_U, (c3_U_atom E 32 _ F32), U_SMd, (c3_U_atom E 24 _ F24), c3_U_lit in Hc;
        cbn [zmd_raw] in Hc;
        rewrite !(Z.mod_small idxb), (Z.mod_small 56), (Z.mod_small (2 ^ 64 - 1 - r)) in Hc by lia;
        unfold zcanon, M64 in Hc; rewrite (Z.mod_small (idxb * 56)) in Hc by lia.
      exfalso. apply Z.ltb_lt in Hc. lia.
    * rewrite branch_ltu_U, (c3_U_atom E 32 _ F32), U_SMd, (c3_U_atom E 24 _ F24), c3_U_lit in Hc;
        cbn [zmd_raw] in Hc;
        rewrite !(Z.mod_small idxb), (Z.mod_small 56), (Z.mod_small (2 ^ 64 - 1 - r)) in Hc by lia;
        unfold zcanon, M64 in Hc; rewrite (Z.mod_small (idxb * 56)) in Hc by lia.
      apply Z.ltb_ge in Hc. clear Hc.
      paj_run_tok RUN HS HJ SHOK C3span; [awr_ok_tac |]. c3_ro HM.
      psrr_branch_tok RUN BR HS SHOK C3span.

      -- (* op & 8 = 0: strncmp (r->box[idx].name, name, 31) *)
         rewrite branch_eq_U, (c3_U_atom E 25 _ F25), c3_U_lit in Hc.
         rewrite !Z.mod_small in Hc by (destruct c3_land8 as [HL|HL]; lia).
         apply Z.eqb_eq in Hc. assert (H8 : Z.land op 8 = 0) by lia. clear Hc.
         paj_run_tok RUN HS HJ SHOK C3span; [awr_ok_tac |]. c3_ro HM.
         pmkst HS. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
         prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1. prreg HS (23%bv : bv 5) Q23.
         rewrite HE in HS.
         assert (GRc : c3_regs (ms_regs ms)) by exact (c3_regs_call _ _ _ _ HS eq_refl GR).
         assert (P23 : getr (ms_regs ms) 23 = w64 XI) by (rewrite Q23, F23, Hre; reflexivity).
         eapply (c3_strncmp_call _ _ _ (r + 56 * XI + 24) q (firstn 31 (c3_sel_s op nm)) (c3_sel_s op nm) _
           HJ GRc HM).
         ++ rewrite Q10, Hxi. exact (c3_a0 E idxb F20 F24 ltac:(lia)).
         ++ rewrite Q11. exact F19.
         ++ rewrite Q12. reflexivity.
         ++ exact Q1.
         ++ apply ret_ok_codeptr_v; [lia | reflexivity].
         ++ exact (c3_fld_ok _ _ HJ HM ltac:(lia)).
         ++ exact (c3_name_ok_q _ _ HJ HM H8).
         ++ intros regs2 mem2 md2 HJ2 HP HM2 Hcmp.
            apply (c3_RET_pt regs2 mem2 md2 (c3_regs_pres _ _ HP GRc)).
            ** rewrite <- P23. exact (HP 23 ltac:(unfold acallee_saved; lia)).
            ** lia.
            ** apply (proj2 Hcmp). exact (c3_strn_eq (c3_sel_s op nm)).
            ** exact HM2.
            ** exact HJ2.

      -- (* op & 8 <> 0: strncmp (r->box[idx].name, "", 31) *)
         rewrite branch_eq_U, (c3_U_atom E 25 _ F25), c3_U_lit in Hc.
         rewrite !Z.mod_small in Hc by (destruct c3_land8 as [HL|HL]; lia).
         apply Z.eqb_neq in Hc. assert (H8 : Z.land op 8 = 8) by (destruct c3_land8 as [HL|HL]; lia).
         assert (Hsnil : c3_sel_s op nm = [])
           by (unfold c3_sel_s; replace (Z.land op 8 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
         clear Hc.
         paj_run_tok RUN HS HJ SHOK C3span; [awr_ok_tac |]. c3_ro HM.
         pmkst HS. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
         prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1. prreg HS (23%bv : bv 5) Q23.
         rewrite HE in HS.
         assert (GRc : c3_regs (ms_regs ms)) by exact (c3_regs_call _ _ _ _ HS eq_refl GR).
         assert (P23 : getr (ms_regs ms) 23 = w64 XI) by (rewrite Q23, F23, Hre; reflexivity).
         eapply (c3_strncmp_call _ _ _ (r + 56 * XI + 24) (VAL (A_OBJ 5))
           (firstn 31 (c3_sel_s op nm)) (c3_sel_s op nm) _ HJ GRc HM).
         ++ rewrite Q10, Hxi. exact (c3_a0 E idxb F20 F24 ltac:(lia)).
         ++ rewrite Q11. exact (c3_img_atom E (A_OBJ 5) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
         ++ rewrite Q12. reflexivity.
         ++ exact Q1.
         ++ apply ret_ok_codeptr_v; [lia | reflexivity].
         ++ exact (c3_fld_ok _ _ HJ HM ltac:(lia)).
         ++ rewrite Hsnil. exact (c3_empty_ok _ _ HJ).
         ++ intros regs2 mem2 md2 HJ2 HP HM2 Hcmp.
            apply (c3_RET_pt regs2 mem2 md2 (c3_regs_pres _ _ HP GRc)).
            ** rewrite <- P23. exact (HP 23 ltac:(unfold acallee_saved; lia)).
            ** lia.
            ** apply (proj2 Hcmp). exact (c3_strn_eq (c3_sel_s op nm)).
            ** exact HM2.
            ** exact HJ2.
Qed.
Lemma c3_bsig : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. unfold bv_signed. rewrite Z_to_bv_unsigned, bv_swrap_wrap. apply c3_swrap. exact Hz.
Qed.

Lemma c3_ren_val_e : forall (E : env) x n, ew E 23 = w64 x -> ew E 26 = w64 n -> -128 <= x < 128 -> 0 <= n <= 5 ->
  alu64 ALU_OR (alu64 ALU_ADD (alu64 ALU_AND (alu64 ALU_XOR (alu64 ALU_SLT (ew E 23) (Z_to_bv 64 0)) (Z_to_bv 64 (-1)))
    (alu64 ALU_SLT (ew E 23) (ew E 26))) (Z_to_bv 64 (-1))) (ew E 23) = w64 (c3_ren x n).
Proof.
intros E x n H23 H26 Hx Hn. rewrite H23, H26. unfold w64, c3_ren.
rewrite <- (LLVMFuzzerTestOneInput_case3.c3_ren_val x n Hx Hn).
unfold alu64, alu, PropExec.v_slti, PropExec.v_slt, PropExec.zsig, PropExec.c_lts, bv_lts.
rewrite !(c3_bsig x) by lia. rewrite !(c3_bsig 0) by lia. rewrite !(c3_bsig n) by lia.
destruct (Z.ltb_spec x 0) as [H0|H0]; destruct (Z.ltb_spec x n) as [H1|H1]; bv_simplify; reflexivity.
Qed.
Lemma c3_SN_pt : forall regs m md,
  c3_regs regs -> getr regs 23 = w64 XI -> getr regs 24 = w64 idxb ->
  getr regs 25 = w64 (Z.land op 8) -> getr regs 27 = w64 fab ->
  c3_mem m -> c3_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + LP_SN)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md GR G23 G24 G25 G27 HM HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G19 & G20 & G21 & G26).
pose proof c3_NN as HN.
set (E := Eimg (Ereg regs (@nil word))).
assert (F23 : ew E 23 = w64 XI) by (unfold E; rewrite (c3_ewR regs [] 23 23%bv eq_refl); exact G23).
assert (F24 : ew E 24 = w64 idxb) by (unfold E; rewrite (c3_ewR regs [] 24 24%bv eq_refl); exact G24).
assert (F25 : ew E 25 = w64 (Z.land op 8)) by (unfold E; rewrite (c3_ewR regs [] 25 25%bv eq_refl); exact G25).
assert (F26 : ew E 26 = w64 NN) by (unfold E; rewrite (c3_ewR regs [] 26 26%bv eq_refl); exact G26).
assert (F27 : ew E 27 = w64 fab) by (unfold E; rewrite (c3_ewR regs [] 27 27%bv eq_refl); exact G27).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HE : E = Eimg (Ereg regs [])) by reflexivity.
clearbody E.
assert (HS : st_ok_pi SEGS VAL E (mkSS LP_SN sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + LP_SN)) m (seg_rom SEGS)))).
{ rewrite HE. apply c3_seat; [vm_compute; reflexivity | apply Forall_nil | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS C3Bx [] E (mrestrict (w_H W3) m)) by constructor.
unfold c3_J in HJ.
paj_run_tok RUN HS HJ SHOK C3span; [apply awr_ok_nil |]. c3_ro HM.
pmkst HS. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
rewrite HE in HS.
apply (c3_P1_pt _ _ _ (c3_regs_run _ _ _ _ HS eq_refl GR)).
- rewrite Q23. apply (c3_ren_val_e E XI NN F23 F26);
    [unfold c3_sext8; destruct (Z.ltb_spec idxb 128) as [HL|HL]; lia | lia].
- rewrite Q24. exact F24.
- rewrite Q25. exact F25.
- rewrite Q27. exact F27.
- exact HM.
- exact HJ.
Qed.
End c.
(* ---- the segment ---- *)
#[local] Notation POSTT := (lxcx -> world SEGS -> config -> Prop).

Theorem c3_segC : forall POST : POSTT, c3_segC_ok B MT POST.
Proof.
intros POST i HFREE cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (pos & r & fab & op & idxb & q & bs & nm & HBODY & Hidxb & G19 & G23 & G24 & G25).
destruct HBODY as (HBD & Hi & Hk & Hacc & HBLK & Hq0 & Hnm & QB & RG & HINV & HFAB & PV & Hop3 & Hop & CUR & SL
  & S58 & G20 & G21 & G26 & G27).
pose proof HBD as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G22) & SV & SH & FL
  & S10 & S18 & S80 & GI).
pose proof (lx_sp_facts B MT cx HB) as (SP16 & SPlo & SPhi & SPsp1 & SPal).
pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & _ & HF64 & HSHeq).
pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as HFeq.
pose proof HJ as (HAR & _).
assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; right; left; reflexivity).
assert (Hqin : In (q, c3_nlen nm + 1) (ablocks B ly3 S3))
  by (rewrite HBLK; apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR Hrin) as (Hr16 & Hr0 & Hrceil & Happr & _).
change (req_size LX_REG) with 288 in Hrceil, Happr.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q (c3_nlen nm + 1) HAR Hqin) as (_ & _ & Hqceil & _).
rewrite (c3_req (c3_nlen nm + 1)) in Hqceil by (unfold c3_nlen; lia).
pose proof HB as (_ & _ & _ & Hin0 & _).
assert (HGin : lc_n cx = 0 \/ (0 < lc_n cx /\ 4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling)).
{ destruct Hin0 as [H0 | (Hn & Hin)]; [left; exact (proj1 H0) | right].
  assert (Hin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)) by (rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ (lc_p cx) (lc_n cx) HAR Hin3) as (_ & Hp0 & Hp1 & _).
  rewrite (c3_req (lc_n cx)) in Hp1 by lia. split; [lia|]. split; lia. }
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + LP_SN)) (ms_mem ms3) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
replace (mkCfg ms3 md3)
  with (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + LP_SN)) (ms_mem ms3) (seg_rom SEGS)) md3)
  by (rewrite <- Hms; reflexivity).
apply (c3_SN_pt POST i cx fp k acc ly3 S3 W3 pos r fab op idxb q bs nm HB HFR HMO HFREE Hi Hk Hacc HBLK Hq0 Hnm
  HINV HFAB Hop3 Hop Hidxb
  ltac:(split; [exact SP16|]; split; [split; [exact SPlo | exact SPhi]|]; split; [exact SPsp1 | exact SPal])
  ltac:(split; [exact HF0|]; split; [exact HFc|]; split; [exact HF64|]; split; [exact HFapp | exact HFeq])
  ltac:(split; [exact Hr16|]; split; [exact Hr0|]; split; [exact Hrceil|]; split; [exact Hrin | exact Happr])
  ltac:(split; [exact Hqin | lia]) HGin (ms_regs ms3) (ms_mem ms3) md3).
- split; [exact G2|]. split; [exact G8|]. split; [exact G9|]. split; [exact G3|]. split; [exact G4|].
  split; [exact G18|]. split; [exact G22|]. split; [exact G19|]. split; [exact G20|]. split; [exact G21 | exact G26].
- exact G23.
- exact G24.
- exact G25.
- exact G27.
- unfold c3_mem. split; [exact SV|]. split; [exact SH|]. split; [exact FL|]. split; [exact S10|].
  split; [exact S18|]. split; [exact S80|]. split; [exact GI|]. split; [exact QB|]. split; [exact RG|].
  split; [exact PV|]. split; [exact CUR|]. split; [exact SL | exact S58].
- exact HJ.
Qed.
End a.