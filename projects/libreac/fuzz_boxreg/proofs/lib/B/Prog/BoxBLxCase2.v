(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module names changed; 1230 of its 1311 lines of code are new or changed and 899 lines of the source are left out. *)
(* Phase case 2 of the ASan+UBSan walk of fuzz_boxreg's LLVMFuzzerTestOneInput (BoxBLxDefs.v's cuts): from the cut T
   with op & 3 = 2 (0x8034c) to the cut K (0x80b08); fuzz_boxreg.c:357-375.

   The code (offsets from 0x7ffac):
   - 0x8034c .. 0x803e4: the switch (andi a0,s7,3; the turn number i to sp1 + 0x58; blt 1,a0 and bne a0,2 to case 2),
     then read_mac (&in, op & 4, mac) (a0 = sp1 + 0x88, a2 = mac = F + 32 from sp1 + 0x68);
   - 0x803e8 .. 0x803f0: find (r, mac);
   - 0x803f4 .. 0x80450: idx < -1 aborts (0x80fa4); the shadow byte of r->n (address at sp1 + 0x40) must be 0 (else
     __asan_report_load4); idx >= r->n aborts; idx < 0 goes to 0x8045c; else the UBSan checks idx <= 4 and
     ~r >= 56 idx (the trap 0x80fac) and bcmp (r + 56 idx, mac, 6) (0x80450);
   - 0x80454: s11 = fab again (sp1 + 0x30); a nonzero bcmp aborts;
   - 0x8045c .. 0x8046c: bcmp (mac, ZERO, 6) (ZERO = A_OBJ 4);
   - 0x80470 .. 0x80480: s8 = 0xffffffff (renamed = -1); idx = -1 goes to K; else a zero MAC aborts, and K.
   Every abort is refuted from find's contract (Pau's reac_boxreg_find_c.find_result: idx = -1, or the first box
   holding the MAC, which is not the zero MAC) and the registry invariant (boxreg_B1: n <= 5); the registry is not
   written, so K holds with bs' = bs and ren = -1.

   The walk runs the engine on small symbolic states, one per straight-line segment: each holds only the spill
   slots and objects its instructions read or write; what the cuts carry about memory is kept as facts on the
   memory (c2_base, c2_mem) across the segments (frame_of) and the calls (the callees' journals and keep facts). *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC85 BoxBCJ.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBReacBoxregInit BoxBReadMac BoxBReacBoxregFind BoxBLxDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg reac_boxreg_find_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the slots of the walk (offsets in the listing, address - 0x7ffac) ---- *)
Definition C2_B : Z := 0x43c.    (* 0x803e8: back from read_mac *)
Definition C2_C : Z := 0x448.    (* 0x803f4: back from find *)
Definition C2_C2 : Z := 0x4a8.   (* 0x80454: back from bcmp (r + 56 idx, mac, 6) *)
Definition C2_E : Z := 0x4c4.    (* 0x80470: back from bcmp (mac, ZERO, 6) *)

(* The shadow base as the engine's shadow tokens see it (no token is used: every shadow byte the walk reads is
   loaded through a spill slot, from a region). *)
Definition C2SB : Z := 0x7fff8000.
Definition C2Bx : sv := SLit C2SB.
Definition C2span : Z * Z := (C2SB, C2SB + 2 ^ 44 - 1).

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
Let LAWS := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- small facts ---- *)
Lemma c2_ewR : forall (regs : bvmap 5 word) extra n (rr : bv 5),
  Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs extra)) n = getr regs rr.
Proof.
intros regs extra n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma c2_rdword_keep : forall (rd rd' : reader) a v,
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk H. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.

Lemma c2_rdword_range : forall (H : word -> bool) mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hr. unfold rdword in Hr.
repeat match type of Hr with context [aview SEGS H mem ?x] =>
  let b := fresh "b" in let Eb := fresh "Eb" in
  destruct (aview SEGS H mem x) as [b|] eqn:Eb; [|discriminate Hr];
  destruct (aview_byte SEGS H mem x b Eb) as (? & _ & _ & ?) end.
injection Hr as <-. lia.
Qed.

Lemma c2_img_atom : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> ew E n = w64 (VAL n).
Proof. intros E n HE Hn. unfold w64. rewrite <- (HE n Hn). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section c.
(* ---- the phase: the cut T's data ---- *)
Variable POST : lxcx -> world SEGS -> config -> Prop.
Variable i : nat.
Variable cx : lxcx.
Variables fp k acc : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable pos : nat.
Variables r fab op : Z.
Variable bs : list byte.
Hypothesis HB : lx_base B MT cx.
Hypothesis HFR : frames S3 = [(LX_CID, fp)].
Hypothesis HMO : mo_le MT (lc_S cx) S3 acc.
Hypothesis HK : lx_from B MT POST (LI_K B MT i).
Hypothesis Hi : (i < 64)%nat.
Hypothesis Hk : k <= 1 + 2 * Z.of_nat i.
Hypothesis Hacc : acc <= LX_A1 MT + Z.of_nat i * LX_AI MT.
Hypothesis HBLK : lblk B cx ly3 S3 r.
Hypothesis HINV : Boxreg.boxreg_inv bs.
Hypothesis HFAB : Boxreg.bx_fabric bs = fab.
Hypothesis Hpos : (pos < length (lc_pl cx))%nat.
Hypothesis Hop : op = bv_unsigned (nth pos (lc_pl cx) (Z_to_bv 8 0)).
Hypothesis Hop3 : Z.land op 3 = 2.
(* The geometry: the two stack pointers, the frame F, the registry block and the input block (from lx_base and AR
   at the cut; none of them moves in the phase). *)
Hypothesis HGsp : lsp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= lsp0 cx <= 2 ^ 47 /\
  lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0.
Hypothesis HGF : 4096 <= lF cx fp /\ lF cx fp + 512 <= alloc_ceiling /\ lF cx fp mod 64 = 0 /\
  in_app (lF cx fp) 512 /\ frame_addr ly3 LX_CID fp = lF cx fp.
Hypothesis HGr : r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ In (r, LX_REG) (ablocks B ly3 S3) /\
  (r + 288 <= lF cx fp \/ lF cx fp + 512 <= r) /\ in_app r 288.
Hypothesis HGin : 0 < lc_n cx /\ 4096 <= lc_p cx /\ lc_p cx + lc_n cx <= alloc_ceiling /\
  In (lc_p cx, lc_n cx) (ablocks B ly3 S3) /\
  (lc_p cx + lc_n cx <= lF cx fp \/ lF cx fp + 512 <= lc_p cx) /\
  (lc_p cx + lc_n cx <= r \/ r + 288 <= lc_p cx \/ (lc_p cx = r /\ lc_n cx = 288)).

(* ---- the memory facts of the phase ---- *)
Definition cms (m : word -> option byte) : machine_state := mkst (lc_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).

(* What K needs of the memory besides the cursor and the slot of the turn number (c2_bpre), and with that slot
   (c2_base). *)
Definition c2_bpre (m : word -> option byte) : Prop :=
  lsaved cx W3 (cms m) /\ lshadow cx fp W3 (cms m) LSH_iter /\
  rdword (aview SEGS (w_H W3) m) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp) /\
  lslot cx W3 (cms m) 0x10 (lF cx fp) /\ lslot cx W3 (cms m) 0x18 (lF cx fp) /\
  lslot cx W3 (cms m) 0x80 (lF cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) m) (lc_p cx) (map (fun b : byte => bv_unsigned b) (lc_pl cx)) /\
  lreg W3 (cms m) r bs /\ lprev cx fp W3 (cms m) bs /\ lslots_loop cx fp W3 (cms m) r fab.
Definition c2_base (m : word -> option byte) : Prop :=
  c2_bpre m /\ lslot cx W3 (cms m) 0x58 (Z.of_nat i).

(* The memory after read_mac: the cursor has read pos' bytes and mac holds M. *)
Definition c2_mem (pos' : nat) (M : list byte) (m : word -> option byte) : Prop :=
  c2_base m /\ lcur cx W3 (cms m) pos' /\
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) m (lF cx fp + 32 + j) = Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0)))).

(* The bytes those facts speak about, and the ones read_mac writes. *)
Definition c2_at (a : Z) : Prop :=
  lsp1 cx <= a < 2 ^ 64 \/ lc_p cx <= a < lc_p cx + lc_n cx \/ lF cx fp <= a < lF cx fp + 512 \/
  lSH cx fp <= a < lSH cx fp + 64 \/ r <= a < r + 288.
Definition c2_wr (a : Z) : Prop :=
  lsp1 cx + 0x88 <= a < lsp1 cx + 0x98 \/ lF cx fp + 32 <= a < lF cx fp + 38.

(* The frame's shadow lies below the allocator's ceiling and apart from the frame. *)
Lemma c2_SH : lSH cx fp = SHADOW_OFF + lF cx fp / 8 /\ 0 <= lF cx fp / 8 /\ lSH cx fp + 64 <= alloc_ceiling /\
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

(* The facts of c2_bpre survive a change of any bytes outside them: the cursor and mac (read_mac), slot 0x58. *)
Lemma c2_bpre_keep : forall (X : Z -> Prop) m m', c2_bpre m ->
  (forall a, X a -> c2_wr a \/ lsp1 cx + 0x58 <= a < lsp1 cx + 0x60) ->
  (forall a, c2_at a -> ~ X a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) -> c2_bpre m'.
Proof.
intros X m m' (SV & SH & FL & S10 & S18 & S80 & GI & RG & PV & SL) HX KP.
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _).
pose proof HGr as (Hr16 & Hr0 & Hr1 & _ & HrF & _). pose proof HGin as (Hn0 & Hp0 & Hp1 & _ & HpF & Hpr).
pose proof c2_SH as (ESH & D0 & HSH1 & HSH2). pose proof asan_consts as (C1 & _).
assert (Hfb : fs_frame_bytes LX_CID = 512) by reflexivity.
assert (NX : forall a, ~ c2_wr a -> ~ (lsp1 cx + 0x58 <= a < lsp1 cx + 0x60) -> ~ X a)
  by (intros a H1 H2 H3; destruct (HX a H3); contradiction).
assert (KS : forall off v, 0 <= off -> off + 8 <= 0x88 -> (off + 8 <= 0x58 \/ 0x60 <= off) ->
  lslot cx W3 (cms m) off v -> lslot cx W3 (cms m') off v).
{ intros off v H0 H1 H2 H. unfold lslot, lview in *. cbn [cms ms_mem mkst] in *.
  eapply (c2_rdword_keep _ _ _ v); [|exact H]. intros q Hq. apply KP.
  - left. lia.
  - apply NX; [unfold c2_wr; lia | lia]. }
unfold c2_bpre. cbn [cms ms_mem mkst] in *.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
- destruct SV as (Sra & Sj). unfold lsaved, lview in *. cbn [ms_mem mkst] in *. split.
  + eapply (c2_rdword_keep _ _ _ _); [|exact Sra]. intros q Hq. apply KP; [left; lia | apply NX; unfold c2_wr; lia].
  + intros j Hj. eapply (c2_rdword_keep _ _ _ _); [|exact (Sj j Hj)]. intros q Hq.
    apply KP; [left; lia | apply NX; unfold c2_wr; lia].
- intros q Hq. unfold lview in *. cbn [ms_mem mkst] in *. rewrite KP; [exact (SH q Hq)| |].
  + right; right; right; left. assert (Z.of_nat (length LSH_iter) = 52) by reflexivity. lia.
  + assert (Z.of_nat (length LSH_iter) = 52) by reflexivity. apply NX; unfold c2_wr; destruct HSH2; lia.
- rewrite Hfb in *. eapply (c2_rdword_keep _ _ _ _); [|exact FL]. intros q Hq.
  apply KP; [right; right; left; lia | apply NX; unfold c2_wr; lia].
- apply KS; [lia | lia | lia | exact S10].
- apply KS; [lia | lia | lia | exact S18].
- apply KS; [lia | lia | lia | exact S80].
- apply (garr8_frame SEGS _ _ _ _ GI). intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview SEGS).
  apply KP; [right; left; unfold lc_n; lia | apply NX; unfold c2_wr, lc_n in *; lia].
- intros q Hq. unfold lview in *. cbn [ms_mem mkst] in *. rewrite KP; [exact (RG q Hq)| |].
  + right; right; right; right. unfold LX_REG in Hq. lia.
  + apply NX; unfold c2_wr, LX_REG in *; lia.
- intros q Hq. unfold lview in *. cbn [ms_mem mkst] in *. rewrite KP; [exact (PV q Hq)| |].
  + right; right; left. unfold LX_REG in Hq. lia.
  + apply NX; unfold c2_wr, LX_REG in *; lia.
- destruct SL as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
  repeat split; apply KS; first [lia | assumption].
Qed.

Lemma c2_base_keep : forall m m', c2_base m ->
  (forall a, c2_at a -> ~ c2_wr a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) -> c2_base m'.
Proof.
intros m m' (BP & S58) KP. pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32).
split; [exact (c2_bpre_keep c2_wr m m' BP (fun a H => or_introl H) KP)|].
unfold lslot, lview in *. cbn [cms ms_mem mkst] in *.
eapply (c2_rdword_keep _ _ _ _); [|exact S58]. intros q Hq. apply KP; [left; lia | unfold c2_wr; lia].
Qed.

Lemma c2_mem_keep : forall pos' M m m', c2_mem pos' M m ->
  (forall a, c2_at a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) -> c2_mem pos' M m'.
Proof.
intros pos' M m m' (BA & (Hp & C88 & C90) & MC) KP.
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _).
pose proof asan_consts as (C1 & _).
split; [apply (c2_base_keep m m' BA); intros a Ha _; exact (KP a Ha)|].
split; [split; [exact Hp|]; split|].
- unfold lslot, lview in *. cbn [cms ms_mem mkst] in *. eapply (c2_rdword_keep _ _ _ _); [|exact C88].
  intros q Hq. apply KP. left. lia.
- unfold lslot, lview in *. cbn [cms ms_mem mkst] in *. eapply (c2_rdword_keep _ _ _ _); [|exact C90].
  intros q Hq. apply KP. left. lia.
- intros j Hj. rewrite KP; [exact (MC j Hj)|]. right; right; left. lia.
Qed.

(* A run that wrote nothing keeps the memory. *)
Lemma c2_mem_same : forall pos' M m m', c2_mem pos' M m -> (forall x, m' x = m x) -> c2_mem pos' M m'.
Proof.
intros pos' M m m' H E. apply (c2_mem_keep pos' M m m' H). intros a _. unfold aview, mbyte, mrestrict. rewrite E. reflexivity.
Qed.

(* ---- the registers every point of the walk keeps ---- *)
Definition c2_regs (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lsp1 cx) /\ getr regs 8 = w64 (lsp0 cx) /\ getr regs 9 = w64 (lsp1 cx) /\
  getr regs 3 = getr (lc_regs cx) 3 /\ getr regs 4 = getr (lc_regs cx) 4 /\
  getr regs 18 = w64 SHADOW_OFF /\ getr regs 22 = w64 (lSH cx fp) /\
  getr regs 20 = w64 r /\ getr regs 21 = w64 (lF cx fp + 64) /\ getr regs 27 = w64 fab.
Definition C2R : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27].

Lemma c2_regs_same : forall regs regs',
  (forall n, In n [2; 3; 4; 8; 9; 18; 20; 21; 22; 27] -> getr regs' (Z_to_bv 5 n) = getr regs (Z_to_bv 5 n)) ->
  c2_regs regs -> c2_regs regs'.
Proof.
intros regs regs' K (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27). unfold c2_regs.
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

Lemma c2_regs_pres : forall regs regs', aregs_preserved regs regs' -> c2_regs regs -> c2_regs regs'.
Proof.
intros regs regs' HP. apply c2_regs_same. intros n Hn. apply HP. unfold acallee_saved.
cbv [In] in Hn. lia.
Qed.

(* The journal of the phase at a memory m. *)
Definition c2_J (m : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 m md k.

(* ---- facts every call of the walk uses ---- *)
Lemma c2_ar : forall m md, c2_J m md -> AR SEGS B ly3 S3 W3 m md.
Proof. intros m md HJ. exact (proj1 HJ). Qed.

Lemma c2_mod8 : forall a q, a mod q = 0 -> q mod 8 = 0 -> 0 < q -> a mod 8 = 0.
Proof.
intros a q Ha Hq Hq0. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hq; [|lia]. apply Z.mod_divide; [lia|].
destruct Ha as [x Hx]. destruct Hq as [y Hy]. exists (x * y). lia.
Qed.

(* sp1 - sp0, the offset of the walk's calls from the function's entry sp, is a multiple of 16. *)
Lemma c2_o16 : (lsp1 cx - lsp0 cx) mod 16 = 0.
Proof.
pose proof HGsp as (Hs16 & _ & _ & Hs32).
apply Z.mod_divide in Hs16; [|lia]. apply Z.mod_divide in Hs32; [|lia]. apply Z.mod_divide; [lia|].
destruct Hs16 as [x Hx]. destruct Hs32 as [y Hy]. exists (2 * y - x). lia.
Qed.

Lemma c2_gptp : getr (lc_regs cx) 3 = w64 (as_gp B) /\ getr (lc_regs cx) 4 = w64 (as_tp B).
Proof. pose proof HB as ((_ & _ & _ & Hgp & Htp & _) & _). split; assumption. Qed.

(* The shadow byte AR fixes for each registered global (its size). *)
Lemma c2_gshadow : forall g sz m md, In (g, sz) LX_GLOBS -> c2_J m md ->
  aview SEGS (w_H W3) m (shadow_addr (VAL (A_OBJ g))) = Some sz.
Proof.
intros g sz m md Hin HJ. destruct (c2_ar m md HJ) as (M & _).
pose proof (am_const _ _ _ _ M) as C. rewrite Forall_forall in C.
assert (Hc : In (z1 (ANum (shadow_addr (VAL (A_OBJ g)))) sz) (as_const B ly3)).
{ apply (blx_cells B (lh_glob B MT HY) ly3). unfold lx_glob_cells. apply in_flat_map.
  exists (g, sz). split; [exact Hin|]. cbn [fst snd]. left. reflexivity. }
assert (Hsz : 0 <= sz < 256) by (cbv [LX_GLOBS In] in Hin; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]); destruct Hin).
specialize (C _ Hc). unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. rewrite C. f_equal.
unfold le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r, Z.mod_mod by lia. apply Z.mod_small. exact Hsz.
Qed.

(* The bytes the read-only image holds at each global, in the walk's memory (arodata_okP, kept by the journal). *)
Lemma c2_gbytes : forall g l m md j, In (g, l) LX_GLOB_BYTES -> c2_J m md -> 0 <= j < Z.of_nat (length l) ->
  aview SEGS (w_H W3) m (VAL (A_OBJ g) + j) = Some (nth (Z.to_nat j) l 0).
Proof.
intros g l m md j Hin HJ Hj.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
pose proof (lx_arodata_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO) as HRO3.
destruct (blx_rom_bytes B (lh_glob B MT HY) (g, l) Hin j Hj) as (Hrom & Ho & He & Hb).
cbn [fst snd] in *. rewrite (HRO3 _ (or_introl Hrom) Ho He). exact Hb.
Qed.

Lemma c2_gra : forall g sz m md, In (g, sz) LX_GLOBS -> 0 <= sz < 8 -> c2_J m md ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (VAL (A_OBJ g)) sz.
Proof.
intros g sz m md Hin Hsz HJ. apply range_addressable_partial; [exact (c2_gshadow g sz m md Hin HJ) | | exact Hsz].
apply (c2_mod8 _ 32); [exact (blx_al B (lh_glob B MT HY) (g, sz) Hin) | reflexivity | lia].
Qed.

Lemma c2_ghull : forall g sz m md, In (g, sz) LX_GLOBS -> 0 < sz -> c2_J m md ->
  shadow_hull_vis (aview SEGS (w_H W3) m) (VAL (A_OBJ g)) sz.
Proof.
intros g sz m md Hin Hsz HJ. destruct (blx_marg B (lh_glob B MT HY) (g, sz) Hin) as [M1 M2]. cbn [fst snd] in *.
eapply ro_hull; [exact (blx_isv B (lh_glob B MT HY)) | exact (c2_ar m md HJ) | exact Hsz | exact M1 | exact M2].
Qed.

(* mac = F + 32 .. F + 37: its shadow byte (LSH_iter's 6) and the hull of its granule. *)
Lemma c2_mac_ra : forall m, c2_base m -> range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (lF cx fp + 32) 6.
Proof.
intros m ((_ & SH & _) & _). pose proof HGF as (HF0 & _ & HF64 & _).
assert (HF8 : lF cx fp mod 8 = 0) by (apply (c2_mod8 _ 64); [exact HF64 | reflexivity | lia]).
apply range_addressable_partial; [| apply (c2_mod8 _ 8); [|reflexivity|lia] | lia].
- assert (Hq : (lF cx fp + 32) / 8 = lF cx fp / 8 + 4).
  { pose proof (Z.div_mod (lF cx fp) 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
    rewrite D at 1. replace (8 * (lF cx fp / 8) + 32) with ((lF cx fp / 8 + 4) * 8) by lia. apply Z.div_mul. lia. }
  pose proof (SH 4%nat ltac:(cbn; lia)) as S4. unfold lview in S4. cbn [cms ms_mem mkst] in S4.
  unfold shadow_of_addr. rewrite Hq.
  replace (SHADOW_OFF + (lF cx fp / 8 + 4)) with (lSH cx fp + Z.of_nat 4)
    by (change (lSH cx fp) with (SHADOW_OFF + lF cx fp / 8); lia).
  exact S4.
- replace (lF cx fp + 32) with (lF cx fp + 4 * 8) by lia. rewrite Z.mod_add by lia. exact HF8.
Qed.

Lemma c2_mac_hull : forall m md, c2_J m md -> shadow_hull_vis (aview SEGS (w_H W3) m) (lF cx fp + 32) 6.
Proof.
intros m md HJ. pose proof HGF as (HF0 & HF1 & _ & _ & HFeq).
eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 m md LX_CID fp); [exact (c2_ar m md HJ) | rewrite HFR; left; reflexivity | | |].
- rewrite HFeq. lia.
- rewrite HFeq. change (fs_frame_bytes LX_CID) with 512. lia.
- lia.
Qed.

(* ---- K (0x80b08): the cut's predicate, with the registry unchanged and no box renamed ---- *)
Lemma c2_kept : lkept bs bs (-1).
Proof. intros j _. repeat split; right; reflexivity. Qed.

Lemma c2_K : forall regs m md pos' M,
  c2_regs regs -> getr regs 24 = w64 ((-1) mod 2 ^ 32) -> c2_mem pos' M m -> c2_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + LP_K)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md pos' M (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27) G24
  (((SV & SH & FL & S10 & S18 & S80 & GI & RG & PV & SL) & S58) & CUR & _) HJ.
pose proof (lh_mtl B MT HY) as ML.
pose proof (mo_malloc_nonneg MT ML 48 ltac:(lia)) as Hm48. pose proof (mo_free_nonneg MT ML) as Hfr0.
pose proof HINV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
apply (HK cx fp k acc ly3 S3 W3 (mkst regs (Z_to_bv 64 (BASE + LP_K)) m (seg_rom SEGS)) md HB HJ HFR HMO).
exists pos', r, fab, (-1), bs, bs.
split.
{ unfold lx_body. do 6 (split; [reflexivity|]).
  split; [exact (conj G2 (conj G8 (conj G9 (conj G3 (conj G4 (conj G18 G22))))))|].
  split; [exact SV|]. split; [exact SH|]. split; [exact FL|].
  split; [exact S10|]. split; [exact S18|]. split; [exact S80 | exact GI]. }
split; [exact Hi|]. split; [lia|].
split; [unfold LX_AI in *; nia|].
split; [exact HBLK|]. split; [exact PV|]. split; [exact HINV|]. split; [exact HFAB|].
split; [exact RG|]. split; [exact HINV|]. split; [exact HFAB|]. split; [exact c2_kept|].
split; [lia|]. split; [exact CUR|]. split; [exact SL|]. split; [exact S58|].
split; [exact G20|]. split; [exact G21|]. split; [exact G24 | exact G27].
Qed.

(* ---- the engine's states of the walk ---- *)
(* A small symbolic state: the registers as atoms 0 .. 31 (and `extra` from 32 on), the regions rs. *)
Lemma c2_seat : forall (regs : bvmap 5 word) extra m pc rs G,
  regions_wf rs = true -> Forall (region_ok SEGS (Eimg (Ereg regs extra)) (mrestrict (w_H W3) m)) rs ->
  pairwise_disjoint (Eimg (Ereg regs extra)) rs -> facts_ok (Eimg (Ereg regs extra)) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) (mkSS pc sr_atoms rs None G)
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS))).
Proof.
intros regs extra m pc rs G Hwf Hok Hd HG. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hok | exact Hd | exact HG].
Qed.

(* A run whose regions are all read-only writes no byte. *)
Lemma c2_frame_ro : forall E rs m m', forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs = true ->
  frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (rg & Hin & Ha).
rewrite forallb_forall in Hro. specialize (Hro rg Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma c2_U_atom : forall E n z, ew E n = w64 z -> U E (SOff n 0) = z mod 2 ^ 64.
Proof.
intros E n z H. rewrite U_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_mod. lia.
Qed.

Lemma c2_U_lit : forall E x, U E (SLit x) = x mod 2 ^ 64.
Proof. intros E x. rewrite U_SLit. reflexivity. Qed.

Lemma c2_U_reg : forall E n w, ew E n = w -> U E (SOff n 0) = bv_unsigned w.
Proof.
intros E n w H. rewrite U_SOff, H, Z.add_0_r. apply zcanon_id. pose proof (bv_unsigned_in_range 64 w) as R.
change (bv_modulus 64) with (2 ^ 64) in R. unfold M64. lia.
Qed.

(* After a run with read-only regions: the memory facts carry over. *)
Ltac c2_ro HM :=
  lazymatch type of HM with c2_mem ?p ?M ?m0 =>
  match goal with HF : frame_of _ ?rs m0 ?m1 |- _ =>
    let H := fresh "HM" in
    pose proof (c2_mem_same p M m0 m1 HM (c2_frame_ro _ rs m0 m1 eq_refl HF)) as H; clear HM; rename H into HM
  end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* The registers a run keeps, as the final symbolic registers say. *)
Lemma c2_regs_run : forall regs extra ss (ms : machine_state),
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) ss (restrict (w_H W3) ms) ->
  forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) = true ->
  c2_regs regs -> c2_regs (ms_regs ms).
Proof.
intros regs extra ss ms HS Hl. apply c2_regs_same. intros n Hn.
apply (regs_kept_of_st_ok_pi _ ss (restrict (w_H W3) ms) regs extra (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) HS);
  [| exact Hl | apply in_map; exact Hn].
split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.
(* At K: the landing (c2_K). HE says the environment's registers are regs. *)
Ltac c2_land HS HJ HM HE GR :=
  pmkst HS;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
  rewrite HE in HS;
  let R24 := fresh "R24" in prreg HS (24%bv : bv 5) R24;
  eapply (c2_K (ms_regs msn) (ms_mem msn) _ _ _);
  [ exact (c2_regs_run _ _ _ _ HS eq_refl GR)
  | rewrite R24; reflexivity
  | exact HM
  | exact HJ ] end.


(* The same at a call (the engine's state at the callee's entry). *)
Lemma c2_regs_call : forall regs extra ss (ms : machine_state),
  st_ok SEGS (Eimg (Ereg regs extra)) ss (restrict (w_H W3) ms) ->
  forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) = true ->
  c2_regs regs -> c2_regs (ms_regs ms).
Proof.
intros regs extra ss ms HS Hl. apply c2_regs_same. intros n Hn.
pose proof (regs_kept_of_st_ok SEGS _ ss (restrict (w_H W3) ms) regs extra
  (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 20; 21; 22; 27]) HS) as K.
cbn [restrict ms_regs] in K. apply K; [| exact Hl | apply in_map; exact Hn].
split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* A read-only spill slot of the machine frame, at the atom of s1 (= sp1). *)
Definition c2_rs (off : Z) (e : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 e)].

Lemma c2_rs_ok : forall E m off e v, bv_unsigned (ew E 9) = lsp1 cx ->
  lslot cx W3 (cms m) off v -> sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= off -> off + 8 <= 0x98 ->
  region_ok SEGS E (mrestrict (w_H W3) m) (c2_rs off e).
Proof.
intros E m off e v H9 Hs He Hv H0 H1. pose proof HGsp as (_ & Hs0 & Hs1 & _).
unfold region_ok, c2_rs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (lsp1 cx) off 8 e v He); [cbn; lia | cbn; lia |].
apply (val_mem_of_rdword SEGS (w_H W3) m). exact Hs.
Qed.

(* The fact on sp1 the engine's loads and stores at s1 use. *)
Definition C2_AF9 : nat * afact := (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5).
Lemma c2_af9 : forall E, bv_unsigned (ew E 9) = lsp1 cx -> afact_ok E (fst C2_AF9) (snd C2_AF9).
Proof.
intros E H9. pose proof HGsp as (_ & Hs0 & Hs1 & Hs32). pose proof asan_consts as (C1 & _).
unfold afact_ok, C2_AF9. cbn [fst snd af_lo af_hi af_al2]. rewrite H9. change (2 ^ 5) with 32.
split; [lia|]. split; [exact Hs32 | lia].
Qed.

(* ---- 0x80470 .. K: s8 = 0xffffffff; idx = -1 goes to K; else a0 = 0 (a zero MAC) would abort ---- *)
Definition ss_E : sstate := mkSS C2_E sr_atoms [] None (mkFacts [] [] []).

Lemma c2_E_pt : forall regs m md pos' M z,
  c2_regs regs -> getr regs 19 = w64 z ->
  (bv_unsigned (getr regs 10) = 0 <-> M = Boxreg.zero6) ->
  (z = -1 \/ (0 <= z < 5 /\ M <> Boxreg.zero6)) -> c2_mem pos' M m -> c2_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C2_E)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md pos' M z GR G19 Hv Hz HM HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (c2_seat regs [] m C2_E [] (mkFacts [] [] []) eq_refl (Forall_nil _) I (conj I (conj I I))) as HS.
assert (SHOK : sh_ok SEGS C2Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W3) m)) by constructor.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (F19 : ew E 19 = w64 z) by (subst E; rewrite (c2_ewR regs [] 19 19%bv eq_refl); exact G19).
assert (F10 : ew E 10 = getr regs 10) by (subst E; exact (c2_ewR regs [] 10 10%bv eq_refl)).
unfold c2_J in HJ.
paj_run_to_tok RUNTO HS HJ SHOK C2span LP_K; [apply awr_ok_nil |]. c2_ro HM.
(* beq s3, a1 (0x80478): idx = -1 *)
psrr_branch_tok RUN BR HS SHOK C2span;
  rewrite branch_eq_U, (c2_U_atom E 19 z F19), c2_U_lit in Hc.
- destruct Hz as [-> | (Hz & HMz)]; [| rewrite !Z.mod_small in Hc by lia; apply Z.eqb_eq in Hc; lia].
  paj_run_to_tok RUNTO HS HJ SHOK C2span LP_K; [apply awr_ok_nil |]. c2_ro HM.
  c2_land HS HJ HM HE GR.
- destruct Hz as [-> | (Hz & HMz)]; [vm_compute in Hc; discriminate Hc |]. clear Hc.
  (* beqz a0 (0x8047c): a zero MAC aborts *)
  paj_run_to_tok RUNTO HS HJ SHOK C2span LP_K; [apply awr_ok_nil |]. c2_ro HM.
  psrr_branch_tok RUN BR HS SHOK C2span;
    rewrite branch_eq_U, (c2_U_reg E 10 _ F10), c2_U_lit in Hc.
  + exfalso. rewrite Z.mod_small in Hc by (pose proof (bv_unsigned_in_range 64 (getr regs 10)) as Rg;
      change (bv_modulus 64) with (2 ^ 64) in Rg; lia).
    apply Z.eqb_eq in Hc. apply HMz. apply Hv. exact Hc.
  + paj_run_to_tok RUNTO HS HJ SHOK C2span LP_K; [apply awr_ok_nil |]. c2_ro HM.
    c2_land HS HJ HM HE GR.
Qed.

(* ---- the bcmp wrapper (abcmp_realizes, through aj_bcmp_at) ---- *)
Lemma c2_at_rng : forall a, c2_at a -> 0 <= a < 2 ^ 64 /\ (a + 8192 < lsp1 cx \/ lsp1 cx <= a).
Proof.
intros a Ha. pose proof HGsp as (_ & Hs0 & Hs1 & _). pose proof HGF as (HF0 & HF1 & _).
pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof HGin as (_ & Hp0 & Hp1 & _).
pose proof c2_SH as (ESH & D0 & HSH1 & _). pose proof asan_consts as (C1 & _).
unfold c2_at in Ha. unfold SHADOW_OFF in ESH. destruct Ha as [H|[H|[H|[H|H]]]]; split; lia.
Qed.

Lemma c2_zero6 : forall M : list byte, length M = 6%nat ->
  (M = Boxreg.zero6 <-> forall i, 0 <= i < 6 -> bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)) = 0).
Proof.
intros M HL. split.
- intros -> q Hq. unfold Boxreg.zero6. rewrite nth_repeat. reflexivity.
- intros H. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite HL; reflexivity|].
  intros q Hq. rewrite HL in Hq. unfold Boxreg.zero6. rewrite nth_repeat.
  apply bv_eq. rewrite <- (Nat2Z.id q). rewrite (H (Z.of_nat q)) by lia. reflexivity.
Qed.

(* bcmp (x, y, 6) called at sp = sp1: the result is 0 exactly when the six bytes agree; it keeps every byte the
   phase's facts speak about. *)
Lemma c2_bcmp_call : forall (regsT : bvmap 5 word) memT mdT x y raw,
  c2_J memT mdT -> c2_regs regsT ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 6 -> getr regsT 1 = raw ->
  YK0s.ret_ok raw ->
  (forall a, x <= a < x + 6 -> aview SEGS (w_H W3) memT a <> None) ->
  (forall a, y <= a < y + 6 -> aview SEGS (w_H W3) memT a <> None) ->
  4096 <= x -> x + 6 <= alloc_ceiling -> 4096 <= y -> y + 6 <= alloc_ceiling ->
  amem_range x 6 -> amem_range y 6 ->
  range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF x 6 -> shadow_hull_vis (aview SEGS (w_H W3) memT) x 6 ->
  range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF y 6 -> shadow_hull_vis (aview SEGS (w_H W3) memT) y 6 ->
  (forall (regs2 : bvmap 5 word) mem2 md2, c2_J mem2 md2 -> aregs_preserved regsT regs2 ->
     (bv_unsigned (getr regs2 10) = 0 <->
       forall i, 0 <= i < 6 -> aview SEGS (w_H W3) memT (x + i) = aview SEGS (w_H W3) memT (y + i)) ->
     (forall a, c2_at a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a) ->
     SRr SEGS W3 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) (POST cx)) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (POST cx).
Proof.
intros regsT memT mdT x y raw HJ (G2 & G8 & G9 & G3 & G4 & _) H10 H11 H12 Hra Hraw Vx Vy Hx0 Hx1 Hy0 Hy1
  Mx My Rx Ux Ry Uy KONT.
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof asan_consts as (C1 & _).
pose proof c2_gptp as (Hgp & Htp).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : spZ regsT = lsp0 cx + (lsp1 cx - lsp0 cx)).
{ unfold spZ. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ (lh_bcmp B MT HY) W3 regsT memT LX_STK (lsp0 cx) []
    (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 mdT k x y 6
    (lsp1 cx - lsp0 cx) raw HJ H10 H11 H12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp c2_o16
    ltac:(lia) ltac:(unfold LX_STK; rewrite Hes; lia) ltac:(rewrite G3; exact Hgp) ltac:(rewrite G4; exact Htp)
    Hra Hraw).
  - intros a Ha. split; [exact (Vx a Ha) | rewrite Hsp, Hes; lia].
  - intros a Ha. split; [exact (Vy a Ha) | rewrite Hsp, Hes; lia].
  - intros a Ha. rewrite Hes. lia.
  - intros a Ha. rewrite Hes. lia.
  - exact Mx.
  - exact My.
  - exact Rx.
  - intros _. exact Ux.
  - exact Ry.
  - intros _. exact Uy. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & _).
apply (KONT regs2 mem2 md2 HJ2 HP).
- rewrite Hv. split.
  + intros H0. apply Hcmp. apply bv_eq. rewrite H0. reflexivity.
  + intros H. rewrite (proj2 Hcmp H). reflexivity.
- intros a Ha. destruct (c2_at_rng a Ha) as [Hr Hw]. apply Hfr; [exact Hr | rewrite Hes; lia].
Qed.

Lemma c2_Z_bytes : forall m md j, c2_J m md -> 0 <= j < 6 -> aview SEGS (w_H W3) m (VAL (A_OBJ 4) + j) = Some 0.
Proof.
intros m md j HJ Hj. rewrite (c2_gbytes 4 [0; 0; 0; 0; 0; 0] m md j ltac:(cbn; tauto) HJ ltac:(cbn; lia)).
f_equal. assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia;
reflexivity.
Qed.

Lemma c2_Z_img : 4096 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 6 <= alloc_ceiling /\ amem_range (VAL (A_OBJ 4)) 6.
Proof.
destruct (blx_marg B (lh_glob B MT HY) (4%nat, 6) ltac:(cbn; tauto)) as [M1 M2]. cbn [fst snd] in *.
pose proof asan_consts as (C1 & _). unfold IMG_HI in M2.
split; [lia|]. split; [lia|]. unfold amem_range, kLowMemEnd. left. lia.
Qed.

(* 0x8046c: bcmp (mac, ZERO, 6), then 0x80470. *)
Lemma c2_bcmp2 : forall (regsT : bvmap 5 word) memT mdT pos' M z,
  c2_regs regsT -> getr regsT 19 = w64 z -> (z = -1 \/ (0 <= z < 5 /\ M <> Boxreg.zero6)) ->
  getr regsT 10 = w64 (lF cx fp + 32) -> getr regsT 11 = w64 (VAL (A_OBJ 4)) -> getr regsT 12 = w64 6 ->
  getr regsT 1 = Z_to_bv 64 (BASE + C2_E) -> length M = 6%nat ->
  c2_mem pos' M memT -> c2_J memT mdT ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (POST cx).
Proof.
intros regsT memT mdT pos' M z GR G19 Hz H10 H11 H12 Hra HL HM HJ.
pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _). pose proof c2_Z_img as (Z0 & Z1 & ZM).
pose proof HM as (HBA & _ & MB).
apply (c2_bcmp_call regsT memT mdT (lF cx fp + 32) (VAL (A_OBJ 4)) _ HJ GR H10 H11 H12 Hra).
- apply ret_ok_codeptr_v; [unfold C2_E; lia | reflexivity].
- intros a Ha. replace a with (lF cx fp + 32 + (a - (lF cx fp + 32))) by lia. rewrite MB by lia. discriminate.
- intros a Ha. replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia. rewrite (c2_Z_bytes memT mdT) by (exact HJ || lia).
  discriminate.
- lia. - lia. - exact Z0. - exact Z1.
- exact (amem_range_sub_app (lF cx fp) 512 (lF cx fp + 32) 6 HFapp HF1 ltac:(lia) ltac:(lia) ltac:(lia)).
- exact ZM.
- exact (c2_mac_ra memT HBA).
- exact (c2_mac_hull memT mdT HJ).
- exact (c2_gra 4 6 memT mdT ltac:(cbn; tauto) ltac:(lia) HJ).
- exact (c2_ghull 4 6 memT mdT ltac:(cbn; tauto) ltac:(lia) HJ).
- intros regs2 mem2 md2 HJ2 HP Hcmp Hkp.
  apply (c2_E_pt regs2 mem2 md2 pos' M z (c2_regs_pres regsT regs2 HP GR)).
  + rewrite <- G19. exact (HP 19 ltac:(unfold acallee_saved; lia)).
  + rewrite Hcmp, (c2_zero6 M HL). split.
    * intros H q Hq. specialize (H q Hq). rewrite MB, (c2_Z_bytes memT mdT q HJ Hq) in H by exact Hq.
      injection H as H. exact H.
    * intros H q Hq. rewrite MB, (c2_Z_bytes memT mdT q HJ Hq) by exact Hq. rewrite (H q Hq). reflexivity.
  + exact Hz.
  + exact (c2_mem_keep pos' M memT mem2 HM Hkp).
  + exact HJ2.
Qed.

Lemma c2_den0 : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. Qed.

Lemma c2_denv : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.

(* At the jal of 0x8046c (bcmp (mac, ZERO, 6)), the engine's call state: c2_bcmp2 takes over. The goal left is
   the fact on idx. *)
Ltac c2_call_bcmp2 HS HE HEI HJ HM GR F19 F21 HL :=
  pmkst HS;
  let R10 := fresh "R10" in let R11 := fresh "R11" in let R12 := fresh "R12" in let R1 := fresh "R1" in
  let R19 := fresh "R19" in
  prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11; prreg HS (12%bv : bv 5) R12;
  prreg HS (1%bv : bv 5) R1; prreg HS (19%bv : bv 5) R19;
  rewrite HE in HS;
  eapply (c2_bcmp2 _ _ _ _ _ _ (c2_regs_call _ _ _ _ HS eq_refl GR));
  [ rewrite R19; exact F19
  |
  | rewrite R10, F21; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
  | rewrite R11; apply (c2_img_atom _ _ HEI); unfold A_OBJ, A_TEXT, A_LIM; lia
  | rewrite R12; reflexivity
  | rewrite R1; reflexivity
  | exact HL
  | exact HM
  | exact HJ ].

(* ---- 0x80454 .. 0x8046c: s11 = fab again; bcmp (r + 56 idx, mac) = 0 (else abort); then bcmp (mac, ZERO) ---- *)
Definition ss_C2 : sstate :=
  mkSS C2_C2 sr_atoms [c2_rs 0x30 (SOff 27 0); c2_rs 0x68 (SOff 21 (-32))] None (mkFacts [C2_AF9] [] []).

Lemma c2_C2_pt : forall regs m md pos' M z,
  c2_regs regs -> getr regs 19 = w64 z -> 0 <= z < 5 -> M <> Boxreg.zero6 ->
  bv_unsigned (getr regs 10) = 0 -> length M = 6%nat -> c2_mem pos' M m -> c2_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C2_C2)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md pos' M z GR G19 Hz HMz G10 HL HM HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _).
pose proof asan_consts as (C1 & _).
pose proof HM as (((_ & _ & _ & _ & _ & _ & _ & _ & _ & SL) & _) & _).
pose proof SL as (_ & _ & S30 & _ & _ & S68 & _).
set (E := Eimg (Ereg regs [])).
assert (U9 : bv_unsigned (ew E 9) = lsp1 cx) by (unfold E; rewrite (c2_ewR regs [] 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (F21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; rewrite (c2_ewR regs [] 21 21%bv eq_refl); exact G21).
assert (F27 : ew E 27 = w64 fab) by (unfold E; rewrite (c2_ewR regs [] 27 27%bv eq_refl); exact G27).
assert (F19 : ew E 19 = w64 z) by (unfold E; rewrite (c2_ewR regs [] 19 19%bv eq_refl); exact G19).
assert (Hfab : 0 <= fab < 2 ^ 64) by exact (c2_rdword_range _ _ _ _ S30).
assert (HS : st_ok_pi SEGS VAL E ss_C2 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + C2_C2)) m (seg_rom SEGS)))).
{ apply c2_seat; [vm_compute; reflexivity | | | ].
  - constructor; [|constructor; [|constructor]].
    + apply (c2_rs_ok E m 0x30 (SOff 27 0) fab U9 S30 (c2_den0 E 27 _ F27) Hfab); lia.
    + apply (c2_rs_ok E m 0x68 (SOff 21 (-32)) (lF cx fp + 32) U9 S68); [| lia | lia | lia].
      rewrite (c2_denv E 21 (lF cx fp + 64) (-32) F21) by lia. f_equal. lia.
  - unfold c2_rs. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. repeat split; unfold YP09.extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia.
  - split; [cbn [f_atoms atoms_ok]; split; [exact (c2_af9 E U9) | exact I] | split; exact I]. }
assert (SHOK : sh_ok SEGS C2Bx [] E (mrestrict (w_H W3) m)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (F10 : ew E 10 = getr regs 10) by (unfold E; exact (c2_ewR regs [] 10 10%bv eq_refl)).
assert (HE : E = Eimg (Ereg regs [])) by reflexivity.
clearbody E. unfold c2_J in HJ.
paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
(* bnez a0 (0x80458): a nonzero bcmp aborts *)
psrr_branch_tok RUN BR HS SHOK C2span; rewrite branch_ne_U, (c2_U_reg E 10 _ F10), c2_U_lit, G10 in Hc.
{ vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
c2_call_bcmp2 HS HE HEI HJ HM GR F19 F21 HL.
right. split; [lia | exact HMz].
Qed.

(* 0x80450: bcmp (r + 56 idx, mac, 6) on the box find returned; its MAC is the MAC, so the result is 0. *)
Lemma c2_bcmp1 : forall (regsT : bvmap 5 word) memT mdT pos' M z,
  c2_regs regsT -> getr regsT 19 = w64 z -> 0 <= z < 5 -> Boxreg.bx_mac bs z = M -> M <> Boxreg.zero6 ->
  getr regsT 10 = w64 (r + 56 * z) -> getr regsT 11 = w64 (lF cx fp + 32) -> getr regsT 12 = w64 6 ->
  getr regsT 1 = Z_to_bv 64 (BASE + C2_C2) -> length M = 6%nat ->
  c2_mem pos' M memT -> c2_J memT mdT ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (POST cx).
Proof.
intros regsT memT mdT pos' M z GR G19 Hz Hmac HMz H10 H11 H12 Hra HL HM HJ.
pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _). pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & _).
pose proof HM as (HBA & _ & MB). pose proof HBA as ((_ & _ & _ & _ & _ & _ & _ & RG & _) & _).
pose proof HINV as ((HLbs & _) & _).
pose proof (c2_ar memT mdT HJ) as HAR.
assert (Hrq : req_size LX_REG = 288) by reflexivity.
assert (RB : forall q, 0 <= q < 6 -> aview SEGS (w_H W3) memT (r + 56 * z + q) =
  Some (bv_unsigned (nth (Z.to_nat q) M (Z_to_bv 8 0)))).
{ intros q Hq. replace (r + 56 * z + q) with (r + (56 * z + q)) by lia.
  unfold lreg, lview in RG. cbn [cms ms_mem mkst] in RG. rewrite RG by (unfold LX_REG; lia).
  rewrite (proj1 (fnd_mac_eq bs M z HLbs HL Hz) Hmac q Hq). reflexivity. }
apply (c2_bcmp_call regsT memT mdT (r + 56 * z) (lF cx fp + 32) _ HJ GR H10 H11 H12 Hra).
- apply ret_ok_codeptr_v; [unfold C2_C2; lia | reflexivity].
- intros a Ha. replace a with (r + 56 * z + (a - (r + 56 * z))) by lia. rewrite RB by lia. discriminate.
- intros a Ha. replace a with (lF cx fp + 32 + (a - (lF cx fp + 32))) by lia. rewrite MB by lia. discriminate.
- lia. - lia. - lia. - lia.
- apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 memT mdT r LX_REG); [exact HAR | exact Hin | lia | rewrite Hrq; lia].
- exact (amem_range_sub_app (lF cx fp) 512 (lF cx fp + 32) 6 HFapp HF1 ltac:(lia) ltac:(lia) ltac:(lia)).
- apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 memT mdT r LX_REG); [exact HAR | exact Hin | lia | rewrite Hrq; lia].
- apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 memT mdT r LX_REG); [exact HAR | exact Hin | lia | rewrite Hrq; lia | lia].
- exact (c2_mac_ra memT HBA).
- exact (c2_mac_hull memT mdT HJ).
- intros regs2 mem2 md2 HJ2 HP Hcmp Hkp.
  apply (c2_C2_pt regs2 mem2 md2 pos' M z (c2_regs_pres regsT regs2 HP GR)).
  + rewrite <- G19. exact (HP 19 ltac:(unfold acallee_saved; lia)).
  + exact Hz.
  + exact HMz.
  + apply (proj2 Hcmp). intros q Hq. rewrite RB, MB by exact Hq. reflexivity.
  + exact HL.
  + exact (c2_mem_keep pos' M memT mem2 HM Hkp).
  + exact HJ2.
Qed.

(* At the jal of 0x80450 (bcmp (r + 56 idx, mac, 6)): c2_bcmp1 takes over. *)
Ltac c2_call_bcmp1 HS HE HEI HJ HM GR F19 F20 F21 HL :=
  pmkst HS;
  let R10 := fresh "R10" in let R11 := fresh "R11" in let R12 := fresh "R12" in let R1 := fresh "R1" in
  let R19 := fresh "R19" in
  prreg HS (10%bv : bv 5) R10; prreg HS (11%bv : bv 5) R11; prreg HS (12%bv : bv 5) R12;
  prreg HS (1%bv : bv 5) R1; prreg HS (19%bv : bv 5) R19;
  rewrite HE in HS;
  eapply (c2_bcmp1 _ _ _ _ _ _ (c2_regs_call _ _ _ _ HS eq_refl GR));
  [ rewrite R19; exact F19 | | |
  | idtac
  | rewrite R11, F21; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia
  | rewrite R12; reflexivity
  | rewrite R1; reflexivity
  | exact HL
  | exact HM
  | exact HJ ].

(* ---- 0x803f4 .. the two bcmp calls: the checks of find's result ---- *)
(* r->n's shadow byte (at sp1 + 0x40's address) is 0: the block's granule r + 280 .. r + 287 is whole. *)
Lemma c2_sa : shadow_addr (r + 280) = SHADOW_OFF + r / 8 + 35 /\
  (r + 288 <= shadow_addr (r + 280) \/ shadow_addr (r + 280) + 1 <= r) /\ shadow_addr (r + 280) + 1 <= alloc_ceiling.
Proof.
pose proof HGr as (Hr16 & Hr0 & Hr1 & _ & _ & Happ). pose proof asan_consts as (C1 & _).
assert (Hr8 : r mod 8 = 0) by (apply (c2_mod8 _ 16); [exact Hr16 | reflexivity | lia]).
assert (E : shadow_addr (r + 280) = SHADOW_OFF + r / 8 + 35).
{ unfold shadow_addr. pose proof (Z.div_mod r 8 ltac:(lia)) as D. rewrite Hr8, Z.add_0_r in D.
  rewrite D at 1. replace (8 * (r / 8) + 280) with ((r / 8 + 35) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (D0 : 0 <= r / 8) by (apply Z.div_pos; lia).
assert (D1 : 8 * (r / 8) <= r) by (apply Z.mul_div_le; lia).
split; [exact E|]. rewrite E. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF.
destruct Happ as [_ [Hlo | [Hhi1 Hhi2]]].
- assert (r / 8 <= 268430848) by (apply Z.div_le_upper_bound; lia). split; [left; lia | lia].
- assert (r / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia). split; [right; lia | lia].
Qed.

Lemma c2_sa_zero : forall m md, c2_J m md -> aview SEGS (w_H W3) m (shadow_addr (r + 280)) = Some 0.
Proof.
intros m md HJ. pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & _).
destruct (al_shadow _ _ LAWS ly3 S3 W3 m md r LX_REG (c2_ar m md HJ) Hin) as [(_ & _ & HBS) _].
change (req_size LX_REG) with 288 in HBS.
pose proof (HBS 35 ltac:(split; [lia | reflexivity])) as H35. change (35 <? 288 / 8) with true in H35.
rewrite (proj1 c2_sa). unfold shadow_of_addr in H35. rewrite <- H35. f_equal; unfold SHADOW_OFF; lia.
Qed.

Lemma c2_vm1 : forall m a, aview SEGS (w_H W3) m a = Some 0 -> val_mem SEGS (mrestrict (w_H W3) m) a 1 0.
Proof.
intros m a H kk Hkk. assert (kk = 0%nat) by lia. subst kk. rewrite Z.add_0_r.
destruct (aview_byte SEGS _ _ _ _ H) as (b & Hb & Hbv & _). rewrite Hb. f_equal. apply bv_eq.
rewrite <- Hbv. reflexivity.
Qed.

Lemma c2_n_val : forall m, c2_base m -> val_mem SEGS (mrestrict (w_H W3) m) (r + 280) 4 (Boxreg.bx_n bs).
Proof.
intros m ((_ & _ & _ & _ & _ & _ & _ & RG & _) & _) kk Hkk.
pose proof HINV as ((HL & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
assert (HA : aview SEGS (w_H W3) m (r + (280 + Z.of_nat kk)) = Some (bv_unsigned (nth (280 + kk) bs (Z_to_bv 8 0)))).
{ unfold lreg, lview in RG. cbn [cms ms_mem mkst] in RG. rewrite RG by (unfold LX_REG; lia).
  replace (Z.to_nat (280 + Z.of_nat kk)) with (280 + kk)%nat by lia. reflexivity. }
destruct (aview_byte SEGS _ _ _ _ HA) as (b & Hb & Hbv & _).
replace (r + 280 + Z.of_nat kk) with (r + (280 + Z.of_nat kk)) by lia. rewrite Hb. f_equal.
replace b with (nth (280 + kk) bs (Z_to_bv 8 0)) by (apply bv_eq; lia). exact (fnd_n_bytes bs HL ltac:(lia) kk Hkk).
Qed.

Lemma c2_blt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.
Lemma c2_bge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.

Lemma c2_swrap : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations. lia.
Qed.

Lemma c2_S_atom : forall E n z, ew E n = w64 z -> - 2 ^ 63 <= z < 2 ^ 63 -> Sg E (SOff n 0) = z.
Proof.
intros E n z H Hz. rewrite S_SOff, H, Z.add_0_r. unfold w64. rewrite Z_to_bv_unsigned. rewrite bv_swrap_wrap.
apply c2_swrap. exact Hz.
Qed.

(* find's result: -1, or the first box that holds the MAC, which then is not the zero MAC. *)
Lemma c2_find_z : forall M z, reac_boxreg_find_c.find_result bs M z ->
  z = -1 \/ (0 <= z < Boxreg.bx_n bs /\ Boxreg.bx_mac bs z = M /\ M <> Boxreg.zero6).
Proof.
intros M z [(_ & ->) | [(HN & Hz & Hm & _) | (_ & -> & _)]]; [left; reflexivity | right | left; reflexivity].
split; [exact Hz|]. split; [exact Hm | exact HN].
Qed.

(* a0 at the jal of 0x80450: r + 56 idx, as the engine leaves it (idx * 56 + r). *)
Lemma c2_a0_b1 : forall E z, ew E 10 = w64 z -> ew E 20 = w64 r -> 0 <= z < 5 ->
  alu64 ALU_ADD (mul_div M_MUL (ew E 10) (Z_to_bv 64 56)) (ew E 20) = w64 (r + 56 * z).
Proof.
intros E z H10 H20 Hz. pose proof HGr as (_ & Hr0 & Hr1 & _). pose proof asan_consts as (C1 & _).
assert (D : alu64 ALU_ADD (mul_div M_MUL (ew E 10) (Z_to_bv 64 56)) (ew E 20) =
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 56)) (SOff 20 0)))
  by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
rewrite D, denot_lit_U, U_SAlu, U_SMd, (c2_U_atom E 10 z H10), (c2_U_atom E 20 r H20), c2_U_lit.
cbn [zalu_raw zmd_raw]. rewrite (Z.mod_small z), (Z.mod_small 56), (Z.mod_small r) by lia.
unfold zcanon, M64. rewrite (Z.mod_small (z * 56)) by lia. rewrite (Z.mod_small (z * 56 + r)) by lia.
unfold w64. f_equal. lia.
Qed.

Definition RC_SH : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition RC_N : YP09.region := YP09.mkRegion (Some 20%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 33 0))].
Definition ss_C : sstate :=
  mkSS C2_C sr_atoms [c2_rs 0x40 (SOff 32 0); RC_SH; c2_rs 0x28 (SOff 20 280); RC_N; c2_rs 0x70 (SOff 34 0);
    c2_rs 0x68 (SOff 21 (-32))] None
    (mkFacts [C2_AF9; (20%nat, mkAF 4096 (2 ^ 47) 4); (33%nat, mkAF 0 5 0)] [] []).

Lemma c2_C_pt : forall regs m md pos' M z,
  c2_regs regs -> getr regs 10 = w64 z -> reac_boxreg_find_c.find_result bs M z ->
  length M = 6%nat -> c2_mem pos' M m -> c2_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C2_C)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md pos' M z GR G10 HFz HL HM HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _).
pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & HrF & Happ). pose proof asan_consts as (C1 & _).
pose proof c2_sa as (ESA & HSA1 & HSA2).
pose proof HINV as ((HLbs & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1.
pose proof HM as (HBA & _). pose proof HBA as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & SL) & _).
pose proof SL as (_ & S28 & _ & _ & S40 & S68 & S70 & _).
set (ex := [w64 (shadow_addr (r + 280)); w64 (Boxreg.bx_n bs); w64 (2 ^ 64 - 1 - r)]).
set (E := Eimg (Ereg regs ex)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j ex (w64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs ex j). }
assert (F32 : ew E 32 = w64 (shadow_addr (r + 280))) by exact (EX 0%nat ltac:(lia)).
assert (F33 : ew E 33 = w64 (Boxreg.bx_n bs)) by exact (EX 1%nat ltac:(lia)).
assert (F34 : ew E 34 = w64 (2 ^ 64 - 1 - r)) by exact (EX 2%nat ltac:(lia)).
assert (U9 : bv_unsigned (ew E 9) = lsp1 cx) by (unfold E; rewrite (c2_ewR regs ex 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (F20 : ew E 20 = w64 r) by (unfold E; rewrite (c2_ewR regs ex 20 20%bv eq_refl); exact G20).
assert (U20 : bv_unsigned (ew E 20) = r) by (rewrite F20; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = shadow_addr (r + 280)) by (rewrite F32; apply unsigned_lit_small; unfold SHADOW_OFF in ESA; lia).
assert (U33 : bv_unsigned (ew E 33) = Boxreg.bx_n bs) by (rewrite F33; apply unsigned_lit_small; lia).
assert (F21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; rewrite (c2_ewR regs ex 21 21%bv eq_refl); exact G21).
assert (F10 : ew E 10 = w64 z) by (unfold E; rewrite (c2_ewR regs ex 10 10%bv eq_refl); exact G10).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HE : E = Eimg (Ereg regs ex)) by reflexivity.
clearbody E ex.
assert (HS : st_ok_pi SEGS VAL E ss_C (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + C2_C)) m (seg_rom SEGS)))).
{ rewrite HE. apply c2_seat; [vm_compute; reflexivity | | | ]; rewrite <- HE.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (c2_rs_ok E m 0x40 (SOff 32 0) (shadow_addr (r + 280)) U9 S40 (c2_den0 E 32 _ F32)); unfold SHADOW_OFF in ESA; lia.
    + unfold region_ok, RC_SH. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. unfold SHADOW_OFF in ESA. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. apply (chunk_ok_val SEGS E _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (c2_vm1 m _ (c2_sa_zero m md HJ)).
    + apply (c2_rs_ok E m 0x28 (SOff 20 280) (r + 280) U9 S28); [| lia | lia | lia].
      exact (c2_denv E 20 r 280 F20 ltac:(lia)).
    + unfold region_ok, RC_N. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor]. apply (chunk_ok_val SEGS E _ _ 280 4 (SOff 33 0) (Boxreg.bx_n bs));
        [exact (c2_den0 E 33 _ F33) | cbn; lia | cbn; lia |].
      exact (c2_n_val m HBA).
    + apply (c2_rs_ok E m 0x70 (SOff 34 0) (2 ^ 64 - 1 - r) U9 S70 (c2_den0 E 34 _ F34)); lia.
    + apply (c2_rs_ok E m 0x68 (SOff 21 (-32)) (lF cx fp + 32) U9 S68); [| lia | lia | lia].
      rewrite (c2_denv E 21 (lF cx fp + 64) (-32) F21) by lia. f_equal. lia.
  - unfold c2_rs, RC_SH, RC_N. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. repeat split; unfold YP09.extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U20, ?U32; unfold SHADOW_OFF in ESA; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [exact (c2_af9 E U9)|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; split; [lia|]; split; [exact Hr16 | lia]|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U33; rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I]. }
assert (SHOK : sh_ok SEGS C2Bx [] E (mrestrict (w_H W3) m)) by constructor.
unfold c2_J in HJ.
paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
(* blt idx, -1 (0x803fc): find's result is -1 or a box index *)
pose proof (c2_find_z M z HFz) as HZ.
psrr_branch_tok RUN BR HS SHOK C2span; rewrite c2_blt, (c2_S_atom E 10 z F10), S_SLit in Hc
  by (destruct HZ as [-> | (? & ? & _)]; lia);
  change (bv_swrap 64 18446744073709551615) with (-1) in Hc.
{ exfalso. apply Z.ltb_lt in Hc. destruct HZ as [-> | (? & ? & _)]; lia. }
clear Hc.
paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
(* bge idx, r->n (0x80414): idx < n *)
psrr_branch_tok RUN BR HS SHOK C2span; rewrite c2_bge, (c2_S_atom E 10 z F10), (c2_S_atom E 33 _ F33) in Hc
  by (destruct HZ as [-> | (? & ? & _)]; lia).
{ exfalso. apply negb_true_iff, Z.ltb_ge in Hc. destruct HZ as [-> | (? & ? & _)]; lia. }
clear Hc.
paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
(* bltz idx (0x80418): idx = -1 goes to 0x8045c *)
psrr_branch_tok RUN BR HS SHOK C2span; rewrite c2_blt, (c2_S_atom E 10 z F10), S_SLit in Hc
  by (destruct HZ as [-> | (? & ? & _)]; lia); change (bv_swrap 64 0) with 0 in Hc.
- apply Z.ltb_lt in Hc. assert (Hz1 : z = -1) by (destruct HZ as [-> | (? & ? & _)]; lia). subst z. clear Hc.
  paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
  c2_call_bcmp2 HS HE HEI HJ HM GR F10 F21 HL.
  left. reflexivity.
- apply Z.ltb_ge in Hc. destruct HZ as [HZ | (Hz0 & Hmac & HMz)]; [lia|]. clear Hc.
  paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
  (* bltu 4, idx (0x80420): the UBSan index check, idx <= 4 *)
  psrr_branch_tok RUN BR HS SHOK C2span; rewrite branch_ltu_U, c2_U_lit, (c2_U_atom E 10 z F10) in Hc;
    rewrite !Z.mod_small in Hc by lia.
  { exfalso. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
  (* bltu ~r, 56 idx (0x80434): the UBSan pointer-overflow check of r + 56 idx *)
  psrr_branch_tok RUN BR HS SHOK C2span;
    rewrite branch_ltu_U, (c2_U_atom E 34 _ F34), U_SMd, (c2_U_atom E 10 z F10), c2_U_lit in Hc;
    cbn [zmd_raw] in Hc; rewrite !(Z.mod_small z), (Z.mod_small 56), (Z.mod_small (2 ^ 64 - 1 - r)) in Hc by lia;
    unfold zcanon, M64 in Hc; rewrite (Z.mod_small (z * 56)) in Hc by lia.
  { exfalso. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK C2span; [awr_ok_tac |]. c2_ro HM.
  c2_call_bcmp1 HS HE HEI HJ HM GR F10 F20 F21 HL.
  + lia.
  + exact Hmac.
  + exact HMz.
  + match goal with R : getr _ 10 = _ |- _ => rewrite R end. exact (c2_a0_b1 E z F10 F20 ltac:(lia)).
Qed.

(* ---- find (r, mac) (0x803f0): reac_boxreg_find's contract through cl_callS ---- *)
(* A callee's own journal (no footprint) keeps every byte the phase's facts speak about. *)
Lemma c2_keep_call : forall STK1 memc mdc mem2 md2 k1,
  ajournal SEGS B STK1 (lsp1 cx) [] ly3 S3 W3 memc mdc [] ly3 S3 W3 mem2 md2 k1 ->
  forall a, c2_at a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memc a.
Proof.
intros STK1 memc mdc mem2 md2 k1 HJ1 a Ha.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
pose proof HGsp as (_ & Hs0 & Hs1 & _). pose proof HGF as (HF0 & HF1 & _ & _ & HFeq).
pose proof HGr as (_ & Hr0 & Hr1 & Hin & _). pose proof HGin as (Hn0 & Hp0 & Hp1 & Hpin & _).
pose proof asan_consts as (C1 & _).
assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct Ha as [H|[H|[H|[H|H]]]].
- apply F1; lia.
- pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. unfold lc_n in *.
  replace a with (lc_p cx + (a - lc_p cx)) by lia.
  apply (F2 (lc_p cx) (lc_n cx) (a - lc_p cx) Hpin Hpin); [unfold lc_n; lia | apply inFP_nil].
- apply (F4 LX_CID fp a Hfin); [| apply inFP_nil]. left. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite HFeq. change (fs_frame_bytes LX_CID) with 512. lia.
- apply (F4 LX_CID fp a Hfin); [| apply inFP_nil]. right. unfold in_zr. cbn [fst snd].
  rewrite HFeq. change (fs_frame_bytes LX_CID / 8) with 64. exact H.
- replace a with (r + (a - r)) by lia.
  apply (F2 r LX_REG (a - r) Hin Hin); [change (req_size LX_REG) with 288; lia | apply inFP_nil].
Qed.

(* The call chain the walk's program callees get at sp1 (lx_achain at the phase's layout). *)
Lemma c2_achain : forall m md, c2_base m -> c2_J m md ->
  achain ly3 (aview SEGS (w_H W3) m) (lsp1 cx) (lsp0 cx) (lch cx).
Proof.
intros m md ((SV & _) & _) HJ.
pose proof HB as ((HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & _). pose proof asan_consts as (C1 & _).
destruct SV as (Sra & Sj). unfold lview in Sra, Sj. cbn [cms ms_mem mkst] in Sra, Sj.
apply (achain_ly_top (lc_ly cx) ly3 _ _ _ _ Etop).
eapply lx_achain.
- exact Hch.
- unfold lsp0 in *. lia.
- unfold lsp0 in *. lia.
- apply (c2_mod8 _ 16); [exact Hs16 | reflexivity | lia].
- exact Hra4.
- intros a Ha. apply F1; [lia | unfold LX_STK; lia].
- exact Sra.
- pose proof (Sj 0 ltac:(lia)) as S0. rewrite Z.mul_0_r, Z.sub_0_r in S0. rewrite S0. reflexivity.
- lia.
Qed.

Lemma c2_find : forall (regsc : bvmap 5 word) memc mdc pos' M,
  c2_regs regsc -> getr regsc 10 = w64 r -> getr regsc 11 = w64 (lF cx fp + 32) ->
  getr regsc 1 = Z_to_bv 64 (BASE + C2_C) -> length M = 6%nat -> c2_mem pos' M memc -> c2_J memc mdc ->
  SRr SEGS W3 (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA BB_reac_boxreg_find)) memc (seg_rom SEGS)) mdc) (POST cx).
Proof.
intros regsc memc mdc pos' M GR H10 H11 Hra HL HM HJ.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & _). pose proof c2_gptp as (Hgp & Htp).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGF as (HF0 & HF1 & HF64 & HFapp & HFeq).
pose proof HGr as (Hr16 & Hr0 & Hr1 & Hin & _). pose proof asan_consts as (C1 & _).
pose proof HINV as ((HLbs & HB1 & _) & _).
pose proof HM as (HBA & _ & MB). pose proof HBA as ((_ & _ & _ & _ & _ & _ & _ & RG & _) & _).
assert (WS : REAC_BOXREG_FIND_STKB = 8272) by reflexivity.
assert (Hsp : spZ regsc = lsp0 cx + (lsp1 cx - lsp0 cx)) by (unfold spZ; rewrite G2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (HFO : afobj SEGS B ly3 S3 W3 memc (lF cx fp + 32) 6).
{ split; [exists LX_CID, fp; rewrite HFeq; split; [rewrite HFR; left; reflexivity|] |].
  - change (fs_frame_bytes LX_CID) with 512. split; [unfold LX_CID; lia|].
    split; [apply (c2_mod8 _ 64); [exact HF64 | reflexivity | lia] | lia].
  - split; [| exact (c2_mac_ra memc HBA)].
    replace (lF cx fp + 32) with (lF cx fp + 4 * 8) by lia. rewrite Z.mod_add by lia.
    apply (c2_mod8 _ 64); [exact HF64 | reflexivity | lia]. }
rewrite pa_sigma_reac_boxreg_find.
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 regsc memc _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 mdc k REAC_BOXREG_FIND_STKB [] 0 (lsp1 cx - lsp0 cx) (getr regsc 1) (lch cx)
    (fun ly' S' W' regs' mem' md' =>
       ly' = ly3 /\ S' = S3 /\ W' = W3 /\ Permutation (ablocks B ly' S') (ablocks B ly3 S3) /\
       (forall q, 0 <= q < REG_SIZEB ->
          aview SEGS (w_H W') mem' (r + q) = Some (bv_unsigned (nth (Z.to_nat q) bs (Z_to_bv 8 0)))) /\
       (forall q, 0 <= q < 6 ->
          aview SEGS (w_H W') mem' (lF cx fp + 32 + q) = Some (bv_unsigned (nth (Z.to_nat q) M (Z_to_bv 8 0)))) /\
       exists z, getr regs' 10 = w64 z /\ reac_boxreg_find_c.find_result bs M z) HJ Hsp c2_o16).
  - lia.
  - rewrite WS. lia.
  - rewrite WS. unfold LX_STK. lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - reflexivity.
  - rewrite Hra. apply ret_ok_codeptr_v; [unfold C2_C; lia | reflexivity].
  - rewrite Hra. pose proof (pa_base_lo (PL := PL_boxb) (PI := PI)) as HBLO. pose proof pa_B_ok as (HB0 & HB1' & _).
    rewrite unsigned_lit_small by (unfold C2_C; lia). unfold C2_C. lia.
  - replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia. unfold s0Z. rewrite G8. unfold w64.
    rewrite unsigned_lit_small by lia. exact (c2_achain memc mdc HBA HJ).
  - intros HPRE. exact (lh_find B MT HY ly3 S3 W3 regsc memc mdc (lch cx) r (lF cx fp + 32) bs M HPRE H10 H11 Hin HLbs
      (fun q Hq => RG q Hq) HB1 HFO HL MB).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (-> & -> & -> & _ & _ & _ & (z & Hz10 & HFz))).
rewrite Z.add_0_r in HJ2. replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HJc by lia.
rewrite Hra.
exact (c2_C_pt regs2 mem2 md2 pos' M z (c2_regs_pres regsc regs2 HP GR) Hz10 HFz HL
  (c2_mem_keep pos' M memc mem2 HM (c2_keep_call _ _ _ _ _ _ HJc)) HJ2).
Qed.

(* ---- 0x803e8 .. 0x803f0: a0 = r, a1 = mac, find ---- *)
Definition ss_B : sstate := mkSS C2_B sr_atoms [] None (mkFacts [] [] []).

Lemma c2_B_pt : forall regs m md pos' M,
  c2_regs regs -> getr regs 19 = w64 (lF cx fp + 32) -> length M = 6%nat -> c2_mem pos' M m -> c2_J m md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + C2_B)) m (seg_rom SEGS)) md) (POST cx).
Proof.
intros regs m md pos' M GR G19 HL HM HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & G18 & G22 & G20 & G21 & G27).
pose proof (c2_seat regs [] m C2_B [] (mkFacts [] [] []) eq_refl (Forall_nil _) I (conj I (conj I I))) as HS.
assert (SHOK : sh_ok SEGS C2Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W3) m)) by constructor.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (F19 : ew E 19 = w64 (lF cx fp + 32)) by (subst E; rewrite (c2_ewR regs [] 19 19%bv eq_refl); exact G19).
assert (F20 : ew E 20 = w64 r) by (subst E; rewrite (c2_ewR regs [] 20 20%bv eq_refl); exact G20).
unfold c2_J in HJ.
paj_run_tok RUN HS HJ SHOK C2span; [apply awr_ok_nil |]. c2_ro HM.
pmkst HS. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
rewrite HE in HS.
apply (c2_find _ _ _ pos' M (c2_regs_call _ _ _ _ HS eq_refl GR)).
- rewrite Q10. exact F20.
- rewrite Q11. exact F19.
- rewrite Q1. reflexivity.
- exact HL.
- exact HM.
- exact HJ.
Qed.

(* ---- read_mac (&in, op & 4, mac) (0x803e4): BoxBReadMac.v's caller-journal contract ---- *)
Lemma c2_rm_len : forall full pl, length (tbread_mac_out full pl) = 6%nat.
Proof.
intros full pl. unfold tbread_mac_out. destruct (full =? 0).
- rewrite length_app, length_firstn, length_app. cbn [length tbread_mac_base map]. lia.
- rewrite length_firstn, length_app, repeat_length. lia.
Qed.

Lemma c2_used : forall full len, 0 <= len -> 0 <= tbread_mac_used full len <= len.
Proof. intros full len H. unfold tbread_mac_used. destruct (full =? 0); lia. Qed.

(* The cursor's 16 bytes lie in the machine stack, whose shadow AR keeps zero. *)
Lemma c2_stack_ra : forall m md, c2_J m md ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (lsp1 cx + 0x88) 16.
Proof.
intros m md HJ. pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof HB as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HGsp as (_ & Hs0 & Hs1 & _).
pose proof (al_zshadow _ _ LAWS ly3 S3 W3 m md (ly_stk_lo ly3, ly_stk_hi ly3 - ly_stk_lo ly3) HAR
  ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ. cbn [fst snd] in HZ.
rewrite Eslo, Eshi in HZ. fold (lsp0 cx) in Hslo, Hshi. unfold LX_STK in Hslo.
set (lo := ly_stk_lo (lc_ly cx)) in *. set (hi := ly_stk_hi (lc_ly cx)) in *.
intros x Hx. exists 0. split; [| left; reflexivity].
assert (D1 : 8 * (x / 8) <= x) by (apply Z.mul_div_le; lia).
pose proof (Z.div_mod lo 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as D3.
pose proof (Z.div_mod (hi - lo) 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound (hi - lo) 8 ltac:(lia)) as D5.
pose proof (Z.div_mod x 8 ltac:(lia)) as D6. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D7.
replace (shadow_of_addr SHADOW_OFF x) with (shadow_of_addr SHADOW_OFF lo + (x / 8 - lo / 8))
  by (unfold shadow_of_addr; lia).
apply HZ. lia.
Qed.

Lemma c2_afobj : forall m, c2_base m -> afobj SEGS B ly3 S3 W3 m (lF cx fp + 32) 6.
Proof.
intros m HBA. pose proof HGF as (HF0 & HF1 & HF64 & HFapp & HFeq).
split; [exists LX_CID, fp; rewrite HFeq; split; [rewrite HFR; left; reflexivity|] |].
- change (fs_frame_bytes LX_CID) with 512. split; [unfold LX_CID; lia|].
  split; [apply (c2_mod8 _ 64); [exact HF64 | reflexivity | lia] | lia].
- split; [| exact (c2_mac_ra m HBA)].
  replace (lF cx fp + 32) with (lF cx fp + 4 * 8) by lia. rewrite Z.mod_add by lia.
  apply (c2_mod8 _ 64); [exact HF64 | reflexivity | lia].
Qed.

(* read_mac's keep (tbcj_kept) is the phase's keep outside the cursor and mac. *)
Lemma c2_keep_rm : forall memc mem2,
  tbcj_kept B READ_MAC_STKB ly3 S3 W3 memc W3 mem2 (lsp1 cx)
    (fun a => lsp1 cx + 0x88 <= a < lsp1 cx + 0x88 + 16 \/ lF cx fp + 32 <= a < lF cx fp + 32 + 6) ->
  forall a, c2_at a -> ~ c2_wr a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memc a.
Proof.
intros memc mem2 (K1 & K2 & _ & K4 & _) a Ha Hw.
pose proof HGsp as (_ & Hs0 & Hs1 & _). pose proof HGF as (HF0 & HF1 & _ & _ & HFeq).
pose proof HGr as (_ & Hr0 & Hr1 & Hin & _). pose proof HGin as (Hn0 & Hp0 & Hp1 & Hpin & _).
pose proof asan_consts as (C1 & _).
assert (HRM : READ_MAC_STKB = 4128) by reflexivity.
assert (NE : forall x, ~ c2_wr x -> ~ (lsp1 cx + 0x88 <= x < lsp1 cx + 0x88 + 16 \/ lF cx fp + 32 <= x < lF cx fp + 32 + 6))
  by (intros x Hx Hc; apply Hx; unfold c2_wr; lia).
assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct Ha as [H|[H|[H|[H|H]]]].
- apply K1; [lia | rewrite HRM; lia | exact (NE a Hw)].
- pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. unfold lc_n in *.
  replace a with (lc_p cx + (a - lc_p cx)) by lia.
  apply (K2 (lc_p cx) (lc_n cx) (a - lc_p cx) Hpin); [unfold lc_n; lia | replace (lc_p cx + (a - lc_p cx)) with a by lia; exact (NE a Hw)].
- apply (K4 LX_CID fp a Hfin); [| exact (NE a Hw)]. left. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite HFeq. change (fs_frame_bytes LX_CID) with 512. lia.
- apply (K4 LX_CID fp a Hfin); [| exact (NE a Hw)]. right. unfold in_zr. cbn [fst snd].
  rewrite HFeq. change (fs_frame_bytes LX_CID / 8) with 64. exact H.
- replace a with (r + (a - r)) by lia.
  apply (K2 r LX_REG (a - r) Hin); [change (req_size LX_REG) with 288; lia | replace (r + (a - r)) with a by lia; exact (NE a Hw)].
Qed.

(* full = op & 4, as the register a1 holds it (any value: the cut K does not depend on the MAC or the cursor's
   advance). *)
Lemma c2_read_mac : forall (regsc : bvmap 5 word) memc mdc,
  c2_regs regsc -> getr regsc 19 = w64 (lF cx fp + 32) -> getr regsc 10 = w64 (lsp1 cx + 0x88) ->
  getr regsc 12 = w64 (lF cx fp + 32) ->
  getr regsc 1 = Z_to_bv 64 (BASE + C2_B) -> c2_base memc -> lcur cx W3 (cms memc) (S pos) -> c2_J memc mdc ->
  SRr SEGS W3 (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA BB_read_mac)) memc (seg_rom SEGS)) mdc) (POST cx).
Proof.
intros regsc memc mdc GR G19 H10 H12 Hra HBA (Hcp & C88 & C90) HJ.
set (full := bv_unsigned (getr regsc 11)).
assert (H11 : getr regsc 11 = w64 full) by (unfold full, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hfull : 0 <= full < 2 ^ 64) by (unfold full; pose proof (bv_unsigned_in_range 64 (getr regsc 11)) as R;
  change (bv_modulus 64) with (2 ^ 64) in R; exact R).
clearbody full.
pose proof GR as (G2 & G8 & G9 & G3 & G4 & _). pose proof c2_gptp as (Hgp & Htp).
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGF as (HF0 & HF1 & HF64 & HFapp & HFeq).
pose proof HGin as (Hn0 & Hp0 & Hp1 & Hpin & _). pose proof asan_consts as (C1 & _).
pose proof HBA as ((_ & _ & _ & _ & _ & _ & GI & _) & _).
pose proof (c2_ar memc mdc HJ) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof HB as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & _). fold (lsp0 cx) in Hslo, Hshi.
assert (HRM : READ_MAC_STKB = 4128) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : spZ regsc = lsp1 cx) by (unfold spZ; rewrite G2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
set (pl := skipn (S pos) (lc_pl cx)).
assert (Hlpl : Z.of_nat (length pl) = lc_n cx - Z.of_nat (S pos)) by (unfold pl; rewrite length_skipn; unfold lc_n; lia).
assert (HFO := c2_afobj memc HBA).
rewrite pa_sigma_read_mac.
eapply SRr_bind.
{ apply (lh_read_mac B MT HY LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 memc mdc k regsc (lsp1 cx + 0x88) full (lF cx fp + 32)
    (lc_p cx + Z.of_nat (S pos)) (lc_p cx) (lc_n cx) pl HJ).
  - rewrite Hra. apply ret_ok_codeptr_v; [unfold C2_B; lia | reflexivity].
  - unfold raZ. rewrite Hra. pose proof (pa_base_lo (PL := PL_boxb) (PI := PI)) as HBLO.
    pose proof pa_B_ok as (HB0 & HB1' & _). rewrite unsigned_lit_small by (unfold C2_B; lia). unfold C2_B. lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - rewrite Hsp. apply Z.mod_divide; [lia|]. pose proof HGsp as (_ & _ & _ & H32).
    apply Z.mod_divide in H32; [|lia]. destruct H32 as [q' Hq']. exists (2 * q'). lia.
  - rewrite Hsp, HRM. unfold LX_STK. lia.
  - rewrite Hsp. lia.
  - exact H10.
  - exact H11.
  - exact H12.
  - lia.
  - replace (lsp1 cx + 0x88) with (lsp1 cx + 17 * 8) by lia. rewrite Z.mod_add by lia.
    apply (c2_mod8 _ 32); [exact Hs32 | reflexivity | lia].
  - rewrite Hsp. lia.
  - apply (val_mem_of_rdword SEGS (w_H W3) memc). exact C88.
  - rewrite Hlpl. replace (lsp1 cx + 0x88 + 8) with (lsp1 cx + 0x90) by lia.
    apply (val_mem_of_rdword SEGS (w_H W3) memc). exact C90.
  - exact (c2_stack_ra memc mdc HJ).
  - intros a Ha. split; [left; unfold LX_STK; lia|]. split; [apply HPRES; unfold LX_STK; lia|].
    split; [apply (al_stack _ _ LAWS ly3 S3 W3 memc mdc a HAR); rewrite Eslo, Eshi; unfold LX_STK in Hslo; lia|].
    rewrite Hsp, Hes. lia.
  - unfold lc_n in *. lia.
  - intros _. split; [exact Hpin|]. unfold lc_n in *. lia.
  - intros q Hq. unfold pl in *. rewrite Hlpl in Hq.
    assert (Hj : (S pos + Z.to_nat q < length (map (fun b : byte => bv_unsigned b) (lc_pl cx)))%nat)
      by (rewrite length_map; unfold lc_n in Hq; lia).
    destruct (GI _ Hj) as [Hv Hb].
    replace (lc_p cx + Z.of_nat (S pos) + q) with (lc_p cx + Z.of_nat (S pos + Z.to_nat q)) by lia.
    rewrite (aview_of_val_mem1 SEGS _ _ _ _ Hv Hb).
    rewrite nth_skipn. f_equal. rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) by exact Hj.
    rewrite map_nth. reflexivity.
  - exact HFO.
  - pose proof (al_frames _ _ LAWS ly3 S3 W3 memc mdc LX_CID fp HAR ltac:(rewrite HFR; left; reflexivity))
      as (_ & _ & HFP & _). rewrite HFeq in HFP. change (fs_frame_bytes LX_CID) with 512 in HFP.
    intros a Ha. destruct (HFP a ltac:(lia)) as [Hpr Hno]. split.
    + right; right; right. exists LX_CID, fp. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite HFeq. change (fs_frame_bytes LX_CID) with 512. lia.
    + split; [exact Hpr|]. split; [exact Hno|]. rewrite Hsp, Hes. lia.
  - left. lia.
  - left. rewrite Hsp, HRM. lia.
  - intros q Hq. rewrite (c2_gbytes 6 [0; 64; 171; 0; 0] memc mdc q ltac:(cbn; tauto) HJ ltac:(cbn; lia)).
    assert (q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4) as [-> | [-> | [-> | [-> | ->]]]] by lia; reflexivity.
  - exact (c2_gra 6 5 memc mdc ltac:(cbn; tauto) ltac:(lia) HJ).
  - exact (c2_ghull 6 5 memc mdc ltac:(cbn; tauto) ltac:(lia) HJ). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HMB & HC0 & HC8 & HKP).
rewrite Hsp in HKP.
pose proof (c2_used full (Z.of_nat (length pl)) ltac:(lia)) as Hu.
set (used := tbread_mac_used full (Z.of_nat (length pl))) in *.
rewrite Hra.
apply (c2_B_pt regs2 mem2 md2 (S pos + Z.to_nat used) (tbread_mac_out full pl) (c2_regs_pres regsc regs2 HP GR)).
- rewrite <- G19. exact (HP 19 ltac:(unfold acallee_saved; lia)).
- apply c2_rm_len.
- split; [exact (c2_base_keep memc mem2 HBA (c2_keep_rm memc mem2 HKP))|]. split.
  + split; [unfold lc_n in *; lia|]. split.
    * unfold lslot, lview. cbn [cms ms_mem mkst]. apply (rdword_of_val_mem SEGS (w_H W3) mem2); [|lia].
      replace (lc_p cx + Z.of_nat (S pos + Z.to_nat used)) with (lc_p cx + Z.of_nat (S pos) + used) by lia. exact HC0.
    * unfold lslot, lview. cbn [cms ms_mem mkst]. apply (rdword_of_val_mem SEGS (w_H W3) mem2); [|unfold lc_n in *; lia].
      replace (lsp1 cx + 0x90) with (lsp1 cx + 0x88 + 8) by lia.
      replace (lc_n cx - Z.of_nat (S pos + Z.to_nat used)) with (Z.of_nat (length pl) - used) by lia. exact HC8.
  + intros j Hj. exact (HMB j Hj).
- exact HJ2.
Qed.

(* ---- T (0x8034c) .. 0x803e4: the switch to case 2, i to sp1 + 0x58, read_mac's arguments ---- *)
Definition RA_58 : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x60 0x58 0x60 [].
Definition ss_A : sstate := mkSS LP_T sr_atoms [RA_58; c2_rs 0x68 (SOff 21 (-32))] None (mkFacts [C2_AF9] [] []).

(* The window of slot 0x58: a run of ss_A changes no other byte. *)
Ltac c2_wkeep KA :=
  lazymatch type of KA with forall a, _ -> _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
  match goal with HFr : frame_of ?Ex ?rs (mrestrict _ m1) (mrestrict _ ?m2) |- _ =>
    let K := fresh "KA" in
    assert (K : forall a, c2_at a -> ~ (lsp1 cx + 0x58 <= a < lsp1 cx + 0x60) ->
                aview SEGS (w_H W3) m2 a = aview SEGS (w_H W3) m0 a);
    [ intros a Ha Hn; etransitivity; [|exact (KA a Ha Hn)];
      apply (kept_of_frame Ex rs _ m1 m2 (fun x => lsp1 cx + 0x58 <= x < lsp1 cx + 0x60) HFr);
      [ let rs' := eval vm_compute in (windows rs) in change (windows rs) with rs';
        intros bb wlo whi aa Hwin Hr; cbn [In] in Hwin;
        repeat (destruct Hwin as [Hwin | Hwin]; [injection Hwin as <- <- <-; cbn [base_val] in Hr;
          lazymatch goal with U9 : bv_unsigned (ew Ex 9) = _ |- _ => rewrite U9 in Hr end; cbv beta; lia |]);
        destruct Hwin
      | exact (proj1 (c2_at_rng a Ha))
      | exact Hn ]
    | clear KA; rename K into KA ] end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac c2_awrA U9 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (lsp1 cx - lsp0 cx));
  [ reflexivity | rewrite U9; lia | cbn; unfold LX_STK; lia | cbn; lia | ];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.

Lemma c2_T : forall (ms3 : machine_state) md3,
  lx_body cx fp LP_T W3 ms3 LSH_iter -> lreg W3 ms3 r bs -> lprev cx fp W3 ms3 bs -> lcur cx W3 ms3 (S pos) ->
  lslots_loop cx fp W3 ms3 r fab ->
  getr (ms_regs ms3) 19 = w64 1 -> getr (ms_regs ms3) 20 = w64 r -> getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) ->
  getr (ms_regs ms3) 23 = w64 op -> getr (ms_regs ms3) 24 = w64 (Z.of_nat i) -> getr (ms_regs ms3) 27 = w64 fab ->
  c2_J (ms_mem ms3) md3 -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros ms3 md3 HBODY RG PV CUR SL G19 G20 G21 G23 G24 G27 HJ.
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfcsr & (G2 & G8 & G9 & G3 & G4 & G18 & G22) & SV & SH & FL & S10 & S18 & S80 & GI).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HGsp as (Hs16 & Hs0 & Hs1 & Hs32). pose proof HGF as (HF0 & HF1 & HF64 & HFapp & _).
pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
pose proof SL as (_ & _ & _ & _ & _ & S68 & _).
assert (Hopr : 0 <= op < 256).
{ rewrite Hop. pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R. }
assert (GR : c2_regs (ms_regs ms3)) by (repeat split; assumption).
assert (BP : c2_bpre (ms_mem ms3)) by exact (conj SV (conj SH (conj FL (conj S10 (conj S18 (conj S80 (conj GI (conj RG (conj PV SL))))))))).
assert (Hms : restrict (w_H W3) ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + LP_T)) (mrestrict (w_H W3) (ms_mem ms3))
  (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hsvc, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
set (E := Eimg (Ereg (ms_regs ms3) [])).
assert (U9 : bv_unsigned (ew E 9) = lsp1 cx) by (unfold E; rewrite (c2_ewR _ [] 9 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (F19 : ew E 19 = w64 1) by (unfold E; rewrite (c2_ewR _ [] 19 19%bv eq_refl); exact G19).
assert (F21 : ew E 21 = w64 (lF cx fp + 64)) by (unfold E; rewrite (c2_ewR _ [] 21 21%bv eq_refl); exact G21).
assert (F23 : ew E 23 = w64 op) by (unfold E; rewrite (c2_ewR _ [] 23 23%bv eq_refl); exact G23).
assert (F24 : ew E 24 = w64 (Z.of_nat i)) by (unfold E; rewrite (c2_ewR _ [] 24 24%bv eq_refl); exact G24).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HE : E = Eimg (Ereg (ms_regs ms3) [])) by reflexivity.
assert (HS : st_ok_pi SEGS VAL E ss_A (restrict (w_H W3) ms3)).
{ assert (HS0 : st_ok_pi SEGS VAL E ss_A
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + LP_T)) (ms_mem ms3) (seg_rom SEGS))));
  [| rewrite restrict_mkst_fx, <- Hms in HS0; exact HS0].
  apply c2_seat; [vm_compute; reflexivity | | | ]; fold E.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, RA_58. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPRES. unfold LX_STK. lia.
    + apply (c2_rs_ok E (ms_mem ms3) 0x68 (SOff 21 (-32)) (lF cx fp + 32) U9 S68); [| lia | lia | lia].
      rewrite (c2_denv E 21 (lF cx fp + 64) (-32) F21) by lia. f_equal. lia.
  - unfold c2_rs, RA_58. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. repeat split; unfold YP09.extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia.
  - split; [cbn [f_atoms atoms_ok]; split; [exact (c2_af9 E U9) | exact I] | split; exact I]. }
clearbody E.
assert (SHOK : sh_ok SEGS C2Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
assert (KA : forall a, c2_at a -> ~ (lsp1 cx + 0x58 <= a < lsp1 cx + 0x60) ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
unfold c2_J in HJ.
paj_run_tok RUN HS HJ SHOK C2span; [c2_awrA U9 |]. c2_wkeep KA.
(* blt 1, op & 3 (0x80354): the switch's first test, op & 3 = 2 *)
assert (UAND : U E (SAlu ALU_AND (SOff 23 0) (SLit 3)) = 2)
  by (rewrite U_and_lit by lia; rewrite (c2_U_atom E 23 op F23), Z.mod_small by lia; exact Hop3).
assert (U19 : U E (SOff 19 0) = 1) by (rewrite (c2_U_atom E 19 1 F19); reflexivity).
psrr_branch_tok RUN BR HS SHOK C2span; rewrite c2_blt, !S_of_U, U19, UAND in Hc;
  change (bv_swrap 64 1) with 1 in Hc; change (bv_swrap 64 2) with 2 in Hc.
2:{ exfalso. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK C2span; [c2_awrA U9 |]. c2_wkeep KA.
(* bne op & 3, 2 (0x803d0) *)
psrr_branch_tok RUN BR HS SHOK C2span; rewrite branch_ne_U, UAND, (c2_U_lit E 2) in Hc.
{ exfalso. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_tok RUN HS HJ SHOK C2span; [c2_awrA U9 |]. c2_wkeep KA.
(* the call of read_mac (0x803e4) *)
pmkst HS.
lazymatch goal with HSc : st_ok _ _ ?ssc (restrict _ ?msn) |- _ =>
  assert (S58 : lslot cx W3 (cms (ms_mem msn)) 0x58 (Z.of_nat i));
  [ unfold lslot, lview; cbn [cms ms_mem mkst];
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msn)); [|lia];
    apply (field_of_region E _ 9%nat (lsp1 cx) [YP09.mkChunk 0x58 (CVal 8 (SOff 24 0))] 0x58 0x60 0x58 0x60 0x58 8
      (SOff 24 0) (Z.of_nat i) (st_ok_region_nth E ssc _ 0%nat _ HSc eq_refl) U9 ltac:(left; reflexivity));
    [ exact (c2_den0 E 24 _ F24) | cbn; lia | cbn; lia ]
  | ] end.
prreg HS (10%bv : bv 5) Q10. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
prreg HS (19%bv : bv 5) Q19.
rewrite HE in HS.
apply (c2_read_mac _ _ _ (c2_regs_call _ _ _ _ HS eq_refl GR)).
- rewrite Q19, F21. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
- rewrite Q10. unfold w64. rewrite U9. reflexivity.
- rewrite Q12, F21. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
- rewrite Q1. reflexivity.
- split; [| exact S58].
  apply (c2_bpre_keep (fun a => lsp1 cx + 0x58 <= a < lsp1 cx + 0x60) (ms_mem ms3) _ BP);
    [intros a Ha; right; exact Ha | intros a Ha Hn; exact (KA a Ha Hn)].
- split; [exact (proj1 CUR)|]. pose proof CUR as (_ & C88 & C90). split.
  + unfold lslot, lview in *. cbn [cms ms_mem mkst] in *.
    eapply (c2_rdword_keep _ _ _ _); [|exact C88]. intros q Hq. apply KA; [left; lia | lia].
  + unfold lslot, lview in *. cbn [cms ms_mem mkst] in *.
    eapply (c2_rdword_keep _ _ _ _); [|exact C90]. intros q Hq. apply KA; [left; lia | lia].
- exact HJ.
Qed.

End c.

(* ---- the phase ---- *)
#[local] Notation POSTT := (lxcx -> world SEGS -> config -> Prop).

Theorem lx_case2 : forall (POST : POSTT) i, lx_from B MT POST (LI_K B MT i) -> lx_from B MT POST (LI_T B MT 2 i).
Proof.
intros POST i HK cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (pos & r & fab & op & bs & HBODY & Hi & Hk & Hacc & HBLK & RG & HINV & HFAB & PV & Hpos & Hop & Hop3
  & CUR & SL & G19 & G20 & G21 & G23 & G24 & G26 & G27).
pose proof HB as (HPRE & _ & _ & Hin0 & _ & Hfr0 & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & Hly & _).
pose proof asan_consts as (C1 & _).
assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 (proj1 (proj2 HJ))) as (_ & Efa & _).
assert (HFeq : frame_addr ly3 LX_CID fp = lF cx fp) by (unfold lF; apply Efa).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ LX_CID fp HAR Hfin) as (HF0 & HFc & HFapp).
rewrite HFeq in HF0, HFc, HFapp. change (fs_frame_bytes LX_CID) with 512 in HF0, HFc, HFapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 LX_CID fp HAR Hfin) as (HF64 & _).
rewrite HFeq in HF64.
assert (Hinr : In (r, LX_REG) (ablocks B ly3 S3)) by (unfold lblk in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR Hinr) as (Hr16 & Hr0 & Hr1 & Happr & _).
change (req_size LX_REG) with 288 in Hr1, Happr.
assert (Hn0 : 0 < lc_n cx).
{ destruct Hin0 as [Hn0 | (Hn & _)]; [|lia]. exfalso.
  assert (length (lc_pl cx) = 0%nat) by (unfold lc_n in Hn0; lia). lia. }
assert (Hinp : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)).
{ unfold lblk in HBLK; rewrite HBLK; apply in_or_app; left.
  destruct Hin0 as [Hz0 | (_ & Hin)]; [unfold lc_n in *; lia | exact Hin]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (lc_p cx) (lc_n cx) HAR Hinp) as (_ & Hp0 & Hp1 & _).
pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hrq]. unfold lc_n in Hp1, Hrq.
assert (HrF : r + 288 <= lF cx fp \/ lF cx fp + 512 <= r).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r LX_REG LX_CID fp HAR Hinr Hfin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFeq in D. change (req_size LX_REG) with 288 in D.
  change (fs_frame_bytes LX_CID) with 512 in D. exact D. }
assert (HpF : lc_p cx + lc_n cx <= lF cx fp \/ lF cx fp + 512 <= lc_p cx).
{ pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (lc_p cx) (lc_n cx) LX_CID fp HAR Hinp Hfin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFeq in D. change (fs_frame_bytes LX_CID) with 512 in D.
  unfold lc_n in *. lia. }
assert (Hpr : lc_p cx + lc_n cx <= r \/ r + 288 <= lc_p cx \/ (lc_p cx = r /\ lc_n cx = 288)).
{ destruct (Z.eq_dec (lc_p cx) r) as [Hpe | Hpe].
  - destruct (Z.eq_dec (lc_n cx) 288) as [Hne | Hne]; [right; right; split; assumption|].
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (lc_p cx) (lc_n cx) r LX_REG HAR Hinp Hinr
      ltac:(intros Heq; injection Heq as _ Hna; exact (Hne Hna))) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (req_size LX_REG) with 288 in D. unfold lc_n in *. lia.
  - pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (lc_p cx) (lc_n cx) r LX_REG HAR Hinp Hinr
      ltac:(intros Heq; injection Heq as Hpa _; exact (Hpe Hpa))) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. change (req_size LX_REG) with 288 in D. unfold lc_n in *. lia. }
assert (Hsp1 : lsp0 cx - 287 <= lsp1 cx <= lsp0 cx - 256 /\ lsp1 cx mod 32 = 0).
{ unfold lsp1. pose proof (Z.div_mod (lsp0 cx - 256) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (lsp0 cx - 256) 32 ltac:(lia)) as Hmp.
  split; [lia|]. rewrite Z.mul_comm, Z_mod_mult. reflexivity. }
unfold lsp0 in Hal16, Hstk0, Hslo, Hshi, H47.
eapply (c2_T POST i cx fp k acc ly3 S3 W3 pos r fab op bs HB HFR HMO HK Hi Hk Hacc HBLK HINV HFAB Hpos Hop Hop3);
  try eassumption.
- unfold LX_STK in Hslo. split; [exact Hal16|].
  split; [change (lsp0 cx) with (spZ (lc_regs cx)); split; lia|].
  split; [exact (proj1 Hsp1) | exact (proj2 Hsp1)].
- split; [exact HF0|]. split; [exact HFc|]. split; [exact HF64|]. split; [exact HFapp | exact HFeq].
- split; [exact Hr16|]. split; [exact Hr0|]. split; [exact Hr1|]. split; [exact Hinr|].
  split; [exact HrF | exact Happr].
- split; [exact Hn0|]. split; [exact Hp0|]. split; [unfold lc_n in *; lia|]. split; [exact Hinp|].
  split; [exact HpF | exact Hpr].
Qed.

End a.
