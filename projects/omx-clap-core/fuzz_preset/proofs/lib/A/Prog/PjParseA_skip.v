(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: THE INLINED skip_ws LOOP of pj_parse's image-A' walk (fuzz_preset asan, #102 pin
   1be0f53d96cb, unstripped twin bff8519bbe3e; A' 0x85e20; preset_file.c :36-40 inlined into :296-309), over
   lib/A/Prog/PjParseA_defs.v's names. proves no function (kind: segment lemma): pjs_loop is the loop's step from
   its head to its one exit, for any continuation at the exit; lib/A/Prog/PjParseA_seg_c2ok.v composes it.
   THE CODE (whole-program listing lib/A/Listing_prog.v, PA := PI_prog_A; pc offsets from pj_parse's entry):
     LOOP  +0x74 srli a6, a0, 3      +0x78 add a6, a6, s1        +0x7c lb a6, 0(a6)   (the shadow byte of p)
           +0x80 bnez a6 -> +0xac    +0x84 lbu a6, 0(a3)         (the text byte c at p)
           +0x88 bltu a4, a6 -> +0xbc (c > 32)                   +0x8c srl a6, a5, a6  +0x90 andi a6, a6, 1
           +0x94 beqz a6 -> +0xbc    (c not white space)         +0x98 addi a2, a3, 1  +0x9c addi a0, a0, 1
           +0xa0 mv a3, a2           +0xa4 bne a2, a1 -> +0x74   +0xa8 j +0xb8
     SLOW  +0xac andi a7, a0, 7      +0xb0 blt a7, a6 -> +0x84   +0xb4 jal __asan_report_load1
     EXIT  +0xb8 mv a2, a1           +0xbc (the exit: `sd a2, 0(sp)`, PjParseA_seg_c2ok.v)
   At the loop head a0 = a2 = a3 = p, a1 = end = t0 + len, a4 = 32, a5 = the white-space mask PJS_WS_MASK (bits 9, 10,
   13 and 32: '\t', '\n', '\r', ' '), s1 = SHADOW_OFF (pjp_inv's s1 conjunct).
   THE SHADOW CHECK (+0x74 .. +0x80 and the slow block +0xac .. +0xb0): the token engine (lib/Reusable/YCbn.v
   tok_load / tok_branch, sound by sym_run_pi_tok_sound) reads `lb` at s1 + (a0 >> 3) as the shadow byte of p and
   takes `bnez` with the slow block `andi a7, a0, 7; blt a7, a6` as one step to +0x84, a7 havocked, under the
   obligation range_addressable SHADOW_OFF p 1. The loop discharges it from the text's range_addressable over
   [t0, t0 + len) (src_rd's), by range_addressable_sub: the shadow s of p is 0 or p mod 8 < s < 8, so `bnez` falls
   through or `blt` returns to +0x84. So +0xb4 (`jal __asan_report_load1`) is never reached.
   THE MODEL (lib/A/PRH_FnReader.v tskip_ws_specX, its model: PjGrammar.skip): the loop's invariant is
   PjGrammar.skip rest = PjGrammar.skip (skipn (p - t0) tl); it exits with a2 = t0 + len - |PjGrammar.skip rest|:
   at a byte above 32 or not white space a2 = p and skip rest = skipn (p - t0) tl; at p + 1 = end a2 = end and
   skip rest = []. The loop reads the text byte at p and its shadow byte only, and writes no memory.
   HOW: induction on the bytes left, t0 + len - p; each turn is engine stretches over YCbqG's ajournal_xR R at a world
   relation R with its two laws (YC1fPx.v paj_run_x_invR / paj_run_to_x_invR at P := YAkMemnorm.memnorm,
   YSRrMemnorm.srr_inv_laws_memnorm_k; YSRrG.v paj_branchR), seated fresh at the loop head with the byte c as atom 32
   (Caw102A_WA3.v caw_loop's form, the same loop shape). The loop calls nothing; it runs after parse_value's call,
   where the journal is at wle' segs RZ_cf, so its statement is over R and concludes SRrG R (seg_c2ok instantiates
   R := wle' SEGS RZ_cf).
   NEW CODE on A' (the B' walk at preset-tree-at-2026-10-30T09-35-36Z.tsv (sha256 60ab58a4fb09; internal record)
   called the out-of-line skip_ws, lib/B/Prog/skip_ws_x.v): nothing here is PORTED from the B' pj_parse files; the
   loop invariant and the shadow-check arms follow lib/B/Prog/skip_ws_x.v skw_loop and lib/A/Prog/Caw102A_WA3.v caw_loop.
   Numerals: 32 (WORD: the space byte, the loop's bound), PJS_WS_MASK = 2 ^ 9 + 2 ^ 10 + 2 ^ 13 + 2 ^ 32 (WORD: the
   mask the code builds with `lui 0x800; addiw 0x13; slli 9`), 255 / 256 (the byte range), 4096 (the page floor),
   2 ^ 44 / 2 ^ 47 / 2 ^ 64 (shadow span, address bounds); atom numbers 9 .. 32 and 512 DERIVED (the engine's
   numbering); pc offsets DERIVED from PjParseA_defs.v's PJP_C2OK (+ 36 = +0x74, + 108 = +0xbc). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjParseA_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the loop's pc offsets from pj_parse's entry (DERIVED from the cut PJP_C2OK = +0x50) ---- *)
Definition PJS_LOOP : Z := PJP_C2OK + 36.   (* +0x74, the loop head `srli a6, a0, 3` *)
Definition PJS_EXIT : Z := PJP_C2OK + 108.  (* +0xbc, `sd a2, 0(sp)`, the loop's one exit *)

(* the white-space mask a5: bit c set for c = 9, 10, 13, 32 (the value the engine computes from `lui a0, 0x800;
   addiw a0, a0, 0x13; slli a5, a0, 9`) *)
Definition PJS_WS_MASK : Z := 4294977024.
Lemma pjs_mask_bits : PJS_WS_MASK = 2 ^ 9 + 2 ^ 10 + 2 ^ 13 + 2 ^ 32.
Proof. reflexivity. Qed.

(* ---- the model: one step of PjGrammar.skip over skipn i tl, its end (Caw102A_WA3.v cawp_skipn_nth / caw_skip_cons /
   caw_skip_end, image-free) ---- *)
Lemma pjs_skipn_nth : forall i (x : list Z), (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
induction i as [|i IH]; intros [|b x] H; cbn [length] in H; try lia.
- reflexivity.
- exact (IH x ltac:(lia)).
Qed.

Lemma pjs_skip_cons : forall i x, (i < length x)%nat ->
  PjGrammar.skip (skipn i x) =
  if PjGrammar.ws (nth i x 0) then PjGrammar.skip (skipn (S i) x) else skipn i x.
Proof. intros i x H. rewrite (pjs_skipn_nth i x H). reflexivity. Qed.

Lemma pjs_skip_end : forall x, PjGrammar.skip (skipn (length x) x) = [].
Proof. induction x as [|b x IH]; [reflexivity|exact IH]. Qed.

(* the machine's white-space test: the mask shifted right by c, low bit, for c <= 32; no byte above 32 is white space *)
Lemma pjs_ws_mask : forall c, 0 <= c <= 32 ->
  Z.land (Z.shiftr PJS_WS_MASK c) 1 = if PjGrammar.ws c then 1 else 0.
Proof.
intros c Hc. unfold PJS_WS_MASK.
replace c with (Z.of_nat (Z.to_nat c)) by lia.
assert (Hn : (Z.to_nat c <= 32)%nat) by lia.
revert Hn. generalize (Z.to_nat c) as n. intros n Hn. clear Hc.
do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma pjs_ws_big : forall c, 32 < c -> PjGrammar.ws c = false.
Proof.
intros c Hc. unfold PjGrammar.ws.
rewrite (proj2 (Z.eqb_neq c 32)), (proj2 (Z.eqb_neq c 9)), (proj2 (Z.eqb_neq c 10)),
  (proj2 (Z.eqb_neq c 13)) by lia.
reflexivity.
Qed.

(* the turn's white-space test as the engine states it: (a5 >> c) & 1 *)
Lemma pjs_U_bit : forall E c, ew E 15 = Z_to_bv 64 PJS_WS_MASK -> ew E 32 = Z_to_bv 64 c -> 0 <= c <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SOff 15 0) (SOff 32 0)) (SLit 1)) = if PjGrammar.ws c then 1 else 0.
Proof.
intros E c H15 H32 Hc.
assert (Hl : Z.land c 63 = c).
{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
assert (Hb : 0 <= Z.shiftr PJS_WS_MASK c <= PJS_WS_MASK).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)) as Hp.
  split; [apply Z.div_pos; unfold PJS_WS_MASK; lia|]. apply Z.div_le_upper_bound; [lia|]. unfold PJS_WS_MASK. nia. }
assert (Ui : U E (SAlu ALU_SRL (SOff 15 0) (SOff 32 0)) = Z.shiftr PJS_WS_MASK c).
{ rewrite U_SAlu, (U_atom E 15 PJS_WS_MASK H15 ltac:(unfold PJS_WS_MASK; lia)), (U_atom E 32 c H32 ltac:(lia)).
  cbn [zalu_raw]. rewrite Hl. apply zcanon_id. unfold M64, PJS_WS_MASK in *. lia. }
rewrite U_SAlu, Ui, U_SLit. rewrite (zcanon_id 1) by (unfold M64; lia). cbn [zalu_raw].
rewrite pjs_ws_mask by lia. destruct (PjGrammar.ws c); apply zcanon_id; unfold M64; lia.
Qed.

(* ---- the engine's seat at the loop head: every register its own atom, the byte c at a3 = p the extra atom 32; the
   shadow base is s1 (atom 9, the engine's Bx), the cursor of the shadow test a0 (atom 10) ---- *)
Definition pjs_ssL : sstate :=
  mkSS PJS_LOOP sr_atoms [YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
    (mkFacts [(9%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF 0 255 0)]
      [] []).
(* the engine's shadow span (cgif's convention) *)
Definition PJS_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the registers no turn writes (a0, a2, a3, a6 and a7 are the turn's) *)
Definition PJS_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 11; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Ltac pjs_in := cbn [In PJS_KEPT]; repeat (first [left; reflexivity | right]).
(* the write premise of a run whose regions are read-only *)
Ltac pjs_nowr := let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn in Hin; repeat (destruct Hin as [<- | Hin]; [cbn in Hr; lia|]); destruct Hin.
(* after a read-only run: EM : the new machine memory = the old one *)
Ltac pjs_ro0 HF HFr HG EM :=
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as EM end;
  clear HF HFr HG.
Ltac pjs_ro HF HFr HG EM :=
  let Em := fresh "Em" in
  lazymatch type of HF with frame_of _ ?rs _ _ =>
    pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Em end;
  clear HF HFr HG; rewrite EM in Em; clear EM; rename Em into EM.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
#[local] Notation AJR R := (ajournal_xR (SK := SK) SEGS B PST ARx R).

(* a register the run's end state holds as atom n plus z *)
Lemma pjs_reg_off : forall (fz : YK11.FPState) (H : word -> bool) E ss ms (r : bv 5) n z v,
  st_ok_pi (fx := fz) SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n z ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 -> getr (ms_regs ms) r = Z_to_bv 64 (v + z).
Proof.
intros fz H E ss ms r n z v HS Hsr Hv Hv0 Hvz.
rewrite (st_ok_pi_restrict_reg (fx := fz) (L := A_prog_listing) (PI := PA) H E ss ms r HS), Hsr, denot_lit_U.
rewrite (U_atom_off E n v z Hv Hv0 Hvz). reflexivity.
Qed.

(* the registers a run leaves as their own atoms keep their values (YC1fP.v regs_kept_of_st_ok_pi, at the machine
   state itself) *)
Lemma pjs_kept : forall (fz : YK11.FPState) (H : word -> bool) E ss ms regs extra (l : list (bv 5)),
  st_ok_pi (fx := fz) SEGS VAL E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) l = true ->
  forall r, In r l -> getr (ms_regs ms) r = getr regs r.
Proof.
intros fz H E ss ms regs extra l HS HA Hl r Hr.
pose proof (regs_kept_of_st_ok_pi (fx := fz) (L := A_prog_listing) (PI := PA) E ss (restrict H ms) regs extra l
  HS HA Hl r Hr) as X.
cbn [restrict ms_regs] in X. exact X.
Qed.

(* the loop: induction on the bytes left (t0 + len - p); each turn reads the byte c at p (its shadow test folded by
   the engine into the obligation range_addressable SHADOW_OFF p 1, discharged from the text's: the report site +0xb4
   is never reached), then exits to +0xbc (c above 32, or not white space, or p + 1 = end) or goes round at p + 1; at
   any world relation R with its two laws, the journal at R *)
Lemma pjs_loop : forall (R : world SEGS -> world SEGS -> Prop) (Rr : forall W, R W W)
    (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3)
    (n : nat) (Q : world SEGS -> config -> Prop) (fy : YK11.FPState) (W : world SEGS)
    (regs : bvmap 5 word) mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k (t0 : Z) (tl rest : list Z) (P : Z),
  (Z.to_nat (t0 + Z.of_nat (length tl) - P) <= n)%nat ->
  AJR R STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md k ->
  YAkMemnorm.memnorm SEGS mem ->
  getr regs 9 = w64 SHADOW_OFF -> getr regs 10 = w64 P -> getr regs 11 = w64 (t0 + Z.of_nat (length tl)) ->
  getr regs 12 = w64 P -> getr regs 13 = w64 P -> getr regs 14 = w64 32 -> getr regs 15 = w64 PJS_WS_MASK ->
  4096 <= t0 -> t0 + Z.of_nat (length tl) < 2 ^ 47 ->
  garr8 SEGS (rdW W mem) t0 tl ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t0 (Z.of_nat (length tl)) ->
  t0 <= P < t0 + Z.of_nat (length tl) ->
  PjGrammar.skip rest = PjGrammar.skip (skipn (Z.to_nat (P - t0)) tl) ->
  (forall regs' md',
     AJR R STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md' k ->
     (forall r, In r PJS_KEPT -> getr regs' r = getr regs r) ->
     getr regs' 12 = w64 (t0 + Z.of_nat (length tl) - Z.of_nat (length (PjGrammar.skip rest))) ->
     SRrG SEGS R W (pjp_cfg fy PJS_EXIT regs' mem md') Q) ->
  SRrG SEGS R W (pjp_cfg fy PJS_LOOP regs mem md) Q.
Proof.
intros R Rr Rt n. induction n as [|n IH]; intros Q fy W regs mem md STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k
  t0 tl rest P Hn HJ HPM R9 R10 R11 R12 R13 R14 R15 Ht4 Htend HGT HRA HP Hskip KX.
{ exfalso. lia. }
assert (Hjn : (Z.to_nat (P - t0) < length tl)%nat) by lia.
set (c := nth (Z.to_nat (P - t0)) tl 0).
destruct (HGT (Z.to_nat (P - t0)) Hjn) as [HVc HRc]. fold c in HVc, HRc.
replace (t0 + Z.of_nat (Z.to_nat (P - t0))) with P in HVc by lia.
set (E := Eimg (Ereg regs [Z_to_bv 64 c])).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew E n = getr regs r).
{ intros n0 r Hn0 H32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hn0). }
assert (E32 : ew E 32 = Z_to_bv 64 c).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). replace 32%nat with (32 + 0)%nat by lia.
  rewrite ew_Ereg_extra. reflexivity. }
assert (AGE : forall E', (forall n, (n < 512)%nat -> ew E' n = ew E n) -> ed E' = ed E ->
  env_agree 32 (Ereg regs [Z_to_bv 64 c]) E').
{ intros E' HE' Hd. split.
  - intros i Hi. rewrite HE' by lia. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
  - rewrite Hd. subst E. reflexivity. }
assert (U9 : U E (SOff 9 0) = SHADOW_OFF)
  by (apply U_atom; [rewrite (ER 9%nat 9%bv eq_refl ltac:(lia)); exact R9 | unfold SHADOW_OFF; lia]).
assert (U10 : U E (SOff 10 0) = P) by (apply U_atom; [rewrite (ER 10%nat 10%bv eq_refl ltac:(lia)); exact R10 | lia]).
assert (U32 : U E (SOff 32 0) = c) by (apply U_atom; [exact E32 | lia]).
assert (HS : st_ok_pi (fx := fy) SEGS VAL E pjs_ssL
  (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + PJS_LOOP)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pjs_ssL. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (ER 13%nat 13%bv eq_refl ltac:(lia)), R13. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ P 0 1 (SOff 32 0) c).
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact HVc.
  - exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok].
    split; [|split; [|split; [|exact I]]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite (ER 9%nat 9%bv eq_refl ltac:(lia)), R9. unfold w64.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold SHADOW_OFF; lia.
    + rewrite (ER 10%nat 10%bv eq_refl ltac:(lia)), R10. unfold w64.
      rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    + rewrite E32, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
pose (RUN := paj_run_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)
  B PST ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) R Rr Rt).
pose (RUNTO := paj_run_to_x_invR (fx := fy) (SK := SK) (L := A_prog_listing) (PL := PL_prog_A) (PI := PA)
  B PST ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) R Rr Rt).
pose (BR := paj_branchR (fx := fy) (L := A_prog_listing) (PI := PA) R).
(* the exits to +0xbc: the memory is the loop head's, a2 = p2 *)
assert (EXIT : forall regs' md' p2, AJR R STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp W mem md' k ->
  (forall r, In r PJS_KEPT -> getr regs' r = getr regs r) -> getr regs' 12 = w64 p2 ->
  p2 = t0 + Z.of_nat (length tl) - Z.of_nat (length (PjGrammar.skip rest)) ->
  SRrG SEGS R W (pjp_cfg fy PJS_EXIT regs' mem md') Q).
{ intros regs' md' p2 HJ' KP R12' ->. exact (KX regs' md' HJ' KP R12'). }
unfold pjp_cfg.
paj_run_tok_x_invR RUN HS HJ SHOK HPM PJS_Bspan.
- (* THE REPORT SITE +0xb4 REFUTED: the turn's one obligation, the shadow of its byte p, from the text's *)
  cbn [ms_mem mkst]. rewrite U9, U10. eapply range_addressable_sub; [exact HRA | lia | lia].
- pjs_nowr.
- pjs_ro0 HF HFr HG EM.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E' := Ex) in * end.
  assert (EE : forall n, (n < 512)%nat -> ew E' n = ew E n)
    by (intros n0 Hn0; subst E'; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (ED : ed E' = ed E) by (subst E'; reflexivity).
  pose proof (AGE E' EE ED) as AG.
  assert (U14' : U E' (SOff 14 0) = 32) by (apply U_atom; [rewrite EE, (ER 14%nat 14%bv eq_refl) by lia; exact R14 | lia]).
  assert (U32' : U E' (SOff 32 0) = c) by (apply U_atom; [rewrite EE by lia; exact E32 | lia]).
  (* +0x88 `bltu a4, a6`: 32 < c, not white space *)
  psrr_branch_tok RUN BR HS SHOK PJS_Bspan.
  + rewrite branch_ltu_U, U14', U32' in Hc. apply Z.ltb_lt in Hc.
    pose proof (pjs_ws_big c Hc) as Hws.
    paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJS_Bspan PJS_EXIT.
    { pjs_nowr. }
    pjs_ro HF HFr HG EM.
    lazymatch goal with |- SRrG _ _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
      pmkst HS;
      lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
        replace n with PJS_EXIT by (vm_compute; reflexivity) end;
      rewrite EM in HJ, HPM |- *;
      apply (EXIT (ms_regs m) d P HJ);
      [ exact (pjs_kept fy (w_H W) E' _ _ regs _ PJS_KEPT HS AG ltac:(vm_compute; reflexivity))
      | rewrite (pjs_kept fy (w_H W) E' _ _ regs _ [12%bv] HS AG ltac:(vm_compute; reflexivity) 12%bv
          (or_introl eq_refl)); exact R12
      | rewrite Hskip, (pjs_skip_cons _ _ Hjn); fold c; rewrite Hws; cbv iota; rewrite length_skipn; lia ]
    end.
  + rewrite branch_ltu_U, U14', U32' in Hc. apply Z.ltb_ge in Hc.
    assert (Hc32 : 0 <= c <= 32) by lia. clear Hc.
    paj_run_tok_x_invR RUN HS HJ SHOK HPM PJS_Bspan.
    { pjs_nowr. }
    pjs_ro HF HFr HG EM.
    assert (Ubit : U E' (SAlu ALU_AND (SAlu ALU_SRL (SOff 15 0) (SOff 32 0)) (SLit 1)) =
      if PjGrammar.ws c then 1 else 0).
    { apply pjs_U_bit; [rewrite EE, (ER 15%nat 15%bv eq_refl) by lia; exact R15 | rewrite EE by lia; exact E32
        | exact Hc32]. }
    (* +0x94 `beqz a6`: c is not white space *)
    psrr_branch_tok RUN BR HS SHOK PJS_Bspan.
    * rewrite branch_eq_U, Ubit, U_SLit in Hc. apply Z.eqb_eq in Hc.
      assert (Hws : PjGrammar.ws c = false)
        by (destruct (PjGrammar.ws c); [vm_compute in Hc; discriminate | reflexivity]).
      paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJS_Bspan PJS_EXIT.
      { pjs_nowr. }
      pjs_ro HF HFr HG EM.
      lazymatch goal with |- SRrG _ _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
        pmkst HS;
        lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
          replace n with PJS_EXIT by (vm_compute; reflexivity) end;
        rewrite EM in HJ, HPM |- *;
        apply (EXIT (ms_regs m) d P HJ);
        [ exact (pjs_kept fy (w_H W) E' _ _ regs _ PJS_KEPT HS AG ltac:(vm_compute; reflexivity))
        | rewrite (pjs_kept fy (w_H W) E' _ _ regs _ [12%bv] HS AG ltac:(vm_compute; reflexivity) 12%bv
            (or_introl eq_refl)); exact R12
        | rewrite Hskip, (pjs_skip_cons _ _ Hjn); fold c; rewrite Hws; cbv iota; rewrite length_skipn; lia ]
      end.
    * rewrite branch_eq_U, Ubit, U_SLit in Hc. apply Z.eqb_neq in Hc.
      assert (Hws : PjGrammar.ws c = true)
        by (destruct (PjGrammar.ws c); [reflexivity | exfalso; apply Hc; reflexivity]).
      clear Hc.
      assert (Hskip' : PjGrammar.skip rest = PjGrammar.skip (skipn (Datatypes.S (Z.to_nat (P - t0))) tl))
        by (rewrite Hskip, (pjs_skip_cons _ _ Hjn); fold c; rewrite Hws; reflexivity).
      paj_run_tok_x_invR RUN HS HJ SHOK HPM PJS_Bspan.
      { pjs_nowr. }
      pjs_ro HF HFr HG EM.
      assert (U13p : U E' (SOff 13 1) = P + 1)
        by (apply U_atom_off; [rewrite EE, (ER 13%nat 13%bv eq_refl) by lia; exact R13 | lia | lia]).
      assert (U11' : U E' (SOff 11 0) = t0 + Z.of_nat (length tl))
        by (apply U_atom; [rewrite EE, (ER 11%nat 11%bv eq_refl) by lia; exact R11 | lia]).
      (* +0xa4 `bne a2, a1`: p + 1 <> end, round again *)
      psrr_branch_tok RUN BR HS SHOK PJS_Bspan.
      -- rewrite branch_ne_U, U13p, U11' in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
         paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJS_Bspan PJS_LOOP.
         { pjs_nowr. }
         pjs_ro HF HFr HG EM.
         lazymatch goal with |- SRrG _ _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
           pmkst HS;
           lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (_ + ?nn)) _ _; cfg_model := _ |} _ =>
             replace nn with PJS_LOOP by (vm_compute; reflexivity) end;
           rewrite EM in HJ, HPM |- *;
           pose proof (pjs_kept fy (w_H W) E' _ _ regs _ PJS_KEPT HS AG ltac:(vm_compute; reflexivity)) as KP;
           assert (R10n : getr (ms_regs m) 10 = w64 (P + 1))
             by (exact (pjs_reg_off fy (w_H W) E' _ _ 10%bv 10 1 P HS eq_refl
                   ltac:(rewrite EE, (ER 10%nat 10%bv eq_refl) by lia; exact R10) ltac:(lia) ltac:(lia)));
           assert (R12n : getr (ms_regs m) 12 = w64 (P + 1))
             by (exact (pjs_reg_off fy (w_H W) E' _ _ 12%bv 13 1 P HS eq_refl
                   ltac:(rewrite EE, (ER 13%nat 13%bv eq_refl) by lia; exact R13) ltac:(lia) ltac:(lia)));
           assert (R13n : getr (ms_regs m) 13 = w64 (P + 1))
             by (exact (pjs_reg_off fy (w_H W) E' _ _ 13%bv 13 1 P HS eq_refl
                   ltac:(rewrite EE, (ER 13%nat 13%bv eq_refl) by lia; exact R13) ltac:(lia) ltac:(lia)));
           refine (IH Q fy W (ms_regs m) mem d STK sp0 FP ly0 S0 Hp0 W0 mem0 md0 own ly S Hp k t0 tl rest (P + 1)
             _ HJ HPM _ R10n _ R12n R13n _ _ Ht4 Htend HGT HRA _ _ _)
         end.
         ++ lia.
         ++ rewrite (KP 9%bv ltac:(pjs_in)). exact R9.
         ++ rewrite (KP 11%bv ltac:(pjs_in)). exact R11.
         ++ rewrite (KP 14%bv ltac:(pjs_in)). exact R14.
         ++ rewrite (KP 15%bv ltac:(pjs_in)). exact R15.
         ++ lia.
         ++ rewrite Hskip'. f_equal. f_equal. lia.
         ++ intros regs' md' HJ' KP' R12'. apply (KX regs' md' HJ'); [|exact R12'].
            intros r Hr. rewrite (KP' r Hr). exact (KP r Hr).
      -- (* p + 1 = end: `j +0xb8`, `mv a2, a1`: p2 = end *)
         rewrite branch_ne_U, U13p, U11' in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
         paj_run_to_tok_x_invR RUNTO HS HJ SHOK HPM PJS_Bspan PJS_EXIT.
         { pjs_nowr. }
         pjs_ro HF HFr HG EM.
         lazymatch goal with |- SRrG _ _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ =>
           pmkst HS;
           lazymatch goal with |- SRrG _ _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (_ + ?nn)) _ _; cfg_model := _ |} _ =>
             replace nn with PJS_EXIT by (vm_compute; reflexivity) end;
           rewrite EM in HJ, HPM |- *;
           apply (EXIT (ms_regs m) d (t0 + Z.of_nat (length tl)) HJ);
           [ exact (pjs_kept fy (w_H W) E' _ _ regs _ PJS_KEPT HS AG ltac:(vm_compute; reflexivity))
           | rewrite (pjs_reg_off fy (w_H W) E' _ _ 12%bv 11 0 (t0 + Z.of_nat (length tl)) HS eq_refl
               ltac:(rewrite EE, (ER 11%nat 11%bv eq_refl) by lia; exact R11) ltac:(lia) ltac:(lia)), Z.add_0_r;
             reflexivity
           | rewrite Hskip';
             replace (Datatypes.S (Z.to_nat (P - t0))) with (length tl) by lia;
             rewrite pjs_skip_end; cbn [length Z.of_nat]; lia ]
         end.
Qed.
End l.

Check @pjs_loop.
Print Assumptions pjs_loop.
