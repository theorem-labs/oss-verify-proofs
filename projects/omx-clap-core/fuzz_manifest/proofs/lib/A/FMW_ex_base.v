(* G4: expected 0x81130 (fuzz_manifest.c:125-172) on fm.asan, 402 instructions: the walk's shared base.
   The walk is cut at fixed pcs; every cut carries a semantic invariant (registers, frame slots, the journal from
   expected's entry, the strings), and every segment builds its own symbolic state from it (FMW_plain.v's entry-lemma
   pattern: L_entry, N_entry). The segments are stated here as Props; each segment file proves one of them from the
   Props of the segments it jumps to; FMW_ex_top.v composes them (the main loop by induction on |t| - i, as fm's plain
   proof does, lib/Prog/expected_ml.v:983).
   Frame (MEASURED, fm-fn-measure.md 5, expected): addi sp,sp,-208; ra@200, s0@192, s1@184, s2@176, s3@168, s4@160,
   s5@152, s6@144, s7@136, s8@128, s9@120, s10@112, s11@104 (offsets from F = entry sp - 208). Slots after the setup
   0x81200..0x8125c: F+0x18 declared, F+0x20 uri, F+0x30 n = strlen uri, F+0x38 uri - text - 2, F+0x40 text + 1,
   F+0x48 text + 2, F+0x50 "prefix" (.str 0x20d00), F+0x58 text, F+0x60 the NUL/space mask; scratch F+0 (ex_token
   e - j base), F+8 local, F+0x10 text + prefix_len, F+0x28 close. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the code table of expected (0x81130, 402 words) ---- *)
Definition EX_tbl : ctable := Eval vm_compute in fmw_ranges [(A_expected, 402%nat)] TEmpty.
Lemma EX_tbl_ok : table_ok tfibsegs EX_tbl.
Proof.
  change EX_tbl with (fmw_ranges [(A_expected, 402%nat)] TEmpty).
  apply fmw_ranges_ok; [repeat constructor; cbn; unfold A_expected; lia | apply table_ok_empty].
Qed.
Definition EX_Bx : sv := SOff 32 0.
Definition EX_Bspan : Z * Z := (FW_SB, FW_SB + 2 ^ 44 - 1).

(* ---- the cut pcs ---- *)
Definition EX_C1 : Z := 0x81184.   (* after strlen (uri), fuzz_manifest.c:127 *)
Definition EX_WL : Z := 0x811a4.   (* ex_whole's loop head (s4 = a '<' in text), :118-119 *)
Definition EX_MS : Z := 0x81200.   (* the scan's setup, :134 *)
Definition EX_L : Z := 0x81260.    (* the declaration scan's head, :134 *)
Definition EX_P : Z := 0x81344.    (* p = text + i + a1, a1 = 7 ('@prefix') or 6 (ex_prefix_word), :140, :142 *)
Definition EX_T : Z := 0x8152c.    (* declared stored; ex_token's strlen (local) next, :164-166 *)
Definition EX_R1 : Z := 0x81700.   (* a0 = 1; restore; return *)
Definition EX_R : Z := 0x81704.    (* restore; return a0 *)
Definition EX_CONT : Z := 0x814dc. (* s3 = s3 + 1; back to EX_L *)

(* the constants the scan keeps in its frame *)
Definition EX_MASK1 : Z := 0x100003e01.   (* bits 0, 9..13, 32: NUL and ex_space, fuzz_manifest.c:149 *)
Definition EX_PREFIX : Z := 0x20d00.      (* .str "prefix", :139 *)
Definition EX_WORD : Z := 0x20d20.        (* ex_prefix_word.word "prefix" (asan global, 7 bytes + redzone), :86 *)

(* the saved registers: (offset from F, register) *)
Definition EX_SAVED : list (Z * Z) :=
  [(200, 1); (192, 8); (184, 9); (176, 18); (168, 19); (160, 20); (152, 21); (144, 22); (136, 23); (128, 24);
   (120, 25); (112, 26); (104, 27)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* expected's entry: the values expected_spec quantifies *)
Record ecx := mkECX {
  cx_ly : alayout; cx_S : astate; cx_W : world tfibsegs; cx_regs : bvmap 5 word; cx_mem : word -> option byte;
  cx_md : Model; cx_ch : list (Z * Z * Z);
  cx_t : Z; cx_u : Z; cx_tb : list Z; cx_ub : list Z;
  cx_live : Z; cx_peak : Z; cx_cnt : Z; cx_fail : Z }.

Definition cx_sp (cx : ecx) : Z := spZ (cx_regs cx).
Definition cx_F (cx : ecx) : Z := cx_sp cx - 208.
Definition cx_n (cx : ecx) : Z := Z.of_nat (length (cx_ub cx)).
Definition cx_res (cx : ecx) : Z := ManifestModel.names (cx_tb cx) (cx_ub cx).

(* expected_spec's premises *)
Definition ex_base (cx : ecx) : Prop :=
  let ly := cx_ly cx in let S := cx_S cx in let W := cx_W cx in let regs := cx_regs cx in let mem := cx_mem cx in
  fpre tfibsegs B STK_expected ly S W regs mem (cx_md cx) (cx_ch cx) /\
  fm_glob tfibsegs W mem (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx) /\
  getr regs 10 = w64 (cx_t cx) /\ getr regs 11 = w64 (cx_u cx) /\
  cstr_ok tfibsegs W mem (cx_t cx) (cx_tb cx) /\ cstr_ok tfibsegs W mem (cx_u cx) (cx_ub cx) /\
  cstr_kept B ly S (cx_t cx) (cx_tb cx) /\ cstr_kept B ly S (cx_u cx) (cx_ub cx) /\
  (length (cx_ub cx) <= 255)%nat /\ Z.of_nat (length (cx_tb cx)) <= MANIFEST_MAX.

(* expected_spec's post *)
Definition ex_post (cx : ecx) : world tfibsegs -> config -> Prop :=
  fpost tfibsegs B STK_expected [] (cx_regs cx) (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) 0
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (cx_res cx) /\ ablocks B ly' S' = ablocks B (cx_ly cx) (cx_S cx) /\
       fm_glob tfibsegs W' mem' (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx)).

(* the saved registers in the frame *)
Definition ex_saved_ok (cx : ecx) (W3 : world tfibsegs) (mem3 : word -> option byte) : Prop :=
  Forall (fun s => val_mem tfibsegs (rdW W3 mem3) (cx_F cx + fst s) 8
    (bv_unsigned (getr (cx_regs cx) (Z_to_bv 5 (snd s))))) EX_SAVED.

(* what every cut after the prologue carries: the journal from expected's entry (no events: expected allocates
   nothing, plain neither), the blocks unchanged, the allocator statics, sp = F, gp/tp, s9 = the shadow base, the saved
   registers, the relro view, the two strings with their homes *)
Definition ex_com (cx : ecx) ly3 S3 (W3 : world tfibsegs) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  ajournal tfibsegs B STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 mem3 md3 0 /\
  ablocks B ly3 S3 = ablocks B (cx_ly cx) (cx_S cx) /\
  fm_glob tfibsegs W3 mem3 (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx) /\
  getr regs3 2 = w64 (cx_F cx) /\ getr regs3 3 = getr (cx_regs cx) 3 /\ getr regs3 4 = getr (cx_regs cx) 4 /\
  getr regs3 25 = w64 SHADOW_OFF /\
  ex_saved_ok cx W3 mem3 /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W3) mem3) /\
  cstr_ok tfibsegs W3 mem3 (cx_t cx) (cx_tb cx) /\ cstr_ok tfibsegs W3 mem3 (cx_u cx) (cx_ub cx) /\
  cstr_kept B ly3 S3 (cx_t cx) (cx_tb cx) /\ cstr_kept B ly3 S3 (cx_u cx) (cx_ub cx).

(* the scan's frame slots (set at 0x81200..0x8125c), d = declared *)
Definition ex_slots (cx : ecx) (W3 : world tfibsegs) (mem3 : word -> option byte) (d : nat) : Prop :=
  let F := cx_F cx in let t := cx_t cx in let u := cx_u cx in
  val_mem tfibsegs (rdW W3 mem3) (F + 0x18) 8 (Z.of_nat d) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x20) 8 u /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x30) 8 (cx_n cx) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x38) 8 ((u - t - 2) mod 2 ^ 64) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x40) 8 (t + 1) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x48) 8 (t + 2) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x50) 8 EX_PREFIX /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x58) 8 t /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x60) 8 EX_MASK1.

(* the scan's constant registers: s7 = text, s6 = 6, s2 = 5, s0 = ' ' (callee-saved, live across every call) *)
Definition ex_sregs (cx : ecx) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 23 = w64 (cx_t cx) /\ getr regs3 22 = w64 6 /\ getr regs3 18 = w64 5 /\ getr regs3 8 = w64 32.

(* the model state of the scan at a declaration index i (fm plain expected_ml.v:985-986) *)
Definition ex_scan (cx : ecx) (i d f : nat) : Prop :=
  (i <= length (cx_tb cx))%nat /\ (d <= 16)%nat /\ (length (cx_tb cx) - i < f)%nat /\
  (length (cx_ub cx) <> 0)%nat /\
  cx_res cx = ManifestModel.scan (cx_tb cx) (cx_ub cx) i d f.

(* ---- the segments ---- *)

(* the return at EX_R (0x81704): a0 = expected's answer *)
Definition ex_seg_R : Prop :=
  forall cx ly3 S3 W3 regs3 mem3 md3,
  ex_base cx -> ex_com cx ly3 S3 W3 regs3 mem3 md3 -> getr regs3 10 = w64 (cx_res cx) ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_R regs3 mem3 md3) (ex_post cx).

(* the scan's head EX_L at index i (s3 = i, s1 = '@', a5 = ':', a6 = the mask) *)
Definition ex_at_L (cx : ecx) (i d f : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base cx /\ ex_com cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_sregs cx regs3 /\
  ex_scan cx i d f /\
  getr regs3 19 = w64 (Z.of_nat i) /\ getr regs3 9 = w64 64 /\ getr regs3 15 = w64 58 /\
  getr regs3 16 = w64 EX_MASK1.
Definition ex_seg_L_from (cx : ecx) (i0 : nat) : Prop :=
  forall i d f ly3 S3 W3 regs3 mem3 md3, (i0 < i)%nat ->
  ex_at_L cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post cx).
Definition ex_seg_L : Prop :=
  forall cx i d f ly3 S3 W3 regs3 mem3 md3,
  ex_at_L cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post cx).

(* entry to the end of the prologue's whole check: from expected's entry to EX_L (i = d = 0) or EX_R *)
Definition ex_seg_entry : Prop :=
  forall cx, ex_base cx ->
  (forall ly3 S3 W3 regs3 mem3 md3, ex_at_L cx 0 0 (S (length (cx_tb cx))) ly3 S3 W3 regs3 mem3 md3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post cx)) ->
  SRr tfibsegs (cx_W cx) (cfg_at tfibsegs A_expected (cx_regs cx) (cx_mem cx) (cx_md cx)) (ex_post cx).

(* EX_P (0x81344): head (text, i) = Some (i + a1); s4 = text + i *)
Definition ex_at_P (cx : ecx) (i d f : nat) (a1 : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base cx /\ ex_com cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_sregs cx regs3 /\
  ex_scan cx i d f /\ (i < length (cx_tb cx))%nat /\
  ManifestModel.head (cx_tb cx) i = Some (i + a1)%nat /\ (a1 = 6 \/ a1 = 7)%nat /\
  getr regs3 19 = w64 (Z.of_nat i) /\ getr regs3 20 = w64 (cx_t cx + Z.of_nat i) /\
  getr regs3 11 = w64 (Z.of_nat a1) /\ getr regs3 9 = w64 64 /\ getr regs3 15 = w64 58 /\
  getr regs3 16 = w64 EX_MASK1.
Definition ex_seg_P : Prop :=
  forall cx i d f a1 ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from cx i -> ex_at_P cx i d f a1 ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_P regs3 mem3 md3) (ex_post cx).

(* the head's body: EX_L at i continues to EX_L at i + 1, to EX_P, or returns (text[i] = NUL) *)
Definition ex_seg_head : Prop :=
  forall cx i d f ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from cx i -> ex_seg_P -> ex_at_L cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post cx).

(* EX_T (0x8152c): a declaration that matches, declared = d + 1 <= 16 stored; ex_token next.
   s4 = text + name, s5 = name_len, s8 = 1 + name_len, s3 = s1 = text + 1 + name_len; F+8 = local = uri + nl2,
   F+0x28 = close = text + close *)
Definition ex_at_T (cx : ecx) (i d f : nat) (name nl ns nl2 close : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base cx /\ ex_com cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 (S d) /\ ex_sregs cx regs3 /\
  ex_scan cx i d f /\ (i < length (cx_tb cx))%nat /\ (S d <= 16)%nat /\
  ManifestModel.decl (cx_tb cx) i = ManifestModel.DFound name nl ns nl2 close /\
  ManifestModel.matches (cx_tb cx) (cx_ub cx) ns nl2 = true /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 8) 8 (cx_u cx + Z.of_nat nl2) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x28) 8 (cx_t cx + Z.of_nat close) /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat name) /\ getr regs3 21 = w64 (Z.of_nat nl) /\
  getr regs3 24 = w64 (1 + Z.of_nat nl) /\ getr regs3 19 = w64 (cx_t cx + 1 + Z.of_nat nl) /\
  getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat nl).
Definition ex_seg_T : Prop :=
  forall cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from cx i -> ex_at_T cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_T regs3 mem3 md3) (ex_post cx).
End c.
