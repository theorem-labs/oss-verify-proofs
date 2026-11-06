(* G4, IMAGE B: expected 0x81274 (fuzz_manifest.c:125-172) on fm.asan-ubsan, 453 instructions: the walk's shared base.
   The walk is cut at fixed pcs; every cut carries a semantic invariant (registers, frame slots, the journal from
   expected's entry, the strings), and every segment builds its own symbolic state from it (FMW_plain.v's entry-lemma
   pattern: L_entry, N_entry). The segments are stated here as Props; each segment file proves one of them from the
   Props of the segments it jumps to; FMW_ex_top.v composes them (the main loop by induction on |t| - i, as fm's plain
   proof does, lib/Prog/expected_ml.v:983).
   Frame (B, read from B's code, (internal path)): addi sp,sp,-240; ra@232, s0@224, s1@216,
   s2@208, s3@200, s4@192, s5@184, s6@176, s7@168, s8@160, s9@152, s10@144, s11@136 (offsets from F = entry sp - 240).
   Slots after the setup 0x81358..0x813bc: see ex_slots below (F+0x28 ~uri, F+0x30 declared, F+0x38 uri, F+0x48 n,
   F+0x58 text + 1, F+0x60 uri - 2, F+0x68 "prefix", F+0x70 the NUL/space mask, F+0x78 text, F+0x80 ~text); scratch
   F+0x20 local, F+0x40 close. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


(* IMAGE B (fm.asan-ubsan, pin ca61e5c9eabc0050): expected at 0x81274, 453 instructions. NOT a relocation of A's base:
   B's compiler strength-reduced the scan (it keeps BOTH s7 = i and the pointer s5 = text + i), keeps its loop constants
   in other registers (callee-saved s3 = 5, s11 = ' ', s0 = -1; caller-saved a7 = 6, t0 = ':', t1 = mask, a6 = text,
   re-made after every call), returns its answer through s7 (0x81904 `mv a0, s7`) and carries 19 UBSan guards to the trap
   0x8194c (a Theorem Labs lane's B5 table; refute them with FMTrapB.fm_kill_trap). Every fact below is read from B's code:
   (internal path), plan (internal path).
   ecx, ex_base, ex_post and ex_scan are spec-level and as in A; the frame, the slots, the registers and the cuts are B's. *)

(* ---- the code table of expected (0x81274, 453 words) ---- *)
Definition EX_tbl : ctable := Eval vm_compute in fmw_ranges [(A_expected, 453%nat)] TEmpty.
Lemma EX_tbl_ok : table_ok tfibsegs EX_tbl.
Proof.
  change EX_tbl with (fmw_ranges [(A_expected, 453%nat)] TEmpty).
  apply fmw_ranges_ok; [repeat constructor; cbn; unfold A_expected; lia | apply table_ok_empty].
Qed.
Definition EX_Bx : sv := SOff 32 0.
Definition EX_Bspan : Z * Z := (FW_SB, FW_SB + 2 ^ 44 - 1).

(* ---- the cut pcs (B) ---- *)
Definition EX_C1 : Z := 0x812c8.   (* after strlen (uri) *)
Definition EX_WL : Z := 0x812f8.   (* the whole-match loop head: s3 = a '<' in text *)
Definition EX_MS : Z := 0x81358.   (* the scan's setup *)
Definition EX_L : Z := 0x813c0.    (* the declaration scan's head: s7 = i, s5 = text + i *)
Definition EX_P : Z := 0x814cc.    (* after the prefix word: a0 = 7 ('@prefix') or 6 (ex_prefix_word) *)
Definition EX_T : Z := 0x816dc.    (* a matching declaration stored (d + 1 <= 16); s7 = 1; ex_token next *)
Definition EX_A0 : Z := 0x81900.   (* s7 = 0, answer 0 *)
Definition EX_A1 : Z := 0x81944.   (* s7 = 1, answer 1 *)
Definition EX_R : Z := 0x81908.    (* restore; return a0 (= s7, set at 0x81904) *)
Definition EX_NEXT : Z := 0x81694. (* s7 = s7 + 1; s5 = text + s7; guard; back to EX_L *)
Definition EX_JUMP : Z := 0x81690. (* s7 = a1 - a6 + 1 (a1 a pointer into text, a6 = text); then as EX_NEXT *)

(* the constants the scan keeps in its frame *)
Definition EX_MASK1 : Z := 0x100003e01.   (* bits 0, 9..13, 32: NUL and ex_space *)
Definition EX_PREFIX : Z := 0x20d00.      (* .str "prefix" *)
Definition EX_WORD : Z := 0x20d20.        (* ex_prefix_word.word "prefix" *)

(* the saved registers: (offset from F, register); B's frame is 240 bytes *)
Definition EX_SAVED : list (Z * Z) :=
  [(232, 1); (224, 8); (216, 9); (208, 18); (200, 19); (192, 20); (184, 21); (176, 22); (168, 23); (160, 24);
   (152, 25); (144, 26); (136, 27)].

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
Definition cx_F (cx : ecx) : Z := cx_sp cx - 240.
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

(* what every cut after the prologue carries (as in A): the journal from expected's entry, the blocks unchanged, the
   allocator statics, sp = F, gp/tp, s9 = the shadow base, the saved registers, the relro view, the two strings *)
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

(* B's scan frame slots (set at EX_MS 0x81358..0x813bc), d = declared *)
Definition ex_slots (cx : ecx) (W3 : world tfibsegs) (mem3 : word -> option byte) (d : nat) : Prop :=
  let F := cx_F cx in let t := cx_t cx in let u := cx_u cx in
  val_mem tfibsegs (rdW W3 mem3) (F + 0x30) 8 (Z.of_nat d) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x28) 8 (2 ^ 64 - 1 - u) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x38) 8 u /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x48) 8 (cx_n cx) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x58) 8 (t + 1) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x60) 8 (u - 2) /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x68) 8 EX_PREFIX /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x70) 8 EX_MASK1 /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x78) 8 t /\
  val_mem tfibsegs (rdW W3 mem3) (F + 0x80) 8 (2 ^ 64 - 1 - t).

(* the scan's callee-saved constants (live across every call): s3 = 5, s11 = ' ', s0 = -1 *)
Definition ex_sregs (cx : ecx) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 19 = w64 5 /\ getr regs3 27 = w64 32 /\ getr regs3 8 = w64 (2 ^ 64 - 1).

(* the caller-saved constants, re-made after every call: a6 = text, a7 = 6, t0 = ':', t1 = the mask *)
Definition ex_cregs (cx : ecx) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 16 = w64 (cx_t cx) /\ getr regs3 17 = w64 6 /\ getr regs3 5 = w64 58 /\ getr regs3 6 = w64 EX_MASK1.

(* the model state of the scan at a declaration index i (as in A) *)
Definition ex_scan (cx : ecx) (i d f : nat) : Prop :=
  (i <= length (cx_tb cx))%nat /\ (d <= 16)%nat /\ (length (cx_tb cx) - i < f)%nat /\
  (length (cx_ub cx) <> 0)%nat /\
  cx_res cx = ManifestModel.scan (cx_tb cx) (cx_ub cx) i d f.

(* ---- the segments ---- *)

(* the return at EX_R (0x81908): a0 = expected's answer (B sets it from s7 at 0x81904) *)
Definition ex_seg_R : Prop :=
  forall cx ly3 S3 W3 regs3 mem3 md3,
  ex_base cx -> ex_com cx ly3 S3 W3 regs3 mem3 md3 -> getr regs3 10 = w64 (cx_res cx) ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_R regs3 mem3 md3) (ex_post cx).

(* the scan's head EX_L at index i: s7 = i, s5 = text + i, the callee- and caller-saved constants *)
Definition ex_at_L (cx : ecx) (i d f : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base cx /\ ex_com cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_sregs cx regs3 /\
  ex_cregs cx regs3 /\ ex_scan cx i d f /\
  getr regs3 23 = w64 (Z.of_nat i) /\ getr regs3 21 = w64 (cx_t cx + Z.of_nat i).
Definition ex_seg_L_from (cx : ecx) (i0 : nat) : Prop :=
  forall i d f ly3 S3 W3 regs3 mem3 md3, (i0 < i)%nat ->
  ex_at_L cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post cx).
Definition ex_seg_L : Prop :=
  forall cx i d f ly3 S3 W3 regs3 mem3 md3,
  ex_at_L cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post cx).

(* entry to the end of the prologue's whole check: from expected's entry to EX_L (i = d = 0) or the return *)
Definition ex_seg_entry : Prop :=
  forall cx, ex_base cx ->
  (forall ly3 S3 W3 regs3 mem3 md3, ex_at_L cx 0 0 (S (length (cx_tb cx))) ly3 S3 W3 regs3 mem3 md3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post cx)) ->
  SRr tfibsegs (cx_W cx) (cfg_at tfibsegs A_expected (cx_regs cx) (cx_mem cx) (cx_md cx)) (ex_post cx).

(* EX_P (0x814cc): head (text, i) = Some (i + a1) with a1 in a0; s5 = text + i, s7 = i *)
Definition ex_at_P (cx : ecx) (i d f : nat) (a1 : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base cx /\ ex_com cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 d /\ ex_sregs cx regs3 /\
  ex_cregs cx regs3 /\ ex_scan cx i d f /\ (i < length (cx_tb cx))%nat /\
  ManifestModel.head (cx_tb cx) i = Some (i + a1)%nat /\ (a1 = 6 \/ a1 = 7)%nat /\
  getr regs3 23 = w64 (Z.of_nat i) /\ getr regs3 21 = w64 (cx_t cx + Z.of_nat i) /\
  getr regs3 10 = w64 (Z.of_nat a1).
Definition ex_seg_P : Prop :=
  forall cx i d f a1 ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from cx i -> ex_at_P cx i d f a1 ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_P regs3 mem3 md3) (ex_post cx).

(* the head's body: EX_L at i continues to EX_L at i + 1, to EX_P, or returns (text[i] = NUL) *)
Definition ex_seg_head : Prop :=
  forall cx i d f ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from cx i -> ex_seg_P -> ex_at_L cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_L regs3 mem3 md3) (ex_post cx).

(* EX_T (0x816dc): a declaration that matches, declared = d + 1 <= 16 stored, s7 = 1; ex_token next.
   s4 = text + name, s5 = name_len, s2 = 1 + name_len, s6 = s1 = text + 1 + name_len, s8 = nl2;
   F+0x20 = local = uri + nl2, F+0x40 = close = text + close. The caller-saved constants are NOT live here (plain was
   just called). *)
Definition ex_at_T (cx : ecx) (i d f : nat) (name nl ns nl2 close : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  ex_base cx /\ ex_com cx ly3 S3 W3 regs3 mem3 md3 /\ ex_slots cx W3 mem3 (S d) /\ ex_sregs cx regs3 /\
  ex_scan cx i d f /\ (i < length (cx_tb cx))%nat /\ (S d <= 16)%nat /\
  ManifestModel.decl (cx_tb cx) i = ManifestModel.DFound name nl ns nl2 close /\
  ManifestModel.matches (cx_tb cx) (cx_ub cx) ns nl2 = true /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x20) 8 (cx_u cx + Z.of_nat nl2) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_F cx + 0x40) 8 (cx_t cx + Z.of_nat close) /\
  getr regs3 23 = w64 1 /\
  getr regs3 20 = w64 (cx_t cx + Z.of_nat name) /\ getr regs3 21 = w64 (Z.of_nat nl) /\
  getr regs3 18 = w64 (1 + Z.of_nat nl) /\ getr regs3 22 = w64 (cx_t cx + 1 + Z.of_nat nl) /\
  getr regs3 9 = w64 (cx_t cx + 1 + Z.of_nat nl) /\ getr regs3 24 = w64 (Z.of_nat nl2).
Definition ex_seg_T : Prop :=
  forall cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3,
  ex_seg_L_from cx i -> ex_at_T cx i d f name nl ns nl2 close ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_T regs3 mem3 md3) (ex_post cx).
End c.
