(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the interface of sup_chain's image-B walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry 0x8c1c4, a Theorem Labs lane's lib/B/Prog/sup_chain_c.v `tsup_chain_spec`): the walk is cut at the
   loop head 0x8c3d0 (BASE + SCB_LOOP) and at the loop exit 0x8c444 (BASE + SCB_LEXIT), as the ASan walk
   lib/A/Prog/sup_chain_s8.v cuts it (sc_segA / sc_segB, sc_loop, sc_segC). Definitions only:
   - scb_lctx: what the walk from the entry to the loop's first arrival leaves (the journal from the entry, the
     blocks the callees made and freed, the recorder's state, the memory facts the loop and the tail read);
   - scb_inv: the loop's invariant after k passes, at the loop head (k < n) and at the exit (k = n), relative to
     the memory memL of the first arrival (lib/A/Prog/sup_chain_s5.v scl_inv's form).
   Registers (B code, capstone over the pin's .symtab): s0 = x8 = entry sp, s1 = x9 = sp1 = (entry sp - 192) & -32 (also
   sp), s2 = x18 = ~list, s3 = x19 = s8 = x24 = ids + 4k, s4 = x20 = (ids <> 0) = 1, s5 = x21 = o (the text printed so
   far), s6 = x22 = list, s7 = x23 = "%d" 0x21f40, s9 = x25 = 1 (ids 4-aligned and non-null), s10 = x26 = k,
   s11 = x27 = n. Stack words (sp1-relative): +8 the slot, +16 the frame F, +24 F's shadow SB + F / 8, +32 F (the
   stack-malloc result), +40 " %d" 0x21f20, +48 ids, +56 SB, +80 F. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c xmalloc_c arg_s_c rec_shape_of_c answer_c sup_chain_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_chain_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the statement's footprint (sup_chain_c.v:156): g_rec, record.spill and the recorder's own blocks *)
Definition SCB_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the saved registers at entry sp - 8 - 8j (ra, s0 .. s11), as the A walk's sc_saved *)
Definition scb_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
(* the realigned sp (0x8c204) *)
Definition scb_sp1 (sp0 : Z) : Z := 32 * ((sp0 - 192) / 32).
(* the 16 shadow bytes of the class-1 frame from its set-up on (outside the inlined arg_i's windows) *)
Definition scb_shadow0 : list Z := [0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf8; 0xf2; 0xf2; 0xf8; 0xf8; 0xf3; 0xf3; 0; 0; 0; 0].
(* the size of arg_s's copy of a printed number *)
Definition scb_m (v : Z) : Z := Z.of_nat (length (dec v)) + 1.
(* the journal count at the loop: record()'s frees, xmalloc's malloc, the two arg_s mallocs *)
Definition scb_kL (R : rstate) : Z := EV_RECORD R + EV_XMALLOC + EV_ARG_S + EV_ARG_S.

(* the FP state (a Theorem Labs lane pass 4b, f490061c104): the printf wrappers return at SOME fx' whose rounding mode is 0 and whose
   f registers equal the caller's except f10 (lib/B/Rt/RtPFCmd.v:187-190); the statement's post apost_baseF asks the
   same of the return against the entry's f registers fr0 and fcsr csr0 (lib/B/Prog/CmdBase.v apost_baseF). A
   segment of the walk starts at any FP state with rounding mode 0 that is `scb_fxok fr0 csr0` and hands the next
   segment the FP state it returns at. *)
Definition scb_frm0 (fx : YK11.FPState) : Prop := Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Definition scb_fxok (fr0 : bvmap 5 word) (csr0 : bv 32) (fx : YK11.FPState) : Prop :=
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx) k = Sem.reg_get fr0 k) /\
(@fp_csr fx = csr0 \/ scb_frm0 fx).
Lemma scb_fxok_entry : forall fx : YK11.FPState, scb_fxok (@fp_regs fx) (@fp_csr fx) fx.
Proof. intros fx. split; [intros k _; reflexivity | left; reflexivity]. Qed.
(* a printf wrapper's return keeps scb_fxok *)
Lemma scb_fxok_step : forall fr0 csr0 (fx fx' : YK11.FPState), scb_fxok fr0 csr0 fx ->
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) ->
scb_frm0 fx' -> scb_fxok fr0 csr0 fx'.
Proof. intros fr0 csr0 fx fx' [H1 _] H2 H3. split; [intros k Hk; rewrite (H2 k Hk); exact (H1 k Hk) | right; exact H3]. Qed.
(* an apost_baseF callee's return (fcsr kept, or rounding mode 0) keeps scb_fxok *)
Lemma scb_fxok_stepF : forall fr0 csr0 (fx fx' : YK11.FPState), scb_fxok fr0 csr0 fx ->
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) ->
(@fp_csr fx' = @fp_csr fx \/ scb_frm0 fx') -> scb_fxok fr0 csr0 fx'.
Proof.
intros fr0 csr0 fx fx' [H1 H1c] H2 H3. split; [intros k Hk; rewrite (H2 k Hk); exact (H1 k Hk)|].
destruct H3 as [E|E]; [rewrite E; destruct H1c as [E1|E1]; [left; exact E1 | right; unfold scb_frm0 in *; rewrite E; exact E1] | right; exact E].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* apost_baseF with the entry's f registers fr0 and fcsr csr0 named (lib/B/Prog/CmdBase.v:77-85): a segment that
   starts at an FP state other than the entry's states the post this way; scb_postF_baseF gives apost_baseF at the
   entry's FP state *)
Definition scb_postF (fr0 : bvmap 5 word) (csr0 : bv 32) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word)
  ly S W mem md (k : Z)
  (Q : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world SEGS -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
scb_fxok fr0 csr0 fx' /\
ajournal SEGS B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
Lemma scb_postF_baseF : forall STK FP regs ly S W mem md k Q W' c',
scb_postF (@fp_regs fx) (@fp_csr fx) STK FP regs ly S W mem md k Q W' c' ->
apost_baseF SEGS B STK FP regs ly S W mem md k Q W' c'.
Proof.
intros STK FP regs ly S W mem md k Q W' c' (fx' & ly' & S' & regs' & mem' & md' & Ec & [Hf Hc] & HJ & HP & HQ).
exists fx', ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact Hf|]. split; [exact Hc|].
split; [exact HJ|]. split; [exact HP | exact HQ].
Qed.

Definition scb_frame_at (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error scb_saved j = Some r ->
val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* the own stack words the walk stores below the saved registers and reads later *)
Definition scb_words (W : world SEGS) (mem : word -> option byte) (sp1 c F pids : Z) : Prop :=
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 8) 8 c /\
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 16) 8 F /\
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 24) 8 (SB + F / 8) /\
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 32) 8 F /\
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 40) 8 0x21f20 /\
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 48) 8 pids /\
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 56) 8 SB /\
val_mem SEGS (mrestrict (w_H W) mem) (sp1 + 80) 8 F.

(* the frame's 16 shadow bytes *)
Definition scb_fshadow (W : world SEGS) (mem : word -> option byte) (F : Z) : Prop :=
forall i, 0 <= i < 16 -> rdW W mem (SB + F / 8 + i) = Some (nth (Z.to_nat i) scb_shadow0 0).

(* the loop context. Entry: ly S W regs mem md (the statement's), id pids ids R O. First arrival at the loop head:
   lyL SL WL memL mdL; the class-1 frame (1, fpos); the text block lst (xmalloc's, 12n + 1 bytes); bl1 the blocks
   after record(), Frec the blocks record()'s spill arm freed, O1 the recorder's blocks then; p1, p2 the copies the
   two arg_s calls made (of dec id and dec n) *)
Definition scb_lctx (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z))
  (lyL : alayout) (SL : astate) (WL : world SEGS) (memL : word -> option byte) (mdL : Model)
  (fpos lst : Z) (bl1 Frec O1 : list (Z * Z)) (p1 p2 : Z) : Prop :=
let n := Z.of_nat (length ids) in
let sp0 := spZ regs in
let F := frame_addr lyL 1 fpos in
(* the journal from the entry, with the class-1 frame as this call's own *)
ajournal SEGS B SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md [(1, fpos)] lyL SL WL memL mdL (scb_kL R) /\
(* record(): it freed Frec (the recorder's) and nothing else *)
Permutation (ablocks B ly S) (bl1 ++ Frec) /\ (forall pn, In pn Frec -> In pn O) /\
Z.of_nat (length Frec) = rec_spill_frees R /\ (forall pn, In pn O1 <-> In pn O /\ ~ In pn Frec) /\
(* xmalloc and the two arg_s: three fresh blocks *)
Permutation (ablocks B lyL SL) ((p2, scb_m n) :: (p1, scb_m id) :: (lst, 12 * n + 1) :: bl1) /\
Forall (fun qk => iv_apart lst (12 * n + 1) (fst qk) (snd qk)) bl1 /\
Forall (fun qk => iv_apart p1 (scb_m id) (fst qk) (snd qk)) ((lst, 12 * n + 1) :: bl1) /\
Forall (fun qk => iv_apart p2 (scb_m n) (fst qk) (snd qk)) ((p1, scb_m id) :: (lst, 12 * n + 1) :: bl1) /\
4096 <= p1 < 2 ^ 64 /\ 4096 <= p2 < 2 ^ 64 /\ 4096 <= lst < 2 ^ 64 /\
(* the recorder holds the call (17, [dec id; dec n]) in the slot rec_slot R *)
rec_repA B lyL SL (rdW WL memL) (rec_record R REC_CHAIN [dec id; dec n]) ((p2, scb_m n) :: (p1, scb_m id) :: O1) /\
blocks_bytes SL <= blocks_bytes S + LIVE_XMALLOC (12 * n + 1) + LIVE_ARG_S (Some (dec id)) +
  LIVE_ARG_S (Some (dec n)) /\
mo_le MT S SL (XM_RECORD MT R + XM_XMALLOC MT (12 * n + 1) + XM_ARG_S MT (Some (dec id)) +
  XM_ARG_S MT (Some (dec n))) /\
(* the memory the loop and the tail read *)
scb_frame_at (mrestrict (w_H WL) memL) sp0 regs /\
scb_words WL memL (scb_sp1 sp0) (rec_slot R) F pids /\
scb_fshadow WL memL F /\
rdword (rdW WL memL) (F + 120) = Some (flag_addr lyL 1 fpos) /\
rdW WL memL lst = Some 0 /\
abytes_atR (rdW WL memL) pids (concat (map le32 ids)) /\
range_addressable (rdW WL memL) SHADOW_OFF pids (4 * n) /\
iv_apart pids (4 * n) lst (12 * n + 1) /\ pids + 4 * n <= alloc_ceiling /\
arodata_okP SEGS CMD_RLO CMD_RHI B (rdW WL memL).

(* the loop's invariant after k passes: the journal (the loop allocates nothing), the registers, the text written so
   far and its terminator, and everything outside the text block and the runtime entries' scratch window below sp1
   as at the first arrival *)
Definition scb_inv (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z))
  (lyL : alayout) (SL : astate) (WL : world SEGS) (memL : word -> option byte)
  (fpos lst : Z) (k : nat) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
let n := Z.of_nat (length ids) in
let sp0 := spZ regs in
let sp1 := scb_sp1 sp0 in
(k <= length ids)%nat /\
ajournal SEGS B SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md [(1, fpos)] lyL SL WL mem' md' (scb_kL R) /\
spZ regs' = sp1 /\ getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
getr regs' 8 = w64 sp0 /\ getr regs' 9 = w64 sp1 /\
getr regs' 18 = w64 (2 ^ 64 - 1 - lst) /\ getr regs' 19 = w64 (pids + 4 * Z.of_nat k) /\ getr regs' 20 = w64 1 /\
getr regs' 21 = w64 (Z.of_nat (length (dec_list (firstn k ids)))) /\ getr regs' 22 = w64 lst /\
getr regs' 23 = w64 0x21f40 /\ getr regs' 24 = w64 (pids + 4 * Z.of_nat k) /\ getr regs' 25 = w64 1 /\
getr regs' 26 = w64 (Z.of_nat k) /\ getr regs' 27 = w64 n /\
abytes_atR (rdW WL mem') lst (dec_list (firstn k ids) ++ [Z_to_bv 8 0]) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (lst <= a < lst + 12 * n + 1) -> ~ (sp1 - 3 * ESTACK <= a < sp1) ->
   rdW WL mem' a = rdW WL memL a).
End e.
End f.
End d.
