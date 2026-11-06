(* The contract of syntax_reply_matches on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/syntax_reply_matches_c.v:12-31 (a0 = 1 when the reply has the shape, else 0; the 32-bit depth bound :22)
   and its model lib/Prog/CommandModel.v:80-132 (shape_items, item_scan, word_len, has_lt, reply_matches), used as
   they are.
   The function (syntax.h:156-176, with syntax_item and syntax_has inlined) walks the shape's items and the reply's
   words: the strcspn wrapper (`___interceptor_strcspn`, reached through the 4-byte jump
   `__interceptor_trampoline_strcspn`) gives the length of the next reply word, and the bcmp wrapper
   (`__interceptor_trampoline_bcmp`) compares an item that holds no '<' with that word. Its six 1-byte loads have
   inline checks: three on the shape, three on the reply. The shape and reply premises below make those bytes
   usable, so the error path (a call of `__asan_report_load1`) is not reached. The strcspn set " " is .str.4 at
   0x21120, among the image's read-only bytes (cmd_ro_ok, RO_lit_21120); what the strcspn wrapper asks of it comes
   from CmdRecFacts' cmd_aread_ok_chk and cmd_tail_vis, what the bcmp wrapper asks of a read-only shape from
   cmd_ro_rd, and the stack-protector GOT word and guard cell musl's strcspn reads (aguard_ok) from cmd_rec_cells.
   No CmdRecFacts fact is a premise here.

   The plain premises map as follows: the shape's cstr_at and outside_stack (:17) become astr_argA (a read-only
   literal of the image owned by no runtime entry, or a live block: check_reply passes the literal "resp 0" and
   rec_shape_of's read-only result); the reply's bytes_at, no-NUL and outside_stack (:18, :20) become a live block
   holding a NUL-terminated string; the slack premise (:19) becomes RtDefs.v's atail_vis on the reply; the canary
   premises (:21) are dropped (the ASan build has no stack protector).

   Addresses: entry BASE + AF_syntax_reply_matches = 0x8857c (M, the pinned image). 158 instructions, 6 inline
   checks, 4 loops (the item loop, with the space-skip, item-scan and '<' loops inside it), no side-stack frame. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the stack this call needs: its own 112-byte frame, and the window the strcspn and bcmp wrappers ask for
   (RtDefs.v's ecall_pre_stk segs B (2 * ESTACK); cgif's abcmp_realizes, lib/YG0d.v:355) *)
Definition SYNTAX_REPLY_MATCHES_STK : Z := 112 + 2 * ESTACK.
Definition EV_SYNTAX_REPLY_MATCHES : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with this tree's and cgif's names *)
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD.
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   tsyntax_reply_matches_spec B MT *)
#[using="MT"]
Definition tsyntax_reply_matches_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (ps rp : Z) (shape reply : list byte),
afn_pre_na SEGS B SYNTAX_REPLY_MATCHES_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 ps -> 0 <= ps < 2 ^ 64 -> getr regs 11 = w64 rp -> 0 <= rp < 2 ^ 64 ->
(* the shape (plain syntax_reply_matches_c.v:17, :22): a string argument (a read-only literal or a live block) *)
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] ps (Some shape) ->
Z.of_nat (length shape) < 2 ^ 31 ->
(* the reply (plain :18-20): a NUL-terminated string inside a live block, with the bytes after its terminator up to
   the end of that 8-byte word readable (the strcspn wrapper's musl loop reads them, RtDefs.v's atail_vis) *)
in_blockA (ablocks B ly S) rp (Z.of_nat (length reply) + 1) -> astr_atR (rdW W mem) rp reply ->
atail_vis SEGS W mem (rp + Z.of_nat (length reply)) ->
(* the strcspn set " ", among the image's read-only bytes, and the bridge from the listing's object atoms to its
   address (lib/A/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
st_nev S + EV_SYNTAX_REPLY_MATCHES <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_syntax_reply_matches) regs mem md)
(apost_base SEGS B SYNTAX_REPLY_MATCHES_STK [] regs ly S W mem md EV_SYNTAX_REPLY_MATCHES
(fun ly' S' W' regs' mem' md' =>
 (* plain :25 *)
 getr regs' 10 = w64 (if reply_matches shape reply then 1 else 0) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame: layout and allocator state unchanged (M6; mo_le_refl
    gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
