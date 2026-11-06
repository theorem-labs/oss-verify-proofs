(* The contract of rec_shape_of on the ASan build of plugin-hostd/fuzz_command.

   Shape: cgif_file_fuzzer's per-function contracts (lib/YC7x.v:72-167, lib/YC21.v:33-88): afn_pre at the entry,
   SRr of apost_base at the return. Functional content: fuzz_command's own released plain contract
   lib/Prog/rec_shape_of_c.v:58-80 (a0 = shape_find shape_rows v: the reply shape of the row whose name is the verb,
   else mod-host's "resp 0"; the `a1 <= 16 ->` premise on the verb's bytes, :66-69), stated with the address-free
   form of the same table, lib/Prog/RecFacts.v:280-319 (shape_table, shape_lookup, shape_of), used as it is.
   The function (recorder.c:77-85) scans the 28 rows of the read-only table g_shapes (0xa5ec0, 16 bytes a row:
   name pointer, reply pointer): for each row it asks the strlen wrapper (`___interceptor_strlen`, reached through
   the 4-byte jump `__interceptor_trampoline_strlen`) for the name's length and, when it equals len, compares the
   name with the verb through the bcmp wrapper (`__interceptor_trampoline_bcmp`); at the first match it returns the
   row's reply pointer, else the literal "resp 0" (.str 0x21ce0). The two 8-byte loads from g_shapes have inline
   checks; g_shapes is a registered global of 448 bytes (M: asan_globals descriptor, size_with_redzone 544), so its
   shadow bytes say usable (CmdRecFacts' cmd_addressable_chk) and the error path (a call of `__asan_report_load8`)
   is not reached. The table and the 56 strings it points to, and .str 0x21ce0, are among the image's read-only
   bytes (cmd_ro_ok, lib/A/Prog/CmdRo.v: RO_g_shapes and the RO_lit_* lists); what the strlen and bcmp wrappers ask
   of a name (aread_ok, the bytes after its terminator) comes from cmd_aread_ok_chk and cmd_tail_vis, and what the
   bcmp wrapper asks of a read-only verb (in the image, shadow words visible, off the scratch window) from cmd_ro_rd.
   No CmdRecFacts fact is a premise here.

   The post names the returned address by what it holds: a read-only string equal to shape_of v, which no runtime
   entry owns and which is not the errno cell (the read-only branch of astr_argA, lib/A/Prog/CmdRep.v). The walk
   proves which literal it is from RO_g_shapes and the unowned part from cmd_img_facts' cif_ro_unowned; no caller
   needs the address itself (check_reply passes it to syntax_reply_matches, the recorder's verbs to answer, both of
   which take the string as astr_argA).

   Addresses: entry BASE + AF_rec_shape_of = 0x891ec (M, the pinned image). 69 instructions, 2 inline checks,
   1 loop (28 iterations, s5 steps by -2 from 0 to -56, back edge 0x89290 -> 0x89254), no side-stack frame. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
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
(* the stack this call needs: its own 96-byte frame, and below it the bcmp wrapper's window (2 * ESTACK, cgif's
   abcmp_realizes, lib/YG0d.v:355), which covers the strlen wrapper's (ESTACK, the runtime contracts' final windows) *)
Definition REC_SHAPE_OF_STK : Z := 96 + 2 * ESTACK.
Definition EV_REC_SHAPE_OF : Z := 0.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches, with this tree's and cgif's names *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
(* `using MT`: the post has no meter conjunct (frame form), so MT is named here to keep the uniform signature
   trec_shape_of_spec B MT *)
#[using="MT"]
Definition trec_shape_of_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md (p : Z) (v : list byte),
afn_pre_na SEGS B REC_SHAPE_OF_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(* the verb and its length (plain rec_shape_of_c.v:66) *)
getr regs 10 = w64 p -> 0 <= p < 2 ^ 64 ->
getr regs 11 = w64 (Z.of_nat (length v)) -> Z.of_nat (length v) < 2 ^ 64 ->
(* the table and the strings it points to (plain :64), each byte of them read-only (what astr_argA's read-only
   case of the post asks), and the bridge from the listing's object atoms to the table's address
   (lib/A/Prog/CmdObj.v) *)
cmd_ro_ok (rdW W mem) -> cmd_val_objs ->
(* the verb's bytes, which the bcmp wrapper reads only when len equals a name's length, so len <= 16
   (plain :67-69). Two kinds of caller: a byte range inside a live block that need not end in a NUL
   (sup_instance_verb passes line + strspn with the strcspn length, 0x8b48c-0x8b4a0), or a whole string, the
   read-only literals (sup_worker_list's "worker_list" 0x21d80 with 11, descriptors_get's 0x21f60 with 14,
   sup_chain's 0x21f20 with 5, ...) and check_reply's word w0 (strlen, 0x86f64-0x86f74), stated through
   astr_argA itself so its read-only arm is the one every other statement uses *)
(Z.of_nat (length v) <= 16 ->
 abytes_atR (rdW W mem) p v /\
 (in_blockA (ablocks B ly S) p (Z.of_nat (length v)) \/
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] p (Some v))) ->
st_nev S + EV_REC_SHAPE_OF <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_rec_shape_of) regs mem md)
(apost_base SEGS B REC_SHAPE_OF_STK [] regs ly S W mem md EV_REC_SHAPE_OF
(fun ly' S' W' regs' mem' md' =>
 (* a0: the reply shape's literal in the table's read-only strings (the plain post names shape_find of the
    shape rows, plain rec_shape_of_c.v:72), stated as astr_argA (lib/A/Prog/CmdRep.v) for ANY owned-block list:
    the pre form its users ask (answer's premise answer_c.v:95, syntax_reply_matches' shape premise; check_reply
    passes it on at 0x86fdc). It holds through the read-only arm: every byte read-only, owned by no runtime entry
    and not the errno cell (cmd_img_facts' cif_ro_unowned), its shadow usable; a heap result would have to be
    apart from every list O, and this one never is a block. *)
 (exists q, getr regs' 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
  forall O, astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) O q (Some (shape_of v))) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* it allocates nothing and takes no side-stack frame: layout and allocator state unchanged (M6; mo_le_refl
    gives the meter) *)
 ly' = ly /\ S' = S)).
End e.
End f.
End d.
