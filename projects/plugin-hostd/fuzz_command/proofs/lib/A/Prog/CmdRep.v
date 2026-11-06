(* The recorder's state in the ASan build's memory, and the byte vocabulary the program contracts use.

   This is lib/Prog/RecInv.v (fuzz_command's own released plain proof: rep_at, g1_*, call_at, answer_at, reply_at)
   over the ASan side's reader: `bytes_at segs mem` becomes RtDefs' `abytes_atR` / `astr_atR` and `aval_mem` over `aview segs (w_H W) mem`,
   the block list is `ablocks B ly S` of the ASan allocator state, and the plain `wr_at` writability conjuncts are
   dropped (the ASan side gets them from AR and from the shadow facts of each contract). The model itself —
   `rstate`, `rec_record`, `rec_stub`, the 20 `sup_*_m` — is lib/Prog/RecModel.v, used as it is.

   Addresses are fuzz_command.asan's: g_rec 0x5e3740, record.spill 0x5e3be0 (the pinned image's symbols). The field
   offsets are RecInv.v:9-24, unchanged: ASan moves the object, not the layout inside it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04 YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdChk CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* Bytes and strings through a reader are the runtime's: `abytes_atR` and `astr_atR` of lib/A/Rt/RtDefs.v, with the
   bridges abytes_atR_view / astr_atR_view to the forms its runtime contracts take, so a walk that calls a wrapper
   needs no rewriting between two shapes. Only the n-wide little-endian field read, which the recorder's layout
   needs and no runtime contract has, is defined here; where a width is 4 or 8, a contract says rd32 / rd64. *)
Definition aval_mem (rd : reader) (a : Z) (n : nat) (v : Z) : Prop :=
forall k, (k < n)%nat -> rd (a + Z.of_nat k) = Some (YG0f.le_byte v n k).

(* a range inside a live block (the plain proof's in_block, lib/Prog/joined_c.v:30-31). The harness's words are
   pointers into one `copy` block, not block starts, so a contract says this, not In (p, n) (ablocks B ly S). *)
Definition in_blockA (bl : list (Z * Z)) (a n : Z) : Prop :=
exists p k, In (p, k) bl /\ p <= a /\ a + n <= p + k.

(* The word array verbs_receive's tok[64] holds after strtok_r (the plain proof's toks_at, lib/Prog/VerbsB.v:54-60):
   one 8-byte pointer per word, each word NUL-terminated and inside the one block strdup made for `copy`
   (src/verbs.c:225). *)
Definition atoks_atA (rd : reader) (tok : Z) (ptrs : list Z) (tks : list (list byte)) (cb ncb : Z) : Prop :=
tok mod 8 = 0 /\ length ptrs = length tks /\
(forall i p, nth_error ptrs i = Some p -> aval_mem rd (tok + 8 * Z.of_nat i) 8 p) /\
(forall i p w, nth_error ptrs i = Some p -> nth_error tks i = Some w ->
 astr_atR rd p w /\ Z.of_nat (length w) <= 8192 /\ cb <= p /\ p + Z.of_nat (length w) + 1 <= cb + ncb).

(* RecInv.v:42-50 call_at, over the reader *)
Definition acall_at (bl : list (Z * Z)) (rd : reader) (a : Z) (c : rcall) (P : list (Z * Z)) : Prop :=
0 <= fst c < REC_FN_COUNT /\ (length (snd c) <= 6)%nat /\ length P = length (snd c) /\
aval_mem rd (a + CALL_OFF_FN) 4 (fst c) /\
aval_mem rd (a + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd c))) /\
NoDup (map fst P) /\
(forall k s pn, nth_error (snd c) k = Some s -> nth_error P k = Some pn ->
 aval_mem rd (a + CALL_OFF_ARGS + 8 * Z.of_nat k) 8 (fst pn) /\
 fst pn <> 0 /\ In pn bl /\ Z.of_nat (length s) + 1 <= snd pn <= LMAX + 2 /\
 astr_atR rd (fst pn) s).

(* RecInv.v:55-78 answer_at / reply_at *)
Definition aanswer_at (bl : list (Z * Z)) (rd : reader) (gr : Z) (t : option (list byte)) (q : option (Z * Z)) : Prop :=
match t, q with
| None, None => aval_mem rd (gr + OFF_ANSWER) 8 0
| Some x, Some pn =>
    aval_mem rd (gr + OFF_ANSWER) 8 (fst pn) /\
    fst pn <> 0 /\ In pn bl /\ Z.of_nat (length x) + 1 <= snd pn <= LMAX + 2 /\
    astr_atR rd (fst pn) x /\ Z.of_nat (length x) <= LMAX
| _, _ => False
end.
Definition areply_at (bl : list (Z * Z)) (rd : reader) (gr : Z) (y : option (list byte)) (q : option (Z * Z)) : Prop :=
match y, q with
| None, None => aval_mem rd (gr + OFF_REPLY) 8 0 /\ aval_mem rd (gr + OFF_REPLY_SIZE) 8 0
| Some x, Some pn =>
    aval_mem rd (gr + OFF_REPLY) 8 (fst pn) /\
    aval_mem rd (gr + OFF_REPLY_SIZE) 8 (Z.of_nat (length x)) /\
    fst pn <> 0 /\ x <> [] /\ In pn bl /\ Z.of_nat (length x) <= snd pn <= LMAX + 2 /\
    abytes_atR rd (fst pn) x /\ Z.of_nat (length x) <= LMAX + 2
| _, _ => False
end.

(* RecInv.v:84-112 g1_calls / g1_scalars / g1_own / rep_at, without the writability conjuncts *)
Definition ag1_calls (bl : list (Z * Z)) (rd : reader) (gr sc : Z) (R : rstate) (Q : rlay) : Prop :=
(length (r_calls R) <= 16)%nat /\ length (l_calls Q) = length (r_calls R) /\
aval_mem rd (gr + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))) /\
(forall i c P, nth_error (r_calls R) i = Some c -> nth_error (l_calls Q) i = Some P ->
 acall_at bl rd (gr + OFF_CALLS + CALL_SIZE * Z.of_nat i) c P /\
 Forall (fun s => Z.of_nat (length s) <= LMAX) (snd c)) /\
acall_at bl rd sc (r_spill R) (l_spill Q) /\
Forall (fun s => Z.of_nat (length s) <= LMAX) (snd (r_spill R)).
Definition ag1_scalars (rd : reader) (gr : Z) (R : rstate) : Prop :=
aval_mem rd (gr + OFF_REFUSE) 4 (r_refuse R) /\
aval_mem rd (gr + OFF_CODE) 4 (r_code R) /\
aval_mem rd (gr + OFF_NREPLIES) 4 (r_nreplies R) /\
aval_mem rd (gr + OFF_STATE) 8 (r_state R) /\
aval_mem rd (gr + OFF_HOST) 8 (r_host R) /\
-2^31 <= r_refuse R < 2^31 /\ -2^31 <= r_code R < 2^31 /\ 0 <= r_nreplies R < 2^31 /\
0 <= r_state R < 2^64 /\ 0 <= r_host R < 2^64.
Definition ag1_own (gr sc : Z) (Q : rlay) : Prop :=
NoDup (map fst (lay_blocks Q)) /\
forall pn, In pn (lay_blocks Q) -> iv_apart (fst pn) (snd pn) gr REC_SIZE /\ iv_apart (fst pn) (snd pn) sc SC_SIZE.
Definition arep_at (bl : list (Z * Z)) (rd : reader) (gr sc : Z) (R : rstate) (Q : rlay) : Prop :=
gr mod 8 = 0 /\ sc mod 8 = 0 /\ iv_apart gr REC_SIZE sc SC_SIZE /\
ag1_calls bl rd gr sc R Q /\
aanswer_at bl rd gr (r_answer R) (l_answer Q) /\
areply_at bl rd gr (r_reply R) (l_reply Q) /\
ag1_scalars rd gr R /\
ag1_own gr sc Q.

(* The read-only words of the image that the program loads as constants. With an abstract PAImg the walk cannot
   evaluate `seg_rom SEGS`, so a contract names the words it needs and the instance discharges them by vm_compute
   against the image (cgif does the same with the .rodata byte lists of lib/YI0x.v:21-27, discharged in A/ACke.v).
   These four GOT words are the ones every recorder function loads: g_rec, rec_ncodes, rec_codes, g_quitting. *)
Definition cmd_got_ok (rd : reader) : Prop :=
aval_mem rd 0xa7068 8 A_G_REC /\ aval_mem rd 0xa7070 8 0x21cc0 /\
aval_mem rd 0xa7078 8 0x21ba0 /\ aval_mem rd 0xa7080 8 A_G_QUITTING.

(* The allocator events a recorder state's own blocks cost to free: one per recorded call's argument, plus the
   call's own two (the canonical line and the answer text). The five contracts whose counts can multiply —
   rec_clear, rec_calls_copy, rec_calls_free, send_message, check_round_trip — state their EV as a function of the
   recorder state through this, not as a type-cap constant: with `length (r_calls R) <= 2` (the plain proof's
   step_frame, lib/Prog/HarnessPropsProof.v:1363-1364) it is at most 16, against 96 from the type caps. *)
Definition ev_args (R : rstate) : Z :=
fold_right (fun c acc => Z.of_nat (length (snd c)) + acc) 0 (r_calls R).
Definition ev_calls (R : rstate) : Z := 2 * Z.of_nat (length (r_calls R)) + ev_args R.

(* The frees the recorder's record() arm spends: when the table already holds 16 calls the new call goes to the
   spill slot and the arguments the spill held are freed (recorder.c:210-215, RecModel.v:38-39 `rec_record`).
   A caller that knows the table holds at most 2 calls (the plain proof's step_frame,
   lib/Prog/HarnessPropsProof.v:1363-1364) gets 0. *)
Definition rec_spill_frees (R : rstate) : Z :=
if Nat.ltb (length (r_calls R)) 16 then 0 else Z.of_nat (length (snd (r_spill R))).

Section d.
Variable B : asyms.
(* A string argument the recorder was handed (the plain proof's str_arg, lib/Prog/RecKindB.v:164-175): either it
   lies in a live block that is none of the recorder's own blocks O (which record()/answer() may free during the
   call), or it is a read-only byte range of the image that no runtime entry owns and that is not the errno cell,
   so every journal of a later call keeps it (the journal's image clause) and a caller passing an image literal
   discharges it by cmd_img_facts' cif_ro_unowned, while the record's shadow checks (cmd_addr_b, cmd_hull_b, and the
   string's end among CmdRo's literal ends) hold at EVERY later state, which is what a string handed to a runtime
   entry after an allocation or a free needs: cmd_aread_ok_chk and cmd_tail_vis_at turn them into aread_ok and
   atail_vis. `ro` is `in_roP SEGS RLO RHI`. *)
Definition astr_argA (ly : alayout) (S : astate) (rd : reader) (ro : Z -> Prop) (O : list (Z * Z))
(p : Z) (v : option (list byte)) : Prop :=
match v with
| None => p = 0
| Some x =>
  let n := Z.of_nat (length x) + 1 in
  p <> 0 /\ astr_atR rd p x /\ n <= LMAX + 1 /\
  ((in_blockA (ablocks B ly S) p n /\ Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O) \/
   ((forall i, 0 <= i < n -> ro (p + i) /\ ~ Exists (in_zr (p + i)) (as_owned_static B) /\
       ~ (as_errno B <= p + i < as_errno B + 4)) /\
    cmd_addr_b p n = true /\ cmd_hull_b p n = true /\ In (p + Z.of_nat (length x)) cmd_ro_ends))
end.

(* the recorder's state of fuzz_command.asan: g_rec and record.spill at the image's addresses, over the ASan
   allocator's live blocks; O is the list of blocks the recorder owns *)
Definition rec_repA (ly : alayout) (S : astate) (rd : reader) (R : rstate) (O : list (Z * Z)) : Prop :=
exists Q, arep_at (ablocks B ly S) rd A_G_REC A_REC_SPILL R Q /\ (forall pn, In pn O <-> In pn (lay_blocks Q)).
End d.
