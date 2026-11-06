(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared definitions of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0, 198 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_cx, cl_post, cl_mid and the segment statements CL_*_stmt): the entry context, the post, the invariant of the body between the frame's allocation and its release, and the three cut points the segment walks meet at (BODY after the shadow fills, HEAD of syntax_instantiate's loop, JOIN before hand_back); the walk tactics of cgif's lib/A/ACkc.v over fuzz_command's listing; and the facts every segment carries over a journal of the walk (read-only bytes, the shape string, arodata_okP). *)
(* Modified by Theorem Labs, 2026-10: statement passes 4 and 5 (lib/A/Prog/answer_c.v): an_pre without the stack's presence (astack_pres), BODY with the rounding-mode premise and the FP-existential post an_postF; HEAD and JOIN keep apost_base, at whatever FP state they are used. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import mix_call_c hand_back_c answer_c.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
(* lia without the Euclidean-division equations: the flag value these proofs were checked with, which PaDenot.v
   gave them until an earlier commit made its redefinition Local *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the points of answer the walk names, as listing offsets from BASE (M, the pinned image, the disassembler:
   0x8a4c0 = BASE + AF_answer = BASE + 0x3fdc) ---- *)
Definition AN_MALLOC : Z := 0x4054.     (* 0x8a538 jal __asan_stack_malloc_7 (a0 = 4256) *)
Definition AN_F8A : Z := 0x40e4.        (* 0x8a5c8 jal __asan_set_shadow_f8 (s6, 512) *)
Definition AN_SH00 : Z := 0x4134.       (* 0x8a618 jal __asan_set_shadow_00 (s6, 512) *)
Definition AN_BODY : Z := 0x4138.       (* 0x8a61c the return of __asan_set_shadow_00 *)
Definition AN_SNP : Z := 0x415c.        (* 0x8a640 jal snprintf (buf, 4096, "resp %d", g_rec.code) *)
Definition AN_MIX : Z := 0x4170.        (* 0x8a654 jal mix_call (g_rec.state, c) *)
Definition AN_HEAD : Z := 0x418c.       (* 0x8a670 the head of syntax_instantiate's loop *)
Definition AN_EXIT : Z := 0x4230.       (* 0x8a714 the loop's exit: buf's terminator *)
Definition AN_JOIN : Z := 0x4250.       (* 0x8a734 mv a0,s5; the two arms meet *)
Definition AN_HB : Z := 0x4254.         (* 0x8a738 jal hand_back (buf) *)
Definition AN_F8B : Z := 0x4264.        (* 0x8a748 jal __asan_set_shadow_f8 (s6, 512) *)
Definition AN_FREE : Z := 0x4284.       (* 0x8a768 jal __asan_stack_free_7 (s2, 4256) *)
Definition AN_RET : Z := 0x42d8.        (* 0x8a7bc ret *)
(* the frame size the class-7 entries take (lui a0,1; addiw a0,a0,160) *)
Definition AN_FRAME : Z := 4256.
(* the callee-saved registers the prologue saves at sp0 - 8 - 8 j (0x8a4c8 .. 0x8a4f8: ra at 120(sp), s0 at 112(sp),
   ..., s11 at 24(sp), sp = sp0 - 128) *)
Definition an_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* ---- cgif's walk tactics (cgif lib/A/ACkc.v:32-389), over fuzz_command's listing, as arg_i's walk copies them ---- *)
Definition chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Ltac rnLAWS := lazymatch goal with L : AR_laws _ _ |- _ => L end.
Ltac rnTL := lazymatch goal with T : PALib _ |- _ => T end.
Ltac rnTLF := lazymatch goal with T : PALibF _ |- _ => T end.
Ltac rnHEI E := lazymatch goal with H : img_env _ _ E |- _ => H | _ => fail "rnHEI: no img_env fact for" E end.
Ltac hei_pose Eo kk ws :=
let Ho := rnHEI Eo in let H := fresh "HEIh" in
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as H | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as H ].
Ltac hei_havoc HS :=
lazymatch type of HS with
| st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ => first [ let H0 := rnHEI constr:(havoc Eo kk ws) in idtac | hei_pose Eo kk ws ]
| _ => idtac end.
Ltac nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 32)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac idx_of_base rs n :=
lazymatch rs with
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_base tl n in constr:(S i)
end.
Ltac clear_frames := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac submem_to := repeat (first [apply submem_keep; [subregion_tac|] | apply submem_drop]); apply submem_nil.
Definition trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => trim_region r lo hi :: t
| _ => r :: trim_stack t lo hi end end.
Lemma sp1_facts : forall x, 0 <= x -> x mod 16 = 0 -> x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. rewrite M64_val.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma sv_denot_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma zr_apart : forall lo1 hi1 lo2 hi2, lo1 < hi1 -> lo2 < hi2 ->
(forall a, lo1 <= a < hi1 -> ~ (lo2 <= a < hi2)) -> hi1 <= lo2 \/ hi2 <= lo1.
Proof. intros lo1 hi1 lo2 hi2 H1 H2 H. destruct (Z_le_gt_dec hi1 lo2); [left; exact l|]. right.
destruct (Z_le_gt_dec hi2 lo1); [exact l|]. exfalso. apply (H (Z.max lo1 lo2)); lia. Qed.

(* ---- the model: the recorder state answer hands to hand_back ---- *)
Definition an_R1 (R : rstate) (e : rcall) (chg : bool) : rstate :=
if r_refuse R =? 0 then (if chg then rec_mix R e else R) else R.
Lemma an_R1_answer : forall R e x chg,
rec_answer R e x chg = hand_back (an_R1 R e chg) (snd (rec_answer R e x chg)).
Proof. intros R e x chg. unfold rec_answer, an_R1, hand_back. destruct (r_refuse R =? 0); reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the read-only range is fixed (CmdGlob.v CMD_RLO / CMD_RHI) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* answer's footprint (answer_c.v:111-112) *)
Definition an_FP (old : Z) (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
ablocks_fp (filter (fun pn => fst pn =? old) O).

(* answer's post-condition body (answer_c.v:115-130), word for word *)
Definition an_Q (R : rstate) (e : rcall) (x : list byte) (chg : bool) (old : Z) (O : list (Z * Z)) ly S
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
let t := snd (rec_answer R e x chg) in
(fun ly' S' W' regs' mem' md' => exists p1 p2 O',
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
 (forall pn, In pn (ablocks B ly S) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
 (forall pn, In pn (ablocks B ly' S') <->
   (In pn (ablocks B ly S) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
 rec_repA B ly' S' (rdW W' mem') (fst (rec_answer R e x chg)) O' /\
 (forall pn, In pn O' <-> (In pn O /\ fst pn <> old) \/ pn = (p1, n)) /\
 astr_atR (rdW W' mem') p2 t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_ANSWER t /\
 mo_le MT S S' (XM_ANSWER MT t)).

Definition an_post (regs : bvmap 5 word) ly S W mem md R e x chg old O : world SEGS -> config -> Prop :=
apost_base SEGS B ANSWER_STK (an_FP old O) regs ly S W mem md EV_ANSWER (an_Q R e x chg old O ly S).
(* the statement's post (answer_c.v:113-133): FP-existential, since the refusal arm calls the snprintf wrapper *)
Definition an_postF (regs : bvmap 5 word) ly S W mem md R e x chg old O : world SEGS -> config -> Prop :=
apost_baseF SEGS B ANSWER_STK (an_FP old O) regs ly S W mem md EV_ANSWER (an_Q R e x chg old O ly S).

(* answer's premises (answer_c.v:85-111) but the rounding mode, bundled; the 64-bit ranges of c, sh and old in the
   last *)
Definition an_pre ly S W (regs : bvmap 5 word) mem md ch (c sh old : Z) (e : rcall) (x : list byte) (chg : bool)
(R : rstate) (O : list (Z * Z)) : Prop :=
let t := snd (rec_answer R e x chg) in
afn_pre SEGS B ANSWER_STK ly S W regs mem md ch /\
Z.of_nat (length (frames S)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 c /\ getr regs 11 = w64 sh /\ chg = negb (bv_unsigned (getr regs 12) =? 0) /\
rec_repA B ly S (rdW W mem) R O /\
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old /\
(r_refuse R = 0 -> astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O sh (Some x) /\ fits x) /\
(r_refuse R = 0 -> chg = true ->
 (exists k, nth_error (r_calls R) k = Some e /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
 (c = A_REC_SPILL /\ e = r_spill R)) /\
st_nev S + EV_ANSWER <= EV_MAX /\ blocks_bytes S + LIVE_ANSWER t <= LIVE_MAX /\
mo_ok MT S (XM_ANSWER MT t) /\
(0 <= c < 2 ^ 64 /\ 0 <= sh < 2 ^ 64 /\ 0 <= old < 2 ^ 64).

(* the callee-saved registers of the entry, in the prologue's slots *)
Definition an_saved_ok (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error an_saved j = Some r ->
aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).

(* the registers of the body, between the prologue and the epilogue (F = the class-7 frame, sp1 = the realigned sp):
   sp = s1 = sp1, s0 = sp0, s2 = s9 = F, s4 = shadow(F), s5 = buf = F + 32, s6 = shadow(buf), s7 = changes, s8 = c,
   s10 = the shadow base *)
Definition an_regs_body (regs regs1 : bvmap 5 word) (sp1 F : Z) : Prop :=
getr regs1 2 = w64 sp1 /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (spZ regs) /\ getr regs1 9 = w64 sp1 /\
getr regs1 18 = w64 F /\ getr regs1 25 = w64 F /\
getr regs1 20 = w64 (shadow_addr F) /\ getr regs1 21 = w64 (F + 32) /\ getr regs1 22 = w64 (shadow_addr F + 4) /\
getr regs1 23 = getr regs 12 /\ getr regs1 24 = getr regs 10 /\ getr regs1 26 = w64 SB.

(* the invariant of the body: the walk's journal from answer's entry holds the class-7 frame (7, pos), the meter has
   not moved and the live blocks are the entry's (nothing before hand_back allocates or frees), the prologue's slots
   hold the callee-saved registers, the frame's flag word is intact (for __asan_stack_free_7), buf's shadow is zero
   (for the inline checks and hand_back), and the recorder's representation holds R1 with the answer `old` *)
Definition an_mid ly S W (regs : bvmap 5 word) mem md (R1 : rstate) (old : Z) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) memc mdc (pos k sp1 : Z) : Prop :=
let F := frame_addr lyc 7 pos in
ajournal SEGS B ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] lyc Sc Wc memc mdc k /\
mo_le MT S Sc 0 /\ Permutation (ablocks B lyc Sc) (ablocks B ly S) /\
sp1 = 32 * ((spZ regs - 128) / 32) /\
an_saved_ok (rdW Wc memc) (spZ regs) regs /\
rdword (rdW Wc memc) (F + fs_frame_bytes 7 - 8) = Some (flag_addr lyc 7 pos) /\
zero_shadow (rdW Wc memc) SHADOW_OFF (F + 32) 4096 /\
rec_repA B lyc Sc (rdW Wc memc) R1 O /\
aval_mem (rdW Wc memc) (A_G_REC + OFF_ANSWER) 8 old.

(* ---- the three cut points ---- *)

(* BODY, 0x8a61c: back from __asan_set_shadow_00; s3 = the shape pointer. The refusal arm calls the snprintf
   wrapper, so BODY carries the statement's rounding-mode premise (answer_c.v:87) and its FP-existential post. *)
Definition AN_BODY_stmt : Prop :=
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1,
an_pre ly S W regs mem md ch c sh old e x chg R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
an_mid ly S W regs mem md R old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body regs regs1 sp1 (frame_addr lyc 7 pos) ->
getr regs1 19 = w64 sh ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AN_BODY)) memc (seg_rom SEGS)) mdc)
(an_postF regs ly S W mem md R e x chg old O).

(* HEAD, 0x8a670: j bytes of the shape consumed at depth d, `out` written into buf, out ++ inst_go d (rest) = inst x;
   a0 = s3 = sh + j, a1 = |out|, a2 = d, a3 = '<', a4 = '>', s11 = g_rec *)
Definition AN_HEAD_stmt : Prop :=
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 j d out,
an_pre ly S W regs mem md ch c sh old e x chg R O ->
r_refuse R = 0 ->
an_mid ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body regs regs1 sp1 (frame_addr lyc 7 pos) ->
getr regs1 27 = w64 A_G_REC ->
(j <= length x)%nat -> (d <= j)%nat -> out ++ inst_go d (skipn j x) = inst x ->
getr regs1 10 = w64 (sh + Z.of_nat j) -> getr regs1 19 = w64 (sh + Z.of_nat j) ->
getr regs1 11 = w64 (Z.of_nat (length out)) -> getr regs1 12 = w64 (Z.of_nat d) ->
getr regs1 13 = w64 60 -> getr regs1 14 = w64 62 ->
abytes_atR (rdW Wc memc) (frame_addr lyc 7 pos + 32) out ->
astr_atR (rdW Wc memc) sh x ->
range_addressable (rdW Wc memc) SHADOW_OFF sh (Z.of_nat (length x) + 1) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AN_HEAD)) memc (seg_rom SEGS)) mdc)
(an_post regs ly S W mem md R e x chg old O).

(* JOIN, 0x8a734: buf holds the answer text t and its terminator; the recorder holds an_R1 *)
Definition AN_JOIN_stmt : Prop :=
forall ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1,
an_pre ly S W regs mem md ch c sh old e x chg R O ->
an_mid ly S W regs mem md (an_R1 R e chg) old O lyc Sc Wc memc mdc pos 0 sp1 ->
an_regs_body regs regs1 sp1 (frame_addr lyc 7 pos) ->
getr regs1 27 = w64 A_G_REC ->
astr_atR (rdW Wc memc) (frame_addr lyc 7 pos + 32) (snd (rec_answer R e x chg)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AN_JOIN)) memc (seg_rom SEGS)) mdc)
(an_post regs ly S W mem md R e x chg old O).

(* ---- facts a segment carries over the walk's journal ---- *)
Section k.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.

(* the program's statics are the record's (CmdBSyms' ts_prog) *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hr & Ha). rewrite (ts_prog B HB). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
unfold TFIB_PROG_STATIC. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
[apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
unfold in_zr; cbn [fst snd]; lia.
Qed.

(* the runtime entries' read-only view (RtDefs.v rt_rom_view, a ROM byte outside the owned ranges and the errno
   cell) is part of arodata_okP: a ROM byte is in_roP's first disjunct *)
Lemma an_rom_view : forall (W : world SEGS) mem,
arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof. intros W mem HR a Hrom Ho He. apply HR; [left; exact Hrom | exact Ho | exact He]. Qed.

End k.
End e.
End f.
End d.
