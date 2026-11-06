(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's op_add, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (call sites) and lib/A/ACbk.v (entry and return). *)
(* op_add () at 0x84f10 (fuzz_reply.c:573-594).  It scans g_s[0..3] for the first source whose open flag is 0;
   if there is none it returns with nothing changed.  Otherwise, for that slot i it calls source_reset (the slot
   is already closed, so the callee's o is None), bumps the global g_nfd, stores the new descriptor
   100 + g_nfd into g_s[i].fd, mallocs the 6000-byte partial buffer into g_s[i].partial, sets g_s[i].open to 1
   and calls relay_add (g_s[i].fd), aborting unless it returns 0 (it cannot abort: the descriptor is >= 0).
   Plain contract: lib/Prog/op_add_c.v:33-97, without the plain side's runtime-resource terms
   (rt_ok / roomF / runF), which the ASan side states as the allocator's live-state meter MT.
   Section hypotheses: the two internal calls (SR = source_reset, RA = relay_add) and the allocator's
   malloc site rule AMA (W_journal.v amalloc_cf_rule_c, GUIDE section 3.1, at its caller context), plus the placement
   equations HGS / HNFD of the two globals it names and their separation HOAD. *)
(* Theorem Labs, 2026-10 (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): the walk is proved ONCE, in
   Section x, over the generic allocator relation ARx with its laws (YCbqG.AR_laws_x) and the generic journal of
   W_journal_x.v: pb_op_add_x : oa_spec_x, where oa_post_x / oa_spec_x are this file's contract with the ghost head set
   Hp after S (Hp' after S').  pb_op_add (statement unchanged) and pb_op_add_g are corollaries at ARx := ARi0 (cgif's AR
   with Hp = []), PST := [].  The malloc site is the caller-context rule (amalloc_cf_rule_c(_x)) at one closed trace
   fact HCTX_oa_malloc: op_add hands malloc the empty chain, so the trace is [op_add + 0xcc]. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00 YN0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_journal W_rep W_contract
W_frame W_op_add_src.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_kit_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_srlf_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_op_add : Z := AF_fr_op_add.
Definition A_op_addP : Z := BASE + A_op_add.
(* g_nfd (fuzz_reply.asan 0x5d8820, the listing's A_OBJ 29); it is not one of W_rep.v's rep_globals. *)
Definition A_NFD : Z := 0x5d8820.
Definition OA_FRAME : Z := 64.
(* A register whose value the engine cannot name again after the loop's strength reduction
   (s3 = SB + (g_s + 4 + 96 i) / 8 is built as SB + (g_s + 4) / 8 + 12 i, which the shadow-token
   matcher of Reusable/YCbn.v:78 match_x does not see): replace its symbolic value by one with the
   same denotation.  This is Reusable/YI08.v:129 st_ok_set_reg at the pi layer. *)
Lemma st_ok_pi_set_sv : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> r <> 0%bv -> getr (ms_regs ms) r = sv_denot E e ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He. unfold st_ok_pi, abs_ss in HS |- *.
destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts setpc] in HS |- *.
exact (YI08.st_ok_set_reg SEGS E (mkSST (VAL A_TEXT + pc0) sr0 fr0 sm0 rv0 fs0) ms r e HS Hr He).
Qed.
(* one trip of the loop: the shadow pointer of g_s + c moves by 12 bytes, which is the shadow of 96 *)
Lemma oa_sh_bump : forall (E : env) (gs c : Z),
ew E 37 = Z_to_bv 64 SB -> ew E 263 = Z_to_bv 64 gs ->
0 <= gs -> gs + 400 < 2 ^ 64 -> 0 <= c -> c + 96 <= 400 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SRL (SOff 263 c) (SLit 3))) (SLit 12))
= sv_denot E (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SRL (SOff 263 (c + 96)) (SLit 3))).
Proof.
intros E gs c H37 H263 Hgs0 Hgs1 Hc0 Hc1. apply U_inj.
assert (Hd : (gs + (c + 96)) / 8 = (gs + c) / 8 + 12).
{ replace (gs + (c + 96)) with (gs + c + 12 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
assert (Hq0 : 0 <= (gs + c) / 8) by (apply Z.div_pos; lia).
assert (Hq1 : 8 * ((gs + c) / 8) <= gs + c) by (apply Z.mul_div_le; lia).
assert (Hr : forall d, 0 <= d -> d <= 400 ->
  U E (SAlu ALU_SRL (SOff 263 d) (SLit 3)) = (gs + d) / 8).
{ intros d Hd0 Hd1. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E 263 gs d H263) by lia. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|].
  pose proof (Z.div_le_upper_bound (gs + d) 8 (gs + d) ltac:(lia) ltac:(lia)). lia. }
rewrite !(U_SAlu E ALU_ADD). cbn [zalu_raw].
rewrite (Hr c Hc0 ltac:(lia)), (Hr (c + 96) ltac:(lia) ltac:(lia)).
rewrite !(U_atom E 37 SB H37) by (unfold SB; lia).
rewrite U_SLit, Hd. change (zcanon 12) with 12.
rewrite (zcanon_id (SB + (gs + c) / 8)) by (unfold M64, SB; lia).
f_equal. lia.
Qed.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).

(* ---------------- op_add's own contract ---------------- *)
(* frame 64; the deepest callee is relay_add (RA_STK = 128 + ASTACK), above source_reset (SR_STK) and malloc *)
Definition OA_STK : Z := OA_FRAME + RA_STK.
(* the first slot whose open flag is zero *)
Definition oa_first (os : list Z) : option nat :=
if nth 0 os 0 =? 0 then Some 0%nat
else if nth 1 os 0 =? 0 then Some 1%nat
else if nth 2 os 0 =? 0 then Some 2%nat
else if nth 3 os 0 =? 0 then Some 3%nat else None.
Definition oa_HA (i : nat) : Z := rg_s fr_globals + ASRC * Z.of_nat i.
(* the source op_add opens: descriptor fd, the 6000-byte buffer q, everything else zero
   (lib/Prog/op_add_c.v:22 new_src) *)
Definition oa_new_src (fd q : Z) (pj : list byte) : hsrc :=
HS fd 1 0 0 empty_list 0 q pj 0 0 [] empty_list empty_list.
Definition oa_cost : Z := sr_cost MT None + mo_malloc MT APARTIAL + mo_malloc MT ATABLE + mo_free MT.
Definition oa_FP (os : list Z) (T : Z) (es : list rentry) : list (Z * Z) :=
match oa_first os with None => [] | Some _ => ra_FP T es end.
(* the program globals op_add writes: the slot it opens, g_nfd, and the four words relay_add writes.
   Every OTHER byte of the caller's G keeps its view (the callee journals are taken at their own globals,
   so each keeps every image byte outside them).  errno is NOT in this clause (gx_rt keeps it out of G); oa_post
   states errno's view separately, as its last conjunct. *)
Definition oa_wr (os : list Z) (a : Z) : Prop :=
match oa_first os with
| None => False
| Some i => oa_HA i <= a < oa_HA i + ASRC \/ A_NFD <= a < A_NFD + 4 \/ inG (RA_G fr_globals) a
end.
Definition oa_kept (os : list Z) (W : world SEGS) (mem : word -> option byte)
(W' : world SEGS) (mem' : word -> option byte) : Prop :=
forall a, inG G a -> ~ oa_wr os a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
(* what one run of the walk keeps: every byte outside op_add's own frame *)
Definition oa_kept_fr (W : world SEGS) (sp : Z) (mem m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (sp - OA_FRAME <= a < sp) ->
aview SEGS (w_H W) m a = aview SEGS (w_H W) mem a.
Definition oa_post (regs : bvmap 5 word) ly S (W : world SEGS) (mem : word -> option byte) (md : Model)
(os : list Z) (n0 T : Z) (es : list rentry) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md' kk,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx SEGS B G 0 [] OA_STK (spZ regs) (oa_FP os T es) ly S W mem md [] ly' S' W' mem' md' kk /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\ oa_kept os W mem W' mem' /\ frames S' = frames S /\
match oa_first os with
| None => ly' = ly /\ S' = S /\ W' = W /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - OA_STK <= a < spZ regs) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)
| Some i => exists (q T' : Z) (pj : list byte),
    asrc_at B ly' S' W' mem' (oa_HA i) (oa_new_src (100 + n0) q pj) /\
    val_mem SEGS (arm W' mem') A_NFD 4 (n0 + 1) /\
    arelay_at B fr_globals ly' S' W' mem' T' (es ++ [ra_new (100 + n0)]) /\
    alock_at fr_globals W' mem' false /\
    ((T = 0 /\ Permutation (ablocks B ly' S') ((T', ATABLE) :: (q, APARTIAL) :: ablocks B ly S)) \/
     (T <> 0 /\ T' = T /\ Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S))) /\
    mo_le MT S S' oa_cost
end /\
(* errno's four bytes keep their view (source_reset, malloc and relay_add keep them; op_add's runs never store to
   them: gx_rt keeps errno out of G) *)
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
(* G is op_add's own G (oa_spec_g takes it with gx_prog).  It must hold ALL of g_s (384 bytes), g_nfd and RA_G:
   G_oa = [(rg_s fr_globals, 384); (A_NFD, 4)] ++ RA_G fr_globals (it misses errno, so gx_prog can hold).  The slot
   alone, [(rg_s fr_globals + 96 * i, 96)], is too small: op_add reads every open flag and writes g_nfd and RA_G.
   The writability of the bytes op_add stores to is gx_prog's (every byte of G is writable in every memory). *)
Definition oa_spec (pc : Z) : Prop :=
forall W ly S regs mem md ch (os : list Z) (n0 T : Z) (es : list rentry),
afn_pre SEGS B OA_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
length os = 4%nat ->
(forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31) ->
(forall i, (i < 4)%nat -> val_mem SEGS (arm W mem) (oa_HA i + 4) 4 (nth i os 0)) ->
(forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W mem (oa_HA i)) ->
val_mem SEGS (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es ->
alock_at fr_globals W mem false -> awake_at fr_globals W mem ->
rom_view SEGS W mem ->
(oa_first os <> None -> (length es < 4)%nat /\ ~ In (100 + n0) (map re_fd es)) ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX ->
mo_ok MT S oa_cost ->
SRr SEGS W (cfg_at SEGS pc regs mem md) (oa_post regs ly S W mem md os n0 T es).
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): op_add's allocator calls counted by W_contract_x.MT_rk (source_reset
   on no slot, the slot's malloc, relay_add's realloc), and its peak net growth of live P-requests (the table, the
   slot's APARTIAL block) *)
Definition oa_rk : nat := Z.to_nat (sr_cost MT_rk None + mo_malloc MT_rk APARTIAL + mo_malloc MT_rk ATABLE + mo_free MT_rk).
Definition oa_peak : (Z -> bool) -> nat := fun P => ((if P ATABLE then 1 else 0) + (if P APARTIAL then 1 else 0))%nat.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): oa_post_x / oa_spec_x (Section x below) at a world relation R.  Each <name>_xR is
   <name> with the journal ajournal_gx_x -> ajournal_gx_xR .. R and SRr SEGS -> SRrG SEGS R; every other token is the
   strict text's.  R comes right after ARx (NAMES.md sha256 4a0eb3e6fe06; internal record), so these texts sit in their own Section before
   Section x: oa_spec_xR B MT G PST ARx R RP pc.  At R := wle they are the strict texts (oa_post_x_wle / oa_spec_x_wle,
   by reflexivity). *)
Section xR.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable R : world SEGS -> world SEGS -> Prop.
Variable RP : roomp.
(* :207 oa_post_x *)
Definition oa_post_xR (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(os : list Z) (n0 T : Z) (es : list rentry) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] OA_STK (spZ regs) (oa_FP os T es) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\ oa_kept os W mem W' mem' /\ frames S' = frames S /\ rp_RM RP S' kr /\
match oa_first os with
| None => ly' = ly /\ S' = S /\ W' = W /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - OA_STK <= a < spZ regs) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)
| Some i => exists (q T' : Z) (pj : list byte),
    asrc_at B ly' S' W' mem' (oa_HA i) (oa_new_src (100 + n0) q pj) /\
    val_mem SEGS (arm W' mem') A_NFD 4 (n0 + 1) /\
    arelay_at B fr_globals ly' S' W' mem' T' (es ++ [ra_new (100 + n0)]) /\
    alock_at fr_globals W' mem' false /\
    ((T = 0 /\ Permutation (ablocks B ly' S') ((T', ATABLE) :: (q, APARTIAL) :: ablocks B ly S)) \/
     (T <> 0 /\ T' = T /\ Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S))) /\
    mo_le MT S S' oa_cost
end /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
(* :227 oa_spec_x *)
Definition oa_spec_xR (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch (os : list Z) (n0 T : Z) (es : list rentry),
afn_pre_x SEGS B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
length os = 4%nat ->
(forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31) ->
(forall i, (i < 4)%nat -> val_mem SEGS (arm W mem) (oa_HA i + 4) 4 (nth i os 0)) ->
(forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W mem (oa_HA i)) ->
val_mem SEGS (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es ->
alock_at fr_globals W mem false -> awake_at fr_globals W mem ->
rom_view SEGS W mem ->
(oa_first os <> None -> (length es < 4)%nat /\ ~ In (100 + n0) (map re_fd es)) ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX ->
mo_ok MT S oa_cost ->
forall kr : nat,
rp_RM RP S (oa_rk + kr) ->
cnt_ok_pk RP oa_peak (ablocks B ly S) ->
SRrG SEGS R W (cfg_at SEGS pc regs mem md) (oa_post_xR regs ly S Hp W mem md os n0 T es kr).
End xR.

(* ---------------- the walk, over the generic allocator relation ARx ---------------- *)
(* The Section hypotheses beyond the AR walk's: PST / ARx / hl / LAWS (the generic relation and its laws), HP0 (no hidden
   head in any ARx state; a Theorem Labs lane's ruling), HPST (the program statics PST miss the image: every walk takes
   PST := [], the program's globals go through the G overlay), and the allocator rules' caller-context tables: CTX_M
   for malloc with op_add's malloc trace HCTX_oa_malloc, CTX_R for relay_add's realloc with its trace HCTXRA (the
   instance proves each rule at its own table, so the two are separate variables). *)
Section x.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable RP : roomp.
(* oa_post / oa_spec over ARx: the same text, with the ghost head set Hp after S (Hp' after S') *)
Definition oa_post_x (regs : bvmap 5 word) ly S (Hp : list Z) (W : world SEGS) (mem : word -> option byte) (md : Model)
(os : list Z) (n0 T : Z) (es : list rentry) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md' kk,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
ajournal_gx_x SEGS B PST ARx G 0 [] OA_STK (spZ regs) (oa_FP os T es) ly S Hp W mem md [] ly' S' Hp' W' mem' md' kk /\
aregs_preserved regs regs' /\
apres_kept B W mem W' mem' /\ oa_kept os W mem W' mem' /\ frames S' = frames S /\ rp_RM RP S' kr /\
match oa_first os with
| None => ly' = ly /\ S' = S /\ W' = W /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - OA_STK <= a < spZ regs) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)
| Some i => exists (q T' : Z) (pj : list byte),
    asrc_at B ly' S' W' mem' (oa_HA i) (oa_new_src (100 + n0) q pj) /\
    val_mem SEGS (arm W' mem') A_NFD 4 (n0 + 1) /\
    arelay_at B fr_globals ly' S' W' mem' T' (es ++ [ra_new (100 + n0)]) /\
    alock_at fr_globals W' mem' false /\
    ((T = 0 /\ Permutation (ablocks B ly' S') ((T', ATABLE) :: (q, APARTIAL) :: ablocks B ly S)) \/
     (T <> 0 /\ T' = T /\ Permutation (ablocks B ly' S') ((q, APARTIAL) :: ablocks B ly S))) /\
    mo_le MT S S' oa_cost
end /\
(* errno's four bytes keep their view (source_reset, malloc and relay_add keep them; op_add's runs never store to
   them: gx_rt keeps errno out of G) *)
(forall i, 0 <= i < 4 -> aview SEGS (w_H W') mem' (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
Definition oa_spec_x (pc : Z) : Prop :=
forall W ly S Hp regs mem md ch (os : list Z) (n0 T : Z) (es : list rentry),
afn_pre_x SEGS B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
length os = 4%nat ->
(forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31) ->
(forall i, (i < 4)%nat -> val_mem SEGS (arm W mem) (oa_HA i + 4) 4 (nth i os 0)) ->
(forall i, (i < 4)%nat -> nth i os 0 = 0 -> asrc_closed W mem (oa_HA i)) ->
val_mem SEGS (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es ->
alock_at fr_globals W mem false -> awake_at fr_globals W mem ->
rom_view SEGS W mem ->
(oa_first os <> None -> (length es < 4)%nat /\ ~ In (100 + n0) (map re_fd es)) ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX ->
mo_ok MT S oa_cost ->
forall kr : nat,
rp_RM RP S (oa_rk + kr) ->
cnt_ok_pk RP oa_peak (ablocks B ly S) ->
SRr SEGS W (cfg_at SEGS pc regs mem md) (oa_post_x regs ly S Hp W mem md os n0 T es kr).
Lemma oa_post_x_wle : oa_post_x = oa_post_xR PST ARx (@wle SEGS) RP. Proof. reflexivity. Qed.
Lemma oa_spec_x_wle : oa_spec_x = oa_spec_xR PST ARx (@wle SEGS) RP. Proof. reflexivity. Qed.
(* the strict contract gives the R contract at any R containing wle (the post journal by ajournal_gx_xR_mono) *)
Section xRi.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Lemma oa_post_xR_of_x : forall regs ly S Hp W mem md os n0 T es kr W' c',
  oa_post_x regs ly S Hp W mem md os n0 T es kr W' c' -> oa_post_xR PST ARx R RP regs ly S Hp W mem md os n0 T es kr W' c'.
Proof.
intros regs ly S Hp W mem md os n0 T es kr W' c' (ly' & S' & Hp' & regs' & mem' & md' & kk & Hc & HJ & REST).
exists ly', S', Hp', regs', mem', md', kk. split; [exact Hc|]. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma oa_spec_xR_of_x : forall pc, oa_spec_x pc -> oa_spec_xR PST ARx R RP pc.
Proof.
intros pc H. unfold oa_spec_xR. intros.
eapply SRrG_mono; [eapply SRr_SRrG; [exact WLE_R | eapply H; eassumption] |].
intros W' c' _ HP. eapply oa_post_xR_of_x. exact HP.
Qed.
End xRi.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* the image is off PST, so a callee's journal keeps every image byte outside the callee's own G, and ROM *)
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
(* the room round: the room's budget monotonicity (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) section 0.4, RMM; true at the instance,
   whose RM ignores the budget).  op_add's arm with no free slot and its arm with a table (T <> 0) spend less than
   oa_rk *)
Hypothesis RMM : forall S k k', (k <= k')%nat -> rp_RM RP S k' -> rp_RM RP S k.
Variable MMAX : Z.
Hypothesis HMMAX : APARTIAL < MMAX.
(* op_add's own G: W_contract_x.v gx_prog_x (gx_ok, gx_rt, rom_out and the three image facts its source_reset call
   needs at the slot) *)
Hypothesis HGP : gx_prog_x B ARx G.
Let HG : gx_ok SEGS B G := proj1 HGP.
Let HGRT : gx_rt B G := proj1 (proj2 HGP).
Let HRO : rom_out SEGS B G := proj1 (proj2 (proj2 HGP)).
Let HGW : forall a, inG G a -> forall m, writable_at SEGS m a := proj1 (proj2 (proj2 (proj2 (proj2 HGP)))).
(* the two globals op_add names, at the pinned placement (W_img.v PB_fr decides both by vm_compute) *)
Hypothesis HGS : VAL (A_OBJ 22) = rg_s fr_globals.
Hypothesis HNFD : VAL (A_OBJ 29) = A_NFD.
(* the auipc that g_nfd's store goes through: the listing fixes the load's object but not the store's
   base, so the walk takes the one equation (vm_compute at PB_fr: 0x5d8fa8 = 0x5d8820 + 1928) *)
Hypothesis HHI92 : VAL (A_HI 92) = A_NFD + 1928.
(* g_s and g_nfd miss the GOT slot of the shadow base and the shadow cell, so the entry's symbolic regions are
   disjoint (vm_compute at PB_fr) *)
Hypothesis HOAD :
(VAL (A_OBJ 0) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 0) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 32) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 32)) /\
(VAL (A_OBJ 32) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 32)).
(* g_wake[1] (awake_at) is an image byte outside the allocator's statics and errno, so the source_reset and malloc
   calls before relay_add keep it (it is not in G: op_add never writes it; vm_compute at PB_fr) *)
Hypothesis HWK : forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* malloc at the caller-context rule (W_journal_x.v Section hc): op_add hands malloc the EMPTY chain too (s0 is the
   g_s slot pointer), so the call's trace is its one return address, op_add + 0xcc (`jal malloc` at 0x84fd8 returns to
   0x84fdc = 0x84f10 + 0xcc), whatever op_add's caller is: a CLOSED fact about the table (StartupTrace: A's
   CTX_AMALLOC holds [0x84fdc]).  CTX_M is malloc's table (the instance's CTX_AMALLOC). *)
Variable CTX_M : list (list Z).
Hypothesis HCTX_oa_malloc : In [BASE + AF_fr_op_add + 0xcc] CTX_M.
Hypothesis AMA : amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_M.
Hypothesis SR : sr_spec_g_x B PST ARx MT RP (BASE + AF_fr_source_reset).
(* relay_add at its own globals RA_G fr_globals (W_contract_x.v Section w5g ra_spec_g_x), over the allocator rules'
   caller-context table CTX_R (W_journal.v Section hc; the instance's CTX_AREALLOC).  op_add hands relay_add the EMPTY chain: op_add reuses s0 as
   the g_s slot pointer, an image address, so the unwinder stops at relay_add's own record (achain_low below).  The
   realloc relay_add makes when its table is new therefore has the trace [relay_add + 332; op_add + 264] (relay_add's
   realloc returns to 0x82a9c = 0x82950 + 332; op_add's `jal relay_add` at 0x85014 returns to 0x85018 = 0x84f10 +
   264), whatever op_add's caller is: a CLOSED fact about the table, vm_compute at the instance's CTX_R. *)
Variable CTX_R : list (list Z).
Hypothesis HCTXRA : In [BASE + AF_fr_relay_add + 332; BASE + AF_fr_op_add + 264] CTX_R.
Hypothesis RA : ra_spec_g_x B PST ARx MT RP fr_globals CTX_R (BASE + AF_fr_relay_add).
(* ROM is image, so off PST *)
Lemma oa_pstr : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr]. Qed.
(* the room round: the count premises op_add hands its three allocator calls, from its own count at the entry
   (cnt_ok_pk RP oa_peak).  source_reset and malloc run on a permutation of the entry's blocks (peak 0); relay_add runs
   with the slot's APARTIAL block added, and its peak is at most the table *)
Lemma oa_cnt_perm : forall pk' l l', Permutation l' l -> (forall P, (pk' P <= oa_peak P)%nat) ->
cnt_ok_pk RP oa_peak l -> cnt_ok_pk RP pk' l'.
Proof.
intros pk' l l' Hp Hk Hc. apply (cnt_ok_pk_mono RP oa_peak pk' l l'); [|exact Hc].
intros P. rewrite (acnt_perm P _ _ Hp). specialize (Hk P). lia.
Qed.
Lemma oa_cnt_ra : forall l l2 q T, Permutation l2 l ->
cnt_ok_pk RP oa_peak l -> cnt_ok_pk RP (ra_peak T) (l2 ++ [(q, APARTIAL)]).
Proof.
intros l l2 q T Hp Hc. apply (cnt_ok_pk_mono RP oa_peak (ra_peak T) l (l2 ++ [(q, APARTIAL)])); [|exact Hc].
intros P. rewrite acnt_app, (acnt_perm P _ _ Hp), acnt_cons, acnt_nil. unfold ra_peak, oa_peak. cbn [snd].
destruct (P ATABLE), (P APARTIAL), (T =? 0); cbn [andb]; lia.
Qed.
(* What a callee taken at its OWN globals G' keeps: every image byte outside G', the allocator's statics
   and errno.  This is the donor journal's image clause (Reusable/YCbq.v:363) read through the overlay of
   W_journal.v's ajournal_g (the callee's start memory differs from the caller's only on G'). *)
Lemma oa_call_keep : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world SEGS) m0 md0 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k,
ajournal_gx_x SEGS B PST ARx G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
forall a, in_img SEGS a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W1) m1 a = aview SEGS (w_H W0) m0 a.
Proof.
intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a Him Hno He (HPST a Him) ltac:(apply fp_spares_closed; exact Hsk)).
apply (aview_gagree SEGS G' (w_H W0) m0 memS a HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* the bytes of a block live before and after the call, outside the callee's FP *)
Lemma oa_call_keep_blk : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world SEGS) m0 md0 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k,
gx_ok SEGS B G' ->
ajournal_gx_x SEGS B PST ARx G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
~ inFP FP (p + j) -> aview SEGS (w_H W1) m1 (p + j) = aview SEGS (w_H W0) m0 (p + j).
Proof.
intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 p n j H0 H1 Hj Hfp).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
apply (aview_gagree SEGS G' (w_H W0) m0 memS (p + j) HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
(* and what it keeps above alloc_ceiling: every byte outside its own window (the caller's frame is there,
   so the caller's stack region survives the call) *)
Lemma oa_call_keep_hi : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world SEGS) m0 md0 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k,
gx_ok SEGS B G' ->
ajournal_gx_x SEGS B PST ARx G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview SEGS (w_H W1) m1 a = aview SEGS (w_H W0) m0 a.
Proof.
intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HJx a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno).
apply (aview_gagree SEGS G' (w_H W0) m0 memS a HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bx : sv := SOff 37 0.
Definition oa_gs_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 22)) 0 384 0 0
[YP09.mkChunk 4 (CVal 4 (SOff 32 0)); YP09.mkChunk 100 (CVal 4 (SOff 33 0));
 YP09.mkChunk 196 (CVal 4 (SOff 34 0)); YP09.mkChunk 292 (CVal 4 (SOff 35 0))].
(* read-only in the loop: op_add writes g_nfd only after the source_reset call, where the walk adds a
   writable region for it (so a run of the loop writes nothing but the frame) *)
Definition oa_nfd_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 29)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 36 0))].
Definition oa_regions : smem :=
[ stack_region OA_FRAME; got_regionP; bcell_regionP 37; oa_gs_region; oa_nfd_region ].
Definition oa_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4);
          (A_OBJ 22, mkAF (rg_s fr_globals) (rg_s fr_globals) 5);
          (A_OBJ 29, mkAF A_NFD A_NFD 5);
          (32%nat, mkAF 0 (2 ^ 31 - 1) 0); (33%nat, mkAF 0 (2 ^ 31 - 1) 0);
          (34%nat, mkAF 0 (2 ^ 31 - 1) 0); (35%nat, mkAF 0 (2 ^ 31 - 1) 0);
          (36%nat, mkAF 0 512 0); (37%nat, mkAF SB SB 0) ] [] [].
Definition ss_oa : sstate := mkSS A_op_add sr_atoms oa_regions None oa_facts.
Definition oa_SH : list shent := [ mkSHE (A_OBJ 22) 0 384 ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition oa_extra (os : list Z) (n0 : Z) : list word :=
map (Z_to_bv 64) [nth 0 os 0; nth 1 os 0; nth 2 os 0; nth 3 os 0; n0; SB].


Lemma oa_entry : forall W ly S Hp regs mem md ch (os : list Z) (n0 : Z),
afn_pre_x SEGS B ARx OA_STK ly S Hp W regs mem md ch ->
length os = 4%nat ->
(forall i, (i < 4)%nat -> 0 <= nth i os 0 < 2 ^ 31) ->
(forall i, (i < 4)%nat -> val_mem SEGS (arm W mem) (oa_HA i + 4) 4 (nth i os 0)) ->
val_mem SEGS (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (oa_extra os n0))) ss_oa
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_op_addP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx oa_SH (Eimg (Ereg regs (oa_extra os n0))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch os n0 HPRE Hlen Hrng Hcells Hnfd Hn0 HZ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : OA_STK = 16576) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (oa_extra os n0))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (nth 0 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (nth 1 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nth 2 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (nth 3 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 n0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E263 : ew E (A_OBJ 22) = Z_to_bv 64 (VAL (A_OBJ 22))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E270 : ew E (A_OBJ 29) = Z_to_bv 64 (VAL (A_OBJ 29))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 32)) as R32.
pose proof (pa_obj_img 22 ltac:(lia)) as HgsR. rewrite HGS in HgsR.
pose proof (pa_obj_img 29 ltac:(lia)) as HnfdR. rewrite HNFD in HnfdR.
pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (Vgs : base_val E (Some (A_OBJ 22)) = rg_s fr_globals)
by (apply (VB (A_OBJ 22)); [rewrite E263, HGS; reflexivity | unfold fr_globals, rg_s; lia]).
assert (Vnfd : base_val E (Some (A_OBJ 29)) = A_NFD)
by (apply (VB (A_OBJ 29)); [rewrite E270, HNFD; reflexivity | unfold A_NFD; lia]).
split.
- unfold ss_oa, A_op_addP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold oa_regions, oa_gs_region, oa_nfd_region, stack_region, got_regionP, bcell_regionP, OA_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite Vgs. split; [unfold fr_globals, rg_s; lia|]. split; [unfold fr_globals, rg_s in *; lia|].
split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
-- apply (chunk_ok_val SEGS E _ (rg_s fr_globals) 4 4 (SOff 32 0) (nth 0 os 0));
   [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
   | pose proof (Hrng 0%nat ltac:(lia)); zside | zside |].
   pose proof (Hcells 0%nat ltac:(lia)) as HC. unfold oa_HA, arm in HC. cbn [Z.of_nat] in HC.
   rewrite Z.mul_0_r, Z.add_0_r in HC. exact HC.
-- apply (chunk_ok_val SEGS E _ (rg_s fr_globals) 100 4 (SOff 33 0) (nth 1 os 0));
   [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
   | pose proof (Hrng 1%nat ltac:(lia)); zside | zside |].
   pose proof (Hcells 1%nat ltac:(lia)) as HC. unfold oa_HA, arm, ASRC in HC. cbn [Z.of_nat] in HC.
   replace (rg_s fr_globals + 100) with (rg_s fr_globals + 96 * 1 + 4) by lia. exact HC.
-- apply (chunk_ok_val SEGS E _ (rg_s fr_globals) 196 4 (SOff 34 0) (nth 2 os 0));
   [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
   | pose proof (Hrng 2%nat ltac:(lia)); zside | zside |].
   pose proof (Hcells 2%nat ltac:(lia)) as HC. unfold oa_HA, arm, ASRC in HC. cbn [Z.of_nat] in HC.
   replace (rg_s fr_globals + 196) with (rg_s fr_globals + 96 * 2 + 4) by lia. exact HC.
-- apply (chunk_ok_val SEGS E _ (rg_s fr_globals) 292 4 (SOff 35 0) (nth 3 os 0));
   [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
   | pose proof (Hrng 3%nat ltac:(lia)); zside | zside |].
   pose proof (Hcells 3%nat ltac:(lia)) as HC. unfold oa_HA, arm, ASRC in HC. cbn [Z.of_nat] in HC.
   replace (rg_s fr_globals + 292) with (rg_s fr_globals + 96 * 3 + 4) by lia. exact HC.
* rewrite Vnfd. split; [unfold A_NFD; lia|]. split; [unfold A_NFD; lia|].
split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ A_NFD 0 4 (SOff 36 0) n0);
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Hnfd.
+ apply pairwise_disjoint_of_extents.
unfold oa_regions, oa_gs_region, oa_nfd_region, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite Vgs, Vnfd, (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia.
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct HOAD as (D1 & D2 & D3 & D4).
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HgsR HnfdR HgotR HcellR HgcD D1 D2 D3 D4. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, A_NFD, fr_globals, rg_s, ASRC,
OA_FRAME, OA_STK, RA_STK, RA_FRAME, ASTACK.
intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [oa_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, E34, E35, E36, E37, E263, E270, HGS, HNFD, !unsigned_lit_small
  by (unfold SB, A_NFD, fr_globals, rg_s;
      first [ lia | pose proof (Hrng 0%nat ltac:(lia)); lia | pose proof (Hrng 1%nat ltac:(lia)); lia
            | pose proof (Hrng 2%nat ltac:(lia)); lia | pose proof (Hrng 3%nat ltac:(lia)); lia ]).
change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
pose proof (Hrng 0%nat ltac:(lia)). pose proof (Hrng 1%nat ltac:(lia)).
pose proof (Hrng 2%nat ltac:(lia)). pose proof (Hrng 3%nat ltac:(lia)).
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Hn0.
unfold SB, A_NFD, fr_globals, rg_s, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; first [lia | vm_compute; reflexivity].
- unfold sh_ok, oa_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bx (A_OBJ 22) (rg_s fr_globals) (4 * ASRC) (rg_s fr_globals) 0 384).
+ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md _ _ HAR HZ).
+ unfold U, Bx. cbn [sv_denot]. rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E263, Z.add_0_r, Z_to_bv_bv_unsigned, HGS.
  rewrite unsigned_lit_small by (unfold fr_globals, rg_s; lia). reflexivity.
+ lia.
+ unfold ASRC. lia.
+ intros x Hx. unfold SHADOW_OFF, fr_globals, rg_s in *. lia.
Qed.

(* the write obligation of a run of the loop: every region but the frame is read-only there, so the run
   writes no program global and the donor's own obligation does it *)
Ltac oa_awr0 Usp := apply awr_ok_x_of0; awr_ok_tac; exact Usp.
(* one run's view-keeping, outside the frame *)
Ltac oa_keep KEEP Usp :=
  lazymatch type of KEEP with
  | oa_kept_fr ?Wv ?spv ?mem0 ?m1 =>
    lazymatch goal with
    | HFr : frame_of ?Ev ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      let K2 := fresh "KEEP" in
      let Hout := fresh "Hout" in
      assert (K2 : oa_kept_fr Wv spv mem0 m2);
      [ intros a Ha Hno;
        assert (Hout : ~ in_wrange Ev rs a);
        [ intros (r & Hin & Hr);
          try unfold ss_oa, oa_regions in Hin; cbn [ss_mem In] in Hin;
          repeat (destruct Hin as [<- | Hin]); try (destruct Hin);
          unfold stack_region, got_regionP, bcell_regionP, oa_gs_region, oa_nfd_region, OA_FRAME in Hr, Hno;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
          rewrite ?Usp in Hr; first [apply Hno; lia | lia]
        | rewrite (aview_kept_out Ev rs (w_H Wv) m1 m2 HFr a Ha Hout); apply KEEP; assumption ]
      | clear KEEP; rename K2 into KEEP ]
    end
  end.
(* replace a register's symbolic value by one with the same denotation, proved by `tac` *)
Ltac oa_setsv HS r e tac :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    let R := fresh "Rsv" in
    pose proof (st_ok_pi_restrict_reg H Ev ss ms r HS) as R;
    let v := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with v in R;
    let HS' := fresh "HSx" in
    pose proof (st_ok_pi_set_sv Ev ss (restrict H ms) r e HS
      ltac:(intros Heq; apply (f_equal bv_unsigned) in Heq; cbv in Heq; discriminate)
      ltac:(cbn [ms_regs restrict]; rewrite R; tac)) as HS';
    clear HS R; rename HS' into HS;
    let ss2 := eval vm_compute in
      (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) in
    change (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) with ss2 in HS
  end.
(* the loop's strength-reduced shadow pointer s3, renamed to the shadow of g_s + c + 96 *)
Ltac oa_bump HS c E37 E263 :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    let R := fresh "R19" in
    pose proof (st_ok_pi_restrict_reg H Ev ss ms (19%bv : bv 5) HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) (19%bv : bv 5)) in
    change (sr_get (ss_regs ss) (19%bv : bv 5)) with e in R;
    let HS' := fresh "HSb" in
    pose proof (st_ok_pi_set_sv Ev ss (restrict H ms) (19%bv : bv 5)
      (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SRL (SOff 263 (c + 96)) (SLit 3))) HS
      ltac:(intros Heq; apply (f_equal bv_unsigned) in Heq; cbv in Heq; discriminate)
      ltac:(cbn [ms_regs restrict]; rewrite R;
            apply (oa_sh_bump Ev (rg_s fr_globals) c E37 E263); unfold fr_globals, rg_s; lia)) as HS';
    clear HS R; rename HS' into HS;
    let ss2 := eval vm_compute in (mkSS (ss_pc ss) (sr_set (ss_regs ss) (19%bv : bv 5)
      (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SRL (SOff 263 (c + 96)) (SLit 3)))) (ss_mem ss) (ss_resv ss) (ss_facts ss)) in
    change (mkSS (ss_pc ss) (sr_set (ss_regs ss) (19%bv : bv 5)
      (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SRL (SOff 263 (c + 96)) (SLit 3)))) (ss_mem ss) (ss_resv ss) (ss_facts ss))
      with ss2 in HS
  end.
(* an open-flag branch: the flag of slot i against zero *)
Ltac oa_flag Hc Ek i Hrng :=
  rewrite branch_eq_U, (U_atom _ _ _ Ek), U_SLit in Hc by (pose proof (Hrng i ltac:(lia)); lia);
  change (zcanon 0) with 0 in Hc.
(* presence of every image byte that was present at entry, carried across one run *)
Ltac oa_pres AP :=
  lazymatch type of AP with apres_kept ?Bv ?Wv ?memv _ ?m1 =>
  lazymatch goal with HGr : mem_grows (mrestrict _ m1) (mrestrict _ ?m2) |- _ =>
    let AP' := fresh "AP" in
    assert (AP' : apres_kept Bv Wv memv Wv m2)
      by (intros a H1 H2 H3 H4; exact (apresent_grows _ _ _ a HGr (AP a H1 H2 H3 H4)));
    clear AP; rename AP' into AP
  end end.

(* ---------------- the found arm ---------------- *)
(* op_add's frame, as the prologue stores it: ra at 56, s0 .. s6 at 48 .. 0 (offsets from the new sp) *)
Definition oa_saved : list (Z * Z) := [(56, 1); (48, 8); (40, 9); (32, 18); (24, 19); (16, 20); (8, 21); (0, 22)].
(* 0x84fa8, the return address of the source_reset call *)
Definition A_oaf : Z := A_op_add + 152.
(* a symbolic value read as a number *)
Lemma oa_sv_lit : forall E e v, U E e = zcanon v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. apply bv_eq. unfold U in H. rewrite H, Z_to_bv_unsigned. apply zcanon_wrap. Qed.
Lemma oa_sv_lit' : forall E e v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H Hv. apply oa_sv_lit. rewrite H. symmetry. apply zcanon_id. unfold M64. lia. Qed.
(* the shadow address of a + c, SB + (a + c) / 8, in the shadow matcher's form *)
Lemma oa_sh_den : forall E (bx g : nat) sb a c,
ew E bx = Z_to_bv 64 sb -> ew E g = Z_to_bv 64 a -> 0 <= sb < 2 ^ 62 -> 0 <= a < 2 ^ 62 -> 0 <= a + c < 2 ^ 62 ->
sv_denot E (SAlu ALU_ADD (SOff bx 0) (SAlu ALU_SRL (SOff g c) (SLit 3))) = Z_to_bv 64 (sb + (a + c) / 8).
Proof.
intros E bx g sb a c Hb Hg Hsb Ha Hac. apply oa_sv_lit. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E bx sb Hb) by lia. rewrite (U_atom_off E g a c Hg) by lia. rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (a + c) / 8 <= a + c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite (zcanon_id ((a + c) / 8)) by (unfold M64; lia). reflexivity.
Qed.
(* the saved registers, read off a stack region holding them as atoms *)
Lemma oa_saved_of_region : forall E m spv cs lo hi wlo whi (regs : bvmap 5 word),
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = spv ->
(forall r, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))) ->
Forall (fun p => In (YP09.mkChunk (fst p - 64) (CVal 8 (SOff (Z.to_nat (snd p)) 0))) cs) oa_saved ->
Forall (fun p => val_mem SEGS m (spv - 64 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) oa_saved.
Proof.
intros E m spv cs lo hi wlo whi regs HR Hsp EA HIn.
rewrite Forall_forall in HIn |- *. intros [off r] Hp. pose proof (HIn _ Hp) as Hin. cbn [fst snd] in Hin |- *.
assert (Hr : 0 <= r < 32) by (unfold oa_saved in Hp; cbn [In] in Hp;
  repeat (destruct Hp as [Hp | Hp]; [injection Hp as <- <-; lia|]); destruct Hp).
replace (spv - 64 + off) with (spv + (off - 64)) by lia. change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2 spv cs lo hi wlo whi (off - 64) 8 (SOff (Z.to_nat r) 0) _ HR Hsp Hin).
- cbn [sv_denot]. rewrite EA by lia. rewrite Z2Nat.id by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HB. change (bv_modulus 64) with (2 ^ 64) in HB.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- lia.
Qed.
Lemma oa_key_ptrs_len : forall ks, Z.of_nat (length (bzs (gestures_end_b_c.key_ptrs ks))) = 8 * Z.of_nat (length ks).
Proof.
intros ks. unfold bzs, gestures_end_b_c.key_ptrs. rewrite length_map.
induction ks as [|k ks IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, Mem.length_le8. cbn [length]. lia.
Qed.
(* every byte an entry's predicate reads lies in one of its blocks *)
Lemma oa_efp_in : forall ly S (W : world SEGS) mem e, aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n.
Proof.
intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr a Ha.
unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | [<- | Hr]].
- revert Hr. destruct (Z.eqb_spec (re_cap e) 0) as [Hc | Hc]; intros Hr; [destruct Hr|].
  destruct Hr as [<- | []]. destruct H10 as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [lia|].
  exists (re_buf e), (re_cap e). split; [exact Hin|]. unfold gfp, bzs in Ha. cbn [fst snd] in Ha.
  rewrite length_map, length_app in Ha. unfold req_size. destruct (Z.eqb_spec (re_cap e) 0); lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. rewrite oa_key_ptrs_len in Ha.
  destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk8 & Hk1 & _)]; [rewrite Hk in Ha; cbn [length] in Ha; lia|].
  exists (re_hp e), (re_kh e). split; [exact Hin|]. unfold re_nheld in Hk8.
  unfold req_size. destruct (Z.eqb_spec (re_kh e) 0); lia.
- apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (Hin & _).
  exists (gestures_end_b_c.key_addr k), (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1). split; [exact Hin|].
  unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
  unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length (gestures_end_b_c.key_text k)) + 1) 0); lia.
Qed.
Lemma oa_eblks_in : forall ly S (W : world SEGS) mem e, aentry_ok B ly S W mem e ->
forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb]; [|apply in_app_or in Hb as [Hb | Hb]].
- revert Hb. destruct (Z.eqb_spec (re_cap e) 0) as [Hc | Hc]; intros Hb; [destruct Hb|].
  destruct Hb as [<- | []]. destruct H10 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
- revert Hb. destruct (Z.eqb_spec (re_hp e) 0) as [Hc | Hc]; intros Hb; [destruct Hb|].
  destruct Hb as [<- | []]. destruct H12 as [(Hz & _) | (_ & Hin & _)]; [lia | exact Hin].
- apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
(* an image byte stays writable, across worlds, when its presence is kept (W_lp_tail.v lpt_writable_img) *)
Lemma oa_writable_img : forall (Wa Wb : world SEGS) (m m' : word -> option byte) a,
in_img SEGS a -> (apresent (w_H Wa) m a -> apresent (w_H Wb) m' a) ->
writable_at SEGS (mrestrict (w_H Wa) m) a -> writable_at SEGS (mrestrict (w_H Wb) m') a.
Proof.
intros Wa Wb m m' a Hi Hp Hw.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H Wa (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (HB : w_H Wb (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
unfold writable_at, wview, mrestrict in *. rewrite HA in Hw. rewrite HB.
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj HA (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* an image byte outside the allocator's statics is owned in no allocator state *)
Lemma oa_not_owned : forall ly S Hp (W : world SEGS) m md a, ARx ly S Hp W m md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof. intros ly S Hp W m md a HAR Hi Ho Hao. exact (Ho (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W m md a HAR Hi) Hao)). Qed.
(* the relay as relay_add expects it, carried over a stretch that keeps relay_add's globals (view and writability)
   and every byte of every block live at the start *)
Lemma oa_rel_kept : forall ly S (W : world SEGS) mem ly' S' Hp' (W' : world SEGS) mem' md' T es,
ra_rel B fr_globals ly S W mem T es -> ARx ly' S' Hp' W' mem' md' ->
(forall b, In b (ablocks B ly S) -> In b (ablocks B ly' S')) ->
(forall b n j, In (b, n) (ablocks B ly S) -> 0 <= j < req_size n ->
 aview SEGS (w_H W') mem' (b + j) = aview SEGS (w_H W) mem (b + j)) ->
(forall a, inG (RA_G fr_globals) a -> abyte_kept W mem W' mem' a) ->
ra_rel B fr_globals ly' S' W' mem' T es.
Proof.
intros ly S W mem ly' S' Hp' W' mem' md' T es Hrel HAR' Hin HBK HGK.
assert (Gsrc : forall x, rg_src fr_globals <= x < rg_src fr_globals + 8 -> abyte_kept W mem W' mem' x).
{ intros x Hx. apply HGK. unfold RA_G. apply inG_cons. right. apply inG_cons. right. apply inG_cons. right.
  apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
assert (Gnsrc : forall x, rg_nsrc fr_globals <= x < rg_nsrc fr_globals + 4 -> abyte_kept W mem W' mem' x).
{ intros x Hx. apply HGK. unfold RA_G. apply inG_cons. right. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
assert (Gcap : forall x, rg_capsrc fr_globals <= x < rg_capsrc fr_globals + 4 -> abyte_kept W mem W' mem' x).
{ intros x Hx. apply HGK. unfold RA_G. apply inG_cons. right. apply inG_cons. right. apply inG_cons. left.
  unfold in_zr. cbn [fst snd]. lia. }
assert (KB : forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n -> abyte_kept W mem W' mem' a).
{ intros b n a Hb Ha. split.
  - replace a with (b + (a - b)) by lia. apply (HBK b n (a - b)); [exact Hb | lia].
  - intros _. destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W' mem' md' b n HAR' (Hin _ Hb)) as (_ & _ & _ & _ & Hp & _).
    exact (apresent_writable SEGS _ _ _ (proj1 (Hp a Ha))). }
destruct Hrel as [(HT & Hes & H1 & H2 & H3 & H4 & H5 & H6) | Hat].
- left. split; [exact HT|]. split; [exact Hes|].
  split; [apply (akept_vm W mem); [intros x Hx; apply Gsrc; lia | exact H1]|].
  split; [apply (akept_awr W mem); [exact Gsrc | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply Gnsrc; lia | exact H3]|].
  split; [apply (akept_awr W mem); [exact Gnsrc | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply Gcap; lia | exact H5]|].
  apply (akept_awr W mem); [exact Gcap | exact H6].
- right. pose proof Hat as (_ & _ & _ & _ & _ & _ & _ & HT & _ & HE & _). rewrite Forall_forall in HE.
  apply (arelay_at_kept B fr_globals ly S W mem ly' S' W' mem' T es Hat).
  + intros r Hr x Hx. unfold arelay_fp in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Hx.
    * exact (Gsrc x Hx).
    * exact (Gnsrc x Hx).
    * exact (Gcap x Hx).
    * apply (KB T ATABLE x HT). change (req_size ATABLE) with 896. unfold ATABLE in Hx. lia.
    * apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
      destruct (oa_efp_in ly S W mem e (HE e He) r Hr x Hx) as (b & n & Hb & Hbx). exact (KB b n x Hb Hbx).
  + intros b Hb. apply Hin. destruct Hb as [<- | Hb]; [exact HT|].
    apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
    exact (oa_eblks_in ly S W mem e (HE e He) b Hb).
Qed.
(* ---- the symbolic state at 0x84fa8, seated afresh after the source_reset call ----
   Atoms: 0 .. 31 the registers there (s0 = atom 8 is the slot g_s + 96 i, s4 = atom 20 is g_s, s5 = atom 21 is
   -(SB + 12 i)); 32 .. 39 the caller's ra and s0 .. s6 as the frame holds them (oa_saved order); 40 the shadow
   base SB; 41 g_nfd's value n0.  s3 is the shadow address of the slot's open flag, in the shadow matcher's form.
   The slot region holds the zero words source_reset left that op_add does not write, so their values survive
   the stores (whose window is the slot's first 48 bytes) and the calls. *)
Definition oaf_stack : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
[YP09.mkChunk 56 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0));
 YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 37 0));
 YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
Definition oaf_slot : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 96 0 48
[YP09.mkChunk 8 (CVal 4 (SLit 0)); YP09.mkChunk 12 (CVal 4 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0));
 YP09.mkChunk 24 (CVal 4 (SLit 0)); YP09.mkChunk 28 (CVal 4 (SLit 0)); YP09.mkChunk 32 (CVal 8 (SLit 0));
 YP09.mkChunk 48 (CVal 8 (SLit 0)); YP09.mkChunk 56 (CVal 4 (SLit 0)); YP09.mkChunk 64 (CVal 8 (SLit 0));
 YP09.mkChunk 72 (CVal 4 (SLit 0)); YP09.mkChunk 76 (CVal 4 (SLit 0)); YP09.mkChunk 80 (CVal 8 (SLit 0));
 YP09.mkChunk 88 (CVal 4 (SLit 0)); YP09.mkChunk 92 (CVal 4 (SLit 0))].
Definition oaf_nfd : YP09.region :=
YP09.mkRegion (Some (A_OBJ 29)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 41 0))].
Definition oaf_regions : smem := [oaf_stack; oaf_slot; oaf_nfd].
Definition oaf_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 6129888 6130176 5); (A_OBJ 29, mkAF A_NFD A_NFD 5);
          (40%nat, mkAF SB SB 0); (41%nat, mkAF 0 512 0) ] [] [].
Definition oaf_regs : list sv := sr_set sr_atoms 19%bv (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SRL (SOff 8 4) (SLit 3))).
Definition ss_oaf : sstate := mkSS A_oaf oaf_regs oaf_regions None oaf_facts.
Definition oaf_SH : list shent := [mkSHE 8 0 96].
Definition Bxf : sv := SOff 40 0.
Definition oaf_extra (regs : bvmap 5 word) (n0 : Z) : list word :=
map (fun p => getr regs (Z_to_bv 5 (snd p))) oa_saved ++ map (Z_to_bv 64) [SB; n0].
Lemma oa_regs_ok_set : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hv r'. unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
specialize (Hr r'). unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma oa_le_byte_0 : forall w k, YO0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l. reflexivity. Qed.
(* a word inside the zeros source_reset leaves *)
Lemma oa_zero_vm : forall m a n off (w : nat), garr8 SEGS m a (repeat 0 n) -> 0 <= off ->
off + Z.of_nat w <= Z.of_nat n -> val_mem SEGS m (a + off) w 0.
Proof.
intros m a n off w Hg Ho Hw k Hk.
assert (Hj : (Z.to_nat off + k < length (repeat 0%Z n))%nat) by (rewrite repeat_length; lia).
pose proof (garr8_mbyte SEGS m a (repeat 0%Z n) (Z.to_nat off + k) Hg Hj) as H.
rewrite nth_repeat in H. replace (a + off + Z.of_nat k) with (a + Z.of_nat (Z.to_nat off + k)) by lia.
rewrite H, oa_le_byte_0. reflexivity.
Qed.
Lemma oa_seat : forall (i : nat) W ly S Hp regs mem md ch n0 (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2,
(i < 4)%nat ->
afn_pre_x SEGS B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
asrc_closed W2 mem2 (oa_HA i) -> val_mem SEGS (arm W2 mem2) A_NFD 4 n0 -> awr W2 mem2 A_NFD 4 ->
getr regs2 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs2 8 = Z_to_bv 64 (oa_HA i) ->
getr regs2 19 = Z_to_bv 64 (SB + (oa_HA i + 4) / 8) ->
Forall (fun p => val_mem SEGS (arm W2 mem2) (spZ regs - 64 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) oa_saved ->
st_ok_pi SEGS VAL (Eimg (Ereg regs2 (oaf_extra regs n0))) ss_oaf
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_oaf)) mem2 (seg_rom SEGS)))
/\ sh_ok SEGS Bxf oaf_SH (Eimg (Ereg regs2 (oaf_extra regs n0))) (mrestrict (w_H W2) mem2).
Proof.
intros i W ly S Hp regs mem md ch n0 W2 ly2 S2 Hp2 regs2 mem2 md2 Hi4 HPRE Hal32 Hn0 HZgs HAR2 ACL2 KN NFDW R2 R8 R19 SAVED.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAv : oa_HA i = 6129888 + 96 * Z.of_nat i) by (unfold oa_HA, ASRC, fr_globals, rg_s; lia).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs2 (oaf_extra regs n0))).
assert (EA : forall r, (r < 32)%nat -> ew E r = getr regs2 (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec r 32); [reflexivity | lia]. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (oaf_extra regs n0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 64)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E8 : ew E 8 = Z_to_bv 64 (oa_HA i)) by exact (eq_trans (EA 8%nat ltac:(lia)) R8).
assert (E40 : ew E 40 = Z_to_bv 64 SB) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = Z_to_bv 64 n0) by exact (EX 9%nat ltac:(lia)).
assert (E270 : ew E 270 = Z_to_bv 64 A_NFD)
by (subst E; rewrite <- HNFD; apply (Eimg_img _ (A_OBJ 29)); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (U8 : bv_unsigned (ew E 8) = oa_HA i) by (rewrite E8; apply unsigned_lit_small; lia).
assert (Unfd : bv_unsigned (ew E 270) = A_NFD) by (rewrite E270; apply unsigned_lit_small; unfold A_NFD; lia).
assert (U40 : bv_unsigned (ew E 40) = SB) by (rewrite E40; apply unsigned_lit_small; unfold SB; lia).
assert (U41 : bv_unsigned (ew E 41) = n0) by (rewrite E41; apply unsigned_lit_small; lia).
assert (CK : forall off j r, ew E (32 + j) = getr regs (Z_to_bv 5 r) -> In (off, r) oa_saved ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W2) mem2) (spZ regs - 64) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j r Hew Hin. apply (chunk_ok_val SEGS E _ (spZ regs - 64) off 8 _ (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  - cbn [sv_denot]. rewrite Hew, Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. zside.
  - zside.
  - rewrite Forall_forall in SAVED. replace (spZ regs - 64 + off) with (spZ regs - 64 + fst (off, r)) by reflexivity.
    exact (SAVED (off, r) Hin). }
assert (CZ : forall off (w : N), 0 <= off -> off + Z.of_N w <= 96 -> (Z.of_N w <= 8) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W2) mem2) (oa_HA i) (YP09.mkChunk off (CVal w (SLit 0)))).
{ intros off w Ho Hw Hw8. apply (chunk_ok_val SEGS E _ (oa_HA i) off w _ 0).
  - reflexivity.
  - pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_N w) ltac:(lia) ltac:(lia)). lia.
  - exact Hw8.
  - apply (oa_zero_vm _ _ (Z.to_nat ASRC)); [exact (proj1 ACL2) | lia | unfold ASRC; lia]. }
assert (WS : OA_STK = 16576) by reflexivity.
assert (Hm16 : (spZ regs - 64) mod 16 = 0)
by (replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16).
assert (Hm32 : oa_HA i mod 32 = 0)
by (rewrite HAv; replace (6129888 + 96 * Z.of_nat i) with ((191559 + 3 * Z.of_nat i) * 32) by lia; apply Z_mod_mult).
split.
- unfold ss_oaf, A_oaf. apply pa_entry_st_ok_full.
  + unfold oaf_regs. apply oa_regs_ok_set; [apply regs_ok_Eimg_Ereg|].
    rewrite (oa_sh_den E 40 8 SB (oa_HA i) 4 E40 E8) by (unfold SB; lia). rewrite R19. reflexivity.
  + vm_compute. reflexivity.
  + unfold oaf_regions, oaf_stack, oaf_slot, oaf_nfd.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [exact (CK 56 0%nat 1 (EX 0%nat ltac:(lia)) ltac:(cbn [In oa_saved]; tauto))|].
      constructor; [exact (CK 48 1%nat 8 (EX 1%nat ltac:(lia)) ltac:(cbn [In oa_saved]; tauto))|].
      constructor; [exact (CK 40 2%nat 9 (EX 2%nat ltac:(lia)) ltac:(cbn [In oa_saved]; tauto))|].
      constructor; [exact (CK 32 3%nat 18 (EX 3%nat ltac:(lia)) ltac:(cbn [In oa_saved]; tauto))|].
      constructor; [exact (CK 24 4%nat 19 (EX 4%nat ltac:(lia)) ltac:(cbn [In oa_saved]; tauto))|].
      constructor; [exact (CK 16 5%nat 20 (EX 5%nat ltac:(lia)) ltac:(cbn [In oa_saved]; tauto))|].
      constructor; [exact (CK 8 6%nat 21 (EX 6%nat ltac:(lia)) ltac:(cbn [In oa_saved]; tauto))|].
      constructor; [exact (CK 0 7%nat 22 (EX 7%nat ltac:(lia)) ltac:(cbn [In oa_saved]; tauto))|].
      constructor.
    * rewrite U8. split; [lia|]. split; [lia|].
      split; [intros o Ho; exact (proj2 ACL2 o ltac:(unfold ASRC; lia))|].
      repeat apply Forall_cons; try apply Forall_nil; apply CZ; lia.
    * change (A_OBJ 29) with 270%nat. rewrite Unfd. split; [unfold A_NFD; lia|]. split; [unfold A_NFD; lia|].
      split; [intros o Ho; exact (NFDW o Ho)|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ A_NFD 0 4 (SOff 41 0) n0);
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact KN.
  + apply pairwise_disjoint_of_extents.
    unfold oaf_regions, oaf_stack, oaf_slot, oaf_nfd, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (A_OBJ 29) with 270%nat.
    rewrite Usp, U8, Unfd.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hceil C1 Hstk0 HAv Hi4. clear.
    unfold A_NFD, OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [oaf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (A_OBJ 29) with 270%nat.
    rewrite Usp, U8, Unfd, U40, U41.
    change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end;
    first [exact Hm16 | exact Hm32 | lia | unfold spZ in *; lia | unfold SB; lia | vm_compute; reflexivity].
- unfold sh_ok, oaf_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E Bxf 8 (rg_s fr_globals) (4 * ASRC) (oa_HA i) 0 96).
  + exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 HZgs).
  + unfold U, Bxf. cbn [sv_denot]. rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite HAv. unfold fr_globals, rg_s. lia.
  + rewrite HAv. unfold ASRC, fr_globals, rg_s. lia.
  + intros x Hx. rewrite HAv in Hx. unfold SHADOW_OFF. lia.
Qed.
(* the slot's shadow entry, at any allocator state (the zero shadow of g_s is a law) *)
Lemma oa_shok : forall (i : nat) Ex ly S Hp (W : world SEGS) m md, (i < 4)%nat -> ARx ly S Hp W m md ->
azs B (rg_s fr_globals) (4 * ASRC) -> ew Ex 40 = Z_to_bv 64 SB -> ew Ex 8 = Z_to_bv 64 (oa_HA i) ->
sh_ok SEGS Bxf oaf_SH Ex (mrestrict (w_H W) m).
Proof.
intros i Ex ly S Hp W m md Hi4 HAR HZgs E40 E8.
assert (HAv : oa_HA i = 6129888 + 96 * Z.of_nat i) by (unfold oa_HA, ASRC, fr_globals, rg_s; lia).
unfold sh_ok, oaf_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) m Ex Bxf 8 (rg_s fr_globals) (4 * ASRC) (oa_HA i) 0 96).
- exact (azs_range_addressable_x B ARx LAWS ly S Hp W m md _ _ HAR HZgs).
- unfold U, Bxf. cbn [sv_denot]. rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by lia. reflexivity.
- rewrite HAv. unfold fr_globals, rg_s. lia.
- rewrite HAv. unfold ASRC, fr_globals, rg_s. lia.
- intros x Hx. rewrite HAv in Hx. unfold SHADOW_OFF. lia.
Qed.
(* the new block of an allocator call is disjoint from every block before it (W_lp_tail.v lpt_new_disj) *)
Lemma oa_new_disj : forall ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 lyc Sc res n b m,
ARx ly2 S2 Hp2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] -> In (b, m) (ablocks B lyc Sc) ->
b + req_size m <= res \/ res + req_size n <= b.
Proof.
intros ly2 S2 Hp2 W2 mem2 md2 lyc Sc res n b m HAR2 Ebl Hin. apply in_split in Hin as (l1 & l2 & E1).
pose proof (sep_blocks_pos_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (b, m) (res, n) l1 l2 [] HAR2) as Hd.
rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.
(* relay_add's globals, at fr_globals *)
Lemma oa_ra_g : forall a, inG (RA_G fr_globals) a ->
0x5d8ac0 <= a < 0x5d8ac0 + 12 \/ 0x5d87a0 <= a < 0x5d87a0 + 4 \/ 0x5d8800 <= a < 0x5d8800 + 4 \/
0x5d87c0 <= a < 0x5d87c0 + 8.
Proof.
intros a Ha. unfold RA_G in Ha.
apply inG_cons in Ha as [Ha | Ha]; [left; unfold in_zr, fr_globals, rg_lock in Ha; cbn [fst snd] in Ha; lia|].
apply inG_cons in Ha as [Ha | Ha]; [right; left; unfold in_zr, fr_globals, rg_nsrc in Ha; cbn [fst snd] in Ha; lia|].
apply inG_cons in Ha as [Ha | Ha]; [right; right; left; unfold in_zr, fr_globals, rg_capsrc in Ha; cbn [fst snd] in Ha; lia|].
apply inG_cons in Ha as [Ha | Ha]; [right; right; right; unfold in_zr, fr_globals, rg_src in Ha; cbn [fst snd] in Ha; lia|].
exfalso. exact (inG_nil a Ha).
Qed.
(* the write obligation of a run from the seat: the slot's first 48 bytes and g_nfd are in G *)
Ltac oa_awr2 Usp U8 Unfd HSL HGnfd :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?Usp, ?U8, ?Unfd in Ha;
      first [ lia | right; left; apply HSL; lia | right; left; apply HGnfd; lia ] |]);
  apply awr_ok_x_nil.
(* a run from the seat keeps every byte outside the slot's first 48 bytes and g_nfd (KR, from m0), and every
   present byte (APR, from m0) *)
Ltac oa_kr i m0 HFr KR Usp U8 Unfd :=
  lazymatch type of HFr with frame_of ?Ev ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2) =>
    let rs' := eval vm_compute in rs in change rs with rs' in HFr;
    let K2 := fresh "KR" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (oa_HA i <= a < oa_HA i + 48) -> ~ (A_NFD <= a < A_NFD + 4) ->
      aview SEGS H m2 a = aview SEGS H m0 a);
    [ intros a Ha H1 H2;
      rewrite (aview_kept_out Ev rs' H m1 m2 HFr a Ha);
      [ exact (KR a Ha H1 H2)
      | intros (r & Hin & Hr); cbn [In] in Hin; repeat (destruct Hin as [<- | Hin]); try destruct Hin;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?U8, ?Unfd in Hr; lia ]
    | clear KR; rename K2 into KR ]
  end.
Ltac oa_apr m0 HGr APR :=
  lazymatch type of HGr with mem_grows (mrestrict ?H ?m1) (mrestrict _ ?m2) =>
    let A2 := fresh "APR" in
    assert (A2 : forall a, apresent H m0 a -> apresent H m2 a)
      by (intros a Hpa; exact (apresent_grows _ _ _ a HGr (APR a Hpa)));
    clear APR; rename A2 into APR
  end.

(* the strength-reduced shadow address (g_s + c) >> 3 - s5, with s5 = -(SB + 12 i), named as the shadow of
   slot + c, slot = g_s + 96 i *)
Lemma oa_sh_sub : forall E sb gs (i : Z) c,
ew E 40 = Z_to_bv 64 sb -> ew E 8 = Z_to_bv 64 (gs + 96 * i) -> ew E 20 = Z_to_bv 64 gs ->
ew E 21 = Z_to_bv 64 (- (sb + 12 * i)) -> 0 <= sb < 2 ^ 62 -> 0 <= gs < 2 ^ 61 -> 0 <= i <= 3 -> 0 <= c <= 96 ->
sv_denot E (SAlu ALU_SUB (SAlu ALU_SRL (SOff 20 c) (SLit 3)) (SOff 21 0)) =
sv_denot E (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SRL (SOff 8 c) (SLit 3))).
Proof.
intros E sb gs i c H40 H8 H20 H21 Hsb Hgs Hi Hc.
rewrite (oa_sh_den E 40 8 sb (gs + 96 * i) c H40 H8) by lia.
apply oa_sv_lit. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 20 gs c H20) by lia. rewrite U_SLit, U_SOff, H21, Z.add_0_r, Z_to_bv_unsigned.
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : (gs + 96 * i + c) / 8 = (gs + c) / 8 + 12 * i).
{ replace (gs + 96 * i + c) with (gs + c + (12 * i) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
rewrite Hd. assert (Hq : 0 <= (gs + c) / 8 <= gs + c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite (zcanon_id ((gs + c) / 8)) by (unfold M64; lia).
unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod, Zminus_mod_idemp_r. f_equal. lia.
Qed.
(* From 0x84fa8 (back from source_reset) to the return, for the slot i op_add opens. *)
Lemma oa_tail : forall (i : nat) W ly S Hp regs mem md ch os n0 T es W2 ly2 S2 Hp2 regs2 mem2 md2 k2 (kr : nat),
oa_first os = Some i ->
afn_pre_x SEGS B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 -> count_cid 0 (frames S) < fs_frames 0 ->
0 <= n0 <= 512 -> (length es < 4)%nat -> ~ In (100 + n0) (map re_fd es) ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es -> alock_at fr_globals W mem false -> awake_at fr_globals W mem ->
rom_view SEGS W mem ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX -> mo_ok MT S oa_cost ->
rp_RM RP S2 (3 + kr)%nat -> cnt_ok_pk RP oa_peak (ablocks B ly S) ->
ajournal_gx_x SEGS B PST ARx G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k2 ->
apres_kept B W mem W2 mem2 ->
(forall a, inG G a -> ~ (oa_HA i <= a < oa_HA i + ASRC) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
(forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
(forall b n j, In (b, n) (ablocks B ly S) -> 0 <= j < req_size n ->
 aview SEGS (w_H W2) mem2 (b + j) = aview SEGS (w_H W) mem (b + j)) ->
Permutation (ablocks B ly2 S2) (ablocks B ly S) -> frames S2 = frames S -> mo_le MT S S2 (sr_cost MT None) ->
asrc_closed W2 mem2 (oa_HA i) ->
val_mem SEGS (arm W2 mem2) A_NFD 4 n0 -> awr W2 mem2 A_NFD 4 ->
getr regs2 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
getr regs2 8 = Z_to_bv 64 (oa_HA i) -> getr regs2 19 = Z_to_bv 64 (SB + (oa_HA i + 4) / 8) ->
getr regs2 20 = Z_to_bv 64 (rg_s fr_globals) -> getr regs2 21 = Z_to_bv 64 (- (SB + 12 * Z.of_nat i)) ->
getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 -> getr regs2 25 = getr regs 25 ->
getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 ->
Forall (fun p => val_mem SEGS (arm W2 mem2) (spZ regs - 64 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) oa_saved ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_oaf)) mem2 (seg_rom SEGS)) md2)
  (oa_post_x regs ly S Hp W mem md os n0 T es kr).
Proof.
intros i W ly S Hp regs mem md ch os n0 T es W2 ly2 S2 Hp2 regs2 mem2 md2 k2 kr Hfirst HPRE Hal32 Hcid Hn0 Hes4 Hfd HZgs
HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hlive Hmok HRM2 HCNT HJ AP GK2 WK2 ERR2 BK2 HP2 Hfr2 Hmle2 ACL2 KN NFDW
R2 R3 R4 R8 R19 R20 R21 R23 R24 R25 R26 R27 SAVED.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : OA_STK = 16576) by reflexivity.
assert (Hi4 : (i < 4)%nat).
{ unfold oa_first in Hfirst.
  destruct (nth 0 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 1 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 2 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 3 os 0 =? 0); [injection Hfirst as <-; lia | discriminate]. }
assert (HAv : oa_HA i = 6129888 + 96 * Z.of_nat i) by (unfold oa_HA, ASRC, fr_globals, rg_s; lia).
assert (HSL : forall a, oa_HA i <= a < oa_HA i + 96 -> inG G a)
by (intros a Ha; apply HGgs; rewrite HAv in Ha; unfold ASRC, fr_globals, rg_s; lia).
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k2 HJ) as HAR2.
destruct (oa_seat i W ly S Hp regs mem md ch n0 W2 ly2 S2 Hp2 regs2 mem2 md2 Hi4 HPRE Hal32 Hn0 HZgs HAR2 ACL2 KN NFDW
  R2 R8 R19 SAVED) as [HS SHOK].
remember (Eimg (Ereg regs2 (oaf_extra regs n0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall r, (r < 32)%nat -> ew E r = getr regs2 (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec r 32); [reflexivity | lia]. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (oaf_extra regs n0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E270 : ew E 270 = Z_to_bv 64 A_NFD)
by (subst E; rewrite <- HNFD; apply (Eimg_img _ (A_OBJ 29)); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E372 : ew E 372 = Z_to_bv 64 (VAL (A_HI 92))).
{ rewrite <- (HEI (A_HI 92) ltac:(unfold A_TEXT, A_LIM, A_HI; lia)). rewrite Z_to_bv_bv_unsigned. reflexivity. }
clear HE.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 64)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E8 : ew E 8 = Z_to_bv 64 (oa_HA i)) by exact (eq_trans (EA 8%nat ltac:(lia)) R8).
assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_globals)) by exact (eq_trans (EA 20%nat ltac:(lia)) R20).
assert (E21 : ew E 21 = Z_to_bv 64 (- (SB + 12 * Z.of_nat i))) by exact (eq_trans (EA 21%nat ltac:(lia)) R21).
assert (E40 : ew E 40 = Z_to_bv 64 SB) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = Z_to_bv 64 n0) by exact (EX 9%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (U8 : bv_unsigned (ew E 8) = oa_HA i) by (rewrite E8; apply unsigned_lit_small; lia).
assert (Unfd : bv_unsigned (ew E 270) = A_NFD) by (rewrite E270; apply unsigned_lit_small; unfold A_NFD; lia).
unfold A_oaf, A_op_add.
(* R1a: 0x84fa8 .. the store of g_nfd + 1, through the auipc the listing does not name *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr2 Usp U8 Unfd HSL HGnfd. }
rename HFr into HFr1a, HG0 into HGr1a. clear HF.
oa_setsv HS (11%bv : bv 5) (SOff 270 1928)
  ltac:(apply U_inj;
        rewrite (U_atom_off E 270 A_NFD 1928 E270) by (unfold A_NFD; lia);
        rewrite (U_atom E 372 (VAL (A_HI 92)) E372) by (pose proof (pa_val_range (A_HI 92)); lia);
        exact HHI92).
(* R1b: the store of g_nfd + 1, then s6 = (g_s >> 3) - s5 *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr2 Usp U8 Unfd HSL HGnfd. }
rename HFr into HFr1b, HG0 into HGr1b. clear HF.
oa_setsv HS (22%bv : bv 5) (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SRL (SOff 8 0) (SLit 3)))
  ltac:(rewrite HAv in E8; exact (oa_sh_sub E SB (rg_s fr_globals) (Z.of_nat i) 0 E40 E8 E20 E21
          ltac:(unfold SB; lia) ltac:(unfold fr_globals, rg_s; lia) ltac:(lia) ltac:(lia))).
(* R1c: the store of the descriptor 100 + n0 into the slot, malloc (6000) *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr2 Usp U8 Unfd HSL HGnfd. }
rename HFr into HFr1c, HG0 into HGr1c. clear HF.
(* the three runs wrote nothing but the slot's first 48 bytes and g_nfd, and kept every present byte *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (oa_HA i <= a < oa_HA i + 48) -> ~ (A_NFD <= a < A_NFD + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by reflexivity.
assert (APR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros a Ha; exact Ha).
oa_kr i mem2 HFr1a KR Usp U8 Unfd. oa_kr i mem2 HFr1b KR Usp U8 Unfd. oa_kr i mem2 HFr1c KR Usp U8 Unfd.
oa_apr mem2 HGr1a APR. oa_apr mem2 HGr1b APR. oa_apr mem2 HGr1c APR.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => let x := fresh "msA" in rename mm into x end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (Usp1 : spZ (ms_regs msA) = spZ regs - 64) by (unfold spZ; rewrite Q2; exact Usp).
assert (GOK : forall a, inG G a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ 0 <= a < kLowMemEnd).
{ intros a Ha. destruct (HG a Ha) as (Him & Hno & _). destruct (HGRT a Ha) as [He _].
  pose proof (Hsegs a Him). split; [exact Him|]. split; [exact Hno|]. split; [exact He | lia]. }
assert (Hbb2 : blocks_bytes S2 = blocks_bytes S)
by (rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S); exact (bsum_perm _ _ HP2)).
pose proof HJ as HJ2k.
destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
(* malloc (6000) *)
eapply SRr_bind.
{ rewrite (pal_malloc B TL).
  eapply (AMA W2 (ms_regs msA) (ms_mem msA) OA_STK (spZ regs) (ra_FP T es) ly S Hp W memS md [] ly2 S2 Hp2 _ k2
    APARTIAL (-64) _ [] (2 + kr)%nat HJi).
  - rewrite Q10. reflexivity.
  - unfold APARTIAL in *. lia.
  - rewrite Hbb2. unfold APARTIAL, ATABLE in *. lia.
  - (* the room round: malloc's count at S2, whose blocks are the entry's (HP2) *)
    exact (oa_cnt_perm (fun _ => 0%nat) _ _ HP2 ltac:(intros P; cbv beta; lia) HCNT).
  - rewrite Usp1. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ASTACK. lia.
  - (* the room round: the allocator's stack room below the call, from the journal's astk_ok *)
    exact (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-64) (ms_regs msA) HJi
      ltac:(rewrite Usp1; lia) ltac:(rewrite WS; unfold ASTACK; lia)).
  - rewrite Q3. exact (eq_trans (EA 3%nat ltac:(lia)) (eq_trans R3 Hgp)).
  - rewrite Q4. exact (eq_trans (EA 4%nat ltac:(lia)) (eq_trans R4 Htp)).
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre ly2 _ (spZ regs - 64) (oa_HA i) [] (ms_regs msA)).
    + apply achain_low. rewrite HAv. lia.
    + rewrite Usp1. unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK in *. lia.
    + unfold s0Z. rewrite Q8. exact U8.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - (* malloc's caller context: the chain is [] (s0 holds the slot, an image address), so the trace is the one return
       address op_add + 0xcc (HCTX_oa_malloc) *)
    cbn [spine map]. replace (raZ (ms_regs msA)) with (BASE + AF_fr_op_add + 0xcc); [exact HCTX_oa_malloc|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    first [lia | (unfold AF_fr_op_add in *; lia) |
           (idtac "MCTX-RA"; match goal with |- ?g => idtac g end; fail)].
  - (* the room round: malloc charges 1 of the 3 left after source_reset *)
    exact HRM2.
  - apply (mok_station MT S S2 oa_cost (sr_cost MT None) _ MLAW Hmok Hmle2).
    + apply (mo_malloc_nonneg MT MLAW). unfold APARTIAL. lia.
    + unfold oa_cost. pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia)).
      pose proof (mo_free_nonneg MT MLAW). lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & q & -> & HJ3i & HP3 & Hq10 & Hfr3 & Hq4096 & Hbl3 &
  Hkept3 & Hmle3 & HRM3 & Herr3 & Hpres3).
pose proof (proj1 HJ3i) as HAR3.
assert (Hqn : In (q, APARTIAL) (ablocks B ly3 S3)) by (rewrite Hbl3; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 _ _ HAR3 Hqn) as (Hq16 & _ & Hqceil & Hqapp & Hqpres & _).
change (req_size APARTIAL) with 6000 in Hqceil, Hqapp, Hqpres.
(* back in op_add: the frame, the slot and g_nfd are image or stack bytes malloc keeps *)
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U8, ?Unfd.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 Hkept3); rewrite ?Usp1; unfold ASTACK in *; lia.
  - intros a Ha. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GOK a (HSL a ltac:(lia))) as (Him & Hno & He & _).
    exact (proj1 (proj2 (proj2 Hkept3)) a Him Hno He).
  - intros a Ha _. apply HGW. apply HSL. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GOK a (HGnfd a ltac:(lia))) as (Him & Hno & He & _).
    exact (proj1 (proj2 (proj2 Hkept3)) a Him Hno He).
  - intros a Ha _. apply HGW. apply HGnfd. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HIa : forall m, (64 <= m)%nat -> ew Ea m = ew E m)
by (intros m Hm; rewrite HEa; apply ew_havoc_above; cbn [length map CLOB]; lia).
assert (Ea52 : ew Ea 52 = w64 q) by (rewrite HEa; exact Hq10).
clear HEa.
assert (HFa : afact_ok Ea 52 (mkAF 4096 0x7fffff800000 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ea52. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite Hq16. lia. }
pose proof (st_ok_pi_add_fact Ea _ _ 52%nat _ HS HFa) as HSa. clear HS HFa. rename HSa into HS.
assert (HJ3 : ajournal_gx_x SEGS B PST ARx G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly3 S3 Hp3 W3 mem3 md3 (k2 + 1)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly3 S3 Hp3 W3 mem3 md3 (k2 + 1) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ3i | exact HAG | apply out_none]. }
assert (SHOKa : sh_ok SEGS Bxf oaf_SH Ea (mrestrict (w_H W3) mem3))
by (apply (oa_shok i Ea ly3 S3 Hp3 W3 mem3 md3 Hi4 HAR3 HZgs); rewrite OLDa by lia; [exact E40 | exact E8]).
assert (Usp3 : bv_unsigned (ew Ea 2) = spZ regs - 64) by (rewrite OLDa by lia; exact Usp).
assert (U83 : bv_unsigned (ew Ea 8) = oa_HA i) by (rewrite OLDa by lia; exact U8).
assert (Unfd3 : bv_unsigned (ew Ea 270) = A_NFD) by (rewrite HIa by lia; exact Unfd).
(* R2a: s4 + 40, its shadow (g_s + 40) >> 3 - s5 *)
paj_run_tok_x RUN HS HJ3 SHOKa Bspan. { oa_awr2 Usp3 U83 Unfd3 HSL HGnfd. }
rename HFr into HFr2a, HG0 into HGr2a. clear HF.
assert (F40 : ew Ea 40 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E40).
assert (F8 : ew Ea 8 = Z_to_bv 64 (oa_HA i)) by (rewrite OLDa by lia; exact E8).
assert (F20 : ew Ea 20 = Z_to_bv 64 (rg_s fr_globals)) by (rewrite OLDa by lia; exact E20).
assert (F21 : ew Ea 21 = Z_to_bv 64 (- (SB + 12 * Z.of_nat i))) by (rewrite OLDa by lia; exact E21).
assert (F41 : ew Ea 41 = Z_to_bv 64 n0) by (rewrite OLDa by lia; exact E41).
oa_setsv HS (12%bv : bv 5) (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SRL (SOff 8 40) (SLit 3)))
  ltac:(rewrite HAv in F8; exact (oa_sh_sub Ea SB (rg_s fr_globals) (Z.of_nat i) 40 F40 F8 F20 F21
          ltac:(unfold SB; lia) ltac:(unfold fr_globals, rg_s; lia) ltac:(lia) ltac:(lia))).
(* R2b: the partial buffer into the slot, the open flag, the descriptor reloaded, the jal to relay_add *)
paj_run_to_tok_x RUNTO HS HJ3 SHOKa Bspan AF_fr_relay_add. { oa_awr2 Usp3 U83 Unfd3 HSL HGnfd. }
rename HFr into HFr2b, HG0 into HGr2b. clear HF.
(* the two runs after malloc kept everything outside the slot's first 48 bytes and g_nfd *)
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (oa_HA i <= a < oa_HA i + 48) -> ~ (A_NFD <= a < A_NFD + 4) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W3) mem3 a) by reflexivity.
assert (APR3 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem3 a) by (intros a Ha; exact Ha).
oa_kr i mem3 HFr2a KR3 Usp3 U83 Unfd3. oa_kr i mem3 HFr2b KR3 Usp3 U83 Unfd3.
oa_apr mem3 HGr2a APR3. oa_apr mem3 HGr2b APR3.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => let x := fresh "msB" in rename mm into x end.
repeat rewrite wvb_collapse in HJ3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdl) _ => remember mdl as mdB in * end.
(* the slot and g_nfd as relay_add finds them *)
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RSL.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RNF.
cbn [ms_mem restrict] in RSL, RNF.
assert (VF0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + 0) (N.to_nat 4) (100 + n0)).
{ eapply (field_of_region Ea _ 8 (oa_HA i));
  [exact RSL | exact U83 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite F41, unsigned_lit_small by lia. f_equal. lia. }
assert (VF4 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + 4) (N.to_nat 4) 1).
{ eapply (field_of_region Ea _ 8 (oa_HA i));
  [exact RSL | exact U83 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  reflexivity. }
assert (VF40 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + 40) (N.to_nat 8) q).
{ eapply (field_of_region Ea _ 8 (oa_HA i));
  [exact RSL | exact U83 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite Ea52. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VZ : Forall (fun p => val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + fst p) (snd p) 0)
  [(8,4%nat);(12,4%nat);(16,8%nat);(24,4%nat);(28,4%nat);(32,8%nat);(48,8%nat);(56,4%nat);(64,8%nat);(72,4%nat);
   (76,4%nat);(80,8%nat);(88,4%nat);(92,4%nat)]).
{ repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  lazymatch goal with
  | |- val_mem _ _ _ 4%nat _ => change 4%nat with (N.to_nat 4)
  | |- val_mem _ _ _ 8%nat _ => change 8%nat with (N.to_nat 8)
  end;
  (eapply (field_of_region Ea _ 8 (oa_HA i));
   [exact RSL | exact U83 | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]). }
assert (VN : val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (A_NFD + 0) (N.to_nat 4) (n0 + 1)).
{ eapply (field_of_region Ea _ 270 A_NFD); [exact RNF | exact Unfd3 | cbn [In]; left; reflexivity | | zside | zside].
  cbn [sv_denot]. rewrite F41, unsigned_lit_small by lia. reflexivity. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (Usp4 : spZ (ms_regs msB) = spZ regs - 64) by (unfold spZ; rewrite P2; exact Usp3).
pose proof (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARB.
pose proof HJ3 as (_ & _ & (memSB & HJiB & _) & _). rewrite !Z.add_0_r in HJiB.
pose proof HJiB as (_ & HLYB & _ & _ & _ & HFRB & _ & _ & _ & _ & _ & _ & _ & HPRB & _ & _ & HQTB).
destruct HLYB as (_ & _ & _ & _ & _ & _ & _ & _ & LYtop & LYlo & LYhi & _).
cbn [app] in HFRB.
(* what the stretch from op_add's entry to the call kept *)
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (oa_HA i <= a < oa_HA i + 48) -> ~ (A_NFD <= a < A_NFD + 4) ->
  aview SEGS (w_H W3) (ms_mem msB) a = aview SEGS (w_H W2) mem2 a).
{ intros a Him Hno He Hs Hn. pose proof (Hsegs a Him) as Hlo. unfold kLowMemEnd in Hlo.
  rewrite (KR3 a ltac:(lia) Hs Hn). rewrite (proj1 (proj2 (proj2 Hkept3)) a Him Hno He).
  exact (KR a ltac:(lia) Hs Hn). }
assert (KG3 : forall a, inG G a -> ~ (oa_HA i <= a < oa_HA i + ASRC) -> ~ (A_NFD <= a < A_NFD + 4) ->
  aview SEGS (w_H W3) (ms_mem msB) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hs Hn. destruct (GOK a Ha) as (Him & Hno & He & _).
  rewrite (KIMG a Him Hno He ltac:(unfold ASRC in Hs; lia) Hn). exact (GK2 a Ha Hs). }
assert (KW3 : forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
  aview SEGS (w_H W3) (ms_mem msB) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (HWK a Ha) as (Him & Hno & He).
  rewrite (KIMG a Him Hno He) by (rewrite ?HAv; unfold fr_globals, rg_wake, A_NFD in *; lia). exact (WK2 a Ha). }
assert (APIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> apresent (w_H W) mem a -> apresent (w_H W3) (ms_mem msB) a).
{ intros a Him Hno He Hpa. apply APR3.
  apply (Hpres3 a Him (oa_not_owned _ _ _ _ _ _ a (proj1 HJi) Him Hno) (oa_not_owned _ _ _ _ _ _ a HAR3 Him Hno) He).
  - intros Hb. exact (blk_img_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 q APARTIAL a HAR3 Hqn Hb Him).
  - apply APR. exact (AP a Him Hno He Hpa). }
assert (KBLK : forall b n j, In (b, n) (ablocks B ly S) -> 0 <= j < req_size n ->
  aview SEGS (w_H W3) (ms_mem msB) (b + j) = aview SEGS (w_H W) mem (b + j)).
{ intros b n j Hb Hj.
  assert (Hni : ~ in_img SEGS (b + j)) by exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b n (b + j) HAR Hb ltac:(lia)).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hb) as (_ & H4096 & Hbc & _).
  assert (Hns : ~ (oa_HA i <= b + j < oa_HA i + 48))
  by (intros Hs; apply Hni; exact (proj1 (GOK (b + j) (HSL (b + j) ltac:(lia))))).
  assert (Hnn : ~ (A_NFD <= b + j < A_NFD + 4)) by (intros Hs; apply Hni; exact (proj1 (GOK _ (HGnfd _ Hs)))).
  assert (Hb2 : In (b, n) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HP2) Hb).
  pose proof (oa_new_disj ly3 S3 Hp3 W3 mem3 md3 ly2 S2 q APARTIAL b n HAR3 Hbl3 Hb2) as Hd.
  change (req_size APARTIAL) with 6000 in Hd.
  rewrite (KR3 (b + j) ltac:(lia) Hns Hnn).
  rewrite (proj1 (proj2 Hkept3) b n j Hb2 Hj ltac:(cbv beta; change (req_size APARTIAL) with 6000; lia)).
  rewrite (KR (b + j) ltac:(lia) Hns Hnn).
  exact (BK2 b n j Hb Hj). }
assert (KRAG : forall a, inG (RA_G fr_globals) a -> abyte_kept W mem W3 (ms_mem msB) a).
{ intros a Ha. pose proof (oa_ra_g a Ha) as Hr. split.
  - apply KG3; [exact (HGra a Ha) | rewrite HAv; unfold ASRC; lia | unfold A_NFD; lia].
  - intros _. exact (HGW a (HGra a Ha) _). }
(* relay_add's premises at the call *)
assert (Hrel3 : ra_rel B fr_globals ly3 S3 W3 (ms_mem msB) T es).
{ apply (oa_rel_kept ly S W mem ly3 S3 Hp3 W3 (ms_mem msB) mdB T es Hrel HARB); [|exact KBLK | exact KRAG].
  intros b Hb. rewrite Hbl3. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym HP2) Hb). }
assert (Hlock3 : alock_at fr_globals W3 (ms_mem msB) false).
{ apply (alock_at_kept fr_globals W mem W3 (ms_mem msB) false Hlock).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha. apply KRAG.
  unfold RA_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
assert (Hwake3 : awake_at fr_globals W3 (ms_mem msB)).
{ apply (awake_at_kept fr_globals W mem W3 (ms_mem msB) Hwake).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha. destruct (HWK a Ha) as (Him & Hno & He).
  split; [exact (KW3 a Ha)|]. intros Hw.
  exact (oa_writable_img W W3 mem (ms_mem msB) a Him (APIMG a Him Hno He) Hw). }
assert (Hrom3 : rom_view SEGS W3 (ms_mem msB))
by (eapply ajournal_gx_rom_view_x; first [exact Hsegs | exact LAWS | exact HJ3 | exact HRO | exact oa_pstr | exact Hrom]).
assert (Hbb3 : blocks_bytes S3 = blocks_bytes S + APARTIAL).
{ rewrite (blocks_bytes_bsum B ly3 S3), Hbl3, bsum_app, <- (blocks_bytes_bsum B ly2 S2), Hbb2. reflexivity. }
assert (Hmle23 : mo_le MT S S3 (sr_cost MT None + mo_malloc MT APARTIAL))
by exact (mle_station MT S S2 S3 _ _ MLAW Hmle2 Hmle3).
assert (Hmok3 : mo_ok MT S3 (ra_cost MT T)).
{ pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia)) as M1. pose proof (mo_free_nonneg MT MLAW) as M2.
  apply (mok_station MT S S3 oa_cost _ _ MLAW Hmok Hmle23); unfold ra_cost, oa_cost; destruct (T =? 0); lia. }
assert (HGra_ok : gx_ok SEGS B (RA_G fr_globals)) by exact (gx_ok_sub SEGS B _ G HGra HG).
assert (HGra_rt : gx_rt B (RA_G fr_globals)) by exact (gx_rt_sub B _ G HGra HGRT).
assert (HPREra : afn_pre_x SEGS B ARx RA_STK ly3 S3 Hp3 W3 (ms_regs msB) (ms_mem msB) mdB []).
{ split; [exact HARB|].
  split; [rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]|].
  split; [unfold raZ; rewrite P1, unsigned_lit_small by lia; lia|].
  split; [rewrite P3; exact (eq_trans (OLDa 3%nat ltac:(lia)) (eq_trans (EA 3%nat ltac:(lia)) (eq_trans R3 Hgp)))|].
  split; [rewrite P4; exact (eq_trans (OLDa 4%nat ltac:(lia)) (eq_trans (EA 4%nat ltac:(lia)) (eq_trans R4 Htp)))|].
  split.
  { rewrite Usp4. unfold astk_ok, ly_bot in *. rewrite LYtop, LYlo, LYhi.
    unfold RA_STK, RA_FRAME, OA_STK, OA_FRAME, ASTACK in *.
    split; [replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
    repeat split; lia. }
  split.
  { intros a Ha. apply HPRB. rewrite Usp4 in Ha. unfold RA_STK, RA_FRAME, OA_STK, OA_FRAME, ASTACK in *. lia. }
  split; [|exact HQTB].
  apply achain_low. unfold s0Z. rewrite P8, U83, HAv. lia. }
(* relay_add (100 + n0) *)
(* relay_add's caller-context conjunct: room above relay_add's sp (op_add's frame is 64 bytes below op_add's sp,
   which is below the stack top), and the trace [relay_add + 332; op_add + 264] (HCTXRA), the chain being [] *)
assert (HRACTX : 0 <= 100 + n0 -> T = 0 ->
  spZ (ms_regs msB) + 16 < ly_top ly3 /\
  In (BASE + AF_fr_relay_add + 332 :: raZ (ms_regs msB) :: spine []) CTX_R).
{ intros _ _. split.
  - rewrite Usp4. unfold astk_ok, ly_bot in *. rewrite ?LYtop. unfold OA_STK, OA_FRAME, ASTACK in *.
    first [lia | (idtac "RACTX-ROOM"; match goal with |- ?g => idtac g end; fail)].
  - cbn [spine map]. replace (raZ (ms_regs msB)) with (BASE + AF_fr_op_add + 264); [exact HCTXRA|].
    unfold raZ. rewrite P1, unsigned_lit_small by lia.
    first [lia | (unfold AF_fr_op_add in *; lia) |
           (idtac "RACTX-RA"; match goal with |- ?g => idtac g end; fail)]. }
eapply SRr_bind.
{ exact (RA (RA_G fr_globals) HGra_ok HGra_rt W3 ly3 S3 Hp3 (ms_regs msB) (ms_mem msB) mdB [] (100 + n0) T es HPREra
    ltac:(rewrite Usp4; replace (spZ regs - 64) with (spZ regs + (-2) * 32) by lia; rewrite Z_mod_plus_full; exact Hal32)
    ltac:(rewrite Hfr3, Hfr2; exact Hcid)
    ltac:(rewrite P10, F41, unsigned_lit_small by lia; f_equal; lia)
    ltac:(lia) Hlock3 Hwake3 Hrom3 Hrel3
    ltac:(intros _; split; [exact Hes4 | exact Hfd])
    ltac:(intros a Ha; exact Ha)
    ltac:(intros a Ha; exact (proj1 (HGRT a (HGra a Ha))))
    ltac:(intros _ _; rewrite Hbb3; unfold APARTIAL, ATABLE in *; lia)
    HRACTX
    Hmok3 kr
    (* the room round: relay_add charges ra_cost MT_rk T (2 when the table is new, else 0) of the 2 left after malloc;
       its count at S3 is the entry's plus the slot's APARTIAL block (Hbl3, HP2) *)
    (RMM S3 (Z.to_nat (ra_cost MT_rk T) + kr)%nat (2 + kr)%nat ltac:(unfold ra_cost; destruct (T =? 0); cbv; lia) HRM3)
    ltac:(rewrite Hbl3; exact (oa_cnt_ra _ _ q T HP2 HCNT))). }
cbv beta. intros W4 c4 Hwle4
  (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & -> & HJ4 & HP4 & AP4 & Hfr4 & Hmle4 & HRM4 & Hlock4 & Hcases & Herr4).
destruct Hcases as [(Hneg & _) | (_ & Hr10 & T' & Hrelay4 & HTc)]; [lia|].
(* the table relay_add used, when it existed, is a live block at the call (so T is no address 0 and the entry it
   writes lies in it) *)
assert (HTb : T <> 0 -> In (T, ATABLE) (ablocks B ly3 S3)).
{ intros HT0. destruct Hrel3 as [(HT & _) | Hat3]; [lia|].
  pose proof Hat3 as (_ & _ & _ & _ & _ & _ & _ & HTB & _). exact HTB. }
assert (Hsk : ~ YI16.sink_open_fp (ra_FP T es)).
{ unfold YI16.sink_open_fp, YI16.in_fp, ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0].
  - intros (r & [] & _).
  - destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 (ms_mem msB) mdB T ATABLE HARB (HTb HT0)) as (_ & HT4096 & _).
    intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold AENT in Hr. lia. }
(* back in op_add after relay_add: only the frame is read from here on *)
jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp3.
  - intros a Ha. apply (mbyte_of_aview SEGS).
    apply (oa_call_keep_hi (RA_G fr_globals) RA_STK (spZ (ms_regs msB)) _ ly3 S3 Hp3 W3 (ms_mem msB) mdB ly4 S4 Hp4 W4 mem4 md4 k4
      HGra_ok HJ4); rewrite ?Usp4; unfold RA_STK, RA_FRAME, ASTACK, OA_STK, OA_FRAME in *; lia.
  - intros a Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc Ea 64 (map (getr regs4) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 64)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (Eb68 : ew Eb 68 = w64 0) by (rewrite HEb; exact Hr10).
clear HEb.
assert (HFb : afact_ok Eb 68 (mkAF 0 0 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Eb68. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_pi_add_fact Eb _ _ 68%nat _ HS HFb) as HSb. clear HS HFb. rename HSb into HS.
(* the journal through relay_add, at op_add's G *)
assert (HFP : forall a, inFP (ra_FP T es) a ->
  (inFP (ra_FP T es) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly3 S3) a).
{ intros a Ha. left. split; [exact Ha|]. revert Ha. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0].
  - intros (r & [] & _).
  - intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. exists T, ATABLE. split; [exact (HTb HT0)|].
    change (req_size ATABLE) with 896. unfold AENT in Hr. lia. }
assert (HJ5 : ajournal_gx_x SEGS B PST ARx G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md ([] ++ []) ly4 S4 Hp4 W4 mem4 md4
  (k2 + 1 + k4)).
{ eapply ajournal_gx_sub_x;
  first [ exact LAWS | exact Hsegs | exact HJ3 | exact HG | exact HFP
        | (eapply ajournal_gx_G_mono_x; [exact HGra | exact HJ4])
        | (intros a (r & Hin & _); destruct Hin)
        | (rewrite Usp4; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK; lia) ]. }
cbn [app] in HJ5.
pose proof (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HAR4.
assert (SHOKb : sh_ok SEGS Bxf oaf_SH Eb (mrestrict (w_H W4) mem4))
by (apply (oa_shok i Eb ly4 S4 Hp4 W4 mem4 md4 Hi4 HAR4 HZgs); rewrite OLDb, OLDa by lia; [exact E40 | exact E8]).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs - 64) by (rewrite OLDb by lia; exact Usp3).
(* R3: a0 = 0, the epilogue, the ret *)
rewrite P1.
psrr_branch_tok RUN BR HS SHOKb Bspan.
{ (* bnez a0 -> abort: relay_add returned 0 *)
  exfalso. rewrite ?branch_ne_U, ?branch_eq_U in Hc. rewrite ?(U_atom Eb 68 0 Eb68) in Hc by lia.
  rewrite ?U_SLit in Hc. change (zcanon 0) with 0 in Hc. discriminate Hc. }
paj_run_tok_x RUN HS HJ5 SHOKb Bspan. { oa_awr2 Uspb U83 Unfd3 HSL HGnfd. }
rename HFr into HFr3, HG0 into HGr3. clear HF.
pose proof (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HARF.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => let x := fresh "msF" in rename mm into x end.
assert (KF : forall a, aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W4) mem4 a).
{ lazymatch type of HFr3 with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr3 end.
  intros a. apply aview_eq_of. apply HFr3. intros (r & Hin & Hr). cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]); try destruct Hin; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
prreg HS (1%bv : bv 5) X1. prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
prreg HS (8%bv : bv 5) X8. prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19.
prreg HS (20%bv : bv 5) X20. prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (23%bv : bv 5) X23.
prreg HS (24%bv : bv 5) X24. prreg HS (25%bv : bv 5) X25. prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
assert (OLDE : forall m, (m < 48)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
assert (EX32 : ew E 32 = getr regs 1) by exact (EX 0%nat ltac:(lia)).
eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matf. unfold oa_post_x, oa_FP. rewrite Hfirst.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists ly4, S4, Hp4, r, m, d, (k2 + 1 + k4) end.
split; [cbn [ms_regs]; rewrite X1, OLDE, EX32 by lia; rewrite Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ5|].
split.
{ apply aregs_preserved_eqs.
  - rewrite X2, Uspb. replace (spZ regs - 64 + 64) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite X3. exact (eq_trans (OLDE 3%nat ltac:(lia)) (eq_trans (EA 3%nat ltac:(lia)) R3)).
  - rewrite X4. exact (eq_trans (OLDE 4%nat ltac:(lia)) (eq_trans (EA 4%nat ltac:(lia)) R4)).
  - rewrite X8. exact (eq_trans (OLDE 33%nat ltac:(lia)) (EX 1%nat ltac:(lia))).
  - rewrite X9. exact (eq_trans (OLDE 34%nat ltac:(lia)) (EX 2%nat ltac:(lia))).
  - rewrite X18. exact (eq_trans (OLDE 35%nat ltac:(lia)) (EX 3%nat ltac:(lia))).
  - rewrite X19. exact (eq_trans (OLDE 36%nat ltac:(lia)) (EX 4%nat ltac:(lia))).
  - rewrite X20. exact (eq_trans (OLDE 37%nat ltac:(lia)) (EX 5%nat ltac:(lia))).
  - rewrite X21. exact (eq_trans (OLDE 38%nat ltac:(lia)) (EX 6%nat ltac:(lia))).
  - rewrite X22. exact (eq_trans (OLDE 39%nat ltac:(lia)) (EX 7%nat ltac:(lia))).
  - rewrite X23. exact (eq_trans (OLDE 23%nat ltac:(lia)) (eq_trans (EA 23%nat ltac:(lia)) R23)).
  - rewrite X24. exact (eq_trans (OLDE 24%nat ltac:(lia)) (eq_trans (EA 24%nat ltac:(lia)) R24)).
  - rewrite X25. exact (eq_trans (OLDE 25%nat ltac:(lia)) (eq_trans (EA 25%nat ltac:(lia)) R25)).
  - rewrite X26. exact (eq_trans (OLDE 26%nat ltac:(lia)) (eq_trans (EA 26%nat ltac:(lia)) R26)).
  - rewrite X27. exact (eq_trans (OLDE 27%nat ltac:(lia)) (eq_trans (EA 27%nat ltac:(lia)) R27)). }
split.
{ intros a H1 H2 H3 H4. apply (apresent_grows _ _ _ a HGr3). exact (AP4 a H1 H2 H3 (APIMG a H1 H2 H3 H4)). }
(* what relay_add and the epilogue keep, from the call on *)
assert (KRA : forall a, in_img SEGS a -> ~ inG (RA_G fr_globals) a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem msB) a).
{ intros a Him HnG Hno He. rewrite KF.
  exact (oa_call_keep (RA_G fr_globals) RA_STK (spZ (ms_regs msB)) (ra_FP T es) ly3 S3 Hp3 W3 (ms_mem msB) mdB
    ly4 S4 Hp4 W4 mem4 md4 k4 HJ4 Hsk a Him HnG Hno He). }
split.
{ unfold oa_kept, oa_wr. rewrite Hfirst. intros a Ha Hno. destruct (GOK a Ha) as (Him & Hnos & He & _).
  rewrite (KRA a Him ltac:(intros Hr; apply Hno; right; right; exact Hr) Hnos He).
  apply KG3; [exact Ha | intros Hs; apply Hno; left; exact Hs | intros Hn; apply Hno; right; left; exact Hn]. }
split; [rewrite Hfr4, Hfr3, Hfr2; reflexivity|].
split; [exact HRM4|].
(* the slot and g_nfd at the end *)
assert (KSL : forall a, oa_HA i <= a < oa_HA i + 96 ->
  aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem msB) a).
{ intros a Ha. destruct (GOK a (HSL a Ha)) as (Him & Hno & He & _).
  apply (KRA a Him); [intros Hr; pose proof (oa_ra_g a Hr); rewrite HAv in Ha; lia | exact Hno | exact He]. }
assert (KNF : forall a, A_NFD <= a < A_NFD + 4 ->
  aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem msB) a).
{ intros a Ha. destruct (GOK a (HGnfd a Ha)) as (Him & Hno & He & _).
  apply (KRA a Him); [intros Hr; pose proof (oa_ra_g a Hr); unfold A_NFD in Ha; lia | exact Hno | exact He]. }
assert (VS : forall off (w : nat) v, 0 <= off -> off + Z.of_nat w <= 96 ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + off) w v ->
  val_mem SEGS (arm W4 (ms_mem msF)) (oa_HA i + off) w v).
{ intros off w v Ho Hw Hv. apply (val_mem_kept SEGS (w_H W3) (w_H W4) (ms_mem msB) (ms_mem msF) _ w); [|exact Hv].
  intros k Hk. apply KSL. lia. }
assert (HqF : In (q, APARTIAL) (ablocks B ly4 S4)).
{ destruct HTc as [(_ & HP4b) | (_ & _ & HE4)].
  - apply (Permutation_in _ (Permutation_sym HP4b)). right. exact Hqn.
  - rewrite HE4. exact Hqn. }
destruct (oa_new_src_at_x B ARx LAWS ly4 S4 Hp4 W4 (ms_mem msF) _ (oa_HA i) (100 + n0) q HARF HqF ltac:(lia)
  ltac:(intros j Hj; exact (HGW (oa_HA i + j) (HSL (oa_HA i + j) ltac:(unfold ASRC in Hj; lia)) _))
  ltac:(rewrite <- (Z.add_0_r (oa_HA i)); apply VS; [lia | lia | exact VF0])
  ltac:(apply VS; [lia | lia | exact VF4])
  ltac:(apply VS; [lia | lia | exact VF40])
  ltac:(rewrite Forall_forall in VZ |- *; intros p HIp; pose proof (VZ p HIp) as Hv;
        assert (Hb : 0 <= fst p /\ fst p + Z.of_nat (snd p) <= 96)
          by (cbn [In] in HIp; repeat (destruct HIp as [<- | HIp]; [cbn [fst snd]; lia|]); destruct HIp);
        apply VS; [lia | lia | exact Hv])) as (pj & Hsrc).
(* errno: relay_add (ra_post), malloc (its rule) and source_reset (ERR2) keep it; the runs store only to the
   slot's first 48 bytes and g_nfd, which are in G, and gx_rt keeps errno out of G *)
assert (ERRF : forall j, 0 <= j < 4 ->
  aview SEGS (w_H W4) (ms_mem msF) (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)).
{ pose proof (proj1 (pal_env B TL)) as (Ee0 & Ee1).
  intros j Hj.
  assert (Hs : ~ (oa_HA i <= as_errno B + j < oa_HA i + 48)).
  { intros Hs. exact (proj1 (HGRT (as_errno B + j) (HSL (as_errno B + j) ltac:(lia))) ltac:(lia)). }
  assert (Hn : ~ (A_NFD <= as_errno B + j < A_NFD + 4)).
  { intros Hn. exact (proj1 (HGRT (as_errno B + j) (HGnfd (as_errno B + j) Hn)) ltac:(lia)). }
  rewrite KF, (Herr4 j Hj), (KR3 (as_errno B + j) ltac:(lia) Hs Hn), (Herr3 j Hj),
    (KR (as_errno B + j) ltac:(lia) Hs Hn).
  exact (ERR2 j Hj). }
split; [|exact ERRF].
exists q, T', pj.
split; [exact Hsrc|].
split.
{ apply (val_mem_kept SEGS (w_H W3) (w_H W4) (ms_mem msB) (ms_mem msF) _ 4); [|rewrite Z.add_0_r in VN; exact VN].
  intros k Hk. apply KNF. lia. }
assert (KF4 : forall fp, akept W4 mem4 W4 (ms_mem msF) fp).
{ intros fp r Hr a Ha. split; [exact (KF a)|]. intros Hw. exact (writable_at_grows SEGS _ _ a HGr3 Hw). }
split.
{ apply (arelay_at_kept B fr_globals ly4 S4 W4 mem4 ly4 S4 W4 (ms_mem msF) T' _ Hrelay4 (KF4 _)).
  pose proof Hrelay4 as (_ & _ & _ & _ & _ & _ & _ & HTB4 & _ & HE4' & _). rewrite Forall_forall in HE4'.
  intros b Hb. destruct Hb as [<- | Hb]; [exact HTB4|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  exact (oa_eblks_in ly4 S4 W4 mem4 e (HE4' e He) b Hb). }
split; [exact (alock_at_kept fr_globals W4 mem4 W4 (ms_mem msF) false Hlock4 (KF4 _))|].
split.
{ destruct HTc as [(HT0 & HP4b) | (HT0 & HTT & HE4)].
  - left. split; [exact HT0|]. eapply Permutation_trans; [exact HP4b|]. apply perm_skip. rewrite Hbl3.
    eapply Permutation_trans; [apply Permutation_app_tail; exact HP2|]. apply Permutation_sym, Permutation_cons_append.
  - right. split; [exact HT0|]. split; [exact HTT|]. rewrite HE4, Hbl3.
    eapply Permutation_trans; [apply Permutation_app_tail; exact HP2|]. apply Permutation_sym, Permutation_cons_append. }
pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia)) as M1. pose proof (mo_free_nonneg MT MLAW) as M2.
apply (mle_weaken MT S S4 _ oa_cost MLAW (mle_station MT S S3 S4 _ _ MLAW Hmle23 Hmle4)).
unfold oa_cost, ra_cost. destruct (T =? 0); lia.
Qed.

(* From the source_reset call (0x84fa4) on, for the slot i op_add opens: source_reset at the slot's own G, then
   oa_tail. *)
Lemma oa_found : forall (i : nat) W ly S Hp regs mem md ch os n0 T es regs0 mem0 md0 k0 (kr : nat),
oa_first os = Some i -> nth i os 0 = 0 ->
afn_pre_x SEGS B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
asrc_closed W mem (oa_HA i) ->
val_mem SEGS (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es ->
alock_at fr_globals W mem false -> awake_at fr_globals W mem -> rom_view SEGS W mem ->
(length es < 4)%nat -> ~ In (100 + n0) (map re_fd es) ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX -> mo_ok MT S oa_cost ->
rp_RM RP S (oa_rk + kr)%nat -> cnt_ok_pk RP oa_peak (ablocks B ly S) ->
ajournal_gx_x SEGS B PST ARx G 0 [] OA_STK (spZ regs) (oa_FP os T es) ly S Hp W mem md [] ly S Hp W mem0 md0 k0 ->
oa_kept_fr W (spZ regs) mem mem0 -> apres_kept B W mem W mem0 ->
getr regs0 1 = Z_to_bv 64 (BASE + A_oaf) -> getr regs0 2 = Z_to_bv 64 (spZ regs - 64) ->
getr regs0 3 = getr regs 3 -> getr regs0 4 = getr regs 4 ->
getr regs0 8 = Z_to_bv 64 (oa_HA i) -> getr regs0 10 = Z_to_bv 64 (oa_HA i) ->
getr regs0 19 = Z_to_bv 64 (SB + (oa_HA i + 4) / 8) -> getr regs0 20 = Z_to_bv 64 (rg_s fr_globals) ->
getr regs0 21 = Z_to_bv 64 (- (SB + 12 * Z.of_nat i)) ->
getr regs0 23 = getr regs 23 -> getr regs0 24 = getr regs 24 -> getr regs0 25 = getr regs 25 ->
getr regs0 26 = getr regs 26 -> getr regs0 27 = getr regs 27 ->
Forall (fun p => val_mem SEGS (arm W mem0) (spZ regs - 64 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) oa_saved ->
SRr SEGS W (mkCfg (mkst regs0 (Z_to_bv 64 (BASE + AF_fr_source_reset)) mem0 (seg_rom SEGS)) md0)
  (oa_post_x regs ly S Hp W mem md os n0 T es kr).
Proof.
intros i W ly S Hp regs mem md ch os n0 T es regs0 mem0 md0 k0 kr Hfirst Hc0 HPRE Hal32 Hcid ACL0 Hnfd Hn0 HZgs
HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT HJ KEEP AP
R1 R2 R3 R4 R8 R10 R19 R20 R21 R23 R24 R25 R26 R27 SAVED.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hi4 : (i < 4)%nat).
{ unfold oa_first in Hfirst.
  destruct (nth 0 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 1 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 2 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 3 os 0 =? 0); [injection Hfirst as <-; lia | discriminate]. }
assert (HAv : oa_HA i = 6129888 + 96 * Z.of_nat i) by (unfold oa_HA, ASRC, fr_globals, rg_s; lia).
assert (HAr : rg_s fr_globals <= oa_HA i /\ oa_HA i + ASRC <= rg_s fr_globals + 4 * ASRC)
by (rewrite HAv; unfold ASRC, fr_globals, rg_s; lia).
assert (GOK : forall a, inG G a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ 0 <= a < kLowMemEnd).
{ intros a Ha. destruct (HG a Ha) as (Him & Hno & _). destruct (HGRT a Ha) as [He _].
  pose proof (Hsegs a Him). split; [exact Him|]. split; [exact Hno|]. split; [exact He | lia]. }
assert (Hfr : forall a, 0 <= a < kLowMemEnd -> ~ (spZ regs - OA_FRAME <= a < spZ regs)).
{ intros a Ha [HA1 HB1]. unfold OA_FRAME, OA_STK, RA_STK, RA_FRAME, ASTACK, kLowMemEnd in *. lia. }
unfold oa_FP in HJ. rewrite Hfirst in HJ.
(* the slot as source_reset finds it: closed *)
assert (ABK : forall a, oa_HA i <= a < oa_HA i + ASRC -> abyte_kept W mem W mem0 a).
{ intros a Ha. destruct (GOK a (HGgs a ltac:(lia))) as (Him & Hno & He & Hlo). split.
  - apply KEEP; [lia | exact (Hfr a Hlo)].
  - apply writable_kept. intros Hpa. exact (AP a Him Hno He Hpa). }
assert (ACL : asrc_closed W mem0 (oa_HA i)).
{ destruct ACL0 as [HGZ HWR]. split.
  - apply (akept_garr8 W mem W mem0 (oa_HA i) (repeat 0 (Z.to_nat ASRC))); [|exact HGZ].
    intros x Hx. apply ABK. rewrite repeat_length in Hx. unfold ASRC in *. lia.
  - apply (akept_awr W mem W mem0 (oa_HA i) ASRC); [intros x Hx; apply ABK; lia | exact HWR]. }
(* source_reset at the slot's own globals *)
pose (G1 := [(oa_HA i, ASRC)]).
assert (HinGs1 : forall a, inG G1 a -> oa_HA i <= a < oa_HA i + ASRC).
{ intros a Ha. apply inG_cons in Ha as [Hz | Hz]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia
  | exfalso; exact (inG_nil a Hz)]. }
assert (HGP1 : gx_prog_x B ARx G1).
{ apply (gx_prog_sub_x B ARx G1 G); [|exact HGP]. intros a Ha. apply HGgs. pose proof (HinGs1 a Ha). lia. }
pose proof (proj1 HGP1) as HGok1.
pose proof HJ as (HSTK0 & HXO0 & (memS0 & HJi0 & HAG0) & HOUT0).
rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRc & _).
assert (Hspc : spZ regs0 = spZ regs - 64)
by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HPREc : afn_pre_x SEGS B ARx SR_STK ly S Hp W regs0 mem0 md0 []).
{ split; [eapply ajournal_gx_AR_x; exact HJ|].
  split; [rewrite R1; apply ret_ok_codeptr_v; [unfold A_oaf, A_op_add, AF_fr_op_add; lia | reflexivity]|].
  split; [unfold raZ; rewrite R1, unsigned_lit_small by (unfold A_oaf, A_op_add, AF_fr_op_add; lia);
          unfold A_oaf, A_op_add, AF_fr_op_add; lia|].
  split; [rewrite R3; exact Hgp|].
  split; [rewrite R4; exact Htp|].
  split.
  { rewrite Hspc. unfold astk_ok, SR_STK, LF_STK, OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK in *.
    split; [replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
    repeat split; lia. }
  split.
  { intros a Ha. apply HPRc. rewrite Hspc in Ha.
    unfold SR_STK, LF_STK, OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK in *. lia. }
  split; [|exact HQT].
  apply achain_low. unfold s0Z. rewrite R8, unsigned_lit_small by lia. lia. }
(* the room round: oa_rk = 7, of which source_reset at None charges 4 (four free(NULL)) *)
assert (Hrk : oa_rk = 7%nat) by reflexivity.
assert (Hsr4 : Z.to_nat (sr_cost MT_rk None) = 4%nat) by reflexivity.
eapply SRr_bind.
{ exact (SR G1 HGP1 W ly S Hp regs0 mem0 md0 [] (oa_HA i) None HPREc R10
    ltac:(unfold oa_HA, ASRC; cbn [fr_globals rg_s]; clear; rewrite Z.add_mod, Z.mul_mod by lia; reflexivity) ACL
    ltac:(intros a Ha; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia)
    ltac:(destruct HZgs as (r & Hin & H8 & Hlo & Hhi); exists r; split; [exact Hin|]; split; [exact H8|]; lia)
    ltac:(eapply ajournal_gx_rom_view_x; first [exact Hsegs | exact LAWS | exact HJ | exact HRO | exact oa_pstr | exact Hrom])
    ltac:(apply (mok_station MT S S oa_cost 0 (sr_cost MT None) MLAW Hmok (mle_start MT S MLAW));
          [unfold sr_cost; pose proof (mo_free_nonneg MT MLAW); lia
          | unfold oa_cost; pose proof (mo_malloc_nonneg MT MLAW APARTIAL ltac:(unfold APARTIAL; lia));
            pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia));
            pose proof (mo_free_nonneg MT MLAW); lia])
    (3 + kr)%nat
    ltac:(rewrite Hsr4; rewrite Hrk in HRM; exact HRM)
    (oa_cnt_perm (fun _ => 0%nat) _ _ (Permutation_refl _) ltac:(intros P; cbv beta; lia) HCNT)). }
cbv beta. intros W2 c2 Hwle2
  (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk2 & -> & HJ2 & Hpres2 & ACL2 & Hperm2 & AP2 & Herr2 & Hfr2 & Hmle2 & HRM2).
(* the callee's journal, at the caller's G *)
assert (HJ3 : ajournal_gx_x SEGS B PST ARx G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md ([] ++ []) ly2 S2 Hp2 W2 mem2 md2 (k0 + kk2)).
{ eapply ajournal_gx_sub_x;
  first [ exact LAWS | exact Hsegs | exact HJ | exact HG
        | (eapply ajournal_gx_G_mono_x; [intros a Ha; apply HGgs; pose proof (HinGs1 a Ha); lia | exact HJ2])
        | (intros a (r & Hin & _); destruct Hin)
        | (rewrite Hspc; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, SR_STK, LF_STK, ASTACK; lia) ]. }
cbn [app] in HJ3.
assert (AP3 : apres_kept B W mem W2 mem2) by (intros a H1 H2 H3 H4; apply AP2; auto; apply AP; auto).
assert (HP2 : Permutation (ablocks B ly2 S2) (ablocks B ly S)) by exact (Hperm2 _ (Permutation_refl _)).
(* what source_reset keeps *)
assert (KSR : forall a, in_img SEGS a -> ~ inG G1 a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Him HnG Hno He.
  rewrite (oa_call_keep G1 SR_STK (spZ regs0) _ ly S Hp W mem0 md0 ly2 S2 Hp2 W2 mem2 md2 kk2 HJ2
    ltac:(intros (r & Hin & _); destruct Hin) a Him HnG Hno He).
  pose proof (Hsegs a Him) as Hlo. apply KEEP; [unfold kLowMemEnd in *; lia | exact (Hfr a Hlo)]. }
assert (GK2 : forall a, inG G a -> ~ (oa_HA i <= a < oa_HA i + ASRC) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hns. destruct (GOK a Ha) as (Him & Hno & He & _).
  apply KSR; [exact Him | intros Hin; exact (Hns (HinGs1 a Hin)) | exact Hno | exact He]. }
(* errno: source_reset keeps it (sr_post), and the runs before the call keep every byte outside the frame *)
assert (ERR2 : forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)).
{ pose proof (proj1 (pal_env B TL)) as (Ee0 & Ee1).
  intros j Hj. rewrite (Herr2 j Hj). apply KEEP; [lia | apply Hfr; lia]. }
assert (WK2 : forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (HWK a Ha) as (Him & Hno & He).
  apply KSR; [exact Him | intros Hin; pose proof (HinGs1 a Hin) as Hs; rewrite HAv in Hs;
    unfold fr_globals, rg_wake in Ha; lia | exact Hno | exact He]. }
assert (BK2 : forall b n j, In (b, n) (ablocks B ly S) -> 0 <= j < req_size n ->
  aview SEGS (w_H W2) mem2 (b + j) = aview SEGS (w_H W) mem (b + j)).
{ intros b n j Hb Hj.
  rewrite (oa_call_keep_blk G1 SR_STK (spZ regs0) _ ly S Hp W mem0 md0 ly2 S2 Hp2 W2 mem2 md2 kk2 HGok1 HJ2 b n j Hb
    (Permutation_in _ (Permutation_sym HP2) Hb) Hj ltac:(intros (r & Hin & _); destruct Hin)).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hb) as (_ & H4096 & Hbc & _).
  apply KEEP; [lia | intros [HA1 HB1]; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK in *; lia]. }
(* the frame is above source_reset's window *)
assert (SAVED2 : Forall (fun p => val_mem SEGS (arm W2 mem2) (spZ regs - 64 + fst p) 8
  (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) oa_saved).
{ rewrite Forall_forall in SAVED |- *. intros p HIp. pose proof (SAVED p HIp) as Hv.
  assert (Hoff : 0 <= fst p <= 56) by (unfold oa_saved in HIp; cbn [In] in HIp;
    repeat (destruct HIp as [HIp | HIp]; [subst p; cbn [fst]; lia|]); destruct HIp).
  apply (val_mem_kept SEGS (w_H W) (w_H W2) mem0 mem2 _ 8); [|exact Hv]. intros kk Hk.
  apply (oa_call_keep_hi G1 SR_STK (spZ regs0) _ ly S Hp W mem0 md0 ly2 S2 Hp2 W2 mem2 md2 kk2 HGok1 HJ2);
  rewrite ?Hspc; unfold SR_STK, LF_STK, OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK in *; lia. }
(* g_nfd still holds n0, and its bytes are still writable *)
assert (NFDK : forall a, A_NFD <= a < A_NFD + 4 -> abyte_kept W mem W2 mem2 a).
{ intros a Ha. destruct (GOK a (HGnfd a Ha)) as (Him & Hno & He & Hlo). split.
  - apply GK2; [exact (HGnfd a Ha) | rewrite HAv; unfold A_NFD in *; lia].
  - apply (oa_writable_img W W2 mem mem2 a Him). intros Hpa. exact (AP3 a Him Hno He Hpa). }
assert (KN : val_mem SEGS (arm W2 mem2) A_NFD 4 n0).
{ apply (akept_vm W mem W2 mem2 A_NFD 4%nat n0); [|exact Hnfd]. intros x Hx. apply NFDK. lia. }
assert (NFDW : awr W2 mem2 A_NFD 4).
{ intros j Hj. exact (HGW (A_NFD + j) (HGnfd (A_NFD + j) ltac:(lia)) _). }
rewrite R1.
apply (oa_tail i W ly S Hp regs mem md ch os n0 T es W2 ly2 S2 Hp2 regs2 mem2 md2 (k0 + kk2) kr Hfirst HPRE Hal32 Hcid Hn0
  Hes4 Hfd HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hlive Hmok HRM2 HCNT HJ3 AP3 GK2 WK2 ERR2 BK2 HP2 Hfr2 Hmle2 ACL2 KN NFDW
  (eq_trans (Hpres2 2 ltac:(unfold acallee_saved; lia)) R2) (eq_trans (Hpres2 3 ltac:(unfold acallee_saved; lia)) R3)
  (eq_trans (Hpres2 4 ltac:(unfold acallee_saved; lia)) R4) (eq_trans (Hpres2 8 ltac:(unfold acallee_saved; lia)) R8)
  (eq_trans (Hpres2 19 ltac:(unfold acallee_saved; lia)) R19) (eq_trans (Hpres2 20 ltac:(unfold acallee_saved; lia)) R20)
  (eq_trans (Hpres2 21 ltac:(unfold acallee_saved; lia)) R21) (eq_trans (Hpres2 23 ltac:(unfold acallee_saved; lia)) R23)
  (eq_trans (Hpres2 24 ltac:(unfold acallee_saved; lia)) R24) (eq_trans (Hpres2 25 ltac:(unfold acallee_saved; lia)) R25)
  (eq_trans (Hpres2 26 ltac:(unfold acallee_saved; lia)) R26) (eq_trans (Hpres2 27 ltac:(unfold acallee_saved; lia)) R27)
  SAVED2).
Qed.

(* the registers at the source_reset call of an arm of the loop, read off its symbolic state *)
Ltac oa_found_reg HS EA Usp E37 E263 HEI :=
  lazymatch goal with
  | |- getr (ms_regs ?ms) ?r = _ =>
    lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ms) =>
      rewrite (st_ok_pi_restrict_reg H Ev ss ms r HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e;
      lazymatch e with
      | SOff 240 ?k => exact (codeptr_val Ev k HEI)
      | SOff 2 ?k => cbn [sv_denot]; rewrite Usp; f_equal; lia
      | SOff 263 ?k =>
          apply oa_sv_lit';
          [ rewrite (U_atom_off Ev 263 (rg_s fr_globals) k E263) by (unfold fr_globals, rg_s; lia);
            unfold oa_HA, ASRC; lia
          | unfold oa_HA, ASRC, fr_globals, rg_s; lia ]
      | SOff ?n 0 => cbn [sv_denot]; rewrite (EA n ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SRL (SOff 263 ?k) (SLit 3)) =>
          rewrite (oa_sh_den Ev 37 263 SB (rg_s fr_globals) k E37 E263) by (unfold SB, fr_globals, rg_s; lia);
          unfold oa_HA, ASRC; do 3 f_equal; lia
      | SAlu ALU_SUB (SLit 0) (SOff 37 ?k) =>
          apply oa_sv_lit; rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SLit, (U_atom_off Ev 37 SB k E37) by (unfold SB; lia);
          change (zcanon 0) with 0; f_equal; lia
      end
    end
  end.
(* the frame at the source_reset call of an arm: the caller's ra and s0 .. s6, as the prologue stored them *)
Ltac oa_found_frame HS EA Usp :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    let RF := fresh "RF" in
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF; cbn [ms_mem restrict] in RF;
    apply (oa_saved_of_region Ev _ _ _ _ _ _ _ _ RF Usp EA);
    unfold oa_saved; repeat apply Forall_cons; try apply Forall_nil;
    cbn [fst snd]; repeat (first [left; reflexivity | right])
  end.

Theorem pb_op_add_x : oa_spec_x A_op_addP.
Proof.
intros W ly S Hp regs mem md ch os n0 T es HPRE Hal32 Hcid Hlen Hrng Hcells Hclosed Hnfd Hn0
HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hfree Hlive Hmok kr HRM HCNT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (oa_entry W ly S Hp regs mem md ch os n0 HPRE Hlen Hrng Hcells Hnfd Hn0 HZgs) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ajournal_gx_init_x SEGS B PST ARx G 0 [] OA_STK (oa_FP os T es) ly S Hp W regs mem md ch HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (oa_extra os n0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (oa_extra os n0)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EA : forall r, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec r 32); [reflexivity | lia]. }
assert (E32 : ew E 32 = Z_to_bv 64 (nth 0 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (nth 1 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nth 2 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (nth 3 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E37 : ew E 37 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E263 : ew E 263 = Z_to_bv 64 (rg_s fr_globals))
by (subst E; rewrite <- HGS; apply (Eimg_img _ (A_OBJ 22)); unfold A_OBJ, A_TEXT, A_LIM; lia).
clear HE.
unfold cfg_at. change (w64 A_op_addP) with (Z_to_bv 64 A_op_addP). unfold A_op_addP, A_op_add.
paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr0 Usp. }
assert (AP : apres_kept B W mem W mem) by (intros a _ _ _ Ha; exact Ha).
assert (KEEP : oa_kept_fr W (spZ regs) mem mem) by (intros a _ _; reflexivity).
oa_pres AP. oa_keep KEEP Usp.
(* the loop: trip i reads g_s[i].open; the first zero flag leaves it for oa_found *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- oa_flag Hc E32 0%nat Hrng. apply Z.eqb_eq in Hc.
  assert (Hfirst : oa_first os = Some 0%nat)
  by (unfold oa_first; rewrite (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
  paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_source_reset. { oa_awr0 Usp. }
  oa_pres AP. oa_keep KEEP Usp. repeat rewrite wvb_collapse in HJ. pmkst HS.
  destruct (Hfree ltac:(rewrite Hfirst; discriminate)) as [Hes4 Hfd].
  apply (oa_found 0%nat W ly S Hp regs mem md ch os n0 T es _ _ _ _ kr Hfirst Hc HPRE Hal32 Hcid
    (Hclosed 0%nat ltac:(lia) Hc) Hnfd Hn0 HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT
    HJ KEEP AP);
  lazymatch goal with |- Forall _ _ => oa_found_frame HS EA Usp | |- _ => oa_found_reg HS EA Usp E37 E263 HEI end.
- oa_flag Hc E32 0%nat Hrng. apply Z.eqb_neq in Hc. rename Hc into Hnz0.
  paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
  oa_bump HS 4 E37 E263.
  paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + oa_flag Hc E33 1%nat Hrng. apply Z.eqb_eq in Hc.
    assert (Hfirst : oa_first os = Some 1%nat)
    by (unfold oa_first; rewrite (proj2 (Z.eqb_neq _ _) Hnz0), (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
    paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_source_reset. { oa_awr0 Usp. }
    oa_pres AP. oa_keep KEEP Usp. repeat rewrite wvb_collapse in HJ. pmkst HS.
    destruct (Hfree ltac:(rewrite Hfirst; discriminate)) as [Hes4 Hfd].
    apply (oa_found 1%nat W ly S Hp regs mem md ch os n0 T es _ _ _ _ kr Hfirst Hc HPRE Hal32 Hcid
      (Hclosed 1%nat ltac:(lia) Hc) Hnfd Hn0 HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT
      HJ KEEP AP);
    lazymatch goal with |- Forall _ _ => oa_found_frame HS EA Usp | |- _ => oa_found_reg HS EA Usp E37 E263 HEI end.
  + oa_flag Hc E33 1%nat Hrng. apply Z.eqb_neq in Hc. rename Hc into Hnz1.
    paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
    oa_bump HS 100 E37 E263.
    paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * oa_flag Hc E34 2%nat Hrng. apply Z.eqb_eq in Hc.
      assert (Hfirst : oa_first os = Some 2%nat)
      by (unfold oa_first; rewrite (proj2 (Z.eqb_neq _ _) Hnz0), (proj2 (Z.eqb_neq _ _) Hnz1), (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
      paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_source_reset. { oa_awr0 Usp. }
      oa_pres AP. oa_keep KEEP Usp. repeat rewrite wvb_collapse in HJ. pmkst HS.
      destruct (Hfree ltac:(rewrite Hfirst; discriminate)) as [Hes4 Hfd].
      apply (oa_found 2%nat W ly S Hp regs mem md ch os n0 T es _ _ _ _ kr Hfirst Hc HPRE Hal32 Hcid
        (Hclosed 2%nat ltac:(lia) Hc) Hnfd Hn0 HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT
        HJ KEEP AP);
      lazymatch goal with |- Forall _ _ => oa_found_frame HS EA Usp | |- _ => oa_found_reg HS EA Usp E37 E263 HEI end.
    * oa_flag Hc E34 2%nat Hrng. apply Z.eqb_neq in Hc. rename Hc into Hnz2.
      paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
      oa_bump HS 196 E37 E263.
      paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- oa_flag Hc E35 3%nat Hrng. apply Z.eqb_eq in Hc.
       assert (Hfirst : oa_first os = Some 3%nat)
       by (unfold oa_first; rewrite (proj2 (Z.eqb_neq _ _) Hnz0), (proj2 (Z.eqb_neq _ _) Hnz1), (proj2 (Z.eqb_neq _ _) Hnz2), (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
       paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_source_reset. { oa_awr0 Usp. }
       oa_pres AP. oa_keep KEEP Usp. repeat rewrite wvb_collapse in HJ. pmkst HS.
       destruct (Hfree ltac:(rewrite Hfirst; discriminate)) as [Hes4 Hfd].
       apply (oa_found 3%nat W ly S Hp regs mem md ch os n0 T es _ _ _ _ kr Hfirst Hc HPRE Hal32 Hcid
         (Hclosed 3%nat ltac:(lia) Hc) Hnfd Hn0 HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT
         HJ KEEP AP);
       lazymatch goal with |- Forall _ _ => oa_found_frame HS EA Usp | |- _ => oa_found_reg HS EA Usp E37 E263 HEI end.
      -- oa_flag Hc E35 3%nat Hrng. apply Z.eqb_neq in Hc. rename Hc into Hnz3.
         (* every slot is open: the loop ends and op_add returns with nothing changed *)
         paj_run_tok_x RUN HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
         assert (Hfz : oa_first os = None).
         { unfold oa_first. rewrite (proj2 (Z.eqb_neq _ _) Hnz0), (proj2 (Z.eqb_neq _ _) Hnz1),
           (proj2 (Z.eqb_neq _ _) Hnz2), (proj2 (Z.eqb_neq _ _) Hnz3). reflexivity. }
         prreg HS (1%bv : bv 5) R1.
         eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
         intros mat'. unfold oa_post_x. rewrite Hfz.
         lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
           exists ly, S, Hp, r, m, d, 0 end.
         split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
         split; [apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ|].
         split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (oa_extra os n0) HS);
                 [exact HAE | vm_compute; reflexivity]|].
         split; [exact AP|].
         split; [intros a HaG _; pose proof (Hsegs a (proj1 (HG a HaG))) as Hlo;
                 apply KEEP; [unfold kLowMemEnd in Hlo; lia
                 | intros [HA1 HB1]; unfold OA_FRAME, OA_STK, RA_STK, RA_FRAME, ASTACK, kLowMemEnd in *; lia]|].
         split; [reflexivity|].
         (* the room round: no allocator call on this arm, so the budget only shrinks (RMM) *)
         split; [exact (RMM S kr (oa_rk + kr)%nat ltac:(lia) HRM)|].
         split.
         { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           intros a Ha Hno. apply KEEP; [exact Ha|].
           intros [HA1 HB1]. apply Hno.
           unfold OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK in *. lia. }
         (* errno: outside op_add's frame (api_env puts it below kLowMemEnd) *)
         pose proof (proj1 (pal_env B TL)) as (Ee0 & Ee1).
         intros j Hj. apply KEEP; [lia|].
         intros [HA1 HB1]. unfold OA_FRAME in *. lia.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): op_add's walk at a world relation R.  Each <name>_xR below is <name> above with
   the journal `ajournal_gx_x SEGS B PST ARx` -> `ajournal_gx_xR SEGS B PST ARx R`, `SRr SEGS` -> `SRrG SEGS R`, the
   journal lemmas -> their _xR twins (W_journal_x.v), the runs -> the Section g runs paj_run_x_xG / paj_run_to_x_xG
   (W_journal_x.v, concluding SRrG) with the run tactics paj_run_tok_xR / paj_run_to_tok_xR (W_kit_x.v), the branch ->
   paj_branch_xR (W_kit.v), the binds -> SRrG_bind SEGS R R_trans, the return -> the strict step lifted by SRr_SRrG
   (WLE_R), and the three calls -> their R forms: malloc AMA_R := amalloc_cf_rule_c_xR .. RO CTX_M R (its RO
   call-boundary premise from ARx at the call state, RO_ARx; part 3c removed its memnorm premise), source_reset SR_R :=
   sr_spec_g_xR, relay_add RA_R := ra_spec_g_xR (W_contract_srlf_xR.v).  Every other token is the strict text's.  The
   strict pb_op_add_x above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AMA_R : amalloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO CTX_M R.
Hypothesis SR_R : sr_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_source_reset).
Hypothesis RA_R : ra_spec_g_xR B PST ARx R MT RP fr_globals CTX_R (BASE + AF_fr_relay_add).
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* What a callee taken at its OWN globals G' keeps: every image byte outside G', the allocator's statics
   and errno.  This is the donor journal's image clause (Reusable/YCbq.v:363) read through the overlay of
   W_journal.v's ajournal_g (the callee's start memory differs from the caller's only on G'). *)
(* :399 oa_call_keep *)
Lemma oa_call_keep_xR : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world SEGS) m0 md0 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k,
ajournal_gx_xR SEGS B PST ARx R G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
forall a, in_img SEGS a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W1) m1 a = aview SEGS (w_H W0) m0 a.
Proof.
intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a Him Hno He (HPST a Him) ltac:(apply fp_spares_closed; exact Hsk)).
apply (aview_gagree SEGS G' (w_H W0) m0 memS a HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* the bytes of a block live before and after the call, outside the callee's FP *)
(* :414 oa_call_keep_blk *)
Lemma oa_call_keep_blk_xR : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world SEGS) m0 md0 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k,
gx_ok SEGS B G' ->
ajournal_gx_xR SEGS B PST ARx R G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
~ inFP FP (p + j) -> aview SEGS (w_H W1) m1 (p + j) = aview SEGS (w_H W0) m0 (p + j).
Proof.
intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 p n j H0 H1 Hj Hfp).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
apply (aview_gagree SEGS G' (w_H W0) m0 memS (p + j) HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
exact (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
(* and what it keeps above alloc_ceiling: every byte outside its own window (the caller's frame is there,
   so the caller's stack region survives the call) *)
(* :432 oa_call_keep_hi *)
Lemma oa_call_keep_hi_xR : forall G' STK sp0 FP ly0 S0 Hp0 (W0 : world SEGS) m0 md0 ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k,
gx_ok SEGS B G' ->
ajournal_gx_xR SEGS B PST ARx R G' 0 [] STK sp0 FP ly0 S0 Hp0 W0 m0 md0 [] ly1 S1 Hp1 W1 m1 md1 k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview SEGS (w_H W1) m1 a = aview SEGS (w_H W0) m0 a.
Proof.
intros G' STK sp0 FP ly0 S0 Hp0 W0 m0 md0 ly1 S1 Hp1 W1 m1 md1 k HGok HJx a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno).
apply (aview_gagree SEGS G' (w_H W0) m0 memS a HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
(* From 0x84fa8 (back from source_reset) to the return, for the slot i op_add opens. *)
(* :1069 oa_tail *)
Lemma oa_tail_xR : forall (i : nat) W ly S Hp regs mem md ch os n0 T es W2 ly2 S2 Hp2 regs2 mem2 md2 k2 (kr : nat),
oa_first os = Some i ->
afn_pre_x SEGS B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 -> count_cid 0 (frames S) < fs_frames 0 ->
0 <= n0 <= 512 -> (length es < 4)%nat -> ~ In (100 + n0) (map re_fd es) ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es -> alock_at fr_globals W mem false -> awake_at fr_globals W mem ->
rom_view SEGS W mem ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX -> mo_ok MT S oa_cost ->
rp_RM RP S2 (3 + kr)%nat -> cnt_ok_pk RP oa_peak (ablocks B ly S) ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k2 ->
apres_kept B W mem W2 mem2 ->
(forall a, inG G a -> ~ (oa_HA i <= a < oa_HA i + ASRC) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
(forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a) ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)) ->
(forall b n j, In (b, n) (ablocks B ly S) -> 0 <= j < req_size n ->
 aview SEGS (w_H W2) mem2 (b + j) = aview SEGS (w_H W) mem (b + j)) ->
Permutation (ablocks B ly2 S2) (ablocks B ly S) -> frames S2 = frames S -> mo_le MT S S2 (sr_cost MT None) ->
asrc_closed W2 mem2 (oa_HA i) ->
val_mem SEGS (arm W2 mem2) A_NFD 4 n0 -> awr W2 mem2 A_NFD 4 ->
getr regs2 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
getr regs2 8 = Z_to_bv 64 (oa_HA i) -> getr regs2 19 = Z_to_bv 64 (SB + (oa_HA i + 4) / 8) ->
getr regs2 20 = Z_to_bv 64 (rg_s fr_globals) -> getr regs2 21 = Z_to_bv 64 (- (SB + 12 * Z.of_nat i)) ->
getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 -> getr regs2 25 = getr regs 25 ->
getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 ->
Forall (fun p => val_mem SEGS (arm W2 mem2) (spZ regs - 64 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) oa_saved ->
SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_oaf)) mem2 (seg_rom SEGS)) md2)
  (oa_post_xR PST ARx R RP regs ly S Hp W mem md os n0 T es kr).
Proof.
intros i W ly S Hp regs mem md ch os n0 T es W2 ly2 S2 Hp2 regs2 mem2 md2 k2 kr Hfirst HPRE Hal32 Hcid Hn0 Hes4 Hfd HZgs
HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hlive Hmok HRM2 HCNT HJ AP GK2 WK2 ERR2 BK2 HP2 Hfr2 Hmle2 ACL2 KN NFDW
R2 R3 R4 R8 R19 R20 R21 R23 R24 R25 R26 R27 SAVED.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : OA_STK = 16576) by reflexivity.
assert (Hi4 : (i < 4)%nat).
{ unfold oa_first in Hfirst.
  destruct (nth 0 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 1 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 2 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 3 os 0 =? 0); [injection Hfirst as <-; lia | discriminate]. }
assert (HAv : oa_HA i = 6129888 + 96 * Z.of_nat i) by (unfold oa_HA, ASRC, fr_globals, rg_s; lia).
assert (HSL : forall a, oa_HA i <= a < oa_HA i + 96 -> inG G a)
by (intros a Ha; apply HGgs; rewrite HAv in Ha; unfold ASRC, fr_globals, rg_s; lia).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k2 HJ) as HAR2.
destruct (oa_seat i W ly S Hp regs mem md ch n0 W2 ly2 S2 Hp2 regs2 mem2 md2 Hi4 HPRE Hal32 Hn0 HZgs HAR2 ACL2 KN NFDW
  R2 R8 R19 SAVED) as [HS SHOK].
remember (Eimg (Ereg regs2 (oaf_extra regs n0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall r, (r < 32)%nat -> ew E r = getr regs2 (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec r 32); [reflexivity | lia]. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (oaf_extra regs n0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E270 : ew E 270 = Z_to_bv 64 A_NFD)
by (subst E; rewrite <- HNFD; apply (Eimg_img _ (A_OBJ 29)); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E372 : ew E 372 = Z_to_bv 64 (VAL (A_HI 92))).
{ rewrite <- (HEI (A_HI 92) ltac:(unfold A_TEXT, A_LIM, A_HI; lia)). rewrite Z_to_bv_bv_unsigned. reflexivity. }
clear HE.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 64)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E8 : ew E 8 = Z_to_bv 64 (oa_HA i)) by exact (eq_trans (EA 8%nat ltac:(lia)) R8).
assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_globals)) by exact (eq_trans (EA 20%nat ltac:(lia)) R20).
assert (E21 : ew E 21 = Z_to_bv 64 (- (SB + 12 * Z.of_nat i))) by exact (eq_trans (EA 21%nat ltac:(lia)) R21).
assert (E40 : ew E 40 = Z_to_bv 64 SB) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E 41 = Z_to_bv 64 n0) by exact (EX 9%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (U8 : bv_unsigned (ew E 8) = oa_HA i) by (rewrite E8; apply unsigned_lit_small; lia).
assert (Unfd : bv_unsigned (ew E 270) = A_NFD) by (rewrite E270; apply unsigned_lit_small; unfold A_NFD; lia).
unfold A_oaf, A_op_add.
(* R1a: 0x84fa8 .. the store of g_nfd + 1, through the auipc the listing does not name *)
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr2 Usp U8 Unfd HSL HGnfd. }
rename HFr into HFr1a, HG0 into HGr1a. clear HF.
oa_setsv HS (11%bv : bv 5) (SOff 270 1928)
  ltac:(apply U_inj;
        rewrite (U_atom_off E 270 A_NFD 1928 E270) by (unfold A_NFD; lia);
        rewrite (U_atom E 372 (VAL (A_HI 92)) E372) by (pose proof (pa_val_range (A_HI 92)); lia);
        exact HHI92).
(* R1b: the store of g_nfd + 1, then s6 = (g_s >> 3) - s5 *)
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr2 Usp U8 Unfd HSL HGnfd. }
rename HFr into HFr1b, HG0 into HGr1b. clear HF.
oa_setsv HS (22%bv : bv 5) (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SRL (SOff 8 0) (SLit 3)))
  ltac:(rewrite HAv in E8; exact (oa_sh_sub E SB (rg_s fr_globals) (Z.of_nat i) 0 E40 E8 E20 E21
          ltac:(unfold SB; lia) ltac:(unfold fr_globals, rg_s; lia) ltac:(lia) ltac:(lia))).
(* R1c: the store of the descriptor 100 + n0 into the slot, malloc (6000) *)
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr2 Usp U8 Unfd HSL HGnfd. }
rename HFr into HFr1c, HG0 into HGr1c. clear HF.
(* the three runs wrote nothing but the slot's first 48 bytes and g_nfd, and kept every present byte *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (oa_HA i <= a < oa_HA i + 48) -> ~ (A_NFD <= a < A_NFD + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a) by reflexivity.
assert (APR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros a Ha; exact Ha).
oa_kr i mem2 HFr1a KR Usp U8 Unfd. oa_kr i mem2 HFr1b KR Usp U8 Unfd. oa_kr i mem2 HFr1c KR Usp U8 Unfd.
oa_apr mem2 HGr1a APR. oa_apr mem2 HGr1b APR. oa_apr mem2 HGr1c APR.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => let x := fresh "msA" in rename mm into x end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (Usp1 : spZ (ms_regs msA) = spZ regs - 64) by (unfold spZ; rewrite Q2; exact Usp).
assert (GOK : forall a, inG G a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ 0 <= a < kLowMemEnd).
{ intros a Ha. destruct (HG a Ha) as (Him & Hno & _). destruct (HGRT a Ha) as [He _].
  pose proof (Hsegs a Him). split; [exact Him|]. split; [exact Hno|]. split; [exact He | lia]. }
assert (Hbb2 : blocks_bytes S2 = blocks_bytes S)
by (rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S); exact (bsum_perm _ _ HP2)).
pose proof HJ as HJ2k.
destruct HJ as (HSTK1 & HXO1 & (memS & HJi & HAG) & HOUT1). rewrite !Z.add_0_r in HJi.
(* malloc (6000) *)
eapply (SRrG_bind SEGS R R_trans).
{ rewrite (pal_malloc B TL).
  eapply (AMA_R W2 (ms_regs msA) (ms_mem msA) OA_STK (spZ regs) (ra_FP T es) ly S Hp W memS md [] ly2 S2 Hp2 _ k2
    APARTIAL (-64) _ [] (2 + kr)%nat HJi).
  - rewrite Q10. reflexivity.
  - unfold APARTIAL in *. lia.
  - rewrite Hbb2. unfold APARTIAL, ATABLE in *. lia.
  - (* the room round: malloc's count at S2, whose blocks are the entry's (HP2) *)
    exact (oa_cnt_perm (fun _ => 0%nat) _ _ HP2 ltac:(intros P; cbv beta; lia) HCNT).
  - rewrite Usp1. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ASTACK. lia.
  - (* the room round: the allocator's stack room below the call, from the journal's astk_ok *)
    exact (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-64) (ms_regs msA) HJi
      ltac:(rewrite Usp1; lia) ltac:(rewrite WS; unfold ASTACK; lia)).
  - rewrite Q3. exact (eq_trans (EA 3%nat ltac:(lia)) (eq_trans R3 Hgp)).
  - rewrite Q4. exact (eq_trans (EA 4%nat ltac:(lia)) (eq_trans R4 Htp)).
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre ly2 _ (spZ regs - 64) (oa_HA i) [] (ms_regs msA)).
    + apply achain_low. rewrite HAv. lia.
    + rewrite Usp1. unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK in *. lia.
    + unfold s0Z. rewrite Q8. exact U8.
    + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - (* route R: RO at the call memory, from ARx at the call state (RO_ARx) *)
    exact (RO_ARx _ _ _ _ _ _ (proj1 HJi)).
  - (* malloc's caller context: the chain is [] (s0 holds the slot, an image address), so the trace is the one return
       address op_add + 0xcc (HCTX_oa_malloc) *)
    cbn [spine map]. replace (raZ (ms_regs msA)) with (BASE + AF_fr_op_add + 0xcc); [exact HCTX_oa_malloc|].
    unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    first [lia | (unfold AF_fr_op_add in *; lia) |
           (idtac "MCTX-RA_R"; match goal with |- ?g => idtac g end; fail)].
  - (* the room round: malloc charges 1 of the 3 left after source_reset *)
    exact HRM2.
  - apply (mok_station MT S S2 oa_cost (sr_cost MT None) _ MLAW Hmok Hmle2).
    + apply (mo_malloc_nonneg MT MLAW). unfold APARTIAL. lia.
    + unfold oa_cost. pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia)).
      pose proof (mo_free_nonneg MT MLAW). lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & q & -> & HJ3i & HP3 & Hq10 & Hfr3 & Hq4096 & Hbl3 &
  Hkept3 & Hmle3 & HRM3 & Herr3 & Hpres3).
pose proof (proj1 HJ3i) as HAR3.
assert (Hqn : In (q, APARTIAL) (ablocks B ly3 S3)) by (rewrite Hbl3; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 _ _ HAR3 Hqn) as (Hq16 & _ & Hqceil & Hqapp & Hqpres & _).
change (req_size APARTIAL) with 6000 in Hqceil, Hqapp, Hqpres.
(* back in op_add: the frame, the slot and g_nfd are image or stack bytes malloc keeps *)
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?U8, ?Unfd.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 Hkept3); rewrite ?Usp1; unfold ASTACK in *; lia.
  - intros a Ha. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GOK a (HSL a ltac:(lia))) as (Him & Hno & He & _).
    exact (proj1 (proj2 (proj2 Hkept3)) a Him Hno He).
  - intros a Ha _. apply HGW. apply HSL. lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). destruct (GOK a (HGnfd a ltac:(lia))) as (Him & Hno & He & _).
    exact (proj1 (proj2 (proj2 Hkept3)) a Him Hno He).
  - intros a Ha _. apply HGW. apply HGnfd. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HIa : forall m, (64 <= m)%nat -> ew Ea m = ew E m)
by (intros m Hm; rewrite HEa; apply ew_havoc_above; cbn [length map CLOB]; lia).
assert (Ea52 : ew Ea 52 = w64 q) by (rewrite HEa; exact Hq10).
clear HEa.
assert (HFa : afact_ok Ea 52 (mkAF 4096 0x7fffff800000 4)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ea52. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 4) with 16. rewrite Hq16. lia. }
pose proof (st_ok_pi_add_fact Ea _ _ 52%nat _ HS HFa) as HSa. clear HS HFa. rename HSa into HS.
assert (HJ3 : ajournal_gx_xR SEGS B PST ARx R G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly3 S3 Hp3 W3 mem3 md3 (k2 + 1)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md [] ly3 S3 Hp3 W3 mem3 md3 (k2 + 1) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ3i | exact HAG | apply out_none]. }
assert (SHOKa : sh_ok SEGS Bxf oaf_SH Ea (mrestrict (w_H W3) mem3))
by (apply (oa_shok i Ea ly3 S3 Hp3 W3 mem3 md3 Hi4 HAR3 HZgs); rewrite OLDa by lia; [exact E40 | exact E8]).
assert (Usp3 : bv_unsigned (ew Ea 2) = spZ regs - 64) by (rewrite OLDa by lia; exact Usp).
assert (U83 : bv_unsigned (ew Ea 8) = oa_HA i) by (rewrite OLDa by lia; exact U8).
assert (Unfd3 : bv_unsigned (ew Ea 270) = A_NFD) by (rewrite HIa by lia; exact Unfd).
(* R2a: s4 + 40, its shadow (g_s + 40) >> 3 - s5 *)
paj_run_tok_xR RUNG HS HJ3 SHOKa Bspan. { oa_awr2 Usp3 U83 Unfd3 HSL HGnfd. }
rename HFr into HFr2a, HG0 into HGr2a. clear HF.
assert (F40 : ew Ea 40 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E40).
assert (F8 : ew Ea 8 = Z_to_bv 64 (oa_HA i)) by (rewrite OLDa by lia; exact E8).
assert (F20 : ew Ea 20 = Z_to_bv 64 (rg_s fr_globals)) by (rewrite OLDa by lia; exact E20).
assert (F21 : ew Ea 21 = Z_to_bv 64 (- (SB + 12 * Z.of_nat i))) by (rewrite OLDa by lia; exact E21).
assert (F41 : ew Ea 41 = Z_to_bv 64 n0) by (rewrite OLDa by lia; exact E41).
oa_setsv HS (12%bv : bv 5) (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SRL (SOff 8 40) (SLit 3)))
  ltac:(rewrite HAv in F8; exact (oa_sh_sub Ea SB (rg_s fr_globals) (Z.of_nat i) 40 F40 F8 F20 F21
          ltac:(unfold SB; lia) ltac:(unfold fr_globals, rg_s; lia) ltac:(lia) ltac:(lia))).
(* R2b: the partial buffer into the slot, the open flag, the descriptor reloaded, the jal to relay_add *)
paj_run_to_tok_xR RUNTOG HS HJ3 SHOKa Bspan AF_fr_relay_add. { oa_awr2 Usp3 U83 Unfd3 HSL HGnfd. }
rename HFr into HFr2b, HG0 into HGr2b. clear HF.
(* the two runs after malloc kept everything outside the slot's first 48 bytes and g_nfd *)
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (oa_HA i <= a < oa_HA i + 48) -> ~ (A_NFD <= a < A_NFD + 4) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W3) mem3 a) by reflexivity.
assert (APR3 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem3 a) by (intros a Ha; exact Ha).
oa_kr i mem3 HFr2a KR3 Usp3 U83 Unfd3. oa_kr i mem3 HFr2b KR3 Usp3 U83 Unfd3.
oa_apr mem3 HGr2a APR3. oa_apr mem3 HGr2b APR3.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => let x := fresh "msB" in rename mm into x end.
repeat rewrite wvb_collapse in HJ3.
lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdl) _ => remember mdl as mdB in * end.
(* the slot and g_nfd as relay_add finds them *)
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RSL.
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RNF.
cbn [ms_mem restrict] in RSL, RNF.
assert (VF0 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + 0) (N.to_nat 4) (100 + n0)).
{ eapply (field_of_region Ea _ 8 (oa_HA i));
  [exact RSL | exact U83 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite F41, unsigned_lit_small by lia. f_equal. lia. }
assert (VF4 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + 4) (N.to_nat 4) 1).
{ eapply (field_of_region Ea _ 8 (oa_HA i));
  [exact RSL | exact U83 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  reflexivity. }
assert (VF40 : val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + 40) (N.to_nat 8) q).
{ eapply (field_of_region Ea _ 8 (oa_HA i));
  [exact RSL | exact U83 | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite Ea52. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VZ : Forall (fun p => val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + fst p) (snd p) 0)
  [(8,4%nat);(12,4%nat);(16,8%nat);(24,4%nat);(28,4%nat);(32,8%nat);(48,8%nat);(56,4%nat);(64,8%nat);(72,4%nat);
   (76,4%nat);(80,8%nat);(88,4%nat);(92,4%nat)]).
{ repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  lazymatch goal with
  | |- val_mem _ _ _ 4%nat _ => change 4%nat with (N.to_nat 4)
  | |- val_mem _ _ _ 8%nat _ => change 8%nat with (N.to_nat 8)
  end;
  (eapply (field_of_region Ea _ 8 (oa_HA i));
   [exact RSL | exact U83 | cbn [In]; repeat first [left; reflexivity | right] | reflexivity | zside | zside]). }
assert (VN : val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (A_NFD + 0) (N.to_nat 4) (n0 + 1)).
{ eapply (field_of_region Ea _ 270 A_NFD); [exact RNF | exact Unfd3 | cbn [In]; left; reflexivity | | zside | zside].
  cbn [sv_denot]. rewrite F41, unsigned_lit_small by lia. reflexivity. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (Usp4 : spZ (ms_regs msB) = spZ regs - 64) by (unfold spZ; rewrite P2; exact Usp3).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARB.
pose proof HJ3 as (_ & _ & (memSB & HJiB & _) & _). rewrite !Z.add_0_r in HJiB.
pose proof HJiB as (_ & HLYB & _ & _ & _ & HFRB & _ & _ & _ & _ & _ & _ & _ & HPRB & _ & _ & HQTB).
destruct HLYB as (_ & _ & _ & _ & _ & _ & _ & _ & LYtop & LYlo & LYhi & _).
cbn [app] in HFRB.
(* what the stretch from op_add's entry to the call kept *)
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (oa_HA i <= a < oa_HA i + 48) -> ~ (A_NFD <= a < A_NFD + 4) ->
  aview SEGS (w_H W3) (ms_mem msB) a = aview SEGS (w_H W2) mem2 a).
{ intros a Him Hno He Hs Hn. pose proof (Hsegs a Him) as Hlo. unfold kLowMemEnd in Hlo.
  rewrite (KR3 a ltac:(lia) Hs Hn). rewrite (proj1 (proj2 (proj2 Hkept3)) a Him Hno He).
  exact (KR a ltac:(lia) Hs Hn). }
assert (KG3 : forall a, inG G a -> ~ (oa_HA i <= a < oa_HA i + ASRC) -> ~ (A_NFD <= a < A_NFD + 4) ->
  aview SEGS (w_H W3) (ms_mem msB) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hs Hn. destruct (GOK a Ha) as (Him & Hno & He & _).
  rewrite (KIMG a Him Hno He ltac:(unfold ASRC in Hs; lia) Hn). exact (GK2 a Ha Hs). }
assert (KW3 : forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
  aview SEGS (w_H W3) (ms_mem msB) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (HWK a Ha) as (Him & Hno & He).
  rewrite (KIMG a Him Hno He) by (rewrite ?HAv; unfold fr_globals, rg_wake, A_NFD in *; lia). exact (WK2 a Ha). }
assert (APIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> apresent (w_H W) mem a -> apresent (w_H W3) (ms_mem msB) a).
{ intros a Him Hno He Hpa. apply APR3.
  apply (Hpres3 a Him (oa_not_owned _ _ _ _ _ _ a (proj1 HJi) Him Hno) (oa_not_owned _ _ _ _ _ _ a HAR3 Him Hno) He).
  - intros Hb. exact (blk_img_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 q APARTIAL a HAR3 Hqn Hb Him).
  - apply APR. exact (AP a Him Hno He Hpa). }
assert (KBLK : forall b n j, In (b, n) (ablocks B ly S) -> 0 <= j < req_size n ->
  aview SEGS (w_H W3) (ms_mem msB) (b + j) = aview SEGS (w_H W) mem (b + j)).
{ intros b n j Hb Hj.
  assert (Hni : ~ in_img SEGS (b + j)) by exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b n (b + j) HAR Hb ltac:(lia)).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hb) as (_ & H4096 & Hbc & _).
  assert (Hns : ~ (oa_HA i <= b + j < oa_HA i + 48))
  by (intros Hs; apply Hni; exact (proj1 (GOK (b + j) (HSL (b + j) ltac:(lia))))).
  assert (Hnn : ~ (A_NFD <= b + j < A_NFD + 4)) by (intros Hs; apply Hni; exact (proj1 (GOK _ (HGnfd _ Hs)))).
  assert (Hb2 : In (b, n) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym HP2) Hb).
  pose proof (oa_new_disj ly3 S3 Hp3 W3 mem3 md3 ly2 S2 q APARTIAL b n HAR3 Hbl3 Hb2) as Hd.
  change (req_size APARTIAL) with 6000 in Hd.
  rewrite (KR3 (b + j) ltac:(lia) Hns Hnn).
  rewrite (proj1 (proj2 Hkept3) b n j Hb2 Hj ltac:(cbv beta; change (req_size APARTIAL) with 6000; lia)).
  rewrite (KR (b + j) ltac:(lia) Hns Hnn).
  exact (BK2 b n j Hb Hj). }
assert (KRAG : forall a, inG (RA_G fr_globals) a -> abyte_kept W mem W3 (ms_mem msB) a).
{ intros a Ha. pose proof (oa_ra_g a Ha) as Hr. split.
  - apply KG3; [exact (HGra a Ha) | rewrite HAv; unfold ASRC; lia | unfold A_NFD; lia].
  - intros _. exact (HGW a (HGra a Ha) _). }
(* relay_add's premises at the call *)
assert (Hrel3 : ra_rel B fr_globals ly3 S3 W3 (ms_mem msB) T es).
{ apply (oa_rel_kept ly S W mem ly3 S3 Hp3 W3 (ms_mem msB) mdB T es Hrel HARB); [|exact KBLK | exact KRAG].
  intros b Hb. rewrite Hbl3. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym HP2) Hb). }
assert (Hlock3 : alock_at fr_globals W3 (ms_mem msB) false).
{ apply (alock_at_kept fr_globals W mem W3 (ms_mem msB) false Hlock).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha. apply KRAG.
  unfold RA_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
assert (Hwake3 : awake_at fr_globals W3 (ms_mem msB)).
{ apply (awake_at_kept fr_globals W mem W3 (ms_mem msB) Hwake).
  intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha. destruct (HWK a Ha) as (Him & Hno & He).
  split; [exact (KW3 a Ha)|]. intros Hw.
  exact (oa_writable_img W W3 mem (ms_mem msB) a Him (APIMG a Him Hno He) Hw). }
assert (Hrom3 : rom_view SEGS W3 (ms_mem msB))
by (eapply ajournal_gx_rom_view_xR; first [exact Hsegs | exact LAWS | exact HJ3 | exact HRO | exact oa_pstr | exact Hrom]).
assert (Hbb3 : blocks_bytes S3 = blocks_bytes S + APARTIAL).
{ rewrite (blocks_bytes_bsum B ly3 S3), Hbl3, bsum_app, <- (blocks_bytes_bsum B ly2 S2), Hbb2. reflexivity. }
assert (Hmle23 : mo_le MT S S3 (sr_cost MT None + mo_malloc MT APARTIAL))
by exact (mle_station MT S S2 S3 _ _ MLAW Hmle2 Hmle3).
assert (Hmok3 : mo_ok MT S3 (ra_cost MT T)).
{ pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia)) as M1. pose proof (mo_free_nonneg MT MLAW) as M2.
  apply (mok_station MT S S3 oa_cost _ _ MLAW Hmok Hmle23); unfold ra_cost, oa_cost; destruct (T =? 0); lia. }
assert (HGra_ok : gx_ok SEGS B (RA_G fr_globals)) by exact (gx_ok_sub SEGS B _ G HGra HG).
assert (HGra_rt : gx_rt B (RA_G fr_globals)) by exact (gx_rt_sub B _ G HGra HGRT).
assert (HPREra : afn_pre_x SEGS B ARx RA_STK ly3 S3 Hp3 W3 (ms_regs msB) (ms_mem msB) mdB []).
{ split; [exact HARB|].
  split; [rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]|].
  split; [unfold raZ; rewrite P1, unsigned_lit_small by lia; lia|].
  split; [rewrite P3; exact (eq_trans (OLDa 3%nat ltac:(lia)) (eq_trans (EA 3%nat ltac:(lia)) (eq_trans R3 Hgp)))|].
  split; [rewrite P4; exact (eq_trans (OLDa 4%nat ltac:(lia)) (eq_trans (EA 4%nat ltac:(lia)) (eq_trans R4 Htp)))|].
  split.
  { rewrite Usp4. unfold astk_ok, ly_bot in *. rewrite LYtop, LYlo, LYhi.
    unfold RA_STK, RA_FRAME, OA_STK, OA_FRAME, ASTACK in *.
    split; [replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
    repeat split; lia. }
  split.
  { intros a Ha. apply HPRB. rewrite Usp4 in Ha. unfold RA_STK, RA_FRAME, OA_STK, OA_FRAME, ASTACK in *. lia. }
  split; [|exact HQTB].
  apply achain_low. unfold s0Z. rewrite P8, U83, HAv. lia. }
(* relay_add (100 + n0) *)
(* relay_add's caller-context conjunct: room above relay_add's sp (op_add's frame is 64 bytes below op_add's sp,
   which is below the stack top), and the trace [relay_add + 332; op_add + 264] (HCTXRA), the chain being [] *)
assert (HRACTX : 0 <= 100 + n0 -> T = 0 ->
  spZ (ms_regs msB) + 16 < ly_top ly3 /\
  In (BASE + AF_fr_relay_add + 332 :: raZ (ms_regs msB) :: spine []) CTX_R).
{ intros _ _. split.
  - rewrite Usp4. unfold astk_ok, ly_bot in *. rewrite ?LYtop. unfold OA_STK, OA_FRAME, ASTACK in *.
    first [lia | (idtac "RACTX-ROOM"; match goal with |- ?g => idtac g end; fail)].
  - cbn [spine map]. replace (raZ (ms_regs msB)) with (BASE + AF_fr_op_add + 264); [exact HCTXRA|].
    unfold raZ. rewrite P1, unsigned_lit_small by lia.
    first [lia | (unfold AF_fr_op_add in *; lia) |
           (idtac "RACTX-RA_R"; match goal with |- ?g => idtac g end; fail)]. }
eapply (SRrG_bind SEGS R R_trans).
{ exact (RA_R (RA_G fr_globals) HGra_ok HGra_rt W3 ly3 S3 Hp3 (ms_regs msB) (ms_mem msB) mdB [] (100 + n0) T es HPREra
    ltac:(rewrite Usp4; replace (spZ regs - 64) with (spZ regs + (-2) * 32) by lia; rewrite Z_mod_plus_full; exact Hal32)
    ltac:(rewrite Hfr3, Hfr2; exact Hcid)
    ltac:(rewrite P10, F41, unsigned_lit_small by lia; f_equal; lia)
    ltac:(lia) Hlock3 Hwake3 Hrom3 Hrel3
    ltac:(intros _; split; [exact Hes4 | exact Hfd])
    ltac:(intros a Ha; exact Ha)
    ltac:(intros a Ha; exact (proj1 (HGRT a (HGra a Ha))))
    ltac:(intros _ _; rewrite Hbb3; unfold APARTIAL, ATABLE in *; lia)
    HRACTX
    Hmok3 kr
    (* the room round: relay_add charges ra_cost MT_rk T (2 when the table is new, else 0) of the 2 left after malloc;
       its count at S3 is the entry's plus the slot's APARTIAL block (Hbl3, HP2) *)
    (RMM S3 (Z.to_nat (ra_cost MT_rk T) + kr)%nat (2 + kr)%nat ltac:(unfold ra_cost; destruct (T =? 0); cbv; lia) HRM3)
    ltac:(rewrite Hbl3; exact (oa_cnt_ra _ _ q T HP2 HCNT))). }
cbv beta. intros W4 c4 Hwle4
  (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & -> & HJ4 & HP4 & AP4 & Hfr4 & Hmle4 & HRM4 & Hlock4 & Hcases & Herr4).
destruct Hcases as [(Hneg & _) | (_ & Hr10 & T' & Hrelay4 & HTc)]; [lia|].
(* the table relay_add used, when it existed, is a live block at the call (so T is no address 0 and the entry it
   writes lies in it) *)
assert (HTb : T <> 0 -> In (T, ATABLE) (ablocks B ly3 S3)).
{ intros HT0. destruct Hrel3 as [(HT & _) | Hat3]; [lia|].
  pose proof Hat3 as (_ & _ & _ & _ & _ & _ & _ & HTB & _). exact HTB. }
assert (Hsk : ~ YI16.sink_open_fp (ra_FP T es)).
{ unfold YI16.sink_open_fp, YI16.in_fp, ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0].
  - intros (r & [] & _).
  - destruct (alx_blocks _ _ _ LAWS ly3 S3 Hp3 W3 (ms_mem msB) mdB T ATABLE HARB (HTb HT0)) as (_ & HT4096 & _).
    intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold AENT in Hr. lia. }
(* back in op_add after relay_add: only the frame is read from here on *)
jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?ty -> _ => assert (HRK : ty); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp3.
  - intros a Ha. apply (mbyte_of_aview SEGS).
    apply (oa_call_keep_hi_xR (RA_G fr_globals) RA_STK (spZ (ms_regs msB)) _ ly3 S3 Hp3 W3 (ms_mem msB) mdB ly4 S4 Hp4 W4 mem4 md4 k4
      HGra_ok HJ4); rewrite ?Usp4; unfold RA_STK, RA_FRAME, ASTACK, OA_STK, OA_FRAME in *; lia.
  - intros a Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc Ea 64 (map (getr regs4) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 64)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (Eb68 : ew Eb 68 = w64 0) by (rewrite HEb; exact Hr10).
clear HEb.
assert (HFb : afact_ok Eb 68 (mkAF 0 0 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Eb68. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_pi_add_fact Eb _ _ 68%nat _ HS HFb) as HSb. clear HS HFb. rename HSb into HS.
(* the journal through relay_add, at op_add's G *)
assert (HFP : forall a, inFP (ra_FP T es) a ->
  (inFP (ra_FP T es) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly3 S3) a).
{ intros a Ha. left. split; [exact Ha|]. revert Ha. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0].
  - intros (r & [] & _).
  - intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. exists T, ATABLE. split; [exact (HTb HT0)|].
    change (req_size ATABLE) with 896. unfold AENT in Hr. lia. }
assert (HJ5 : ajournal_gx_xR SEGS B PST ARx R G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md ([] ++ []) ly4 S4 Hp4 W4 mem4 md4
  (k2 + 1 + k4)).
{ eapply ajournal_gx_sub_xR;
  first [ exact R_trans | exact LAWS | exact Hsegs | exact HJ3 | exact HG | exact HFP
        | (eapply ajournal_gx_G_mono_xR; [exact HGra | exact HJ4])
        | (intros a (r & Hin & _); destruct Hin)
        | (rewrite Usp4; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK; lia) ]. }
cbn [app] in HJ5.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HAR4.
assert (SHOKb : sh_ok SEGS Bxf oaf_SH Eb (mrestrict (w_H W4) mem4))
by (apply (oa_shok i Eb ly4 S4 Hp4 W4 mem4 md4 Hi4 HAR4 HZgs); rewrite OLDb, OLDa by lia; [exact E40 | exact E8]).
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs - 64) by (rewrite OLDb by lia; exact Usp3).
(* R3: a0 = 0, the epilogue, the ret *)
rewrite P1.
psrr_branch_tok RUNG BRR HS SHOKb Bspan.
{ (* bnez a0 -> abort: relay_add returned 0 *)
  exfalso. rewrite ?branch_ne_U, ?branch_eq_U in Hc. rewrite ?(U_atom Eb 68 0 Eb68) in Hc by lia.
  rewrite ?U_SLit in Hc. change (zcanon 0) with 0 in Hc. discriminate Hc. }
paj_run_tok_xR RUNG HS HJ5 SHOKb Bspan. { oa_awr2 Uspb U83 Unfd3 HSL HGnfd. }
rename HFr into HFr3, HG0 into HGr3. clear HF.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HARF.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => let x := fresh "msF" in rename mm into x end.
assert (KF : forall a, aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W4) mem4 a).
{ lazymatch type of HFr3 with frame_of _ ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr3 end.
  intros a. apply aview_eq_of. apply HFr3. intros (r & Hin & Hr). cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]); try destruct Hin; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
prreg HS (1%bv : bv 5) X1. prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
prreg HS (8%bv : bv 5) X8. prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18. prreg HS (19%bv : bv 5) X19.
prreg HS (20%bv : bv 5) X20. prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (23%bv : bv 5) X23.
prreg HS (24%bv : bv 5) X24. prreg HS (25%bv : bv 5) X25. prreg HS (26%bv : bv 5) X26. prreg HS (27%bv : bv 5) X27.
assert (OLDE : forall m, (m < 48)%nat -> ew Eb m = ew E m) by (intros m Hm; rewrite OLDb, OLDa by lia; reflexivity).
assert (EX32 : ew E 32 = getr regs 1) by exact (EX 0%nat ltac:(lia)).
apply (SRr_SRrG SEGS R WLE_R). eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros matf. unfold oa_post_xR, oa_FP. rewrite Hfirst.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists ly4, S4, Hp4, r, m, d, (k2 + 1 + k4) end.
split; [cbn [ms_regs]; rewrite X1, OLDE, EX32 by lia; rewrite Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ5|].
split.
{ apply aregs_preserved_eqs.
  - rewrite X2, Uspb. replace (spZ regs - 64 + 64) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - rewrite X3. exact (eq_trans (OLDE 3%nat ltac:(lia)) (eq_trans (EA 3%nat ltac:(lia)) R3)).
  - rewrite X4. exact (eq_trans (OLDE 4%nat ltac:(lia)) (eq_trans (EA 4%nat ltac:(lia)) R4)).
  - rewrite X8. exact (eq_trans (OLDE 33%nat ltac:(lia)) (EX 1%nat ltac:(lia))).
  - rewrite X9. exact (eq_trans (OLDE 34%nat ltac:(lia)) (EX 2%nat ltac:(lia))).
  - rewrite X18. exact (eq_trans (OLDE 35%nat ltac:(lia)) (EX 3%nat ltac:(lia))).
  - rewrite X19. exact (eq_trans (OLDE 36%nat ltac:(lia)) (EX 4%nat ltac:(lia))).
  - rewrite X20. exact (eq_trans (OLDE 37%nat ltac:(lia)) (EX 5%nat ltac:(lia))).
  - rewrite X21. exact (eq_trans (OLDE 38%nat ltac:(lia)) (EX 6%nat ltac:(lia))).
  - rewrite X22. exact (eq_trans (OLDE 39%nat ltac:(lia)) (EX 7%nat ltac:(lia))).
  - rewrite X23. exact (eq_trans (OLDE 23%nat ltac:(lia)) (eq_trans (EA 23%nat ltac:(lia)) R23)).
  - rewrite X24. exact (eq_trans (OLDE 24%nat ltac:(lia)) (eq_trans (EA 24%nat ltac:(lia)) R24)).
  - rewrite X25. exact (eq_trans (OLDE 25%nat ltac:(lia)) (eq_trans (EA 25%nat ltac:(lia)) R25)).
  - rewrite X26. exact (eq_trans (OLDE 26%nat ltac:(lia)) (eq_trans (EA 26%nat ltac:(lia)) R26)).
  - rewrite X27. exact (eq_trans (OLDE 27%nat ltac:(lia)) (eq_trans (EA 27%nat ltac:(lia)) R27)). }
split.
{ intros a H1 H2 H3 H4. apply (apresent_grows _ _ _ a HGr3). exact (AP4 a H1 H2 H3 (APIMG a H1 H2 H3 H4)). }
(* what relay_add and the epilogue keep, from the call on *)
assert (KRA : forall a, in_img SEGS a -> ~ inG (RA_G fr_globals) a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem msB) a).
{ intros a Him HnG Hno He. rewrite KF.
  exact (oa_call_keep_xR (RA_G fr_globals) RA_STK (spZ (ms_regs msB)) (ra_FP T es) ly3 S3 Hp3 W3 (ms_mem msB) mdB
    ly4 S4 Hp4 W4 mem4 md4 k4 HJ4 Hsk a Him HnG Hno He). }
split.
{ unfold oa_kept, oa_wr. rewrite Hfirst. intros a Ha Hno. destruct (GOK a Ha) as (Him & Hnos & He & _).
  rewrite (KRA a Him ltac:(intros Hr; apply Hno; right; right; exact Hr) Hnos He).
  apply KG3; [exact Ha | intros Hs; apply Hno; left; exact Hs | intros Hn; apply Hno; right; left; exact Hn]. }
split; [rewrite Hfr4, Hfr3, Hfr2; reflexivity|].
split; [exact HRM4|].
(* the slot and g_nfd at the end *)
assert (KSL : forall a, oa_HA i <= a < oa_HA i + 96 ->
  aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem msB) a).
{ intros a Ha. destruct (GOK a (HSL a Ha)) as (Him & Hno & He & _).
  apply (KRA a Him); [intros Hr; pose proof (oa_ra_g a Hr); rewrite HAv in Ha; lia | exact Hno | exact He]. }
assert (KNF : forall a, A_NFD <= a < A_NFD + 4 ->
  aview SEGS (w_H W4) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem msB) a).
{ intros a Ha. destruct (GOK a (HGnfd a Ha)) as (Him & Hno & He & _).
  apply (KRA a Him); [intros Hr; pose proof (oa_ra_g a Hr); unfold A_NFD in Ha; lia | exact Hno | exact He]. }
assert (VS : forall off (w : nat) v, 0 <= off -> off + Z.of_nat w <= 96 ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem msB)) (oa_HA i + off) w v ->
  val_mem SEGS (arm W4 (ms_mem msF)) (oa_HA i + off) w v).
{ intros off w v Ho Hw Hv. apply (val_mem_kept SEGS (w_H W3) (w_H W4) (ms_mem msB) (ms_mem msF) _ w); [|exact Hv].
  intros k Hk. apply KSL. lia. }
assert (HqF : In (q, APARTIAL) (ablocks B ly4 S4)).
{ destruct HTc as [(_ & HP4b) | (_ & _ & HE4)].
  - apply (Permutation_in _ (Permutation_sym HP4b)). right. exact Hqn.
  - rewrite HE4. exact Hqn. }
destruct (oa_new_src_at_x B ARx LAWS ly4 S4 Hp4 W4 (ms_mem msF) _ (oa_HA i) (100 + n0) q HARF HqF ltac:(lia)
  ltac:(intros j Hj; exact (HGW (oa_HA i + j) (HSL (oa_HA i + j) ltac:(unfold ASRC in Hj; lia)) _))
  ltac:(rewrite <- (Z.add_0_r (oa_HA i)); apply VS; [lia | lia | exact VF0])
  ltac:(apply VS; [lia | lia | exact VF4])
  ltac:(apply VS; [lia | lia | exact VF40])
  ltac:(rewrite Forall_forall in VZ |- *; intros p HIp; pose proof (VZ p HIp) as Hv;
        assert (Hb : 0 <= fst p /\ fst p + Z.of_nat (snd p) <= 96)
          by (cbn [In] in HIp; repeat (destruct HIp as [<- | HIp]; [cbn [fst snd]; lia|]); destruct HIp);
        apply VS; [lia | lia | exact Hv])) as (pj & Hsrc).
(* errno: relay_add (ra_post), malloc (its rule) and source_reset (ERR2) keep it; the runs store only to the
   slot's first 48 bytes and g_nfd, which are in G, and gx_rt keeps errno out of G *)
assert (ERRF : forall j, 0 <= j < 4 ->
  aview SEGS (w_H W4) (ms_mem msF) (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)).
{ pose proof (proj1 (pal_env B TL)) as (Ee0 & Ee1).
  intros j Hj.
  assert (Hs : ~ (oa_HA i <= as_errno B + j < oa_HA i + 48)).
  { intros Hs. exact (proj1 (HGRT (as_errno B + j) (HSL (as_errno B + j) ltac:(lia))) ltac:(lia)). }
  assert (Hn : ~ (A_NFD <= as_errno B + j < A_NFD + 4)).
  { intros Hn. exact (proj1 (HGRT (as_errno B + j) (HGnfd (as_errno B + j) Hn)) ltac:(lia)). }
  rewrite KF, (Herr4 j Hj), (KR3 (as_errno B + j) ltac:(lia) Hs Hn), (Herr3 j Hj),
    (KR (as_errno B + j) ltac:(lia) Hs Hn).
  exact (ERR2 j Hj). }
split; [|exact ERRF].
exists q, T', pj.
split; [exact Hsrc|].
split.
{ apply (val_mem_kept SEGS (w_H W3) (w_H W4) (ms_mem msB) (ms_mem msF) _ 4); [|rewrite Z.add_0_r in VN; exact VN].
  intros k Hk. apply KNF. lia. }
assert (KF4 : forall fp, akept W4 mem4 W4 (ms_mem msF) fp).
{ intros fp r Hr a Ha. split; [exact (KF a)|]. intros Hw. exact (writable_at_grows SEGS _ _ a HGr3 Hw). }
split.
{ apply (arelay_at_kept B fr_globals ly4 S4 W4 mem4 ly4 S4 W4 (ms_mem msF) T' _ Hrelay4 (KF4 _)).
  pose proof Hrelay4 as (_ & _ & _ & _ & _ & _ & _ & HTB4 & _ & HE4' & _). rewrite Forall_forall in HE4'.
  intros b Hb. destruct Hb as [<- | Hb]; [exact HTB4|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  exact (oa_eblks_in ly4 S4 W4 mem4 e (HE4' e He) b Hb). }
split; [exact (alock_at_kept fr_globals W4 mem4 W4 (ms_mem msF) false Hlock4 (KF4 _))|].
split.
{ destruct HTc as [(HT0 & HP4b) | (HT0 & HTT & HE4)].
  - left. split; [exact HT0|]. eapply Permutation_trans; [exact HP4b|]. apply perm_skip. rewrite Hbl3.
    eapply Permutation_trans; [apply Permutation_app_tail; exact HP2|]. apply Permutation_sym, Permutation_cons_append.
  - right. split; [exact HT0|]. split; [exact HTT|]. rewrite HE4, Hbl3.
    eapply Permutation_trans; [apply Permutation_app_tail; exact HP2|]. apply Permutation_sym, Permutation_cons_append. }
pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia)) as M1. pose proof (mo_free_nonneg MT MLAW) as M2.
apply (mle_weaken MT S S4 _ oa_cost MLAW (mle_station MT S S3 S4 _ _ MLAW Hmle23 Hmle4)).
unfold oa_cost, ra_cost. destruct (T =? 0); lia.
Qed.

(* From the source_reset call (0x84fa4) on, for the slot i op_add opens: source_reset at the slot's own G, then
   oa_tail_xR. *)
(* :1601 oa_found *)
Lemma oa_found_xR : forall (i : nat) W ly S Hp regs mem md ch os n0 T es regs0 mem0 md0 k0 (kr : nat),
oa_first os = Some i -> nth i os 0 = 0 ->
afn_pre_x SEGS B ARx OA_STK ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
count_cid 0 (frames S) < fs_frames 0 ->
asrc_closed W mem (oa_HA i) ->
val_mem SEGS (arm W mem) A_NFD 4 n0 -> 0 <= n0 <= 512 ->
azs B (rg_s fr_globals) (4 * ASRC) ->
(forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG G a) ->
(forall a, A_NFD <= a < A_NFD + 4 -> inG G a) ->
(forall a, inG (RA_G fr_globals) a -> inG G a) ->
ra_rel B fr_globals ly S W mem T es ->
alock_at fr_globals W mem false -> awake_at fr_globals W mem -> rom_view SEGS W mem ->
(length es < 4)%nat -> ~ In (100 + n0) (map re_fd es) ->
blocks_bytes S + APARTIAL + ATABLE <= LIVE_MAX -> mo_ok MT S oa_cost ->
rp_RM RP S (oa_rk + kr)%nat -> cnt_ok_pk RP oa_peak (ablocks B ly S) ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] OA_STK (spZ regs) (oa_FP os T es) ly S Hp W mem md [] ly S Hp W mem0 md0 k0 ->
oa_kept_fr W (spZ regs) mem mem0 -> apres_kept B W mem W mem0 ->
getr regs0 1 = Z_to_bv 64 (BASE + A_oaf) -> getr regs0 2 = Z_to_bv 64 (spZ regs - 64) ->
getr regs0 3 = getr regs 3 -> getr regs0 4 = getr regs 4 ->
getr regs0 8 = Z_to_bv 64 (oa_HA i) -> getr regs0 10 = Z_to_bv 64 (oa_HA i) ->
getr regs0 19 = Z_to_bv 64 (SB + (oa_HA i + 4) / 8) -> getr regs0 20 = Z_to_bv 64 (rg_s fr_globals) ->
getr regs0 21 = Z_to_bv 64 (- (SB + 12 * Z.of_nat i)) ->
getr regs0 23 = getr regs 23 -> getr regs0 24 = getr regs 24 -> getr regs0 25 = getr regs 25 ->
getr regs0 26 = getr regs 26 -> getr regs0 27 = getr regs 27 ->
Forall (fun p => val_mem SEGS (arm W mem0) (spZ regs - 64 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) oa_saved ->
SRrG SEGS R W (mkCfg (mkst regs0 (Z_to_bv 64 (BASE + AF_fr_source_reset)) mem0 (seg_rom SEGS)) md0)
  (oa_post_xR PST ARx R RP regs ly S Hp W mem md os n0 T es kr).
Proof.
intros i W ly S Hp regs mem md ch os n0 T es regs0 mem0 md0 k0 kr Hfirst Hc0 HPRE Hal32 Hcid ACL0 Hnfd Hn0 HZgs
HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT HJ KEEP AP
R1 R2 R3 R4 R8 R10 R19 R20 R21 R23 R24 R25 R26 R27 SAVED.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hi4 : (i < 4)%nat).
{ unfold oa_first in Hfirst.
  destruct (nth 0 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 1 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 2 os 0 =? 0); [injection Hfirst as <-; lia|].
  destruct (nth 3 os 0 =? 0); [injection Hfirst as <-; lia | discriminate]. }
assert (HAv : oa_HA i = 6129888 + 96 * Z.of_nat i) by (unfold oa_HA, ASRC, fr_globals, rg_s; lia).
assert (HAr : rg_s fr_globals <= oa_HA i /\ oa_HA i + ASRC <= rg_s fr_globals + 4 * ASRC)
by (rewrite HAv; unfold ASRC, fr_globals, rg_s; lia).
assert (GOK : forall a, inG G a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ 0 <= a < kLowMemEnd).
{ intros a Ha. destruct (HG a Ha) as (Him & Hno & _). destruct (HGRT a Ha) as [He _].
  pose proof (Hsegs a Him). split; [exact Him|]. split; [exact Hno|]. split; [exact He | lia]. }
assert (Hfr : forall a, 0 <= a < kLowMemEnd -> ~ (spZ regs - OA_FRAME <= a < spZ regs)).
{ intros a Ha [HA1 HB1]. unfold OA_FRAME, OA_STK, RA_STK, RA_FRAME, ASTACK, kLowMemEnd in *. lia. }
unfold oa_FP in HJ. rewrite Hfirst in HJ.
(* the slot as source_reset finds it: closed *)
assert (ABK : forall a, oa_HA i <= a < oa_HA i + ASRC -> abyte_kept W mem W mem0 a).
{ intros a Ha. destruct (GOK a (HGgs a ltac:(lia))) as (Him & Hno & He & Hlo). split.
  - apply KEEP; [lia | exact (Hfr a Hlo)].
  - apply writable_kept. intros Hpa. exact (AP a Him Hno He Hpa). }
assert (ACL : asrc_closed W mem0 (oa_HA i)).
{ destruct ACL0 as [HGZ HWR]. split.
  - apply (akept_garr8 W mem W mem0 (oa_HA i) (repeat 0 (Z.to_nat ASRC))); [|exact HGZ].
    intros x Hx. apply ABK. rewrite repeat_length in Hx. unfold ASRC in *. lia.
  - apply (akept_awr W mem W mem0 (oa_HA i) ASRC); [intros x Hx; apply ABK; lia | exact HWR]. }
(* source_reset at the slot's own globals *)
pose (G1 := [(oa_HA i, ASRC)]).
assert (HinGs1 : forall a, inG G1 a -> oa_HA i <= a < oa_HA i + ASRC).
{ intros a Ha. apply inG_cons in Ha as [Hz | Hz]; [unfold in_zr in Hz; cbn [fst snd] in Hz; lia
  | exfalso; exact (inG_nil a Hz)]. }
assert (HGP1 : gx_prog_x B ARx G1).
{ apply (gx_prog_sub_x B ARx G1 G); [|exact HGP]. intros a Ha. apply HGgs. pose proof (HinGs1 a Ha). lia. }
pose proof (proj1 HGP1) as HGok1.
pose proof HJ as (HSTK0 & HXO0 & (memS0 & HJi0 & HAG0) & HOUT0).
rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRc & _).
assert (Hspc : spZ regs0 = spZ regs - 64)
by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (HPREc : afn_pre_x SEGS B ARx SR_STK ly S Hp W regs0 mem0 md0 []).
{ split; [eapply ajournal_gx_AR_xR; exact HJ|].
  split; [rewrite R1; apply ret_ok_codeptr_v; [unfold A_oaf, A_op_add, AF_fr_op_add; lia | reflexivity]|].
  split; [unfold raZ; rewrite R1, unsigned_lit_small by (unfold A_oaf, A_op_add, AF_fr_op_add; lia);
          unfold A_oaf, A_op_add, AF_fr_op_add; lia|].
  split; [rewrite R3; exact Hgp|].
  split; [rewrite R4; exact Htp|].
  split.
  { rewrite Hspc. unfold astk_ok, SR_STK, LF_STK, OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK in *.
    split; [replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
    repeat split; lia. }
  split.
  { intros a Ha. apply HPRc. rewrite Hspc in Ha.
    unfold SR_STK, LF_STK, OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK in *. lia. }
  split; [|exact HQT].
  apply achain_low. unfold s0Z. rewrite R8, unsigned_lit_small by lia. lia. }
(* the room round: oa_rk = 7, of which source_reset at None charges 4 (four free(NULL)) *)
assert (Hrk : oa_rk = 7%nat) by reflexivity.
assert (Hsr4 : Z.to_nat (sr_cost MT_rk None) = 4%nat) by reflexivity.
eapply (SRrG_bind SEGS R R_trans).
{ exact (SR_R G1 HGP1 W ly S Hp regs0 mem0 md0 [] (oa_HA i) None HPREc R10
    ltac:(unfold oa_HA, ASRC; cbn [fr_globals rg_s]; clear; rewrite Z.add_mod, Z.mul_mod by lia; reflexivity) ACL
    ltac:(intros a Ha; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia)
    ltac:(destruct HZgs as (r & Hin & H8 & Hlo & Hhi); exists r; split; [exact Hin|]; split; [exact H8|]; lia)
    ltac:(eapply ajournal_gx_rom_view_xR; first [exact Hsegs | exact LAWS | exact HJ | exact HRO | exact oa_pstr | exact Hrom])
    ltac:(apply (mok_station MT S S oa_cost 0 (sr_cost MT None) MLAW Hmok (mle_start MT S MLAW));
          [unfold sr_cost; pose proof (mo_free_nonneg MT MLAW); lia
          | unfold oa_cost; pose proof (mo_malloc_nonneg MT MLAW APARTIAL ltac:(unfold APARTIAL; lia));
            pose proof (mo_malloc_nonneg MT MLAW ATABLE ltac:(unfold ATABLE; lia));
            pose proof (mo_free_nonneg MT MLAW); lia])
    (3 + kr)%nat
    ltac:(rewrite Hsr4; rewrite Hrk in HRM; exact HRM)
    (oa_cnt_perm (fun _ => 0%nat) _ _ (Permutation_refl _) ltac:(intros P; cbv beta; lia) HCNT)). }
cbv beta. intros W2 c2 Hwle2
  (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk2 & -> & HJ2 & Hpres2 & ACL2 & Hperm2 & AP2 & Herr2 & Hfr2 & Hmle2 & HRM2).
(* the callee's journal, at the caller's G *)
assert (HJ3 : ajournal_gx_xR SEGS B PST ARx R G 0 [] OA_STK (spZ regs) (ra_FP T es) ly S Hp W mem md ([] ++ []) ly2 S2 Hp2 W2 mem2 md2 (k0 + kk2)).
{ eapply ajournal_gx_sub_xR;
  first [ exact R_trans | exact LAWS | exact Hsegs | exact HJ | exact HG
        | (eapply ajournal_gx_G_mono_xR; [intros a Ha; apply HGgs; pose proof (HinGs1 a Ha); lia | exact HJ2])
        | (intros a (r & Hin & _); destruct Hin)
        | (rewrite Hspc; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, SR_STK, LF_STK, ASTACK; lia) ]. }
cbn [app] in HJ3.
assert (AP3 : apres_kept B W mem W2 mem2) by (intros a H1 H2 H3 H4; apply AP2; auto; apply AP; auto).
assert (HP2 : Permutation (ablocks B ly2 S2) (ablocks B ly S)) by exact (Hperm2 _ (Permutation_refl _)).
(* what source_reset keeps *)
assert (KSR : forall a, in_img SEGS a -> ~ inG G1 a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Him HnG Hno He.
  rewrite (oa_call_keep_xR G1 SR_STK (spZ regs0) _ ly S Hp W mem0 md0 ly2 S2 Hp2 W2 mem2 md2 kk2 HJ2
    ltac:(intros (r & Hin & _); destruct Hin) a Him HnG Hno He).
  pose proof (Hsegs a Him) as Hlo. apply KEEP; [unfold kLowMemEnd in *; lia | exact (Hfr a Hlo)]. }
assert (GK2 : forall a, inG G a -> ~ (oa_HA i <= a < oa_HA i + ASRC) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hns. destruct (GOK a Ha) as (Him & Hno & He & _).
  apply KSR; [exact Him | intros Hin; exact (Hns (HinGs1 a Hin)) | exact Hno | exact He]. }
(* errno: source_reset keeps it (sr_post), and the runs before the call keep every byte outside the frame *)
assert (ERR2 : forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) mem (as_errno B + j)).
{ pose proof (proj1 (pal_env B TL)) as (Ee0 & Ee1).
  intros j Hj. rewrite (Herr2 j Hj). apply KEEP; [lia | apply Hfr; lia]. }
assert (WK2 : forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (HWK a Ha) as (Him & Hno & He).
  apply KSR; [exact Him | intros Hin; pose proof (HinGs1 a Hin) as Hs; rewrite HAv in Hs;
    unfold fr_globals, rg_wake in Ha; lia | exact Hno | exact He]. }
assert (BK2 : forall b n j, In (b, n) (ablocks B ly S) -> 0 <= j < req_size n ->
  aview SEGS (w_H W2) mem2 (b + j) = aview SEGS (w_H W) mem (b + j)).
{ intros b n j Hb Hj.
  rewrite (oa_call_keep_blk_xR G1 SR_STK (spZ regs0) _ ly S Hp W mem0 md0 ly2 S2 Hp2 W2 mem2 md2 kk2 HGok1 HJ2 b n j Hb
    (Permutation_in _ (Permutation_sym HP2) Hb) Hj ltac:(intros (r & Hin & _); destruct Hin)).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n HAR Hb) as (_ & H4096 & Hbc & _).
  apply KEEP; [lia | intros [HA1 HB1]; unfold OA_STK, OA_FRAME, RA_STK, RA_FRAME, ASTACK in *; lia]. }
(* the frame is above source_reset's window *)
assert (SAVED2 : Forall (fun p => val_mem SEGS (arm W2 mem2) (spZ regs - 64 + fst p) 8
  (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) oa_saved).
{ rewrite Forall_forall in SAVED |- *. intros p HIp. pose proof (SAVED p HIp) as Hv.
  assert (Hoff : 0 <= fst p <= 56) by (unfold oa_saved in HIp; cbn [In] in HIp;
    repeat (destruct HIp as [HIp | HIp]; [subst p; cbn [fst]; lia|]); destruct HIp).
  apply (val_mem_kept SEGS (w_H W) (w_H W2) mem0 mem2 _ 8); [|exact Hv]. intros kk Hk.
  apply (oa_call_keep_hi_xR G1 SR_STK (spZ regs0) _ ly S Hp W mem0 md0 ly2 S2 Hp2 W2 mem2 md2 kk2 HGok1 HJ2);
  rewrite ?Hspc; unfold SR_STK, LF_STK, OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK in *; lia. }
(* g_nfd still holds n0, and its bytes are still writable *)
assert (NFDK : forall a, A_NFD <= a < A_NFD + 4 -> abyte_kept W mem W2 mem2 a).
{ intros a Ha. destruct (GOK a (HGnfd a Ha)) as (Him & Hno & He & Hlo). split.
  - apply GK2; [exact (HGnfd a Ha) | rewrite HAv; unfold A_NFD in *; lia].
  - apply (oa_writable_img W W2 mem mem2 a Him). intros Hpa. exact (AP3 a Him Hno He Hpa). }
assert (KN : val_mem SEGS (arm W2 mem2) A_NFD 4 n0).
{ apply (akept_vm W mem W2 mem2 A_NFD 4%nat n0); [|exact Hnfd]. intros x Hx. apply NFDK. lia. }
assert (NFDW : awr W2 mem2 A_NFD 4).
{ intros j Hj. exact (HGW (A_NFD + j) (HGnfd (A_NFD + j) ltac:(lia)) _). }
rewrite R1.
apply (oa_tail_xR i W ly S Hp regs mem md ch os n0 T es W2 ly2 S2 Hp2 regs2 mem2 md2 (k0 + kk2) kr Hfirst HPRE Hal32 Hcid Hn0
  Hes4 Hfd HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hlive Hmok HRM2 HCNT HJ3 AP3 GK2 WK2 ERR2 BK2 HP2 Hfr2 Hmle2 ACL2 KN NFDW
  (eq_trans (Hpres2 2 ltac:(unfold acallee_saved; lia)) R2) (eq_trans (Hpres2 3 ltac:(unfold acallee_saved; lia)) R3)
  (eq_trans (Hpres2 4 ltac:(unfold acallee_saved; lia)) R4) (eq_trans (Hpres2 8 ltac:(unfold acallee_saved; lia)) R8)
  (eq_trans (Hpres2 19 ltac:(unfold acallee_saved; lia)) R19) (eq_trans (Hpres2 20 ltac:(unfold acallee_saved; lia)) R20)
  (eq_trans (Hpres2 21 ltac:(unfold acallee_saved; lia)) R21) (eq_trans (Hpres2 23 ltac:(unfold acallee_saved; lia)) R23)
  (eq_trans (Hpres2 24 ltac:(unfold acallee_saved; lia)) R24) (eq_trans (Hpres2 25 ltac:(unfold acallee_saved; lia)) R25)
  (eq_trans (Hpres2 26 ltac:(unfold acallee_saved; lia)) R26) (eq_trans (Hpres2 27 ltac:(unfold acallee_saved; lia)) R27)
  SAVED2).
Qed.
(* :1812 pb_op_add_x *)
Theorem pb_op_add_xR : oa_spec_xR PST ARx R RP A_op_addP.
Proof.
intros W ly S Hp regs mem md ch os n0 T es HPRE Hal32 Hcid Hlen Hrng Hcells Hclosed Hnfd Hn0
HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hfree Hlive Hmok kr HRM HCNT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (oa_entry W ly S Hp regs mem md ch os n0 HPRE Hlen Hrng Hcells Hnfd Hn0 HZgs) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] OA_STK (oa_FP os T es) ly S Hp W regs mem md ch HPRE
  ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (oa_extra os n0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (oa_extra os n0)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EA : forall r, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec r 32); [reflexivity | lia]. }
assert (E32 : ew E 32 = Z_to_bv 64 (nth 0 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (nth 1 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nth 2 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (nth 3 os 0)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E37 : ew E 37 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E263 : ew E 263 = Z_to_bv 64 (rg_s fr_globals))
by (subst E; rewrite <- HGS; apply (Eimg_img _ (A_OBJ 22)); unfold A_OBJ, A_TEXT, A_LIM; lia).
clear HE.
unfold cfg_at. change (w64 A_op_addP) with (Z_to_bv 64 A_op_addP). unfold A_op_addP, A_op_add.
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr0 Usp. }
assert (AP : apres_kept B W mem W mem) by (intros a _ _ _ Ha; exact Ha).
assert (KEEP : oa_kept_fr W (spZ regs) mem mem) by (intros a _ _; reflexivity).
oa_pres AP. oa_keep KEEP Usp.
(* the loop: trip i reads g_s[i].open; the first zero flag leaves it for oa_found_xR *)
psrr_branch_tok RUNG BRR HS SHOK Bspan.
- oa_flag Hc E32 0%nat Hrng. apply Z.eqb_eq in Hc.
  assert (Hfirst : oa_first os = Some 0%nat)
  by (unfold oa_first; rewrite (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
  paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan AF_fr_source_reset. { oa_awr0 Usp. }
  oa_pres AP. oa_keep KEEP Usp. repeat rewrite wvb_collapse in HJ. pmkst HS.
  destruct (Hfree ltac:(rewrite Hfirst; discriminate)) as [Hes4 Hfd].
  apply (oa_found_xR 0%nat W ly S Hp regs mem md ch os n0 T es _ _ _ _ kr Hfirst Hc HPRE Hal32 Hcid
    (Hclosed 0%nat ltac:(lia) Hc) Hnfd Hn0 HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT
    HJ KEEP AP);
  lazymatch goal with |- Forall _ _ => oa_found_frame HS EA Usp | |- _ => oa_found_reg HS EA Usp E37 E263 HEI end.
- oa_flag Hc E32 0%nat Hrng. apply Z.eqb_neq in Hc. rename Hc into Hnz0.
  paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
  oa_bump HS 4 E37 E263.
  paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
  psrr_branch_tok RUNG BRR HS SHOK Bspan.
  + oa_flag Hc E33 1%nat Hrng. apply Z.eqb_eq in Hc.
    assert (Hfirst : oa_first os = Some 1%nat)
    by (unfold oa_first; rewrite (proj2 (Z.eqb_neq _ _) Hnz0), (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
    paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan AF_fr_source_reset. { oa_awr0 Usp. }
    oa_pres AP. oa_keep KEEP Usp. repeat rewrite wvb_collapse in HJ. pmkst HS.
    destruct (Hfree ltac:(rewrite Hfirst; discriminate)) as [Hes4 Hfd].
    apply (oa_found_xR 1%nat W ly S Hp regs mem md ch os n0 T es _ _ _ _ kr Hfirst Hc HPRE Hal32 Hcid
      (Hclosed 1%nat ltac:(lia) Hc) Hnfd Hn0 HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT
      HJ KEEP AP);
    lazymatch goal with |- Forall _ _ => oa_found_frame HS EA Usp | |- _ => oa_found_reg HS EA Usp E37 E263 HEI end.
  + oa_flag Hc E33 1%nat Hrng. apply Z.eqb_neq in Hc. rename Hc into Hnz1.
    paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
    oa_bump HS 100 E37 E263.
    paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
    psrr_branch_tok RUNG BRR HS SHOK Bspan.
    * oa_flag Hc E34 2%nat Hrng. apply Z.eqb_eq in Hc.
      assert (Hfirst : oa_first os = Some 2%nat)
      by (unfold oa_first; rewrite (proj2 (Z.eqb_neq _ _) Hnz0), (proj2 (Z.eqb_neq _ _) Hnz1), (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
      paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan AF_fr_source_reset. { oa_awr0 Usp. }
      oa_pres AP. oa_keep KEEP Usp. repeat rewrite wvb_collapse in HJ. pmkst HS.
      destruct (Hfree ltac:(rewrite Hfirst; discriminate)) as [Hes4 Hfd].
      apply (oa_found_xR 2%nat W ly S Hp regs mem md ch os n0 T es _ _ _ _ kr Hfirst Hc HPRE Hal32 Hcid
        (Hclosed 2%nat ltac:(lia) Hc) Hnfd Hn0 HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT
        HJ KEEP AP);
      lazymatch goal with |- Forall _ _ => oa_found_frame HS EA Usp | |- _ => oa_found_reg HS EA Usp E37 E263 HEI end.
    * oa_flag Hc E34 2%nat Hrng. apply Z.eqb_neq in Hc. rename Hc into Hnz2.
      paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
      oa_bump HS 196 E37 E263.
      paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
      psrr_branch_tok RUNG BRR HS SHOK Bspan.
      -- oa_flag Hc E35 3%nat Hrng. apply Z.eqb_eq in Hc.
       assert (Hfirst : oa_first os = Some 3%nat)
       by (unfold oa_first; rewrite (proj2 (Z.eqb_neq _ _) Hnz0), (proj2 (Z.eqb_neq _ _) Hnz1), (proj2 (Z.eqb_neq _ _) Hnz2), (proj2 (Z.eqb_eq _ _) Hc); reflexivity).
       paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan AF_fr_source_reset. { oa_awr0 Usp. }
       oa_pres AP. oa_keep KEEP Usp. repeat rewrite wvb_collapse in HJ. pmkst HS.
       destruct (Hfree ltac:(rewrite Hfirst; discriminate)) as [Hes4 Hfd].
       apply (oa_found_xR 3%nat W ly S Hp regs mem md ch os n0 T es _ _ _ _ kr Hfirst Hc HPRE Hal32 Hcid
         (Hclosed 3%nat ltac:(lia) Hc) Hnfd Hn0 HZgs HGgs HGnfd HGra Hrel Hlock Hwake Hrom Hes4 Hfd Hlive Hmok HRM HCNT
         HJ KEEP AP);
       lazymatch goal with |- Forall _ _ => oa_found_frame HS EA Usp | |- _ => oa_found_reg HS EA Usp E37 E263 HEI end.
      -- oa_flag Hc E35 3%nat Hrng. apply Z.eqb_neq in Hc. rename Hc into Hnz3.
         (* every slot is open: the loop ends and op_add returns with nothing changed *)
         paj_run_tok_xR RUNG HS HJ SHOK Bspan. { oa_awr0 Usp. } oa_pres AP. oa_keep KEEP Usp.
         assert (Hfz : oa_first os = None).
         { unfold oa_first. rewrite (proj2 (Z.eqb_neq _ _) Hnz0), (proj2 (Z.eqb_neq _ _) Hnz1),
           (proj2 (Z.eqb_neq _ _) Hnz2), (proj2 (Z.eqb_neq _ _) Hnz3). reflexivity. }
         prreg HS (1%bv : bv 5) R1.
         apply (SRr_SRrG SEGS R WLE_R). eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
         intros mat'. unfold oa_post_xR. rewrite Hfz.
         lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
           exists ly, S, Hp, r, m, d, 0 end.
         split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
         split; [apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ|].
         split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (oa_extra os n0) HS);
                 [exact HAE | vm_compute; reflexivity]|].
         split; [exact AP|].
         split; [intros a HaG _; pose proof (Hsegs a (proj1 (HG a HaG))) as Hlo;
                 apply KEEP; [unfold kLowMemEnd in Hlo; lia
                 | intros [HA1 HB1]; unfold OA_FRAME, OA_STK, RA_STK, RA_FRAME, ASTACK, kLowMemEnd in *; lia]|].
         split; [reflexivity|].
         (* the room round: no allocator call on this arm, so the budget only shrinks (RMM) *)
         split; [exact (RMM S kr (oa_rk + kr)%nat ltac:(lia) HRM)|].
         split.
         { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           intros a Ha Hno. apply KEEP; [exact Ha|].
           intros [HA1 HB1]. apply Hno.
           unfold OA_STK, RA_STK, RA_FRAME, OA_FRAME, ASTACK in *. lia. }
         (* errno: outside op_add's frame (api_env puts it below kLowMemEnd) *)
         pose proof (proj1 (pal_env B TL)) as (Ee0 & Ee1).
         intros j Hj. apply KEEP; [lia|].
         intros [HA1 HB1]. unfold OA_FRAME in *. lia.
Qed.
End wR.
End x.

(* ---------------- pb_op_add, re-derived (CONVERSION.md (sha256 1015972e02a9; internal record) 3.): its statement is the AR walk's, now a corollary of
   pb_op_add_x at ARx := ARi0 (cgif's AR with the head set empty), PST := [].  The Section takes LX0 (the laws at ARi0,
   a Theorem Labs lane's rulings (a) and HP0) in place of LAWS (the instance builds it once: W_journal_x.AR_laws_x_ARi0
   (YCbqG.AR_laws_x_of_AR ..)), and the caller-context malloc rule amalloc_cf_rule_c with its trace HCTX_oa_malloc in
   place of amalloc_cf_rule.  The bridges: oa_spec_x_AR0 below (this file's contract), W_contract_x's
   gx_prog_x_ARi0_of / sr_spec_g_x_of_AR0 / ra_spec_g_x_of_AR0, W_journal_x's amalloc_cf_rule_c_x_of_AR0 and
   ARi0_hp0; HPST holds at PST := []. ---------------- *)
(* the conclusion direction for op_add's contract: the generic post / spec at ARi0 give oa_post / oa_spec *)
Lemma oa_post_x_AR0 : forall regs ly S Hp W mem md os n0 T es kr W' c',
oa_post_x [] (ARi0 SEGS B) RP_AR regs ly S Hp W mem md os n0 T es kr W' c' -> oa_post regs ly S W mem md os n0 T es W' c'.
Proof.
intros regs ly S Hp W mem md os n0 T es kr W' c'
  (ly' & S' & Hp' & regs' & mem' & md' & kk & Hc & HJ & Hpr & Hak & Hok & Hfr & _ & Hr).
exists ly', S', regs', mem', md', kk. split; [exact Hc|]. split; [|exact (conj Hpr (conj Hak (conj Hok (conj Hfr Hr))))].
eapply ajournal_gx_x_ARi0_AR. exact HJ.
Qed.
Lemma oa_spec_x_AR0 : forall pc, oa_spec_x [] (ARi0 SEGS B) RP_AR pc -> oa_spec pc.
Proof.
intros pc H W ly S regs mem md ch os n0 T es HPRE. intros.
pose proof (afn_pre_x_ARi0_of_AR SEGS B _ _ _ _ _ _ _ _ HPRE) as HPRE0.
(* the room round: at RP_AR the room and the counts hold trivially (budget 0) *)
eapply SRr_mono.
{ eapply (H W ly S [] regs mem md ch os n0 T es HPRE0); try eassumption;
  first [exact (rp_RM_AR S (oa_rk + 0)) | apply cnt_ok_pk_AR; cbv; lia]. }
intros W' c' _ Hq. exact (oa_post_x_AR0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hq).
Qed.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : APARTIAL < MMAX.
(* op_add's own G: W_contract.v gx_prog *)
Hypothesis HGP : gx_prog B G.
(* the two globals op_add names, at the pinned placement (W_img.v PB_fr decides both by vm_compute) *)
Hypothesis HGS : VAL (A_OBJ 22) = rg_s fr_globals.
Hypothesis HNFD : VAL (A_OBJ 29) = A_NFD.
(* the auipc that g_nfd's store goes through: the listing fixes the load's object but not the store's
   base, so the walk takes the one equation (vm_compute at PB_fr: 0x5d8fa8 = 0x5d8820 + 1928) *)
Hypothesis HHI92 : VAL (A_HI 92) = A_NFD + 1928.
(* g_s and g_nfd miss the GOT slot of the shadow base and the shadow cell, so the entry's symbolic regions are
   disjoint (vm_compute at PB_fr) *)
Hypothesis HOAD :
(VAL (A_OBJ 0) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 0) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 32) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 32)) /\
(VAL (A_OBJ 32) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 32)).
(* g_wake[1] (awake_at) is an image byte outside the allocator's statics and errno, so the source_reset and malloc
   calls before relay_add keep it (it is not in G: op_add never writes it; vm_compute at PB_fr) *)
Hypothesis HWK : forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* the allocator rules' caller-context tables, as in Section x: malloc's CTX_M with its trace HCTX_oa_malloc, relay_add's
   realloc table CTX_R with its trace HCTXRA *)
Variable CTX_M : list (list Z).
Hypothesis HCTX_oa_malloc : In [BASE + AF_fr_op_add + 0xcc] CTX_M.
Hypothesis AMA : amalloc_cf_rule_c SEGS B MT MMAX CTX_M.
Hypothesis SR : sr_spec_g B MT (BASE + AF_fr_source_reset).
Variable CTX_R : list (list Z).
Hypothesis HCTXRA : In [BASE + AF_fr_relay_add + 332; BASE + AF_fr_op_add + 264] CTX_R.
Hypothesis RA : ra_spec_g B MT fr_globals CTX_R (BASE + AF_fr_relay_add).
Theorem pb_op_add : oa_spec A_op_addP.
Proof.
apply oa_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
pose proof (gx_prog_x_ARi0_of B G HGP) as HGPx.
pose proof (amalloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX_M AMA) as AMAx.
pose proof (sr_spec_g_x_of_AR0 B MT _ SR) as SRx.
pose proof (ra_spec_g_x_of_AR0 B MT fr_globals CTX_R _ RA) as RAx.
(* the room round: RMM at RP_AR *)
assert (RMMx : forall S k k', (k <= k')%nat -> rp_RM RP_AR S k' -> rp_RM RP_AR S k)
by (intros S k k' _ _; exact (rp_RM_AR S k)).
eapply pb_op_add_x; eassumption.
Qed.
End c.
(* op_add's G-generic form, taken at op_add's OWN G like lf_spec_g / sr_spec_g (W_contract.v gx_prog); W8 copies it
   as oa_spec_g in W_LLVMFuzzerTestOneInput_pro.v. *)
Definition oa_spec_g (B : asyms) (MT : ameter_ops) (pc : Z) : Prop := forall G, gx_prog B G -> oa_spec B MT G pc.
(* its generic twin, over ARx (W_contract_x.v's argument order: PST ARx right after B) *)
Definition oa_spec_g_x (B : asyms) (PST : list (Z * Z))
(ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop) (MT : ameter_ops) (RP : roomp)
(pc : Z) : Prop :=
forall G, gx_prog_x B ARx G -> oa_spec_x B MT G PST ARx RP pc.
(* route R: oa_spec_g_x at a world relation R (R right after ARx, NAMES.md (sha256 4a0eb3e6fe06; internal record)) *)
Definition oa_spec_g_xR (B : asyms) (PST : list (Z * Z))
(ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
(R : world SEGS -> world SEGS -> Prop) (MT : ameter_ops) (RP : roomp) (pc : Z) : Prop :=
forall G, gx_prog_x B ARx G -> oa_spec_xR B MT G PST ARx R RP pc.
Lemma oa_spec_g_x_wle : forall B PST ARx MT RP, oa_spec_g_x B PST ARx MT RP = oa_spec_g_xR B PST ARx (@wle SEGS) MT RP.
Proof. reflexivity. Qed.
Lemma oa_spec_g_xR_of_x : forall B PST ARx MT RP (R : world SEGS -> world SEGS -> Prop),
  (forall W W', wle W W' -> R W W') -> forall pc, oa_spec_g_x B PST ARx MT RP pc -> oa_spec_g_xR B PST ARx R MT RP pc.
Proof. intros B PST ARx MT RP R WLE_R pc H G HG. exact (oa_spec_xR_of_x B MT G PST ARx RP R WLE_R pc (H G HG)). Qed.
(* pb_op_add_x at every G op_add may be taken at; its other premises are B-level (the laws, the call-site rules), the
   image off PST, or closed facts of the placement PB_fr (HGS, HNFD, HHI92, HOAD), of the instance (HWK) and of the
   caller-context tables (CTX_M with HCTX_oa_malloc: op_add's malloc trace; CTX_R with HCTXRA: relay_add's realloc
   trace when op_add calls it; vm_compute at the instance's tables) *)
Theorem pb_op_add_g_x : forall (B : asyms) (PST : list (Z * Z))
(ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop) (hl : Z) (MT : ameter_ops)
(RP : roomp),
AR_laws_x SEGS B ARx hl -> (forall a, in_img SEGS a -> ~ Exists (in_zr a) PST) -> PALib B -> ameter_laws MT ->
(forall S k k', (k <= k')%nat -> rp_RM RP S k' -> rp_RM RP S k) ->
forall MMAX, APARTIAL < MMAX ->
VAL (A_OBJ 22) = rg_s fr_globals -> VAL (A_OBJ 29) = A_NFD -> VAL (A_HI 92) = A_NFD + 1928 ->
(VAL (A_OBJ 0) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 0) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 32) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 32)) /\
(VAL (A_OBJ 32) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 32)) ->
(forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
 in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
forall CTX_M : list (list Z), In [BASE + AF_fr_op_add + 0xcc] CTX_M ->
amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_M ->
sr_spec_g_x B PST ARx MT RP (BASE + AF_fr_source_reset) ->
forall CTX_R : list (list Z), In [BASE + AF_fr_relay_add + 332; BASE + AF_fr_op_add + 264] CTX_R ->
ra_spec_g_x B PST ARx MT RP fr_globals CTX_R (BASE + AF_fr_relay_add) ->
oa_spec_g_x B PST ARx MT RP (BASE + AF_fr_op_add).
Proof.
intros B PST ARx hl MT RP LAWS HPST TL MLAW RMM MMAX HMMAX HGS HNFD HHI92 HOAD HWK CTX_M HCTXM AMA SR CTX_R HCTXRA RA G HGP.
eapply pb_op_add_x; eassumption.
Qed.
(* ---- route R: pb_op_add_g_x at a world relation R (R right after ARx, as oa_spec_g_xR takes it; NAMES.md (sha256 4a0eb3e6fe06; internal record)),
   from pb_op_add_xR.  Against pb_op_add_g_x: R and its laws, RO with RO_ARx, and the three call premises at R
   (amalloc_cf_rule_c_xR .. RO CTX_M R, sr_spec_g_xR, ra_spec_g_xR); every other premise is the strict text's. ---- *)
(* :2033 pb_op_add_g_x *)
Theorem pb_op_add_g_xR : forall (B : asyms) (PST : list (Z * Z))
(ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
(R : world SEGS -> world SEGS -> Prop),
(forall W, R W W) -> (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', @wle SEGS W W' -> R W W') ->
forall (hl : Z) (MT : ameter_ops) (RP : roomp) (RO : (word -> option byte) -> Prop),
(forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem) ->
AR_laws_x SEGS B ARx hl -> (forall a, in_img SEGS a -> ~ Exists (in_zr a) PST) -> PALib B -> ameter_laws MT ->
(forall S k k', (k <= k')%nat -> rp_RM RP S k' -> rp_RM RP S k) ->
forall MMAX, APARTIAL < MMAX ->
VAL (A_OBJ 22) = rg_s fr_globals -> VAL (A_OBJ 29) = A_NFD -> VAL (A_HI 92) = A_NFD + 1928 ->
(VAL (A_OBJ 0) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 0) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 32) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 32)) /\
(VAL (A_OBJ 32) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 32)) ->
(forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
 in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
forall CTX_M : list (list Z), In [BASE + AF_fr_op_add + 0xcc] CTX_M ->
amalloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO CTX_M R ->
sr_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_source_reset) ->
forall CTX_R : list (list Z), In [BASE + AF_fr_relay_add + 332; BASE + AF_fr_op_add + 264] CTX_R ->
ra_spec_g_xR B PST ARx R MT RP fr_globals CTX_R (BASE + AF_fr_relay_add) ->
oa_spec_g_xR B PST ARx R MT RP (BASE + AF_fr_op_add).
Proof.
intros B PST ARx R R_refl R_trans WLE_R hl MT RP RO RO_ARx LAWS HPST TL MLAW RMM MMAX HMMAX HGS HNFD HHI92 HOAD HWK
CTX_M HCTXM AMA_R SR_R CTX_R HCTXRA RA_R G HGP.
eapply pb_op_add_xR with (R := R) (RO := RO); eassumption.
Qed.
(* pb_op_add at every G op_add may be taken at, re-derived: the laws at ARi0 (LX0) and the caller-context malloc rule with
   its trace in place of AR_laws and amalloc_cf_rule; the other premises as before *)
Theorem pb_op_add_g : forall (B : asyms) (MT : ameter_ops),
AR_laws_x SEGS B (ARi0 SEGS B) 0 -> PALib B -> ameter_laws MT ->
forall MMAX, APARTIAL < MMAX ->
VAL (A_OBJ 22) = rg_s fr_globals -> VAL (A_OBJ 29) = A_NFD -> VAL (A_HI 92) = A_NFD + 1928 ->
(VAL (A_OBJ 0) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 0) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 0)) /\
(VAL (A_OBJ 32) + 8 <= rg_s fr_globals \/ rg_s fr_globals + 4 * ASRC <= VAL (A_OBJ 32)) /\
(VAL (A_OBJ 32) + 8 <= A_NFD \/ A_NFD + 4 <= VAL (A_OBJ 32)) ->
(forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
 in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
forall CTX_M : list (list Z), In [BASE + AF_fr_op_add + 0xcc] CTX_M ->
amalloc_cf_rule_c SEGS B MT MMAX CTX_M ->
sr_spec_g B MT (BASE + AF_fr_source_reset) ->
forall CTX_R : list (list Z), In [BASE + AF_fr_relay_add + 332; BASE + AF_fr_op_add + 264] CTX_R ->
ra_spec_g B MT fr_globals CTX_R (BASE + AF_fr_relay_add) ->
oa_spec_g B MT (BASE + AF_fr_op_add).
Proof.
intros B MT LX0 TL MLAW MMAX HMMAX HGS HNFD HHI92 HOAD HWK CTX_M HCTXM AMA SR CTX_R HCTXRA RA G HGP.
eapply pb_op_add; eassumption.
Qed.
End b.
End a.
