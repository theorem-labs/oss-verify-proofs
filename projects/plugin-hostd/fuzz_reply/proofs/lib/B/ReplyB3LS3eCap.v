(* The image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3eCap.v at
   1318828167d3 (sha256 ca64a9d622c0; internal record), WHOLE, row G-BLS-drain:
   the same definitions and lemmas under the same names over
   lib/B's records, at LS := lib/B/ReplyB3LS3c.v fr_LS3c B CALL_ROOM_B /\ lib/B/ReplyLSBo.v fr_OUT /\
   lib/B/ReplyB3LS3e.v fr_ENT B, MMAX := fr_MMAX.  proves no function (kind: invariant lemma).
   CAPOUT_MAX_OUT_MAX4 (A :92, by reflexivity) holds on B because B's out bound is 133,953,540: lib/B/ReplyLSBo.v
   OUT_MAX4 and lib/B/YCfn_cf.v OUT_MAX, the B twin of a Theorem Labs lane's fix (be3d698ebfa, on a Theorem Labs lane's 8963bbb77ad4 and
   on k3's a6411d87d214, both under this tree).  It does NOT hold on the old B top e43cf0c7bef, whose OUT_MAX is
   33,554,430; ls3e_cap_lt_MMAX and fr_LS3c_gone_rig_c4_e read it.
   A -> B SWAPS (as lib/B/ReplyB3LS3Arms.v made them): lib/A AB1v -> lib/B YB1v; Reusable YE01 + lib/A AE2k -> lib/B
   YE01 YE2k; lib/A ACfn -> lib/B YCfn (Required only); lib/A W_* -> lib/B W_* (W_rep's arm, W_frame's
   rdword_of_val_mem, _cut's fr_RG / fr_hblks / OPS_MAX), then ReplyGuardB; lib/A ReplyLS / ReplyLSArms / ReplyRINV ->
   lib/B/ReplyLSB.v, ReplyLSBArms.v (gn_pairs), ReplyRINVB.v; ReplyLS3 / ReplyLS3c -> lib/B/ReplyB3LS3.v /
   ReplyB3LS3c.v; ReplyLS3o (OUT_MAX4, XB, fr_OUT) -> lib/B/ReplyLSBo.v; ReplyLS3e (fr_ENT) -> lib/B/ReplyB3LS3e.v
   (Required, cited qualified); ReplyLS3cTopxRig -> lib/B/ReplyB3LS3cTopxRig.v; ACfn_cf.CALL_ROOM -> the Section
   variable CALL_ROOM_B (lib/B/ReplyLSB.v's ruling; no lemma here reads its value); MMAX: A's WR_MMAX -> fr_MMAX
   (lib/A/CfParamsReply.v, as lib/B/ReplyB3LS3Arms.v; the same value 1,072,693,248).  KF-COUNT B step 3: no lemma
   here reads a meter; A's `Local Notation MT := ameter_triv` (unused) is gone.
   A's header follows; its line numbers are A's. *)
(* A, row #31's R4: `lm_cap m < MMAX` (CfParamsReply.fr_MMAX = WR_MMAX = 2 ^ 30 - 2 ^ 20 = 1,072,693,248) at every
   cut, from LS := fr_LS3c B /\ fr_OUT OM /\ fr_ENT (lib/A/ReplyLS3o.v, lib/A/ReplyLS3e.v) and the entry
   contract's g_capout clause.  proves no function (kind: invariant lemma).

   WHY fr_OUT ALONE DOES NOT GIVE IT.  fr_OUT bounds g_capout by XB + OUT_MAX, and XB is
   blocks_bytes (c_S cx) - blocks_bytes S + bsum (model_blks m): it counts the ENTRY's live bytes, which the
   driver's earlier calls may have left large, and g_capout itself persists across calls (it is a global the
   harness never frees).  So the bound needs one fact about the state the call starts in.

   WHAT fr_ENT ADDS.  Under fr_ENT the entry's blocks are the input block, the entry's harness blocks and THIS
   call's rest, so XB is exactly the entry's harness bytes (ent_XB below):
     XB cx m S = bsum (fr_hblks (c_W cx) (c_mem cx)),
   the relay table it was handed (ATABLE when g_src is not 0) plus the g_out buffer it was handed (g_capout).

   THE ENTRY CLAUSE AS IT LANDED on W8's room head 3250b98efc5 (3250b98efc532f6fa3a60ea8ec1796ce187cbf07):
   lib/A/W_LLVMFuzzerTestOneInput_cut.v:181 `Definition CAPOUT_MAX : Z := 4 * (OPS_MAX - 1) * 65535.`, and LAST in
   fr_lib_pre_cf (:213) and in its post (:233), at the call's world and memory:
     exists c, val_mem segs (arm W mem) (rg_capout fr_RG) 8 c /\ c <= CAPOUT_MAX
   There segs is _cut.v:140 `Local Notation segs := tfibsegs` (Section cf) and arm is W_rep.v:71
   `arm W mem := mrestrict (w_H W) mem`; this worktree's W_rep.v:71 is the same definition.  ent_capout_ok below is
   that text word for word, so the cut's conjunct plugs by `exact`.

   IT BOUNDS NOTHING (ent_capout_ok_any, Qed).  val_mem stores the LOW 64 bits of c: its bytes are le_byte c 8 k,
   and le_byte reduces c mod 2 ^ 64 (Reusable/YG0f.v:263).  So whatever 8-byte value v g_capout holds, c := v - 2 ^ 64
   reads the same bytes and is negative, hence <= CAPOUT_MAX.  The bound is therefore NOT provable from the
   landed clause: at the first head lm_cap m is the entry's cap, and fr_LS3c / fr_OUT / fr_ENT all hold with an
   entry g_capout of, say, 2 ^ 32 (blocks_bytes (c_S cx) + CALL_ROOM <= LIVE_MAX allows entry blocks up to 2 ^ 33),
   which is above MMAX.

   THE FIX, one word: give c its sign, `0 <= c <= CAPOUT_MAX` (ent_capout_ok0).  aout_at already carries it for the
   value it reads at the same address (W_rep.v:191-192: cap = 0, or 0 < cap), so W8 can state it from the same
   source.  With it the bridge holds: W_frame.v:192 rdword_of_val_mem turns the val_mem read into fr_hblks' rdword
   read (it needs 0 <= c < 2 ^ 64, which the fixed clause gives), and ent_hblks_bsum bounds the entry's harness
   bytes by ATABLE + CAPOUT_MAX.

   WHAT COMES OUT, from the fixed clause.  lm_cap m <= ATABLE + CAPOUT_MAX + OM, so at OM = OUT_MAX4 = CAPOUT_MAX:
   lm_cap m <= ATABLE + 2 * OUT_MAX4 = 267,907,976 <= 2 ^ 29 < MMAX = 1,072,693,248 (a factor 4 of room).
   fr_LS3c_gone_rig_c4_e below is ReplyLS3cTopxRig.v:460 fr_LS3c_gone_rig_c4 with this premise in place of its
   named `Hcap : lm_cap m <= 2 ^ 29`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads relay_instance_gone_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyLSBArms ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBTrPeak ReplyLSBDrainPre ReplyLSBRig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBo.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3Base ReplyB3LS3 ReplyB3LSCntL ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyB3LS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cTopxRig.
Import ListNotations.
(* the gone arm's gn_pairs (lib/B/ReplyLSBArms.v copied it; s5-r1d's cutover, lib/B/ReplyLSBI.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_gone_base.
Local Notation gn_pairs := W_LLVMFuzzerTestOneInput_gone_base.gn_pairs.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation MMAX := fr_MMAX.

(* W8's bound, 3250b98efc5 lib/A/W_LLVMFuzzerTestOneInput_cut.v:181, word for word (OPS_MAX: lib/B's cut, 512) *)
Definition CAPOUT_MAX : Z := 4 * (OPS_MAX - 1) * 65535.
Lemma CAPOUT_MAX_OUT_MAX4 : CAPOUT_MAX = OUT_MAX4.
Proof. reflexivity. Qed.
Lemma CAPOUT_MAX_val : CAPOUT_MAX = 133953540.
Proof. reflexivity. Qed.

(* the cut's Section cf context (A's 3250b98efc5 _cut.v:112-113), which arm's implicit arguments read *)
Section eclause.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* THE CLAUSE AS IT LANDED on A, 3250b98efc5 _cut.v:213 (fr_lib_pre_cf, last) and :233 (its post, last), word for
   word with segs := tfibsegs (lib/B/YB1v.v) and arm := lib/B/W_rep.v's (its implicit arguments: this Section's fx /
   rc and the image instance PB_fr) *)
Definition ent_capout_ok (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  exists c, val_mem tfibsegs (arm W mem) (rg_capout fr_RG) 8 c /\ c <= CAPOUT_MAX.

(* le_byte keeps only the low 64 bits of an 8-byte value *)
Lemma le_byte_m64 : forall v k, le_byte v 8 k = le_byte (v - 2 ^ 64) 8 k.
Proof.
  intros v k. unfold le_byte.
  assert (E : (v - 2 ^ 64) mod 2 ^ (8 * Z.of_nat 8) = v mod 2 ^ (8 * Z.of_nat 8)).
  { assert (E8 : 8 * Z.of_nat 8 = 64) by reflexivity. rewrite E8.
    replace (v - 2 ^ 64) with (v + (-1) * 2 ^ 64) by ring. apply Z.mod_add. lia. }
  rewrite E. reflexivity.
Qed.
(* IT BOUNDS NOTHING: whatever 8-byte value v g_capout holds, c := v - 2 ^ 64 reads the same bytes and is negative *)
Lemma ent_capout_ok_any : forall W mem v,
  val_mem tfibsegs (arm W mem) (rg_capout fr_RG) 8 v -> 0 <= v < 2 ^ 64 -> ent_capout_ok W mem.
Proof.
  intros W mem v Hv Hr. exists (v - 2 ^ 64). split; [|unfold CAPOUT_MAX, OPS_MAX; lia].
  unfold val_mem in *. intros k Hk. rewrite (Hv k Hk).
  (* val_mem's le_byte and the one this file resolves are two constants with one body (lib/Reusable YG0f.v, YO0f.v) *)
  change (Some (Z_to_bv 8 (le_byte v 8 k)) = Some (Z_to_bv 8 (le_byte (v - 2 ^ 64) 8 k))).
  rewrite (le_byte_m64 v k). reflexivity.
Qed.
(* the cut's conjunct, as typed there (`arm W mem`, instance left to resolution), plugs by exact *)
Lemma ent_capout_ok_text : forall W mem,
  (exists c, val_mem tfibsegs (arm W mem) (rg_capout fr_RG) 8 c /\ c <= CAPOUT_MAX) -> ent_capout_ok W mem.
Proof. intros W mem H. exact H. Qed.

(* THE FIX: the same conjunct with c's sign, which aout_at carries for the value it reads at this address
   (W_rep.v:191-192) *)
Definition ent_capout_ok0 (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  exists c, val_mem tfibsegs (arm W mem) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX.
Lemma ent_capout_ok0_ok : forall W mem, ent_capout_ok0 W mem -> ent_capout_ok W mem.
Proof. intros W mem (c & Hv & Hc). exists c. split; [exact Hv | lia]. Qed.

(* THE BRIDGE: lib/B/W_frame.v rdword_of_val_mem turns the clause's val_mem read into fr_hblks' rdword read at the
   same address (fr_hblks: lib/B/W_LLVMFuzzerTestOneInput_cut.v, the text of A's); the table is ATABLE or nothing *)
Lemma ent_hblks_bsum : forall W mem, ent_capout_ok0 W mem -> bsum (fr_hblks W mem) <= ATABLE + CAPOUT_MAX.
Proof.
  intros W mem (c & Hv & Hle).
  assert (Hc : rdword (aview tfibsegs (w_H W) mem) (rg_capout fr_RG) = Some c).
  { apply (rdword_of_val_mem tfibsegs (w_H W) mem); [exact Hv | unfold CAPOUT_MAX, OPS_MAX in *; lia]. }
  unfold fr_hblks. rewrite bsum_app.
  assert (HA : 0 <= ATABLE) by (unfold ATABLE; lia).
  set (v := aview tfibsegs (w_H W) mem) in *.
  assert (H1 : bsum (match rdword v (rg_src fr_RG) with
                     | Some G => if G =? 0 then [] else [(G, ATABLE)] | None => [] end) <= ATABLE).
  { destruct (rdword v (rg_src fr_RG)) as [G|]; [destruct (G =? 0)|];
      cbn [bsum fold_right snd]; lia. }
  assert (H2 : bsum (match rdword v (rg_out fr_RG), rdword v (rg_capout fr_RG) with
                     | Some o, Some c0 => if c0 =? 0 then [] else [(o, c0)] | _, _ => [] end) <= CAPOUT_MAX).
  { rewrite Hc. destruct (rdword v (rg_out fr_RG)) as [o|]; [|cbn [bsum fold_right snd]; unfold CAPOUT_MAX, OPS_MAX; lia].
    destruct (c =? 0); cbn [bsum fold_right snd]; unfold CAPOUT_MAX, OPS_MAX in *; lia. }
  lia.
Qed.
End eclause.

Section ecap.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LSH : lib_shape}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.
Variable OM : Z.

(* fr_ENT turns XB into the entry's harness bytes: the input block and the rest cancel *)
Lemma ent_XB : forall cx t m ly S,
  fr_LS3 B CALL_ROOM_B cx t m ly S -> ReplyB3LS3e.fr_ENT B cx m ly S -> XB cx m S = bsum (fr_hblks (c_W cx) (c_mem cx)).
Proof.
  intros cx t m ly S HLS HE. destruct HLS as (rest & e0 & HP & _).
  pose proof (HE rest HP) as HEnt.
  unfold XB.
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP),
    (blocks_bytes_bsum B (c_ly cx) (c_S cx)), (bsum_perm _ _ HEnt), !bsum_app. lia.
Qed.

(* R4 at every cut, from the fixed entry clause (the landed one bounds nothing: ent_capout_ok_any) *)
Lemma ls3e_cap_le : forall cx t m ly S,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_OUT OM cx t m ly S -> ReplyB3LS3e.fr_ENT B cx m ly S ->
  (* HCAP0 *) ent_capout_ok0 (c_W cx) (c_mem cx) ->
  lm_cap m <= ATABLE + CAPOUT_MAX + OM.
Proof.
  intros cx t m ly S (HLS & _) (U1 & U2 & U3 & U4) HE HCAP0.
  rewrite (ent_XB cx t m ly S HLS HE) in U3.
  pose proof (ent_hblks_bsum (c_W cx) (c_mem cx) HCAP0) as HB. lia.
Qed.
End ecap.

Section ecap4.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LSH : lib_shape}.
Variable B : asyms.
Variable CALL_ROOM_B : Z.

(* at the contract's own bound (CAPOUT_MAX = OUT_MAX4): 267,907,976 <= 2 ^ 29 < 1,072,693,248 *)
Lemma ls3e_cap_lt_MMAX : forall cx t m ly S,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_OUT OUT_MAX4 cx t m ly S -> ReplyB3LS3e.fr_ENT B cx m ly S ->
  ent_capout_ok0 (c_W cx) (c_mem cx) ->
  lm_cap m <= ATABLE + 2 * OUT_MAX4 /\ lm_cap m <= 2 ^ 29 /\ lm_cap m < MMAX.
Proof.
  intros cx t m ly S HLS HOU HE HCAP0.
  pose proof (ls3e_cap_le B CALL_ROOM_B OUT_MAX4 cx t m ly S HLS HOU HE HCAP0) as H.
  rewrite CAPOUT_MAX_OUT_MAX4 in H.
  assert (E1 : ATABLE + 2 * OUT_MAX4 <= 2 ^ 29) by (vm_compute; discriminate).
  assert (E2 : 2 ^ 29 < MMAX) by (vm_compute; reflexivity).
  repeat split; lia.
Qed.

(* lib/B/ReplyB3LS3cTopxRig.v fr_LS3c_gone_rig_c4 (A's ReplyLS3cTopxRig.v:460) with the fixed entry clause in place of
   its named `Hcap : lm_cap m <= 2 ^ 29` *)
Lemma fr_LS3c_gone_rig_c4_e : forall cx t m ly S hs,
  fr_LS3c B CALL_ROOM_B cx t m ly S -> fr_OUT OUT_MAX4 cx t m ly S -> ReplyB3LS3e.fr_ENT B cx m ly S ->
  fr_RINV cx t m -> gn_pairs m hs ->
  (* HCAP0 *) ent_capout_ok0 (c_W cx) (c_mem cx) ->
  lm_cap m < MMAX.
Proof.
  intros cx t m ly S hs HLS HOU HE HRI Hpairs HCAP0.
  destruct (ls3e_cap_lt_MMAX cx t m ly S HLS HOU HE HCAP0) as (_ & Hle & _).
  exact (fr_LS3c_gone_rig_c4 B CALL_ROOM_B cx t m ly S hs HLS HRI Hpairs Hle).
Qed.
End ecap4.
