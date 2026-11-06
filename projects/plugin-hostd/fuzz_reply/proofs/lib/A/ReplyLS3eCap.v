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

   THE ENTRY CLAUSE.  lib/A/W_LLVMFuzzerTestOneInput_cut.v:223 `Definition CAPOUT_MAX : Z := 4 * (OPS_MAX - 1) *
   65535.`, and LAST in fr_lib_pre_cf (:213; _cut_x.v:109 in fr_lib_pre_cf_x), at the call's world and memory:
     exists c, val_mem segs (arm W mem) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX
   with segs := tfibsegs (_cut.v's Section cf) and arm := W_rep.v:69.  The R4 lemmas below take that text at
   W := c_W cx, mem := c_mem cx, word for word, so the cut's conjunct plugs by `exact`.  (The clause as it first
   landed, `c <= CAPOUT_MAX` without c's sign, bounded nothing: val_mem stores the low 64 bits of c, so a negative c
   reads any 8 bytes; W8 fixed it as fd261f0a4de.)

   THE BRIDGE.  W_frame.v:192 rdword_of_val_mem turns the val_mem read into fr_hblks' rdword read (it needs
   0 <= c < 2 ^ 64, which the clause gives), and ent_hblks_bsum bounds the entry's harness bytes by
   ATABLE + CAPOUT_MAX.

   WHAT COMES OUT.  lm_cap m <= ATABLE + CAPOUT_MAX + OM, so at OM = OUT_MAX4 = CAPOUT_MAX:
   lm_cap m <= ATABLE + 2 * OUT_MAX4 = 267,907,976 <= 2 ^ 29 < MMAX = 1,072,693,248 (a factor 4 of room).
   fr_LS3c_gone_rig_c4_e below is ReplyLS3cTopxRig.v fr_LS3c_gone_rig_c4 with this premise in place of its
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ACfn_cf CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLS3 ReplyLSDrainPre ReplyLSDrain3 ReplyLSRemove3 ReplyLSEvent3 ReplyLS3Arms ReplyLSCntL ReplyLS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3o ReplyLS3e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS3cTopx ReplyLS3cTopxRig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Notation MT := ameter_triv.
Local Notation MMAX := WR_MMAX.

(* CAPOUT_MAX is W_LLVMFuzzerTestOneInput_cut.v:181's *)
Lemma CAPOUT_MAX_OUT_MAX4 : CAPOUT_MAX = OUT_MAX4.
Proof. reflexivity. Qed.
Lemma CAPOUT_MAX_val : CAPOUT_MAX = 133953540.
Proof. reflexivity. Qed.

(* THE BRIDGE: W_frame.v:192 rdword_of_val_mem turns the clause's val_mem read into fr_hblks' rdword read at the
   same address (fr_hblks: W_LLVMFuzzerTestOneInput_cut.v:166); the table is ATABLE or nothing *)
Section eclause.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ent_hblks_bsum : forall W mem,
  (exists c, val_mem tfibsegs (arm W mem) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  bsum (fr_hblks W mem) <= ATABLE + CAPOUT_MAX.
Proof.
  intros W mem (c & Hv & Hle).
  assert (Hc : rdword (aview tfibsegs (w_H W) mem) (rg_capout fr_RG) = Some c).
  { apply (rdword_of_val_mem tfibsegs (w_H W) mem); [exact Hv | unfold CAPOUT_MAX, OPS_MAX in *; lia]. }
  unfold fr_hblks. cbv zeta. rewrite bsum_app.
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
  apply Z.add_le_mono; [exact H1 | exact H2].
Qed.
End eclause.

Section ecap.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LSH : lib_shape}.
Variable B : asyms.
Variable OM : Z.

(* fr_ENT turns XB into the entry's harness bytes: the input block and the rest cancel *)
Lemma ent_XB : forall cx t m ly S,
  fr_LS3 B cx t m ly S -> fr_ENT B cx m ly S -> XB cx m S = bsum (fr_hblks (c_W cx) (c_mem cx)).
Proof.
  intros cx t m ly S HLS HE. destruct HLS as (rest & e0 & HP & _).
  pose proof (HE rest HP) as HEnt.
  unfold XB.
  rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP),
    (blocks_bytes_bsum B (c_ly cx) (c_S cx)), (bsum_perm _ _ HEnt), !bsum_app. lia.
Qed.

(* R4 at every cut, from the entry clause *)
Lemma ls3e_cap_le : forall cx t m ly S,
  fr_LS3c B cx t m ly S -> fr_OUT OM cx t m ly S -> fr_ENT B cx m ly S ->
  (* HCAP0 *) (exists c, val_mem tfibsegs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
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

(* at the contract's own bound (CAPOUT_MAX = OUT_MAX4): 267,907,976 <= 2 ^ 29 < 1,072,693,248 *)
Lemma ls3e_cap_lt_MMAX : forall cx t m ly S,
  fr_LS3c B cx t m ly S -> fr_OUT OUT_MAX4 cx t m ly S -> fr_ENT B cx m ly S ->
  (exists c, val_mem tfibsegs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  lm_cap m <= ATABLE + 2 * OUT_MAX4 /\ lm_cap m <= 2 ^ 29 /\ lm_cap m < MMAX.
Proof.
  intros cx t m ly S HLS HOU HE HCAP0.
  pose proof (ls3e_cap_le B OUT_MAX4 cx t m ly S HLS HOU HE HCAP0) as H.
  rewrite CAPOUT_MAX_OUT_MAX4 in H.
  assert (E1 : ATABLE + 2 * OUT_MAX4 <= 2 ^ 29) by (vm_compute; discriminate).
  assert (E2 : 2 ^ 29 < MMAX) by (vm_compute; reflexivity).
  repeat split; lia.
Qed.

(* ReplyLS3cTopxRig.v:459 fr_LS3c_gone_rig_c4 with the fixed entry clause in place of its named
   `Hcap : lm_cap m <= 2 ^ 29` *)
Lemma fr_LS3c_gone_rig_c4_e : forall cx t m ly S hs,
  fr_LS3c B cx t m ly S -> fr_OUT OUT_MAX4 cx t m ly S -> fr_ENT B cx m ly S ->
  fr_RINV cx t m -> gn_pairs m hs ->
  (* HCAP0 *) (exists c, val_mem tfibsegs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  lm_cap m < MMAX.
Proof.
  intros cx t m ly S hs HLS HOU HE HRI Hpairs HCAP0.
  destruct (ls3e_cap_lt_MMAX cx t m ly S HLS HOU HE HCAP0) as (_ & Hle & _).
  exact (fr_LS3c_gone_rig_c4 B cx t m ly S hs HLS HRI Hpairs Hle).
Qed.
End ecap4.
