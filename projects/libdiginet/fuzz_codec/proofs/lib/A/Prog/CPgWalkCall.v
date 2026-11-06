(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: region_kept_tcj_stack and region_kept_tcj_frame are the text of lib/A/ACem.v's
   region_kept_ownframe_aj (copied there from projects/libreac/fuzz_knock/proofs/lib/A/ACem.v) with the call's acall_kept
   replaced by a callee's tcj_kept (lib/A/Prog/CodecCJ.v), cpw_apresent_of_writable that of lib/A/AE7f.v's
   apresent_of_writable; the re-seat in cpw_call_reseat and cpw_rebase is the text of lib/A/AWalkFw2.v's reseatL (copied
   there from projects/libreac/fuzz_knock/proofs/lib/A/AWalkFw2.v) with the environment equation kept for env_agree,
   cpw_kept_std that of lib/A/AWalkFw1.v's aconstsF with the region_kept_val cases of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgMain3.v:186-194, and cpw_leaf that of lib/A/Prog/CPgWalk.v's cw_leaf with the
   state's layout, astate and model taken through the calls' chain; for libdiginet/fuzz_codec's ASan build (image A).
   cpw_call, cpw_entry, cpw_kept_run, cpw_io, cpw_keep and cpw_sp_off are new. *)
(* A call of one of codec's own functions from an image-A walk, through the callee's A-level contract.
   - cpw_call: at the callee's entry (the walk ran the `jal`, so pc is the callee's address and ra the return
     address), the walk's goal follows from the callee's cdc_<f>_specX instance and a continuation from its post.
   - region_kept_tcj_stack / region_kept_tcj_frame: a region of the walk's state is kept across the call, from the
     callee post's tcj_kept: a stack region above the callee's window (clauses 1 and 5), or a region inside a frame of
     the call state or that frame's shadow, off the callee's write set (clause 4).
   - cpw_entry: the callee's cdc_entry at the walk's state; cpw_kept_run: a run inside the walk's window keeps the
     walk's tcj_kept since its entry.
   - the tactics (below): cpw_keep folds a run into that tcj_kept; cpw_call_reseat_at (the callee's sp given as spv,
     for a walk that realigned sp) and cpw_call_reseat (sp less the frame fr) bind the callee's contract at its
     entry, discharges cdc_entry, re-seats the symbolic state at the return address (lib/Reusable/YI04.v
     jafter_call_keep with region_kept_tcj_* / cpw_kept_std), composes the tcj_kept with the callee's (CPgWalkKept.v
     cw_kept_cj) and extends the chain of frames, blocks, model and meter; cpw_rebase names a havoc'd environment;
     cpw_leaf ends the walk at `ret` in cdc_post after such calls. lib/A/Prog/check_text_masks_A.v is the first walk
     built with them. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgWalk CPgWalkKept.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ================================ the call ================================ *)
(* At the callee's entry pc = ss_pc ss: its contract instance P, then the walk on from P. *)
Lemma cpw_call : forall (W : world tfibsegs) E ss ms mdc (P Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
SRr tfibsegs W (cfg_at tfibsegs (ss_pc ss) (ms_regs ms) (ms_mem ms) mdc) P ->
(forall W2 c2, P W2 c2 -> SRr tfibsegs W2 c2 Q) ->
SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros W E ss ms mdc P Q HS Hrv HP HK.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS Hrv).
eapply SRr_bind; [exact HP|]. intros W2 c2 _ H2. exact (HK W2 c2 H2).
Qed.

(* ================================ regions kept across the call ================================ *)
(* a byte off the image that the state lets the walk write is present *)
Lemma cpw_apresent_of_writable : forall (H : word -> bool) (m : word -> option byte) a,
0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
writable_at tfibsegs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hn Hw. unfold apresent. unfold writable_at, wview, mrestrict in Hw.
rewrite unsigned_lit_small in Hw by lia. rewrite (YCbq.find_segment_none tfibsegs a Hn) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity|].
try rewrite Eb in Hw. exfalso. apply Hw. reflexivity.
Qed.
Variable B : asyms.
(* A region of the walk on the machine stack above the allocator ceiling and off the callee's window
   [sp - T, sp) (the callee's sp and T) and its write set Er: kept by the callee post's tcj_kept clause 1, its
   writable bytes by clause 5. *)
Lemma region_kept_tcj_stack : forall E T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (Er : Z -> Prop)
n lo hi wlo whi cs b,
tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp Er ->
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> alloc_ceiling <= a < 2 ^ 64 /\ ~ (sp - T <= a < sp) /\ ~ Er a) ->
(forall a, b + wlo <= a < b + whi -> alloc_ceiling <= a < 2 ^ 64 /\ ~ (sp - T <= a < sp)) ->
region_kept tfibsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E T lyc Sc W memc W2 mem2 sp Er n lo hi wlo whi cs b (K1 & _ & _ & _ & K5 & _) Hn Hr Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- destruct (Hr a Ha) as (Ha1 & Ha2 & Ha3). apply (mbyte_of_aview tfibsegs). exact (K1 a Ha1 Ha2 Ha3).
- intros Hwr. destruct (Hw a Ha) as (Ha1 & Ha2). apply (apresent_writable tfibsegs). apply (K5 a Ha1 Ha2).
  apply (cpw_apresent_of_writable (w_H W) memc a); [lia | | exact Hwr].
  intros Him. pose proof (tfib_segs_low a Him) as Hl. unfold kLowMemEnd in Hl. lia.
Qed.
(* A region inside a frame of the call state or that frame's shadow, off the callee's write set: kept by the
   callee post's tcj_kept clause 4; its writable bytes are present after the call. *)
Lemma region_kept_tcj_frame : forall E T lyc Sc (W : world tfibsegs) memc W2 mem2 sp (Er : Z -> Prop)
n lo hi wlo whi cs b cid pos,
tcj_kept tfibsegs B T lyc Sc W memc W2 mem2 sp Er ->
bv_unsigned (ew E n) = b -> In (cid, pos) (frames Sc) ->
((frame_addr lyc cid pos <= b + lo /\ b + hi <= frame_addr lyc cid pos + fs_frame_bytes cid) \/
(shadow_addr (frame_addr lyc cid pos) <= b + lo /\ b + hi <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8)) ->
(forall a, b + lo <= a < b + hi -> ~ Er a) ->
(forall a, b + wlo <= a < b + whi -> apresent (w_H W2) mem2 a) ->
region_kept tfibsegs E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E T lyc Sc W memc W2 mem2 sp Er n lo hi wlo whi cs b cid pos (_ & _ & _ & K4 & _) Hn Hin Hrng HnE Hpres.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply (K4 cid pos a Hin); [|apply HnE; exact Ha].
  destruct Hrng as [[H1 H2] | [H1 H2]]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; lia.
- intros _. apply (apresent_writable tfibsegs). apply Hpres. exact Ha.
Qed.
(* The journal premise of a callee's cdc_entry at the walk's state (lyd, Sd), whose blocks are a permutation of the
   call state's (lyc, Sc): the live-bytes bound carries over. *)
Lemma cpw_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc lyd Sd (W : world tfibsegs) memc mdc k regs T,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyd Sd W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - T -> spZ regs <= sp0 ->
st_nev S + k + EV_CDC <= EV_MAX ->
Permutation (ablocks B lyd Sd) (ablocks B lyc Sc) -> blocks_bytes Sc + LIVE_CDC <= LIVE_MAX ->
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyd Sd W memc mdc k regs T.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc lyd Sd W memc mdc k regs T HJ Hra Hra4 Hgp Htp Hal Hlo Hhi Hev HP Hlive.
split; [exact HJ|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hev|].
rewrite (blocks_bytes_bsum B lyd Sd), (bsum_perm _ _ HP), <- (blocks_bytes_bsum B lyc Sc). exact Hlive.
Qed.
Section k.
Hypothesis LAWS : AR_laws tfibsegs B.
(* A run whose write windows lie in the walk's window [sp - T, sp) keeps the walk's tcj_kept. *)
Lemma cpw_kept_run : forall T lyc Sc (W : world tfibsegs) m0 mdc W1 m1 m2 sp (E : Z -> Prop) (Ev : env) (rs : smem),
AR tfibsegs B lyc Sc W m0 mdc ->
tcj_kept tfibsegs B T lyc Sc W m0 W1 m1 sp E ->
frame_of Ev rs (mrestrict (w_H W1) m1) (mrestrict (w_H W1) m2) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) m2) ->
(forall a, in_wrange Ev rs a -> sp - T <= a < sp) ->
alloc_ceiling <= sp - T ->
tcj_kept tfibsegs B T lyc Sc W m0 W1 m2 sp E.
Proof.
intros T lyc Sc W m0 mdc W1 m1 m2 sp E Ev rs HAR KT HFr HG HW Hce.
apply (cw_kept_step B LAWS T lyc Sc W m0 mdc W1 m1 m2 sp E (fun a => sp - T <= a < sp) Hce HAR KT).
- intros a Ha Hx. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. intros X. exact (Hx (HW a X)).
- intros a Hx. left. exact Hx.
- intros a (Hh & b & Hb). split; [exact Hh|].
  pose proof (HG (Z_to_bv 64 a)) as G. unfold mrestrict in G. rewrite Hh, Hb in G. cbn in G.
  destruct (m2 (Z_to_bv 64 a)) as [b2|]; [exists b2; reflexivity|].
  exfalso. apply (G ltac:(discriminate)). reflexivity.
Qed.
End k.
End b.

(* ================================ the tactics ================================
   The walk carries: HS (the state), the newest journal (index k) and the entry journal (older), KT : tcj_kept B T lyc
   Sc W memc Wc mc sp E (what the walk kept since its entry, at the current world and memory), HAE : env_agree 32
   (Ereg regs xs) E, B2 : bv_unsigned (ew E 2) = spZ regs, SHOK, and the chain from the call state (lyc, Sc, mdc) to
   the walk's state (lyd, Sd): HFRS : frames Sd = frames Sc (or (cid, pos) :: frames Sc after the walk's own side-stack
   frame request), HPERM : Permutation (ablocks B lyd Sd) (ablocks B lyc
   Sc), HIO : same_io mdc mdi (mdi the model after the last call; the runs since add with_vm_backing layers), HMO :
   mo_le MT Sc Sd 0; and the entry facts (gp, tp, sp mod 16, the event and live-bytes bounds). The tactics find them
   by their types. At the entry: KT from cw_kept0, HFRS eq_refl, HPERM Permutation_refl, HIO same_io_refl, HMO
   mo_le_refl. *)
(* same_io from the call state's model to the current one, through the runs' with_vm_backing layers *)
Ltac cpw_io := let rec kio := first [apply same_io_refl | assumption | eapply same_io_trans; [| apply cw_same_io_wvb]; kio] in kio.
(* fold the last run into KT; kwr proves that the run's write windows lie in the walk's window *)
Ltac cpw_keep kwr :=
lazymatch goal with
| HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows (mrestrict _ _) (mrestrict _ _),
  KT : tcj_kept tfibsegs ?Bv _ ?lyc ?Sc ?W ?m0 _ _ _ _, L : AR_laws tfibsegs ?Bv,
  HJ0 : ajournal tfibsegs ?Bv _ _ _ _ _ _ _ _ _ ?lyc ?Sc ?W ?m0 _ _ |- _ =>
  let KS := fresh "KS" in
  pose proof (cpw_kept_run Bv L _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HJ0) KT HFr HG) as KS;
  lazymatch type of KS with ?P -> _ => let KW := fresh "KW" in assert (KW : P) by kwr; specialize (KS KW); clear KW end;
  specialize (KS ltac:(lia)); clear KT HFr HG; rename KS into KT
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the regions every walk carries (cw_regs: the save area at atom 2, the .got slot, the shadow-offset cell), kept
   across a frameless callee whose window lies below the save area and that writes nothing there: the save area by
   region_kept_tcj_stack (KT2 the callee post's tcj_kept), the two image cells by their values in the journals before
   (HJa) and after (HJb) the call *)
Ltac cpw_kept_std KT2 HJa HJb :=
idtac; first
[ lazymatch goal with |- region_kept _ ?E _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
  lazymatch goal with B2 : bv_unsigned (ew E 2) = _ |- _ =>
  eapply (region_kept_tcj_stack _);
  [ exact KT2 | exact B2
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; [lia | split; [lia | intros []]]
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; lia ] end end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion None ?a _ _ _ _) =>
  let L := rnLAWS in let TL := rnTL in
  let Kc := fresh "Kc" in let Ku := fresh "Ku" in let Kg := fresh "Kg" in let Kgu := fresh "Kgu" in
  let Kc2 := fresh "Kc" in let Ku2 := fresh "Ku" in let Kg2 := fresh "Kg" in let Kgu2 := fresh "Kgu" in
  destruct (al_const _ _ L _ _ _ _ _ (proj1 HJa)) as (Kc & Ku & Kg & Kgu);
  destruct (al_const _ _ L _ _ _ _ _ (proj1 HJb)) as (Kc2 & Ku2 & Kg2 & Kgu2);
  rewrite (tl_got_shadow _ TL), (tl_shadow_cell _ TL) in Kg, Kg2; rewrite (tl_shadow_cell _ TL) in Kc, Kc2;
  first
  [ change a with A_GOT_shadow; apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
    [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kg) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kg2) | lia]
  | change a with A_shadow_glob; apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
    [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kc) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kc2) | lia] ] end ].
(* the state's environment `havoc Ev K ws` (a re-seat, or registers moved to fresh atoms) named afresh: env_agree, the
   facts on atoms below K and the shadow-entry list (empty) carried to it *)
Ltac cpw_rebase :=
lazymatch goal with
| HS : st_ok tfibsegs (havoc ?Ev ?K ?ws) _ (restrict (w_H ?Wc) ?ms), HAE : env_agree 32 (Ereg ?regs ?xs) ?Ev |- _ =>
let E' := fresh "E" in let HEv := fresh "HEv" in
remember (havoc Ev K ws) as E' eqn:HEv in *;
let HAE2 := fresh "HAE" in
assert (HAE2 : env_agree 32 (Ereg regs xs) E') by (rewrite HEv; apply env_agree_havoc_ge; [cbv; lia | exact HAE]);
clear HAE; rename HAE2 into HAE;
repeat match goal with
| H : ew Ev ?n = ?v |- _ =>
  let H2 := fresh in
  first [ assert (H2 : ew E' n = v)
          by (rewrite HEv, ew_havoc_old by (apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity); exact H);
          clear H; rename H2 into H
        | clear H ]
| H : bv_unsigned (ew Ev ?n) = ?v |- _ =>
  let H2 := fresh in
  first [ assert (H2 : bv_unsigned (ew E' n) = v)
          by (rewrite HEv, ew_havoc_old by (apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity); exact H);
          clear H; rename H2 into H
        | clear H ]
end;
clear HEv;
repeat match goal with SH : sh_ok _ _ _ Ev _ |- _ => clear SH end;
pose proof (cw_sh_ok_nil E' (mrestrict (w_H Wc) (ms_mem ms))) as SHOK;
try clear Ev
end.
(* At a callee's entry (the walk ran the `jal`, so pc is the callee's address and ra the literal return address):
   bind SPEC (the callee's cdc_<f>_specX instance) by cpw_call; discharge its cdc_entry from the newest journal, the
   registers (the callee's sp is spv, sptac proves spZ (ms_regs ms) = spv; R1 .. R4 name ra, sp, gp, tp at the stop)
   and the entry facts (spv mod 16 = 0 from the context or from the entry sp's), its own premises by argtac; then
   re-seat the state at the return address (YI04.jafter_call_keep with the regions keep, each kept by kept_tac KT2 HJ
   HJ2, e.g. cpw_kept_std), carry the facts on atoms below the junk window to the new environment, compose KT with the
   callee post's tcj_kept by cw_kept_cj (its window sides by lia over spv; e1tac: each byte the callee may write is
   in the walk's window, its write set, or fresh; `intros ? []` for cno_wr) and extend the chain. Leaves HRc (the
   callee's result R) and HA0c : ew E' j = getr regs2 10 (a0 after the call, in its junk atom j). *)
Ltac cpw_call_reseat_at SPEC spv sptac argtac keep kept_tac e1tac :=
lazymatch goal with
| HS : st_ok tfibsegs ?Ev ?ss (restrict (w_H ?Wc) ?ms), HAE : env_agree 32 (Ereg ?regs ?xs) ?Ev,
  KT : tcj_kept tfibsegs ?Bv ?T ?lyc ?Sc ?W ?memc ?Wc _ ?sp ?Er,
  HJ0 : ajournal tfibsegs ?Bv _ _ _ _ _ _ _ _ _ ?lyc ?Sc ?W ?memc _ _,
  HJ : ajournal tfibsegs ?Bv _ _ _ _ _ _ _ _ _ ?lyd ?Sd ?Wc (ms_mem ?ms) ?mdd _,
  HFRS : frames ?Sd = _, HPERM : Permutation (ablocks ?Bv ?lyd ?Sd) (ablocks ?Bv ?lyc ?Sc),
  HIO : same_io ?mdc _, HMO : mo_le _ ?Sc ?Sd 0,
  Hal16 : spZ ?regs mod 16 = 0, Hlive : blocks_bytes ?Sc + LIVE_CDC <= LIVE_MAX,
  L : AR_laws tfibsegs ?Bv, ML : ameter_laws _ |- SRr _ ?Wc (mkCfg ?ms ?mdd) _ =>
let R1 := fresh "R1" in let R2 := fresh "R2" in let R3 := fresh "R3" in let R4 := fresh "R4" in
let Esp := fresh "Esp" in
rreg HS (1%bv : bv 5) R1; rreg HS (2%bv : bv 5) R2; rreg HS (3%bv : bv 5) R3; rreg HS (4%bv : bv 5) R4;
assert (Esp : spZ (ms_regs ms) = spv) by sptac;
eapply (cpw_call Wc Ev ss ms mdd);
[ exact HS | reflexivity
| eapply SPEC;
  [ eapply cpw_entry;
    [ exact HJ
    | rewrite R1; apply ret_ok_even; vm_compute; reflexivity
    | unfold raZ; rewrite R1, unsigned_lit_small by lia; lia
    | rewrite R3, (proj1 HAE 3%nat ltac:(lia)), (cw_ew_reg regs _ 3 3%bv eq_refl); assumption
    | rewrite R4, (proj1 HAE 4%nat ltac:(lia)), (cw_ew_reg regs _ 4 4%bv eq_refl); assumption
    | rewrite Esp; first [rewrite Zminus_mod, Hal16; reflexivity | assumption]
    | rewrite Esp; lazymatch goal with |- _ <= _ - ?T1 => let t := eval cbv in T1 in change T1 with t end; lia
    | rewrite Esp; lia
    | first [assumption | unfold EV_CDC in *; lia]
    | exact HPERM
    | exact Hlive ]
  | argtac .. ]
| ];
let W2 := fresh "W" in let c2 := fresh "c" in let ly2 := fresh "ly" in let S2 := fresh "S" in
let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in
let HJ2 := fresh "HJ" in let HP2 := fresh "HP" in let Hfrs2 := fresh "Hfrs" in let HPerm2 := fresh "HPerm" in
let HIO2 := fresh "HIO" in let HMLE2 := fresh "HMLE" in let KT2 := fresh "KT" in
cbv beta; intros W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfrs2 & HPerm2 & HIO2 & HMLE2 & KT2 & HRc);
rewrite R1;
rewrite Esp in KT2;
lazymatch type of KT2 with tcj_kept _ _ ?T1 _ _ _ _ _ _ _ _ => let t := eval cbv in T1 in change T1 with t in KT2 end;
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ss) in
let HS2 := fresh "HS2" in
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2;
match type of HS2 with ?Q -> _ =>
  let HQ := fresh "HQ" in
  assert (HQ : Q); [cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac KT2 HJ HJ2
  | specialize (HS2 HQ); clear HQ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let j := eval vm_compute in (K + 4)%nat in
lazymatch type of HS with st_ok _ (havoc ?E0 ?K0 ?ws0) _ _ =>
assert (HA0c : ew (havoc E0 K0 ws0) j = getr regs2 10)
  by exact (ew_havoc_new E0 K0 ws0 4 (Z_to_bv 64 0) ltac:(cbn [length map CLOB]; lia)) end;
cpw_rebase;
let KTn := fresh "KT" in
assert (KTn : tcj_kept tfibsegs Bv T lyc Sc W memc W2 mem2 sp Er)
  by (eapply (cw_kept_cj Bv L) with (1 := HJ0) (2 := HJ) (4 := HPERM) (10 := KT) (11 := KT2);
      [ first [apply incl_refl | rewrite HFRS; first [apply incl_refl | apply incl_tl, incl_refl]] | lia | lia | lia | lia | e1tac ]);
let HFRSn := fresh "HFRS" in let HPERMn := fresh "HPERM" in let HIOn := fresh "HIO" in let HMOn := fresh "HMO" in
pose proof (eq_trans Hfrs2 HFRS) as HFRSn;
pose proof (Permutation_trans HPerm2 HPERM) as HPERMn;
assert (HIOn : same_io mdc md2) by (apply (fun H => same_io_trans _ _ _ H HIO2); cpw_io);
pose proof (mle_station _ _ _ _ 0 0 ML HMO HMLE2) as HMOn;
rewrite Z.add_0_r in HMOn;
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (?k1 + EV_CDC) =>
  replace (k1 + EV_CDC) with k1 in HJ2 by (unfold EV_CDC; lia) end;
clear R1 R2 R3 R4 Esp HP2 HIO2 Hfrs2 HPerm2 HMLE2 KT2 HFRS HPERM HIO HMO KT HJ;
try clear ms;
rename HJ2 into HJ; rename KTn into KT; rename HFRSn into HFRS; rename HPERMn into HPERM;
rename HIOn into HIO; rename HMOn into HMO
end.
(* The callee's sp is spZ regs - fr, through the stop's sp equation (the one hypothesis getr _ _ = _ that rewrites the
   goal), then B2 (sp an offset of atom 2) or lia over the walk's facts (sp held by an atom, e.g. after a realignment,
   with fr := spZ regs - SP1 and bv_unsigned (ew E m) = SP1 in context). *)
Ltac cpw_sp_off :=
match goal with R : getr _ _ = _ |- spZ _ = _ =>
  unfold spZ at 1; rewrite R;
  first [ lazymatch goal with B2 : bv_unsigned (ew _ 2) = spZ _ |- _ =>
            rewrite B2; rewrite unsigned_lit_small by lia; lia end
        | lia
        | rewrite unsigned_lit_small by lia; lia ] end.
Ltac cpw_call_reseat SPEC fr argtac keep kept_tac e1tac :=
lazymatch goal with
| HS : st_ok tfibsegs ?Ev _ _, HAE : env_agree 32 (Ereg ?regs _) ?Ev |- _ =>
  cpw_call_reseat_at SPEC (spZ regs - fr) ltac:(idtac; cpw_sp_off) argtac keep kept_tac e1tac
end.
(* The `ret` leaf of a walk that called its own callees: cw_leaf with the state's layout, astate and model those of
   the last callee's post (the chain HFRS, HPERM, HIO, HMO). *)
Ltac cpw_leaf ktac rtac :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _ |- _ =>
let R1 := fresh "R1" in rreg HS (1%bv : bv 5) R1;
let R10 := fresh "R10" in cw_r10 R10;
eapply (SRr_ret_at tfibsegs tfibtbl_lib tfibtbl_lib_ok Hwx_tfa W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [lazymatch goal with E1 : ew _ 1 = _, Hra : YK0s.ret_ok _ |- _ => rewrite R1, E1, Hra; reflexivity end|];
split; [unfold EV_CDC; rewrite Z.add_0_r; eapply ajournal_materialize; eassumption|];
split; [eapply aregs_preserved_of_st_ok;
  [exact HS | lazymatch goal with HAE : env_agree 32 _ _ |- _ => env_agree_chain HAE end | vm_compute; reflexivity]|];
split; [first [reflexivity | assumption]|];
split; [first [apply Permutation_refl | assumption]|];
split; [cpw_io|];
split; [first [assumption | apply mo_le_refl; assumption]|];
split; [ktac | rtac]
end.
