From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YN03 YN2b YN0b_cf YN07_cf YN0a_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW03_cf YW0e_cf YW06_cf YW07_cf YW09_cf YY00_cf YY03_cf YV00_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma realloc_small_tree A g am fr n :
WF A -> usedX [] A g am -> ss_fr (nth_slot am 0) = Some fr -> am_sc am = 63 -> am_last am = 0 -> 0 <= n < MMAP_THRESHOLD ->
realloc (Some (frame_ptr am 0 fr)) n A = realloc_move (frame_ptr am 0 fr) n A.
Proof using.
intros HW Hu Hfr H63 Hlast Hn.
assert (Hff : find_frame_in (st_metas A) (frame_ptr am 0 fr) = Some (g, 0))
by (apply (find_frame_in_spec [] None U0 A HW g am 0 fr Hu); [rewrite Hlast; lia | exact Hfr]).
assert (Mg : mlookup (st_metas A) g = Some (MUsed am)) by exact (proj1 (usedX_MT _ _ _ _ Hu)).
unfold realloc.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; unfold MMAP_THRESHOLD in Hn; lia).
unfold bind at 1. unfold find_frame. unfold bind at 1. unfold get. cbn [ibind]. rewrite Hff.
unfold ret at 1. cbn [ibind fst snd].
unfold bind at 1. unfold getm at 1. unfold bind at 1. unfold get. cbn [ibind]. rewrite Mg. unfold ret at 1. cbn [ibind].
rewrite Hfr.
replace (am_sc am <=? size_to_class n + 1) with false
by (rewrite H63; symmetry; apply Z.leb_gt; pose proof (size_to_class_range n Hn); lia).
rewrite andb_false_r.
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
rewrite andb_false_r. reflexivity.
Qed.
Definition condLT : acond := mkAC BC_LTU (SOff aEP 0) (SOff aN 0).
Definition condGE : acond := mkAC BC_GEU (SOff aEP 0) (SOff aN 0).
Section b.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Local Notation VV := (YW06_cf.vv L regs g am fr a rg).
Lemma den_lo gd err k : (k < 96)%nat ->
sv_denot (Er L regs g am fr n a rg gd err) (SOff k 0) = sv_denot (EV (xvf VV)) (SOff k 0).
Proof using.
intros Hk. cbn [sv_denot]. unfold Er, EV. cbn [ew]. unfold xvr.
replace (k <? 96)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk). reflexivity.
Qed.
Lemma cond_split :
(forall gd err, conds_ok (Er L regs g am fr n a rg gd err) [condLT]) \/
(forall gd err, conds_ok (Er L regs g am fr n a rg gd err) [condGE]).
Proof using.
destruct (branch_taken BC_LTU (sv_denot (EV (xvf VV)) (SOff aEP 0)) (sv_denot (EV (xvf VV)) (SOff aN 0))) eqn:Eb.
- left. intros gd err. split; [| exact I]. unfold acond_ok, condLT. cbn [ac_c ac_a ac_b].
rewrite !den_lo by (unfold aEP, aN; lia). exact Eb.
- right. intros gd err. split; [| exact I]. unfold acond_ok, condGE. cbn [ac_c ac_a ac_b].
rewrite !den_lo by (unfold aEP, aN; lia). cbn [branch_taken] in Eb |- *. rewrite Eb. reflexivity.
Qed.
Lemma arrives_fb gd err : 0 <= gd < 2 ^ 64 -> 0 <= err < 2 ^ 32 -> forall c,
arrives (Er L regs g am fr n a rg gd err) (rcr am fr) mem md c ->
mreal_cf src0segs c (realloc_move (pp am fr) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (pp am fr) (fr_n fr) n).
Proof using HC.
intros Hgd Herr c (regs4 & mem4 & -> & AR).
exact (realloc_fb_gen L A regs mem md (pp am fr) (fr_n fr) n regs4 mem4
(fb_of_arr L A regs mem md g am fr n a ka rg HC gd err Hgd Herr regs4 mem4 AR)).
Qed.
End b.
End a.
