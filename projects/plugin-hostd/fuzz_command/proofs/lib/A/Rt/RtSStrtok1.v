(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> CmdBSyms, its addresses moved to plugin-hostd/fuzz_command's ASan build, and the module destructor's write set XW2 stated with the shadow of the whole image ([0x7fffa000, 0x800b8c00)) instead of the shadow bytes of cgif's three registered globals (fuzz_command registers 180), plus the odr indicator bytes of the four globals that have one (0x5e3c40..0x5e3c42, 0x5e3c80), which __asan_unregister_globals clears. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE23.v; 161 of its 206 lines of code are new or changed and 1630 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AB1w AE34 AF0l AF0m AF0x AE2y AE3d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI RtString.
From OSSVerify.plugin_hostd.fuzz_command.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* musl's strtok_r of plugin-hostd/fuzz_command's ASan build, 0x9f804..0x9f890 (36 instructions, frame 32, no
   stack protector of its own; measured with the disassembler on the pinned fuzz_command.asan). It calls the strspn
   trampoline 0x45148 at 0x9f838 and the strcspn trampoline 0x4514c at 0x9f850, and returns at 0x9f890. The
   symbolic run uses the musl table of the layer (AB1v.tfibmusl_tbl), which does not hold the trampolines, so each
   run stops at the call. Atoms of the environment beyond the registers:
   32 the saved pointer *p, 33 the string C, 34 C + k, 35 C + k + j, 36 the byte at C + k, 37 the byte at C + k + j,
   where k is strspn's result and j strcspn's. The walk of the two calls and the theorem are in RtSStrtok2.v. *)

Definition NUL : byte := Z_to_bv 8 0.

Lemma spn_le : forall set s, (PSpn.spn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; [cbn; lia|]. cbn [PSpn.spn_len length]. destruct (PSpn.in_set set x); lia. Qed.
Lemma cspn_le : forall set s, (PCspn.cspn_len set s <= length s)%nat.
Proof.
intros set s. induction s as [|x s IH]; [cbn; lia|]. cbn [PCspn.cspn_len length].
destruct (existsb _ set); lia.
Qed.
Lemma nth_skipn_l : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof. induction l as [|x l IH]; intros [|k] i d; cbn; try reflexivity; try (destruct i; reflexivity). apply IH. Qed.
Lemma skipn_app_le : forall (l z : list byte) k, (k <= length l)%nat -> skipn k (l ++ z) = skipn k l ++ z.
Proof. induction l as [|x l IH]; intros z [|k] Hk; cbn in *; try reflexivity; try lia. apply IH. lia. Qed.
Lemma in_skipn_l : forall (l : list byte) k x, In x (skipn k l) -> In x l.
Proof. induction l as [|y l IH]; intros [|k] x Hx; cbn in *; try exact Hx. right. exact (IH k x Hx). Qed.
Lemma length_skipn_l : forall (l : list byte) k, length (skipn k l) = (length l - k)%nat.
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.
Lemma nth_firstn_l : forall (l : list byte) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof. induction l as [|x l IH]; intros [|n] [|i] d Hi; cbn; try reflexivity; try lia. apply IH. lia. Qed.
Lemma length_firstn_l : forall (l : list byte) n, (n <= length l)%nat -> length (firstn n l) = n.
Proof. induction l as [|x l IH]; intros [|n] Hn; cbn in *; try reflexivity; try lia. f_equal. apply IH. lia. Qed.
Lemma byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as Ha. unfold bv_modulus in Ha. change (2 ^ Z.of_N 8) with 256 in Ha. exact Ha. Qed.
Lemma nth_str_nz : forall (s : list byte) i, ~ In NUL s -> (i < length s)%nat -> bv_unsigned (nth i (s ++ [NUL]) NUL) <> 0.
Proof.
intros s i Hn Hi E. apply Hn. rewrite app_nth1 in E by lia.
assert (X : nth i s NUL = NUL) by (apply bv_eq; rewrite E; reflexivity).
rewrite <- X. apply nth_In. exact Hi.
Qed.
Lemma nth_str_end : forall (s : list byte), nth (length s) (s ++ [NUL]) NUL = NUL.
Proof. intros s. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma nth_str_zero : forall (s : list byte) i, ~ In NUL s -> (i <= length s)%nat ->
bv_unsigned (nth i (s ++ [NUL]) NUL) = 0 -> i = length s.
Proof.
intros s i Hn Hi E. destruct (Nat.eq_dec i (length s)) as [->|Hne]; [reflexivity|].
exfalso. exact (nth_str_nz s i Hn ltac:(lia) E).
Qed.
Lemma nth_cut : forall (s : list byte) m i, (m < length s)%nat -> (i <= length s)%nat ->
nth i (firstn m s ++ NUL :: skipn (S m) s ++ [NUL]) NUL = if Nat.eqb i m then NUL else nth i (s ++ [NUL]) NUL.
Proof.
intros s m i Hm Hi. pose proof (length_firstn_l s m ltac:(lia)) as Lf.
destruct (Nat.lt_trichotomy i m) as [L|[->|L]].
- rewrite (proj2 (Nat.eqb_neq i m)) by lia. rewrite app_nth1 by lia. rewrite app_nth1 by lia.
apply nth_firstn_l. exact L.
- rewrite Nat.eqb_refl. rewrite app_nth2 by lia. rewrite Lf, Nat.sub_diag. reflexivity.
- rewrite (proj2 (Nat.eqb_neq i m)) by lia. rewrite app_nth2 by lia. rewrite Lf.
replace (i - m)%nat with (S (i - S m)) by lia. cbn [nth].
rewrite <- skipn_app_le by lia. rewrite nth_skipn_l. f_equal. lia.
Qed.

Definition TOK_RET1 : Z := 0x9f83c.
Definition TOK_RET2 : Z := 0x9f854.
Definition rSTK : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition rP : YP09.region := YP09.mkRegion (Some 12%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition rCK : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition rCJ : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
Definition ss0 : sstate := mkSS PC_strtok_r sr_atoms [rSTK; rP] None (mkFacts [] [] []).
Definition PIN (ss : sstate) (r : bv 5) (e : sv) : sstate :=
mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition ADDR (ss : sstate) (r : YP09.region) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition RUN (s : sstate) := sym_runN tfibsegs tfibmusl_tbl FUEL s.
(* The state at the strspn call: both entry paths (s <> 0, and s = 0 with *p <> 0) reach it with C in a0 and s1. *)
Definition eA : sstate := Eval vm_compute in fst (RUN (add_cond (fst (RUN ss0)) (mkAC BC_NE (SOff 10 0) (SLit 0)))).
Definition UA : sstate := Eval vm_compute in DROPC (PIN (PIN eA 9 (SOff 33 0)) 10 (SOff 33 0)).
Definition SC1 : sstate := Eval vm_compute in ss_after_call UA (ss_mem UA) 38 TOK_RET1.
(* The state at the strcspn call, and after it. *)
Definition eC1 : sstate := Eval vm_compute in fst (RUN SC1).
Definition eC2 : sstate := Eval vm_compute in fst (RUN (ADDR (PIN eC1 9 (SOff 34 0)) rCK)).
Definition SN : sstate := Eval vm_compute in fst (RUN (add_cond eC2 (mkAC BC_NE (SExt false 8 (SOff 36 0)) (SLit 0)))).
Definition SC2 : sstate := Eval vm_compute in ss_after_call SN (pick (ss_mem SN) [1%nat; 2%nat]) 54 TOK_RET2.
Lemma UA_pc : ss_pc UA = PC_strspn. Proof. reflexivity. Qed.
Lemma SN_pc : ss_pc SN = PC_strcspn. Proof. reflexivity. Qed.
Lemma r9_nz : (9%bv : bv 5) <> 0%bv. Proof. intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate. Qed.
Lemma r10_nz : (10%bv : bv 5) <> 0%bv. Proof. intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma tok_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tfibmusl_tbl FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
(forall x, w_H W x = true -> ms_mem ms1 x = ms_mem ms x)).
Proof.
intros W E ss ss' st ms md HS Hrun.
destruct (msteps_run_gen tfibsegs tfibmusl_tbl tfibmusl_tbl_ok FUEL E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
apply (SRr_msteps tfibsegs AF0x.Hwx_tfa W ms msr' md _ Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb md model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (msteps_mem_grows tfibsegs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr, Hfr.
apply SRr_ret. split; [reflexivity|].
exists (unrestrict (w_H W) (ms_mem ms) msr'), (m_vm_materialized model'). split; [reflexivity|].
assert (Hmm : mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) = ms_mem msr').
{ change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr'))) with
(ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))). rewrite Hrr. reflexivity. }
split; [rewrite Hrr; exact HS'|].
split; [rewrite Hmm; exact Hfr|].
split; [rewrite Hmm; exact Hgr|].
intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
Qed.
End c.

(* One symbolic run from the state HS describes: [tok_phase] at the model term the goal names (trap #4: the instance
   is passed, not left to unification), then the fresh model term is set and cleared (trap #1). The results are
   named by the caller: the machine state [ms'], the frame [HF], the growth [HG], the hidden bytes [HH], the
   model relation [Hsb] and the model term [mdv]. *)
Ltac tphase HS ms' HF HG HH Hsb mdv :=
lazymatch type of HS with
| st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_runN tfibsegs tfibmusl_tbl FUEL ss) in
lazymatch r with (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN tfibsegs tfibmusl_tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
lazymatch goal with |- SRr _ _ (mkCfg _ ?md0) _ =>
eapply SRr_bind; [exact (tok_phase W E ss ss' st ms md0 HS Hrun)|]
end;
clear Hrun HS; cbv beta;
let W' := fresh "W" in let c' := fresh "c" in let Hle := fresh "Hle" in let mat := fresh "mat" in
intros W' c' Hle; clear Hle; intros (-> & ms' & mat & -> & HS & HF & HG & HH);
cbv beta iota in HS;
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mt ?m0] =>
pose proof (with_vm_backing_same m0 mt) as Hsb;
set (mdv := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdv
end
end end.

Section g.
Lemma apresent_grows' : forall H m m' a, mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|]. specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg.
rewrite Hh, Hb in Hg. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. exact (Hg ltac:(discriminate) eq_refl).
Qed.
Lemma aview_keeps_vis' : forall H m m' a, mem_grows (mrestrict H m) (mrestrict H m') ->
aview tfibsegs H m a <> None -> aview tfibsegs H m' a <> None.
Proof.
intros H m m' a Hg. unfold aview, mbyte.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E.
- intros _. pose proof (Hg _ ltac:(rewrite E; discriminate)) as X.
destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exfalso; exact (X eq_refl)].
- intros Hv. destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.
Lemma writable_keep : forall H m m' a, writable_at tfibsegs (mrestrict H m) a ->
(apresent H m a -> apresent H m' a) -> writable_at tfibsegs (mrestrict H m') a.
Proof.
intros H m m' a Hw Hp. unfold writable_at, wview, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:Hh; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb.
- destruct (Hp (conj Hh (ex_intro _ b Eb))) as [_ [b' Hb']]. rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma val_mem_aview_eq : forall H m m' a n v, val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v ->
forall x, a <= x < a + Z.of_nat n -> aview tfibsegs H m' x = aview tfibsegs H m x.
Proof.
intros H m m' a n v V V' x Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
unfold aview. rewrite (V (Z.to_nat (x - a)) ltac:(lia)), (V' (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.
Lemma aview_byte_rng : forall H m a v, aview tfibsegs H m a = Some v -> 0 <= v < 256.
Proof. intros H m a v Hv. destruct (AE2y.aview_byte_ex H m a v Hv) as (b & _ & -> & R). exact R. Qed.
Lemma rdword_rng : forall H m a v, rdword (aview tfibsegs H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H m a v Hw. unfold rdword in Hw.
destruct (aview tfibsegs H m a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs H m (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs H m (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs H m (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs H m (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs H m (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs H m (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs H m (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply aview_byte_rng in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.
Lemma in_rom_low : forall a, in_rom tfibsegs a -> 0 <= a < TFIB_IMG_END.
Proof.
intros a (sg & Hin & _ & Hr).
assert (Hm : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs))
by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin).
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in Hm. unfold TFIB_IMG_END.
repeat (destruct Hm as [Hm|Hm]; [injection Hm as <- <-; lia|]). destruct Hm.
Qed.
Lemma U_w64 : forall E n z, ew E n = w64 z -> U E (SOff n 0) = z mod 2 ^ 64.
Proof.
intros E n z Hn. rewrite U_SOff, Hn. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r. unfold zcanon, M64. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
End g.
