(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v and ACam.v (a walk segment, the side-stack frame's release): from strtol's return (0x8e534) to number's return, the four paths of number's tests (the word's first byte, the end pointer's byte, the range of the value) and the release of the class-0 frame. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/numberB.v (a working branch a7e5999afe4) for fuzz_command.asan-ubsan: module paths and the segment's addresses in that image (strtol's return 0x8e030, the release 0x8e0ac = BASE + 31612, the range test's bltu 0x8e088 = BASE + 31576). B adds three UBSan trap branches (0x8e030 word null, 0x8e054 end null, 0x8e090 out misaligned, all to the `unimp` at 0x8e148); the token runs decide each not taken from the atom facts of ss_nB (atoms 10 and 1058 at or above 4096, atom 11 4-aligned), so the segment's steps are A's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require number.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import number_c numberE numberR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma n_nonzero : forall (wd : list byte), ~ In (Z_to_bv 8 0) wd -> Forall (fun b : byte => bv_unsigned b <> 0) wd.
Proof.
intros wd H. apply Forall_forall. intros b Hb Hz. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|].
apply bv_eq. rewrite Hz. reflexivity.
Qed.
Lemma n_wd_nil : forall (wd : list byte), ~ In (Z_to_bv 8 0) wd ->
bv_unsigned (nth 0 (wd ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) = 0 -> wd = [].
Proof.
intros wd H0 Hb. destruct (number.byte_first wd (n_nonzero wd H0)) as (b & Hb' & Hiff). apply Hiff.
change (Z.to_nat 0) with 0%nat in Hb'. rewrite (nth_error_nth _ _ (Z_to_bv 8 0) Hb') in Hb. exact Hb.
Qed.
Lemma n_end_iff : forall (wd : list byte), ~ In (Z_to_bv 8 0) wd ->
bv_unsigned (nth (Z.to_nat (__intscan_c.s10_end wd)) (wd ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) = 0 <->
__intscan_c.s10_end wd = Z.of_nat (length wd).
Proof.
intros wd H0. destruct (number.byte_end wd (n_nonzero wd H0)) as (b & Hb & Hiff).
rewrite (nth_error_nth _ _ (Z_to_bv 8 0) Hb). exact Hiff.
Qed.
(* range_addressable over SHADOW_OFF reads only shadow bytes of the 64-bit space, so it moves to a reader that
   agrees there *)
Lemma n_ra_keep : forall (rd rd' : reader) a n, 0 <= a -> a + n <= 2 ^ 63 ->
(forall y, 0 <= y < 2 ^ 64 -> rd' y = rd y) ->
range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n Ha Hn HK H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
rewrite HK; [exact Hs|]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF. unfold SB.
assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia.
Qed.
Lemma n_val1 : forall {fx : YK11.FPState} segs H (m : word -> option byte) a v,
aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros fx segs H m a v Hv j Hj. replace j with 0%nat by lia. rewrite Z.add_0_r.
destruct (aview_byte segs H m a v Hv) as (b & Hb & -> & Hr). rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 8 b) as R8. change (bv_modulus 8) with 256 in R8.
unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma n_aval_of_val : forall {fx : YK11.FPState} segs H (m : word -> option byte) a n v,
val_mem segs (mrestrict H m) a n v -> aval_mem (aview segs H m) a n v.
Proof.
intros fx segs H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, le_byte. apply Z.mod_mod. lia.
Qed.
(* a 4-byte chunk of a value v (sw stores the low 4 bytes of the register): the 4 bytes hold le_byte v 4 k, for
   any integer v, negative ones included *)
Lemma n_chunk4_aval : forall {fx : YK11.FPState} segs E H (m : word -> option byte) base off e (v : Z),
YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
aval_mem (aview segs H m) (base + off) 4 v.
Proof.
intros fx segs E H m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len; cbn [YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. rewrite He, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64).
unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros j Hj.
destruct (Z_lt_le_dec j 8) as [Hj8|Hj8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma n_region_aval4 : forall {fx : YK11.FPState} segs E H (m : word -> option byte) n b cs lo hi wlo whi od e v,
region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
aval_mem (aview segs H m) (b + od) 4 v.
Proof.
intros fx segs E H m n b cs lo hi wlo whi od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (n_chunk4_aval segs E H m b od e v Hck He).
Qed.
Lemma n_range_U : forall E (v : Z), -9223372036854775808 <= v <= 9223372036854775807 -> ew E 1046 = Z_to_bv 64 v ->
(U E (SOff 1046 (-1000001)) <? U E (SLit 18446744073707551615)) = negb ((-1000000 <=? v) && (v <=? 1000000)).
Proof.
intros E v Hv He. rewrite <- (number.range_ltu v Hv). unfold U, bv_ltu. cbn [sv_denot]. rewrite He.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
(* n_SH's one entry names the atoms 11 (the result cell) and 32 (the shadow base), so sh_ok moves to any
   environment that agrees there *)
Lemma n_sh_move : forall {fx : YK11.FPState} segs E E' m,
ew E' 11 = ew E 11 -> ew E' 32 = ew E 32 ->
sh_ok segs (SOff 32 0) n_SH E m -> sh_ok segs (SOff 32 0) n_SH E' m.
Proof.
intros fx segs E E' m H11 H32 H. unfold sh_ok, n_SH in *.
apply Forall_cons; [|apply Forall_nil]. inversion H as [|x l Hx _]; subst.
destruct Hx as [Hra Hap]. unfold shent_ok, app_apart, U in *. cbn [she_m she_lo she_hi] in *.
cbn [sv_denot] in Hra, Hap |- *. rewrite !Z.add_0_r in *. rewrite H11, H32. split; [exact Hra | exact Hap].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Ltac n_awr_ro :=
lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac n_evE := repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia].
(* the shadow knowledge of n_SH moves to another environment that agrees at the atoms 11 and 32 *)
Ltac n_shok SHOK2 HS SHOK :=
lazymatch type of HS with st_ok_pi _ _ ?Ex _ ?msx =>
lazymatch type of SHOK with sh_ok ?sg ?Bx ?SHl ?E0 ?m0 =>
assert (SHOK2 : sh_ok sg Bx SHl Ex m0) by
(apply (n_sh_move sg E0 Ex m0); [ n_evE; reflexivity | n_evE; reflexivity | exact SHOK ]) end end.
Ltac n_unch_out UN HFr out :=
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => out <= a < out + 4) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
  first [exfalso; clear - Hrr; lia | (lazymatch goal with Ux : bv_unsigned (ew _ 11) = out |- _ => rewrite Ux in Hrr end); clear - Hrr; lia]|]); destruct Hin)) as UN.
Ltac n_unch UN HFr :=
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN.
Ltac n_in_tac := let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; vm_compute in Hx; repeat (destruct Hx as [<- | Hx]; [vm_compute; repeat (first [left; reflexivity | right]) |]); destruct Hx.
Ltac n_setr HS EH i r :=
lazymatch type of HS with st_ok_pi ?sg2 ?vl2 ?Ex2 ?ssx2 ?ms2 =>
let HS4 := fresh "HS4" in
pose proof (st_ok_pi_set_reg Ex2 _ _ r (SOff (1100 + i) 0) HS ltac:(discriminate) (eq_sym (EH i r ltac:(lia) eq_refl))) as HS4;
clear HS; rename HS4 into HS end.
(* bring a state at the release (0x8e0ac) to ss_rel0: the regions n_keep selects, ss_nB's facts, a0..a3 as the fresh
   atoms 1100..1103 of the environment Ev1 *)
Ltac n_canon HS Ev1 AG1 E1100 :=
n_keep_regions HS n_keep;
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in let HS3 := fresh "HS3" in
assert (Q1 : forall x, In x (f_atoms (ss_facts ss_nB)) -> In x (f_atoms (ss_facts ssx))) by n_in_tac;
assert (Q2 : forall x, In x (f_alias (ss_facts ss_nB)) -> In x (f_alias (ss_facts ssx))) by n_in_tac;
pose proof (st_ok_pi_facts_incl Ex ssx msx (f_atoms (ss_facts ss_nB)) (f_alias (ss_facts ss_nB)) HS Q1 Q2) as HS3;
clear HS Q1 Q2; rename HS3 into HS end;
nnorm HS;
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?H ?msx) =>
let HS3 := fresh "HS3" in let EH := fresh "EH" in
pose proof (st_ok_pi_havoc_hi 1100 Ex ssx (restrict H msx) [getr (ms_regs msx) 10%bv; getr (ms_regs msx) 11%bv; getr (ms_regs msx) 12%bv; getr (ms_regs msx) 13%bv] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
set (Ev1 := havoc Ex 1100 [getr (ms_regs msx) 10%bv; getr (ms_regs msx) 11%bv; getr (ms_regs msx) 12%bv; getr (ms_regs msx) 13%bv]) in HS;
assert (AG1 : forall n, (n < 1100)%nat -> ew Ev1 n = ew Ex n) by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; subst Ev1; apply ew_havoc_old; exact Hn);
assert (EH : forall i r, (i < 4)%nat -> nth i [10%bv; 11%bv; 12%bv; 13%bv] 0%bv = r -> sv_denot Ev1 (SOff (1100 + i) 0) = getr (ms_regs msx) r)
  by (let i := fresh "i" in let r := fresh "r" in let Hi := fresh "Hi" in let Hr := fresh "Hr" in
      intros i r Hi Hr; cbn [sv_denot]; subst Ev1; rewrite (ew_havoc_new Ex 1100 _ i (Z_to_bv 64 0)) by (cbn; lia);
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; subst r; do 4 (destruct i as [|i]; [reflexivity|]); lia);
assert (E1100 : ew Ev1 1100 = getr (ms_regs msx) 10%bv)
  by (rewrite <- (EH 0%nat 10%bv ltac:(lia) eq_refl); cbn [sv_denot Nat.add]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
n_setr HS EH (0%nat) (10%bv : bv 5); n_setr HS EH (1%nat) (11%bv : bv 5); n_setr HS EH (2%nat) (12%bv : bv 5); n_setr HS EH (3%nat) (13%bv : bv 5);
clear EH end; nnorm HS.
(* finish a path at the release: apply the release lemma *)
Ltac n_finish HS HJ AGR retv hq :=
let R10 := fresh "R10" in prreg HS (10%bv : bv 5) R10;
let Ev1 := fresh "Ev1" in let AG1 := fresh "AG1" in let E1100 := fresh "E1100" in
n_canon HS Ev1 AG1 E1100;
lazymatch type of HS with st_ok_pi _ _ ?Ev1x _ (restrict _ ?msx) =>
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
let HEIx := lazymatch goal with H : img_env _ _ _ |- _ => H end in
eapply (n_release B ASF FFL LAWS ML _ _ _ _ _ _ _ _ _ msx mdx _ _ Ev1x retv ltac:(eassumption) ltac:(eassumption)
  ltac:(subst Ev1; apply img_env_havoc_hi; [exact HEIx | unfold A_LIM; lia]) HS HJ ltac:(eassumption) ltac:(eassumption)
  ltac:(eassumption));
[ let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in
  intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
  rewrite AG1 by lia; n_evE; apply AGR; exact Hn
| rewrite AG1 by lia; n_evE; assumption
| rewrite AG1 by lia; n_evE; assumption
| rewrite AG1 by lia; n_evE; assumption
| rewrite AG1 by lia; n_evE; assumption
| rewrite AG1 by lia; n_evE; assumption
| rewrite E1100, R10; cbn [sv_denot]; n_evE; first [reflexivity | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; assumption | idtac]
| hq ] end end.

(* the walk from strtol's return to number's return *)
Lemma n_segB : forall ly S W (regs : bvmap 5 word) mem md ch (w out : Z) (wd : list byte) ms md3 S2 fpos Ev,
afn_pre SEGS B NUMBER_STK ly S W regs mem md ch ->
out mod 4 = 0 ->
((exists cid pos, In (cid, pos) (frames S) /\
   frame_addr ly cid pos <= out /\ out + 4 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
 (spZ regs <= out /\ out + 4 <= ly_top ly)) ->
4096 <= w -> w + Z.of_nat (length wd) + 1 <= 2 ^ 47 ->
img_env VAL A_LIM Ev ->
st_ok_pi SEGS VAL Ev ss_nB (restrict (w_H W) ms) ->
ajournal SEGS B NUMBER_STK (spZ regs) [(out, out + 4)] ly S W mem md [(0, fpos)] ly S2 W (ms_mem ms) md3 0 ->
frames S2 = (0, fpos) :: frames S -> ablocks B ly S2 = ablocks B ly S -> (exists f, S2 = set_fs f S) ->
st_nev S2 <= st_nev S ->
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ev n = getr regs r) ->
getr regs 10 = w64 w -> getr regs 11 = w64 out ->
ew Ev 32 = Z_to_bv 64 SB -> ew Ev 33 = Z_to_bv 64 (nsp1 (spZ regs)) ->
ew Ev 1028 = Z_to_bv 64 (frame_addr ly 0 fpos) -> ew Ev 1040 = Z_to_bv 64 (flag_addr ly 0 fpos) ->
ew Ev 1041 = Z_to_bv 64 (SB + frame_addr ly 0 fpos / 8) ->
ew Ev 1046 = Z_to_bv 64 (__intscan_c.s10_val wd) -> ew Ev 1058 = Z_to_bv 64 (w + __intscan_c.s10_end wd) ->
ew Ev 1059 = Z_to_bv 64 (n_byte0 wd) ->
(* the word at this state: its bytes, its shadow, its place (below the frames' and the stack's ranges, outside
   the frame, the result cell and the shadow band) *)
astr_at SEGS W (ms_mem ms) w wd ->
range_addressable (rdW W (ms_mem ms)) SHADOW_OFF w (Z.of_nat (length wd) + 1) ->
(forall a, w <= a <= w + Z.of_nat (length wd) ->
  (a < kLowShadowBeg \/ kHighShadowEnd <= a) /\ a < alloc_ceiling /\
  (a < frame_addr ly 0 fpos \/ frame_addr ly 0 fpos + 64 <= a) /\ (a < out \/ out + 4 <= a)) ->
(* the result cell at this state: its shadow, its bytes are the entry's, and it is present *)
range_addressable (rdW W (ms_mem ms)) SHADOW_OFF out 4 ->
(forall i, 0 <= i < 4 -> rdW W (ms_mem ms) (out + i) = rdW W mem (out + i)) ->
(forall a, out <= a < out + 4 -> apresent (w_H W) (ms_mem ms) a) ->
SRr SEGS W (mkCfg ms md3) (apost_base SEGS B NUMBER_STK [(out, out + 4)] regs ly S W mem md EV_NUMBER (n_Q B ly S W mem out wd)).
Proof.
intros ly S W regs mem md ch w out wd ms md3 S2 fpos Ev HPRE Hout4 HOUT Hw4096 Hw47 HEI HS HJ Hfrs2 Eab HS2f Hnev2
AGR H10 H11 E32 E33 E1028 E1040 E1041 E1046 E1058 E1059 HWB HWRA HWP HORA OUTK HOP.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : NUMBER_STK = 12400) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
set (sp0 := spZ regs) in *. set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
set (len := Z.of_nat (length wd)) in *.
pose proof (proj1 HJ) as HAR3.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 Hfin2) as (HFal32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR3 Hfin2) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B ly S2 W _ _ 0 fpos HAR3 Hfin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F in HFal32, HFapp, HFpres, HFSpres, HF4096, HFceil, HF64.
assert (HF8b : 512 <= F / 8 <= 2 ^ 44 - 8) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
assert (U2 : bv_unsigned (ew Ev 2) = sp0) by (rewrite (AGR 2%nat 2%bv eq_refl); reflexivity).
assert (U10 : bv_unsigned (ew Ev 10) = w) by (rewrite (AGR 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew Ev 11) = out) by (rewrite (AGR 11%nat 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; destruct HOUT as [(c & p & Hc & Hp1 & Hp2) | (Hs1 & Hs2)]; [destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR Hc) | ]; lia).
assert (U32 : bv_unsigned (ew Ev 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U1028 : bv_unsigned (ew Ev 1028) = F) by (rewrite E1028; apply unsigned_lit_small; lia).
assert (UB : U Ev (SOff 32 0) = SHADOW_OFF) by (rewrite (U_atom Ev 32 SB E32) by (unfold SB; lia); reflexivity).
(* the result cell: where it is, and that a write to it is the walk's footprint *)
assert (HOUTZ : 4096 <= out /\ out + 4 <= 2 ^ 47 /\ (out + 4 <= kLowMemEnd \/ kHighMemBeg <= out) /\
  forall a, out <= a < out + 4 -> awr_prog_or_caller SEGS B sp0 [(out, out + 4)] (frames S) ly a).
{ destruct HOUT as [(c & p & Hc & Hp1 & Hp2) | (Hs1 & Hs2)].
- destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR Hc) as (Hc0 & Hc1 & Hc2).
unfold in_app, ASAN_CEIL in Hc2. rewrite C3 in Hc2 |- *. unfold kLowShadowBeg in Hc2. rewrite C5.
split; [lia|]. split; [lia|]. split; [lia|].
intros a Ha. right; right. split; [exists (out, out + 4); split; [left; reflexivity | cbn; lia]|].
exists c, p. split; [exact Hc|]. left. unfold in_zr. cbn [fst snd]. lia.
- split; [lia|]. split; [lia|]. split; [rewrite C3; lia|].
intros a Ha. right; left. split; [exists (out, out + 4); split; [left; reflexivity | cbn; lia]|]. lia. }
destruct HOUTZ as (Hout0 & Hout47 & Houtz & HOUTW).
(* the result cell is not in the image: a frame byte, or above the stack pointer *)
assert (HOUTI : forall a, out <= a < out + 4 -> ~ in_img SEGS a).
{ intros a Ha Hi. destruct HOUT as [(ocid & opos & Hoin & Hoa & Hob) | (Hos & Hot)].
- exact (frm_img SEGS B LAWS ly S W mem md ocid opos a HAR Hoin ltac:(lia) Hi).
- pose proof (Hsegs a Hi). lia. }
assert (U11' : U Ev (SOff 11 0) = out) by (rewrite (U_atom Ev 11 out); [reflexivity | rewrite (AGR 11%nat 11%bv eq_refl), H11; reflexivity | lia]).
assert (U10' : U Ev (SOff 10 0) = w) by (rewrite (U_atom Ev 10 w); [reflexivity | rewrite (AGR 10%nat 10%bv eq_refl), H10; reflexivity | lia]).
(* the shadow knowledge of the token runs: the result cell's 4 bytes are addressable *)
assert (SHOK : sh_ok SEGS (SOff 32 0) n_SH Ev (mrestrict (w_H W) (ms_mem ms))).
{ unfold sh_ok, n_SH. apply Forall_cons; [|apply Forall_nil]. split; cbn [she_m she_lo she_hi].
- rewrite Z.add_0_r, Z.sub_0_r. rewrite U11'. eapply (obl_of_range SEGS _ _ Ev (SOff 32 0) _ 4 out 4 HORA UB); lia.
- intros a Ha. cbn [she_m she_lo she_hi] in Ha. change (Z.min 0 4) with 0 in Ha. change (Z.max 0 4) with 4 in Ha. rewrite U11' in Ha. rewrite UB. unfold SHADOW_OFF. rewrite C3, C5 in Houtz. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite U10'.
eapply (obl_of_range SEGS _ _ Ev (SOff 32 0) _ 1 w (len + 1) HWRA UB); lia. }
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own => let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 11%nat out); [reflexivity | exact U11 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; right; apply HOUTW; lia |].
do 5 (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; rewrite FFS; lia | cbn; lia |].
apply awr_ok_nil. }
n_unch UN1 HFr. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the word's first byte is 0: the word is empty, number returns 0 *)
  rewrite branch_eq_U in Hc.
  assert (Hb0 : n_byte0 wd = 0).
  { lazymatch type of Hc with (U ?Ex (SOff 1059 0) =? U _ _) = true =>
    rewrite (U_atom Ex 1059 (n_byte0 wd)) in Hc; [| n_evE; exact E1059 | unfold n_byte0; pose proof (bv_unsigned_in_range 8 (nth 0 (wd ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R8; change (bv_modulus 8) with 256 in R8; lia] end.
    cbn in Hc. apply Z.eqb_eq in Hc. exact Hc. }
  assert (Hwd : wd = []) by (apply n_wd_nil; [exact (proj2 HWB) | exact Hb0]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 31612.
  all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => n_awr_ro end).
  n_unch UN2 HFr. clear HF HFr HG.
  n_finish HS HJ AGR 0 idtac.
  { rewrite E1059, Hb0. reflexivity. }
  { rewrite Hwd, Verbs.number_m_nil. split; [reflexivity|]. intros i Hi.
    rewrite (UN2 (out + i) ltac:(lia) (fun x => x)), (UN1 (out + i) ltac:(lia) (fun x => x)). apply OUTK. exact Hi. }
- (* the word has a first byte *)
  rewrite branch_eq_U in Hc.
  assert (Hb0 : n_byte0 wd <> 0).
  { lazymatch type of Hc with (U ?Ex (SOff 1059 0) =? U _ _) = false =>
    rewrite (U_atom Ex 1059 (n_byte0 wd)) in Hc; [| n_evE; exact E1059 | unfold n_byte0; pose proof (bv_unsigned_in_range 8 (nth 0 (wd ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R8; change (bv_modulus 8) with 256 in R8; lia] end.
    cbn in Hc. apply Z.eqb_neq in Hc. exact Hc. }
  assert (Hwd : wd <> []) by (intros ->; apply Hb0; reflexivity). clear Hc.
  (* the end pointer: inside the word *)
  pose proof (number.end_le wd) as HEL. fold len in HEL.
  set (e := w + __intscan_c.s10_end wd) in *.
  assert (Heb : w <= e <= w + len) by (subst e; lia).
  assert (HeB : 0 <= n_byteE wd < 256) by (unfold n_byteE; pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (__intscan_c.s10_end wd)) (wd ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R8; change (bv_modulus 8) with 256 in R8; lia).
  assert (HeV : rdW W (ms_mem ms0) e = Some (n_byteE wd)).
  { rewrite (UN1 e ltac:(lia) (fun x => x)). destruct HWB as [HWB1 _].
    pose proof (HWB1 (Z.to_nat (__intscan_c.s10_end wd)) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
    rewrite Z2Nat.id in Hb by lia. exact Hb. }
  (* drop the word's region, add the end byte's (atom 1070) *)
  n_keep_regions HS (fun r : YP09.region => negb (match r_base r with Some 10%nat => true | _ => false end)).
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?H ?msx) =>
  pose proof (st_ok_pi_havoc_hi 1070 Ex ssx (restrict H msx) [Z_to_bv 64 (n_byteE wd)] HS ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  assert (E1070 : ew Ex 1070 = Z_to_bv 64 (n_byteE wd)) by (lazymatch Ex with havoc ?E0 _ ?ws => exact (ew_havoc_new E0 1070 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)) end);
  pose proof (st_ok_pi_add_fact Ex ssx msx 1070 (mkAF 0 255 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E1070, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (Uc2 : bv_unsigned (ew Ex 2) = sp0) by (n_evE; exact U2);
  assert (Uc11 : bv_unsigned (ew Ex 11) = out) by (n_evE; exact U11);
  assert (Uc1028 : bv_unsigned (ew Ex 1028) = F) by (n_evE; exact U1028);
  assert (Uc1041 : bv_unsigned (ew Ex 1041) = SB + F / 8) by (n_evE; rewrite E1041; apply unsigned_lit_small; unfold SB; lia);
  assert (Uc1058 : bv_unsigned (ew Ex 1058) = e) by (n_evE; rewrite E1058; apply unsigned_lit_small; lia);
  assert (Ec1070 : ew Ex 1070 = Z_to_bv 64 (n_byteE wd)) by exact E1070 end.
  destruct (HWP e ltac:(lia)) as (He1 & He2 & He3 & He4).
  pose proof (conj He1 (conj He2 (conj He3 (conj He4 (conj HF4096 (conj HFceil (conj Hceil (conj Hstk0 (conj C1 (conj Hout0 (conj Hout47
    (conj HEL (conj Heb (conj Hw47 (conj HF8b (conj C2 (conj C3 (conj C5 (conj Hslo Hshi))))))))))))))))))) as AM.
  lazymatch type of AM with ?T => change (nam T) in AM end.
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev2 ?ssx (restrict ?H ?msx) =>
  assert (Rok : region_ok sg Ev2 (ms_mem (restrict H msx)) (YP09.mkRegion (Some 1058%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 1070 0))]));
  [ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite Uc1058; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ e 0 1 (SOff 1070 0) (n_byteE wd));
    [cbn [sv_denot]; rewrite Ec1070, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | rewrite Z.add_0_r; exact (n_val1 SEGS _ _ e _ HeV)] |];
  assert (Rdj : all_disjoint Ev2 (YP09.mkRegion (Some 1058%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 1070 0))]) (ss_mem ssx));
  [ ndj; (revert AM; unfold nam, off_img, zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB, NUMBER_STK in *; intros AM; repeat match goal with H : _ /\ _ |- _ => destruct H end; lia) |];
  pose proof (st_ok_pi_add_region Ev2 ssx (restrict H msx) (YP09.mkRegion (Some 1058%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 1070 0))]) HS eq_refl Rok Rdj) as HS3;
  clear HS Rok Rdj; rename HS3 into HS; nnorm HS end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  lazymatch Ex with havoc ?E0 _ _ =>
  assert (HEI1 : img_env VAL A_LIM Ex) by (apply img_env_havoc_hi; [first [exact HEI | lazymatch goal with H : img_env VAL A_LIM E0 |- _ => exact H end] | unfold A_LIM; lia]) end end.
  (* R2: to the test of the end pointer's byte *)
  n_shok SHOK2 HS SHOK. clear SHOK. rename SHOK2 into SHOK.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- Forall _ _ => apply Forall_cons; [|apply Forall_nil] | |- _ => idtac end.
    lazymatch goal with |- range_addressable _ _ (U ?Ex (SOff 1058 0)) 1 =>
    rewrite (U_atom Ex 1058 e); [| n_evE; exact E1058 | lia] end.
    eapply (obl_of_range SEGS _ _ _ (SOff 32 0) _ 1 w (len + 1)); [| n_evE; exact UB | lia | lia].
    eapply (n_ra_keep _ _ w (len + 1)); [lia | lia | | exact HWRA].
    intros y Hy. apply (UN1 y Hy). exact (fun q => q). }
  { n_awr_ro. }
  n_unch UN2 HFr. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* *end is not 0: the word has a tail, number returns 0 *)
    rewrite branch_ne_U in Hc.
    assert (HbE : n_byteE wd <> 0).
    { lazymatch type of Hc with negb (U ?Ex (SOff 1070 0) =? U _ _) = true =>
      rewrite (U_atom Ex 1070 (n_byteE wd)) in Hc; [| n_evE; exact Ec1070 | lia] end.
      cbn in Hc. apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
    assert (Hnone : Verbs.number_m wd = None).
    { apply number.nm_none. intros (_ & Hend & _). apply HbE. apply (n_end_iff wd (proj2 HWB)). exact Hend. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 31612.
    all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => n_awr_ro end).
    n_unch UN3 HFr. clear HF HFr HG.
    n_finish HS HJ AGR 0 idtac.
    { rewrite Hnone. split; [reflexivity|]. intros i Hi.
      rewrite (UN3 (out + i) ltac:(lia) (fun x => x)), (UN2 (out + i) ltac:(lia) (fun x => x)), (UN1 (out + i) ltac:(lia) (fun x => x)).
      apply OUTK. exact Hi. }
  + (* *end is 0: the whole word is the number; the range test *)
    rewrite branch_ne_U in Hc.
    assert (HbE : n_byteE wd = 0).
    { lazymatch type of Hc with negb (U ?Ex (SOff 1070 0) =? U _ _) = false =>
      rewrite (U_atom Ex 1070 (n_byteE wd)) in Hc; [| n_evE; exact Ec1070 | lia] end.
      cbn in Hc. apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
    assert (Hend : __intscan_c.s10_end wd = len) by (apply (n_end_iff wd (proj2 HWB)); exact HbE). clear Hc.
    assert (Hvr : -9223372036854775808 <= __intscan_c.s10_val wd <= 9223372036854775807) by (unfold __intscan_c.s10_val, __intscan_c.LMIN; lia).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 31576.
    all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => n_awr_ro end).
    n_unch UN3 HFr. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* out of range: number returns 0 *)
      assert (Hnone : Verbs.number_m wd = None).
      { apply number.nm_none. intros (_ & _ & Hr).
        lazymatch type of Hc with branch_taken BC_LTU (sv_denot ?Ex _) _ = true =>
        rewrite branch_ltu_U in Hc; rewrite (n_range_U Ex (__intscan_c.s10_val wd) ltac:(lia) ltac:(n_evE; exact E1046)) in Hc end.
        apply negb_true_iff, andb_false_iff in Hc. destruct Hc as [Hc|Hc]; apply Z.leb_gt in Hc; lia. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 31612.
      all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => n_awr_ro end).
      n_unch UN4 HFr. clear HF HFr HG.
      n_finish HS HJ AGR 0 idtac.
      { rewrite Hnone. split; [reflexivity|]. intros i Hi.
        rewrite (UN4 (out + i) ltac:(lia) (fun x => x)), (UN3 (out + i) ltac:(lia) (fun x => x)),
          (UN2 (out + i) ltac:(lia) (fun x => x)), (UN1 (out + i) ltac:(lia) (fun x => x)). apply OUTK. exact Hi. }
    * (* in range: the store, then number returns 1 *)
      assert (Hsome : Verbs.number_m wd = Some (__intscan_c.s10_val wd)).
      { apply number.nm_some; [exact Hwd | exact Hend |].
        lazymatch type of Hc with branch_taken BC_LTU (sv_denot ?Ex _) _ = false =>
        rewrite branch_ltu_U in Hc; rewrite (n_range_U Ex (__intscan_c.s10_val wd) ltac:(lia) ltac:(n_evE; exact E1046)) in Hc end.
        apply negb_false_iff, andb_true_iff in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
      (* the result cell is writable for the store *)
      n_rewin HS 11%nat 0 0 4 ltac:(n_evE; rewrite U11;
        intros o Ho; apply (apresent_writable SEGS);
        eapply (apresent_transfer SEGS (w_H W) (w_H W) (ms_mem ms)); [lia | apply HOUTI; lia | | apply HOP; lia];
        rewrite UN3, UN2, UN1 by (first [lia | exact (fun q => q)]); reflexivity).
      paj_run_to_tok RUNTO HS HJ SHOK Bspan 31612.
      all: try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ =>
        lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
        repeat first [ apply awr_ok_cons_ro; [cbn; lia|]
                     | eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 11%nat out);
                       [reflexivity | n_evE; exact U11 | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; right; apply HOUTW; lia |] ];
        apply awr_ok_nil end).
      lazymatch type of HFr with frame_of ?Ex _ _ _ => assert (Uz11 : bv_unsigned (ew Ex 11) = out) by (n_evE; exact U11) end.
      n_unch_out UN4 HFr out. clear HF HFr HG Uz11.
      (* the stored value: the result cell's region holds strtol's result in its 4 bytes *)
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      let i := eval vm_compute in (n_find (ss_mem ssx) 11%nat 0 0) in
      let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS ltac:(vm_compute; reflexivity)) as HR11;
      cbn [ms_mem restrict] in HR11 end.
      lazymatch type of HR11 with region_ok _ ?Ex _ (YP09.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi ?cs) =>
      pose proof (n_region_aval4 SEGS Ex _ _ 11 out cs lo hi wlo whi 0 (SOff 1046 0) (__intscan_c.s10_val wd) HR11
        ltac:(n_evE; exact U11) ltac:(cbn; tauto)
        ltac:(cbn [sv_denot]; n_evE; rewrite E1046, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as VOUT end.
      rewrite Z.add_0_r in VOUT. clear HR11.
      n_finish HS HJ AGR 1 idtac.
      { rewrite Hsome. split; [reflexivity | exact VOUT]. }
Qed.
End e.
End f.
End d.
