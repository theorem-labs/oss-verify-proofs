(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v (a walk) and ACa2.v (a class-1 side-stack frame): tnumber_spec of lib/A/Prog/number_c.v, from number's entry (0x8e430) through __asan_stack_malloc_0 and strtol to strtol's return, then numberB.v's n_segB. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberA.v, with its module paths and module names changed; 537 of its 673 lines of code are new or changed and 377 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): the head of
   refuse's image-B walk, from the entry (0x892f8) to the two cuts of refuse_K.v: 0x894ac (n_refusals < 8, then
   RB_PRE_stmt) and 0x89544 (n_refusals >= 8, then RB_REL_stmt). The image-B refuse walk lane of the image-B G3 walk owner, 2026-10-30;
   ADAPTED from plugin-hostd/fuzz_command lib/B/Prog/numberA.v and numberB.v (origin/ossv/recipes 501c0d516c69):
   the entry token run, __asan_stack_malloc_0 (here frame_alloc_0, 0x3e608) through aj_stack_malloc_atS, the
   re-seat and the frame's regions, a plain run, then token runs; re-derived on refuse's image-B code
   (refuse.fuzz_segconf.asan-ubsan.s).

   The runs and what each discharges:
   - 0x892f8 .. 0x8937c (token run, no check): the prologue, the variadic spill, the GOT loads, the
     use-after-return flag (decided: AR's constant flag cell holds 1, so 0x89374 `beqz` falls through).
   - frame_alloc_0 (SM0, SMP): the class-0 frame F; F <> 0 decides 0x89390 `bnez` (the real-stack fallback
     0x89394 .. 0x893ac is not reached).
   - 0x89380 .. 0x89414 (plain run): the frame header, its shadow f1 f1 f1 f1 f8 f3 f3 f3, the slot sp1 + 8, and
     UBSan trap T1 (0x89410, c & 7): decided by c's alignment (refuse_pre's c mod 16 = 0).
   - 0x89414 .. (token run over the c block, rb_SH): checks 1, 2, 3 (0x8942c load4 refused, 0x89448 load4
     n_refusals, 0x89494 load1 reading[0]) by the block's tokens; refused + 1 stored; the n test 0x89458 and UBSan
     trap T2 (0x89460 `bgeu n,9`) decided by n's range; UBSan trap T3 (0x8947c, the pointer-overflow test of
     c->refusal[n]) split and refuted (rb_T3: c + 0x2e88 + 200 n stays below 2 ^ 64); the where test 0x894a0 split.
   A run's slow paths (0x895e4 .. 0x8963c) and the `unimp` 0x895e0 are never reached. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI08 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16 YM05 YN2j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c refuse_f refuse_E refuse_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* UBSan trap T3 (0x8947c `bltu ~a0, a1` with a0 = c + 0x2e88, a1 = 200 n): never taken for a block below 2 ^ 47
   and n <= 7 *)
Lemma rb_T3 : forall E c nr, ew E 10 = Z_to_bv 64 c -> ew E 35 = Z_to_bv 64 nr -> 0 <= c -> c + 16616 <= 2 ^ 47 ->
0 <= nr <= 7 ->
(U E (SAlu ALU_XOR (SOff 10 11912) (SLit (-1))) <? U E (SMd M_MUL (SOff 35 0) (SLit 200))) = false.
Proof.
intros E c nr H10 H35 Hc0 Hc1 Hnr.
rewrite (U_not_off E 10 c 11912 H10) by lia.
rewrite U_SMd, (U_atom E 35 nr H35) by lia. rewrite U_SLit. cbn [zmd_raw].
unfold zcanon, M64. rewrite (Z.mod_small 200) by lia. rewrite Z.mod_small by lia.
apply Z.ltb_ge. lia.
Qed.
(* the stored refused + 1 (0x89434 `lw`, 0x8943c `addi`, 0x89440 `sw`): its low 32 bits are refused + 1 *)
Lemma rb_inc_mod : forall E rf, ew E 36 = Z_to_bv 64 rf -> 0 <= rf -> rf + 1 < 2 ^ 32 ->
U E (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) mod 2 ^ 32 = rf + 1.
Proof.
intros E rf H36 H0 H1.
rewrite U_SAlu, U_SExt, (U_atom E 36 rf H36) by lia. rewrite U_SLit. cbn [zalu_raw].
unfold zcanon, M64, bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small rf (2 ^ 32)) by lia.
rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
destruct (Z_lt_le_dec rf (2 ^ 31)) as [Hs|Hs].
- rewrite (Z.mod_small (rf + 2 ^ 31) (2 ^ 32)) by lia. replace (rf + 2 ^ 31 - 2 ^ 31) with rf by lia.
  rewrite (Z.mod_small rf (2 ^ 64)) by lia. rewrite (Z.mod_small (rf + 1) (2 ^ 64)) by lia.
  apply Z.mod_small. lia.
- rewrite <- (Z.mod_unique (rf + 2 ^ 31) (2 ^ 32) 1 (rf + 2 ^ 31 - 2 ^ 32)) by lia.
  replace (rf + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with (rf - 2 ^ 32) by lia.
  rewrite <- (Z.mod_unique (rf - 2 ^ 32) (2 ^ 64) (-1) (rf - 2 ^ 32 + 2 ^ 64)) by lia.
  rewrite (Z.mod_small (rf - 2 ^ 32 + 2 ^ 64 + 1) (2 ^ 64)) by lia.
  symmetry. apply (Z.mod_unique (rf - 2 ^ 32 + 2 ^ 64 + 1) (2 ^ 32) (2 ^ 32 - 1) (rf + 1)); lia.
Qed.
Lemma rb_le_byte_mod : forall v k, YG0f.le_byte v 4 k = YG0f.le_byte (v mod 2 ^ 32) 4 k.
Proof. intros v k. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma rb_chunk4_aval : forall {fx : YK11.FPState} segs E H (m : word -> option byte) base off e (v : Z),
YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
rd32 (aview segs H m) (base + off) v.
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
Lemma rb_region_aval4 : forall {fx : YK11.FPState} segs E H (m : word -> option byte) n b cs lo hi wlo whi od e v,
region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 4 e)) cs -> sv_denot E e = Z_to_bv 64 v ->
rd32 (aview segs H m) (b + od) v.
Proof.
intros fx segs E H m n b cs lo hi wlo whi od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (rb_chunk4_aval segs E H m b od e v Hck He).
Qed.
(* the index of the region with base atom b and low offset lo *)
Fixpoint rb_find (rs : smem) (b : nat) (lo : Z) (i : nat) : nat :=
match rs with
| [] => i
| r :: rs' => if (match YP09.r_base r with Some b' => Nat.eqb b b' | None => false end) && Z.eqb (YP09.r_lo r) lo
              then i else rb_find rs' b lo (S i)
end.
(* make the region with base atom b and low offset lo read-only *)
Ltac rb_ro_region HS bse lo :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
let i := eval vm_compute in (rb_find (ss_mem ssx) bse lo 0) in
let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r lo lo) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r lo lo (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
  ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; rnorm HS end.
Ltac rb_in_tac := let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; vm_compute in Hx; repeat (destruct Hx as [<- | Hx]; [vm_compute; repeat (first [left; reflexivity | right]) |]); destruct Hx.

Lemma rb_rd32_mod : forall (rd : YG0f.reader) a v w, rd32 rd a v -> v mod 2 ^ 32 = w mod 2 ^ 32 -> rd32 rd a w.
Proof.
intros rd a v w H Hm k Hk. rewrite (H k Hk). f_equal. rewrite (rb_le_byte_mod v k), (rb_le_byte_mod w k), Hm. reflexivity.
Qed.
Lemma rb_rdword_keep : forall (rd rd' : YG0f.reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a K. unfold rdword.
rewrite <- (Z.add_0_r a) at 1 2. rewrite (K 0), (K 1), (K 2), (K 3), (K 4), (K 5), (K 6), (K 7) by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma rb_ssp_keep : forall (rd rd' : YG0f.reader) gotw guard, sa_ssp rd gotw guard ->
(forall i, 0 <= i < 8 -> rd' (gotw + i) = rd (gotw + i)) -> (forall i, 0 <= i < 8 -> rd' (guard + i) = rd (guard + i)) ->
sa_ssp rd' gotw guard.
Proof.
intros rd rd' gotw guard (G1 & g & G2) K1 K2. split; [rewrite (rb_rdword_keep rd rd' gotw K1); exact G1|].
exists g. rewrite (rb_rdword_keep rd rd' guard K2). exact G2.
Qed.
(* the walk's entry state: refuse_E.v's ss_r0 without n_refusals' range (atom 35), which the walk adds at 0x89414,
   where the two cases (n < 8, n >= 8) part; everything before reads no n *)
Definition rb_atoms0q : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (N_SP1, mkAF (2^46) (2^47) 5); (N_SB, mkAF SB SB 0); (N_UAR, mkAF 0x10000 kImgEnd 2);
  (10%nat, mkAF 4096 (2^47 - 16616) 4); (11%nat, mkAF 0 (2^31 - 1) 0);
  (N_RF, mkAF 0 (2^32 - 2) 0); (N_RD0, mkAF 0 255 0) ].
Definition ss_q0 : sstate := mkSS AF_refuse sr_atoms rb_regions0 None (mkFacts rb_atoms0q [] rb_alias0).
(* raddreg with a report of the goal it cannot close *)
Ltac rb_addreg HS r rok :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ssx (restrict ?H ?msx) =>
let Rok := fresh "Rok" in let Rdj := fresh "Rdj" in let HS3 := fresh "HS3" in
assert (Rok : region_ok sg Ev (ms_mem (restrict H msx)) r);
[ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  first [ rok | match goal with |- ?G => idtac "RB_ADDREG_ROK_FAIL" G end; fail 1 ] |];
assert (Rdj : all_disjoint Ev r (ss_mem ssx));
[ rdj; first [ rzl | match goal with |- ?G => idtac "RB_ADDREG_DJ_FAIL" G end; fail 1 ] |];
pose proof (st_ok_pi_add_region Ev ssx (restrict H msx) r HS eq_refl Rok Rdj) as HS3;
clear HS Rok Rdj; rename HS3 into HS; rnorm HS end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a region over bytes a call left unchanged, whose write window is present after the call *)
Lemma rb_region_kept_pres : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
(* the shadow knowledge of the token runs: c's block, 16616 addressable bytes in application memory *)
Lemma rb_shok : forall E H mem c, bv_unsigned (ew E 10) = c -> ew E 32 = Z_to_bv 64 SB ->
range_addressable (aview SEGS H mem) SHADOW_OFF c 16616 -> in_app c 16616 -> 0 <= c -> c + 16616 <= 2 ^ 47 ->
sh_ok SEGS (SOff 32 0) rb_SH E (mrestrict H mem).
Proof.
intros E H mem c Uc E32 HRA Happ Hc0 Hc1.
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
assert (Uc' : U E (SOff 10 0) = c) by (rewrite U_SOff, Uc, Z.add_0_r; apply zcanon_id; unfold M64; lia).
unfold sh_ok, rb_SH. apply Forall_cons; [|apply Forall_nil]. split; cbn [she_m she_lo she_hi].
- rewrite Z.add_0_r, Z.sub_0_r, Uc'. eapply (obl_of_range SEGS _ _ E (SOff 32 0) _ 16616 c 16616 HRA UB); lia.
- intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha. rewrite Uc' in Ha. rewrite UB.
  revert Happ Ha. clear. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL. intros. lia.
Qed.
Section e.
Variable B : asyms.
Hypothesis SM0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Variables (STK RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z).
Hypothesis HSTK : 160 + 16 + 3 * ESTACK <= STK.
(* the stack-protector cells at every AR state (the image-A G3 walk owner's SSPX, image B's cells): used once, right after the
   frame take, where the journal's image clause cannot keep the two words; the head keeps them from there *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotw guard.
(* where the two cells lie (image B: 0xa3e98 and 0x5ff838, both image bytes) *)
Hypothesis HGW : 0x10000 <= gotw /\ gotw + 8 <= kImgEnd /\ 0x10000 <= guard /\ guard + 8 <= kImgEnd.
(* the default where (0x894a4 auipc + 0x894a8 addi: listing object 34) is the contract's literal "reac-pw.conf" *)
Hypothesis LIT34 : VAL (A_OBJ 34) = lit SegModel.S_base.
Hypothesis PRE : RB_PRE_stmt B STK RLO RHI lit gotw guard.
Hypothesis REL : RB_REL_stmt B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* the write windows of the head's token runs: the stack slots and c's refused cell (frames read-only) *)
Ltac rb_awr_tok U2 U33 U10 HCW HbinS2 sp0 c :=
lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
do 4 (apply awr_ok_cons_ro; [cbn; lia|]);
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |];
eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (rsp1 sp0 - sp0)); [reflexivity | rewrite U33; lia | cbn; lia | cbn; lia |];
do 4 (apply awr_ok_cons_ro; [cbn; lia|]);
eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 10%nat c); [reflexivity | exact U10 |
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; left; apply (HCW _ HbinS2 a); lia |];
apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.
(* what a token run of the head kept: everything but the stack slots and c's refused cell *)
Ltac rb_unch_tok UN U2 U33 U10 Hs1b sp0 c :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 176 <= a < sp0) \/ (c + 13516 <= a < c + 13520)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U33, ?U10 in Hrr; clear - Hrr Hs1b; lia |]);
  destruct Hin)) as UN end;
lazymatch goal with HF : frame_of _ _ _ _, HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ => clear HF HFr HG end.
Lemma rb_head : forall ly S W (regs : bvmap 5 word) mem md ch c line fp ln rcs f args,
rb_cx B STK RLO RHI lit gotw guard ly S W regs mem md ch c line fp ln rcs f args ->
SRr SEGS W (cfg_at SEGS (BASE + AF_refuse) regs mem md)
  (RB_POST B STK regs ly S W mem md c rcs (SegModel.refuse rcs ln f args)).
Proof.
intros ly S W regs mem md ch c line fp ln rcs f args HCX.
pose proof HCX as (HPRE & HROD & H10 & Hc64 & H11 & Hl64 & H12 & Hf64 & HRP & HROOM & HEV).
pose proof HRP as (Hc0 & Hc16 & HRC & HHEAP & HADDR & Hrfb & Hln & Hline & Hfin & Hck & Hfp0 & Hfpl & Hfl & Hva & Hvl & Hfrm & Hssp & Hlits).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
(* the block c lies in *)
pose proof HHEAP as (bc & mc & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS ly S W mem md bc mc HAR Hbin) as (Hbc16 & Hbc4096 & Hbcceil & Hbcapp & Hbcpres & _ & Hmc).
pose proof (req_size_pos0 mc ltac:(lia)) as [Hmc0 Hmcr].
pose proof (blk_off_imgP B ly S W mem md bc mc HAR Hbin) as Hbcimg.
(* the three cells refuse reads *)
pose proof (rf_rd_nref _ _ _ HRC) as Hnr. pose proof (rf_rd_refd _ _ _ HRC) as Hrf. pose proof (rf_rd_rd0 _ _ _ HRC) as Hrd0.
pose proof HRC as (bs & Hbs & Henc).
pose proof (rf_nref_le _ _ Henc) as Hn23.
destruct (rf_rd_byte _ _ _ 0x4080 HRC ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (v0 & Hv0 & Hv0r).
assert (Hrd0r : 0 <= SegModel.hd0 (rc_reading rcs) <= 255).
{ unfold seg_spec.RC_READING in Hrd0. rewrite Hrd0 in Hv0. injection Hv0 as <-. lia. }
pose proof Henc as (_ & _ & _ & _ & _ & _ & _ & (Hrf0 & _) & _).
assert (Hcb : 4096 <= c /\ c + 16616 <= alloc_ceiling /\ off_img c 16616).
{ unfold seg_spec.SEG_C_SIZE in Hb2. unfold off_img in *. lia. }
destruct Hcb as (Hcb0 & Hcb1 & Hcbimg).
change seg_spec.RC_NREF with 0x34c8 in Hnr. change seg_spec.RC_REFUSED with 0x34cc in Hrf.
change seg_spec.RC_READING with 0x4080 in Hrd0.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs (rb_extra (spZ regs) (as_uar_cell B) (Z.of_nat (length (rc_refusal rcs)))
  (rc_refused rcs) (SegModel.hd0 (rc_reading rcs))))) ss_q0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_refuse)) mem (seg_rom SEGS)))).
{ destruct (Nat.lt_ge_cases (length (rc_refusal rcs)) 8) as [Hq|Hq];
  [ pose proof (rb_entry B LAWS TL TLF false STK W ly S regs mem md ch c line (Z.of_nat (length (rc_refusal rcs)))
      (rc_refused rcs) (SegModel.hd0 (rc_reading rcs)) HPRE ltac:(lia) H10 H11 Hcb0 Hcb1 Hcbimg Hc16 ltac:(subst line; lia)
      ltac:(intros i Hi; apply (proj1 (Hbcpres (c + i) ltac:(unfold seg_spec.SEG_C_SIZE in Hb2; lia))))
      Hnr Hrf Hrd0 ltac:(cbn; lia) ltac:(lia) Hrd0r) as H0
  | pose proof (rb_entry B LAWS TL TLF true STK W ly S regs mem md ch c line (Z.of_nat (length (rc_refusal rcs)))
      (rc_refused rcs) (SegModel.hd0 (rc_reading rcs)) HPRE ltac:(lia) H10 H11 Hcb0 Hcb1 Hcbimg Hc16 ltac:(subst line; lia)
      ltac:(intros i Hi; apply (proj1 (Hbcpres (c + i) ltac:(unfold seg_spec.SEG_C_SIZE in Hb2; lia))))
      Hnr Hrf Hrd0 ltac:(cbn; lia) ltac:(lia) Hrd0r) as H0 ];
  exact (st_ok_pi_facts_incl _ _ _ rb_atoms0q rb_alias0 H0 ltac:(rb_in_tac) ltac:(rb_in_tac)). }
pose proof (ajournal_init SEGS B STK (refuse_W c rcs) ly S W regs mem md ch HPRE) as HJ.
set (E := Eimg (Ereg regs (rb_extra (spZ regs) (as_uar_cell B) (Z.of_nat (length (rc_refusal rcs))) (rc_refused rcs)
  (SegModel.hd0 (rc_reading rcs))))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (AGR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (rb_extra (spZ regs) (as_uar_cell B)
  (Z.of_nat (length (rc_refusal rcs))) (rc_refused rcs) (SegModel.hd0 (rc_reading rcs))) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth rb_extra map] in E32, E33, E34, E35, E36, E37. clear EX.
set (sp0 := spZ regs) in *.
destruct (rsp1_facts sp0 Hal16) as (Hs1al & Hs1).
assert (Hs1b : sp0 - 176 <= rsp1 sp0 <= sp0 - 160) by lia.
lazymatch type of Hs1 with ?T => change (ram T) in Hs1 end.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (AGR 2%nat 2%bv eq_refl); reflexivity).
assert (Usp1 : bv_unsigned (ew E 33) = rsp1 sp0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite (AGR 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
(* a byte of c's refused cell is a byte refuse may write: in its footprint and in the live block (bc, mc) *)
assert (HCW : forall bl, In (bc, mc) bl -> forall a, c + 13516 <= a < c + 13520 ->
  inFP (refuse_W c rcs) a /\ exists b n, In (b, n) bl /\ b <= a < b + req_size n).
{ intros bl Hbl a Ha. split.
  - exists (c + seg_spec.RC_REFUSED, c + seg_spec.RC_REFUSED + 4). split; [unfold refuse_W; apply in_or_app; left; left; reflexivity|].
    cbn [fst snd]. unfold seg_spec.RC_REFUSED. lia.
  - exists bc, mc. split; [exact Hbl|]. unfold seg_spec.SEG_C_SIZE in Hb2. lia. }
assert (Hcapp : in_app c 16616) by (unfold in_app in *; unfold seg_spec.SEG_C_SIZE in Hb2; lia).
pose proof HADDR as (_ & _ & _ & HCRA & _). change seg_spec.SEG_C_SIZE with 16616 in HCRA.
pose proof (rb_shok E (w_H W) mem c Uc E32 HCRA Hcapp ltac:(lia) ltac:(lia)) as SHOK.
unfold cfg_at. change (w64 (BASE + AF_refuse)) with (Z_to_bv 64 (BASE + AF_refuse)).
(* R1: the entry to the call of frame_alloc_0 (0x8937c) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ unfold ss_q0, rb_regions0, r_stk_lo, r_stk_hi, r_stk_s1, r_cnt, r_rd0; cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (rsp1 sp0 - sp0)); [reflexivity | rewrite Usp1; lia | cbn; lia | cbn; lia |].
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 10%nat c); [reflexivity | exact Uc | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. apply (HCW _ Hbin a). lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* the entry run writes its stack slots and c's refused cell only *)
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 176 <= a < sp0 \/ c + 13516 <= a < c + 13520) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Usp1, ?Uc in Hrr; clear - Hrr Hs1b; lia |]);
  destruct Hin)) as UNa.
clear HF HFr. rename HG into HGa.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
pose proof (palf_sm B TLF 0 ltac:(clear; cbn; tauto)) as SM0e. change (cs_stack_malloc 0) with SS___asan_stack_malloc_0 in SM0e.
rewrite SM0e.
pose proof (count_cid_le_length 0 (frames S)) as Hcnt.
(* frame_alloc_0 (0x3e608): the class-0 frame *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 (SM0 fx) ltac:(lia) W (ms_regs msX) (ms_mem msX) STK sp0
    (refuse_W c rcs) ly S W mem md [] ly S _ 0 (rsp1 sp0 - sp0) _ HJ) end.
  - unfold spZ. rewrite R2, E33, unsigned_lit_small by lia. lia.
  - unfold ram in Hs1. destruct Hs1 as [Hq|Hq]; rewrite Hq;
    [replace (sp0 - 160 - sp0) with (-160) by lia | replace (sp0 - 176 - sp0) with (-176) by lia]; reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite R3, (AGR 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (AGR 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold sa_room in HROOM. change (fs_frames 0) with 16384. lia. }
cbv beta. clear R2 R3 R4 R1 SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJc & (fS2 & ES2)).
pose proof (proj1 HJ) as HAR1. pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & Kuar1 & Kgot1 & Kguar1).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & Kuar2 & Kgot2 & Kguar2).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot1, Kgot2. rewrite (pal_cell B TL) in Kcell1, Kcell2.
rewrite (palf_got_uar B TLF) in Kguar1, Kguar2.
pose proof (palf_uar_img B TLF) as Huar. assert (Hkimg : kImgEnd = 0x602000) by reflexivity.
(* the stack-protector cells right after the frame take (SSPX) *)
pose proof (SSPX _ _ _ _ _ HAR2) as Hssp2.
(* c's block at the new state *)
assert (HbinS2 : In (bc, mc) (ablocks B ly S2)) by (rewrite Eab; exact Hbin).
destruct (al_blocks _ _ LAWS ly S2 W mem2 md2 bc mc HAR2 HbinS2) as (_ & _ & _ & _ & Hbcpres2 & _).
pose proof HK as (KK1 & KK2 & KK3 & KK4 & KK5 & KK6).
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1;2;3;4;5;6;7;8]%nat HS2.
match type of HS2 with ?A -> _ => assert (HQ : A); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp1 | lia | lia | lia | lia | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
  [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1) |
   exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
  [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1) |
   exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia].
- apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
  [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kguar1) |
   exact (val_mem_of_rdword SEGS _ _ _ _ Kguar2) | lia].
- apply (region_kept_val_at E _ _ 34 (as_uar_cell B) 4 1);
  [rewrite E34; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar1) |
   exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar2) | lia].
- apply (rb_region_kept_pres E (w_H W) _ _ 10 c); [exact Uc | |].
  + intros a Ha. replace a with (bc + (a - bc)) by lia. apply (KK2 bc mc (a - bc) Hbin);
    [unfold seg_spec.SEG_C_SIZE in Hb2; lia | intros Hf; exact Hf].
  + intros a Ha. apply (proj1 (Hbcpres2 a ltac:(unfold seg_spec.SEG_C_SIZE in Hb2; lia))).
- apply (rb_region_kept_pres E (w_H W) _ _ 10 c); [exact Uc | |].
  + intros a Ha. replace a with (bc + (a - bc)) by lia. apply (KK2 bc mc (a - bc) Hbin);
    [unfold seg_spec.SEG_C_SIZE in Hb2; lia | intros Hf; exact Hf].
  + intros a Ha. lia. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
(* the frame of class 0, its flag cell and its shadow *)
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg.
destruct (frame_al64 SEGS B ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
fold F FL in HFal32, HFapp, HFpres, HFSpres, HF4096, HFceil, HFimg, HF64, Hz, Hflag.
set (Ev1 := YN3v.havoc E 1024 (map (getr regs2) CLOB)) in HS.
assert (AG1 : forall n, (n < 1024)%nat -> ew Ev1 n = ew E n) by (intros n Hn; subst Ev1; apply ew_havoc_old; exact Hn).
assert (E1028 : ew Ev1 1028 = Z_to_bv 64 F) by (subst Ev1; change 1028%nat with (1024 + 4)%nat;
  rewrite (ew_havoc_new E 1024 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map CLOB]; exact Ha0).
assert (HEI1 : img_env VAL A_LIM Ev1) by (subst Ev1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
pose proof (st_ok_pi_havoc_hi 1040 Ev1 _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS; rename HS3 into HS.
set (Ev2 := YN3v.havoc Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) in HS.
assert (AG2 : forall n, (n < 1024)%nat -> ew Ev2 n = ew E n) by (intros n Hn; subst Ev2; rewrite ew_havoc_old by lia; apply AG1; exact Hn).
assert (E2_1028 : ew Ev2 1028 = Z_to_bv 64 F) by (subst Ev2; rewrite ew_havoc_old by lia; exact E1028).
assert (E2_1040 : ew Ev2 1040 = Z_to_bv 64 FL) by (subst Ev2; exact (ew_havoc_new Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2_1041 : ew Ev2 1041 = Z_to_bv 64 (SB + F / 8)) by (subst Ev2; exact (ew_havoc_new Ev1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env VAL A_LIM Ev2) by (subst Ev2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (U2 : bv_unsigned (ew Ev2 2) = sp0) by (rewrite AG2 by lia; exact Usp).
assert (U33 : bv_unsigned (ew Ev2 33) = rsp1 sp0) by (rewrite AG2 by lia; exact Usp1).
assert (U10 : bv_unsigned (ew Ev2 10) = c) by (rewrite AG2 by lia; exact Uc).
assert (E2_32 : ew Ev2 32 = Z_to_bv 64 SB) by (rewrite AG2 by lia; exact E32).
assert (U1028 : bv_unsigned (ew Ev2 1028) = F) by (rewrite E2_1028; apply unsigned_lit_small; lia).
destruct (al_flag _ _ LAWS ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLapp & HFLceil).
fold FL in HFLpres, HFLown, HFLapp, HFLceil.
assert (HFL0 : 4096 <= FL) by (unfold in_app in HFLapp; lia).
assert (U1040 : bv_unsigned (ew Ev2 1040) = FL) by (rewrite E2_1040; apply unsigned_lit_small; lia).
assert (U1041 : bv_unsigned (ew Ev2 1041) = SB + F / 8).
{ rewrite E2_1041; apply unsigned_lit_small. assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SB; lia. }
assert (UO0 : bv_unsigned (ew Ev2 241) = VAL (A_OBJ 0)) by exact (HEI2 (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (UO1 : bv_unsigned (ew Ev2 242) = VAL (A_OBJ 1)) by exact (HEI2 (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (UO12 : bv_unsigned (ew Ev2 253) = VAL (A_OBJ 12)) by exact (HEI2 (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U34 : bv_unsigned (ew Ev2 34) = as_uar_cell B) by (rewrite AG2, E34 by lia; apply unsigned_lit_small; lia).
assert (Hcin : bc <= c /\ c + 16616 <= bc + req_size mc) by (unfold seg_spec.SEG_C_SIZE in Hb2; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
lazymatch type of Hsep with ?T => change (ram T) in Hsep end.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; rewrite HF64, Z.add_0_r in D; exact D).
assert (HF8d : F / 8 = 8 * (F / 64)) by (rewrite HFq at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8 : F / 8 * 8 = F) by lia.
assert (HF8m : (F / 8) mod 8 = 0) by (rewrite HF8d, Z.mul_comm; apply Z_mod_mult).
assert (HF8b : 512 <= F / 8 <= 2 ^ 44) by lia.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 1028 (mkAF 4096 (2 ^ 47) 6) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1028; change (2 ^ 6) with 64; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1040 (mkAF 4096 (2 ^ 47) 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1040; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 1041 (mkAF (SB + 512) (SB + 2 ^ 44) 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1041; change (2 ^ 3) with 8;
split; [lia|]; split; [unfold SB; rewrite Zplus_mod, HF8m; reflexivity | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 1028 32 1041 F SB E2_1028 ltac:(lia) E2_32 E2_1041)) as HS3;
clear HS; rename HS3 into HS end.
rnorm HS.
assert (Hz8 : forall i, 0 <= i < 8 -> aview SEGS (w_H W) mem2 (SB + F / 8 + i) = Some 0).
{ intros i Hi. pose proof (Hz i Hi) as Q. unfold shadow_of_addr in Q. exact Q. }
assert (HFS8 : forall i, 0 <= i < 8 -> apresent (w_H W) mem2 (SB + F / 8 + i)).
{ intros i Hi. exact (proj1 (HFSpres i Hi)). }
(* c's block apart from the frame (sep_block_frame) and from the frame's shadow (application memory) *)
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 bc mc 0 fpos HAR2 HbinS2 Hfin2) as HWF.
unfold zdisjoint in HWF. cbn [fst snd] in HWF. change (fs_frame_bytes 0) with 64 in HWF. fold F in HWF.
lazymatch type of HWF with ?T => change (ram T) in HWF end.
pose proof (conj Hob0 (conj Hob1 (conj Hob12 (conj Huar (conj Hsep (conj HFimg (conj HF4096 (conj HFceil (conj HFapp
(conj Hceil (conj Hslo (conj Hshi (conj H47 (conj Hs1 (conj C1 (conj HF8b (conj HF8 (conj Hkimg (conj HWF
(conj Hcb0 (conj Hcb1 (conj Hcbimg (conj Hcapp (conj Hcin (conj Hes HSTK))))))))))))))))))))))))) as AM.
lazymatch type of AM with ?T => change (ram T) in AM end.
rb_addreg HS (YP09.mkRegion (Some 1028%nat) 40 64 40 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ F 56 8 _ FL);
[cbn [sv_denot]; rewrite E2_1040, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ]).
rb_addreg HS (YP09.mkRegion (Some 1028%nat) 32 40 32 40 [])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | apply Forall_nil ]).
rb_addreg HS (YP09.mkRegion (Some 1028%nat) 0 32 0 32 [])
ltac:(rewrite U1028; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | apply Forall_nil ]).
rb_addreg HS (YP09.mkRegion (Some 1041%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))])
ltac:(rewrite U1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (HFS8 o ltac:(lia))
| apply Forall_cons; [|apply Forall_nil]; eapply (chunk_ok_val SEGS _ _ (SB + F / 8) 0 8 _ 0);
[reflexivity | zside | zside | rewrite Z.add_0_r; apply val_mem_zero8; exact Hz8] ]).
assert (INF : forall a, F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 -> in_frames ly [(0, fpos)] a).
{ intros a Ha. exists 0, fpos. split; [left; reflexivity|]. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
  change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. fold F. unfold SB in Ha. lia. }
(* R2: the plain run from frame_alloc_0's return to 0x89414: the frame header, its shadow, sp1 + 8, trap T1 *)
paj_run_to_shc RUNTOP HS HJ2 RB_HEAD.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 1041%nat (SB + F / 8)); [reflexivity | exact U1041 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; apply INF; lia |].
  do 3 (eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 1028%nat F); [reflexivity | exact U1028 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; apply INF; lia |]).
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 33%nat (rsp1 sp0 - sp0)); [reflexivity | rewrite U33; lia | cbn; lia | cbn; lia |].
  do 4 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply (awr_ok_cons_gen B _ _ _ _ _ _ _ _ _ _ _ 10%nat c); [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. left. apply (HCW _ HbinS2 a). lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (SB + F / 8 <= a < SB + F / 8 + 8) \/ (F <= a < F + 64) \/ (sp0 - 176 <= a < sp0) \/ (c + 13516 <= a < c + 13520)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U33, ?U1028, ?U1041, ?U10 in Hrr; clear - Hrr Hs1b; lia |]);
  destruct Hin)) as UNb.
clear HF HFr. rename HG into HGb.
(* the token runs of the head only read the frame and its shadow *)
rb_ro_region HS 1041%nat 0. rb_ro_region HS 1028%nat 0. rb_ro_region HS 1028%nat 32. rb_ro_region HS 1028%nat 40.
pose proof (proj1 HJ2) as HAR3.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
pose proof (range_addressable_of_block SEGS B LAWS ly S2 W (ms_mem msx) _ bc mc c 16616 HAR3 HbinS2 Hb1 ltac:(lia)) as HCRA3;
pose proof (rb_shok Ev2 (w_H W) (ms_mem msx) c U10 E2_32 HCRA3 Hcapp ltac:(lia) ltac:(lia)) as SHOK end.
(* the bytes of c's block and the stack-protector cells are not in any write window of the head *)
assert (NOTW : forall a, (c <= a < c + 16616 /\ ~ (c + 13516 <= a < c + 13520)) \/ (0x10000 <= a < kImgEnd) ->
  ~ ((SB + F / 8 <= a < SB + F / 8 + 8) \/ (F <= a < F + 64) \/ (sp0 - 176 <= a < sp0) \/ (c + 13516 <= a < c + 13520))).
{ intros a Ha. lazymatch goal with AMx : ram _ |- _ => revert AMx end. revert Ha. clear.
  unfold ram, off_img, zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB; intros.
  repeat match goal with H : _ /\ _ |- _ => destruct H end. lia. }
assert (E2_35 : ew Ev2 35 = Z_to_bv 64 (Z.of_nat (length (rc_refusal rcs)))) by (rewrite AG2 by lia; exact E35).
assert (U35 : bv_unsigned (ew Ev2 35) = Z.of_nat (length (rc_refusal rcs))) by (rewrite E2_35; apply unsigned_lit_small; lia).
destruct (Nat.lt_ge_cases (length (rc_refusal rcs)) 8) as [Hn8|Hn8].
- (* n_refusals < 8: the slot, then RB_PRE_stmt *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  pose proof (st_ok_pi_add_fact Ex _ _ 35 (mkAF 0 7 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U35; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  rnorm HS.
  (* R3: the token run over c's block: checks 1-3, refused + 1, the n test and trap T2, up to trap T3 *)
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan RB_PRE.
  { rb_awr_tok U2 U33 U10 HCW HbinS2 sp0 c. }
  rb_unch_tok UNc U2 U33 U10 Hs1b sp0 c.
  assert (E2_10 : ew Ev2 10 = Z_to_bv 64 c) by (rewrite AG2 by lia; rewrite (AGR 10%nat 10%bv eq_refl), H10; reflexivity).
  assert (E2_36 : ew Ev2 36 = Z_to_bv 64 (rc_refused rcs)) by (rewrite AG2 by lia; exact E36).
  (* UBSan trap T3 (0x8947c): not taken *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { exfalso. rewrite branch_ltu_U in Hc. rewrite (rb_T3 Ev2 c _ E2_10 E2_35 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
    discriminate Hc. }
  clear Hc.
  (* R4: to the where test (0x894a0) *)
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan RB_PRE.
  { rb_awr_tok U2 U33 U10 HCW HbinS2 sp0 c. }
  rb_unch_tok UNd U2 U33 U10 Hs1b sp0 c.
  assert (E2_37 : ew Ev2 37 = Z_to_bv 64 (SegModel.hd0 (rc_reading rcs))) by (rewrite AG2 by lia; exact E37).
  (* the where test (0x894a0 `bnez reading[0]`) *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* reading[0] <> 0: where = c->reading *)
    assert (Hrd0n : SegModel.hd0 (rc_reading rcs) <> 0).
    { rewrite branch_ne_U in Hc. rewrite (U_atom Ev2 37 _ E2_37 ltac:(lia)), U_SLit in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
    paj_run_to_tok RUNTO HS HJ2 SHOK Bspan RB_PRE.
    { rb_awr_tok U2 U33 U10 HCW HbinS2 sp0 c. }
    rb_unch_tok UNe U2 U33 U10 Hs1b sp0 c.
    prreg HS (13%bv : bv 5) R13.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msF end;
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let i := eval vm_compute in (rb_find (ss_mem ssx) 10%nat 13512 0) in
    let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS ltac:(vm_compute; reflexivity)) as HRcnt;
    cbn [ms_mem restrict] in HRcnt end;
    pose proof (rb_region_aval4 SEGS Ev2 (w_H W) _ 10 c _ _ _ _ _ 13516 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) _
      HRcnt U10 ltac:(left; reflexivity) (eq_sym (Z_to_bv_bv_unsigned _ _))) as Vrf;
    assert (RF1 : rd32 (rdW W (ms_mem msF)) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1));
    [ change seg_spec.RC_REFUSED with 13516; apply (rb_rd32_mod _ _ _ _ Vrf);
      change (bv_unsigned (sv_denot Ev2 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1))))
        with (U Ev2 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)));
      rewrite (rb_inc_mod Ev2 (rc_refused rcs) E2_36 ltac:(lia) Hrfb); symmetry; apply Z.mod_small; lia |];
    assert (KEEPC : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
      rdW W (ms_mem msF) (c + i) = rdW W mem (c + i));
    [ let i := fresh "i" in let Hi := fresh "Hi" in let Hni := fresh "Hni" in let Hn := fresh "Hn" in
      intros i Hi Hni; change seg_spec.SEG_C_SIZE with 16616 in Hi; change seg_spec.RC_REFUSED with 13516 in Hni;
      pose proof (NOTW (c + i) ltac:(left; lia)) as Hn;
      rewrite UNe, UNd, UNc, UNb by (first [lia | cbv beta; tauto]);
      replace (c + i) with (bc + (c + i - bc)) by lia;
      rewrite (KK2 bc mc (c + i - bc) Hbin ltac:(lia) (fun Hf => Hf));
      replace (bc + (c + i - bc)) with (c + i) by lia;
      apply UNa; [lia | cbv beta; lia] |];
    assert (SSP : sa_ssp (rdW W (ms_mem msF)) gotw guard);
    [ apply (rb_ssp_keep (rdW W mem2) _ gotw guard Hssp2);
      [ let i := fresh "i" in let Hi := fresh "Hi" in let Hn := fresh "Hn" in intros i Hi;
        pose proof (NOTW (gotw + i) ltac:(right; lia)) as Hn;
        rewrite UNe, UNd, UNc, UNb by (first [lia | cbv beta; tauto]); reflexivity
      | let i := fresh "i" in let Hi := fresh "Hi" in let Hn := fresh "Hn" in intros i Hi;
        pose proof (NOTW (guard + i) ltac:(right; lia)) as Hn;
        rewrite UNe, UNd, UNc, UNb by (first [lia | cbv beta; tauto]); reflexivity ] |];
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (rb_canon_ok Hh Ex ssx msx 1100 RB_PRE_CLOB (ss_mem ssx) RB_PRE (f_atoms (ss_facts ss_pre)) [] (f_alias (ss_facts ss_pre)) HS
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(rb_in_tac) (fun x (Hx : In x []) => match Hx with end) ltac:(rb_in_tac)) as HS3 end;
    lazymatch type of HS3 with st_ok_pi _ _ _ ?x _ => replace x with ss_pre in HS3 by (vm_compute; reflexivity) end;
    lazymatch type of HS3 with st_ok_pi _ _ ?Ev3x _ _ => set (Evq := Ev3x) in HS3 end;
    assert (HEIq : img_env VAL A_LIM Evq) by (subst Evq; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]);
    assert (AGq : forall n, (n < 1100)%nat -> ew Evq n = ew Ev2 n) by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; subst Evq; apply ew_havoc_old; exact Hn);
    refine (PRE ly S W regs mem md ch c line fp ln rcs f args msF _ S2 fpos Evq HCX HSTK Hn8 HEIq HS3 HJ2 Hfrs2 Eab (ex_intro _ fS2 ES2)
      _ _ _ _ _ _ _ _ _ _ _ KEEPC RF1 SSP);
    [ let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in
      intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite AGq, AG2 by lia; apply AGR; exact Hn
    | rewrite AGq, AG2 by lia; exact E32
    | rewrite AGq, AG2 by lia; exact E33
    | rewrite AGq, AG2 by lia; exact E34
    | rewrite AGq, AG2 by lia; exact E35
    | rewrite AGq, AG2 by lia; exact E36
    | rewrite AGq, AG2 by lia; exact E37
    | rewrite AGq by lia; exact E2_1028
    | rewrite AGq by lia; exact E2_1040
    | rewrite AGq by lia; exact E2_1041
    | subst Evq; change 1101%nat with (1100 + 1)%nat; rewrite (ew_havoc_new _ 1100 _ 1 (Z_to_bv 64 0)) by (cbn; lia);
      cbn [nth map RB_PRE_CLOB]; rewrite R13; (destruct (Z.eqb_spec (SegModel.hd0 (rc_reading rcs)) 0) as [Hq|_]; [contradiction|]; rewrite U10; unfold seg_spec.RC_READING; reflexivity) ].
  + (* reading[0] = 0: where = "reac-pw.conf" (listing object 34) *)
    assert (Hrd00 : SegModel.hd0 (rc_reading rcs) = 0).
    { rewrite branch_ne_U in Hc. rewrite (U_atom Ev2 37 _ E2_37 ltac:(lia)), U_SLit in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
    paj_run_to_tok RUNTO HS HJ2 SHOK Bspan RB_PRE.
    { rb_awr_tok U2 U33 U10 HCW HbinS2 sp0 c. }
    rb_unch_tok UNe U2 U33 U10 Hs1b sp0 c.
    prreg HS (13%bv : bv 5) R13.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msF end;
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let i := eval vm_compute in (rb_find (ss_mem ssx) 10%nat 13512 0) in
    let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS ltac:(vm_compute; reflexivity)) as HRcnt;
    cbn [ms_mem restrict] in HRcnt end;
    pose proof (rb_region_aval4 SEGS Ev2 (w_H W) _ 10 c _ _ _ _ _ 13516 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) _
      HRcnt U10 ltac:(left; reflexivity) (eq_sym (Z_to_bv_bv_unsigned _ _))) as Vrf;
    assert (RF1 : rd32 (rdW W (ms_mem msF)) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1));
    [ change seg_spec.RC_REFUSED with 13516; apply (rb_rd32_mod _ _ _ _ Vrf);
      change (bv_unsigned (sv_denot Ev2 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1))))
        with (U Ev2 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)));
      rewrite (rb_inc_mod Ev2 (rc_refused rcs) E2_36 ltac:(lia) Hrfb); symmetry; apply Z.mod_small; lia |];
    assert (KEEPC : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
      rdW W (ms_mem msF) (c + i) = rdW W mem (c + i));
    [ let i := fresh "i" in let Hi := fresh "Hi" in let Hni := fresh "Hni" in let Hn := fresh "Hn" in
      intros i Hi Hni; change seg_spec.SEG_C_SIZE with 16616 in Hi; change seg_spec.RC_REFUSED with 13516 in Hni;
      pose proof (NOTW (c + i) ltac:(left; lia)) as Hn;
      rewrite UNe, UNd, UNc, UNb by (first [lia | cbv beta; tauto]);
      replace (c + i) with (bc + (c + i - bc)) by lia;
      rewrite (KK2 bc mc (c + i - bc) Hbin ltac:(lia) (fun Hf => Hf));
      replace (bc + (c + i - bc)) with (c + i) by lia;
      apply UNa; [lia | cbv beta; lia] |];
    assert (SSP : sa_ssp (rdW W (ms_mem msF)) gotw guard);
    [ apply (rb_ssp_keep (rdW W mem2) _ gotw guard Hssp2);
      [ let i := fresh "i" in let Hi := fresh "Hi" in let Hn := fresh "Hn" in intros i Hi;
        pose proof (NOTW (gotw + i) ltac:(right; lia)) as Hn;
        rewrite UNe, UNd, UNc, UNb by (first [lia | cbv beta; tauto]); reflexivity
      | let i := fresh "i" in let Hi := fresh "Hi" in let Hn := fresh "Hn" in intros i Hi;
        pose proof (NOTW (guard + i) ltac:(right; lia)) as Hn;
        rewrite UNe, UNd, UNc, UNb by (first [lia | cbv beta; tauto]); reflexivity ] |];
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (rb_canon_ok Hh Ex ssx msx 1100 RB_PRE_CLOB (ss_mem ssx) RB_PRE (f_atoms (ss_facts ss_pre)) [] (f_alias (ss_facts ss_pre)) HS
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(rb_in_tac) (fun x (Hx : In x []) => match Hx with end) ltac:(rb_in_tac)) as HS3 end;
    lazymatch type of HS3 with st_ok_pi _ _ _ ?x _ => replace x with ss_pre in HS3 by (vm_compute; reflexivity) end;
    lazymatch type of HS3 with st_ok_pi _ _ ?Ev3x _ _ => set (Evq := Ev3x) in HS3 end;
    assert (HEIq : img_env VAL A_LIM Evq) by (subst Evq; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]);
    assert (AGq : forall n, (n < 1100)%nat -> ew Evq n = ew Ev2 n) by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; subst Evq; apply ew_havoc_old; exact Hn);
    refine (PRE ly S W regs mem md ch c line fp ln rcs f args msF _ S2 fpos Evq HCX HSTK Hn8 HEIq HS3 HJ2 Hfrs2 Eab (ex_intro _ fS2 ES2)
      _ _ _ _ _ _ _ _ _ _ _ KEEPC RF1 SSP);
    [ let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in
      intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite AGq, AG2 by lia; apply AGR; exact Hn
    | rewrite AGq, AG2 by lia; exact E32
    | rewrite AGq, AG2 by lia; exact E33
    | rewrite AGq, AG2 by lia; exact E34
    | rewrite AGq, AG2 by lia; exact E35
    | rewrite AGq, AG2 by lia; exact E36
    | rewrite AGq, AG2 by lia; exact E37
    | rewrite AGq by lia; exact E2_1028
    | rewrite AGq by lia; exact E2_1040
    | rewrite AGq by lia; exact E2_1041
    | subst Evq; change 1101%nat with (1100 + 1)%nat; rewrite (ew_havoc_new _ 1100 _ 1 (Z_to_bv 64 0)) by (cbn; lia);
      cbn [nth map RB_PRE_CLOB]; rewrite R13; (rewrite Hrd00, Z.eqb_refl; rewrite (img_env_atomP Ev2 275%nat HEI2) by (unfold A_TEXT, A_LIM; lia); change 275%nat with (A_OBJ 34); rewrite LIT34; reflexivity) ].
- (* n_refusals >= 8: refused + 1, the `blt 7,n` exit to the release, then RB_REL_stmt *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  pose proof (st_ok_pi_add_fact Ex _ _ 35 (mkAF 8 23 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U35; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
  clear HS; rename HS3 into HS end.
  rnorm HS.
  assert (E2_36 : ew Ev2 36 = Z_to_bv 64 (rc_refused rcs)) by (rewrite AG2 by lia; exact E36).
  (* R3: the token run over c's block: checks 1, 2, refused + 1, n > 7: to the release (0x89544) *)
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan RB_REL.
  { rb_awr_tok U2 U33 U10 HCW HbinS2 sp0 c. }
  rb_unch_tok UNc U2 U33 U10 Hs1b sp0 c.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msF end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let i := eval vm_compute in (rb_find (ss_mem ssx) 10%nat 13512 0) in
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) i r HS ltac:(vm_compute; reflexivity)) as HRcnt;
  cbn [ms_mem restrict] in HRcnt end.
  pose proof (rb_region_aval4 SEGS Ev2 (w_H W) _ 10 c _ _ _ _ _ 13516 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1)) _
    HRcnt U10 ltac:(left; reflexivity) (eq_sym (Z_to_bv_bv_unsigned _ _))) as Vrf.
  assert (RF1 : rd32 (rdW W (ms_mem msF)) (c + seg_spec.RC_REFUSED) (rc_refused rcs + 1)).
  { change seg_spec.RC_REFUSED with 13516. apply (rb_rd32_mod _ _ _ _ Vrf).
    change (bv_unsigned (sv_denot Ev2 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1))))
      with (U Ev2 (SAlu ALU_ADD (SExt true 32 (SOff 36 0)) (SLit 1))).
    rewrite (rb_inc_mod Ev2 (rc_refused rcs) E2_36 ltac:(lia) Hrfb). symmetry. apply Z.mod_small. lia. }
  assert (KEEPC : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> ~ (seg_spec.RC_REFUSED <= i < seg_spec.RC_REFUSED + 4) ->
    rdW W (ms_mem msF) (c + i) = rdW W mem (c + i)).
  { intros i Hi Hni. change seg_spec.SEG_C_SIZE with 16616 in Hi. change seg_spec.RC_REFUSED with 13516 in Hni.
    pose proof (NOTW (c + i) ltac:(left; lia)) as Hn.
    rewrite UNc, UNb by (first [lia | cbv beta; tauto]).
    replace (c + i) with (bc + (c + i - bc)) by lia.
    rewrite (KK2 bc mc (c + i - bc) Hbin ltac:(lia) (fun Hf => Hf)).
    replace (bc + (c + i - bc)) with (c + i) by lia.
    apply UNa; [lia | cbv beta; lia]. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  pose proof (rb_canon_ok Hh Ex ssx msx 1200 RB_REL_CLOB rel_regions RB_REL rel_atoms [] [] HS
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(rb_in_tac) (fun x (Hx : In x []) => match Hx with end)
    (fun x (Hx : In x []) => match Hx with end)) as HS3 end.
  lazymatch type of HS3 with st_ok_pi _ _ _ ?x _ => replace x with ss_rel0 in HS3 by (vm_compute; reflexivity) end.
  lazymatch type of HS3 with st_ok_pi _ _ ?Evx _ _ => set (Evr := Evx) in HS3 end.
  assert (HEIr : img_env VAL A_LIM Evr) by (subst Evr; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
  assert (AGr : forall n, (n < 1200)%nat -> ew Evr n = ew Ev2 n) by (intros n Hn; subst Evr; apply ew_havoc_old; exact Hn).
  refine (REL STK ly S W regs mem md ch c rcs (SegModel.refuse rcs ln f args) msF _ S2 fpos Evr HPRE ltac:(lia) HHEAP HEIr HS3
    HJ2 Hfrs2 Eab (ex_intro _ fS2 ES2) _ _ _ _ _ _ _).
  + intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite AGr, AG2 by lia. apply AGR. exact Hn.
  + rewrite AGr, AG2 by lia. exact E32.
  + rewrite AGr, AG2 by lia. exact E33.
  + rewrite AGr by lia. exact E2_1028.
  + rewrite AGr by lia. exact E2_1040.
  + rewrite AGr by lia. exact E2_1041.
  + rewrite (rf_refuse_ge8 rcs ln f args Hn8). exact (rf_upd_refd (rdW W mem) _ c rcs HRC Hrfb KEEPC RF1).
Qed.
End e.
End f.
End d.
