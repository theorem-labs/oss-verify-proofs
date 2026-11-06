(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run plumbing of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (cfg_keep, cfg_kwr_ro and the same_io chain of cfg_leaf, as l_keep, l_kwr and l_post) and of proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at b0f706c04a1 (awr_stk, as l_awr: the writable window is the frame [F, F + 0x60) at atom 2), for a segment of reac_role_prop_parse's walk that starts and ends at the cuts of lib/A/RPgParseBase.v; the entry states, exits, string lemmas and the walk below are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v; 492 of its 562 lines of code are new or changed and 844 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v, with its module paths, module names and addresses changed; 33 of its 565 lines of code are new or changed and 30 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v at afaa3cb55c1d for reac-pw/fuzz_rate's
   reac_rate_prop_parse: module paths and the rl_ / Role names changed to rate's; the pcs are image A's of
   fuzz_rate.asan; the find loop's back edge is 0x845cc beqz -> L1 (taken: the next pass) with 0x845d0 j 0x84554
   (not taken: impossible, r' = 0 mod 4). *)
(* reac_rate_prop_parse 0x8449c of reac-pw/fuzz_rate's ASan image A, segment F: one pass of the find loop
   (spa_pod_object_find_prop) from the cut L1 0x84570. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Model Accessors Spa Nearest Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require reac_rate_prop_parse.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0 RtPgBase RtPgCSpec RtPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------- the entry states ---------------------------------- *)
(* (A) the property header [P + r, P + r + 16) lies in the pod: a read-only region at atom 12 (a2) with the key,
   the value size and the value type as atoms 43, 44, 45, and its shadow entry; (B) it does not: no pod region. *)
Definition pod_region : YP09.region :=
YP09.mkRegion (Some 12%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 4 (SOff 43 0)); YP09.mkChunk 8 (CVal 4 (SOff 44 0)); YP09.mkChunk 12 (CVal 4 (SOff 45 0))].
Definition fA_facts : facts :=
mkFacts [(2%nat, mkAF 140735332483072 (2 ^ 47) 4); (12%nat, mkAF 0 (2 ^ 47 - 17) 2); (19%nat, mkAF SBr SBr 0)] [] [].
Definition fB_facts : facts := mkFacts [(2%nat, mkAF 140735332483072 (2 ^ 47) 4); (19%nat, mkAF SBr SBr 0)] [] [].
Definition ssA : sstate := mkSS PC_L1 sr_atoms [frame_region []; pod_region] None fA_facts.
Definition ssB : sstate := mkSS PC_L1 sr_atoms [frame_region []] None fB_facts.
Definition shA : list shent := [mkSHE 12 0 16].
Definition f_L (x : pctx) (r : Z) : list word :=
[w64 (Spa.u32_at (x_bs x) r); w64 (Spa.u32_at (x_bs x) (r + 8)); w64 (Spa.u32_at (x_bs x) (r + 12))].

(* a run keeps every byte outside a zone that holds its write windows *)
Lemma f_kept : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz.
assert (Hm : mrestrict H m2 (Z_to_bv 64 a) = mrestrict H m1 (Z_to_bv 64 a)).
{ apply HF. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)). }
rewrite <- (HK a Ha Hz). unfold aview, mbyte. rewrite Hm. reflexivity.
Qed.

(* ---------------------------------- the walk's plumbing ---------------------------------- *)
(* the write-range obligation of a run: the frame window [F, F + 0x60) lies in the caller's stack allowance; the pod
   region is read-only. B20 : bv_unsigned (ew E0 2) = F and HAE : env_agree k E0 E for the run's env E. *)
Ltac f_B2 HAE B20 E B2 :=
lazymatch type of B20 with bv_unsigned (ew _ 2) = ?F =>
assert (B2 : bv_unsigned (ew E 2) = F) by (first [exact B20 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact B20]) end.
Ltac f_awr HAE B20 :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let B2 := fresh "B2" in f_B2 HAE B20 E B2;
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch type of B2 with _ = ?F =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (F - sp0)); [reflexivity | rewrite B2; lia | cbn; lia | cbn; lia |] ]
end end.
(* after a run: the kept bytes (every write window lies in the frame, inside the callee's stack), then the env *)
Ltac f_keep HAE B20 :=
lazymatch goal with HFr : frame_of ?E _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let B2 := fresh "B2" in f_B2 HAE B20 E B2;
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (f_kept _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by (
  let a := fresh "a" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hb := fresh "Hb" in
  intros a (rg & Hrg & Hb); cbv beta;
  lazymatch type of Hrg with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hrg end;
  repeat (destruct Hrg as [<- | Hrg]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
    first [rewrite B2 in Hb; lia | lia] | ]); destruct Hrg) end;
specialize (KS KW); clear KW KE HFr B2; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac f_upd HAE :=
lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
let H := fresh in assert (H : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H into HAE end end.
Ltac f_run HAE B20 :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok parse_tbl_ok HS HJ SHOK RTBspan; [f_awr HAE B20 | f_keep HAE B20; f_upd HAE] end.
Ltac f_run_to HAE B20 stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok parse_tbl_ok HS HJ SHOK RTBspan stop; [f_awr HAE B20 | f_keep HAE B20; f_upd HAE] end.
Ltac f_br Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok parse_tbl_ok HS SH RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* a branch condition as a test over the U values of the segment's entry env E0 *)
Ltac f_hc HAE H :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
tryif constr_eq E0 E then idtac else (repeat (rewrite (U_agree k E0 E _ HAE) in H by (vm_compute; reflexivity))) end.

(* the engine's subtraction b - a *)
Lemma U_sub_l : forall E a b, U E (SAlu ALU_ADD (SMd M_MUL a (SLit (-1))) b) = (U E b - U E a) mod 2 ^ 64.
Proof.
intros E a b. rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_l by lia.
replace (U E a * 18446744073709551615 + U E b) with ((U E b - U E a) + U E a * 2 ^ 64) by lia.
apply Z_mod_plus_full.
Qed.
(* lw of a u32 s compared with a constant c below 2^31: the test s = c *)
Lemma U_sx32_eqb : forall E a s c, U E a = s -> 0 <= s < 2 ^ 32 -> 0 <= c < 2 ^ 31 ->
(U E (SExt true 32 a) =? c) = (s =? c).
Proof.
intros E a s c Ha Hs Hc. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec s (2 ^ 31)) as [Hlt|Hge].
- rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia. rewrite Z.mod_small by lia. reflexivity.
- assert (M1 : (s + 2 ^ 31) mod 2 ^ 32 = s - 2 ^ 31) by (symmetry; apply Z.mod_unique with 1; [left; lia | lia]).
  rewrite M1. assert (M2 : (s - 2 ^ 31 - 2 ^ 31) mod 2 ^ 64 = s - 2 ^ 32 + 2 ^ 64)
  by (symmetry; apply Z.mod_unique with (-1); [left; lia | lia]).
  rewrite M2. destruct (Z.eqb_spec (s - 2 ^ 32 + 2 ^ 64) c); destruct (Z.eqb_spec s c); first [reflexivity | lia].
Qed.
(* the engine's arithmetic, where no result wraps *)
Lemma U_add : forall E a b, 0 <= U E a + U E b < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = U E a + U E b.
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma U_or : forall E a b, 0 <= Z.lor (U E a) (U E b) < 2 ^ 64 -> U E (SAlu ALU_OR a b) = Z.lor (U E a) (U E b).
Proof. intros E a b H. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma U_srl : forall E a b, 0 <= U E b < 64 -> U E (SAlu ALU_SRL a b) = U E a / 2 ^ (U E b).
Proof.
intros E a b H. rewrite U_SAlu. cbn [zalu_raw].
replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia.
change (2 ^ 6) with 64. rewrite (Z.mod_small (U E b)) by lia.
rewrite Z.shiftr_div_pow2 by lia. pose proof (U_range E a) as Ha.
assert (0 < 2 ^ U E b) by (apply Z.pow_pos_nonneg; lia).
assert (U E a / 2 ^ U E b <= U E a) by (apply Z.div_le_upper_bound; [lia|]; nia).
assert (0 <= U E a / 2 ^ U E b) by (apply Z.div_pos; lia).
unfold zcanon, M64. apply Z.mod_small. unfold M64 in Ha. lia.
Qed.
Lemma U_sext32 : forall E a s, U E a = s -> 0 <= s < 2 ^ 31 -> U E (SExt true 32 a) = s.
Proof.
intros E a s Ha Hs. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small s) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small (s + 2 ^ 31)) by lia. replace (s + 2 ^ 31 - 2 ^ 31) with s by lia.
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma U_sll : forall E a b, 0 <= U E b < 64 -> U E (SAlu ALU_SLL a b) = (U E a * 2 ^ (U E b)) mod 2 ^ 64.
Proof.
intros E a b H. rewrite U_SAlu. cbn [zalu_raw].
replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia.
change (2 ^ 6) with 64. rewrite (Z.mod_small (U E b)) by lia.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma U_add_wrap : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.

Section fs. Context {fx : YK11.FPState}.
(* the first region of a walk state: the frame *)
Lemma f_frame_ok : forall E ss ms (H : word -> bool) rest,
st_ok rsegs E ss (restrict H ms) -> ss_mem ss = frame_region [] :: rest ->
region_ok rsegs E (mrestrict H (ms_mem ms)) (frame_region []).
Proof.
intros E ss ms H rest HS Hm. pose proof (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & HF & _).
rewrite Hm in HF. cbn [ms_mem restrict] in HF. inversion HF; assumption.
Qed.

(* a register the walk did not touch: still the atom it entered with *)
Lemma f_reg_of : forall x regs2 L E ss ms (H : word -> bool) (q : bv 5) (n : nat),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff n 0 ->
env_agree 46 (cut_env x regs2 L) E -> (n < 46)%nat -> Z.of_nat n = bv_unsigned q ->
getr (ms_regs ms) q = getr regs2 q.
Proof.
intros x regs2 L E ss ms H q n HS Hsr HAE Hn Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms q HS), Hsr, sv_denot_SOff0, (proj1 HAE n Hn).
exact (cut_env_reg x regs2 L n q Hq).
Qed.
End fs.

(* a register goal getr (ms_regs ms) q = w64 v, reduced to U E0 e = v *)
Ltac f_rg HAE :=
lazymatch goal with |- getr (ms_regs ?ms) ?q = _ =>
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ms) |- _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) q) in
  rewrite (st_ok_restrict_reg segs H E ss ms q HS);
  change (sr_get (ss_regs ss) q) with e;
  unfold w64; rewrite denot_lit_U; f_equal;
  lazymatch type of HAE with env_agree ?k ?E0 _ =>
    tryif constr_eq E0 E then idtac else rewrite (U_agree k E0 E e HAE ltac:(vm_compute; reflexivity)) end
end end.


Lemma f_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. unfold same_io. repeat split; reflexivity. Qed.
Ltac f_kio := let rec go := first [ apply same_io_refl | (eapply same_io_trans; [| apply f_same_io_wvb]); go ] in go.
(* a goal getr (ms_regs ms) q = _ whose register the walk kept: rewrite it to getr regs2 q *)
Ltac f_rkeep x regs2 L HAE n q :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) |- _ =>
  rewrite (f_reg_of x regs2 L E ss ms (w_H W) q n HS ltac:(vm_compute; reflexivity) HAE ltac:(lia)
                   ltac:(vm_compute; reflexivity))
end.
(* the cut's shared facts at the walk's final state (rest: the regions after the frame) *)
Ltac f_fi B x regs2 L HAE B20 Hio Hcs H2 H8 H19 rest :=
lazymatch goal with
| HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
  let B2 := fresh "B2" in f_B2 HAE B20 E B2;
  split; [exact HJ|];
  split; [eapply same_io_trans; [exact Hio|]; f_kio|];
  split; [intros a Ha Hn; exact (KE a Ha Hn)|];
  split; [ apply (saved_of_frame_region x E (mrestrict (w_H W) (ms_mem ms)) []);
           [ apply (f_frame_ok E ss ms (w_H W) rest HS); vm_compute; reflexivity
           | cbn [base_val]; exact B2
           | intros j Hj; first [ (rewrite (proj1 HAE (33 + j)%nat ltac:(lia)); apply cut_env_saved; exact Hj)
                                | (apply cut_env_saved; exact Hj) ] ] |];
  split; [ f_rkeep x regs2 L HAE 2%nat (2%bv : bv 5); exact H2 |];
  split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in
           intros rr Hrr; destruct Hrr as [Hrr|[Hrr|[Hrr|[Hrr|Hrr]]]]; subst rr;
           [ f_rkeep x regs2 L HAE 3%nat (Z_to_bv 5 3) | f_rkeep x regs2 L HAE 4%nat (Z_to_bv 5 4)
           | f_rkeep x regs2 L HAE 25%nat (Z_to_bv 5 25) | f_rkeep x regs2 L HAE 26%nat (Z_to_bv 5 26)
           | f_rkeep x regs2 L HAE 27%nat (Z_to_bv 5 27) ]; apply Hcs; tauto |];
  split; [ f_rkeep x regs2 L HAE 8%nat (8%bv : bv 5); exact H8
         | f_rkeep x regs2 L HAE 19%nat (19%bv : bv 5); exact H19 ]
end.

(* ---------------------------------- the model's tests ---------------------------------- *)
(* spa_pod_prop_is_inside at a 4-aligned r *)
Lemma f_inside : forall bs size r, r mod 4 = 0 -> 8 <= r -> 16 <= size -> r - 8 <= size - 16 ->
Spa.u32_at bs (r + 8) <= 8 + size - (r + 16) -> Spa.prop_is_inside bs 8 size r = true.
Proof.
intros bs size r H4 H8 H1 H2 H3. rewrite reac_rate_prop_parse.pa_pin by assumption.
apply andb_true_iff; split; [apply andb_true_iff; split|]; apply Z.leb_le; lia.
Qed.
Lemma f_outside : forall bs size r, r mod 4 = 0 -> 8 <= r ->
(size - 16 < r - 8 \/ 8 + size - (r + 16) < Spa.u32_at bs (r + 8)) -> Spa.prop_is_inside bs 8 size r = false.
Proof.
intros bs size r H4 H8 H. rewrite reac_rate_prop_parse.pa_pin by assumption.
apply andb_false_iff. destruct H as [H|H]; [left; apply andb_false_iff; right | right]; apply Z.leb_gt; lia.
Qed.
Lemma f_mod4 : forall a b, a mod 4 = 0 -> b mod 4 = 0 -> (a + b) mod 4 = 0.
Proof. intros a b Ha Hb. rewrite Z.add_mod by lia. rewrite Ha, Hb. reflexivity. Qed.
Lemma f_mod4_of8 : forall a, a mod 8 = 0 -> a mod 4 = 0.
Proof. intros a H. apply Z.mod_divide; [lia|]. apply (Z.divide_trans 4 8); [exists 2; reflexivity|].
apply Z.mod_divide; [lia | exact H]. Qed.
Lemma f_mod4_of16 : forall a, a mod 16 = 0 -> a mod 4 = 0.
Proof. intros a H. apply Z.mod_divide; [lia|]. apply (Z.divide_trans 4 16); [exists 4; reflexivity|].
apply Z.mod_divide; [lia | exact H]. Qed.

(* the ret 0 leaf: from the `ret` the engine stopped at, PPOST through ppost_intro; Hres0 : x_res x = (None, 0) *)
Ltac f_leaf B x regs2 L MTL Hpre HAE H2 Hcs Hio Hret Hfrm Hres0 :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let Hpr := fresh "Hpr" in let Hra := fresh "Hra" in
destruct (leaf_regs B x regs2 L E ss ms (w_H W) Hpre HS ltac:(intros n Hn; apply (proj1 HAE); lia)
  ltac:(vm_compute; reflexivity) H2 Hcs) as [Hpr Hra];
let R10 := fresh "R10" in
pose proof (st_ok_restrict_reg rsegs (w_H W) E ss ms 10%bv HS) as R10;
eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx W E); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat';
rewrite Hra, Hret;
apply (ppost_intro B _ MTL x false);
[ eapply ajournal_materialize; eassumption
| eapply same_io_trans; [exact Hio |];
  let rec kio := first [ apply same_io_refl | eapply same_io_trans; [| apply f_same_io_wvb]; kio ] in kio
| exact Hpr
| apply rt_fxk_refl; exact Hfrm
| intros a Ha Hn _; exact (KE a Ha Hn)
| change (Rate.harness_parse false (x_bs x)) with (x_res x); rewrite Hres0; rewrite R10; reflexivity
| change (Rate.harness_parse false (x_bs x)) with (x_res x); rewrite Hres0; exact I ]
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma entryA : forall x r regs2 mem2 md2, pre_ok B x -> L1_at B x r regs2 mem2 md2 -> r + 16 <= x_len x ->
st_ok rsegs (cut_env x regs2 (f_L x r)) ssA (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_L1) mem2 (seg_rom rsegs))) /\
sh_ok rsegs PBx shA (cut_env x regs2 (f_L x r)) (mrestrict (w_H (x_W x)) mem2).
Proof.
intros x r regs2 mem2 md2 Hpre HL Hin.
pose proof HL as (HFI & H10 & H12 & H14 & H15 & H16 & Hobj & HS16 & Hr & Hr4 & Hres).
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & HSZ & HP63 & _ & _ & _ & HAM & HDJ).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hsp16 & Hwin).
pose proof (pod_at_cut B x regs2 mem2 md2 Hpre HFI) as (HG & HRA & HHV).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
pose proof (amem_range_bounds (x_P x) (x_len x) ltac:(lia) ltac:(lia) HAM) as Hhm.
pose proof HFI as (_ & _ & _ & _ & H2 & _ & _ & H19).
assert (E2 : bv_unsigned (ew (cut_env x regs2 (f_L x r)) 2) = x_F x).
{ rewrite (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2. unfold w64.
  apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia. }
assert (E12 : ew (cut_env x regs2 (f_L x r)) 12 = Z_to_bv 64 (x_P x + r)).
{ rewrite (cut_env_reg x regs2 _ 12 12%bv eq_refl), H12. reflexivity. }
assert (E19 : ew (cut_env x regs2 (f_L x r)) 19 = Z_to_bv 64 SHADOW_OFF).
{ rewrite (cut_env_reg x regs2 _ 19 19%bv eq_refl), H19. reflexivity. }
assert (E43 : ew (cut_env x regs2 (f_L x r)) 43 = Z_to_bv 64 (Spa.u32_at (x_bs x) r)).
{ exact (cut_env_seg x regs2 (f_L x r) 0). }
assert (E44 : ew (cut_env x regs2 (f_L x r)) 44 = Z_to_bv 64 (Spa.u32_at (x_bs x) (r + 8))).
{ exact (cut_env_seg x regs2 (f_L x r) 1). }
assert (E45 : ew (cut_env x regs2 (f_L x r)) 45 = Z_to_bv 64 (Spa.u32_at (x_bs x) (r + 12))).
{ exact (cut_env_seg x regs2 (f_L x r) 2). }
pose proof (u32_at_range (x_bs x) r) as R0.
pose proof (u32_at_range (x_bs x) (r + 8)) as R8.
pose proof (u32_at_range (x_bs x) (r + 12)) as R12.
assert (B12 : bv_unsigned (ew (cut_env x regs2 (f_L x r)) 12) = x_P x + r) by (rewrite E12; apply unsigned_lit_small; lia).
assert (B19 : bv_unsigned (ew (cut_env x regs2 (f_L x r)) 19) = SHADOW_OFF) by (rewrite E19; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. split.
- unfold ssA. unfold cut_env at 1. apply (entry_st_ok_full rsegs); fold (cut_env x regs2 (f_L x r)).
  + apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + constructor; [exact (frame_region_ok B x regs2 mem2 md2 (f_L x r) [] HFI Hpre (Forall_nil _))|].
    constructor; [|constructor].
    unfold region_ok, pod_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite B12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 43 0) (Spa.u32_at (x_bs x) r));
      [rewrite sv_denot_SOff0; exact E43 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply (pod_u32 x _ r HG); lia.
    * apply (chunk_ok_val rsegs _ _ _ 8 4 (SOff 44 0) (Spa.u32_at (x_bs x) (r + 8)));
      [rewrite sv_denot_SOff0; exact E44 | cbn; lia | cbn; lia |].
      replace (x_P x + r + 8) with (x_P x + (r + 8)) by lia. apply (pod_u32 x _ (r + 8) HG); lia.
    * apply (chunk_ok_val rsegs _ _ _ 12 4 (SOff 45 0) (Spa.u32_at (x_bs x) (r + 12)));
      [rewrite sv_denot_SOff0; exact E45 | cbn; lia | cbn; lia |].
      replace (x_P x + r + 12) with (x_P x + (r + 12)) by lia. apply (pod_u32 x _ (r + 12) HG); lia.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, frame_region, pod_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, B12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. repeat split; lia.
  + assert (HPr4 : (x_P x + r) mod 4 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| apply Z.mod_divide; [lia | exact Hr4]].
      apply (Z.divide_trans 4 16); [exists 4; reflexivity | apply Z.mod_divide; [lia | exact HP16]]. }
    split; [|split; [exact I | exact I]]. cbn [fA_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, B12, B19. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK, SBr, SHADOW_OFF, kHighMemEnd in *.
    repeat split; first [exact HPr4 | lia].
- unfold sh_ok, shA. constructor; [|constructor].
  apply (shent_pod B x regs2 mem2 md2 _ PBx 12 r 0 16 Hpre HFI); [| | lia | lia | lia].
  + unfold PBx. apply (U_atom _ 19 SHADOW_OFF E19). unfold SHADOW_OFF. lia.
  + apply (U_atom _ 12 (x_P x + r) E12). lia.
Qed.

(* (B) the property header does not lie in the pod: the frame alone, no shadow entry *)
Lemma entryB : forall x r regs2 mem2 md2, pre_ok B x -> L1_at B x r regs2 mem2 md2 ->
st_ok rsegs (cut_env x regs2 (f_L x r)) ssB (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_L1) mem2 (seg_rom rsegs))) /\
sh_ok rsegs PBx [] (cut_env x regs2 (f_L x r)) (mrestrict (w_H (x_W x)) mem2).
Proof.
intros x r regs2 mem2 md2 Hpre HL.
pose proof HL as (HFI & H10 & H12 & H14 & H15 & H16 & Hobj & HS16 & Hr & Hr4 & Hres).
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & HSZ & HP63 & _ & _ & _ & HAM & HDJ).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hsp16 & Hwin).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
pose proof HFI as (_ & _ & _ & _ & H2 & _ & _ & H19).
assert (E2 : bv_unsigned (ew (cut_env x regs2 (f_L x r)) 2) = x_F x).
{ rewrite (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2. unfold w64.
  apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia. }
assert (E19 : ew (cut_env x regs2 (f_L x r)) 19 = Z_to_bv 64 SHADOW_OFF).
{ rewrite (cut_env_reg x regs2 _ 19 19%bv eq_refl), H19. reflexivity. }
assert (B19 : bv_unsigned (ew (cut_env x regs2 (f_L x r)) 19) = SHADOW_OFF)
  by (rewrite E19; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. split; [|constructor].
unfold ssB. unfold cut_env at 1. apply (entry_st_ok_full rsegs); fold (cut_env x regs2 (f_L x r)).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [exact (frame_region_ok B x regs2 mem2 md2 (f_L x r) [] HFI Hpre (Forall_nil _)) | constructor].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, frame_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. cbn [fB_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, B19. change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK, SBr, SHADOW_OFF in *.
  repeat split; lia.
Qed.

Lemma segF_ok : segF_stmt B MT.
Proof using MTL LAWS.
unfold segF_stmt, L1_ok. intros x r Hpre HL1 HL2 regs2 mem2 md2 HL.
unfold cfg_at in HL1. unfold L2_ok, cfg_at in HL2.
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
  pose proof HL as (HFI & H10 & H12 & H14 & H15 & H16 & Hobj & HS16 & Hr & Hr4 & Hres).
  pose proof HFI as (HJ & Hio & KE & HSV & H2 & Hcs & H8 & H19).
  pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & HSZ & HP63 & _ & _ & _ & HAM & HDJ).
  pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hsp16 & Hwin).
  pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
  assert (HF96 : x_F x = x_sp x - 96) by reflexivity.
  assert (Hz1 : x_sp x - T_parse_STK <= x_F x) by (unfold T_parse_STK, ESTACK; lia).
  assert (Hw1 : x_sp0 x - x_STK x <= x_F x) by (unfold T_parse_STK, ESTACK in Hwin; lia).
  assert (B20 : bv_unsigned (ew (cut_env x regs2 (f_L x r)) 2) = x_F x).
  { rewrite (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2. unfold w64.
    apply unsigned_lit_small. unfold T_parse_STK, ESTACK in *. lia. }
  assert (HAE : env_agree 46 (cut_env x regs2 (f_L x r)) (cut_env x regs2 (f_L x r))) by apply env_agree_refl.
  pose proof (u32_at_range (x_bs x) r) as R0.
  pose proof (u32_at_range (x_bs x) (r + 8)) as R8.
  pose proof (u32_at_range (x_bs x) (r + 12)) as R12.
  assert (U10 : U (cut_env x regs2 (f_L x r)) (SOff 10 0) = x_P x + 8)
    by (apply U_atom; [rewrite (cut_env_reg x regs2 _ 10 10%bv eq_refl), H10; reflexivity | lia]).
  assert (U12 : U (cut_env x regs2 (f_L x r)) (SOff 12 0) = x_P x + r)
    by (apply U_atom; [rewrite (cut_env_reg x regs2 _ 12 12%bv eq_refl), H12; reflexivity | lia]).
  assert (U14 : U (cut_env x regs2 (f_L x r)) (SOff 14 0) = x_SZ x - 16)
    by (apply U_atom; [rewrite (cut_env_reg x regs2 _ 14 14%bv eq_refl), H14; reflexivity | lia]).
  assert (U15 : U (cut_env x regs2 (f_L x r)) (SOff 15 0) = x_P x + x_SZ x - 8)
    by (apply U_atom; [rewrite (cut_env_reg x regs2 _ 15 15%bv eq_refl), H15; reflexivity | lia]).
  assert (U16 : U (cut_env x regs2 (f_L x r)) (SOff 16 0) = 524289)
    by (apply U_atom; [rewrite (cut_env_reg x regs2 _ 16 16%bv eq_refl), H16; reflexivity | lia]).
  assert (U43 : U (cut_env x regs2 (f_L x r)) (SOff 43 0) = Spa.u32_at (x_bs x) r)
    by (apply U_atom; [exact (cut_env_seg x regs2 (f_L x r) 0) | lia]).
  assert (U44 : U (cut_env x regs2 (f_L x r)) (SOff 44 0) = Spa.u32_at (x_bs x) (r + 8))
    by (apply U_atom; [exact (cut_env_seg x regs2 (f_L x r) 1) | lia]).
  assert (U45 : U (cut_env x regs2 (f_L x r)) (SOff 45 0) = Spa.u32_at (x_bs x) (r + 12))
    by (apply U_atom; [exact (cut_env_seg x regs2 (f_L x r) 2) | lia]).
  assert (E12' : ew (cut_env x regs2 (f_L x r)) 12 = Z_to_bv 64 (x_P x + r))
    by (rewrite (cut_env_reg x regs2 _ 12 12%bv eq_refl), H12; reflexivity).
  assert (U12_8 : U (cut_env x regs2 (f_L x r)) (SOff 12 8) = x_P x + r + 8)
    by (rewrite (U_atom_off _ 12 (x_P x + r) 8 E12' ltac:(lia) ltac:(lia)); lia).
  assert (U12_16 : U (cut_env x regs2 (f_L x r)) (SOff 12 16) = x_P x + r + 16)
    by (rewrite (U_atom_off _ 12 (x_P x + r) 16 E12' ltac:(lia) ltac:(lia)); lia).
  assert (Uz44 : U (cut_env x regs2 (f_L x r)) (SExt false 32 (SOff 44 0)) = Spa.u32_at (x_bs x) (r + 8)).
  { rewrite U_zext, U44. change (2 ^ Z.of_N 32) with (2 ^ 32). apply Z.mod_small. lia. }
  assert (Usrl : U (cut_env x regs2 (f_L x r)) (SAlu ALU_SRL (SExt false 32 (SOff 44 0)) (SLit 20)) =
                 Spa.u32_at (x_bs x) (r + 8) / 2 ^ 20).
  { rewrite U_srl by (rewrite (U_lit _ 20 ltac:(lia)); lia). rewrite Uz44, (U_lit _ 20 ltac:(lia)). reflexivity. }
  assert (HPr4 : (x_P x + r) mod 4 = 0) by (apply f_mod4; [apply f_mod4_of16; exact HP16 | exact Hr4]).
  pose proof (reac_rate_prop_parse.pa_ru_facts (Spa.u32_at (x_bs x) (r + 8)) ltac:(lia)) as (RUa & RUb).
  assert (Uor : U (cut_env x regs2 (f_L x r))
                  (SAlu ALU_OR (SAlu ALU_ADD (SExt false 32 (SOff 44 0)) (SLit 15)) (SLit 7)) =
                Spa.round_up8 (16 + Spa.u32_at (x_bs x) (r + 8)) - 1).
  { assert (Uad : U (cut_env x regs2 (f_L x r)) (SAlu ALU_ADD (SExt false 32 (SOff 44 0)) (SLit 15)) =
                  Spa.u32_at (x_bs x) (r + 8) + 15).
    { rewrite U_add by (rewrite Uz44, (U_lit _ 15 ltac:(lia)); lia).
      rewrite Uz44, (U_lit _ 15 ltac:(lia)). reflexivity. }
    rewrite U_or by (rewrite Uad, (U_lit _ 7 ltac:(lia)), reac_rate_prop_parse.pa_ru; lia).
    rewrite Uad, (U_lit _ 7 ltac:(lia)). apply reac_rate_prop_parse.pa_ru. }
  assert (Uin : U (cut_env x regs2 (f_L x r))
                  (SAlu ALU_ADD (SOff 12 0)
                     (SAlu ALU_OR (SAlu ALU_ADD (SExt false 32 (SOff 44 0)) (SLit 15)) (SLit 7))) =
                x_P x + r + (Spa.round_up8 (16 + Spa.u32_at (x_bs x) (r + 8)) - 1)).
  { rewrite U_add by (rewrite U12, Uor; lia). rewrite U12, Uor. reflexivity. }
  assert (Uc0 : U (cut_env x regs2 (f_L x r)) (SLit 0) = 0) by (apply U_lit; lia).
  assert (Uc1 : U (cut_env x regs2 (f_L x r)) (SLit 1) = 1) by (apply U_lit; lia).
  assert (Uc8 : U (cut_env x regs2 (f_L x r)) (SLit 8) = 8) by (apply U_lit; lia).
  assert (Uc14 : U (cut_env x regs2 (f_L x r)) (SLit 14) = 14) by (apply U_lit; lia).
  assert (Ur' : U (cut_env x regs2 (f_L x r))
                  (SAlu ALU_ADD (SAlu ALU_ADD (SOff 12 0)
                     (SAlu ALU_OR (SAlu ALU_ADD (SExt false 32 (SOff 44 0)) (SLit 15)) (SLit 7))) (SLit 1)) =
                x_P x + (r + Spa.round_up8 (16 + Spa.u32_at (x_bs x) (r + 8)))).
  { rewrite U_add; rewrite Uin, Uc1; lia. }
  pose proof Hpre as ((_ & Hret & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm). unfold YK0s.ret_ok in Hret.
  unfold cfg_at. change (w64 PC_L1) with (Z_to_bv 64 PC_L1).
destruct (Z_le_gt_dec (r + 16) (x_len x)) as [Hin|Hout].
- destruct (entryA x r regs2 mem2 md2 Hpre HL Hin) as [HS SHOK].
  (* 0x84570 li a1,0; 0x84574 bltu a2,a0: P + r < P + 8 never *)
  f_run HAE B20. f_br Hb1.
  { exfalso. f_hc HAE Hb1. rewrite U12, U10 in Hb1. apply Z.ltb_lt in Hb1. lia. }
  clear Hb1.
  (* 0x84578 sub a3,a2,a0; 0x8457c bltu a4,a3 *)
  f_run HAE B20. f_br Hb2.
  { exfalso. f_hc HAE Hb2. rewrite U14, U_sub_l, U12, U10 in Hb2.
    replace (x_P x + r - (x_P x + 8)) with (r - 8) in Hb2 by lia. rewrite (Z.mod_small (r - 8)) in Hb2 by lia.
    apply Z.ltb_lt in Hb2. lia. }
  clear Hb2.
  (* 0x84580 .. 0x84594: the checked load of the value size VS'; 0x84598 sub t0,a5,a2; 0x8459c bltu t0,a7 *)
  f_run HAE B20. f_br Hb3.
  { (* taken (S - 8 - r < VS'): prop_is_inside fails, find_prop = None; 0x84554 ret 0 *)
    f_hc HAE Hb3. rewrite U_sub_l, U15, U12, U_zext, U44 in Hb3. change (2 ^ Z.of_N 32) with (2 ^ 32) in Hb3.
    replace (x_P x + x_SZ x - 8 - (x_P x + r)) with (x_SZ x - 8 - r) in Hb3 by lia.
    rewrite (Z.mod_small (x_SZ x - 8 - r)) in Hb3 by lia. rewrite (Z.mod_small (Spa.u32_at _ _)) in Hb3 by lia.
    apply Z.ltb_lt in Hb3.
    assert (Hres0 : x_res x = (None, 0)).
    { rewrite Hres, reac_rate_prop_parse.find_prop_step, (f_outside (x_bs x) (x_SZ x) r Hr4 ltac:(lia) ltac:(right; lia)). reflexivity. }
    f_run HAE B20. f_leaf B x regs2 (f_L x r) MTL Hpre HAE H2 Hcs Hio Hret Hfrm Hres0. }
  f_hc HAE Hb3. rewrite U_sub_l, U15, U12, U_zext, U44 in Hb3. change (2 ^ Z.of_N 32) with (2 ^ 32) in Hb3.
  replace (x_P x + x_SZ x - 8 - (x_P x + r)) with (x_SZ x - 8 - r) in Hb3 by lia.
  rewrite (Z.mod_small (x_SZ x - 8 - r)) in Hb3 by lia. rewrite (Z.mod_small (Spa.u32_at _ _)) in Hb3 by lia.
  apply Z.ltb_ge in Hb3.
  assert (PI : Spa.prop_is_inside (x_bs x) 8 (x_SZ x) r = true) by (apply f_inside; lia).
  rewrite reac_rate_prop_parse.find_prop_step, PI in Hres.
  change Model.POD_PROP_PARAMS with 524289 in Hres.
  (* 0x845a0 .. 0x845b0: the checked load of the key; 0x845b4 beq t0,a6 *)
  f_run HAE B20. f_br Hb4;
  f_hc HAE Hb4; rewrite U16, (U_sx32_eqb _ _ _ 524289 U43 R0 ltac:(lia)) in Hb4.
  { (* taken: the key is SPA_PROP_params, find_prop = Some r; 0x845f8 .. the value checks *)
    apply Z.eqb_eq in Hb4.
    rewrite (proj2 (Z.eqb_eq _ _) Hb4) in Hres. cbn [l1_res] in Hres.
    (* 0x845f8 .. 0x84604 reload VS'; 0x84608 bnez (VS' >> 20) *)
    f_run HAE B20. f_br Hb5; f_hc HAE Hb5; rewrite Uc0, Usrl in Hb5.
    { (* taken: VS' >= 2^20, not a Struct *)
      apply negb_true_iff, Z.eqb_neq in Hb5.
      assert (HB20 : 2 ^ 20 <= Spa.u32_at (x_bs x) (r + 8))
        by (destruct (Z_lt_le_dec (Spa.u32_at (x_bs x) (r + 8)) (2 ^ 20)) as [Hlt|Hge];
            [exfalso; apply Hb5; apply Z.div_small; lia | exact Hge]).
      assert (HLT : (Spa.u32_at (x_bs x) (r + 8) <? 1048576) = false)
        by (apply Z.ltb_ge; change 1048576 with (2 ^ 20); lia).
      assert (HNS : Spa.is_struct_at (x_bs x) (r + 8) = false)
        by (rewrite reac_rate_prop_parse.pa_is_struct, HLT; reflexivity).
      assert (Hres0 : x_res x = (None, 0)) by (rewrite Hres, HNS; reflexivity).
      f_run HAE B20. f_leaf B x regs2 (f_L x r) MTL Hpre HAE H2 Hcs Hio Hret Hfrm Hres0. }
    apply negb_false_iff, Z.eqb_eq in Hb5.
    assert (HB20 : Spa.u32_at (x_bs x) (r + 8) < 2 ^ 20)
      by (apply Z.div_small_iff in Hb5; lia).
    (* 0x8460c .. 0x84620 the checked load of the value type; 0x84628 bne a0,a2 (type <> 14) *)
    f_run HAE B20. f_br Hb6a; f_hc HAE Hb6a;
    rewrite Uc14, (U_sx32_eqb _ _ _ 14 U45 R12 ltac:(lia)) in Hb6a.
    { (* taken: the value is not a Struct *)
      apply negb_true_iff, Z.eqb_neq in Hb6a.
      assert (HNS : Spa.is_struct_at (x_bs x) (r + 8) = false).
      { rewrite reac_rate_prop_parse.pa_is_struct. replace (r + 8 + 4) with (r + 12) by lia.
        rewrite (proj2 (Z.eqb_neq _ _) Hb6a), andb_false_r. reflexivity. }
      assert (Hres0 : x_res x = (None, 0)) by (rewrite Hres, HNS; reflexivity).
      f_run HAE B20. f_leaf B x regs2 (f_L x r) MTL Hpre HAE H2 Hcs Hio Hret Hfrm Hres0. }
    apply negb_false_iff, Z.eqb_eq in Hb6a.
    assert (HLT : (Spa.u32_at (x_bs x) (r + 8) <? 1048576) = true)
      by (apply Z.ltb_lt; change 1048576 with (2 ^ 20); lia).
    assert (HIS : Spa.is_struct_at (x_bs x) (r + 8) = true).
    { rewrite reac_rate_prop_parse.pa_is_struct. replace (r + 8 + 4) with (r + 12) by lia.
      rewrite HLT, (proj2 (Z.eqb_eq _ _) Hb6a). reflexivity. }
    assert (Hresw : x_res x =
      walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) (r + 16) (length (x_bs x)) None)
      by (rewrite Hres, HIS; reflexivity).
    (* 0x8462c .. 0x84640 (the 4-alignment test of P + r + 8 is decided by atom 12's alignment);
       0x84644 bltu a2,s4 (VS' < 8) *)
    f_run HAE B20. f_br Hb8; f_hc HAE Hb8;
    rewrite Uc8, (U_sext32 _ (SOff 44 0) _ U44 ltac:(lia)) in Hb8.
    { (* taken: a Struct of fewer than 8 bytes has no child *)
      apply Z.ltb_lt in Hb8.
      assert (Hres0 : x_res x = (None, 0)).
      { assert (Hlen : exists n0, length (x_bs x) = S n0).
        { unfold x_len in Hl8. destruct (length (x_bs x)) as [|n0];
          [cbn in Hl8; lia | exists n0; reflexivity]. }
        destruct Hlen as [n0 Hlen]. rewrite Hresw, Hlen.
        apply reac_rate_prop_parse.pa_walk_small. lia. }
      f_run HAE B20. f_leaf B x regs2 (f_L x r) MTL Hpre HAE H2 Hcs Hio Hret Hfrm Hres0. }
    apply Z.ltb_ge in Hb8.
    (* 0x84648 .. 0x84668 the foreach setup; L2 at c = r + 16 *)
    assert (Uzz : U (cut_env x regs2 (f_L x r))
                    (SAlu ALU_SRL (SAlu ALU_SLL (SExt true 32 (SOff 44 0)) (SLit 32)) (SLit 32)) =
                  Spa.u32_at (x_bs x) (r + 8)).
    { assert (Uc32 : U (cut_env x regs2 (f_L x r)) (SLit 32) = 32) by (apply U_lit; lia).
      rewrite U_srl by (rewrite Uc32; lia). rewrite U_sll by (rewrite Uc32; lia).
      rewrite Uc32, (U_sext32 _ (SOff 44 0) _ U44 ltac:(lia)).
      rewrite (Z.mod_small (Spa.u32_at (x_bs x) (r + 8) * 2 ^ 32)) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    assert (Ucm8 : U (cut_env x regs2 (f_L x r)) (SLit (-8)) = 2 ^ 64 - 8)
      by (rewrite U_SLit; unfold zcanon, M64; vm_compute; reflexivity).
    f_run_to HAE B20 PC_L2.
    rewrite (st_ok_restrict_mkst rsegs (w_H (x_W x)) _ _ _ HS ltac:(vm_compute; reflexivity)).
    apply (HL2 r (r + 16) None).
    split; [f_fi B x regs2 (f_L x r) HAE B20 Hio Hcs H2 H8 H19 [pod_region]|].
    split; [ split; [f_rg HAE; rewrite U12_16; lia|];
             split; [f_rg HAE; reflexivity|];
             split; [f_rg HAE; reflexivity|];
             split; [f_rg HAE; rewrite U12_16; lia|];
             split; [f_rg HAE; rewrite U_add by (rewrite U12_8, Uzz; lia); rewrite U12_8, Uzz; lia
                   | f_rg HAE; rewrite U_add_wrap, Uzz, Ucm8;
                     replace (Spa.u32_at (x_bs x) (r + 8) + (2 ^ 64 - 8))
                       with ((Spa.u32_at (x_bs x) (r + 8) - 8) + 1 * 2 ^ 64) by lia;
                     rewrite Z_mod_plus_full; apply Z.mod_small; lia] |].
    split; [f_rg HAE; reflexivity|].
    split; [ split; [lia|]; split; [exact Hr4|]; split; [exact HIS|]; split; [lia|lia] |].
    split; [lia|]. split; [apply f_mod4; [exact Hr4 | reflexivity]|].
    split; [intros ck Hck; discriminate Hck|].
    unfold l2_key, l2_fuel. rewrite Hresw. unfold walk_res.
    rewrite (Spa.struct_children_fuel (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) (r + 16)
              (length (x_bs x)) (S (Z.to_nat (r + 16 + Spa.u32_at (x_bs x) (r + 8) - (r + 16))))
              ltac:(lia) ltac:(unfold x_len in *; lia) ltac:(lia)).
    reflexivity. }
  (* not taken: this property is not SPA_PROP_params; the next one is at r' = r + round_up8 (16 + VS') *)
  apply Z.eqb_neq in Hb4.
  rewrite (proj2 (Z.eqb_neq _ _) Hb4) in Hres.
  pose proof (reac_rate_prop_parse.pa_ru_facts (Spa.u32_at (x_bs x) (r + 8)) ltac:(lia)) as (RU1 & RU2).
  (* 0x845b8 .. 0x845c8 (a2 = P + r'); 0x845cc beqz (r' & 3) -> L1 *)
  f_run HAE B20. f_br Hb6.
  { (* taken (r' & 3 = 0): 0x84570, the next pass of the find loop *)
    clear Hb6.
    f_run_to HAE B20 PC_L1.
    rewrite (st_ok_restrict_mkst rsegs (w_H (x_W x)) _ _ _ HS ltac:(vm_compute; reflexivity)).
    apply (HL1 (r + Spa.round_up8 (16 + Spa.u32_at (x_bs x) (r + 8))) ltac:(lia)).
    split; [f_fi B x regs2 (f_L x r) HAE B20 Hio Hcs H2 H8 H19 [pod_region]|].
    split; [f_rkeep x regs2 (f_L x r) HAE 10%nat (10%bv : bv 5); exact H10|].
    split; [f_rg HAE; exact Ur'|].
    split; [f_rkeep x regs2 (f_L x r) HAE 14%nat (14%bv : bv 5); exact H14|].
    split; [f_rkeep x regs2 (f_L x r) HAE 15%nat (15%bv : bv 5); exact H15|].
    split; [f_rkeep x regs2 (f_L x r) HAE 16%nat (16%bv : bv 5); exact H16|].
    split; [exact Hobj|]. split; [exact HS16|].
    split; [split; [lia|lia]|].
    split; [apply f_mod4; [exact Hr4 | apply f_mod4_of8; exact RU2]|].
    rewrite Hres.
    rewrite (Spa.find_prop_fuel (x_bs x) (x_SZ x) 524289
              (r + Spa.round_up8 (16 + Spa.u32_at (x_bs x) (r + 8)))
              (Z.to_nat (8 + x_SZ x - r))
              (S (Z.to_nat (8 + x_SZ x - (r + Spa.round_up8 (16 + Spa.u32_at (x_bs x) (r + 8))))))
              ltac:(lia) ltac:(lia) ltac:(lia)).
    reflexivity. }
  (* not taken (r' & 3 <> 0, then 0x845d0 j 0x84554, ret 0): never, r' = P + r + round_up8 (16 + VS') is 4-aligned *)
  exfalso. f_hc HAE Hb6. rewrite Uc0, (U_and_lit _ _ 3 ltac:(lia)), Ur',
    reac_rate_prop_parse.pa_land3 in Hb6.
  apply Z.eqb_neq in Hb6. apply Hb6.
  apply f_mod4; [apply f_mod4_of16; exact HP16 | apply f_mod4; [exact Hr4 | apply f_mod4_of8; exact RU2]].
- (* (B) the property header does not lie in the pod: prop_is_inside fails on its bounds test and the run
     leaves at 0x8457c with a1 = 0 *)
  destruct (entryB x r regs2 mem2 md2 Hpre HL) as [HS SHOK].
  assert (Hres0 : x_res x = (None, 0)).
  { rewrite Hres, reac_rate_prop_parse.find_prop_step,
      (f_outside (x_bs x) (x_SZ x) r Hr4 ltac:(lia) ltac:(left; lia)). reflexivity. }
  (* 0x84570 li a1,0; 0x84574 bltu a2,a0: P + r < P + 8 never *)
  f_run HAE B20. f_br Hb1.
  { exfalso. f_hc HAE Hb1. rewrite U12, U10 in Hb1. apply Z.ltb_lt in Hb1. lia. }
  clear Hb1.
  (* 0x84578 sub a3,a2,a0; 0x8457c bltu a4,a3: S - 16 < r - 8, so the loop ends at once *)
  f_run HAE B20. f_br Hb2; f_hc HAE Hb2; rewrite U14, U_sub_l, U12, U10 in Hb2;
  replace (x_P x + r - (x_P x + 8)) with (r - 8) in Hb2 by lia;
  rewrite (Z.mod_small (r - 8)) in Hb2 by lia.
  { f_run HAE B20. f_leaf B x regs2 (f_L x r) MTL Hpre HAE H2 Hcs Hio Hret Hfrm Hres0. }
  exfalso. apply Z.ltb_ge in Hb2. lia.
Qed.
End b.
