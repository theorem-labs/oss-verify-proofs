(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run plumbing of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (cfg_keep, cfg_kwr_ro and the same_io chain of cfg_leaf, as l_keep, l_kwr and l_post) and of proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at b0f706c04a1 (awr_stk, as l_awr: the writable window is the frame [F, F + 0x60) at atom 2), for a segment of reac_role_prop_parse's walk that starts and ends at the cuts of lib/A/RPgParseBase.v; the entry states, exits, string lemmas and the walk below are new. *)
(* reac_role_prop_parse 0x82ef0 of reac-pw/fuzz_role's ASan image A, segment L: one pass of the Struct foreach from
   the cut L2 0x830c0 to the next pass (L2), to the String child's last-byte check (LB), through the strcmp call
   0x83150 to its return (K), or to the return of 0. It proves RPgParseBase's segL_stmt under the Section hypotheses
   MTL, LAWS and STRCMP (the strcmp wrapper's contract at 0x41ad0); the segment loads no .got or shadow-cell word. *)
(* The walk (lib/A/RPgParseBase.v's cut states; code 0x830c0 .. 0x83180, slow paths 0x83184 .. 0x831c0):
     0x830c0 mv a1,zero; 0x830c4 bltu s1,s5 (s1 = P + c, s5 = P + r + 16: never taken, c >= r + 16);
     0x830cc bltu s7,a2 with a2 = s1 - s5 (s7 = VS - 8): taken when c + 8 > r + 16 + VS (the child's header is not in
       the body): to 0x832f4, a0 = 0 and the epilogue. The entry splits on this case: in the case c + 8 <= r + 16 + VS
       the 8 header bytes at P + c are a region at atom 9 (s1) with the two u32 chunks CS (slot 43) and the type
       (slot 44), and one shadow entry mkSHE 9 0 8 covers the instrumented checks at s1 (0x830d0 .. 0x830dc,
       0x830f0, 0x8315c) and at s1 + 4 (0x83104 .. 0x83114, slow path 0x831b4);
     0x830e8 bltu a2,a1 with a2 = s6 - s1 (s6 = P + r + 8 + VS), a1 = CS: taken when the child's body is not in the
       Struct body: to 0x82fa8, a1 = 0, then the epilogue (spa_pod_is_inside false: walk_res is (None, 0));
     0x830ec bnez a0: a0 is the pending key P + ck + 8 (ko = Some ck) or 0 (ko = None);
     ko = Some ck: 0x8314c mv a1,s2 (s2 = A_KEY), 0x83150 jal 0x41ad0 (the strcmp wrapper): its contract
       (RPgStrcmp.aj_strcmp_at) over the caller's journal, on the key (a C string in the pod, from key_ok) and the
       literal (rl_cstr at A_KEY, kept since the call); its return 0x83154 is the cut K;
     ko = None: spa_pod_get_string's tests 0x830fc srliw (CS >= 2^20), 0x83118 beqz (CS = 0), 0x83120 bne (type <> 8)
       go to 0x83158 (a0 = 0); a String child reaches LB 0x83130;
     0x8315c .. 0x83180: s1 += ((CS + 7) | 7) + 1 = round_up8 (8 + CS), the alignment test (never taken), back to
       L2 with the key slot empty. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Model Accessors Spa Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require reac_role_prop_parse.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgStrcmp RPgParseBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the entry states ======================================= *)
(* the child's 8 header bytes at s1 = P + c: its size CS (slot 43) and its type (slot 44) *)
Definition pod_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 43 0)); YP09.mkChunk 4 (CVal 4 (SOff 44 0))].
Definition l_atomsA : list (nat * afact) :=
[(2%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (9%nat, mkAF 0 (2 ^ 47 - 9) 2); (19%nat, mkAF SBr SBr 0);
 (43%nat, mkAF 0 (2 ^ 32 - 1) 0); (44%nat, mkAF 0 (2 ^ 32 - 1) 0)].
Definition l_atomsB : list (nat * afact) := [(2%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (19%nat, mkAF SBr SBr 0)].
(* the header in the body (case A) and out of it (case B) *)
Definition ss_LA : sstate := mkSS PC_L2 sr_atoms [frame_region []; pod_region] None (mkFacts l_atomsA [] []).
Definition ss_LB : sstate := mkSS PC_L2 sr_atoms [frame_region []] None (mkFacts l_atomsB [] []).
Definition SH_A : list shent := [mkSHE 9 0 8].
Definition l_vals (x : pctx) (c : Z) : list word :=
[w64 (Spa.u32_at (x_bs x) c); w64 (Spa.u32_at (x_bs x) (c + 4))].

(* ======================================= arithmetic ======================================= *)
Lemma U_subab : forall E n m a b, U E (SOff n 0) = a -> U E (SOff m 0) = b -> 0 <= b <= a ->
U E (SAlu ALU_ADD (SOff n 0) (SMd M_MUL (SOff m 0) (SLit (-1)))) = a - b.
Proof.
intros E n m a b Ha Hb Hab. pose proof (U_range E (SOff n 0)) as Ra. rewrite Ha in Ra. unfold M64 in Ra.
rewrite U_SAlu, U_SMd, Ha, Hb, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_r by lia. replace (a + b * 18446744073709551615) with ((a - b) + b * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma U_subba : forall E n m a b, U E (SOff n 0) = a -> U E (SOff m 0) = b -> 0 <= a <= b ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit (-1))) (SOff m 0)) = b - a.
Proof.
intros E n m a b Ha Hb Hab. pose proof (U_range E (SOff m 0)) as Rb. rewrite Hb in Rb. unfold M64 in Rb.
rewrite U_SAlu, U_SMd, Ha, Hb, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite Z.add_mod_idemp_l by lia. replace (a * 18446744073709551615 + b) with ((b - a) + a * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* lw of a u32 v: its sign extension *)
Lemma U_sext32 : forall E n v, U E (SOff n 0) = v -> 0 <= v < 2 ^ 32 ->
U E (SExt true 32 (SOff n 0)) = if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).
Proof.
intros E n v Hv Hr. rewrite U_SExt, Hv. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small v) by lia. unfold bv_swrap, bv_wrap, zcanon, M64.
change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec v (2 ^ 31)).
- rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia. apply Z.mod_small. lia.
- replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (v - 2 ^ 31)) by lia.
  replace (v - 2 ^ 31 - 2 ^ 31) with ((v + (2 ^ 64 - 2 ^ 32)) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* srliw a0,a1,20 of the sign-extended u32 v: v / 2^20 *)
Lemma U_srliw20 : forall E n v, U E (SOff n 0) = v -> 0 <= v < 2 ^ 32 ->
U E (SAluw ALU_SRL (SExt true 32 (SOff n 0)) (SLit 20)) = v / 2 ^ 20.
Proof.
intros E n v Hv Hr. rewrite U_of_S, S_SAluw, (U_sext32 E n v Hv Hr), U_SLit.
assert (Hm : (if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32)) mod 2 ^ 32 = v).
{ destruct (Z.ltb_spec v (2 ^ 31)); [apply Z.mod_small; lia|].
  replace (v + (2 ^ 64 - 2 ^ 32)) with (v + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  apply Z.mod_small. lia. }
rewrite Hm. change (zcanon 20 mod 2 ^ 32) with 20. cbn [zalu_raw]. change (Z.land 20 31) with 20.
rewrite Z.shiftr_div_pow2 by lia.
assert (0 <= v / 2 ^ 20 < 2 ^ 12) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
(* s1 + ((CS + 7) | 7) + 1, the next child *)
Lemma U_next : forall E v cs, U E (SOff 9 0) = v -> U E (SOff 43 0) = cs -> 0 <= cs < 2 ^ 32 -> 0 <= v ->
v + Spa.round_up8 (8 + cs) < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_OR (SOff 43 7) (SLit 7))) (SLit 1)) = v + Spa.round_up8 (8 + cs).
Proof.
intros E v cs Hv Hc Hcs Hv0 Hlt.
pose proof (reac_role_prop_parse.pb_lor7 cs ltac:(lia)) as (L1 & L2 & _).
assert (H43 : U E (SOff 43 7) = cs + 7).
{ rewrite U_SOff. pose proof (U_range E (SOff 43 0)) as R. rewrite U_SOff in Hc, R. unfold zcanon, M64 in *.
  rewrite Z.add_0_r in Hc, R. rewrite Z.mod_small in Hc by (pose proof (u64_range (ew E 43)); lia).
  rewrite Hc. apply Z.mod_small. lia. }
rewrite !U_SAlu, Hv, H43, !U_SLit. cbn [zalu_raw]. unfold zcanon, M64.
change (7 mod 2 ^ 64) with 7. change (1 mod 2 ^ 64) with 1.
rewrite (Z.mod_small (Z.lor (cs + 7) 7)) by lia. rewrite (Z.mod_small (v + Z.lor (cs + 7) 7)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma U_and3 : forall E e v, U E e = v -> v mod 4 = 0 -> U E (SAlu ALU_AND e (SLit 3)) = 0.
Proof.
intros E e v He Hv. rewrite U_SAlu, He, U_SLit. cbn [zalu_raw]. change (zcanon 3) with 3.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. rewrite Hv. reflexivity.
Qed.
Lemma U_off_of : forall E n v d, U E (SOff n 0) = v -> 0 <= v + d < 2 ^ 64 -> U E (SOff n d) = v + d.
Proof.
intros E n v d Hv Hd. pose proof (u64_range (ew E n)) as R. rewrite U_SOff in *. unfold zcanon, M64 in *.
rewrite Z.add_0_r, Z.mod_small in Hv by lia. rewrite Hv. apply Z.mod_small. lia.
Qed.
(* s8 = (s1 >> 3) + s3, the shadow address of the child (0x830d0 .. 0x830d4) *)
Lemma U_s8 : forall E v, U E (SOff 9 0) = v -> U E (SOff 19 0) = SHADOW_OFF -> 0 <= v < 2 ^ 47 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 19 0)) = Z.shiftr v 3 + SHADOW_OFF.
Proof.
intros E v H9 H19 Hv. rewrite !U_SAlu, H9, H19, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= v / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
unfold zcanon, M64, SHADOW_OFF in *. rewrite (Z.mod_small (v / 8)) by lia. apply Z.mod_small. lia.
Qed.
(* a1 = s1 + 8 + CS - 1, the String child's last body byte (0x83124 .. 0x8312c) *)
Lemma U_last : forall E v cs, U E (SOff 9 0) = v -> U E (SOff 43 0) = cs -> 0 <= v -> 0 <= cs < 2 ^ 31 ->
v + 8 + cs < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 8) (SExt true 32 (SOff 43 0))) (SLit (-1))) = v + 8 + cs - 1.
Proof.
intros E v cs H9 H43 Hv Hcs Hlt. rewrite !U_SAlu, (U_off_of E 9 v 8 H9 ltac:(lia)), (U_sext32 E 43 cs H43 ltac:(lia)), U_SLit.
rewrite (proj2 (Z.ltb_lt cs (2 ^ 31))) by lia. cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small (v + 8 + cs)) by lia. change ((-1) mod 2 ^ 64) with 18446744073709551615.
replace (v + 8 + cs + 18446744073709551615) with ((v + 8 + cs - 1) + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* bne a0,s4 of the sign-extended type word against s4 = 8 *)
Lemma U_sext32_eqb : forall E n v w, U E (SOff n 0) = v -> 0 <= v < 2 ^ 32 -> 0 <= w < 2 ^ 31 ->
(U E (SExt true 32 (SOff n 0)) =? w) = (v =? w).
Proof.
intros E n v w Hv Hr Hw. rewrite (U_sext32 E n v Hv Hr).
destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity|].
destruct (Z.eqb_spec (v + (2 ^ 64 - 2 ^ 32)) w); destruct (Z.eqb_spec v w); lia.
Qed.
Lemma mod4_sum : forall a b d, a mod 16 = 0 -> b mod 4 = 0 -> d mod 8 = 0 -> (a + b + d) mod 4 = 0.
Proof. intros a b d Ha Hb Hd. Z.div_mod_to_equations. lia. Qed.

(* ======================================= the model ======================================= *)
Lemma pin_out_c : forall bs body size c, size - 8 < c - body -> Spa.pod_is_inside bs body size c = false.
Proof.
intros bs body size c H. unfold Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside.
rewrite (proj2 (Z.leb_gt (c - body) (size - 8)) H). rewrite !andb_false_r. reflexivity.
Qed.
Lemma pin_out_s : forall bs body size c, Spa.ptr_remaining body size c 8 < Spa.u32_at bs c ->
Spa.pod_is_inside bs body size c = false.
Proof.
intros bs body size c H. unfold Spa.pod_is_inside. rewrite (proj2 (Z.leb_gt _ _) H). apply andb_false_r.
Qed.
Lemma pin_in : forall bs body size c, c mod 4 = 0 -> body <= c -> 8 <= size -> c - body <= size - 8 ->
Spa.u32_at bs c <= body + size - (c + 8) -> Spa.pod_is_inside bs body size c = true.
Proof.
intros bs body size c H4 H1 H2 H3 H5. unfold Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside, Spa.ptr_remaining.
rewrite H4, (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2), (proj2 (Z.leb_le _ _) H3),
  (proj2 (Z.leb_le _ _) H5). reflexivity.
Qed.

(* the next child c + round_up8 (8 + CS) with the key slot empty (no key, and the child is not a key) *)
Lemma l_model_next : forall x r c, 0 <= r -> r + 16 <= c -> c + 8 <= r + 16 + Spa.u32_at (x_bs x) (r + 8) ->
child_in x r c -> Spa.spa_get_string (Spa.child_at (x_bs x) c) = None ->
walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c (l2_fuel x r c) None =
walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))
  (l2_fuel x r (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))) None.
Proof.
intros x r c H0 H1 H2 Hin Hgs. unfold l2_fuel at 1. rewrite reac_role_prop_parse.walk_res_step.
unfold child_in in Hin. rewrite Hin, Hgs.
pose proof (u32_at_range (x_bs x) c) as R.
pose proof (reac_role_prop_parse.pb_lor7 (Spa.u32_at (x_bs x) c) ltac:(lia)) as (L1 & L2 & _).
unfold reac_role_prop_parse.walk_res.
rewrite (Spa.struct_children_fuel (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8))
  (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c)) (Z.to_nat (r + 16 + Spa.u32_at (x_bs x) (r + 8) - c))
  (l2_fuel x r (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c)))); [reflexivity | lia | lia | unfold l2_fuel; lia].
Qed.

(* ======================================= the walk's plumbing ======================================= *)
(* HAE : env_agree k E0 E names the entry env E0 and the current env E (the engine's fresh atoms are k and up);
   U2 : bv_unsigned (ew E0 2) = x_F x. *)
Ltac l_B2 HAE U2 E B2 :=
assert (B2 : bv_unsigned (ew E 2) = x_F _) by (first [exact U2 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact U2]).
(* the frame [F, F + 0x60) is the only writable window: it lies in the caller's stack window [sp0 - STK, sp0) *)
Ltac l_awr HAE U2 :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
let B2 := fresh "B2" in l_B2 HAE U2 E B2;
lazymatch type of B2 with _ = x_F ?x =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (x_F x - x_sp0 x));
  [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo]; unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia
  | cbn [YP09.r_whi]; unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia |] ] end end.
(* every write window of the run's start state lies in the callee's stack [sp - T_parse_STK, sp) *)
Ltac l_kwr HAE U2 :=
let a := fresh "a" in let rr := fresh "rr" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (rr & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In rr rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
   first [lia | lazymatch type of Hb with context [ew ?E 2] =>
     let B2 := fresh "B2" in l_B2 HAE U2 E B2; rewrite B2 in Hb;
     unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia end] | ]);
destruct Hr.
(* KE : the bytes outside the callee's stack are as at the call; the run's frame keeps it *)
Ltac l_keep HAE U2 :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (RPgCfgChanges.kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by (l_kwr HAE U2) end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* after a run: HAE and Hio follow the new env and model *)
Ltac l_post HAE Hio :=
lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
lazymatch type of HAE with env_agree ?k ?E0 _ =>
let H' := fresh "HAE'" in assert (H' : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H' into HAE end end;
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md _ |- _ =>
lazymatch type of Hio with same_io ?m0 _ =>
let H' := fresh "Hio'" in
assert (H' : same_io m0 md) by (let rec kio := first [exact Hio | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio] in kio);
clear Hio; rename H' into Hio end end.
(* one run of the engine to its next stop, or to the pc stop *)
Ltac l_run HAE U2 Hio :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok parse_tbl_ok HS HJ SHOK RTBspan; [l_awr HAE U2 | ] end;
l_keep HAE U2; l_post HAE Hio.
Ltac l_run_to HAE U2 Hio stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok parse_tbl_ok HS HJ SHOK RTBspan stop; [l_awr HAE U2 | ] end;
l_keep HAE U2; l_post HAE Hio.
(* the branch the engine cannot decide, its condition as Hc over the entry env *)
Ltac l_U0 HAE H :=
lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
first [ constr_eq E0 E1
      | repeat (rewrite (U_agree k E0 E1 _ HAE) in H by (vm_compute; reflexivity)) ]
end.
Ltac l_branch HAE Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok parse_tbl_ok HS SH RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end;
rewrite ?branch_ltu_U, ?branch_geu_U, ?branch_eq_U, ?branch_ne_U in Hc; l_U0 HAE Hc.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis STRCMP : astrcmp_realizes rsegs B A_STRCMP.

Lemma U_cut : forall x regs2 L n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs2 r = w64 v -> 0 <= v < 2 ^ 64 ->
U (cut_env x regs2 L) (SOff n 0) = v.
Proof. intros x regs2 L n r v Hn Hr Hv. apply U_atom; [|exact Hv]. rewrite (cut_env_reg x regs2 L n r Hn). exact Hr. Qed.

(* ---------------------------------- the registers at a stop ---------------------------------- *)
Lemma reg_kept : forall x regs2 L E ss ms (H : word -> bool) k n (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> env_agree k (cut_env x regs2 L) E -> (n < k)%nat ->
Z.of_nat n = bv_unsigned r -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = getr regs2 r.
Proof.
intros x regs2 L E ss ms H k n r HS HAE Hn Hr Hsr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, sv_denot_SOff0, (proj1 HAE n Hn).
apply cut_env_reg. exact Hr.
Qed.
Lemma reg_U : forall E ss ms (H : word -> bool) (r : bv 5) v,
st_ok rsegs E ss (restrict H ms) -> U E (sr_get (ss_regs ss) r) = v -> getr (ms_regs ms) r = w64 v.
Proof. intros E ss ms H r v HS Hv. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), denot_lit_U, Hv. reflexivity. Qed.
(* the registers FI fixes and the foreach keeps: as at the entry of the segment *)
Definition l_fixed (sr : list sv) : Prop :=
sr_get sr 2%bv = SOff 2 0 /\ sr_get sr 8%bv = SOff 8 0 /\ sr_get sr 19%bv = SOff 19 0 /\
(forall n, n = 3 \/ n = 4 \/ n = 25 \/ n = 26 \/ n = 27 -> sr_get sr (Z_to_bv 5 n) = SOff (Z.to_nat n) 0).
Definition l_l2fixed (sr : list sv) : Prop :=
sr_get sr 18%bv = SOff 18 0 /\ sr_get sr 20%bv = SOff 20 0 /\ sr_get sr 21%bv = SOff 21 0 /\
sr_get sr 22%bv = SOff 22 0 /\ sr_get sr 23%bv = SOff 23 0.
Ltac l_fixed_tac :=
split; [vm_compute; reflexivity|]; split; [vm_compute; reflexivity|]; split; [vm_compute; reflexivity|];
let n := fresh "n" in let Hn := fresh "Hn" in
intros n Hn; destruct Hn as [-> | [-> | [-> | [-> | ->]]]]; vm_compute; reflexivity.
Ltac l_l2fixed_tac := repeat split; vm_compute; reflexivity.

(* FI at a stop of the engine *)
Lemma fi_of_st : forall x regs2 mem2 md2 L E ss ms md k,
pre_ok B x -> FI B x regs2 mem2 md2 ->
st_ok rsegs E ss (restrict (w_H (x_W x)) ms) ->
env_agree k (cut_env x regs2 L) E -> (43 <= k)%nat ->
In (frame_region []) (ss_mem ss) -> l_fixed (ss_regs ss) ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) (ms_mem ms) md (x_k x) ->
same_io (x_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 aview rsegs (w_H (x_W x)) (ms_mem ms) a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
FI B x (ms_regs ms) (ms_mem ms) md.
Proof.
intros x regs2 mem2 md2 L E ss ms md k Hpre HFI HS HAE Hk Hin (F2 & F8 & F19 & Fcs) HJ Hio KE.
pose proof HFI as (_ & _ & _ & _ & H2 & Hcs & H8 & H19).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
split; [exact HJ|]. split; [exact Hio|]. split; [exact KE|]. split.
- pose proof (st_ok_mem_ok rsegs E ss _ HS) as (_ & HR & _).
  pose proof (proj1 (Forall_forall _ _) HR _ Hin) as HFR. cbn [ms_mem restrict] in HFR.
  apply (saved_of_frame_region x E _ [] HFR).
  + cbn [base_val]. rewrite (proj1 HAE 2%nat ltac:(lia)), (cut_env_reg x regs2 L 2 2%bv eq_refl), H2. unfold w64.
    apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia.
  + intros j Hj. rewrite (proj1 HAE (33 + j)%nat ltac:(lia)). apply cut_env_saved. exact Hj.
- split; [rewrite (reg_kept x regs2 L E ss ms _ k 2 2%bv HS HAE ltac:(lia) eq_refl F2); exact H2|].
  split; [|split].
  + intros n Hn.
    assert (Hz : Z.of_nat (Z.to_nat n) = bv_unsigned (Z_to_bv 5 n) /\ (Z.to_nat n < 43)%nat)
      by (destruct Hn as [-> | [-> | [-> | [-> | ->]]]]; (split; [reflexivity | cbn; lia])).
    rewrite (reg_kept x regs2 L E ss ms _ k (Z.to_nat n) (Z_to_bv 5 n) HS HAE ltac:(lia) (proj1 Hz) (Fcs n Hn)).
    exact (Hcs n Hn).
  + rewrite (reg_kept x regs2 L E ss ms _ k 8 8%bv HS HAE ltac:(lia) eq_refl F8). exact H8.
  + rewrite (reg_kept x regs2 L E ss ms _ k 19 19%bv HS HAE ltac:(lia) eq_refl F19). exact H19.
Qed.

(* ---------------------------------- the next pass, L2 ---------------------------------- *)
Lemma l_exit_L2 : forall x r c regs2 mem2 md2 L E ss ms md k c',
pre_ok B x -> FI B x regs2 mem2 md2 -> l2_regs x r c regs2 -> struct_ok x r ->
st_ok rsegs E ss (restrict (w_H (x_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_L2 ->
env_agree k (cut_env x regs2 L) E -> (43 <= k)%nat ->
In (frame_region []) (ss_mem ss) -> l_fixed (ss_regs ss) -> l_l2fixed (ss_regs ss) ->
sr_get (ss_regs ss) 10%bv = SLit 0 -> U E (sr_get (ss_regs ss) 9%bv) = x_P x + c' ->
r + 16 <= c' <= r + 16 + Spa.u32_at (x_bs x) (r + 8) + 7 -> c' mod 4 = 0 -> c < c' ->
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c' (l2_fuel x r c') None ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) (ms_mem ms) md (x_k x) ->
same_io (x_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 aview rsegs (w_H (x_W x)) (ms_mem ms) a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
(forall c'' ko', c < c'' <= r + 16 + Spa.u32_at (x_bs x) (r + 8) + 7 -> L2_ok B MT x r c'' ko') ->
SRr rsegs (x_W x) (mkCfg ms md) (PPOST B MT x false).
Proof.
intros x r c regs2 mem2 md2 L E ss ms md k c' Hpre HFI (R9 & R18 & R20 & R21 & R22 & R23) HSt HS Hrv Hpc HAE Hk
Hin Hfix (F18 & F20 & F21 & F22 & F23) F10 U9 Hc' Hc4 Hlt HW HJ Hio KE HNext.
rewrite (st_ok_restrict_mkst rsegs (w_H (x_W x)) E ss ms HS Hrv), Hpc.
apply (HNext c' None ltac:(lia) (ms_regs ms) (ms_mem ms) md).
split; [exact (fi_of_st x regs2 mem2 md2 L E ss ms md k Hpre HFI HS HAE Hk Hin Hfix HJ Hio KE)|].
split; [|split; [|split; [exact HSt|]]].
- split; [exact (reg_U E ss ms _ 9%bv _ HS U9)|].
  rewrite (reg_kept x regs2 L E ss ms _ k 18 18%bv HS HAE ltac:(lia) eq_refl F18),
    (reg_kept x regs2 L E ss ms _ k 20 20%bv HS HAE ltac:(lia) eq_refl F20),
    (reg_kept x regs2 L E ss ms _ k 21 21%bv HS HAE ltac:(lia) eq_refl F21),
    (reg_kept x regs2 L E ss ms _ k 22 22%bv HS HAE ltac:(lia) eq_refl F22),
    (reg_kept x regs2 L E ss ms _ k 23 23%bv HS HAE ltac:(lia) eq_refl F23).
  tauto.
- rewrite (st_ok_restrict_reg rsegs (w_H (x_W x)) E ss ms 10%bv HS), F10. reflexivity.
- split; [lia|]. split; [exact Hc4|]. split; [intros ck Hck; discriminate Hck|]. exact HW.
Qed.

(* ---------------------------------- the String child's last byte, LB ---------------------------------- *)
Lemma l_exit_LB : forall x r c regs2 mem2 md2 L E ss ms md k,
pre_ok B x -> FI B x regs2 mem2 md2 -> l2_regs x r c regs2 -> struct_ok x r ->
st_ok rsegs E ss (restrict (w_H (x_W x)) ms) -> ss_resv ss = None -> ss_pc ss = PC_LB ->
env_agree k (cut_env x regs2 L) E -> (43 <= k)%nat ->
In (frame_region []) (ss_mem ss) -> l_fixed (ss_regs ss) -> l_l2fixed (ss_regs ss) ->
sr_get (ss_regs ss) 9%bv = SOff 9 0 ->
U E (sr_get (ss_regs ss) 24%bv) = s8_val x c -> U E (sr_get (ss_regs ss) 10%bv) = x_P x + c + 8 ->
U E (sr_get (ss_regs ss) 11%bv) = x_P x + c + 8 + Spa.u32_at (x_bs x) c - 1 ->
r + 16 <= c -> c mod 4 = 0 -> child_in x r c ->
1 <= Spa.u32_at (x_bs x) c < Spa.SPA_POD_MAX_SIZE -> Spa.u32_at (x_bs x) (c + 4) = Model.POD_STRING ->
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c (l2_fuel x r c) None ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) (ms_mem ms) md (x_k x) ->
same_io (x_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 aview rsegs (w_H (x_W x)) (ms_mem ms) a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
LB_ok B MT x r c ->
SRr rsegs (x_W x) (mkCfg ms md) (PPOST B MT x false).
Proof.
intros x r c regs2 mem2 md2 L E ss ms md k Hpre HFI (R9 & R18 & R20 & R21 & R22 & R23) HSt HS Hrv Hpc HAE Hk
Hin Hfix (F18 & F20 & F21 & F22 & F23) F9 U24 U10 U11 Hc Hc4 Hci Hcs Hty HW HJ Hio KE HLB.
rewrite (st_ok_restrict_mkst rsegs (w_H (x_W x)) E ss ms HS Hrv), Hpc.
apply (HLB (ms_regs ms) (ms_mem ms) md).
split; [exact (fi_of_st x regs2 mem2 md2 L E ss ms md k Hpre HFI HS HAE Hk Hin Hfix HJ Hio KE)|].
split; [|split; [exact (reg_U E ss ms _ 24%bv _ HS U24)|]].
- unfold l2_regs. rewrite (reg_kept x regs2 L E ss ms _ k 9 9%bv HS HAE ltac:(lia) eq_refl F9),
    (reg_kept x regs2 L E ss ms _ k 18 18%bv HS HAE ltac:(lia) eq_refl F18),
    (reg_kept x regs2 L E ss ms _ k 20 20%bv HS HAE ltac:(lia) eq_refl F20),
    (reg_kept x regs2 L E ss ms _ k 21 21%bv HS HAE ltac:(lia) eq_refl F21),
    (reg_kept x regs2 L E ss ms _ k 22 22%bv HS HAE ltac:(lia) eq_refl F22),
    (reg_kept x regs2 L E ss ms _ k 23 23%bv HS HAE ltac:(lia) eq_refl F23).
  tauto.
- split; [exact (reg_U E ss ms _ 10%bv _ HS U10)|]. split; [exact (reg_U E ss ms _ 11%bv _ HS U11)|].
  tauto.
Qed.

(* ---------------------------------- the strcmp call, K ---------------------------------- *)
(* the pod's key string *)
Lemma bvals_length : forall l, length (bvals l) = length l.
Proof. intros l. unfold bvals. apply length_map. Qed.

Lemma nth_bvals : forall (l : list byte) j, nth j (bvals l) 0 = bv_unsigned (nth j l Cursor.NUL).
Proof. unfold bvals. induction l as [|b l IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma bvals_inj : forall l1 l2, bvals l1 = bvals l2 -> l1 = l2.
Proof.
unfold bvals. induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as Hb Hl. f_equal; [apply bv_eq; exact Hb | apply IH; exact Hl].
Qed.

(* the byte at the first NUL of l is NUL *)
Lemma nul_idx_nth : forall l : list byte, (Cursor.nul_idx l < length l)%nat ->
bv_unsigned (nth (Cursor.nul_idx l) l Cursor.NUL) = 0.
Proof.
induction l as [|b l IH]; [intros H; cbn in H; lia|].
cbn [Cursor.nul_idx length].
destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|E]; intros H; cbn [nth]; [exact E|].
apply IH. lia.
Qed.

Lemma byte_pos : forall b : byte, b <> Cursor.NUL -> 0 < bv_unsigned b < 256.
Proof.
intros b Hb. pose proof (Cursor.byte_range b) as R.
destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia].
exfalso. apply Hb. apply bv_eq. rewrite E. reflexivity.
Qed.

(* the view of the pod's byte j, in any memory that holds the pod *)
Lemma pod_aview : forall x (m : word -> option byte) j,
garr8 rsegs (mrestrict (w_H (x_W x)) m) (x_P x) (bvals (x_bs x)) -> (j < length (x_bs x))%nat ->
aview rsegs (w_H (x_W x)) m (x_P x + Z.of_nat j) = Some (bv_unsigned (nth j (x_bs x) Cursor.NUL)).
Proof.
intros x m j HG Hj. unfold aview.
rewrite (garr8_mbyte rsegs _ _ _ j HG) by (rewrite bvals_length; exact Hj).
cbn [option_map]. rewrite nth_bvals, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* the pending key: the String child at ck of the pod, a C string at P + ck + 8 inside the pod *)
Lemma key_cstr : forall x ck (m : word -> option byte),
garr8 rsegs (mrestrict (w_H (x_W x)) m) (x_P x) (bvals (x_bs x)) -> key_ok x ck ->
exists k', l2_key (x_bs x) (Some ck) = Some k' /\
cstr_at rsegs (x_W x) m (x_P x + ck + 8) (bvals k') /\
ck + 8 + Z.of_nat (length k') + 1 <= x_len x.
Proof.
intros x ck m HG (Hck & Hin & Hgs).
change (l2_key (x_bs x) (Some ck)) with (Spa.spa_get_string (Spa.child_at (x_bs x) ck)).
rewrite (reac_role_prop_parse.pb_gs (x_bs x) ck Hck Hin) in Hgs |- *.
match goal with |- context [if ?t then _ else _] => destruct t eqn:ET end;
[|exfalso; apply Hgs; rewrite ?ET; reflexivity].
apply andb_prop in ET as [ET1 E4]. apply andb_prop in ET1 as [_ E3].
apply Z.leb_le in E3. apply Z.eqb_eq in E4.
unfold x_len in Hin |- *.
set (CS := Spa.u32_at (x_bs x) ck) in *.
remember (firstn (Z.to_nat CS) (skipn (Z.to_nat (ck + 8)) (x_bs x))) as body eqn:EB.
assert (LB : length body = Z.to_nat CS) by (subst body; rewrite length_firstn, length_skipn; lia).
assert (EBn : forall k, (k < Z.to_nat CS)%nat ->
  nth k body Cursor.NUL = nth (Z.to_nat (ck + 8) + k) (x_bs x) Cursor.NUL).
{ intros k Hk. rewrite EB. rewrite reac_role_prop_parse.pb_nth_firstn by exact Hk.
  apply reac_role_prop_parse.pb_nth_skipn. }
assert (NB : bv_unsigned (nth (Z.to_nat CS - 1) body Cursor.NUL) = 0).
{ rewrite EBn by lia.
  replace (Z.to_nat (ck + 8) + (Z.to_nat CS - 1))%nat with (Z.to_nat (ck + 8 + CS - 1)) by lia. exact E4. }
pose proof (reac_role_prop_parse.pb_nul_idx_le body (Z.to_nat CS - 1) ltac:(lia) NB) as NI.
assert (LC : length (Cursor.cstr body) = Cursor.nul_idx body).
{ unfold Cursor.cstr. rewrite length_firstn. pose proof (Cursor.nul_idx_le body). lia. }
exists (Cursor.cstr body). split; [reflexivity|]. split; [|rewrite LC; lia].
unfold cstr_at. rewrite bvals_length, LC. split; [|split].
- intros i Hi. rewrite nth_bvals. unfold Cursor.cstr.
  rewrite reac_role_prop_parse.pb_nth_firstn by lia. rewrite EBn by lia.
  replace (x_P x + ck + 8 + i) with (x_P x + Z.of_nat (Z.to_nat (ck + 8) + Z.to_nat i)) by lia.
  apply pod_aview; [exact HG | lia].
- replace (x_P x + ck + 8 + Z.of_nat (Cursor.nul_idx body))
  with (x_P x + Z.of_nat (Z.to_nat (ck + 8) + Cursor.nul_idx body)) by lia.
  rewrite (pod_aview x m _ HG) by lia. rewrite <- EBn by lia. rewrite nul_idx_nth by lia. reflexivity.
- unfold bvals. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb). cbv beta.
  apply byte_pos. intros ->. exact (reac_role_prop_parse.pb_cstr_nonul body Hb).
Qed.

(* sub-ranges of the pod *)
Lemma hull_le : forall u v, u <= v -> shadow_addr u / 8 * 8 <= shadow_addr v / 8 * 8.
Proof.
intros u v H. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
Qed.

(* a byte range [a, a + n) of the pod, at a cut's memory: what the strcmp wrapper's contract asks of a source string;
   F = x_F x is the caller's sp at the call (the wrapper's window is [F - 2 ESTACK, F)) *)
Lemma pod_sub : forall x regs2 mem2 md2 (regsT : bvmap 5 word) a n, pre_ok B x -> FI B x regs2 mem2 md2 ->
spZ regsT = x_F x -> x_P x <= a -> a + n <= x_P x + x_len x -> 0 < n ->
src_ok rsegs (x_W x) regsT mem2 a n /\
(forall b, a <= b < a + n -> ~ (x_F x - 2 * ESTACK <= b < x_F x)) /\
amem_range a n /\
range_addressable (aview rsegs (w_H (x_W x)) mem2) SHADOW_OFF a n /\
shadow_hull_vis (aview rsegs (w_H (x_W x)) mem2) a n.
Proof.
intros x regs2 mem2 md2 regsT a n Hpre HFI HsT Ha Han Hn.
pose proof (pre_pod B x Hpre) as (HP0 & _ & Hl8 & _ & _ & _ & _ & _ & HAM & HDJ).
pose proof (pod_at_cut B x regs2 mem2 md2 Hpre HFI) as (HG & HRA & HHV).
assert (Hout : forall b, a <= b < a + n -> b < x_F x - 2 * ESTACK \/ x_F x <= b).
{ intros b Hb. unfold x_F, FRAME, ESTACK. unfold T_parse_STK, ESTACK in HDJ.
  destruct HDJ as [HD|HD]; [left|right]; lia. }
split; [|split; [|split; [|split]]].
- intros b Hb. split.
  + replace b with (x_P x + Z.of_nat (Z.to_nat (b - x_P x))) by lia.
    rewrite (pod_aview x mem2 _ HG) by (unfold x_len in Han; lia). discriminate.
  + rewrite HsT. pose proof (Hout b Hb) as Hb'. unfold ESTACK in *. lia.
- intros b Hb. pose proof (Hout b Hb) as Hb'. lia.
- destruct HAM as [HL|[HH1 HH2]]; [left; lia | right; split; lia].
- intros y Hy. apply HRA. lia.
- intros s Hs. apply HHV.
  pose proof (hull_le (x_P x) a Ha). pose proof (hull_le (a + n - 1) (x_P x + x_len x - 1) ltac:(lia)). lia.
Qed.

(* a string of the image (the literal at A_KEY): its rl_cstr facts at the call hold at any cut's memory *)
Lemma rl_cstr_cut : forall x regs2 mem2 md2 a s, pre_ok B x -> FI B x regs2 mem2 md2 ->
rl_cstr rsegs (w_H (x_W x)) (x_memc x) a s -> rl_cstr rsegs (w_H (x_W x)) mem2 a s.
Proof.
intros x regs2 mem2 md2 a s Hpre HFI (Hc & Hn & Hf & Ha0 & Hhi & Him & Ham & Hra & Hhv).
pose proof (pre_stack B x Hpre) as (Hceil & _).
pose proof asan_consts as ((C1 & C2) & _ & _ & C4 & C5).
assert (KS : forall t, 0 <= t < alloc_ceiling ->
  aview rsegs (w_H (x_W x)) mem2 t = aview rsegs (w_H (x_W x)) (x_memc x) t).
{ intros t Ht. apply (kept_view B x regs2 mem2 md2 t HFI); [pose proof alloc_ceiling_lt; lia | lia]. }
assert (Himg : forall i, 0 <= i <= Z.of_nat (length s) -> 0 <= a + i < kLowMemEnd).
{ intros i Hi. apply parse_segs_low. apply Him. exact Hi. }
assert (Hsh : forall y, 0 <= y < kLowMemEnd -> 0 <= SHADOW_OFF + y / 8 /\ SHADOW_OFF + y / 8 + 8 <= alloc_ceiling).
{ intros y Hy. split; [unfold SHADOW_OFF; pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia|].
  apply shadow_below_ceiling. rewrite C4. rewrite C5 in Hy. lia. }
unfold rl_cstr.
split; [|split; [|split; [exact Hf|split; [exact Ha0|split; [exact Hhi|split; [exact Him|split; [exact Ham|split]]]]]]].
- intros i Hi. rewrite KS; [exact (Hc i Hi)|]. pose proof (Himg i ltac:(lia)). lia.
- rewrite KS; [exact Hn|]. pose proof (Himg (Z.of_nat (length s)) ltac:(lia)). lia.
- intros y Hy. destruct (Hra y Hy) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite KS; [exact Hsv|]. unfold shadow_of_addr. pose proof (Himg (y - a) ltac:(lia)) as Hy'.
  replace (a + (y - a)) with y in Hy' by lia. pose proof (Hsh y Hy'). lia.
- intros t Ht Hnone. apply (Hhv t Ht). rewrite <- (KS t); [exact Hnone|].
  pose proof (Himg 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  pose proof (Himg (Z.of_nat (length s)) ltac:(lia)) as H1.
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Ht by lia.
  pose proof (Hsh a H0) as (S0 & _). pose proof (Hsh _ H1) as (_ & S1).
  unfold shadow_addr in Ht.
  pose proof (Z.mul_div_le (SHADOW_OFF + (a + Z.of_nat (length s)) / 8) 8 ltac:(lia)).
  assert (0 <= (SHADOW_OFF + a / 8) / 8) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma pres_r : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac acs_tac := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.

(* FI after the strcmp wrapper: it keeps the callee-saved registers and every byte outside [F - 2 ESTACK, F) *)
Lemma fi_after_call : forall x regsT memT mdT regs3 mem3 md3, pre_ok B x -> FI B x regsT memT mdT ->
aregs_preserved regsT regs3 ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) mem3 md3 (x_k x) ->
same_io mdT md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_F x - 2 * ESTACK <= a < x_F x) ->
 aview rsegs (w_H (x_W x)) mem3 a = aview rsegs (w_H (x_W x)) memT a) ->
FI B x regs3 mem3 md3.
Proof.
intros x regsT memT mdT regs3 mem3 md3 Hpre (HJ & Hio & KE & HSV & H2 & Hcs & H8 & H19) HP HJ3 Hio3 HK3.
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
split; [exact HJ3|]. split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split.
{ intros a Ha Hn. rewrite (HK3 a Ha) by (unfold x_F, FRAME, T_parse_STK in *; lia). exact (KE a Ha Hn). }
split.
{ apply Forall_forall. intros [off rg] Hin. pose proof (proj1 (Forall_forall _ _) HSV _ Hin) as Hv. cbn [fst snd] in *.
  assert (Hoff : 16 <= off <= 88).
  { unfold SAVED in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin. }
  apply (val_mem_kept rsegs (w_H (x_W x)) (w_H (x_W x)) memT mem3 _ 8 _); [|exact Hv].
  intros kk Hkk. apply HK3; unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia. }
split; [rewrite (pres_r regsT regs3 2%bv HP ltac:(acs_tac)); exact H2|].
split; [intros n Hn; rewrite (pres_r regsT regs3 (Z_to_bv 5 n) HP); [exact (Hcs n Hn)|];
  destruct Hn as [-> | [-> | [-> | [-> | ->]]]]; acs_tac|].
split; [rewrite (pres_r regsT regs3 8%bv HP ltac:(acs_tac)); exact H8|].
rewrite (pres_r regsT regs3 19%bv HP ltac:(acs_tac)); exact H19.
Qed.

Lemma rl_cstr_low : forall H m a s, rl_cstr rsegs H m a s ->
forall b, a <= b <= a + Z.of_nat (length s) -> 0 <= b < kLowMemEnd.
Proof.
intros H m a s (_ & _ & _ & _ & _ & Himg & _) b Hb. replace b with (a + (b - a)) by lia.
apply parse_segs_low. apply Himg. lia.
Qed.

Lemma l_exit_call : forall x r c ck regs2 mem2 md2 L E ss ms md k,
pre_ok B x -> FI B x regs2 mem2 md2 -> l2_regs x r c regs2 -> struct_ok x r ->
st_ok rsegs E ss (restrict (w_H (x_W x)) ms) -> ss_resv ss = None -> ss_pc ss = A_STRCMP ->
env_agree k (cut_env x regs2 L) E -> (43 <= k)%nat ->
In (frame_region []) (ss_mem ss) -> l_fixed (ss_regs ss) -> l_l2fixed (ss_regs ss) ->
sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 1%bv = SLit PC_K ->
sr_get (ss_regs ss) 10%bv = SOff 10 0 -> sr_get (ss_regs ss) 11%bv = SOff 18 0 ->
U E (sr_get (ss_regs ss) 24%bv) = s8_val x c ->
getr regs2 10 = w64 (x_P x + ck + 8) -> key_ok x ck ->
r + 16 <= c -> c mod 4 = 0 -> child_in x r c ->
x_res x = walk_res (x_bs x) (r + 16) (Spa.u32_at (x_bs x) (r + 8)) c (l2_fuel x r c) (l2_key (x_bs x) (Some ck)) ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) (ms_mem ms) md (x_k x) ->
same_io (x_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 aview rsegs (w_H (x_W x)) (ms_mem ms) a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
(forall ck' rv, K_ok B MT x r c ck' rv) ->
SRr rsegs (x_W x) (mkCfg ms md) (PPOST B MT x false).
Proof.
intros x r c ck regs2 mem2 md2 L E ss ms md k Hpre HFI (R9 & R18 & R20 & R21 & R22 & R23) HSt HS Hrv Hpc HAE Hk
Hin Hfix (F18 & F20 & F21 & F22 & F23) F9 F1 F10 F11 U24 H10 HKo Hc Hc4 Hci HW HJ Hio KE HKc.
pose proof (fi_of_st x regs2 mem2 md2 L E ss ms md k Hpre HFI HS HAE Hk Hin Hfix HJ Hio KE) as HFIT.
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & HSZ & HP63 & _ & _ & _ & HAM & HDJ).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpre as ((HJc & Hra & Hra4 & Hgp & Htp & _) & _ & _ & _ & _ & _ & _ & Hlit & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & _).
pose proof HFIT as (_ & _ & _ & _ & T2 & Tcs & T8 & T19).
(* the registers at the call *)
assert (R10 : getr (ms_regs ms) 10 = w64 (x_P x + ck + 8))
  by (rewrite (reg_kept x regs2 L E ss ms _ k 10 10%bv HS HAE ltac:(lia) eq_refl F10); exact H10).
assert (R11 : getr (ms_regs ms) 11 = w64 A_KEY).
{ rewrite (st_ok_restrict_reg rsegs (w_H (x_W x)) E ss ms 11%bv HS), F11, sv_denot_SOff0, (proj1 HAE 18%nat ltac:(lia)).
  rewrite (cut_env_reg x regs2 L 18 18%bv eq_refl). exact R18. }
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 PC_K)
  by (rewrite (st_ok_restrict_reg rsegs (w_H (x_W x)) E ss ms 1%bv HS), F1; reflexivity).
assert (Rsp : spZ (ms_regs ms) = x_F x).
{ unfold spZ. rewrite T2. unfold w64. apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia. }
assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ replace (3%bv : bv 5) with (Z_to_bv 5 3) by (apply bv_eq; reflexivity). rewrite (Tcs 3 ltac:(tauto)).
  replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact Hgp. }
assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ replace (4%bv : bv 5) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity). rewrite (Tcs 4 ltac:(tauto)).
  replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact Htp. }
(* the two strings: the key in the pod, the literal in the image *)
pose proof (pod_at_cut B x _ _ _ Hpre HFIT) as (HG & _ & _).
destruct (key_cstr x ck (ms_mem ms) HG HKo) as (k' & Hk' & Hkc & Hkl).
pose proof (rl_cstr_cut x _ _ _ A_KEY (bvals Role.ROLE_KEY) Hpre HFIT Hlit) as HyT.
pose proof (rl_cstr_low _ _ _ _ HyT) as Ly.
destruct (str_meet_of_cstr rsegs (bvals k') (x_W x) (ms_mem ms) (x_P x + ck + 8) (bvals Role.ROLE_KEY) A_KEY Hkc
  (cstr_at_of_rl_cstr rsegs (x_W x) (ms_mem ms) A_KEY _ HyT)) as (kk & c1 & c2 & Hmeet & Hk1 & Hk2 & Hres).
assert (LK : length (bvals Role.ROLE_KEY) = 13%nat)
  by (unfold bvals; rewrite length_map; exact reac_role_prop_parse.ROLE_KEY_length).
assert (LK' : length (bvals k') = length k') by (unfold bvals; apply length_map).
rewrite LK' in Hk1. rewrite LK in Hk2.
pose proof HKo as (Hck0 & Hckl & _).
destruct (pod_sub x _ _ _ (ms_regs ms) (x_P x + ck + 8) (kk + 1) Hpre HFIT Rsp ltac:(lia) ltac:(lia) ltac:(lia))
  as (Hsx & Hwx & Hmx & Hrx & Hhx).
destruct (rl_cstr_args rsegs (x_W x) (ms_regs ms) (ms_mem ms) A_KEY (bvals Role.ROLE_KEY) kk HyT ltac:(rewrite LK; lia)
  ltac:(intros b Hb; pose proof (Ly b Hb); rewrite Rsp; rewrite C5 in *; unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *; lia))
  as (Hy0 & Hyk & Hsy & Hmy & Hry & Hhy).
rewrite (st_ok_restrict_mkst rsegs (w_H (x_W x)) E ss ms HS Hrv), Hpc.
eapply SRr_bind.
{ apply (aj_strcmp_at rsegs B LAWS parse_segs_low A_STRCMP STRCMP (x_W x) (ms_regs ms) (ms_mem ms) (x_STK x) (x_sp0 x)
    (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x) (x_lyc x) (x_Sc x) md (x_k x)
    (x_P x + ck + 8) A_KEY kk c1 c2 (x_F x - x_sp0 x) (Z_to_bv 64 PC_K) HJ R10 R11).
  - lia.
  - unfold A_KEY. lia.
  - lia.
  - lia.
  - exact Hyk.
  - exact Hmeet.
  - rewrite Rsp. lia.
  - unfold x_F, x_sp, FRAME in *. Z.div_mod_to_equations. lia.
  - unfold x_F, x_sp, FRAME in *. lia.
  - unfold x_F, x_sp, FRAME, T_parse_STK in *. lia.
  - exact G3.
  - exact G4.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - exact Hsx.
  - exact Hsy.
  - intros a Ha. replace (x_sp0 x + (x_F x - x_sp0 x)) with (x_F x) by lia. apply Hwx. lia.
  - intros a Ha. pose proof (Ly a ltac:(rewrite LK; lia)). replace (x_sp0 x + (x_F x - x_sp0 x)) with (x_F x) by lia.
    rewrite C5 in *. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia.
  - exact Hmx.
  - exact Hmy.
  - exact Hrx.
  - exact Hhx.
  - exact Hry.
  - exact Hhy. }
cbv beta. intros W' c' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hio3 & R10' & HK3 & _).
apply (HKc ck (strcmp_res c1 c2) regs3 mem3 md3).
assert (HFI3 : FI B x regs3 mem3 md3).
{ apply (fi_after_call x (ms_regs ms) (ms_mem ms) md regs3 mem3 md3 Hpre HFIT HP3 HJ3 Hio3).
  intros a Ha Hn. apply HK3; [exact Ha|]. intros Hw. apply Hn. lia. }
split; [exact HFI3|].
split.
{ unfold l2_regs.
  rewrite (pres_r _ regs3 9%bv HP3 ltac:(acs_tac)), (pres_r _ regs3 18%bv HP3 ltac:(acs_tac)),
    (pres_r _ regs3 20%bv HP3 ltac:(acs_tac)), (pres_r _ regs3 21%bv HP3 ltac:(acs_tac)),
    (pres_r _ regs3 22%bv HP3 ltac:(acs_tac)), (pres_r _ regs3 23%bv HP3 ltac:(acs_tac)).
  rewrite (reg_kept x regs2 L E ss ms _ k 9 9%bv HS HAE ltac:(lia) eq_refl F9),
    (reg_kept x regs2 L E ss ms _ k 18 18%bv HS HAE ltac:(lia) eq_refl F18),
    (reg_kept x regs2 L E ss ms _ k 20 20%bv HS HAE ltac:(lia) eq_refl F20),
    (reg_kept x regs2 L E ss ms _ k 21 21%bv HS HAE ltac:(lia) eq_refl F21),
    (reg_kept x regs2 L E ss ms _ k 22 22%bv HS HAE ltac:(lia) eq_refl F22),
    (reg_kept x regs2 L E ss ms _ k 23 23%bv HS HAE ltac:(lia) eq_refl F23).
  tauto. }
split; [rewrite (pres_r _ regs3 24%bv HP3 ltac:(acs_tac)); exact (reg_U E ss ms _ 24%bv _ HS U24)|].
split; [exact R10'|].
split; [exact HSt|]. split; [exact Hc|]. split; [exact Hc4|]. split; [exact Hci|]. split; [exact HKo|].
split; [unfold strcmp_res; destruct (c1 =? c2); [lia|]; destruct (c1 <? c2); lia|].
split; [|exact HW].
rewrite Hk'. split.
- intros H0. apply Hres in H0. apply bvals_inj in H0. rewrite H0. reflexivity.
- intros H0. injection H0 as ->. apply Hres. reflexivity.
Qed.

(* ---------------------------------- the entry ---------------------------------- *)
Lemma l_entryA : forall x r c ko regs2 mem2 md2, pre_ok B x -> L2_at B x r c ko regs2 mem2 md2 ->
c + 8 <= r + 16 + Spa.u32_at (x_bs x) (r + 8) ->
st_ok rsegs (cut_env x regs2 (l_vals x c)) ss_LA
(restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_L2) mem2 (seg_rom rsegs))) /\
sh_ok rsegs PBx SH_A (cut_env x regs2 (l_vals x c)) (mrestrict (w_H (x_W x)) mem2).
Proof.
intros x r c ko regs2 mem2 md2 Hpre HL2 HA.
pose proof HL2 as (HFI & (R9 & R18 & R20 & R21 & R22 & R23) & H10 & (Hr16 & Hr4 & Hst & HV8 & HVl) & Hc & Hc4 & HKo & HW).
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & HSZ & HP63 & _ & _ & _ & HAM & HDJ).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof (pod_at_cut B x regs2 mem2 md2 Hpre HFI) as (HG & HRA & HHV).
pose proof (amem_range_bounds (x_P x) (x_len x) ltac:(lia) ltac:(lia) HAM) as Hhm.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HFI as (_ & _ & _ & _ & H2 & Hcs & H8 & H19).
pose proof (u32_at_range (x_bs x) c) as RCS. pose proof (u32_at_range (x_bs x) (c + 4)) as RTY.
set (E := cut_env x regs2 (l_vals x c)).
assert (U2 : bv_unsigned (ew E 2) = x_F x).
{ subst E. rewrite (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2. unfold w64.
  apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia. }
assert (U9 : bv_unsigned (ew E 9) = x_P x + c).
{ subst E. rewrite (cut_env_reg x regs2 _ 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF).
{ subst E. rewrite (cut_env_reg x regs2 _ 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (E43 : ew E 43 = w64 (Spa.u32_at (x_bs x) c)) by (subst E; exact (cut_env_seg x regs2 (l_vals x c) 0)).
assert (E44 : ew E 44 = w64 (Spa.u32_at (x_bs x) (c + 4))) by (subst E; exact (cut_env_seg x regs2 (l_vals x c) 1)).
split.
- rewrite restrict_mkst_fx. unfold ss_LA. apply (entry_st_ok_full rsegs).
  + apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (frame_region_ok B x regs2 mem2 md2 (l_vals x c) [] HFI Hpre (Forall_nil _)).
    * unfold region_ok, pod_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      change (Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ l_vals x c)) with E. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val rsegs E _ (x_P x + c) 0 4 (SOff 43 0) (Spa.u32_at (x_bs x) c));
         [rewrite sv_denot_SOff0, E43; reflexivity | cbn; lia | cbn; lia |].
         rewrite Z.add_0_r. apply pod_u32; [exact HG | lia | lia].
      -- apply (chunk_ok_val rsegs E _ (x_P x + c) 4 4 (SOff 44 0) (Spa.u32_at (x_bs x) (c + 4)));
         [rewrite sv_denot_SOff0, E44; reflexivity | cbn; lia | cbn; lia |].
         replace (x_P x + c + 4) with (x_P x + (c + 4)) by lia. apply pod_u32; [exact HG | lia | lia].
  + apply pairwise_disjoint_of_extents. unfold frame_region, pod_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ l_vals x c)) with E. rewrite U2, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *.
    repeat split; try exact I. destruct HDJ as [HD|HD]; [right | left]; lia.
  + split; [|split; [exact I | exact I]]. cbn [l_atomsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ l_vals x c)) with E.
    rewrite U2, U9, U19, E43, E44. unfold w64. rewrite !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    assert (x_F x mod 16 = 0) by (unfold x_F, x_sp, FRAME in *; Z.div_mod_to_equations; lia).
    assert ((x_P x + c) mod 4 = 0) by (Z.div_mod_to_equations; lia).
    unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK, SBr, SHADOW_OFF in *. repeat split; lia.
- unfold sh_ok, SH_A. apply Forall_cons; [|apply Forall_nil].
  apply (shent_pod B x regs2 mem2 md2 E PBx 9 c 0 8 Hpre HFI); [| | lia | lia | lia].
  + unfold U, PBx. rewrite sv_denot_SOff0. exact U19.
  + unfold U. rewrite sv_denot_SOff0. exact U9.
Qed.

Lemma l_entryB : forall x r c ko regs2 mem2 md2, pre_ok B x -> L2_at B x r c ko regs2 mem2 md2 ->
st_ok rsegs (cut_env x regs2 []) ss_LB
(restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_L2) mem2 (seg_rom rsegs))) /\
sh_ok rsegs PBx [] (cut_env x regs2 []) (mrestrict (w_H (x_W x)) mem2).
Proof.
intros x r c ko regs2 mem2 md2 Hpre HL2.
pose proof HL2 as (HFI & _).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HFI as (_ & _ & _ & _ & H2 & Hcs & H8 & H19).
set (E := cut_env x regs2 []).
assert (U2 : bv_unsigned (ew E 2) = x_F x).
{ subst E. rewrite (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2. unfold w64.
  apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia. }
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF).
{ subst E. rewrite (cut_env_reg x regs2 _ 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
split; [|constructor].
rewrite restrict_mkst_fx. unfold ss_LB. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  apply (frame_region_ok B x regs2 mem2 md2 [] [] HFI Hpre (Forall_nil _)).
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. cbn [l_atomsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  change (Ereg regs2 (w64 SBr :: saved_vals (x_regs x) ++ [])) with E.
  rewrite U2, U19. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
  assert (x_F x mod 16 = 0) by (unfold x_F, x_sp, FRAME in *; Z.div_mod_to_equations; lia).
  unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK, SBr, SHADOW_OFF in *. repeat split; lia.
Qed.

(* ---------------------------------- the return of 0 ---------------------------------- *)
(* at the `ret` 0x83324 after the epilogue, a0 = 0 and the answer is (None, 0) *)
Lemma l_leaf0 : forall x regs2 mem2 md2 L E ss ms md k,
pre_ok B x -> FI B x regs2 mem2 md2 ->
st_ok rsegs E ss (restrict (w_H (x_W x)) ms) -> ss_resv ss = None ->
clookup parse_tbl (ss_pc ss) = Some RET_WORD_r ->
env_agree k (cut_env x regs2 L) E -> (43 <= k)%nat ->
leaf_sr_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 10%bv = SLit 0 ->
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) (ms_mem ms) md (x_k x) ->
same_io (x_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 aview rsegs (w_H (x_W x)) (ms_mem ms) a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
x_res x = (None, 0) ->
SRr rsegs (x_W x) (mkCfg ms md) (PPOST B MT x false).
Proof.
intros x regs2 mem2 md2 L E ss ms md k Hpre HFI HS Hrv Hret HAE Hk Hleaf H10 HJ Hio KE Hres.
pose proof HFI as (_ & _ & _ & _ & H2 & Hcs & _).
destruct (leaf_regs B x regs2 L E ss ms (w_H (x_W x)) Hpre HS
  (fun n Hn => proj1 HAE n ltac:(lia)) Hleaf H2 Hcs) as (Hpres & Hra).
eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E ss ms md); [exact HS | exact Hrv | exact Hret |].
intros mat'.
destruct Hpre as ((_ & Hrok & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hfz).
rewrite Hra. unfold YK0s.ret_ok in Hrok. rewrite Hrok.
apply (ppost_intro B MT MTL x false fx (ms_regs ms) (ms_mem ms) _).
- eapply ajournal_materialize; [exact LAWS | exact parse_segs_low | exact HJ].
- eapply same_io_trans; [exact Hio | apply RPgCfgChanges.same_io_wvb].
- exact Hpres.
- apply rl_fxk_refl. exact Hfz.
- intros a Ha Hn _. exact (KE a Ha Hn).
- rewrite (st_ok_restrict_reg rsegs (w_H (x_W x)) E ss ms 10%bv HS), H10.
  unfold rl_parse_res. change (Role.parse_model (x_bs x)) with (x_res x). rewrite Hres. reflexivity.
- unfold rl_parse_res. change (Role.parse_model (x_bs x)) with (x_res x). rewrite Hres. exact I.
Qed.

(* U of a register at a stop, as an expression over the entry env *)
Ltac l_ureg HAE :=
lazymatch goal with |- U ?E (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity) end;
lazymatch type of HAE with env_agree ?k ?E0 ?E1 =>
first [constr_eq E0 E1 | rewrite (U_agree k E0 E1 _ HAE) by (vm_compute; reflexivity)] end.

(* ======================================= the pass ======================================= *)
Theorem segL_ok : segL_stmt B MT.
Proof using MTL LAWS STRCMP.
unfold segL_stmt. intros x r c ko Hpre HNext HLB HKc regs2 mem2 md2 HL2.
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
pose proof HL2 as (HFI & (R9 & R18 & R20 & R21 & R22 & R23) & H10 & (Hr16 & Hr4 & Hst & HV8 & HVl) & Hc & Hc4 & HKo & HW).
pose proof HL2 as (_ & HR & _ & HSt & _).
pose proof HFI as (HJ & Hio & KE & HSV & H2 & Hcs & H8 & H19).
pose proof (pre_pod B x Hpre) as (HP0 & HP16 & Hl8 & HSZ & HP63 & _ & _ & _ & HAM & HDJ).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof (amem_range_bounds (x_P x) (x_len x) ltac:(lia) ltac:(lia) HAM) as Hhm.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (VS := Spa.u32_at (x_bs x) (r + 8)) in *.
unfold cfg_at. change (w64 PC_L2) with (Z_to_bv 64 PC_L2).
destruct (Z_le_gt_dec (c + 8) (r + 16 + VS)) as [HA | HBo].
- (* the child's header is in the body: its two words are the region at s1 = P + c *)
  destruct (l_entryA x r c ko regs2 mem2 md2 Hpre HL2 HA) as [HS SHOK].
  set (E0 := cut_env x regs2 (l_vals x c)) in *.
  assert (HAE : env_agree 45 E0 E0) by apply env_agree_refl.
  assert (U2 : bv_unsigned (ew E0 2) = x_F x).
  { subst E0. rewrite (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2. unfold w64.
    apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia. }
  pose proof (u32_at_range (x_bs x) c) as RCS. pose proof (u32_at_range (x_bs x) (c + 4)) as RTY.
  assert (U9 : U E0 (SOff 9 0) = x_P x + c) by (apply (U_cut x regs2 _ 9 9%bv); [reflexivity | exact R9 | lia]).
  assert (U19 : U E0 (SOff 19 0) = SHADOW_OFF)
    by (apply (U_cut x regs2 _ 19 19%bv); [reflexivity | exact H19 | unfold SHADOW_OFF; lia]).
  assert (U20 : U E0 (SOff 20 0) = 8) by (apply (U_cut x regs2 _ 20 20%bv); [reflexivity | exact R20 | lia]).
  assert (U21 : U E0 (SOff 21 0) = x_P x + r + 16) by (apply (U_cut x regs2 _ 21 21%bv); [reflexivity | exact R21 | lia]).
  assert (U22 : U E0 (SOff 22 0) = x_P x + r + 8 + VS) by (apply (U_cut x regs2 _ 22 22%bv); [reflexivity | exact R22 | lia]).
  assert (U23 : U E0 (SOff 23 0) = VS - 8) by (apply (U_cut x regs2 _ 23 23%bv); [reflexivity | exact R23 | lia]).
  assert (U43 : U E0 (SOff 43 0) = Spa.u32_at (x_bs x) c)
    by (apply U_atom; [exact (cut_env_seg x regs2 (l_vals x c) 0) | lia]).
  assert (U44 : U E0 (SOff 44 0) = Spa.u32_at (x_bs x) (c + 4))
    by (apply U_atom; [exact (cut_env_seg x regs2 (l_vals x c) 1) | lia]).
  (* 0x830c0 mv a1,zero; stop at 0x830c4 bltu s1,s5 *)
  l_run HAE U2 Hio. l_branch HAE Hb1.
  { exfalso. rewrite U9, U21 in Hb1. apply Z.ltb_lt in Hb1. lia. }
  (* stop at 0x830cc bltu s7,a2 *)
  l_run HAE U2 Hio. l_branch HAE Hb2.
  { exfalso. rewrite U23, (U_subab E0 9 21 _ _ U9 U21 ltac:(lia)) in Hb2. apply Z.ltb_lt in Hb2. lia. }
  (* 0x830d0 .. 0x830e4: the check of s1 (shadow entry), lwu CS; stop at 0x830e8 bltu a2,a1 *)
  l_run HAE U2 Hio. l_branch HAE Hb3.
  { (* the child's body is not in the Struct body: 0x82fa8 a1 = 0, the epilogue, stop at the `ret` *)
    rewrite (U_subba E0 9 22 _ _ U9 U22 ltac:(lia)), U43 in Hb3. apply Z.ltb_lt in Hb3.
    l_run HAE U2 Hio.
    eapply (l_leaf0 x regs2 mem2 md2 (l_vals x c) _ _ _ _ 45 Hpre HFI HS eq_refl ltac:(vm_compute; reflexivity) HAE
      ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ Hio KE).
    rewrite HW. unfold l2_fuel. rewrite reac_role_prop_parse.walk_res_step, pin_out_s; [reflexivity|].
    unfold Spa.ptr_remaining. lia. }
  rewrite (U_subba E0 9 22 _ _ U9 U22 ltac:(lia)), U43 in Hb3. apply Z.ltb_ge in Hb3.
  assert (Hci : child_in x r c) by (apply pin_in; lia).
  pose proof (reac_role_prop_parse.pb_lor7 (Spa.u32_at (x_bs x) c) ltac:(lia)) as (L71 & L72 & L73).
  assert (Hm4 : (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c)) mod 4 = 0)
    by (rewrite <- L72; Z.div_mod_to_equations; lia).
  assert (Un : U E0 (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_OR (SOff 43 7) (SLit 7))) (SLit 1)) =
    x_P x + (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))) by (rewrite (U_next E0 _ _ U9 U43); lia).
  assert (Un4 : (x_P x + (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))) mod 4 = 0)
    by (rewrite <- L72 in *; Z.div_mod_to_equations; lia).
  (* stop at 0x830ec bnez a0 *)
  l_run HAE U2 Hio. l_branch HAE Hb4.
  { (* a0 = P + ck + 8: the key slot holds the key of the String child at ck; the strcmp call *)
    destruct ko as [ck|].
    2: { exfalso. assert (U10 : U E0 (SOff 10 0) = 0) by (apply (U_cut x regs2 _ 10 10%bv); [reflexivity | exact H10 | lia]).
         rewrite U10, U_lit in Hb4 by lia. discriminate Hb4. }
    (* 0x8314c mv a1,s2; 0x83150 jal 0x41ad0: stop at the wrapper *)
    l_run HAE U2 Hio.
    eapply (l_exit_call x r c ck regs2 mem2 md2 (l_vals x c) _ _ _ _ 45 Hpre HFI HR HSt HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | vm_compute; left; reflexivity
    | l_fixed_tac | l_l2fixed_tac | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | l_ureg HAE; exact (U_s8 E0 _ U9 U19 ltac:(lia)) | exact H10 | exact (HKo ck eq_refl)
    | lia | exact Hc4 | exact Hci | exact HW | exact HJ | exact Hio | exact KE | exact HKc ]. }
  destruct ko as [ck|].
  { exfalso. pose proof (HKo ck eq_refl) as (Hck0 & Hckl & _). pose proof (u32_at_range (x_bs x) ck).
    assert (U10 : U E0 (SOff 10 0) = x_P x + ck + 8)
      by (apply (U_cut x regs2 _ 10 10%bv); [reflexivity | exact H10 | lia]).
    rewrite U10, U_lit in Hb4 by lia.
    apply negb_false_iff, Z.eqb_eq in Hb4. lia. }
  (* the key slot is empty: spa_pod_get_string's tests; stop at 0x83100 bnez (srliw CS, 20) *)
  l_run HAE U2 Hio. l_branch HAE Hb5.
  { (* CS >= 2^20: 0x83158 a0 = 0, the next child *)
    rewrite (U_srliw20 E0 43 _ U43 RCS), U_lit in Hb5 by lia. apply negb_true_iff, Z.eqb_neq in Hb5.
    assert (Hgs : Spa.spa_get_string (Spa.child_at (x_bs x) c) = None).
    { rewrite (reac_role_prop_parse.pb_gs (x_bs x) c ltac:(lia) ltac:(unfold x_len in *; lia)).
      replace (Spa.u32_at (x_bs x) c <? 2 ^ 20) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
      reflexivity. }
    l_run HAE U2 Hio. l_branch HAE Hb8.
    { exfalso. rewrite (U_and3 E0 _ _ Un Un4), U_lit in Hb8 by lia. discriminate Hb8. }
    l_run_to HAE U2 Hio PC_L2.
    eapply (l_exit_L2 x r c regs2 mem2 md2 (l_vals x c) _ _ _ _ 45 (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))
      Hpre HFI HR HSt HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | vm_compute; left; reflexivity
    | l_fixed_tac | l_l2fixed_tac | vm_compute; reflexivity | l_ureg HAE; exact Un | lia | exact Hm4 | lia
    | rewrite HW; apply l_model_next; [lia | lia | lia | exact Hci | exact Hgs]
    | exact HJ | exact Hio | exact KE | exact HNext ]. }
  rewrite (U_srliw20 E0 43 _ U43 RCS), U_lit in Hb5 by lia. apply negb_false_iff, Z.eqb_eq in Hb5.
  assert (H20 : Spa.u32_at (x_bs x) c < 2 ^ 20) by (Z.div_mod_to_equations; lia).
  (* 0x83104 .. 0x83114: the check of s1 + 4; stop at 0x83118 beqz a1 (CS = 0) *)
  l_run HAE U2 Hio. l_branch HAE Hb6.
  { (* CS = 0: 0x83158, the next child *)
    rewrite U_lit, (U_sext32_eqb E0 43 _ 0 U43 RCS ltac:(lia)) in Hb6 by lia. apply Z.eqb_eq in Hb6.
    assert (Hgs : Spa.spa_get_string (Spa.child_at (x_bs x) c) = None).
    { rewrite (reac_role_prop_parse.pb_gs (x_bs x) c ltac:(lia) ltac:(unfold x_len in *; lia)).
      rewrite Hb6. replace (1 <=? 0) with false by reflexivity. rewrite andb_false_r. reflexivity. }
    l_run HAE U2 Hio. l_branch HAE Hb8.
    { exfalso. rewrite (U_and3 E0 _ _ Un Un4), U_lit in Hb8 by lia. discriminate Hb8. }
    l_run_to HAE U2 Hio PC_L2.
    eapply (l_exit_L2 x r c regs2 mem2 md2 (l_vals x c) _ _ _ _ 45 (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))
      Hpre HFI HR HSt HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | vm_compute; left; reflexivity
    | l_fixed_tac | l_l2fixed_tac | vm_compute; reflexivity | l_ureg HAE; exact Un | lia | exact Hm4 | lia
    | rewrite HW; apply l_model_next; [lia | lia | lia | exact Hci | exact Hgs]
    | exact HJ | exact Hio | exact KE | exact HNext ]. }
  rewrite U_lit, (U_sext32_eqb E0 43 _ 0 U43 RCS ltac:(lia)) in Hb6 by lia. apply Z.eqb_neq in Hb6.
  (* stop at 0x83120 bne a0,s4 (type <> String) *)
  l_run HAE U2 Hio. l_branch HAE Hb7.
  { (* type <> 8: 0x83158, the next child *)
    rewrite U20, (U_sext32_eqb E0 44 _ 8 U44 RTY ltac:(lia)) in Hb7. apply negb_true_iff, Z.eqb_neq in Hb7.
    assert (Hgs : Spa.spa_get_string (Spa.child_at (x_bs x) c) = None).
    { rewrite (reac_role_prop_parse.pb_gs (x_bs x) c ltac:(lia) ltac:(unfold x_len in *; lia)).
      rewrite (proj2 (Z.eqb_neq _ _) Hb7), andb_false_r. reflexivity. }
    l_run HAE U2 Hio. l_branch HAE Hb8.
    { exfalso. rewrite (U_and3 E0 _ _ Un Un4), U_lit in Hb8 by lia. discriminate Hb8. }
    l_run_to HAE U2 Hio PC_L2.
    eapply (l_exit_L2 x r c regs2 mem2 md2 (l_vals x c) _ _ _ _ 45 (c + Spa.round_up8 (8 + Spa.u32_at (x_bs x) c))
      Hpre HFI HR HSt HS);
    [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | vm_compute; left; reflexivity
    | l_fixed_tac | l_l2fixed_tac | vm_compute; reflexivity | l_ureg HAE; exact Un | lia | exact Hm4 | lia
    | rewrite HW; apply l_model_next; [lia | lia | lia | exact Hci | exact Hgs]
    | exact HJ | exact Hio | exact KE | exact HNext ]. }
  rewrite U20, (U_sext32_eqb E0 44 _ 8 U44 RTY ltac:(lia)) in Hb7. apply negb_false_iff, Z.eqb_eq in Hb7.
  (* a String child: 0x83124 .. 0x8312c a0 = s1 + 8, a1 = a0 + CS - 1; stop at LB 0x83130 *)
  l_run_to HAE U2 Hio PC_LB.
  eapply (l_exit_LB x r c regs2 mem2 md2 (l_vals x c) _ _ _ _ 45 Hpre HFI HR HSt HS);
  [ vm_compute; reflexivity | vm_compute; reflexivity | exact HAE | lia | vm_compute; left; reflexivity
  | l_fixed_tac | l_l2fixed_tac | vm_compute; reflexivity
  | l_ureg HAE; exact (U_s8 E0 _ U9 U19 ltac:(lia))
  | l_ureg HAE; exact (U_off_of E0 9 _ 8 U9 ltac:(lia))
  | l_ureg HAE; exact (U_last E0 _ _ U9 U43 ltac:(lia) ltac:(lia) ltac:(lia))
  | lia | exact Hc4 | exact Hci | unfold Spa.SPA_POD_MAX_SIZE; lia | exact Hb7 | exact HW
  | exact HJ | exact Hio | exact KE | exact HLB ].
- (* the child's header is not in the body: 0x830cc bltu s7,a2 is taken, a0 = 0 *)
  destruct (l_entryB x r c ko regs2 mem2 md2 Hpre HL2) as [HS SHOK].
  set (E0 := cut_env x regs2 []) in *.
  assert (HAE : env_agree 43 E0 E0) by apply env_agree_refl.
  assert (U2 : bv_unsigned (ew E0 2) = x_F x).
  { subst E0. rewrite (cut_env_reg x regs2 _ 2 2%bv eq_refl), H2. unfold w64.
    apply unsigned_lit_small. unfold x_F, x_sp, FRAME, T_parse_STK, ESTACK in *. lia. }
  assert (U9 : U E0 (SOff 9 0) = x_P x + c) by (apply (U_cut x regs2 [] 9 9%bv); [reflexivity | exact R9 | lia]).
  assert (U21 : U E0 (SOff 21 0) = x_P x + r + 16) by (apply (U_cut x regs2 [] 21 21%bv); [reflexivity | exact R21 | lia]).
  assert (U23 : U E0 (SOff 23 0) = VS - 8) by (apply (U_cut x regs2 [] 23 23%bv); [reflexivity | exact R23 | lia]).
  (* 0x830c0 mv a1,zero; stop at 0x830c4 bltu s1,s5 *)
  l_run HAE U2 Hio. l_branch HAE Hb1.
  { exfalso. rewrite U9, U21 in Hb1. apply Z.ltb_lt in Hb1. lia. }
  (* stop at 0x830cc bltu s7,a2: taken, since c + 8 > r + 16 + VS *)
  l_run HAE U2 Hio. l_branch HAE Hb2.
  2: { exfalso. rewrite U23, (U_subab E0 9 21 _ _ U9 U21 ltac:(lia)) in Hb2. apply Z.ltb_ge in Hb2. lia. }
  (* to 0x832f4: a0 = a1 = 0, the epilogue, stop at the `ret` *)
  l_run HAE U2 Hio.
  eapply (l_leaf0 x regs2 mem2 md2 [] _ _ _ _ 43 Hpre HFI HS eq_refl ltac:(vm_compute; reflexivity) HAE ltac:(lia)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ Hio KE).
  rewrite HW. unfold l2_fuel. rewrite reac_role_prop_parse.walk_res_step, pin_out_c by lia. reflexivity.
Qed.

End b.
