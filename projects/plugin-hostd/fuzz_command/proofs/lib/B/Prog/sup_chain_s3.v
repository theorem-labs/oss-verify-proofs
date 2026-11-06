(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the member loop of sup_chain's image-B walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, a Theorem Labs lane's lib/B/Prog/sup_chain_c.v `tsup_chain_spec`, statement from a Theorem Labs lane f490061c104):
   from the loop head 0x8c3d0 (BASE + SCB_LOOP) to the loop exit 0x8c444 (BASE + SCB_LEXIT), against the interface
   lib/B/Prog/sup_chain_d.v (scb_lctx, scb_inv), in the shape of the ASan walk's lib/A/Prog/sup_chain_s5.v: one pass
   from a loop head with scb_inv k (k < n) to the next head or the exit, and an induction on the passes left.
   B code of one pass (capstone over the pin's .symtab): 0x8c3d0 `bltu s2,s5` (UBSan, refuted: o <= 12k and
   list + 12n + 1 <= 2^64); 0x8c3d8 `beqz s10` picks "%d" (s7) for k = 0 or " %d" (the stack word sp1 + 40); 0x8c3e4
   `bltu s8,a0`, 0x8c3f0 `beqz a0`, 0x8c3f4 `beqz s9` (UBSan, refuted: pids <> 0, pids mod 4 = 0, pids + 4n below
   alloc_ceiling); the load4 check of ids[k] (0x8c3f8 .. 0x8c408, 0x8c430 .. 0x8c438) goes through the token
   machinery with the obligation range_addressable (ids + 4k, 4), so the report 0x8c440 is not reached; 0x8c40c
   `lw a2,0(s3)`, 0x8c410 a0 := list + o, 0x8c414 the sprintf trampoline (the shared contract RtPFCmd.asprintf_sh at
   FR_cmd); then the counters and the back edge 0x8c428 `bne s11,s10`, or 0x8c42c `j 0x8c444`.
   The sprintf contract returns at some FP state fx' (rounding mode 0, f registers kept but f10), so the part after
   the call (scl_post) is stated per FP state and applied at fx'. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16 YM05 YG05 YG0q YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtPFShared RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c xmalloc_c arg_s_c rec_shape_of_c answer_c sup_chain_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_chain_aux sup_chain_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- program points and the symbolic seeds of the loop ---------- *)
Definition SCL_JOIN : Z := AF_sup_chain + 0x21c.   (* 0x8c3e0: ld a0,48(s1), the two format arms meet *)
Definition SCL_RET : Z := AF_sup_chain + 0x254.    (* 0x8c418: the return from the sprintf trampoline *)
(* the format member k is printed with: "%d" 0x21f40 for k = 0, " %d" 0x21f20 otherwise *)
Definition scl_fmtv (k : nat) : Z := if Nat.eqb k 0 then 0x21f40 else 0x21f20.
Definition scl_fmt (k : nat) : list Z := if Nat.eqb k 0 then scb_fmt0 else scb_fmt1.
(* the stack words the pass reads (sp1 = s1 = atom 9): " %d", ids (atom 34), SB (atom 32); the member word ids[k]
   (s3 = atom 19), its 32-bit value atom 33 *)
Definition scl_stk : YP09.region := YP09.mkRegion (Some 9%nat) 40 64 40 40
  [YP09.mkChunk 40 (CVal 8 (SLit 0x21f20)); YP09.mkChunk 48 (CVal 8 (SOff 34 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition scl_mreg : YP09.region := YP09.mkRegion (Some 19%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
(* s8 = ids + 4k lies below 2^47 - 4 (the token obligation's span), SB is atom 32 *)
Definition scl_facts : facts := mkFacts [(24%nat, mkAF 0 140737488355324 0); (32%nat, mkAF SB SB 0)] [] [].
Definition scl_ss (pc : Z) : sstate := mkSS pc sr_atoms [scl_stk; scl_mreg] None scl_facts.
Definition scl_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition scl_Bx : sv := SOff 32 0.
Definition scl_xs (vk pids : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 vk; Z_to_bv 64 pids].

(* ---------- small facts ---------- *)
Lemma scl_lebyte_eq : forall v j, (j < 4)%nat ->
bv_unsigned (nth j (le32 v) (Z_to_bv 8 0)) = le_byte (v mod 2 ^ 32) 4 j.
Proof.
intros v j Hj.
assert (Hv' : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (Heq : Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
pose proof (word_to_le_bytes_nth 4 (v mod 2 ^ 64) j Hj Hv') as Hn. rewrite Heq in Hn.
assert (Hwe : word_to_le_bytes 4 (Z_to_bv 64 v) = le32 v) by reflexivity.
rewrite Hwe in Hn.
remember (le32 v) as L eqn:HL.
assert (Hlen : length L = 4%nat) by (rewrite HL; unfold le32, le4; apply length_Z_to_le_bytes).
assert (HH : nth_error L j = Some (nth j L (Z_to_bv 8 0))) by (apply nth_error_nth'; rewrite Hlen; lia).
rewrite Hn in HH. injection HH as HH. rewrite <- HH.
rewrite Z_to_bv_unsigned. unfold bv_wrap. unfold YO0f.le_byte, le_byte.
change (bv_modulus 8) with 256. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
assert (H64 : (v mod 2 ^ 64) mod 2 ^ 32 = v mod 2 ^ 32)
  by (symmetry; apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]).
assert (H32 : (v mod 2 ^ 32) mod 2 ^ 32 = v mod 2 ^ 32) by (apply Z.mod_mod; lia).
rewrite H64, H32. apply Z.mod_mod. lia.
Qed.

(* the member word's value as the 32-bit load sees it, from the member array's bytes (A's scl_member) *)
Lemma scl_member : forall (rd : reader) pids ids k v,
abytes_atR rd pids (concat (map le32 ids)) -> nth_error ids k = Some v ->
aval_mem rd (pids + 4 * Z.of_nat k) 4 (v mod 2 ^ 32).
Proof.
intros rd pids ids. revert pids.
induction ids as [|x ids IH]; intros pids k v HB0 E; [destruct k; cbn in E; discriminate|].
cbn [map concat] in HB0.
assert (L4 : length (le32 x) = 4%nat) by (unfold le32, le4; apply length_Z_to_le_bytes).
destruct k as [|k]; cbn [nth_error] in E.
- injection E as <-. replace (pids + 4 * Z.of_nat 0) with pids by lia.
  intros j Hj. replace (pids + Z.of_nat j) with (pids + Z.of_nat (j + 0)) by (f_equal; lia).
  rewrite (HB0 (j + 0)%nat) by (rewrite length_app, L4; lia).
  rewrite app_nth1 by (rewrite L4; lia). replace (j + 0)%nat with j by lia.
  rewrite (scl_lebyte_eq x j Hj). reflexivity.
- assert (HB1 : abytes_atR rd (pids + 4) (concat (map le32 ids))).
  { intros i Hi. replace (pids + 4 + Z.of_nat i) with (pids + Z.of_nat (4 + i)) by lia.
    rewrite (HB0 (4 + i)%nat) by (rewrite length_app, L4; cbn [length] in *; lia).
    rewrite app_nth2 by (rewrite L4; lia). rewrite L4. replace (4 + i - 4)%nat with i by lia. reflexivity. }
  replace (pids + 4 * Z.of_nat (S k)) with ((pids + 4) + 4 * Z.of_nat k) by lia.
  exact (IH (pids + 4) k v HB1 E).
Qed.

Lemma scl_concat_len : forall l : list Z, length (concat (map le32 l)) = (4 * length l)%nat.
Proof.
induction l as [|x l IH]; [reflexivity|].
cbn [map concat]. rewrite length_app, IH.
assert (L4 : length (le32 x) = 4%nat) by (unfold le32, le4; apply length_Z_to_le_bytes).
rewrite L4. cbn [length]. lia.
Qed.

Lemma scl_add64 : forall x y, alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
intros x y. rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma scl_swrap32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma scl_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

(* a byte the text clause names, from the value a runtime post gives for it *)
Lemma scl_lit_fmt : forall (rd : reader) f (fmt : list Z),
abytes_atR rd f (PF.pf_bytes fmt ++ [Z_to_bv 8 0]) -> Forall (fun c => 0 <= c < 256) fmt ->
forall i, 0 <= i <= Z.of_nat (length fmt) -> rd (f + i) = Some (nth (Z.to_nat i) (fmt ++ [0]) 0).
Proof.
intros rd f fmt H HF i Hi.
assert (Hl : length (PF.pf_bytes fmt) = length fmt) by (unfold PF.pf_bytes; apply length_map).
replace (f + i) with (f + Z.of_nat (Z.to_nat i)) by lia.
rewrite (H (Z.to_nat i) ltac:(rewrite length_app, Hl; cbn [length]; lia)).
f_equal.
assert (E : PF.pf_bytes fmt ++ [Z_to_bv 8 0] = map (Z_to_bv 8) (fmt ++ [0]))
  by (unfold PF.pf_bytes; rewrite map_app; reflexivity).
rewrite E, (map_nth (Z_to_bv 8) (fmt ++ [0]) 0 (Z.to_nat i)).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
assert (HF' : Forall (fun c => 0 <= c < 256) (fmt ++ [0])) by (apply Forall_app; split; [exact HF | repeat constructor; lia]).
rewrite Forall_forall in HF'.
destruct (Nat.lt_ge_cases (Z.to_nat i) (length (fmt ++ [0]))) as [Hlt | Hge].
- apply HF'. apply nth_In. exact Hlt.
- rewrite nth_overflow by exact Hge. lia.
Qed.

Lemma scl_lw_mod : forall w,
bv_unsigned (sext 64 (bv_extract 0 32 (Z_to_bv 64 w))) mod 2 ^ 32 = w mod 2 ^ 32.
Proof.
intros w. assert (H64 : forall c, (c mod 2 ^ 64) mod 2 ^ 32 = c mod 2 ^ 32)
  by (intros c; symmetry; apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity]).
rewrite b_lw_val. unfold v_lw. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite H64, scl_swrap32_mod, Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact (H64 w).
Qed.

(* the text member k prints: "%d" gives dec v, " %d" a space and dec v *)
Definition scl_T (k : nat) (v : Z) : list Z := if Nat.eqb k 0 then PF.pf_dec v else 32 :: PF.pf_dec v.
Lemma scl_T_facts : forall k v, -2 ^ 31 <= v < 2 ^ 31 ->
PF.pf_bytes (scl_T k v) = (if Nat.eqb k 0 then dec v else SPACE :: dec v) /\
Z.of_nat (length (scl_T k v)) + 1 < 2 ^ 31 - 1 /\ length (PF.pf_bytes (scl_T k v)) = length (scl_T k v).
Proof.
intros k v Hv. pose proof (scb_pf_dec_len v Hv) as HL.
split; [|split; [unfold scl_T; destruct (Nat.eqb k 0); cbn [length]; lia | unfold PF.pf_bytes; apply length_map]].
unfold scl_T. destruct (Nat.eqb k 0); [exact (snt_pf_dec v Hv)|].
change (PF.pf_bytes (32 :: PF.pf_dec v)) with (Z_to_bv 8 32 :: PF.pf_bytes (PF.pf_dec v)).
rewrite (snt_pf_dec v Hv). reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

Definition scl_E (regs : bvmap 5 word) (vk pids : Z) : env := Eimg (Ereg regs (scl_xs vk pids)).

Lemma scl_E_reg : forall regs vk pids m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (scl_E regs vk pids) m = getr regs r.
Proof.
intros regs vk pids m r Hm. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold scl_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm.
Qed.
Lemma scl_E_32 : forall regs vk pids, ew (scl_E regs vk pids) 32 = Z_to_bv 64 SB.
Proof. intros. unfold scl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma scl_E_33 : forall regs vk pids, ew (scl_E regs vk pids) 33 = Z_to_bv 64 vk.
Proof. intros. unfold scl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.
Lemma scl_E_34 : forall regs vk pids, ew (scl_E regs vk pids) 34 = Z_to_bv 64 pids.
Proof. intros. unfold scl_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). Qed.
Lemma scl_E_img : forall regs vk pids, img_env VAL A_LIM (scl_E regs vk pids).
Proof. intros. unfold scl_E. apply Eimg_env. Qed.
Lemma scl_E_agree : forall regs vk pids, env_agree 32 (Ereg regs (scl_xs vk pids)) (scl_E regs vk pids).
Proof. intros. split; [|reflexivity]. intros n Hn. unfold scl_E. apply Eimg_low. unfold A_TEXT. lia. Qed.

(* the bridge from a contract's n-wide read to the symbolic executor's chunk (A's sc_val_mem) *)
Lemma scl_val_mem : forall (W : world SEGS) mem a n v,
aval_mem (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. pose proof (H k Hk) as Hv. unfold aview in Hv.
unfold val_mem.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hv. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.

(* a field read, carried to a memory the reader agrees with on the bytes it names *)
Lemma scl_val_keep : forall (W : world SEGS) (m m' : word -> option byte) a (n : nat) val,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n val -> val_mem SEGS (mrestrict (w_H W) m') a n val.
Proof.
intros W m m' a n val K Hv i Hi.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m m' (a + Z.of_nat i) (K (a + Z.of_nat i) ltac:(lia))).
exact (Hv i Hi).
Qed.

(* a byte of the view is a byte value *)
Lemma scl_view_byte : forall (W : world SEGS) mem a x, rdW W mem a = Some x -> 0 <= x < 256.
Proof.
intros W mem a x H. unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b|]; cbn [option_map] in H; [|discriminate H].
injection H as <-. pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb. exact Hb.
Qed.

(* the text byte sprintf wrote, in the reader form the loop's text clause states *)
Lemma scl_txt_byte : forall (W : world SEGS) mem a (T : list Z) i,
rdW W mem a = Some (nth i (T ++ [0]) 0) ->
rdW W mem a = Some (bv_unsigned (nth i (PF.pf_bytes (T ++ [0])) (Z_to_bv 8 0))).
Proof.
intros W mem a T i H. pose proof (scl_view_byte W mem a _ H) as Hr. rewrite H. f_equal.
unfold PF.pf_bytes. rewrite (map_nth (Z_to_bv 8) (T ++ [0]) 0 i).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. symmetry. apply Z.mod_small. exact Hr.
Qed.

Lemma scl_pres : forall (rg rg' : bvmap 5 word), aregs_preserved rg rg' ->
forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rg' r = getr rg r.
Proof.
intros rg rg' HP r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [lazymatch goal with |- getr _ ?b = _ => let z := eval vm_compute in (bv_unsigned b) in
     exact (HP z ltac:(unfold acallee_saved; lia)) end |]).
destruct Hr.
Qed.

(* ---------- the seeds of the symbolic executor ---------- *)
Section g. Context {fx : YK11.FPState}.
Lemma scl_seed : forall (W : world SEGS) (rg : bvmap 5 word) mm pc sp1 q vk pids,
getr rg 9 = w64 sp1 -> getr rg 19 = w64 q -> getr rg 24 = w64 q ->
0 <= sp1 -> 0 <= q -> q + 4 <= sp1 + 40 -> q <= 140737488355324 -> sp1 + 64 <= 2 ^ 64 ->
0 <= vk < 2 ^ 32 -> 0 <= pids < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mm) (sp1 + 40) 8 0x21f20 ->
val_mem SEGS (mrestrict (w_H W) mm) (sp1 + 48) 8 pids ->
val_mem SEGS (mrestrict (w_H W) mm) (sp1 + 56) 8 SB ->
aval_mem (rdW W mm) q 4 vk ->
st_ok_pi SEGS VAL (scl_E rg vk pids) (scl_ss pc)
  (restrict (w_H W) (mkst rg (Z_to_bv 64 (BASE + pc)) mm (seg_rom SEGS))) /\
sh_ok SEGS scl_Bx [] (scl_E rg vk pids) (mrestrict (w_H W) mm).
Proof.
intros W rg mm pc sp1 q vk pids H9 H19 H24 Hs0 Hq0 Hqs Hqh Hs64 Hvk Hp V40 V48 V56 HV.
set (E := scl_E rg vk pids).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (unfold E; rewrite (scl_E_reg rg vk pids 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (unfold E; rewrite (scl_E_reg rg vk pids 19%nat 19%bv eq_refl); exact H19).
assert (E24 : ew E 24 = Z_to_bv 64 q) by (unfold E; rewrite (scl_E_reg rg vk pids 24%nat 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; apply scl_E_32).
assert (E33 : ew E 33 = Z_to_bv 64 vk) by (unfold E; apply scl_E_33).
assert (E34 : ew E 34 = Z_to_bv 64 pids) by (unfold E; apply scl_E_34).
assert (B9 : base_val E (Some 9%nat) = sp1) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (B19 : base_val E (Some 19%nat) = q) by (cbn [base_val]; rewrite E19; apply unsigned_lit_small; lia).
split; [| unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx. unfold scl_ss. apply pa_entry_st_ok_full.
- unfold E, scl_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold YP09.region_ok, scl_stk.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val SEGS E _ sp1 40 8 (SLit 0x21f20) 0x21f20); [reflexivity | cbn; lia | cbn; lia | exact V40].
    * apply (chunk_ok_val SEGS E _ sp1 48 8 (SOff 34 0) pids);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V48].
    * apply (chunk_ok_val SEGS E _ sp1 56 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; unfold SB; lia | cbn; lia | exact V56].
  + unfold YP09.region_ok, scl_mreg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ q 0 4 (SOff 33 0) vk).
    * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
    * cbn. lia.
    * rewrite Z.add_0_r. change (N.to_nat 4) with 4%nat. exact (scl_val_mem W mm q 4%nat vk HV).
- apply pairwise_disjoint_of_extents.
  unfold scl_stk, scl_mreg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite B9, B19. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold scl_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E24, E32, !unsigned_lit_small by (unfold SB; lia).
  rewrite Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold SB; lia].
Qed.

(* the seed at the return of the sprintf trampoline: the registers only *)
Lemma scl_seed0 : forall (W : world SEGS) (rg : bvmap 5 word) mm pc,
st_ok_pi SEGS VAL (Eimg (Ereg rg [])) (scl_ss0 pc)
  (restrict (w_H W) (mkst rg (Z_to_bv 64 (BASE + pc)) mm (seg_rom SEGS))) /\
sh_ok SEGS scl_Bx [] (Eimg (Ereg rg [])) (mrestrict (w_H W) mm).
Proof.
intros W rg mm pc. split; [| unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx. unfold scl_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.
End g.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's sprintf contract (sup_chain_c.v, a Theorem Labs lane f490061c104), at every FP state *)
Hypothesis ASPRINTF : forall fx0 : YK11.FPState,
  @asprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_sprintf) 0xa6bf8 0x604158.
Hypothesis HB : YF0m.CmdBSyms B.
(* the per-binary image facts, as a Theorem Labs lane's walks take them (sup_reset.v:307-335) *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let cmd_rec_cells : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  aview SEGS (w_H W) mem 0xae455 = Some 1 /\ aguard_ok SEGS W mem 0xa6bf8 0x604158 /\
  exists ev, rd32 (aview SEGS (w_H W) mem) (as_errno B) ev :=
  CmdRecCells.cmd_rec_cells (SK := SK) SEGS B LAWS HB IMG.

(* ---------- the sprintf chain's read-only words ---------- *)
Lemma scl_cr_bnd : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) CMD_SP_CR.
Proof.
apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) cmd_sp_cr_img r Hr) as Hb.
unfold in_cmd_img, CMD_IMG_LO, CMD_IMG_HI in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2, H3. lia.
Qed.
Lemma scl_cr_off : forall x m, off_img x m -> forall r, In r CMD_SP_CR -> zdisjoint r (x, m).
Proof.
intros x m Hx r Hr. pose proof (proj1 (forallb_forall _ _) cmd_sp_cr_img r Hr) as Hb.
unfold in_cmd_img, CMD_IMG_LO, CMD_IMG_HI in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1, H2, H3.
unfold zdisjoint, off_img in *. cbn [fst snd]. lia.
Qed.
Lemma scl_cr_hi : forall x m, 0x606000 <= x -> forall r, In r CMD_SP_CR -> zdisjoint r (x, m).
Proof. intros x m Hx. apply scl_cr_off. unfold off_img. right. exact Hx. Qed.

(* a read-only byte of the image is no byte of a live block *)
Lemma scl_ro_noblk : forall ly S (W : world SEGS) mem md a p n,
AR SEGS B ly S W mem md -> in_roP SEGS RLO RHI a -> In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n).
Proof.
intros ly S W mem md a p n HAR Hro Hin Hr.
destruct (cmd_ro_prog_apart a Hro) as [Himg _].
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
  (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hr))))) Himg).
Qed.

(* a shadow byte of an application address is no byte of a live block *)
Lemma scl_shadow_apart : forall ly S (W : world SEGS) mem md p n x,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= x < kHighMemEnd ->
~ (p <= shadow_of_addr SHADOW_OFF x < p + req_size n).
Proof.
intros ly S W mem md p n x HAR Hin Hx Hr.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
unfold shadow_of_addr, SHADOW_OFF in Hr.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as Hd0.
pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(unfold kHighMemEnd in Hx; lia)) as Hd1.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia.
Qed.

(* ---------- the format the pass prints with, as the shared contract's family takes it ---------- *)
Lemma scl_fmt_at : forall ly S (W0 : world SEGS) mm md (k : nat) rs, AR SEGS B ly S W0 mm md -> cmd_ro_ok (rdW W0 mm) ->
Forall (zdisjoint (scl_fmtv k, Z.of_nat (length (scl_fmt k)) + 1)) rs ->
fmt_at (rdW W0 mm) rs (scl_fmtv k) (scl_fmt k).
Proof.
intros ly S W0 mm md k rs HAR HRO Hrs. unfold scl_fmt, scl_fmtv in *. destruct (Nat.eqb k 0).
- split; [lia|]. split.
  { apply scl_lit_fmt; [rewrite <- scb_fmt0_lit; exact (scb_lit_21f40_at _ HRO) | repeat constructor; lia]. }
  split; [exact Hrs|]. split; [left; unfold kLowMemEnd; cbn; lia|].
  split; [exact (scb_rng_21f40 B HB ly S W0 mm md HAR) | exact (scb_hull_21f40 B HB ly S W0 mm md HAR)].
- split; [lia|]. split.
  { apply scl_lit_fmt; [rewrite <- scb_fmt1_lit; exact (scb_lit_21f20_at _ HRO) | repeat constructor; lia]. }
  split; [exact Hrs|]. split; [left; unfold kLowMemEnd; cbn; lia|].
  split; [exact (scb_rng_21f20 B HB ly S W0 mm md HAR) | exact (scb_hull_21f20 B HB ly S W0 mm md HAR)].
Qed.

Lemma scl_fmt_fam : forall (k : nat) v (rd : reader) rs ws, -2 ^ 31 <= v < 2 ^ 31 ->
fmt_at rd rs (scl_fmtv k) (scl_fmt k) -> pf_args_asan rd rs ws (map arg_of [PF.AInt v]) ->
FR_cmd rd rs (scl_fmtv k) ws (scl_T k v).
Proof.
intros k v rd rs ws Hv Hf Ha.
unfold scl_fmt, scl_fmtv, scl_T in *. destruct (Nat.eqb k 0).
- apply (FR_cmd_intro rd rs 0x21f40 ws (PF.pf_dec v) scb_fmt0 [PF.Pd] [PF.AInt v] Hf scb_fmt0_parse Ha).
  + apply snt_text_d.
  + exact I.
  + vm_compute; reflexivity.
- apply (FR_cmd_intro rd rs 0x21f20 ws (32 :: PF.pf_dec v) scb_fmt1 [PF.PLit 32; PF.Pd] [PF.AInt v] Hf scb_fmt1_parse Ha).
  + apply scb_fmt1_text.
  + exact I.
  + vm_compute; reflexivity.
Qed.

(* ============================================================================================================
   The loop. Its data: the statement's entry (ly SE W regs mem md), the member array (pids, ids), the recorder
   (R, O), the first arrival at the loop head (lyL SL WL memL mdL), the class-1 frame (1, fpos), the text block
   (lst, 12n + 1 bytes), and the entry's FP registers fr0 and fcsr csr0 (sup_chain_d.v scb_fxok). *)
Section loop.
Variables (ly : alayout) (SE : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)).
Variables (lyL : alayout) (SL : astate) (WL : world SEGS) (memL : word -> option byte) (mdL : Model).
Variables (fpos lst : Z) (bl1 Frec O1 : list (Z * Z)) (p1 p2 : Z).
Variables (fr0 : bvmap 5 word) (csr0 : bv 32).
Hypothesis HIDS : (1 <= length ids <= 62)%nat.
Hypothesis HIDR : Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids.
Hypothesis HPNZ : pids <> 0.
Hypothesis HP4 : pids mod 4 = 0.
Hypothesis HPR : 0 <= pids < 2 ^ 64.
Hypothesis HLC : scb_lctx B MT ly SE W regs mem md id pids ids R O lyL SL WL memL mdL fpos lst bl1 Frec O1 p1 p2.

#[local] Notation NN := (Z.of_nat (length ids)).
#[local] Notation SP0 := (spZ regs).
#[local] Notation SP1 := (scb_sp1 (spZ regs)).
#[local] Notation STK := SUP_CHAIN_STK.
#[local] Notation FP := (SCB_FP O).
#[local] Notation KL := (scb_kL R).
#[local] Notation INV := (scb_inv B ly SE W regs mem md pids ids R O lyL SL WL memL fpos lst).

Ltac scl_unlctx :=
  let HL := fresh "HL" in pose proof HLC as HL; cbv zeta beta delta [scb_lctx] in HL;
  destruct HL as (HJL & Hperm0 & HFrecO & _ & _ & HpermL & Happ1 & _ & _ & _ & _ & Hlst & _ & _ & _ & _ & Hwords
    & _ & _ & Hlst0 & HarrL & HraddrL & Hapart & Hceil & HaroL).

Lemma scl_HBLK : In (lst, 12 * NN + 1) (ablocks B lyL SL).
Proof. scl_unlctx. apply (Permutation_in _ (Permutation_sym HpermL)). right. right. left. reflexivity. Qed.

Lemma scl_req : req_size (12 * NN + 1) = 12 * NN + 1.
Proof. unfold req_size. destruct (Z.eqb_spec (12 * NN + 1) 0); lia. Qed.

Lemma scl_bounds :
alloc_ceiling <= SP1 - 3 * ESTACK /\ SP1 + 192 <= SP0 /\ SP0 <= 2 ^ 47 /\ (SP1 - SP0) mod 16 = 0 /\
SP0 - STK <= SP1 - 3 * ESTACK /\ 3 * ESTACK - (SP1 - SP0) <= STK /\ SP0 - 208 <= SP1 /\
4096 <= lst /\ lst + (12 * NN + 1) <= alloc_ceiling /\ pids + 4 * NN <= alloc_ceiling /\
iv_apart pids (4 * NN) lst (12 * NN + 1) /\ ly_stk_lo ly + STK <= SP0.
Proof.
scl_unlctx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJL as (HARL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkok & _ & _).
pose proof Hstkok as (Hal16 & Hstk0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : 208 + 3 * ESTACK <= STK) by (unfold SUP_CHAIN_STK; lia).
destruct (scb_sp1_facts SP0 Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b).
destruct (al_blocks _ _ LAWS lyL SL WL memL mdL lst (12 * NN + 1) HARL scl_HBLK) as (_ & Hb4096 & Hbceil & _).
rewrite scl_req in Hbceil. unfold scb_sp1. unfold ESTACK in *.
repeat match goal with |- _ /\ _ => split end; first [exact Hapart | exact Hsp1b | lia].
Qed.

(* every byte of the text block is one this walk may write: the block is xmalloc's, so it is new since the entry, or
   it is one of the recorder's blocks record()'s spill arm freed, hence in the statement's footprint *)
Lemma scl_awr : forall a, lst <= a < lst + 12 * NN + 1 ->
awr_byte SEGS B STK SP0 FP (ablocks B ly SE) (ablocks B lyL SL) (frames SE) lyL [(1, fpos)] a.
Proof.
intros a Ha. scl_unlctx. pose proof scl_HBLK as HBLK. pose proof scl_req as Hreq.
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}).
{ intros [x1 x2] [y1 y2]. destruct (Z.eq_dec x1 y1) as [E1|E1]; destruct (Z.eq_dec x2 y2) as [E2|E2];
  [left; congruence | right; congruence | right; congruence | right; congruence]. }
destruct (in_dec Hdec (lst, 12 * NN + 1) (ablocks B ly SE)) as [Hin0 | Hnin0].
- apply (Permutation_in _ Hperm0) in Hin0. apply in_app_or in Hin0 as [Hb1 | Hfr].
  + exfalso. rewrite Forall_forall in Happ1. pose proof (Happ1 _ Hb1) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia.
  + right; left. split.
    * exists (lst, lst + req_size (12 * NN + 1)). split.
      -- right. right. unfold ablocks_fp. apply in_map_iff. exists (lst, 12 * NN + 1). split; [reflexivity | apply HFrecO; exact Hfr].
      -- cbn [fst snd]. rewrite Hreq. lia.
    * exists lst, (12 * NN + 1). split; [exact HBLK | rewrite Hreq; lia].
- right; right; left. exists lst, (12 * NN + 1). split; [exact HBLK|]. split; [exact Hnin0 | rewrite Hreq; lia].
Qed.

(* the facts the pass reads, at a memory the invariant relates to the first arrival's *)
Lemma scl_at : forall k rg mm mdd, INV k rg mm mdd ->
AR SEGS B lyL SL WL mm mdd /\
abytes_atR (rdW WL mm) pids (concat (map le32 ids)) /\
range_addressable (rdW WL mm) SHADOW_OFF pids (4 * NN) /\
val_mem SEGS (mrestrict (w_H WL) mm) (SP1 + 40) 8 0x21f20 /\
val_mem SEGS (mrestrict (w_H WL) mm) (SP1 + 48) 8 pids /\
val_mem SEGS (mrestrict (w_H WL) mm) (SP1 + 56) 8 SB /\
arodata_okP SEGS RLO RHI B (rdW WL mm).
Proof.
intros k rg mm mdd HINV.
cbv zeta beta delta [scb_inv] in HINV.
destruct HINV as (_ & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAG).
scl_unlctx. destruct Hwords as (_ & _ & _ & _ & W40 & W48 & W56 & _).
pose proof scl_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
pose proof (proj1 HJL) as HARL. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof scl_HBLK as HBLK. pose proof scl_req as Hreq.
unfold iv_apart in B11. unfold ESTACK in *.
split; [exact (proj1 HJ)|].
split.
{ intros i Hi. pose proof Hi as Hi'. rewrite scl_concat_len in Hi'.
  rewrite (HAG (pids + Z.of_nat i)); [exact (HarrL i Hi) | lia | lia | lia]. }
split.
{ apply (range_addressable_agree (rdW WL memL) (rdW WL mm)); [|exact HraddrL].
  intros x Hx.
  assert (Hsh : 0x7fff8000 <= shadow_of_addr SHADOW_OFF x < 0x7fff8000 + 2 ^ 44).
  { unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  apply HAG.
  - lia.
  - intros Hin. apply (scl_shadow_apart lyL SL WL memL mdL lst (12 * NN + 1) x HARL HBLK ltac:(unfold kHighMemEnd; lia)).
    rewrite Hreq. lia.
  - lia. }
assert (KS : forall x, SP1 + 40 <= x < SP1 + 64 -> aview SEGS (w_H WL) mm x = aview SEGS (w_H WL) memL x)
  by (intros x Hx; apply HAG; lia).
split; [apply (scl_val_keep WL memL mm (SP1 + 40) 8 _); [intros x Hx; apply KS; cbn in Hx; lia | exact W40]|].
split; [apply (scl_val_keep WL memL mm (SP1 + 48) 8 _); [intros x Hx; apply KS; cbn in Hx; lia | exact W48]|].
split; [apply (scl_val_keep WL memL mm (SP1 + 56) 8 _); [intros x Hx; apply KS; cbn in Hx; lia | exact W56]|].
intros a Hro Ho He.
destruct (cmd_ro_prog_apart a Hro) as [Himg _]. pose proof (pa_segs_low a Himg) as Hlo. unfold kLowMemEnd in Hlo.
rewrite (HAG a ltac:(lia)).
- exact (HaroL a Hro Ho He).
- intros Hin. apply (scl_ro_noblk lyL SL WL memL mdL a lst (12 * NN + 1) HARL Hro HBLK). rewrite Hreq. lia.
- lia.
Qed.

(* the invariant at a state the walk reaches without writing and without touching the registers it keeps *)
Lemma scl_inv_move : forall (k : nat) (rg rg' : bvmap 5 word) mm mdd mm' mdd',
INV k rg mm mdd ->
ajournal SEGS B STK SP0 FP ly SE W mem md [(1, fpos)] lyL SL WL mm' mdd' KL ->
(forall a, 0 <= a < 2 ^ 64 -> rdW WL mm' a = rdW WL mm a) ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rg' r = getr rg r) ->
INV k rg' mm' mdd'.
Proof.
intros k rg rg' mm mdd mm' mdd' HINV HJ' K KR.
pose proof scl_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
cbv zeta beta delta [scb_inv] in HINV |- *.
destruct HINV as (Hkle & HJ & Hsp & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & HTXT & HAG).
pose proof (scb_dec_list_prefix_len ids k HIDR Hkle) as HTL.
split; [exact Hkle|]. split; [exact HJ'|].
split; [unfold spZ in *; rewrite (KR 2%bv ltac:(cbn [In]; tauto)); exact Hsp|].
split; [rewrite (KR 3%bv ltac:(cbn [In]; tauto)); exact R3|].
split; [rewrite (KR 4%bv ltac:(cbn [In]; tauto)); exact R4|].
split; [rewrite (KR 8%bv ltac:(cbn [In]; tauto)); exact R8|].
split; [rewrite (KR 9%bv ltac:(cbn [In]; tauto)); exact R9|].
split; [rewrite (KR 18%bv ltac:(cbn [In]; tauto)); exact R18|].
split; [rewrite (KR 19%bv ltac:(cbn [In]; tauto)); exact R19|].
split; [rewrite (KR 20%bv ltac:(cbn [In]; tauto)); exact R20|].
split; [rewrite (KR 21%bv ltac:(cbn [In]; tauto)); exact R21|].
split; [rewrite (KR 22%bv ltac:(cbn [In]; tauto)); exact R22|].
split; [rewrite (KR 23%bv ltac:(cbn [In]; tauto)); exact R23|].
split; [rewrite (KR 24%bv ltac:(cbn [In]; tauto)); exact R24|].
split; [rewrite (KR 25%bv ltac:(cbn [In]; tauto)); exact R25|].
split; [rewrite (KR 26%bv ltac:(cbn [In]; tauto)); exact R26|].
split; [rewrite (KR 27%bv ltac:(cbn [In]; tauto)); exact R27|].
split.
{ intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (K (lst + Z.of_nat i) ltac:(lia)). exact (HTXT i ltac:(rewrite length_app; cbn [length]; lia)). }
intros a Ha Hb Hs. rewrite (K a Ha). exact (HAG a Ha Hb Hs).
Qed.

Ltac scl_md :=
  try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
    let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv end).
(* after a run whose regions write nothing: the memory is the one the run started from *)
Ltac scl_keep K :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict (w_H ?Wx) ?m0) (mrestrict _ ?m1) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wx) m1 a = aview SEGS (w_H Wx) m0 a);
  [ intros a Ha; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros b wlo whi x Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ]
  | clear HFr; try (lazymatch goal with HF : frame_of _ _ m0 m1 |- _ => clear HF end);
    try (lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end) ] end.
Ltac scl_awr_tac :=
  lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the same, composed with what was kept before: the memory against the one the pass started from *)
Ltac scl_keepc K Kold mb :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict (w_H ?Wx) ?m0) (mrestrict _ ?m1) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H Wx) m1 a = aview SEGS (w_H Wx) mb a);
  [ intros a Ha; rewrite <- (Kold a Ha); apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros b wlo whi x Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ]
  | clear HFr; try (lazymatch goal with HF : frame_of _ _ m0 m1 |- _ => clear HF end);
    try (lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end) ] end.
Ltac scl_snp := unfold snp_out; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold zdisjoint; cbn [fst snd].

(* ---------- after the call: the counters, the back edge or the exit ---------- *)
Section post. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma scl_post : forall (k : nat) (t : Z) rg mm mdd (Q : world SEGS -> config -> Prop),
(k < length ids)%nat ->
scb_frm0 fx -> scb_fxok fr0 csr0 fx ->
ajournal SEGS B STK SP0 FP ly SE W mem md [(1, fpos)] lyL SL WL mm mdd KL ->
spZ rg = SP1 -> getr rg 3 = w64 (as_gp B) -> getr rg 4 = w64 (as_tp B) ->
getr rg 8 = w64 SP0 -> getr rg 9 = w64 SP1 ->
getr rg 18 = w64 (2 ^ 64 - 1 - lst) -> getr rg 19 = w64 (pids + 4 * Z.of_nat k) -> getr rg 20 = w64 1 ->
getr rg 21 = w64 (Z.of_nat (length (dec_list (firstn k ids)))) -> getr rg 22 = w64 lst ->
getr rg 23 = w64 0x21f40 -> getr rg 24 = w64 (pids + 4 * Z.of_nat k) -> getr rg 25 = w64 1 ->
getr rg 26 = w64 (Z.of_nat k) -> getr rg 27 = w64 NN -> getr rg 10 = w64 t ->
Z.of_nat (length (dec_list (firstn (S k) ids))) = Z.of_nat (length (dec_list (firstn k ids))) + t ->
abytes_atR (rdW WL mm) lst (dec_list (firstn (S k) ids) ++ [Z_to_bv 8 0]) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lst <= a < lst + 12 * NN + 1) -> ~ (SP1 - 3 * ESTACK <= a < SP1) ->
   rdW WL mm a = rdW WL memL a) ->
(forall (fx' : YK11.FPState) regs' mem' md', scb_frm0 fx' -> scb_fxok fr0 csr0 fx' ->
   INV (S k) regs' mem' md' -> (S k < length ids)%nat ->
   SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LOOP) regs' mem' md') Q) ->
(forall (fx' : YK11.FPState) regs' mem' md', scb_frm0 fx' -> scb_fxok fr0 csr0 fx' ->
   INV (S k) regs' mem' md' -> S k = length ids ->
   SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LEXIT) regs' mem' md') Q) ->
SRr SEGS WL (cfg_at SEGS (BASE + SCL_RET) rg mm mdd) Q.
Proof.
intros k t rg mm mdd Q Hk HFRM HFXOK HJ Hsp R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R10 Hpiece HTXT HAG
  KH KE.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof scl_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (scb_room ids k HIDR Hk) as Hroom.
pose proof (scb_dec_list_prefix_len ids k HIDR ltac:(lia)) as Hok.
destruct (scl_seed0 WL rg mm SCL_RET) as [HS SHOK].
set (E := Eimg (Ereg rg [])) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr rg r).
{ intros m r Hm. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
(* the invariant after this pass, at a state whose memory is this one and whose registers are the counters' *)
assert (MKINV : forall (rg' : bvmap 5 word) (mm' : word -> option byte) (mdd' : Model),
  ajournal SEGS B STK SP0 FP ly SE W mem md [(1, fpos)] lyL SL WL mm' mdd' KL ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW WL mm' a = rdW WL mm a) ->
  getr rg' 2 = getr rg 2 -> getr rg' 3 = getr rg 3 -> getr rg' 4 = getr rg 4 -> getr rg' 8 = getr rg 8 ->
  getr rg' 9 = getr rg 9 -> getr rg' 18 = getr rg 18 -> getr rg' 20 = getr rg 20 -> getr rg' 22 = getr rg 22 ->
  getr rg' 23 = getr rg 23 -> getr rg' 25 = getr rg 25 -> getr rg' 27 = getr rg 27 ->
  getr rg' 19 = w64 (pids + 4 * Z.of_nat (S k)) -> getr rg' 24 = w64 (pids + 4 * Z.of_nat (S k)) ->
  getr rg' 21 = w64 (Z.of_nat (length (dec_list (firstn (S k) ids)))) -> getr rg' 26 = w64 (Z.of_nat (S k)) ->
  INV (S k) rg' mm' mdd').
{ intros rg' mm' mdd' HJ' K' S2 S3 S4 S8 S9 S18 S20 S22 S23 S25 S27 S19 S24 S21 S26.
  cbv zeta beta delta [scb_inv].
  split; [lia|]. split; [exact HJ'|].
  split; [unfold spZ in *; rewrite S2; exact Hsp|].
  split; [rewrite S3; exact R3|]. split; [rewrite S4; exact R4|]. split; [rewrite S8; exact R8|].
  split; [rewrite S9; exact R9|]. split; [rewrite S18; exact R18|]. split; [exact S19|].
  split; [rewrite S20; exact R20|]. split; [exact S21|]. split; [rewrite S22; exact R22|].
  split; [rewrite S23; exact R23|]. split; [exact S24|]. split; [rewrite S25; exact R25|].
  split; [exact S26|]. split; [rewrite S27; exact R27|].
  split.
  { intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (K' (lst + Z.of_nat i) ltac:(lia)). exact (HTXT i ltac:(rewrite length_app; cbn [length]; lia)). }
  intros a Ha Hb Hs. rewrite (K' a Ha). exact (HAG a Ha Hb Hs). }
unfold cfg_at, w64.
(* 0x8c418 .. 0x8c424: the counters, then the back edge 0x8c428 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ apply awr_ok_nil. }
scl_md. scl_keep KEEP1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the back edge: one more member remains *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan SCB_LOOP.
  { apply awr_ok_nil. }
  scl_md. scl_keep KEEP2.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg2 _ ?mm2 _; cfg_model := ?md2 |} _ =>
    apply (KH fx rg2 mm2 md2 HFRM HFXOK) end.
  + apply MKINV.
    * exact HJ.
    * intros a Ha. rewrite (KEEP2 a Ha). exact (KEEP1 a Ha).
    * rewrite P2, (EE 2%nat 2%bv eq_refl). reflexivity.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). reflexivity.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). reflexivity.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). reflexivity.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). reflexivity.
    * rewrite P18, (EE 18%nat 18%bv eq_refl). reflexivity.
    * rewrite P20, (EE 20%nat 20%bv eq_refl). reflexivity.
    * rewrite P22, (EE 22%nat 22%bv eq_refl). reflexivity.
    * rewrite P23, (EE 23%nat 23%bv eq_refl). reflexivity.
    * rewrite P25, (EE 25%nat 25%bv eq_refl). reflexivity.
    * rewrite P27, (EE 27%nat 27%bv eq_refl). reflexivity.
    * rewrite P19, (EE 19%nat 19%bv eq_refl), R19. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite P24, (EE 24%nat 24%bv eq_refl), R24. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite P21, (EE 10%nat 10%bv eq_refl), (EE 21%nat 21%bv eq_refl), R10, R21. unfold w64. rewrite scl_add64.
      f_equal. lia.
    * rewrite P26, (EE 26%nat 26%bv eq_refl), R26. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
  + rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    rewrite !U_SOff in Hc. prreg_norm Hc.
    rewrite (EE 27%nat 27%bv eq_refl), (EE 26%nat 26%bv eq_refl), R27, R26 in Hc.
    unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite !Z.mod_small in Hc by lia. lia.
- (* the fall-through: this was the last member; 0x8c42c j 0x8c444 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan SCB_LEXIT.
  { apply awr_ok_nil. }
  scl_md. scl_keep KEEP2.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg2 _ ?mm2 _; cfg_model := ?md2 |} _ =>
    apply (KE fx rg2 mm2 md2 HFRM HFXOK) end.
  + apply MKINV.
    * exact HJ.
    * intros a Ha. rewrite (KEEP2 a Ha). exact (KEEP1 a Ha).
    * rewrite P2, (EE 2%nat 2%bv eq_refl). reflexivity.
    * rewrite P3, (EE 3%nat 3%bv eq_refl). reflexivity.
    * rewrite P4, (EE 4%nat 4%bv eq_refl). reflexivity.
    * rewrite P8, (EE 8%nat 8%bv eq_refl). reflexivity.
    * rewrite P9, (EE 9%nat 9%bv eq_refl). reflexivity.
    * rewrite P18, (EE 18%nat 18%bv eq_refl). reflexivity.
    * rewrite P20, (EE 20%nat 20%bv eq_refl). reflexivity.
    * rewrite P22, (EE 22%nat 22%bv eq_refl). reflexivity.
    * rewrite P23, (EE 23%nat 23%bv eq_refl). reflexivity.
    * rewrite P25, (EE 25%nat 25%bv eq_refl). reflexivity.
    * rewrite P27, (EE 27%nat 27%bv eq_refl). reflexivity.
    * rewrite P19, (EE 19%nat 19%bv eq_refl), R19. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite P24, (EE 24%nat 24%bv eq_refl), R24. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
    * rewrite P21, (EE 10%nat 10%bv eq_refl), (EE 21%nat 21%bv eq_refl), R10, R21. unfold w64. rewrite scl_add64.
      f_equal. lia.
    * rewrite P26, (EE 26%nat 26%bv eq_refl), R26. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
  + rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    rewrite !U_SOff in Hc. prreg_norm Hc.
    rewrite (EE 27%nat 27%bv eq_refl), (EE 26%nat 26%bv eq_refl), R27, R26 in Hc.
    unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia.
    unfold zcanon, M64 in Hc. rewrite !Z.mod_small in Hc by lia. lia.
Qed.
End post.

(* ---------- one pass: from the format join (0x8c3e0) through the sprintf call; from the loop head ---------- *)
Section pass. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma scl_pass : forall (k : nat) (vk : Z) rg mm mdd (Q : world SEGS -> config -> Prop),
(k < length ids)%nat -> nth_error ids k = Some vk ->
scb_frm0 fx -> scb_fxok fr0 csr0 fx ->
INV k rg mm mdd -> getr rg 11 = w64 (scl_fmtv k) ->
(forall (fx' : YK11.FPState) regs' mem' md', scb_frm0 fx' -> scb_fxok fr0 csr0 fx' ->
   INV (S k) regs' mem' md' -> (S k < length ids)%nat ->
   SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LOOP) regs' mem' md') Q) ->
(forall (fx' : YK11.FPState) regs' mem' md', scb_frm0 fx' -> scb_fxok fr0 csr0 fx' ->
   INV (S k) regs' mem' md' -> S k = length ids ->
   SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LEXIT) regs' mem' md') Q) ->
SRr SEGS WL (cfg_at SEGS (BASE + SCL_JOIN) rg mm mdd) Q.
Proof.
intros k vk rg mm mdd Q Hk Hnth HFRM HFXOK HINV H11 KH KE.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof scl_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (scl_at k rg mm mdd HINV) as (HARm & HARR & HRADDR & V40 & V48 & V56 & HROD).
pose proof HINV as HINV'. cbv zeta beta delta [scb_inv] in HINV'.
destruct HINV' as (Hkle & HJ & Hsp & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & HTXT & HAG).
assert (Hvk : -2 ^ 31 <= vk < 2 ^ 31) by (rewrite Forall_forall in HIDR; apply HIDR; exact (nth_error_In ids k Hnth)).
assert (HW32 : 0 <= vk mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (HV : aval_mem (rdW WL mm) (pids + 4 * Z.of_nat k) 4 (vk mod 2 ^ 32))
  by exact (scl_member (rdW WL mm) pids ids k vk HARR Hnth).
unfold iv_apart in B11.
assert (HSTKv : 3 * ESTACK = 12288) by reflexivity.
destruct (scl_seed WL rg mm SCL_JOIN SP1 (pids + 4 * Z.of_nat k) (vk mod 2 ^ 32) pids R9 R19 R24
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HW32 HPR V40 V48 V56 HV) as [HS SHOK].
set (E := scl_E rg (vk mod 2 ^ 32) pids) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply scl_E_img).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr rg r)
  by (intros m r Hm; unfold E; apply scl_E_reg; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; apply scl_E_32).
assert (E33 : ew E 33 = Z_to_bv 64 (vk mod 2 ^ 32)) by (unfold E; apply scl_E_33).
assert (E34 : ew E 34 = Z_to_bv 64 pids) by (unfold E; apply scl_E_34).
assert (UB : U E scl_Bx = SHADOW_OFF)
  by (unfold scl_Bx; rewrite (scl_U_atom E 32 SB E32 ltac:(unfold SB; lia)); exact SB_SHADOW_OFF).
assert (U24 : U E (SOff 24 0) = pids + 4 * Z.of_nat k)
  by (apply scl_U_atom; [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | lia]).
pose proof (scb_dec_list_prefix_len ids k HIDR ltac:(lia)) as Hok.
pose proof (scb_room ids k HIDR Hk) as Hroom.
destruct (scl_T_facts k vk Hvk) as (HTb & HTl & HTbl).
set (T := scl_T k vk) in *.
assert (Hpiece : Z.of_nat (length (dec_list (firstn (S k) ids))) =
  Z.of_nat (length (dec_list (firstn k ids))) + Z.of_nat (length T)).
{ rewrite (scb_dec_list_step ids k vk Hnth), length_app, <- HTb, HTbl. lia. }
set (ok := Z.of_nat (length (dec_list (firstn k ids)))) in *.
unfold cfg_at, w64.
(* 0x8c3e0 `ld a0,48(s1)`, then the UBSan check 0x8c3e4 `bltu s8,a0`: ids + 4k does not wrap below ids *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ scl_awr_tac. }
scl_md. scl_keep KEEP1.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite U24, (scl_U_atom E 34 pids E34 ltac:(lia)) in Hc. lia. }
clear Hc.
(* 0x8c3e8 .. 0x8c3ec, then the UBSan check 0x8c3f0 `beqz a0`: ids and ids + 4k are both non-null *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ scl_awr_tac. }
scl_md. scl_keepc KEEP2 KEEP1 mm.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
  rewrite !U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite U24, !U_SLit, (scl_U_atom E 20 1 ltac:(rewrite (EE 20%nat 20%bv eq_refl); exact R20) ltac:(lia)) in Hc.
  replace (pids + 4 * Z.of_nat k <? zcanon 1) with false in Hc
    by (symmetry; apply Z.ltb_ge; unfold zcanon, M64; rewrite Z.mod_small by lia; lia).
  vm_compute in Hc. discriminate Hc. }
clear Hc.
(* the UBSan check 0x8c3f4 `beqz s9`: ids is non-null and 4-aligned *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ scl_awr_tac. }
scl_md. scl_keepc KEEP3 KEEP2 mm.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
  rewrite U_SLit, (scl_U_atom E 25 1 ltac:(rewrite (EE 25%nat 25%bv eq_refl); exact R25) ltac:(lia)) in Hc.
  vm_compute in Hc. discriminate Hc. }
clear Hc.
(* 0x8c3f8 .. 0x8c410: the load4 check of ids[k] (token obligation: ids + 4k addressable), the member word, a0 :=
   list + o, and the call of the sprintf trampoline at 0x8c414 *)
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
  assert (HRADDR3 : range_addressable (rdW WL (ms_mem m)) SHADOW_OFF pids (4 * NN)) end.
{ apply (range_addressable_agree (rdW WL mm)); [|exact HRADDR].
  intros x Hx. apply KEEP3. unfold shadow_of_addr, SHADOW_OFF.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ eapply obl_of_range; [exact HRADDR3 | exact UB | rewrite U24; lia | rewrite U24; lia]. }
{ scl_awr_tac. }
scl_md. scl_keepc KEEP4 KEEP3 mm.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rT _ ?mT _; cfg_model := ?dT |} _ =>
  set (regsT := rT) in *; set (memT := mT) in *; set (mdT := dT) in * end.
pose proof (proj1 HJ) as HARc.
assert (Qsp : spZ regsT = SP1) by (unfold spZ in *; rewrite Q2, (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW WL memT)).
{ intros a Hro Ho He. destruct (cmd_ro_prog_apart a Hro) as [Himg _]. pose proof (pa_segs_low a Himg) as Hlo.
  unfold kLowMemEnd in Hlo. rewrite (KEEP4 a ltac:(lia)). exact (HROD a Hro Ho He). }
pose proof (cmd_ro_ok_of_aro lyL SL WL memT mdT HARc HRODc) as HROc.
destruct (cmd_rec_cells lyL SL WL memT mdT HARc) as (_ & [HG1 [cval HG2]] & _).
destruct (al_blocks _ _ LAWS lyL SL WL memT mdT lst (12 * NN + 1) HARc scl_HBLK) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbmax).
rewrite scl_req in Hbceil, Hbapp, Hbpres.
assert (Hoff : off_img lst (12 * NN + 1)) by (rewrite <- scl_req; eapply blk_off_imgP; [exact HARc | exact scl_HBLK]).
unfold off_img in Hoff.
assert (Hd : lst + ok + sp_len T <= lst + 12 * NN + 1) by (unfold sp_len; lia).
assert (Hra : getr regsT 1 = Z_to_bv 64 (BASE + SCL_RET)) by (rewrite Q1; reflexivity).
destruct (ecall_pre_stk_at SEGS B (3 * ESTACK) STK SP0 FP ly SE W mem md [(1, fpos)] lyL SL WL memT mdT KL regsT (SP1 - SP0)
  HJ ltac:(lia) B4 ltac:(lia) ltac:(unfold ESTACK; lia) B6
  ltac:(rewrite Hra; apply ret_ok_codeptr_v; [unfold SCL_RET, AF_sup_chain; lia | reflexivity])
  ltac:(rewrite Q3, (EE 3%nat 3%bv eq_refl); exact R3) ltac:(rewrite Q4, (EE 4%nat 4%bv eq_refl); exact R4))
  as (HPRE1 & HPRE2 & HPRE3).
set (ws := map (argZ regsT) [2; 3; 4; 5; 6; 7] ++ []).
eapply SRr_bind.
{ pose proof (ASPRINTF fx) as HSP. unfold asprintf_realizes, asprintf_sh, sh_asprintf_realizes in HSP.
  apply (HSP lyL SL WL regsT memT mdT (lst + ok) (scl_fmtv k) [] ws T cval); clear HSP.
  - exact HPRE1.
  - unfold CMD_SP_K. exact HPRE2.
  - intros a Ha. apply HPRE3. unfold ascratch_stk. unfold CMD_SP_K in Ha. exact Ha.
  - rewrite Q10, (EE 21%nat 21%bv eq_refl), (EE 22%nat 22%bv eq_refl), R21, R22. unfold w64. rewrite scl_add64.
    f_equal. unfold ok. lia.
  - rewrite Q11, (EE 11%nat 11%bv eq_refl). exact H11.
  - exact (CmdRecImg.cmd_consts_view_sp (SK := SK) SEGS B LAWS HB IMG RLO RHI WL memT HRODc).
  - exact scl_cr_bnd.
  - apply Forall_forall. intros r Hr. unfold snp_out.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply scl_cr_hi; [unfold CMD_SP_K, ESTACK in *; lia | exact Hr].
    + apply scl_cr_off; [unfold off_img, sp_len in *; lia | exact Hr].
  - exact HG1.
  - exact HG2.
  - lia.
  - lia.
  - lia.
  - lia.
  - scl_snp; unfold CMD_SP_K, ESTACK, sp_len in *; lia.
  - scl_snp; unfold CMD_SP_K, ESTACK, sp_len in *; lia.
  - split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
  - cbn [length]. lia.
  - scl_snp; unfold CMD_SP_K, ESTACK, sp_len in *; cbn [length Z.of_nat]; lia.
  - apply scl_fmt_fam; [exact Hvk | |].
    + apply (scl_fmt_at lyL SL WL memT mdT k _ HARc HROc).
      assert (HFL : 0 <= Z.of_nat (length (scl_fmt k)) <= 3) by (unfold scl_fmt; destruct (Nat.eqb k 0); cbn; lia).
      assert (HFV : 0x21f20 <= scl_fmtv k <= 0x21f40) by (unfold scl_fmtv; destruct (Nat.eqb k 0); lia).
      scl_snp; unfold CMD_SP_K, ESTACK, sp_len in *; lia.
    + unfold ws. cbn [map arg_of app pf_args_asan pf_arg_asan]. split; [|exact I]. split; [exact Hvk|].
      unfold argZ. assert (E12 : Z_to_bv 5 (10 + 2) = (12%bv : bv 5)) by (apply bv_eq; reflexivity). rewrite E12.
      rewrite Q12, E33, scl_lw_mod. apply Z.mod_mod. lia.
  - lia.
  - lia.
  - unfold sp_len in *. lia.
  - cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
    apply Forall_cons; [|apply Forall_nil]. unfold zdisjoint. cbn [fst snd]. unfold CMD_SP_K, ESTACK, sp_len in *. lia.
  - intros a Ha. destruct (Hbpres a ltac:(unfold sp_len in *; lia)) as [Hp Hno].
    split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. unfold ESTACK. lia.
  - apply (amem_range_of_block SEGS B LAWS lyL SL WL memT mdT lst (12 * NN + 1)); [exact HARc | exact scl_HBLK | lia |].
    rewrite scl_req. lia.
  - apply (range_addressable_of_block SEGS B LAWS lyL SL WL memT mdT lst (12 * NN + 1)); [exact HARc | exact scl_HBLK | lia |].
    rewrite scl_req. lia.
  - apply (shadow_hull_vis_of_block SEGS B LAWS lyL SL WL memT mdT lst (12 * NN + 1)); [exact HARc | exact scl_HBLK | lia | |].
    + rewrite scl_req. lia.
    + unfold sp_len. lia.
  - unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. unfold sp_len in *. lia.
  - exact HFRM.
  (* a Theorem Labs lane's two premises (RtPFCmd.v:227-228): no argument slot on the stack (xs = []), sp1 below 2^47; the
     destination's slack word: 8 bytes past the text window stay in the band of xmalloc's block (PaLibH.amem8_of_block) *)
  - cbn [length Z.of_nat]. rewrite Qsp. lia.
  - apply (amem8_of_block SEGS B LAWS lyL SL WL memT mdT lst (12 * NN + 1)); [exact HARc | exact scl_HBLK | lia | |].
    + rewrite scl_req. lia.
    + unfold sp_len. lia. }
cbv beta. intros W2 c2 _ (-> & fx' & regs' & mem' & md' & -> & HFR' & HFRM' & HAR' & HP' & Hsame' & H10' & HBYT & HKP & HPRES).
(* the journal goes on: sprintf wrote its scratch window and the text window, a byte of the text block *)
assert (HJ' : ajournal SEGS B STK SP0 FP ly SE W mem md [(1, fpos)] lyL SL WL mem' md' KL).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
  eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK SP0 FP ly SE W mem md [(1, fpos)] lyL SL WL memT mdT KL
    mem' md' (fun a => (lst + ok <= a < lst + ok + sp_len T) \/ (SP1 - 3 * ESTACK <= a < SP1)) SL [(1, fpos)] HJ).
  - intros a Ha Hn. apply HKP; [exact Ha | intros H; apply Hn; left; exact H |].
    unfold CMD_SP_K. rewrite Qsp. intros H; apply Hn; right; exact H.
  - exact HPRES.
  - exact Hsame'.
  - intros a [Ha | Ha]; left.
    + apply scl_awr. unfold sp_len in *. lia.
    + left. lia.
  - exact HAR'.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (lst + ok <= a < lst + ok + sp_len T) -> ~ (SP1 - 3 * ESTACK <= a < SP1) ->
  rdW WL mem' a = rdW WL mm a).
{ intros a Ha Hw Hs. rewrite (HKP a Ha Hw ltac:(unfold CMD_SP_K; rewrite Qsp; exact Hs)). exact (KEEP4 a Ha). }
pose proof (scl_pres regsT regs' HP') as PRS.
replace (raZ regsT) with (BASE + SCL_RET) by (unfold raZ; rewrite Hra; rewrite unsigned_lit_small by (unfold SCL_RET, AF_sup_chain; lia); reflexivity).
apply (@scl_post fx' k (Z.of_nat (length T)) regs' mem' md' Q Hk HFRM' (scb_fxok_step fr0 csr0 fx fx' HFXOK HFR' HFRM') HJ').
- unfold spZ. rewrite (PRS 2%bv ltac:(cbn [In]; tauto)). exact Qsp.
- rewrite (PRS 3%bv ltac:(cbn [In]; tauto)), Q3, (EE 3%nat 3%bv eq_refl). exact R3.
- rewrite (PRS 4%bv ltac:(cbn [In]; tauto)), Q4, (EE 4%nat 4%bv eq_refl). exact R4.
- rewrite (PRS 8%bv ltac:(cbn [In]; tauto)), Q8, (EE 8%nat 8%bv eq_refl). exact R8.
- rewrite (PRS 9%bv ltac:(cbn [In]; tauto)), Q9, (EE 9%nat 9%bv eq_refl). exact R9.
- rewrite (PRS 18%bv ltac:(cbn [In]; tauto)), Q18, (EE 18%nat 18%bv eq_refl). exact R18.
- rewrite (PRS 19%bv ltac:(cbn [In]; tauto)), Q19, (EE 19%nat 19%bv eq_refl). exact R19.
- rewrite (PRS 20%bv ltac:(cbn [In]; tauto)), Q20, (EE 20%nat 20%bv eq_refl). exact R20.
- rewrite (PRS 21%bv ltac:(cbn [In]; tauto)), Q21, (EE 21%nat 21%bv eq_refl). exact R21.
- rewrite (PRS 22%bv ltac:(cbn [In]; tauto)), Q22, (EE 22%nat 22%bv eq_refl). exact R22.
- rewrite (PRS 23%bv ltac:(cbn [In]; tauto)), Q23, (EE 23%nat 23%bv eq_refl). exact R23.
- rewrite (PRS 24%bv ltac:(cbn [In]; tauto)), Q24, (EE 24%nat 24%bv eq_refl). exact R24.
- rewrite (PRS 25%bv ltac:(cbn [In]; tauto)), Q25, (EE 25%nat 25%bv eq_refl). exact R25.
- rewrite (PRS 26%bv ltac:(cbn [In]; tauto)), Q26, (EE 26%nat 26%bv eq_refl). exact R26.
- rewrite (PRS 27%bv ltac:(cbn [In]; tauto)), Q27, (EE 27%nat 27%bv eq_refl). exact R27.
- exact H10'.
- exact Hpiece.
- (* the text: the bytes before the window as before the call, the window as sprintf wrote it *)
  rewrite (scb_dec_list_step ids k vk Hnth), <- HTb, <- app_assoc.
  intros i Hi. rewrite !length_app in Hi. cbn [length] in Hi. rewrite HTbl in Hi.
  destruct (Nat.lt_ge_cases i (length (dec_list (firstn k ids)))) as [Hlt | Hge].
  + rewrite app_nth1 by lia.
    rewrite (KT (lst + Z.of_nat i) ltac:(lia) ltac:(unfold ok; lia) ltac:(unfold ESTACK in *; lia)).
    pose proof (HTXT i ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
    rewrite app_nth1 in Hb by lia. exact Hb.
  + rewrite app_nth2 by lia.
    set (j := (i - length (dec_list (firstn k ids)))%nat).
    replace (lst + Z.of_nat i) with (lst + ok + Z.of_nat j) by (unfold j, ok; lia).
    pose proof (HBYT (Z.of_nat j) ltac:(unfold j, sp_len; lia)) as Hb.
    rewrite Nat2Z.id in Hb. unfold sp_bytes in Hb.
    rewrite (scl_txt_byte WL mem' _ T j Hb). f_equal. f_equal.
    unfold PF.pf_bytes. rewrite map_app. reflexivity.
- (* what the pass left alone *)
  intros a Ha Hb Hs. rewrite (KT a Ha ltac:(unfold sp_len in *; lia) Hs). exact (HAG a Ha Hb Hs).
- exact KH.
- exact KE.
Qed.

Lemma scl_body : forall (k : nat) rg mm mdd (Q : world SEGS -> config -> Prop),
(k < length ids)%nat ->
scb_frm0 fx -> scb_fxok fr0 csr0 fx ->
INV k rg mm mdd ->
(forall (fx' : YK11.FPState) regs' mem' md', scb_frm0 fx' -> scb_fxok fr0 csr0 fx' ->
   INV (S k) regs' mem' md' -> (S k < length ids)%nat ->
   SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LOOP) regs' mem' md') Q) ->
(forall (fx' : YK11.FPState) regs' mem' md', scb_frm0 fx' -> scb_fxok fr0 csr0 fx' ->
   INV (S k) regs' mem' md' -> S k = length ids ->
   SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LEXIT) regs' mem' md') Q) ->
SRr SEGS WL (cfg_at SEGS (BASE + SCB_LOOP) rg mm mdd) Q.
Proof.
intros k rg mm mdd Q Hk HFRM HFXOK HINV KH KE.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof scl_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (scl_at k rg mm mdd HINV) as (HARm & HARR & HRADDR & V40 & V48 & V56 & HROD).
pose proof HINV as HINV'. cbv zeta beta delta [scb_inv] in HINV'.
destruct HINV' as (Hkle & HJ & Hsp & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & HTXT & HAG).
assert (Hex : exists v, nth_error ids k = Some v).
{ destruct (nth_error ids k) as [v|] eqn:Ev; [exists v; reflexivity|]. apply nth_error_None in Ev. lia. }
destruct Hex as [vk Hnth].
assert (Hvk : -2 ^ 31 <= vk < 2 ^ 31) by (rewrite Forall_forall in HIDR; apply HIDR; exact (nth_error_In ids k Hnth)).
assert (HW32 : 0 <= vk mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (HV : aval_mem (rdW WL mm) (pids + 4 * Z.of_nat k) 4 (vk mod 2 ^ 32))
  by exact (scl_member (rdW WL mm) pids ids k vk HARR Hnth).
unfold iv_apart in B11.
assert (HSTKv : 3 * ESTACK = 12288) by reflexivity.
destruct (scl_seed WL rg mm SCB_LOOP SP1 (pids + 4 * Z.of_nat k) (vk mod 2 ^ 32) pids R9 R19 R24
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HW32 HPR V40 V48 V56 HV) as [HS SHOK].
set (E := scl_E rg (vk mod 2 ^ 32) pids) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply scl_E_img).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr rg r)
  by (intros m r Hm; unfold E; apply scl_E_reg; exact Hm).
pose proof (scb_dec_list_prefix_len ids k HIDR ltac:(lia)) as Hok.
set (ok := Z.of_nat (length (dec_list (firstn k ids)))) in *.
unfold cfg_at, w64.
(* 0x8c3d0, the UBSan check `bltu s2,s5`: list + o does not wrap (o <= 12k, list + 12n + 1 <= 2^64) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc.
  rewrite (scl_U_atom E 18 (2 ^ 64 - 1 - lst) ltac:(rewrite (EE 18%nat 18%bv eq_refl); exact R18) ltac:(lia)),
          (scl_U_atom E 21 ok ltac:(rewrite (EE 21%nat 21%bv eq_refl); exact R21) ltac:(lia)) in Hc.
  exact (scb_trap_3d0 lst NN ok ltac:(lia) ltac:(lia) ltac:(lia) Hc). }
clear Hc.
(* 0x8c3d4 `mv a1,s7`, then the format test 0x8c3d8 `beqz s10` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ scl_awr_tac. }
scl_md. scl_keep KEEP1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the first member: the format stays "%d" *)
  assert (Hk0 : k = 0%nat).
  { rewrite branch_eq_U, U_SLit in Hc. apply Z.eqb_eq in Hc.
    rewrite (scl_U_atom E 26 (Z.of_nat k) ltac:(rewrite (EE 26%nat 26%bv eq_refl); exact R26) ltac:(lia)) in Hc.
    unfold zcanon, M64 in Hc. rewrite Z.mod_0_l in Hc by lia. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan SCL_JOIN.
  { scl_awr_tac. }
  scl_md. scl_keepc KEEP2 KEEP1 mm.
  pose proof (regs_kept_of_st_ok_pi E _ _ rg (scl_xs (vk mod 2 ^ 32) pids)
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS (scl_E_agree rg _ pids)
    ltac:(vm_compute; reflexivity)) as KEPT.
  prreg HS (11%bv : bv 5) P11.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg2 _ ?mm2 _; cfg_model := ?md2 |} _ =>
    apply (scl_pass k vk rg2 mm2 md2 Q Hk Hnth HFRM HFXOK) end.
  + apply (scl_inv_move k rg _ mm mdd _ _ HINV HJ); [exact KEEP2 | exact KEPT].
  + rewrite P11, (EE 23%nat 23%bv eq_refl), R23. unfold scl_fmtv. rewrite Hk0. reflexivity.
  + exact KH.
  + exact KE.
- (* a later member: a1 := the stack word " %d" *)
  assert (Hkn0 : k <> 0%nat).
  { rewrite branch_eq_U, U_SLit in Hc. apply Z.eqb_neq in Hc.
    rewrite (scl_U_atom E 26 (Z.of_nat k) ltac:(rewrite (EE 26%nat 26%bv eq_refl); exact R26) ltac:(lia)) in Hc.
    unfold zcanon, M64 in Hc. rewrite Z.mod_0_l in Hc by lia. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan SCL_JOIN.
  { scl_awr_tac. }
  scl_md. scl_keepc KEEP2 KEEP1 mm.
  pose proof (regs_kept_of_st_ok_pi E _ _ rg (scl_xs (vk mod 2 ^ 32) pids)
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS (scl_E_agree rg _ pids)
    ltac:(vm_compute; reflexivity)) as KEPT.
  prreg HS (11%bv : bv 5) P11.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg2 _ ?mm2 _; cfg_model := ?md2 |} _ =>
    apply (scl_pass k vk rg2 mm2 md2 Q Hk Hnth HFRM HFXOK) end.
  + apply (scl_inv_move k rg _ mm mdd _ _ HINV HJ); [exact KEEP2 | exact KEPT].
  + rewrite P11. unfold scl_fmtv, w64. destruct (Nat.eqb_spec k 0) as [Hq | Hq]; [exfalso; exact (Hkn0 Hq) | reflexivity].
  + exact KH.
  + exact KE.
Qed.
End pass.

(* the whole loop, by induction on the passes left (at most 62; no unrolling); each pass may return at another FP
   state, so the induction is over the FP state too *)
Lemma scl_loop_from : forall (j k : nat) (fx : YK11.FPState) rg mm mdd (Q : world SEGS -> config -> Prop),
(k + j = length ids)%nat -> (0 < j)%nat ->
scb_frm0 fx -> scb_fxok fr0 csr0 fx -> INV k rg mm mdd ->
(forall (fx' : YK11.FPState) regs' mem' md', scb_frm0 fx' -> scb_fxok fr0 csr0 fx' ->
   INV (length ids) regs' mem' md' -> SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LEXIT) regs' mem' md') Q) ->
SRr SEGS WL (@cfg_at fx SEGS (BASE + SCB_LOOP) rg mm mdd) Q.
Proof.
induction j as [|j IH]; intros k fx rg mm mdd Q Hkj Hj HFRM HFXOK HINV KE; [lia|].
apply (@scl_body fx k rg mm mdd Q ltac:(lia) HFRM HFXOK HINV).
- intros fx' rg' mm' mdd' HF' HX' HINV' Hlt. exact (IH (S k) fx' rg' mm' mdd' Q ltac:(lia) ltac:(lia) HF' HX' HINV' KE).
- intros fx' rg' mm' mdd' HF' HX' HINV' Heq. apply (KE fx' rg' mm' mdd' HF' HX'). rewrite <- Heq. exact HINV'.
Qed.

(* the loop from its first arrival (scb_inv 0) to the exit (scb_inv n), at any FP state with rounding mode 0 *)
Lemma scb_loop : forall (fx0 : YK11.FPState) regsL (Q : world SEGS -> config -> Prop),
scb_frm0 fx0 -> scb_fxok fr0 csr0 fx0 ->
scb_inv B ly SE W regs mem md pids ids R O lyL SL WL memL fpos lst 0 regsL memL mdL ->
(forall (fx' : YK11.FPState) regs' mem' md', scb_frm0 fx' -> scb_fxok fr0 csr0 fx' ->
   scb_inv B ly SE W regs mem md pids ids R O lyL SL WL memL fpos lst (length ids) regs' mem' md' ->
   SRr SEGS WL (@cfg_at fx' SEGS (BASE + SCB_LEXIT) regs' mem' md') Q) ->
SRr SEGS WL (@cfg_at fx0 SEGS (BASE + SCB_LOOP) regsL memL mdL) Q.
Proof.
intros fx0 regsL Q HF HX HINV KE.
exact (scl_loop_from (length ids) 0 fx0 regsL memL mdL Q ltac:(lia) ltac:(lia) HF HX HINV KE).
Qed.

End loop.
End e.
End f.
End d.

Print Assumptions scb_loop.
