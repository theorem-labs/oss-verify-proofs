(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 254 of its 304 lines of code are new or changed and 362 lines of the source are left out. *)
(* B twin of lib/A/Prog/check_arity_s6.v (a working branch 9c6410fb32e) on image B
   (fuzz_command.asan-ubsan). Relocation plus B's frame: "..." 0x21880 -> 0x218c0 (RO_lit_218c0), the frame region
   112 -> 144 bytes with its write window [0, 8) -> [0, 40) (ca_shape, ca_kept, ca_awr_sh, ca_regs_back_g); B stores
   to 0(sp) .. 0x20(sp) (0x87824 .. 0x87870) and reads them back after each bcmp call (0x878b0 .. 0x878cc), so
   ca_kept keeps the whole 144-byte frame across the call. ca_final_ok comes from check_arity_s3.v (A: s4), so this
   file no longer needs s4. No code is walked here (a site check only), so no UBSan trap site is in its range.

   check_arity's bcmp call step: the four rows (0, 3, 8, 14) whose syntax string the inlined syntax_has scans
   with a call of the bcmp wrapper against the literal "..." (0x218c0, RO_lit_218c0).

   The call itself is NOT walked: its contract is the ABCMP hypothesis the statement already names
   (check_arity_c.v:112, abcmp_realizes, lib/Reusable/YG0d.v), taken through cgif_file_fuzzer's
   aj_bcmp_at (lib/Reusable/YCbq.v:2333), which carries the journal across the call. Nothing of musl or of the
   ASan runtime is walked here.

   One `ca_bcmp_step` per call site: it takes the symbolic state at the wrapper's entry, checks the site by
   computation (ca_call_ok), discharges the contract's premises, and hands the walk back the state after the
   call, the journal, the read-only invariant (ca_lowkept) and the one fact the following `beqz a0` needs: the
   junk atom of a0 is zero exactly when the three bytes at the item equal "..." (ca_eq3, a computation on the
   row's own bytes). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_arity_s1 check_arity_s2 check_arity_s3 check_arity_s5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the literal "..." the wrapper is called with *)
Definition CA_DOTS : Z := 0x218c0.

(* every region of this walk is either the frame (atom 2, inside the 144-byte frame, writable only in its
   first 40 bytes) or a constant range of the image below 2 ^ 40 with no write window *)
Definition ca_shape (r : YP09.region) : bool :=
match YP09.r_base r with
| Some 2%nat => (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 144) && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 40)
| None => (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 2 ^ 40) && (YP09.r_whi r <=? YP09.r_wlo r)
| _ => false
end.

Definition zseq (lo len : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat len)).
Definition hullb (x n : Z) : bool :=
forallb ca_vis_b (zseq (shadow_addr x / 8 * 8) (shadow_addr (x + n - 1) / 8 * 8 + 8 - shadow_addr x / 8 * 8)).

(* the i-th byte of row k's syntax string at the address a, and of "..." *)
Definition ca_sb (row : nat) (a : Z) : Z :=
bv_unsigned (nth (Z.to_nat (a - ca_syn_addr row)) (ca_syn_bytes row) (Z_to_bv 8 0)).
Definition ca_db (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) RO_lit_218c0 (Z_to_bv 8 0)).
Definition ca_eq3 (row : nat) (x : Z) : bool := forallb (fun i => ca_sb row (x + i) =? ca_db i) [0; 1; 2].

(* the state at a call site of the bcmp wrapper, checked by computation *)
Definition ca_nores (o : option sv) : bool := match o with None => true | _ => false end.
Lemma ca_nores_eq : forall o, ca_nores o = true -> o = None.
Proof. intros [a|] H; [discriminate | reflexivity]. Qed.

Definition ca_call_ok (row : nat) (x retk : Z) (kk : nat) (ss : sstate) : bool :=
sv_eqb (sr_get (ss_regs ss) 10) (SLit x) &&
sv_eqb (sr_get (ss_regs ss) 11) (SOff (A_OBJ 19) 0) &&
sv_eqb (sr_get (ss_regs ss) 12) (SLit 3) &&
sv_eqb (sr_get (ss_regs ss) 3) (SOff 3 0) &&
sv_eqb (sr_get (ss_regs ss) 4) (SOff 4 0) &&
sv_eqb (sr_get (ss_regs ss) 2) (SOff 2 0) &&
sv_eqb (sr_get (ss_regs ss) 1) (SOff A_TEXT retk) &&
(0 <=? retk) && (retk <? 2 ^ 40) && (retk mod 2 =? 0) && (A_LIM <=? kk)%nat &&
ca_nores (ss_resv ss) &&
ss_atoms_p (pband kk (kk + 16)) ss &&
regions_wf (ss_mem ss) && no_cdata (ss_mem ss) && mem_atoms_p (pband kk (kk + 16)) (ss_mem ss) &&
forallb ca_shape (ss_mem ss) &&
(ca_syn_addr row <=? x) && (x + 3 <=? ca_syn_addr row + Z.of_nat (length (ca_syn_bytes row))) &&
hullb x 3.

Lemma ca_call_okE : forall row x retk kk ss, ca_call_ok row x retk kk ss = true ->
sr_get (ss_regs ss) 10 = SLit x /\
sr_get (ss_regs ss) 11 = SOff (A_OBJ 19) 0 /\
sr_get (ss_regs ss) 12 = SLit 3 /\
sr_get (ss_regs ss) 3 = SOff 3 0 /\
sr_get (ss_regs ss) 4 = SOff 4 0 /\
sr_get (ss_regs ss) 2 = SOff 2 0 /\
sr_get (ss_regs ss) 1 = SOff A_TEXT retk /\
0 <= retk < 2 ^ 40 /\ retk mod 2 = 0 /\ (A_LIM <= kk)%nat /\
ss_resv ss = None /\
ss_atoms_p (pband kk (kk + 16)) ss = true /\
regions_wf (ss_mem ss) = true /\ no_cdata (ss_mem ss) = true /\
mem_atoms_p (pband kk (kk + 16)) (ss_mem ss) = true /\
forallb ca_shape (ss_mem ss) = true /\
ca_syn_addr row <= x /\ x + 3 <= ca_syn_addr row + Z.of_nat (length (ca_syn_bytes row)) /\
hullb x 3 = true.
Proof.
intros row x retk kk ss H. unfold ca_call_ok in H.
repeat (apply andb_true_iff in H as [H ?]).
repeat split;
 try (apply ca_nores_eq; assumption);
 try (apply sv_eqb_eq; assumption);
 try (apply Z.leb_le; assumption);
 try (apply Z.ltb_lt; assumption);
 try (apply Z.eqb_eq; assumption);
 try (apply Nat.leb_le; assumption);
 try assumption.
Qed.

Lemma zseq_in : forall lo len a, lo <= a < lo + len -> In a (zseq lo len).
Proof.
intros lo len a Ha. unfold zseq. apply in_map_iff. exists (Z.to_nat (a - lo)).
split; [lia|]. apply in_seq. split; [lia|]. cbn [Nat.add]. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).

(* the walk never writes below 2 ^ 40: every read-only fact of the entry holds at every later memory *)
Definition ca_lowkept (W : world SEGS) (m0 m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 40 -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.

Lemma ca_lowkept_refl : forall W m, ca_lowkept W m m.
Proof. intros W m a Ha. reflexivity. Qed.

Lemma ca_abytes_low : forall (W : world SEGS) m0 m a L,
ca_lowkept W m0 m -> 0 <= a -> a + Z.of_nat (length L) <= 2 ^ 40 ->
abytes_atR (aview SEGS (w_H W) m0) a L -> abytes_atR (aview SEGS (w_H W) m) a L.
Proof.
intros W m0 m a L HLK Ha Hl H i Hi. rewrite (HLK (a + Z.of_nat i) ltac:(lia)). exact (H i Hi).
Qed.

Lemma ca_shape_E : forall r, ca_shape r = true ->
(YP09.r_base r = Some 2%nat /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 144 /\ 0 <= YP09.r_wlo r /\ YP09.r_whi r <= 40)
\/ (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 40 /\ YP09.r_whi r <= YP09.r_wlo r).
Proof.
intros r H. unfold ca_shape in H.
destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Hb; try discriminate.
- left. repeat (apply andb_true_iff in H as [H ?]).
  split; [first [exact Hb | reflexivity]|]; repeat split; apply Z.leb_le; assumption.
- right. repeat (apply andb_true_iff in H as [H ?]).
  split; [first [exact Hb | reflexivity]|]; repeat split; apply Z.leb_le; assumption.
Qed.

Lemma ca_shape_wrange : forall E rs a,
forallb ca_shape rs = true -> 2 ^ 40 <= bv_unsigned (ew E 2) -> in_wrange E rs a -> 2 ^ 40 <= a.
Proof.
intros E rs a Hsh Hsp (r & Hin & Hr).
rewrite forallb_forall in Hsh.
destruct (ca_shape_E r (Hsh r Hin)) as [(Hb & Hlo & Hhi & Hwlo & Hwhi) | (Hb & Hlo & Hhi & Hw)];
 rewrite Hb in Hr; cbn [base_val] in Hr; lia.
Qed.

Lemma region_kept_aview_none : forall E (H : word -> bool) (m m2 : word -> option byte) lo hi wlo whi cs,
(forall a, lo <= a < hi -> aview SEGS H m2 a = aview SEGS H m a) -> whi <= wlo ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion None lo hi wlo whi cs).
Proof.
intros E H m m2 lo hi wlo whi cs Hav Hro.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; [|lia].
apply (mbyte_of_aview SEGS). apply Hav. lia.
Qed.

Lemma ca_kept : forall E (W : world SEGS) (m m2 : word -> option byte) rs d,
forallb ca_shape rs = true -> bv_unsigned (ew E 2) = d -> 2 ^ 40 <= d ->
(forall a, (0 <= a < 2 ^ 40 \/ d <= a < d + 144) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
Forall (region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) m2)) rs.
Proof.
intros E W m m2 rs d Hsh Hd Hd40 Hav Hpr. revert Hsh.
induction rs as [|r rs IH]; intros Hsh; [constructor|].
cbn [forallb] in Hsh. apply andb_true_iff in Hsh as [Hr Hs].
constructor; [|exact (IH Hs)].
destruct (ca_shape_E r Hr) as [(Hb & Hlo & Hhi & Hwlo & Hwhi) | (Hb & Hlo & Hhi & Hw)];
 destruct r as [b lo hi wlo whi cs];
 cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *; subst b.
- apply (region_kept_aview E (w_H W) m m2 2%nat d lo hi wlo whi cs Hd); [|exact Hpr].
  intros aa Haa. apply Hav. right. lia.
- apply region_kept_aview_none; [|exact Hw].
  intros aa Haa. apply Hav. left. lia.
Qed.

Lemma ca_lowkept_run : forall E rs (W : world SEGS) m m' m0,
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
forallb ca_shape rs = true -> 2 ^ 40 <= bv_unsigned (ew E 2) ->
ca_lowkept W m0 m -> ca_lowkept W m0 m'.
Proof.
intros E rs W m m' m0 HFR Hsh Hsp HLK a Ha.
rewrite <- (HLK a Ha). apply (aview_eq_of SEGS). apply HFR.
rewrite unsigned_lit_small by lia. intros Hin.
pose proof (ca_shape_wrange E rs a Hsh Hsp Hin). lia.
Qed.

Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Lemma ca_awr_sh : forall E rs sp0 FP bl0 blc fr0 ly own,
forallb ca_shape rs = true -> bv_unsigned (ew E 2) = sp0 - 144 ->
awr_ok SEGS B E rs CHECK_ARITY_STK sp0 FP bl0 blc fr0 ly own.
Proof.
intros E rs. induction rs as [|r rs IH]; intros sp0 FP bl0 blc fr0 ly own Hsh Hsp; [apply awr_ok_nil|].
cbn [forallb] in Hsh. apply andb_true_iff in Hsh as [Hr Hs].
destruct (ca_shape_E r Hr) as [(Hb & Hlo & Hhi & Hwlo & Hwhi) | (Hb & Hlo & Hhi & Hw)].
- eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -144);
  [ exact Hb | rewrite Hsp; lia | unfold CHECK_ARITY_STK, ESTACK; lia | lia
  | exact (IH sp0 FP bl0 blc fr0 ly own Hs Hsp) ].
- apply awr_ok_cons_ro; [lia | exact (IH sp0 FP bl0 blc fr0 ly own Hs Hsp)].
Qed.

Lemma ca_ro_dots : forall rd, cmd_ro_bytes rd -> abytes_atR rd CA_DOTS RO_lit_218c0.
Proof. intros rd H. unfold cmd_ro_bytes in H. unfold CA_DOTS. ca_pick H. Qed.

Lemma ca_dots_len : Z.of_nat (length RO_lit_218c0) = 4.
Proof. vm_compute. reflexivity. Qed.

Lemma ca_hull_of : forall ly S (W : world SEGS) mem md x n,
AR SEGS B ly S W mem md -> hullb x n = true -> shadow_hull_vis (aview SEGS (w_H W) mem) x n.
Proof.
intros ly S W mem md x n HAR Hb s Hs.
apply (ca_shadow_vis B HB ly S W mem md s HAR).
unfold hullb in Hb. rewrite forallb_forall in Hb. apply Hb. apply zseq_in. lia.
Qed.

Lemma ca_dots_addr : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF CA_DOTS 3.
Proof.
intros ly S W mem md HAR a Ha.
pose proof (ca_shadow_byte B HB ly S W mem md CA_DOTS 4 HAR ltac:(vm_compute; reflexivity)
  ltac:(unfold CA_DOTS; lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as HM.
assert (Hc : a = CA_DOTS \/ a = CA_DOTS + 1 \/ a = CA_DOTS + 2) by (unfold CA_DOTS in *; lia).
assert (Hd : a / 8 = CA_DOTS / 8)
  by (destruct Hc as [E1 | [E1 | E1]]; rewrite E1; vm_compute; reflexivity).
assert (Hm8 : a mod 8 < 4)
  by (destruct Hc as [E1 | [E1 | E1]]; rewrite E1; vm_compute; reflexivity).
exists 4. split.
- unfold shadow_of_addr, aview. rewrite Hd, HM. cbn [option_map].
  first [reflexivity | f_equal; vm_compute; reflexivity].
- unfold saddr_ok. right. split; [exact Hm8 | lia].
Qed.

(* the bytes the wrapper compares: the item's three bytes against "...", both read-only *)
Lemma ca_cmp_bytes : forall (W : world SEGS) m0 m row x,
(row < 22)%nat -> cmd_ro_bytes (aview SEGS (w_H W) m0) -> ca_lowkept W m0 m ->
ca_syn_addr row <= x -> x + 3 <= ca_syn_addr row + Z.of_nat (length (ca_syn_bytes row)) ->
((forall i, 0 <= i < 3 -> aview SEGS (w_H W) m (x + i) = aview SEGS (w_H W) m (CA_DOTS + i))
 <-> ca_eq3 row x = true).
Proof.
intros W m0 m row x Hrow HRO HLK Hx1 Hx2.
destruct (ca_syn_bound row Hrow) as (Hsa & _ & Hsb & _).
pose proof ca_dots_len as HL4.
assert (HSYN : abytes_atR (aview SEGS (w_H W) m) (ca_syn_addr row) (ca_syn_bytes row))
 by (apply (ca_abytes_low W m0 m _ _ HLK); [lia | lia | exact (ca_ro_syn _ HRO row Hrow)]).
assert (HDOT : abytes_atR (aview SEGS (w_H W) m) CA_DOTS RO_lit_218c0)
 by (apply (ca_abytes_low W m0 m _ _ HLK); [unfold CA_DOTS; lia | unfold CA_DOTS; lia | exact (ca_ro_dots _ HRO)]).
assert (VX : forall i, 0 <= i < 3 -> aview SEGS (w_H W) m (x + i) = Some (ca_sb row (x + i))).
{ intros i Hi. unfold ca_sb.
  replace (x + i) with (ca_syn_addr row + Z.of_nat (Z.to_nat (x + i - ca_syn_addr row))) at 1 by lia.
  rewrite (HSYN (Z.to_nat (x + i - ca_syn_addr row)) ltac:(lia)). reflexivity. }
assert (VY : forall i, 0 <= i < 3 -> aview SEGS (w_H W) m (CA_DOTS + i) = Some (ca_db i)).
{ intros i Hi. unfold ca_db.
  replace (CA_DOTS + i) with (CA_DOTS + Z.of_nat (Z.to_nat i)) at 1 by lia.
  rewrite (HDOT (Z.to_nat i) ltac:(lia)). reflexivity. }
unfold ca_eq3. cbn [forallb]. split.
- intros H.
  assert (HE : forall i, 0 <= i < 3 -> ca_sb row (x + i) = ca_db i).
  { intros i Hi. pose proof (H i Hi) as Hq. rewrite (VX i Hi), (VY i Hi) in Hq. injection Hq as Hq. exact Hq. }
  rewrite (proj2 (Z.eqb_eq _ _) (HE 0 ltac:(lia))), (proj2 (Z.eqb_eq _ _) (HE 1 ltac:(lia))),
    (proj2 (Z.eqb_eq _ _) (HE 2 ltac:(lia))). reflexivity.
- intros H i Hi.
  apply andb_true_iff in H as [H0 H]. apply andb_true_iff in H as [H1 H].
  apply andb_true_iff in H as [H2 _].
  rewrite (VX i Hi), (VY i Hi). f_equal.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia.
  destruct Hc as [E1 | [E1 | E1]]; rewrite E1;
   [apply Z.eqb_eq; exact H0 | apply Z.eqb_eq; exact H1 | apply Z.eqb_eq; exact H2].
Qed.

Ltac ca_rbg r lit j :=
  replace (Z_to_bv 5 r) with (lit : bv 5) by (apply bv_eq; reflexivity);
  match goal with GR : forall r, getr _ r = sv_denot _ (sr_get _ r) |- _ => rewrite GR end;
  match goal with Hq : sr_get (ss_regs _) lit = SOff ?n 0 |- _ => rewrite Hq;
    match goal with D0 : forall n, sv_denot _ (SOff n 0) = ew _ n |- _ => rewrite D0 end;
    change n with (32 + j)%nat end;
  match goal with EX : forall j, (j < 14)%nat -> ew _ (32 + j) = _ |- _ => rewrite (EX j ltac:(lia)) end;
  reflexivity.

(* ca_regs_back (check_arity_s3.v) at any environment that agrees with the entry's below A_TEXT: after a
   call the walk's environment is a havoc of it at atoms >= A_LIM *)
Lemma ca_regs_back_g : forall (H : word -> bool) E ss ms (regs regs0 : bvmap 5 word) s3v,
st_ok_pi SEGS VAL E ss (restrict H ms) ->
(forall n, (n < A_TEXT)%nat -> ew E n = ew (Eimg (Ereg regs (ca_extra s3v regs0))) n) ->
ca_final_ok (ss_regs ss) = true ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
spZ regs + 144 = spZ regs0 ->
aregs_preserved regs0 (ms_regs ms) /\ getr (ms_regs ms) 1 = getr regs0 1.
Proof.
intros H E ss ms regs regs0 s3v HS AG Hf R3 R4 Hsp.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite (AG n ltac:(unfold A_TEXT; lia)). rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (ca_extra s3v regs0) (Z_to_bv 64 0)).
{ intros j Hj. rewrite (AG (32 + j)%nat ltac:(unfold A_TEXT; lia)).
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (GR : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. exact (st_ok_pi_restrict_reg H E ss ms r HS). }
unfold ca_final_ok in Hf. repeat rewrite andb_true_iff in Hf.
repeat match type of Hf with
| _ /\ _ => let A := fresh "Hq" in destruct Hf as [Hf A]; apply sv_eqb_eq in A
end.
apply sv_eqb_eq in Hf.
assert (D0 : forall n, sv_denot E (SOff n 0) = ew E n).
{ intros n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
split.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 2%bv = _ |- _ => rewrite Hq end.
    cbn [sv_denot]. rewrite (EE 2%nat 2%bv eq_refl). unfold spZ in Hsp. rewrite Hsp. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 3%bv = _ |- _ => rewrite Hq end.
    rewrite D0, (EE 3%nat 3%bv eq_refl). exact R3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 4%bv = _ |- _ => rewrite Hq end.
    rewrite D0, (EE 4%nat 4%bv eq_refl). exact R4.
  + ca_rbg 8 (8%bv : bv 5) 2%nat.
  + ca_rbg 9 (9%bv : bv 5) 3%nat.
  + ca_rbg 18 (18%bv : bv 5) 4%nat.
  + ca_rbg 19 (19%bv : bv 5) 5%nat.
  + ca_rbg 20 (20%bv : bv 5) 6%nat.
  + ca_rbg 21 (21%bv : bv 5) 7%nat.
  + ca_rbg 22 (22%bv : bv 5) 8%nat.
  + ca_rbg 23 (23%bv : bv 5) 9%nat.
  + ca_rbg 24 (24%bv : bv 5) 10%nat.
  + ca_rbg 25 (25%bv : bv 5) 11%nat.
  + ca_rbg 26 (26%bv : bv 5) 12%nat.
  + ca_rbg 27 (27%bv : bv 5) 13%nat.
- rewrite GR. match goal with Hq : sr_get (ss_regs _) 1%bv = _ |- _ => rewrite Hq end.
  rewrite D0. change 33%nat with (32 + 1)%nat. rewrite (EX 1%nat ltac:(lia)). reflexivity.
Qed.

End e.
End f.
End d.
