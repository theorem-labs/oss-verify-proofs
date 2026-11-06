(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88; its helpers rx_reg_atom,
   rx_reg_ext, rx_reg_lit, rx_st_region, rx_chunk_zero, rx_flag0_of, the tactics z5 / z5g / rx_mach / rx_atom / rx_ext /
   rx_lit / rx_run_flag (the flag-store run with aj_flag_store's full argument count) and the shape of its release run
   (the flag pointer word, the flag byte and the 13 save slots as one symbolic state, then SRr_ret_at) are kept with the
   prefix ep_, on reac-pw/fuzz_rate's image A and lib/A/RtPgDcsvDefs.v's code table dc_tbl; the tail walk of
   reac_rate_drivable_csv below is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgDcsvEpi.v at 693242f63d54 for image B
   (fuzz_rate.asan-ubsan): the walk is image B's tail, on lib/AU/RtPgDcsvDefsB.v and lib/AU/RtPgStepsB.v; its pcs,
   cells and registers are image B's (buflen R+24, buf R+32, tmp R+48, F R+8 / R+16, the frame's shadow address in
   s2, copy in s3, buf in s4); F is an env atom of run C read from the cell R+8 (image B keeps it in no register);
   run B reads the cell R+32 and carries the range facts 0 < buf and 0 < buf + copy and the cond fact
   buf <= buf + copy, so the engine steps over the three B-only trap branches 0x845ac / 0x845c0 / 0x845c8. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): PART 3 of the walk of
   reac_rate_drivable_csv (0x842d8, 1056 bytes, 264 instructions), from the tail 0x8457c to the `ret` at 0x846e4.
   Proves lib/AU/RtPgDcsvDefsB.v dc_epi_stmt (kind: segment lemma; proves no function by itself).

   THE CODE (RtPgDcsvDefsB.v's header, PART 3), in the runs this file makes:
     run A   0x8457c ld a0,24(s1) (n = buflen); stop at 0x84580 beqz a0,0x845e4: SPLIT.
             n = 0: the branch to 0x845e4 (no byte of buf is written).
             n > 0: 0x84584 addi a0,a0,-1; 0x84588 mv s3,s5; stop at 0x8458c bltu s5,a0: SPLIT, so that
             copy = len (taken) or copy = n - 1 (not taken), copy = min(len, n - 1) both ways; then 0x84594 ..
             0x845a0 ld s4,32(s1) (buf), mv a0,s4, ld a1,48(s1) (tmp = F + 32), mv a2,s3; 0x845a4 jal __asan_memcpy.
     call    __asan_memcpy(buf, tmp, copy) at 0x518b8, ra 0x845a8 (RtPgStepsB.v rtsb_intrin_at).
     run B1  0x845a8 add a0,s4,s3; stop at 0x845ac, where a0 = buf + copy is pinned to the env atom 33 and the
             cond fact buf <= buf + copy (RtPgStepsB.v rtb_geu_lit, YP06.v st_ok_add_cond_neg) is added.
     run B2  the three trap branches to the `unimp` 0x846e8, each NOT taken and each decided by the engine alone:
             0x845ac bltu a0,s4 by the cond fact (buf + copy < buf would need a wrap); 0x845b0 .. 0x845c0 ld a1,32(s1),
             snez a1,a1, seqz a2,a0, xor a1,a1,a2, beqz a1 by the atom ranges 1 <= buf and 1 <= buf + copy (snez
             gives 1, seqz gives 0, the xor 1); 0x845c4 / 0x845c8 ld a1,32(s1), beqz a1 by the range 1 <= buf. Then
             0x845cc .. 0x845dc the instrumented check of the 1-byte store at a0 (srli; ld 88(s1) = the shadow
             offset; add; lb; bnez a1,0x846ec with the slow block 0x846ec andi a2,a0,7 / 0x846f0 blt a2,a1,0x845e0),
             through the kernel's token engine with the shadow entry mkSHE 33 0 1 (its shent_ok from the contract's
             range_addressable buf n, copy <= n - 1); 0x845e0 sb zero,0(a0), the NUL; stop at 0x845e4.
     run C   0x845e4 .. 0x845f4 tmp's four shadow bytes := 0xf8; 0x845f8 .. 0x84604 the retirement word at F + 0
             (0x84600 ld a1,8(s1) = F); 0x84608 ld a0,16(s1) (F) and 0x8460c beqz a0 decided NOT taken (F >= 4096),
             so the arm 0x84664 .. 0x846a0 is never stepped; 0x84610 mv a1,a0; 0x84614 .. 0x84654 the frame's 16
             shadow bytes := 0xf5; 0x84658 ld a0,120(a1) (the flag pointer) and 0x8465c sb zero,0(a0): the release
             of the frame (YCbq.v aj_flag_store, which drops (1, pos) from the journal's own list and moves the
             state to stack_free_state 1 pos S1); 0x84660 j 0x846a4; 0x846a4 mv a0,s5 (len); 0x846a8 .. 0x846e0 the
             13 restores; stop at 0x846e4 `ret` (SRr_ret_at).
   WHY NO ERROR PATH IS REACHED: the only instrumented check of this part is the store check of run B2, which the
   token engine decides from the shadow entry (the jal at 0x846f4 is never stepped).
   WHY NO TRAP IS REACHED: the three branches to 0x846e8 are decided from the facts of run B's state: 0 < buf and
   buf + n <= 2^63 (the contract's n > 0 arm) and copy <= n - 1. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0s YF0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB RtPgDcsvDefsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Definition DC_EPI_C : Z := 0x845e4.       (* the join of the two buflen arms; run C starts here *)
Definition DC_EPI_B2 : Z := 0x845ac.      (* after `add a0,s4,s3`: a0 = buf + copy is pinned here *)

(* ======================================= generic lemmas ======================================= *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a register the run did not touch, or a literal, or an extra atom [RPgX01.v rx_reg_atom / rx_reg_lit / rx_reg_ext] *)
Lemma ep_reg_atom : forall segs E ss ms H regs extra (r r' : bv 5) (n : nat),
st_ok segs E ss (restrict H ms) -> E = Ereg regs extra -> sr_get (ss_regs ss) r = SOff n 0 ->
Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros segs E ss ms H regs extra r r' n HS -> Hg Hn. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat regs extra n r' Hn).
Qed.
Lemma ep_reg_ext : forall segs E ss ms H regs extra (r : bv 5) (j : nat),
st_ok segs E ss (restrict H ms) -> E = Ereg regs extra -> sr_get (ss_regs ss) r = SOff (32 + j) 0 ->
getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros segs E ss ms H regs extra r j HS -> Hg. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_extra regs extra j).
Qed.
(* the same after a token run that set two fresh atoms k and k + 1 (the env as aj_run_to_tok leaves it) *)
Lemma ep_reg_atom2 : forall segs regs extra k w w0 ss ms H (r r' : bv 5) (n : nat),
st_ok segs (ewset (ewset (Ereg regs extra) k w) (Datatypes.S k) w0) ss (restrict H ms) ->
sr_get (ss_regs ss) r = SOff n 0 -> (n < k)%nat -> Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros segs regs extra k w w0 ss ms H r r' n HS Hg HK Hn. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite !ew_ewset_other by lia.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat regs extra n r' Hn).
Qed.
(* a region of the symbolic state is ok for the machine's memory, and the byte a chunk of literal 0 shows
   [RPgX01.v rx_st_region / rx_chunk_zero / rx_flag0_of] *)
Lemma ep_st_region : forall segs E ss ms r, st_ok segs E ss ms -> In r (ss_mem ss) -> region_ok segs E (ms_mem ms) r.
Proof.
intros segs E ss ms r (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _) Hin.
exact (proj1 (Forall_forall _ _) Hok r Hin).
Qed.
Lemma ep_chunk_zero : forall segs E m base off n,
YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal n (SLit 0))) -> (1 <= n)%N ->
mbyte segs m (base + off) = Some (Z_to_bv 8 0).
Proof.
intros segs E m base off n Hc Hn. destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hm, Hb. rewrite !Z.add_0_r in Hm. rewrite Hm. injection Hb as <-.
first [reflexivity | f_equal; vm_compute; reflexivity].
Qed.
Lemma ep_byte0_of : forall segs E ss ms (n : nat) lo hi wlo whi,
st_ok segs E ss ms -> In (YP09.mkRegion (Some n) lo hi wlo whi [YP09.mkChunk 0 (CVal 1 (SLit 0))]) (ss_mem ss) ->
mbyte segs (ms_mem ms) (bv_unsigned (ew E n)) = Some (Z_to_bv 8 0).
Proof.
intros segs E ss ms n lo hi wlo whi HS Hin. pose proof (ep_st_region segs E ss ms _ HS Hin) as (_ & _ & _ & Hc).
cbn [YP09.r_chunks YP09.r_base base_val] in Hc. inversion Hc as [|c l Hc0 _]; subst.
rewrite <- (Z.add_0_r (bv_unsigned (ew E n))). exact (ep_chunk_zero segs E _ _ 0 1 Hc0 ltac:(lia)).
Qed.
(* the owned bytes of a state are owned at a state with the same chunks and fewer frames *)
Lemma ep_aowned_sub : forall B ly S S' a, st_chunks S' = st_chunks S ->
(forall cp, In cp (frames S) -> In cp (frames S')) -> aowned B ly S' a -> aowned B ly S a.
Proof.
intros B ly S S' a Ech Hfr [OWN NC].
assert (SE : sec_extents ly S' = sec_extents ly S) by (unfold sec_extents; rewrite Ech; reflexivity).
split.
- rewrite <- SE. exact OWN.
- intros [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)]; apply NC.
  + left. exists k. rewrite Ech. auto.
  + right. exists cp. auto.
Qed.
(* one byte as aview shows it and as val_mem / garr8 state it *)
Lemma ep_le_byte1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. exact Hv.
Qed.
Lemma ep_aview_val1 : forall segs H (m : word -> option byte) a v,
aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros segs H m a v Hv. apply aview_byte in Hv as (b & Hb & Hv & Hr).
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hb. f_equal.
rewrite ep_le_byte1 by exact Hr. subst v. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ep_val1_aview : forall segs H (m : word -> option byte) a v,
val_mem segs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview segs H m a = Some v.
Proof.
intros segs H m a v Hm Hv. unfold aview. specialize (Hm 0%nat ltac:(lia)).
change (Z.of_nat 0) with 0 in Hm. rewrite Z.add_0_r in Hm. rewrite Hm. cbn [option_map]. f_equal.
rewrite ep_le_byte1 by exact Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. exact Hv.
Qed.
Lemma ep_garr8_aview : forall segs H (m : word -> option byte) base l, garr8 segs (mrestrict H m) base l ->
forall j, (j < length l)%nat -> aview segs H m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros segs H m base l Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. exact (ep_val1_aview segs H m _ _ Hv Hr).
Qed.
Lemma ep_aview_garr8 : forall segs H (m : word -> option byte) base l,
(forall j, (j < length l)%nat -> aview segs H m (base + Z.of_nat j) = Some (nth j l 0)) ->
garr8 segs (mrestrict H m) base l.
Proof.
intros segs H m base l Ha j Hj. pose proof (Ha j Hj) as Hv. split; [exact (ep_aview_val1 segs H m _ _ Hv)|].
apply aview_byte in Hv as (b & _ & -> & Hr). exact Hr.
Qed.
(* range_addressable and the shadow hull read only shadow bytes *)
Lemma ep_ra_kept : forall (rd rd' : Z -> option Z) Bz a n,
(forall x, a <= x < a + n -> rd' (shadow_of_addr Bz x) = rd (shadow_of_addr Bz x)) ->
range_addressable rd Bz a n -> range_addressable rd' Bz a n.
Proof.
intros rd rd' Bz a n Hk H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. rewrite (Hk x Hx). auto.
Qed.
Lemma ep_hull_sub : forall (rd : Z -> option Z) x n n', 0 < n' <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn H s Hs. apply H. split; [lia|].
pose proof (shadow_mono (x + n' - 1) (x + n - 1) ltac:(lia)) as M.
assert (shadow_addr (x + n' - 1) / 8 * 8 <= shadow_addr (x + n - 1) / 8 * 8)
  by (apply Z.mul_le_mono_nonneg_r; [lia | apply Z.div_le_mono; lia]).
lia.
Qed.
Lemma ep_cut_len : forall L n, 1 <= n -> (length (RateCsv.csv_cut L n ++ [0%Z]) <= Z.to_nat n)%nat.
Proof. intros L n Hn. rewrite length_app, (RateCsv.csv_cut_length L n Hn). cbn [length]. lia. Qed.
Lemma ep_nth_firstn : forall (l : list Z) i k, (i < k)%nat -> nth i (firstn k l) 0 = nth i l 0.
Proof.
induction l as [|x l IH]; intros i k Hik.
- rewrite firstn_nil. reflexivity.
- destruct k as [|k]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
(* an 8-byte cell holds a value as it holds the value mod 2^64 *)
Lemma ep_val_mod : forall segs (m : word -> option byte) a v, val_mem segs m a 8 v -> val_mem segs m a 8 (v mod 2 ^ 64).
Proof.
intros segs m a v Hv k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold YO0f.le_byte.
change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.
End h.

(* ======================================= tactics ======================================= *)
(* a register index as the numeral the kit's texts write [RPgX01.v z5 / z5g] *)
Ltac ep_z5 H := repeat match type of H with context [Z_to_bv 5 ?k] =>
  replace (Z_to_bv 5 k) with (@BV 5 k I) in H by (apply bv_eq; reflexivity) end.
Ltac ep_z5g := repeat match goal with |- context [Z_to_bv 5 ?k] =>
  replace (Z_to_bv 5 k) with (@BV 5 k I) by (apply bv_eq; reflexivity) end.
Ltac ep_mach HS m := lazymatch type of HS with st_ok _ _ _ (restrict _ ?x) => rename x into m end.
(* the value of a register after a run, from the symbolic state [RPgX01.v rx_atom / rx_ext] *)
Ltac ep_atom HS r r' H :=
lazymatch type of HS with st_ok ?segs (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
assert (H : getr (ms_regs ms) r = getr rg r')
  by (apply (ep_reg_atom segs (Ereg rg ex) ss ms Hh rg ex r r' n HS eq_refl); vm_compute; reflexivity) end end.
Ltac ep_ext HS r H :=
lazymatch type of HS with st_ok ?segs (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
let j := eval vm_compute in (n - 32)%nat in
assert (H : getr (ms_regs ms) r = nth j ex (Z_to_bv 64 0))
  by (apply (ep_reg_ext segs (Ereg rg ex) ss ms Hh rg ex r j HS eq_refl); vm_compute; reflexivity) end end.
Ltac ep_atom2 HS r r' H :=
lazymatch type of HS with st_ok ?segs (ewset (ewset (Ereg ?rg ?ex) ?k ?w) _ ?w0) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
assert (H : getr (ms_regs ms) r = getr rg r')
  by (apply (ep_reg_atom2 segs rg ex k w w0 ss ms Hh r r' n HS); first [lia | vm_compute; reflexivity]) end end.
(* the projections of a cut's record, after a part lemma is applied to an explicit DCx *)
Ltac ep_dx := unfold dx_R, dx_S0;
  cbn [dx_STK dx_sp0 dx_FP dx_ly dx_S dx_W0 dx_mem0 dx_md0 dx_own dx_k dx_lyc dx_Sc dx_W dx_memc dx_mdc
       dx_regs dx_mask dx_buf dx_n].
(* the flag-store run (YCbq.v aj_flag_store) with its sixteen journal arguments [RPgX01.v rx_run_flag] *)
Ltac ep_run_flag HS HJ HL Hsegs ML Hwx HASF FFL :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_runN segs dc_tbl FUEL ss) in
lazymatch r with (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs dc_tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
eapply (aj_flag_store segs _ HL Hsegs ML dc_tbl dc_tbl_ok Hwx HASF FFL W FUEL E ss ss' st ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ] end end.

(* ======================================= run C's symbolic state =======================================
   At 0x845e4: s2 = shF (atom 18), s1 = R (atom 9), s0 = S (atom 8), s5 = len (atom 21); env atom 32 = the flag
   address; atoms 33 + j = the j-th register the prologue saved (ra, s0 .. s11); atom 46 = F (no register holds it
   here: the code reads it from the cells R + 8 and R + 16). Regions: the frame's 16 shadow bytes (written), the
   frame with its retirement word written and its flag pointer word at F + 120, the cells R + 8 and R + 16 (F),
   the flag byte (written), and the 13 save slots at S - 8 - 8 j. *)
Definition ep_svch : list YP09.chunk :=
map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + Nat.succ j) 0))) (seq 0 13).
Definition ep_rC : smem :=
[ YP09.mkRegion (Some 18%nat) 0 16 0 16 [];
  YP09.mkRegion (Some 46%nat) 0 128 0 8 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 46 0)); YP09.mkChunk 16 (CVal 8 (SOff 46 0))];
  YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0 ep_svch ].
Definition ep_GC : facts := mkFacts [(46%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition ep_ssC : sstate := mkSS DC_EPI_C sr_atoms ep_rC None ep_GC.
Definition ep_XC (fl F : Z) (regs : bvmap 5 word) : list word :=
Z_to_bv 64 fl :: map (fun r => getr regs r) dc_saved ++ [Z_to_bv 64 F].

(* ======================================= run A's symbolic state =======================================
   At 0x8457c: s1 = R (atom 9), s5 = len (atom 21, 0 <= len <= 17); env atom 32 = K, 33 = buf, 34 = n (0 <= n <= 23),
   35 = F (4096 <= F <= 2^47). One read-only region: the cells R + 8 and R + 16 (F), R + 24 (n), R + 32 (buf),
   R + 48 (tmp = F + 32) and R + 88 (K). *)
Definition ep_rA : smem :=
[ YP09.mkRegion (Some 9%nat) 8 96 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 35 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
     YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
     YP09.mkChunk 48 (CVal 8 (SOff 35 32)); YP09.mkChunk 88 (CVal 8 (SOff 32 0))] ].
Definition ep_GA : facts := mkFacts [(34%nat, mkAF 0 23 0); (21%nat, mkAF 0 17 0); (35%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition ep_ssA : sstate := mkSS DC_TAIL sr_atoms ep_rA None ep_GA.
Definition ep_XA (buf n F : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 buf; Z_to_bv 64 n; Z_to_bv 64 F].

(* ======================================= run B's symbolic state =======================================
   At 0x845a8 (the memcpy's return): s1 = R (atom 9), s3 = copy (atom 19), s4 = buf (atom 20, 1 <= buf < 2^47);
   env atom 32 = the runtime's shadow offset K (the cell R + 88 holds it), atom 33 = buf + copy (1 <= buf + copy <
   2^47). Regions: the cells R + 32 (buf, which the trap tests read) and R + 88, and the one byte at buf + copy
   (written by the NUL). The token engine's shadow entry: the byte at atom 33 is addressable. The bounds are
   closed numerals, so the engine decides the snez / seqz / beqz of the trap tests over sv_range. *)
Definition ep_Bx : sv := SOff 32 0.
Definition ep_Bspan : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
Definition ep_SH : list shent := [mkSHE 33 0 1].
Definition ep_rB : smem :=
[ YP09.mkRegion (Some 9%nat) 32 96 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 20 0)); YP09.mkChunk 88 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 33%nat) 0 1 0 1 [] ].
Definition ep_GB : facts :=
mkFacts [(32%nat, mkAF 0x7fff8000 0x7fff8000 0); (33%nat, mkAF 1 (2 ^ 47 - 1) 0); (20%nat, mkAF 1 (2 ^ 47 - 1) 0)] [] [].
Definition ep_ssB : sstate := mkSS DC_RA_CPY2 sr_atoms ep_rB None ep_GB.
Definition ep_XB (dc : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 dc].

(* ======================================= the part ======================================= *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis RT : dc_rt B MT.

(* ---- run C: from the join 0x845e4 to the `ret`, into the post ---- *)
Lemma dc_tailC : forall (c : dcx) (fq : YK11.FPState) pos S1 W1 regs3 mem3 md3,
dc_pre (fx := fx) B c -> rt_fxk [10] fx fq ->
ajournal rsegs B (dx_STK c) (dx_sp0 c) (dx_FP c) (dx_ly c) (dx_S c) (dx_W0 c) (dx_mem0 c) (dx_md0 c)
  ((DC_CID, pos) :: dx_own c) (dx_lyc c) S1 W1 mem3 md3 (dx_k c) ->
frames S1 = (DC_CID, pos) :: frames (dx_Sc c) -> ~ In (DC_CID, pos) (frames (dx_Sc c)) ->
(exists f, S1 = set_fs f (dx_Sc c)) -> 0 <= pos < fs_frames DC_CID ->
same_io (dx_mdc c) md3 ->
dx_R c mod 32 = 0 -> dx_S0 c - 240 <= dx_R c <= dx_S0 c - 224 ->
getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
getr regs3 8 = w64 (dx_S0 c) -> getr regs3 9 = w64 (dx_R c) ->
getr regs3 18 = w64 (shadow_addr (frame_addr (dx_lyc c) DC_CID pos)) ->
getr regs3 21 = w64 (Z.of_nat (length (RateCsv.csv_list (dx_mask c)))) ->
val_mem rsegs (mrestrict (w_H W1) mem3) (dx_R c + 8) 8 (frame_addr (dx_lyc c) DC_CID pos) ->
val_mem rsegs (mrestrict (w_H W1) mem3) (dx_R c + 16) 8 (frame_addr (dx_lyc c) DC_CID pos) ->
(forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W1) mem3) (dx_S0 c - 8 - 8 * Z.of_nat j) 8
   (bv_unsigned (getr (dx_regs c) (nth j dc_saved 0%bv)))) ->
rdword (aview rsegs (w_H W1) mem3) (frame_addr (dx_lyc c) DC_CID pos + DC_FSZ - 8) =
  Some (flag_addr (dx_lyc c) DC_CID pos) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dx_S0 c - T_dcsv_STK <= a < dx_S0 c) ->
   ~ (aowned B (dx_lyc c) (dx_Sc c) a \/ (0 < dx_n c /\ dx_buf c <= a < dx_buf c + dx_n c)) ->
   aview rsegs (w_H W1) mem3 a = aview rsegs (w_H (dx_W c)) (dx_memc c) a) ->
(0 < dx_n c -> garr8 rsegs (mrestrict (w_H W1) mem3) (dx_buf c)
   (RateCsv.csv_cut (RateCsv.csv_list (dx_mask c)) (dx_n c) ++ [0])) ->
SRr rsegs W1 (@cfg_at fq rsegs DC_EPI_C regs3 mem3 md3) (dc_post (fx := fx) B MT c).
Proof.
intros c fq pos S1 W1 regs3 mem3 md3 HPRE Hfxk HJ Hfrs Hnin Hsetf Hpos Hio HRal HRb
  R3 R4 R8 R9 R18 R21 C8 C16 HSV HFW HK HRES.
pose proof RT as (HL & ML & _ & FFL & ASF & _ & MTL & MFS & _).
destruct c as [STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n].
unfold dc_pre, dx_R, dx_S0 in *.
cbn [dx_STK dx_sp0 dx_FP dx_ly dx_S dx_W0 dx_mem0 dx_md0 dx_own dx_k dx_lyc dx_Sc dx_W dx_memc dx_mdc
     dx_regs dx_mask dx_buf dx_n] in *.
destruct HPRE as ((HJc & Hraok & Hra4 & Hgp & Htp & Hal16 & Hwin & Hsp0 & _) & _ & _ & _ & _ & Hn & Hbuf & _).
destruct Hsetf as (f0 & Ef).
set (S0 := spZ regs) in *.
set (R := 32 * ((S0 - 224) / 32)) in *.
set (F := frame_addr lyc DC_CID pos) in *.
set (FL := flag_addr lyc DC_CID pos) in *.
set (shF := shadow_addr F) in *.
set (L := RateCsv.csv_list mask) in *.
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _ & _).
pose proof Hstk1 as (Hsp0al & HSTK0 & Hceil & Hslo & _ & H47 & _).
pose proof HJc as (HARc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_lt rc) as Hcl.
unfold T_dcsv_STK, ESTACK in Hwin, HK.
assert (HS064 : 0 <= S0 < 2 ^ 64) by (subst S0; unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as X;
  change (bv_modulus 64) with (2 ^ 64) in X; lia).
(* ---- the frame (1, pos), its flag, and the blocks of S1 ---- *)
assert (Hin1 : In (DC_CID, pos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
assert (Echk : st_chunks S1 = st_chunks Sc) by (rewrite Ef; reflexivity).
assert (Eab : ablocks B lyc S1 = ablocks B lyc Sc) by (unfold ablocks; rewrite Ef; reflexivity).
destruct (al_frames _ _ HL _ _ _ _ _ _ _ HAR1 Hin1) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds _ _ HL _ _ _ _ _ _ _ HAR1 Hin1) as (HF4096 & HFceil & _).
destruct (al_flag _ _ HL _ _ _ _ _ _ _ HAR1 Hin1) as (HFLp & HFLo & HFLapp & HFLceil).
fold F FL in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil, HFLp, HFLo, HFLapp, HFLceil. fold shF in HFSpres.
change (fs_frame_bytes DC_CID) with 128 in HFapp, HFpres, HFSpres, HFceil.
change (128 / 8) with 16 in HFSpres.
assert (HshF : shF = SHADOW_OFF + F / 8) by reflexivity.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
assert (HshB : 2147450880 <= shF /\ shF + 16 <= 17594333495296) by (rewrite HshF; unfold SHADOW_OFF; lia).
assert (EF : frame_addr lyc DC_CID pos = F) by reflexivity.
assert (EFL : flag_addr lyc DC_CID pos = FL) by reflexivity.
assert (EshF : shadow_addr F = shF) by reflexivity.
assert (ES0 : spZ regs = S0) by reflexivity.
assert (EL : RateCsv.csv_list mask = L) by reflexivity.
clearbody S0 R F FL shF L.
assert (HR0 : alloc_ceiling + 8192 <= R) by lia.
assert (HdFFL : FL + 1 <= F \/ F + 128 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 128)) as [Hlt2|Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres FL ltac:(lia)) HFLo). }
(* every byte run C writes is owned at the call *)
assert (HOsh : forall a, shF <= a < shF + 16 -> aowned B lyc Sc a).
{ intros a Ha. apply (own_free_frame_shadow B lyc Sc _ DC_CID pos a (proj1 HARc)); [unfold DC_CID; lia | exact Hpos | exact Hnin|].
  rewrite EF, EshF. change (fs_frame_bytes DC_CID / 8) with 16. lia. }
assert (HOF : forall a, F <= a < F + 128 -> aowned B lyc Sc a).
{ intros a Ha. apply (own_free_frame B lyc Sc _ DC_CID pos a (proj1 HARc)); [unfold DC_CID; lia | exact Hpos | exact Hnin|].
  rewrite EF. change (fs_frame_bytes DC_CID) with 128. lia. }
assert (HOFL : aowned B lyc Sc FL).
{ apply (ep_aowned_sub B lyc Sc S1 FL Echk); [intros cp Hcp; rewrite Hfrs; right; exact Hcp | exact HFLo]. }
(* ---- run C's entry state ---- *)
set (X := ep_XC FL F regs).
set (E := Ereg regs3 X).
assert (B18 : bv_unsigned (ew E 18) = shF)
  by (subst E; rewrite (ew_Ereg_nat regs3 X 18 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
assert (E46 : ew E 46 = Z_to_bv 64 F) by exact (ew_Ereg_extra regs3 X 14).
assert (B46 : bv_unsigned (ew E 46) = F) by (rewrite E46; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9) = R)
  by (subst E; rewrite (ew_Ereg_nat regs3 X 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew E 8) = S0)
  by (subst E; rewrite (ew_Ereg_nat regs3 X 8 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 FL) by exact (ew_Ereg_extra regs3 X 0).
assert (B32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : @st_ok rsegs fq E ep_ssC (restrict (w_H W1) (@mkst fq regs3 (Z_to_bv 64 DC_EPI_C) mem3 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full (fx := fq) rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ep_rC. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E.
    + rewrite B18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (HFSpres o ltac:(lia))).
    + rewrite B46. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable rsegs). apply (proj1 (HFpres (F + o) ltac:(lia))). }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ F 120 8 (SOff 32 0) FL).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword.
        replace (F + 120) with (F + DC_FSZ - 8) by (unfold DC_FSZ; lia). exact HFW.
    + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs _ _ R 8 8 (SOff 46 0) F).
        -- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E46.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. exact C8.
      * apply (chunk_ok_val rsegs _ _ R 16 8 (SOff 46 0) F).
        -- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E46.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. exact C16.
    + rewrite B32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable rsegs). exact HFLp.
    + rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold ep_svch. rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
      apply (chunk_ok_val rsegs _ _ S0 (-8 - 8 * Z.of_nat j) 8 (SOff (32 + Nat.succ j) 0)
        (bv_unsigned (getr regs (nth j dc_saved 0%bv)))).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. subst E.
        rewrite (ew_Ereg_extra regs3 X (Nat.succ j)).
        unfold X, ep_XC. cbn [nth]. rewrite Z_to_bv_bv_unsigned. destruct Hj as [_ Hj]. unfold dc_saved.
        do 13 (destruct j as [|j]; [reflexivity|]). lia.
      * pose proof (bv_unsigned_in_range 64 (getr regs (nth j dc_saved 0%bv))) as Y.
        change (bv_modulus 64) with (2 ^ 64) in Y. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. replace (S0 + (-8 - 8 * Z.of_nat j)) with (S0 - 8 - 8 * Z.of_nat j) by lia.
        apply HSV. lia.
  - unfold ep_rC. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite B18, B46, B9, B32, B8.
    repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [ep_GC f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite B46. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
unfold cfg_at. change (w64 DC_EPI_C) with (Z_to_bv 64 DC_EPI_C).
ep_run_flag HS HJ HL rtsb_segs_low ML rtsb_wx ASF FFL.
- unfold DC_CID. lia.
- intros a (r & Hin & Ha). cbn [ss_mem ep_ssC ep_rC In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; fold E in Ha;
    rewrite ?B18, ?B46, ?B9, ?B32, ?B8 in Ha.
  + left. right. right. right. exists DC_CID, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EF, EshF. change (fs_frame_bytes DC_CID / 8) with 16. lia.
  + left. right. right. right. exists DC_CID, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes DC_CID) with 128. lia.
  + exfalso. lia.
  + right. rewrite EFL. lia.
  + exfalso. lia.
- intros msr HSr. rewrite EFL, <- B32. apply (ep_byte0_of rsegs E _ msr 32 0 1 0 1 HSr).
  cbn [ss_mem In]. right. right. right. left. reflexivity.
- ep_mach HS msD.
  (* what run C kept: every byte outside its three write windows, all owned at the call *)
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a ->
    aview rsegs (w_H W1) (ms_mem msD) a = aview rsegs (w_H W1) mem3 a).
  { intros a Ha Hno. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
    cbn [ss_mem ep_ssC ep_rC In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
      fold E in Hw; rewrite ?B18, ?B46, ?B9, ?B32, ?B8 in Hw.
    - exact (Hno (HOsh a ltac:(lia))).
    - exact (Hno (HOF a ltac:(lia))).
    - lia.
    - replace a with FL in Hno by lia. exact (Hno HOFL).
    - lia. }
  clear HF HG.
  eapply (SRr_ret_at rsegs dc_tbl dc_tbl_ok rtsb_wx W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta. unfold E in HS.
  ep_ext HS (1%bv : bv 5) Rf1. unfold X, ep_XC in Rf1. cbn [nth map app dc_saved] in Rf1.
  ep_atom HS (10%bv : bv 5) (21%bv : bv 5) Rf10. rewrite R21 in Rf10.
  lazymatch goal with |- dc_post _ _ _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) =>
    unfold dc_post, rt_cpost_o, rt_cpost_g;
    cbn [dx_STK dx_sp0 dx_FP dx_ly dx_S dx_W0 dx_mem0 dx_md0 dx_own dx_k dx_lyc dx_Sc dx_W dx_memc dx_mdc
         dx_regs dx_mask dx_buf dx_n];
    exists fq, lyc, (stack_free_state DC_CID pos S1), rg, mm, mdx end.
  split.
  { rewrite Rf1. unfold YK0s.ret_ok in Hraok. rewrite Hraok. reflexivity. }
  split; [exact Hfxk|].
  split; [apply (ajournal_materialize rsegs B HL rtsb_segs_low); exact HJ|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct Hr' as [->|[->|[->|Hr']]].
    - ep_z5g. ep_atom HS (2%bv : bv 5) (8%bv : bv 5) Hx. rewrite Hx, R8.
      rewrite <- ES0. unfold spZ, w64. apply Z_to_bv_bv_unsigned.
    - ep_z5g. ep_atom HS (3%bv : bv 5) (3%bv : bv 5) Hx. rewrite Hx, R3. symmetry. exact Hgp.
    - ep_z5g. ep_atom HS (4%bv : bv 5) (4%bv : bv 5) Hx. rewrite Hx, R4. symmetry. exact Htp.
    - destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; ep_z5g;
      lazymatch goal with |- getr _ ?rr = _ => ep_ext HS rr Hx end;
      rewrite Hx; unfold X, ep_XC; reflexivity. }
  assert (HWF1 : Wf (as_universe B) S1) by exact (am_wf _ _ _ _ (proj1 HAR1)).
  split.
  { destruct (ml_stack_free _ ML S1 DC_CID pos HWF1 Hin1) as (_ & l1 & l2 & E1 & E2). rewrite E2.
    rewrite Hfrs in E1. destruct l1 as [|f1 l1'].
    - cbn in E1. injection E1 as E1. symmetry. exact E1.
    - exfalso. cbn in E1. injection E1 as <- E1'. apply Hnin. rewrite E1'. apply in_or_app. right. left. reflexivity. }
  split.
  { intros a Ha. apply (ep_aowned_sub B lyc Sc (stack_free_state DC_CID pos S1) a); [| | exact Ha].
    - change (st_chunks (stack_free_state DC_CID pos S1)) with (st_chunks S1). exact Echk.
    - intros cp Hcp. destruct (ml_stack_free _ ML S1 DC_CID pos HWF1 Hin1) as (_ & l1 & l2 & E1 & E2). rewrite E2.
      rewrite Hfrs in E1. destruct l1 as [|f1 l1'].
      + cbn in E1. injection E1 as E1. rewrite <- E1. exact Hcp.
      + exfalso. cbn in E1. injection E1 as <- E1'. apply Hnin. rewrite E1'. apply in_or_app. right. left. reflexivity. }
  split.
  { unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B lyc S1). rewrite Eab. apply Permutation_refl. }
  split.
  { let rec kio := first [exact Hio | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio. }
  split.
  { rewrite Ef. unfold stack_free_state. apply (mo_le_set_fs_r MT MFS). apply (mo_le_set_fs_r MT MFS).
    apply (mo_le_refl MT MTL). }
  split.
  { intros a Ha Hw HnE. rewrite (KC a Ha ltac:(intros X0; apply HnE; left; exact X0)).
    apply (HK a Ha); [rewrite ES0 in Hw; unfold T_dcsv_STK, ESTACK in Hw; exact Hw | exact HnE]. }
  rewrite EL. split; [exact Rf10|].
  (* buf's bytes are none of run C's writes *)
  intros Hn0. apply ep_aview_garr8. intros j Hj.
  destruct (Hbuf Hn0) as (Hb0 & Hbn & (m & Hbm & Hbm0 & Hnm) & _ & _ & Hamr & _).
  pose proof (ep_cut_len L n ltac:(lia)) as Hcl2.
  assert (Hjn : Z.of_nat j < n) by lia.
  assert (Hbm1 : In (buf, m) (ablocks B lyc S1)) by (rewrite Eab; exact Hbm).
  pose proof (sep_block_frame _ _ HL _ _ _ _ _ buf m DC_CID pos HAR1 Hbm1 Hin1) as Hdbf.
  rewrite EF in Hdbf. unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. change (fs_frame_bytes DC_CID) with 128 in Hdbf.
  destruct (al_blocks _ _ HL _ _ _ _ _ buf m HAR1 Hbm1) as (_ & _ & _ & _ & Hbpres & _).
  pose proof (req_size_pos m ltac:(lia)) as Hrq.
  assert (HnFL : buf + Z.of_nat j <> FL).
  { intros Heq. apply (proj2 (Hbpres (buf + Z.of_nat j) ltac:(lia))). rewrite Heq. exact HFLo. }
  rewrite <- (ep_garr8_aview _ _ _ _ _ (HRES Hn0) j Hj).
  apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
  cbn [ss_mem ep_ssC ep_rC In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    fold E in Hw; rewrite ?B18, ?B46, ?B9, ?B32, ?B8 in Hw; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia.
Qed.

(* ---- n > 0: __asan_memcpy(buf, tmp, copy), then runs B1 and B2 to the join, then run C ---- *)
Lemma dc_mid : forall (c : dcx) (fq : YK11.FPState) pos S1 W1 regs1 mem1 md1 regsT mdT copy,
dc_pre (fx := fx) B c -> dc_core (fx := fx) B c 3 pos fq S1 W1 regs1 mem1 md1 ->
ajournal rsegs B (dx_STK c) (dx_sp0 c) (dx_FP c) (dx_ly c) (dx_S c) (dx_W0 c) (dx_mem0 c) (dx_md0 c)
  ((DC_CID, pos) :: dx_own c) (dx_lyc c) S1 W1 mem1 mdT (dx_k c) ->
same_io md1 mdT -> 0 < dx_n c ->
copy = Z.min (Z.of_nat (length (RateCsv.csv_list (dx_mask c)))) (dx_n c - 1) ->
getr regsT 1 = w64 DC_RA_CPY2 -> getr regsT 2 = w64 (dx_R c) ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 8 = w64 (dx_S0 c) -> getr regsT 9 = w64 (dx_R c) ->
getr regsT 10 = w64 (dx_buf c) -> getr regsT 11 = w64 (frame_addr (dx_lyc c) DC_CID pos + 32) ->
getr regsT 12 = w64 copy ->
getr regsT 18 = w64 (shadow_addr (frame_addr (dx_lyc c) DC_CID pos)) ->
getr regsT 19 = w64 copy -> getr regsT 20 = w64 (dx_buf c) ->
getr regsT 21 = w64 (Z.of_nat (length (RateCsv.csv_list (dx_mask c)))) ->
SRr rsegs W1 (@cfg_at fq rsegs B_MEMCPY regsT mem1 mdT) (dc_post (fx := fx) B MT c).
Proof.
intros c fq pos S1 W1 regs1 mem1 md1 regsT mdT copy HPRE HC HJT HioT Hn0 Hcopy
  T1 T2 T3 T4 T8 T9 T10 T11 T12 T18 T19 T20 T21.
pose proof RT as (HL & ML & _ & FFL & ASF & _ & MTL & MFS & _ & _ & AIM & _).
pose proof HPRE as HPRE0. pose proof HC as HC0.
destruct c as [STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n].
unfold dc_pre, dc_core, dx_R, dx_S0 in *.
cbn [dx_STK dx_sp0 dx_FP dx_ly dx_S dx_W0 dx_mem0 dx_md0 dx_own dx_k dx_lyc dx_Sc dx_W dx_memc dx_mdc
     dx_regs dx_mask dx_buf dx_n] in *.
destruct HPRE as ((HJc & Hraok & Hra4 & Hgp & Htp & Hal16 & Hwin & Hsp0 & _) & _ & Hmask & _ & _ & Hn & Hbuf & _).
destruct (Hbuf Hn0) as (Hb0 & Hbn & (m & Hbm & Hbm0 & Hnm) & _ & _ & Hamr & Hbw).
destruct HC as (Hi3 & Hfxk & HJ & Hfrs & Hnin & Hsetf & Hpos & Hab & Hnev & Hsecs & Hchk & Hio & Hwle & HRal & HRb &
  R2 & R3 & R4 & R8 & R9 & R18 & R21 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C112 &
  HSV & HFW & Htmp & Hfsh & HFpres0 & HSpres0 & _ & _ & _ & _ & _ & Hbufc & HK).
destruct (Hbufc Hn0) as (Hbra & Hbhull & Hbpres).
set (S0 := spZ regs) in *.
set (R := 32 * ((S0 - 224) / 32)) in *.
set (F := frame_addr lyc DC_CID pos) in *.
set (FL := flag_addr lyc DC_CID pos) in *.
set (shF := shadow_addr F) in *.
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _ & _).
pose proof Hstk1 as (Hsp0al & HSTK0 & Hceil & Hslo & _ & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_lt rc) as Hcl.
unfold T_dcsv_STK, ESTACK in Hwin, HK, Hbw.
assert (HS064 : 0 <= S0 < 2 ^ 64) by (subst S0; unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as X;
  change (bv_modulus 64) with (2 ^ 64) in X; lia).
assert (HR0 : alloc_ceiling + 8192 <= R) by lia.
assert (HR16 : (R - sp0) mod 16 = 0).
{ pose proof (Z.div_mod R 32 ltac:(lia)) as D. rewrite HRal, Z.add_0_r in D.
  pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2. rewrite Hsp0al, Z.add_0_r in D2.
  rewrite D, D2. replace (32 * (R / 32) - 16 * (sp0 / 16)) with ((2 * (R / 32) - sp0 / 16) * 16) by ring.
  apply Z_mod_mult. }
pose proof (dc_len_le mask 3 ltac:(lia) ltac:(lia)) as Hlen. change (RateCsv.csv_prefix mask 3) with (RateCsv.csv_list mask) in Hlen.
set (L := RateCsv.csv_list mask) in *.
set (len := Z.of_nat (length L)) in *.
assert (Hc0 : 0 <= copy <= len /\ copy <= n - 1) by lia.
(* the frame (1, pos) and buf, at S1 *)
assert (Hin1 : In (DC_CID, pos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
assert (Hbm1 : In (buf, m) (ablocks B lyc S1)) by (rewrite Hab; exact Hbm).
destruct (al_frames _ _ HL _ _ _ _ _ _ _ HAR1 Hin1) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds _ _ HL _ _ _ _ _ _ _ HAR1 Hin1) as (HF4096 & HFceil & _).
fold F in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil. fold shF in HFSpres.
change (fs_frame_bytes DC_CID) with 128 in HFapp, HFpres, HFSpres, HFceil.
change (128 / 8) with 16 in HFSpres.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof (sep_block_frame _ _ HL _ _ _ _ _ buf m DC_CID pos HAR1 Hbm1 Hin1) as Hdbf.
fold F in Hdbf. unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. change (fs_frame_bytes DC_CID) with 128 in Hdbf.
pose proof (req_size_pos m ltac:(lia)) as Hrq.
assert (HshF : shF = SHADOW_OFF + F / 8) by reflexivity.
assert (HF8 : F / 8 = 4 * (F / 32)).
{ pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HFal, Z.add_0_r in D. rewrite D at 1.
  replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring. apply Z.div_mul. lia. }
assert (HFd : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)) as D; rewrite HFal, Z.add_0_r in D; exact D).
assert (HshB : 2147450880 <= shF /\ shF + 16 <= 17594333495296) by (rewrite HshF, HF8; unfold SHADOW_OFF; lia).
(* ---- __asan_memcpy(buf, tmp, copy), ra 0x845a8 ---- *)
unfold cfg_at. change (w64 B_MEMCPY) with (Z_to_bv 64 B_MEMCPY).
eapply SRr_bind.
{ refine (rtsb_intrin_at B HL OCpy B_MEMCPY (AIM fq) W1 regsT mem1 STK sp0 FP ly S W0 mem0 md0
    ((DC_CID, pos) :: own) lyc S1 mdT k buf (F + 32) copy (R - sp0) (w64 DC_RA_CPY2) HJT T10 T11 T12
    _ _ _ _ HR16 _ _ T3 T4 T1 _ _ _ _ _ _).
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite T2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - lia.
  - unfold ESTACK. lia.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (buf + (a - buf)) by lia.
      apply (rt_fresh_awr STK sp0 FP (ablocks B ly S) (ablocks B lyc S1) lyc ((DC_CID, pos) :: own) buf m (a - buf));
        [exact Hbm1 | exact Hbm0 | lia].
    + unfold ESTACK. lia.
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ _ buf n buf copy Hbra); lia.
  - intros Hc. apply (ep_hull_sub _ buf n copy ltac:(lia) Hbhull).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - apply (aview_some_of_apresent rsegs). exact (proj1 (HFpres a ltac:(lia))).
      - unfold spZ. rewrite T2. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia. }
    split; [lia|].
    split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
    split.
    { intros x Hx. exists 0. split; [|left; reflexivity].
      assert (Hsx : shadow_of_addr SHADOW_OFF x = shF + (x - F) / 8).
      { unfold shadow_of_addr. rewrite HshF, HF8. replace x with ((x - F) + (F / 32 * 4) * 8) at 1 by lia.
        rewrite Z.div_add by lia. ring. }
      rewrite Hsx. assert (Hq : 4 <= (x - F) / 8 <= 6).
      { split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
      pose proof (Hfsh ((x - F) / 8) ltac:(unfold dc_shA; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as Hv.
      fold shF in Hv. rewrite Hv.
      f_equal. set (q := (x - F) / 8) in *. assert (Hq3 : q = 4 \/ q = 5 \/ q = 6) by lia.
      destruct Hq3 as [-> | [-> | ->]]; reflexivity. }
    intros Hc s Hs. apply (aview_some_of_apresent rsegs). apply HSpres0. unfold DC_FSZ. change (128 / 8) with 16.
    rewrite (rtsb_fsh_addr F 32 HFal ltac:(lia)) in Hs.
    replace (F + 32 + copy - 1) with (F + (31 + copy)) in Hs by lia.
    rewrite (rtsb_fsh_addr F (31 + copy) HFal ltac:(lia)) in Hs. fold shF in Hs. change (32 / 8) with 4 in Hs.
    assert (Ht : 3 <= (31 + copy) / 8 <= 6).
    { split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]. }
    set (t := (31 + copy) / 8) in *.
    pose proof (Z.div_mod (shF + 4) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (shF + 4) 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod (shF + t) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (shF + t) 8 ltac:(lia)) as M2.
    rewrite HshF, HF8 in D1, D2, M1, M2. rewrite HshF, HF8 in Hs |- *. unfold SHADOW_OFF in *. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hsame & _ & Hcpy & Hkeep).
pose proof rtsb_segs_low as Hsegs. pose proof rtsb_wx as Hwx.
(* the registers run B and run C read, kept by the call *)
assert (P2 : getr regs2 2 = w64 R) by (pose proof (HP 2 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T2).
assert (P3 : getr regs2 3 = w64 (as_gp B)) by (pose proof (HP 3 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T3).
assert (P4 : getr regs2 4 = w64 (as_tp B)) by (pose proof (HP 4 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T4).
assert (P8 : getr regs2 8 = w64 S0) by (pose proof (HP 8 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T8).
assert (P9 : getr regs2 9 = w64 R) by (pose proof (HP 9 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T9).
assert (P18 : getr regs2 18 = w64 shF) by (pose proof (HP 18 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T18).
assert (P19 : getr regs2 19 = w64 copy) by (pose proof (HP 19 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T19).
assert (P20 : getr regs2 20 = w64 buf) by (pose proof (HP 20 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T20).
assert (P21 : getr regs2 21 = w64 len) by (pose proof (HP 21 ltac:(unfold acallee_saved; lia)) as X; ep_z5 X; rewrite X; exact T21).
clear HP.
(* the bytes the call kept *)
assert (Kcpy : forall a, 0 <= a < 2 ^ 64 -> ~ (buf <= a < buf + n) -> ~ (R - 4096 <= a < R) ->
  aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha H1 H2. apply Hkeep; [exact Ha | lia | unfold ESTACK; lia]. }
(* ---- run B's entry state ---- *)
set (XB := ep_XB (buf + copy)).
set (EB := Ereg regs2 XB).
assert (B9 : bv_unsigned (ew EB 9) = R)
  by (subst EB; rewrite (ew_Ereg_nat regs2 XB 9 9%bv eq_refl), P9; apply unsigned_lit_small; lia).
assert (B19 : bv_unsigned (ew EB 19) = copy)
  by (subst EB; rewrite (ew_Ereg_nat regs2 XB 19 19%bv eq_refl), P19; apply unsigned_lit_small; lia).
assert (E20 : ew EB 20 = Z_to_bv 64 buf)
  by (subst EB; rewrite (ew_Ereg_nat regs2 XB 20 20%bv eq_refl), P20; reflexivity).
assert (B20 : bv_unsigned (ew EB 20) = buf) by (rewrite E20; apply unsigned_lit_small; lia).
assert (E32 : ew EB 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs2 XB 0).
assert (E33 : ew EB 33 = Z_to_bv 64 (buf + copy)) by exact (ew_Ereg_extra regs2 XB 1).
assert (B33 : bv_unsigned (ew EB 33) = buf + copy) by (rewrite E33; apply unsigned_lit_small; lia).
destruct (al_blocks _ _ HL _ _ _ _ _ buf m (proj1 HJ2) Hbm1) as (_ & _ & _ & _ & Hbp2 & _).
assert (HSB : @st_ok rsegs fq EB ep_ssB (restrict (w_H W1) (@mkst fq regs2 (Z_to_bv 64 DC_RA_CPY2) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full (fx := fq) rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ep_rB. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold EB.
    + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs _ _ R 32 8 (SOff 20 0) buf).
        -- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E20.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem2); [|exact C32].
           intros kk Hk. apply Kcpy; lia.
      * apply (chunk_ok_val rsegs _ _ R 88 8 (SOff 32 0) SHADOW_OFF).
        -- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
        -- unfold SHADOW_OFF. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn. lia.
        -- change (N.to_nat 8) with 8%nat. apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 mem2); [|exact C88].
           intros kk Hk. apply Kcpy; lia.
    + rewrite B33. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). replace (buf + copy + o) with (buf + copy) by lia.
      exact (proj1 (Hbp2 (buf + copy) ltac:(lia))).
  - unfold ep_rB. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold EB. rewrite B9, B33. repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [ep_GB f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. fold EB.
    rewrite B33, B20, E32. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
    repeat split; lia. }
assert (SHOKB : sh_ok rsegs ep_Bx ep_SH EB (mrestrict (w_H W1) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range rsegs (w_H W1) mem2 EB ep_Bx 33 buf n (buf + copy) 0 1).
  - apply (ep_ra_kept (aview rsegs (w_H W1) mem1)); [|exact Hbra].
    intros x Hx. unfold shadow_of_addr. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
    assert (Hx8 : 0 <= x / 8 <= (2 ^ 47 - 1) / 8) by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
    change ((2 ^ 47 - 1) / 8) with 17592186044415 in Hx8.
    apply Kcpy; unfold SHADOW_OFF; lia.
  - unfold ep_Bx. apply (U_atom EB 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia.
  - apply (U_atom EB 33 (buf + copy) E33). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia. }
(* ---- run B1: 0x845a8 add a0,s4,s3; stop at 0x845ac ---- *)
change (w64 DC_RA_CPY2) with (Z_to_bv 64 DC_RA_CPY2).
aj_run_to_tok dc_tbl_ok HSB HJ2 SHOKB ep_Bspan DC_EPI_B2.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (buf + copy)); [reflexivity | exact B33 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (buf + (a - buf)) by lia.
  apply (rt_fresh_awr _ _ _ _ _ _ _ buf m (a - buf)); [exact Hbm1 | exact Hbm0 | lia]. }
ep_mach HSB msB. rename HFr into HFr1. clear HF HG.
(* pin a0 = buf + copy to atom 33 *)
assert (Hden : sv_denot EB (SOff 33 0) = getr (ms_regs (restrict (w_H W1) msB)) 10%bv).
{ cbn [ms_regs restrict]. rewrite (st_ok_restrict_reg rsegs (w_H W1) EB _ msB 10%bv HSB).
  lazymatch goal with |- _ = sv_denot _ ?t => let t' := eval vm_compute in t in change t with t' end.
  apply bv_eq.
  first [ change (U EB (SOff 33 0) = U EB (SAlu ALU_ADD (SOff 19 0) (SOff 20 0)))
        | change (U EB (SOff 33 0) = U EB (SAlu ALU_ADD (SOff 20 0) (SOff 19 0))) ].
  rewrite (U_atom EB 33 (buf + copy) E33 ltac:(lia)).
  rewrite U_add_off_atom; rewrite ?B19, ?B20; unfold M64; lia. }
pose proof (st_ok_pin_sv rsegs EB _ _ 10%bv (SOff 33 0) HSB eq_refl Hden) as HSP. clear HSB Hden.
(* the cond fact buf <= buf + copy: the first trap test 0x845ac `bltu a0,s4` reads it (rtb_geu_lit: buf + copy
   does not wrap) *)
assert (Hbr : branch_taken BC_LTU (sv_denot EB (SOff 33 0)) (sv_denot EB (SOff 20 0)) = false).
{ rewrite (rtsb_den_atom EB 33 (buf + copy) E33 ltac:(lia)), (rtsb_den_atom EB 20 buf E20 ltac:(lia)).
  exact (rtb_geu_lit buf (buf + copy) ltac:(lia) ltac:(lia) ltac:(lia)). }
pose proof (st_ok_add_cond_neg rsegs EB _ _ BC_LTU (SOff 33 0) (SOff 20 0) HSP Hbr) as HSQ.
clear HSP Hbr. rename HSQ into HSP.
(* ---- run B2: the three trap tests 0x845ac .. 0x845c8 (each decided by the engine from the cond fact and the
   atom ranges of atoms 20 and 33), the store check of 0x845cc .. 0x845dc through the token engine, the NUL at
   0x845e0; stop at 0x845e4 ---- *)
aj_run_to_tok dc_tbl_ok HSP HJ2 SHOKB ep_Bspan DC_EPI_C.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (buf + copy)); [reflexivity | exact B33 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (buf + (a - buf)) by lia.
  apply (rt_fresh_awr _ _ _ _ _ _ _ buf m (a - buf)); [exact Hbm1 | exact Hbm0 | lia]. }
ep_mach HSP msC. clear HF HG. rename HFr into HFr2.
(* the memory after run B: as after the call but at buf + copy, which holds the NUL *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> a <> buf + copy ->
  aview rsegs (w_H W1) (ms_mem msC) a = aview rsegs (w_H W1) mem2 a).
{ intros a Ha Hne. transitivity (aview rsegs (w_H W1) (ms_mem msB) a).
  - apply aview_eq_of. apply HFr2. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?B9, ?B33 in Hw; lia.
  - apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?B9, ?B33 in Hw; lia. }
assert (Hnul : aview rsegs (w_H W1) (ms_mem msC) (buf + copy) = Some 0).
{ pose proof (ep_byte0_of rsegs _ _ (restrict (w_H W1) msC) 33 0 1 0 1 HSP ltac:(vm_compute; right; left; reflexivity)) as Hb0'.
  cbn [ms_mem restrict] in Hb0'. rewrite !ew_ewset_other in Hb0' by lia. rewrite B33 in Hb0'.
  unfold aview. rewrite Hb0'. reflexivity. }
clear HFr1 HFr2.
unfold EB in HSP.
ep_atom2 HSP (3%bv : bv 5) (3%bv : bv 5) Q3. ep_atom2 HSP (4%bv : bv 5) (4%bv : bv 5) Q4.
ep_atom2 HSP (8%bv : bv 5) (8%bv : bv 5) Q8. ep_atom2 HSP (9%bv : bv 5) (9%bv : bv 5) Q9.
ep_atom2 HSP (18%bv : bv 5) (18%bv : bv 5) Q18. ep_atom2 HSP (21%bv : bv 5) (21%bv : bv 5) Q21.
(* ---- run C ---- *)
rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ msC HSP eq_refl). cbn [ss_pc].
change (Z_to_bv 64 542180) with (w64 DC_EPI_C).
apply (dc_tailC (DCx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n) fq pos S1 W1).
all: ep_dx; fold S0 R F L.
- exact HPRE0.
- exact Hfxk.
- exact HJ2.
- exact Hfrs.
- exact Hnin.
- exact Hsetf.
- exact Hpos.
- eapply same_io_trans; [exact Hio|]. eapply same_io_trans; [exact HioT|].
  eapply same_io_trans; [apply same_io_materialized; exact Hsame|].
  let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
- exact HRal.
- exact HRb.
- rewrite Q3. exact P3.
- rewrite Q4. exact P4.
- rewrite Q8. exact P8.
- rewrite Q9. exact P9.
- rewrite Q18. exact P18.
- rewrite Q21. exact P21.
- apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 (ms_mem msC)); [|exact C8].
  intros kk Hk. rewrite KB by lia. apply Kcpy; lia.
- apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 (ms_mem msC)); [|exact C16].
  intros kk Hk. rewrite KB by lia. apply Kcpy; lia.
- intros j Hj. apply (val_mem_kept rsegs (w_H W1) (w_H W1) mem1 (ms_mem msC)); [|exact (HSV j Hj)].
  intros kk Hk. rewrite KB by lia. apply Kcpy; lia.
- rewrite (rdword_ext (aview rsegs (w_H W1) mem1) (aview rsegs (w_H W1) (ms_mem msC)) (F + DC_FSZ - 8)); [exact HFW|].
  intros kk Hk. unfold DC_FSZ in *. rewrite KB by lia. apply Kcpy; lia.
- intros a Ha Hw HnE. unfold dx_S0 in Hw. cbn [dx_regs] in Hw. fold S0 in Hw. unfold T_dcsv_STK, ESTACK in Hw.
  rewrite KB by (first [exact Ha | intros ->; apply HnE; right; split; [exact Hn0 | lia]]).
  rewrite Kcpy; [| exact Ha | intros X; apply HnE; right; split; [exact Hn0 | lia] | lia].
  apply HK; [exact Ha | exact Hw | intros X; apply HnE; left; exact X].
- intros _. assert (Ecut : RateCsv.csv_cut L n = firstn (Z.to_nat copy) L).
  { unfold RateCsv.csv_cut. rewrite Hcopy. reflexivity. }
  change (RateCsv.csv_prefix mask 3 ++ [0]) with (L ++ [0]) in Htmp.
  apply ep_aview_garr8. rewrite Ecut. intros j Hj.
  rewrite length_app, length_firstn in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j (Z.to_nat copy)) as [Hjc | Hjc].
  + rewrite app_nth1 by (rewrite length_firstn; lia). rewrite (ep_nth_firstn L j (Z.to_nat copy) Hjc).
    rewrite KB by lia. rewrite (Hcpy (Z.of_nat j) ltac:(lia)).
    assert (Hjl : (j < length L)%nat) by lia.
    rewrite <- (app_nth1 L [0] 0 Hjl).
    apply (ep_garr8_aview _ _ _ _ _ Htmp). rewrite length_app. cbn [length]. lia.
  + assert (j = Z.to_nat copy) as -> by lia.
    rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Z.to_nat copy - Init.Nat.min (Z.to_nat copy) (length L))%nat with 0%nat by lia.
    cbn [nth]. rewrite Z2Nat.id by lia. exact Hnul.
Qed.

(* ---- the part: run A, its two splits, then dc_mid (n > 0) or run C (n = 0) ---- *)
Theorem dc_epi : dc_epi_stmt B MT.
Proof.
unfold dc_epi_stmt. intros c fq pos S1 W1 regs1 mem1 md1 HPRE HC.
pose proof RT as (HL & ML & _ & FFL & ASF & _ & MTL & MFS & _).
pose proof rtsb_segs_low as Hsegs. pose proof rtsb_wx as Hwx.
pose proof HPRE as HPRE0. pose proof HC as HC0.
destruct c as [STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n].
unfold dc_pre, dc_core, dx_R, dx_S0 in HPRE, HC.
cbn [dx_STK dx_sp0 dx_FP dx_ly dx_S dx_W0 dx_mem0 dx_md0 dx_own dx_k dx_lyc dx_Sc dx_W dx_memc dx_mdc
     dx_regs dx_mask dx_buf dx_n] in HPRE, HC.
destruct HPRE as ((HJc & Hraok & Hra4 & Hgp & Htp & Hal16 & Hwin & Hsp0 & _) & _ & Hmask & _ & _ & Hn & Hbuf & _).
destruct HC as (Hi3 & Hfxk & HJ & Hfrs & Hnin & Hsetf & Hpos & Hab & Hnev & Hsecs & Hchk & Hio & Hwle & HRal & HRb &
  R2 & R3 & R4 & R8 & R9 & R18 & R21 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C80 & C88 & C112 &
  HSV & HFW & Htmp & Hfsh & HFpres0 & HSpres0 & _ & _ & _ & _ & _ & Hbufc & HK).
set (S0 := spZ regs) in *.
set (R := 32 * ((S0 - 224) / 32)) in *.
set (F := frame_addr lyc DC_CID pos) in *.
pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _ & _).
pose proof Hstk1 as (Hsp0al & HSTK0 & Hceil & Hslo & _ & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_lt rc) as Hcl.
unfold T_dcsv_STK, ESTACK in Hwin.
assert (HS064 : 0 <= S0 < 2 ^ 64) by (subst S0; unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as X;
  change (bv_modulus 64) with (2 ^ 64) in X; lia).
assert (Hin1 : In (DC_CID, pos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds _ _ HL _ _ _ _ _ _ _ HAR1 Hin1) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
change (fs_frame_bytes DC_CID) with 128 in HFceil.
pose proof (dc_len_le mask 3 ltac:(lia) ltac:(lia)) as Hlen.
set (len := Z.of_nat (length (RateCsv.csv_prefix mask 3))) in *.
(* ---- run A's entry state ---- *)
set (XA := ep_XA buf n F).
set (EA := Ereg regs1 XA).
assert (B9 : bv_unsigned (ew EA 9) = R)
  by (subst EA; rewrite (ew_Ereg_nat regs1 XA 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E21 : ew EA 21 = Z_to_bv 64 len) by (subst EA; rewrite (ew_Ereg_nat regs1 XA 21 21%bv eq_refl), R21; reflexivity).
assert (E32 : ew EA 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs1 XA 0).
assert (E33 : ew EA 33 = Z_to_bv 64 buf) by exact (ew_Ereg_extra regs1 XA 1).
assert (E34 : ew EA 34 = Z_to_bv 64 n) by exact (ew_Ereg_extra regs1 XA 2).
assert (E35 : ew EA 35 = Z_to_bv 64 F) by exact (ew_Ereg_extra regs1 XA 3).
assert (HSA : @st_ok rsegs fq EA ep_ssA (restrict (w_H W1) (@mkst fq regs1 (Z_to_bv 64 DC_TAIL) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full (fx := fq) rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ep_rA. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold EA. rewrite B9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val rsegs _ _ R 8 8 (SOff 35 0) F).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E35.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. exact C8.
    + apply (chunk_ok_val rsegs _ _ R 16 8 (SOff 35 0) F).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E35.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. exact C16.
    + apply (chunk_ok_val rsegs _ _ R 24 8 (SOff 34 0) n).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E34.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. exact C24.
    + apply (chunk_ok_val rsegs _ _ R 32 8 (SOff 33 0) (buf mod 2 ^ 64)).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E33. symmetry. apply Z_to_bv_mod64.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. apply ep_val_mod. exact C32.
    + apply (chunk_ok_val rsegs _ _ R 48 8 (SOff 35 32) (F + 32)).
      * cbn [sv_denot]. rewrite E35, unsigned_lit_small by lia. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. exact C48.
    + apply (chunk_ok_val rsegs _ _ R 88 8 (SOff 32 0) SHADOW_OFF).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * unfold SHADOW_OFF. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. exact C88.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I | exact I]]. cbn [ep_GA f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. fold EA. rewrite E34, E21, E35. rewrite !unsigned_lit_small by lia.
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (SHOKA : sh_ok rsegs ep_Bx [] EA (mrestrict (w_H W1) mem1)) by constructor.
(* ---- run A: 0x8457c; stop at 0x84580 beqz a0 (a0 = n) ---- *)
unfold cfg_at. change (w64 DC_TAIL) with (Z_to_bv 64 DC_TAIL).
aj_run_tok dc_tbl_ok HSA HJ SHOKA ep_Bspan.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
ep_mach HSA msA. lazymatch type of HF with frame_of ?E ?rs ?m ?m0 => pose proof (frame_of_read_only E rs m m0 ltac:(vm_compute; reflexivity) HF) as EmA end. clear HF HFr HG.
srr_branch_tok dc_tbl_ok HSA SHOKA ep_Bspan.
- (* n = 0: the branch to 0x845e4; no byte of buf is written *)
  rewrite branch_eq_U in Hc. rewrite (U_atom EA 34 n E34 ltac:(lia)), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  aj_run_to_tok dc_tbl_ok HSA HJ SHOKA ep_Bspan DC_EPI_C.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  ep_mach HSA msC. lazymatch type of HF with frame_of ?E ?rs ?m ?m0 => pose proof (frame_of_read_only E rs m m0 ltac:(vm_compute; reflexivity) HF) as EmC end. clear HF HFr HG.
  rewrite EmC, EmA in HJ.
  unfold EA in HSA.
  ep_atom HSA (3%bv : bv 5) (3%bv : bv 5) Q3. ep_atom HSA (4%bv : bv 5) (4%bv : bv 5) Q4.
  ep_atom HSA (8%bv : bv 5) (8%bv : bv 5) Q8. ep_atom HSA (9%bv : bv 5) (9%bv : bv 5) Q9.
  ep_atom HSA (18%bv : bv 5) (18%bv : bv 5) Q18. ep_atom HSA (21%bv : bv 5) (21%bv : bv 5) Q21.
  rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ msC HSA eq_refl). cbn [ss_pc].
  change (Z_to_bv 64 542180) with (w64 DC_EPI_C). rewrite EmC, EmA.
  apply (dc_tailC (DCx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n) fq pos S1 W1).
  all: ep_dx; fold S0 R F.
  + exact HPRE0.
  + exact Hfxk.
  + exact HJ.
  + exact Hfrs.
  + exact Hnin.
  + exact Hsetf.
  + exact Hpos.
  + eapply same_io_trans; [exact Hio|].
    let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
  + exact HRal.
  + exact HRb.
  + rewrite Q3. exact R3.
  + rewrite Q4. exact R4.
  + rewrite Q8. exact R8.
  + rewrite Q9. exact R9.
  + rewrite Q18. exact R18.
  + rewrite Q21. exact R21.
  + exact C8.
  + exact C16.
  + exact HSV.
  + exact HFW.
  + intros a Ha Hw HnE. unfold dx_S0 in Hw. cbn [dx_regs] in Hw. fold S0 in Hw. unfold T_dcsv_STK, ESTACK in Hw.
    apply HK; [exact Ha | exact Hw | intros X; apply HnE; left; exact X].
  + intros Hn0. cbn [dx_n] in Hn0. lia.
- (* n > 0 *)
  rewrite branch_eq_U in Hc. rewrite (U_atom EA 34 n E34 ltac:(lia)), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  assert (Hn0 : 0 < n) by lia. clear Hc.
  (* 0x84584 .. 0x84588; stop at 0x8458c bltu s5,a0 (len, n - 1) *)
  aj_run_tok dc_tbl_ok HSA HJ SHOKA ep_Bspan.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end.
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  ep_mach HSA msA2. lazymatch type of HF with frame_of ?E ?rs ?m ?m0 => pose proof (frame_of_read_only E rs m m0 ltac:(vm_compute; reflexivity) HF) as EmA2 end. clear HF HFr HG.
  srr_branch_tok dc_tbl_ok HSA SHOKA ep_Bspan.
  + (* len < n - 1: copy = len *)
    rewrite branch_ltu_U in Hc. rewrite (U_atom EA 21 len E21 ltac:(lia)), (U_atom_off EA 34 n (-1) E34) in Hc by lia.
    apply Z.ltb_lt in Hc.
    aj_run_tok dc_tbl_ok HSA HJ SHOKA ep_Bspan.
    { lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end.
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    ep_mach HSA msT. lazymatch type of HF with frame_of ?E ?rs ?m ?m0 => pose proof (frame_of_read_only E rs m m0 ltac:(vm_compute; reflexivity) HF) as EmT end. clear HF HFr HG.
    rewrite EmT, EmA2, EmA in HJ.
    unfold EA in HSA.
    ep_atom HSA (2%bv : bv 5) (2%bv : bv 5) Q2. ep_atom HSA (3%bv : bv 5) (3%bv : bv 5) Q3.
    ep_atom HSA (4%bv : bv 5) (4%bv : bv 5) Q4. ep_atom HSA (8%bv : bv 5) (8%bv : bv 5) Q8.
    ep_atom HSA (9%bv : bv 5) (9%bv : bv 5) Q9. ep_atom HSA (18%bv : bv 5) (18%bv : bv 5) Q18.
    ep_atom HSA (21%bv : bv 5) (21%bv : bv 5) Q21.
    ep_atom HSA (12%bv : bv 5) (21%bv : bv 5) Q12. ep_atom HSA (19%bv : bv 5) (21%bv : bv 5) Q19.
    ep_ext HSA (10%bv : bv 5) Q10. ep_ext HSA (20%bv : bv 5) Q20.
    unfold XA, ep_XA in Q10, Q20. cbn [nth] in Q10, Q20.
    rreg HSA (1%bv : bv 5) Q1. rreg HSA (11%bv : bv 5) Q11.
    rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ msT HSA eq_refl). cbn [ss_pc].
    change (Z_to_bv 64 334008) with (w64 B_MEMCPY). rewrite EmT, EmA2, EmA.
    apply (dc_mid (DCx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n) fq pos S1 W1
      regs1 mem1 md1 _ _ len HPRE0 HC0 HJ).
    all: ep_dx; fold S0 R F.
    * let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
    * exact Hn0.
    * change (RateCsv.csv_list mask) with (RateCsv.csv_prefix mask 3). fold len. lia.
    * rewrite Q1. reflexivity.
    * rewrite Q2. exact R2.
    * rewrite Q3. exact R3.
    * rewrite Q4. exact R4.
    * rewrite Q8. exact R8.
    * rewrite Q9. exact R9.
    * exact Q10.
    * rewrite Q11. change (ew (Ereg regs1 XA) 35) with (nth 3 XA (Z_to_bv 64 0)). unfold XA, ep_XA. cbn [nth].
      rewrite unsigned_lit_small by lia. reflexivity.
    * rewrite Q12. exact R21.
    * rewrite Q18. exact R18.
    * rewrite Q19. exact R21.
    * exact Q20.
    * rewrite Q21. exact R21.
  + (* len >= n - 1: copy = n - 1 *)
    rewrite branch_ltu_U in Hc. rewrite (U_atom EA 21 len E21 ltac:(lia)), (U_atom_off EA 34 n (-1) E34) in Hc by lia.
    apply Z.ltb_ge in Hc.
    aj_run_tok dc_tbl_ok HSA HJ SHOKA ep_Bspan.
    { lazymatch goal with |- awr_ok ?E ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok E rs' stk s0 fp b0 bc ly own) end.
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    ep_mach HSA msT. lazymatch type of HF with frame_of ?E ?rs ?m ?m0 => pose proof (frame_of_read_only E rs m m0 ltac:(vm_compute; reflexivity) HF) as EmT end. clear HF HFr HG.
    rewrite EmT, EmA2, EmA in HJ.
    unfold EA in HSA.
    ep_atom HSA (2%bv : bv 5) (2%bv : bv 5) Q2. ep_atom HSA (3%bv : bv 5) (3%bv : bv 5) Q3.
    ep_atom HSA (4%bv : bv 5) (4%bv : bv 5) Q4. ep_atom HSA (8%bv : bv 5) (8%bv : bv 5) Q8.
    ep_atom HSA (9%bv : bv 5) (9%bv : bv 5) Q9. ep_atom HSA (18%bv : bv 5) (18%bv : bv 5) Q18.
    ep_atom HSA (21%bv : bv 5) (21%bv : bv 5) Q21.
    ep_ext HSA (10%bv : bv 5) Q10. ep_ext HSA (20%bv : bv 5) Q20.
    unfold XA, ep_XA in Q10, Q20. cbn [nth] in Q10, Q20.
    rreg HSA (1%bv : bv 5) Q1. rreg HSA (11%bv : bv 5) Q11. rreg HSA (12%bv : bv 5) Q12. rreg HSA (19%bv : bv 5) Q19.
    rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ msT HSA eq_refl). cbn [ss_pc].
    change (Z_to_bv 64 334008) with (w64 B_MEMCPY). rewrite EmT, EmA2, EmA.
    apply (dc_mid (DCx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n) fq pos S1 W1
      regs1 mem1 md1 _ _ (n - 1) HPRE0 HC0 HJ).
    all: ep_dx; fold S0 R F.
    * let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
    * exact Hn0.
    * change (RateCsv.csv_list mask) with (RateCsv.csv_prefix mask 3). fold len. lia.
    * rewrite Q1. reflexivity.
    * rewrite Q2. exact R2.
    * rewrite Q3. exact R3.
    * rewrite Q4. exact R4.
    * rewrite Q8. exact R8.
    * rewrite Q9. exact R9.
    * exact Q10.
    * rewrite Q11. change (ew (Ereg regs1 XA) 35) with (nth 3 XA (Z_to_bv 64 0)). unfold XA, ep_XA. cbn [nth].
      rewrite unsigned_lit_small by lia. reflexivity.
    * rewrite Q12. change (ew (Ereg regs1 XA) 34) with (nth 2 XA (Z_to_bv 64 0)). unfold XA, ep_XA. cbn [nth].
      rewrite unsigned_lit_small by lia. reflexivity.
    * rewrite Q18. exact R18.
    * rewrite Q19. change (ew (Ereg regs1 XA) 34) with (nth 2 XA (Z_to_bv 64 0)). unfold XA, ep_XA. cbn [nth].
      rewrite unsigned_lit_small by lia. reflexivity.
    * exact Q20.
    * rewrite Q21. exact R21.
Qed.
End e.

Print Assumptions dc_epi.
