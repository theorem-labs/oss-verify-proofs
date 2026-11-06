(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 1082 of its 1124 lines of code are new or changed and 284 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW5Int.v at a66696a9b1d1 for the same unit's
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; image B keeps the Int-7 value pod in the frame
   object e42 (F + 0x180) and writes it with the out-of-line pod_write_ent (0x82404), where image A put the pod
   straight into the first block with four inlined pod_put32 calls, so the walk is four runs (the scope stores and
   the memset of e42's body, the pod's three words, the first-flag arm with its one instrumented check, the scope
   stores back) around two calls (checked_memset 0x51d54, pod_write_ent 0x83cc4) instead of A's two runs around one;
   the pcs (SELI 0x82398 -> LATCH7 0x8257c), the registers (s1 = R, s3 = the frame's shadow base, s4 = the runtime's
   shadow offset, t0 / t4 / a4 kept across the call in s2 / s6 / s8) and the real-frame cells (R+0x78, R+0x80,
   R+0x90, R+0x160, R+0x168) are image B's; the chaining is lib/AU/RtPgStepsB.v's rtsb_post_seq / rtsb_intrin_seq /
   rtsb_pwe_seq; the prefixes w5_ / w5i_ become w5b_ / w5bi_, rtm_ becomes rtmb_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the core walk of the Int-7
   value pod of one property, SELI 0x82398 -> LATCH7 0x8257c, in LLVMFuzzerTestOneInput (pod.h:412-419).
   Proves no function (kind: segment lemma).

   THE CODE (0x82398 .. 0x82470 and the slow block 0x825ec)
     0x82398-0x823c8  13 x `sb zero,o(s3)`, o = 0x30 .. 0x3c: e42's granules into scope
     0x823cc-0x823e0  a2 = 92, a0 = [R+0x78] = F + 0x18c, a1 = 0, s2 = t0, s6 = t4, s8 = a4
     0x823e4  `jal` 0x51d54 (checked_memset): e42.body[4..96) := 0, back at 0x823e8
     0x823e8-0x823fc  a1 = [R+0x80] = F + 0x180; e42.type := 4, e42.size := 4, e42.body[0..4) := 7
     0x82400  a0 = [R+0x168] = pp
     0x82404  `jal` 0x83cc4 (pod_write_ent): the pod of e42 at pp->len, back at 0x82408
     0x82408-0x82418  a3 = s8, t4 = s6, t0 = s2; a0 = [R+0x160] = first; `beqz a0` -> 0x82434
     0x8241c-0x8242c  a0 = [R+0x90] = pp + 0x400c; its shadow byte; `bnez` -> the slow block 0x825ec
     0x82430  `sw s9,0(a0)`: has_params := 1 (s9 = 1)
     0x82434-0x8246c  a0 = -8, the same 13 `sb a0,o(s3)`: e42's granules out of scope; s8 = -8
     0x82470  `j` 0x8257c (LATCH7)
   THE WALK. Four runs around the two calls, chained with lib/AU/RtPgStepsB.v's rtsb_post_seq.
     run 1 (0x82398 -> the callee's entry 0x51d54, the plain engine YCbq aj_run_to): the 13 scope stores into the
       frame's shadow and the call's arguments. The block has no instrumented check and its write window is the
       frame's shadow, which lies inside the token engine's shadow band, so it runs on the plain engine.
     the call checked_memset(F + 0x18c, 0, 92) through rtsb_intrin_seq (the Section hypothesis W5B_AMEMSET); its
       destination is addressable because the 13 stores just put e42 in scope (RtPgMemB rtmb_sh_e42_in,
       rtmb_B_ra_e42) and its shadow hull lies in the frame's own 88 shadow bytes.
     run 2 (0x823e8 -> 0x83cc4, the plain engine): the pod's three words into e42 and a0 = pp.
     the call pod_write_ent(pp, e42) through rtsb_pwe_seq (the Section hypothesis W5B_PWE, lib/AU/PweSpec.v's
       pod_write_ent_specX at 0x83cc4); its premises at this site are rtsb_pwe_site, PweSpec's pwe_pp_of_block and
       pwe_awr_fresh, and the len cell's value.
     run 3 (0x82408 -> 0x82434, the token engine YCbq aj_run_to_tok, once for first = 0 and once for first = 1):
       the first-flag arm. Its one instrumented check is on pp's bytes and is covered by a shadow entry over them
       (w5b_shent_blk), so no error path is reached and the slow block 0x825ec falls through to the store.
     run 4 (0x82434 -> 0x8257c, the plain engine): the 13 scope stores back to 0xf8 and s8 = -8. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import PweSpec RtPgMemB RtPgStepsB RtPgW5KitB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the pod the piece writes ========================================
   e42 is the Int pod of value 7 (pod.h:413): type POD_INT, size 4, body = the four bytes of 7. Its 104 bytes in
   the frame are Layout.ent_mem e42 (the three words the code stores, then the 92 bytes the memset zeroed) and the
   16 bytes pod_write_ent appends at pp->len are Model.enc_pod e42 = Model.enc_val (Model.PInt 7). *)
Definition w5b_e42 : Model.ent := Model.Ent Model.POD_INT 4 (Cursor.le32 7).
Lemma w5b_e42_wf : Model.ent_wf w5b_e42.
Proof.
unfold Model.ent_wf, w5b_e42, Model.POD_INT. cbn [Model.e_type Model.e_size Model.e_body].
repeat split; first [lia | reflexivity].
Qed.
Lemma w5b_e42_len : pwe_len w5b_e42 = 16.
Proof. reflexivity. Qed.
Lemma w5b_e42_val : Model.enc_val (Model.PInt 7) = Model.enc_pod w5b_e42.
Proof. reflexivity. Qed.
Lemma w5b_e42_mem : Layout.ent_mem w5b_e42 =
  ((Cursor.le32 4 ++ Cursor.le32 4) ++ Cursor.le32 7) ++ repeat (Z_to_bv 8 0) 92.
Proof. reflexivity. Qed.

(* ======================================== the piece's registers and bytes ======================================== *)
(* the registers the piece may change: ra, the temporaries and the arguments (the two callees), and s2 / s6 / s8,
   which keep t0 / t4 / a4 across pod_write_ent (s8 ends at -8) *)
Definition w5bi_clob : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 22; 24; 28; 29; 30; 31]%bv.
Lemma w5bi_clob_sub : forall (l : list (bv 5)) (r : bv 5),
forallb (fun c => existsb (fun d => bv_eqb d c) w5bi_clob) l = true -> In r l -> In r w5bi_clob.
Proof.
intros l r H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as Hq. cbn beta in Hq.
apply existsb_exists in Hq as (d & Hd & Hb). apply bv_eqb_eq in Hb. subst d. exact Hd.
Qed.
Lemma w5bi_notin : forall (l : list (bv 5)) (r : bv 5), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros l r H Hin. assert (Ht : existsb (fun c => bv_eqb c r) l = true).
{ apply existsb_exists. exists r. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
rewrite H in Ht. discriminate.
Qed.
(* the bytes the piece writes: e42's 104 bytes, its 13 shadow granules, the pod at pp->len with the len cell, and
   has_params when this property is the first params one *)
Definition w5bi_E (F pp len fsv : Z) : Z -> Prop :=
fun a => (F + 0x180 <= a < F + 0x1e8) \/ (shadow_addr F + 0x30 <= a < shadow_addr F + 0x3d) \/
         pwe_E pp len w5b_e42 a \/ (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4010).

(* ======================================== engine helpers ======================================== *)
(* the frame for locals has one address under every layout of the journal (layout_le fixes ly_F) *)
Lemma w5bi_fa : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
intros n ly ly' cid pos (_ & _ & _ & _ & _ & HF & _). unfold frame_addr. rewrite HF. reflexivity.
Qed.
(* the value of a register of a run's final state *)
Ltac w5bi_reg r :=
lazymatch goal with HS : st_ok ?sg ?E ?ssf (restrict ?H ?ms) |- context [getr (ms_regs ?ms) r] =>
rewrite (st_ok_restrict_reg sg H E ssf ms r HS);
let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* the region a run's final state holds at index j *)
Ltac w5bi_region HS j Hr :=
lazymatch type of HS with st_ok _ ?E ?ssf (restrict ?H ?msf) =>
let r := eval vm_compute in (nth_error (ss_mem ssf) j) in
lazymatch r with Some ?r1 =>
pose proof (rtsb_region_nth E ssf msf j r1 H HS ltac:(vm_compute; reflexivity)) as Hr end end.
(* the byte a one-byte literal chunk of a final region holds; w is read off by computation *)
Lemma w5bi_byte : forall E H mem base o v w,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit v))) ->
bv_unsigned (byte_of_word (Z_to_bv 64 v) 0) = w ->
aview rsegs H mem (base + o) = Some w.
Proof.
intros E H mem base o v w Hc Hw. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H mem) (base + o) = Some b) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-.
cbn [option_map sv_denot]. f_equal. exact Hw.
Qed.
(* one shadow byte of the frame, from the final region based at the atom of s3 *)
Ltac w5bi_shb E HRS U19 v :=
lazymatch goal with |- aview _ ?H ?mem (?base + ?o) = _ =>
let Hck := fresh "Hck" in
assert (Hck : YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit v))))
  by (apply (rtsb_chunks E _ 19%nat _ _ _ _ _ _ HRS U19); cbn [In]; repeat (first [left; reflexivity | right]));
exact (w5bi_byte E H mem base o v _ Hck ltac:(vm_compute; reflexivity)) end.
(* the 13 shadow bytes of e42's granules *)
Ltac w5bi_sh13 E HRS U19 v :=
let o := fresh "o" in let Ho := fresh "Ho" in let Hc := fresh "Hc" in
intros o Ho;
assert (Hc : o = 48 \/ o = 49 \/ o = 50 \/ o = 51 \/ o = 52 \/ o = 53 \/ o = 54 \/ o = 55 \/ o = 56 \/ o = 57 \/
  o = 58 \/ o = 59 \/ o = 60) by lia;
repeat match goal with H : _ \/ _ |- _ => destruct H end;
subst o; w5bi_shb E HRS U19 v.
(* a 4-byte literal chunk of a final region, as a value *)
Lemma w5bi_val4 : forall E H mem base o v,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 4 (SLit v))) -> 0 <= v < 2 ^ 32 ->
val_mem rsegs (mrestrict H mem) (base + o) 4 v.
Proof.
intros E H mem base o v Hc Hv.
exact (val_of_chunk_ok rsegs E _ base o 4 (SLit v) v Hc ltac:(cbn [sv_denot]; reflexivity)
  ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(cbn; lia)).
Qed.
(* the shadow hull of a range inside the frame's 88 shadow bytes *)
Lemma w5bi_hull_in : forall F o n, F mod 32 = 0 -> 56 <= o -> 0 < n -> o + n <= 640 ->
forall s, shadow_addr (F + o) / 8 * 8 <= s < shadow_addr (F + o + n - 1) / 8 * 8 + 8 ->
shadow_addr F <= s < shadow_addr F + 88.
Proof.
intros F o n H32 Ho Hn Hon s Hs.
rewrite (rtsb_fsh_addr F o H32 ltac:(lia)) in Hs.
replace (F + o + n - 1) with (F + (o + n - 1)) in Hs by ring.
rewrite (rtsb_fsh_addr F (o + n - 1) H32 ltac:(lia)) in Hs.
assert (D0 : 7 <= o / 8) by (apply Z.div_le_lower_bound; lia).
assert (D3 : (o + n - 1) / 8 < 80) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (shadow_addr F + o / 8) 8 ltac:(lia)) as E1.
pose proof (Z.mod_pos_bound (shadow_addr F + o / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (shadow_addr F + (o + n - 1) / 8) 8 ltac:(lia)) as E2.
pose proof (Z.mod_pos_bound (shadow_addr F + (o + n - 1) / 8) 8 ltac:(lia)) as M2.
lia.
Qed.

(* ======================================== the entry states ======================================== *)
(* run 1: 0x82398 -> the memset's entry; atom 32 = the runtime's shadow offset, atom 33 = F + 0x18c (the cell
   R+0x78), the destination of the memset *)
Definition w5bi_x1 (F : Z) : list word := [w64 W5B_SB; w64 (F + 0x18c)].
Definition w5bi_r1R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x78 0x80 0 0 [YP09.mkChunk 0x78 (CVal 8 (SOff 33 0))].
Definition w5bi_r1S : YP09.region := YP09.mkRegion (Some 19%nat) 0x30 0x3d 0x30 0x3d [].
Definition w5bi_ss1 : sstate := mkSS 0x82398 sr_atoms [w5bi_r1R; w5bi_r1S] None (mkFacts [] [] []).
(* run 2: the memset's return -> pod_write_ent's entry; atom 33 = F + 0x180 (&e42, the cell R+0x80), atom 34 = pp
   (the cell R+0x168) *)
Definition w5bi_x2 (F pp : Z) : list word := [w64 W5B_SB; w64 (F + 0x180); w64 pp].
Definition w5bi_r2R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x80 0x170 0 0
    [YP09.mkChunk 0x80 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x168 (CVal 8 (SOff 34 0))].
Definition w5bi_r2F : YP09.region := YP09.mkRegion (Some 33%nat) 0 12 0 12 [].
Definition w5bi_ss2 : sstate := mkSS 0x823e8 sr_atoms [w5bi_r2R; w5bi_r2F] None (mkFacts [] [] []).
(* run 3: pod_write_ent's return -> the scope stores back; atom 33 = pp. s4 is the shadow-base atom and s9 the
   literal 1 the store writes. *)
Definition w5bi_x3 (pp : Z) : list word := [w64 W5B_SB; w64 pp].
Definition w5bi_r3R (f : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x90 0x168 0 0
    [YP09.mkChunk 0x90 (CVal 8 (SOff 33 0x400c)); YP09.mkChunk 0x160 (CVal 8 (SLit f))].
Definition w5bi_r3P (f : Z) : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0x4000 0x4018 (0x4000 + 12 * f) (0x4000 + 16 * f) [].
Definition w5bi_sr3 : list sv := sr_set (sr_set sr_atoms (20%bv : bv 5) w5b_Bx) (25%bv : bv 5) (SLit 1).
Definition w5bi_f3 : facts :=
  mkFacts [(9%nat, mkAF 4096 140737488355328 4); (32%nat, mkAF W5B_SB W5B_SB 0);
           (33%nat, mkAF 4096 140737479966720 4)] [] [].
Definition w5bi_ss3 (f : Z) : sstate := mkSS 0x82408 w5bi_sr3 [w5bi_r3R f; w5bi_r3P f] None w5bi_f3.
Definition w5bi_SH3 : list shent := [mkSHE 33 0x4000 0x4018].
(* run 4: the scope stores back -> LATCH7 *)
Definition w5bi_x4 : list word := [w64 W5B_SB].
Definition w5bi_r4S : YP09.region := YP09.mkRegion (Some 19%nat) 0x30 0x3d 0x30 0x3d [].
Definition w5bi_ss4 : sstate := mkSS 0x82434 sr_atoms [w5bi_r4S] None (mkFacts [] [] []).

(* a value kept across a run, at a state that may have grown the world *)
Lemma w5bi_val_kept : forall H mem H' mem' a n v,
val_mem rsegs (mrestrict H mem) a n v ->
(forall x, a <= x < a + Z.of_nat n -> aview rsegs H' mem' x = aview rsegs H mem x) ->
val_mem rsegs (mrestrict H' mem') a n v.
Proof.
intros H mem H' mem' a n v V K. apply rtmb_val_of_bytes.
eapply (rtmb_bytes_kept rsegs); [apply rtmb_bytes_of_val; exact V|].
rewrite length_Z_to_le_bytes. exact K.
Qed.
(* ---- the bytes written up to each stage of the walk ---- *)
Definition w5bi_W2 (R F : Z) : Z -> Prop :=
fun a => (shadow_addr F + 0x30 <= a < shadow_addr F + 0x3d) \/ (F + 0x180 <= a < F + 0x1e8) \/
         (R - 16384 <= a < R).
Definition w5bi_W3 (R F pp len : Z) : Z -> Prop := fun a => w5bi_W2 R F a \/ pwe_E pp len w5b_e42 a.
Definition w5bi_W4 (R F pp len fsv : Z) : Z -> Prop :=
fun a => w5bi_W3 R F pp len a \/ (fsv = 1 /\ pp + 0x400c <= a < pp + 0x4010).
(* a register named by Z_to_bv 5 r is the register named by the literal *)
Lemma w5bi_getr5 : forall (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z ->
getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
intros regs r z H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. subst z.
unfold bv_wrap. apply Z.mod_small. pose proof (bv_unsigned_in_range 5 r) as Hr. exact Hr.
Qed.

(* ---- what each stage of the chain leaves, as the next stage reads it ---- *)
Definition w5bi_RA (F pp len nps nr sn : Z)
: world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
  getr regs2 18 = w64 nps /\ getr regs2 22 = w64 nr /\ getr regs2 24 = w64 sn /\
  (forall o, 0x30 <= o < 0x3d -> aview rsegs (w_H W2) mem2 (shadow_addr F + o) = Some 0) /\
  (forall i, 0 <= i < 92 -> aview rsegs (w_H W2) mem2 (F + 0x18c + i) = Some 0) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 16384) 8 len.
Definition w5bi_RB (F pp len nps nr sn : Z)
: world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
  getr regs2 18 = w64 nps /\ getr regs2 22 = w64 nr /\ getr regs2 24 = w64 sn /\
  getr regs2 1 = w64 0x82408 /\ getr regs2 10 = w64 pp /\ getr regs2 11 = w64 (F + 0x180) /\
  (forall o, 0x30 <= o < 0x3d -> aview rsegs (w_H W2) mem2 (shadow_addr F + o) = Some 0) /\
  rtmb_bytes rsegs (w_H W2) mem2 (F + 0x180) (Layout.ent_mem w5b_e42) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 16384) 8 len.
Definition w5bi_RC (pp len nps nr sn : Z)
: world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
  getr regs2 18 = w64 nps /\ getr regs2 22 = w64 nr /\ getr regs2 24 = w64 sn /\
  rtmb_bytes rsegs (w_H W2) mem2 (pp + len) (Model.enc_pod w5b_e42) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 16384) 8 (len + 16).
Definition w5bi_RD (pp len fsv nps nr sn : Z)
: world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
  getr regs2 5 = w64 nps /\ getr regs2 29 = w64 nr /\ getr regs2 13 = w64 sn /\
  rtmb_bytes rsegs (w_H W2) mem2 (pp + len) (Model.enc_pod w5b_e42) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 16384) 8 (len + 16) /\
  (fsv = 1 -> rtmb_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Cursor.le32 1)).
Definition w5bi_RE (F pp len fsv nps nr sn : Z)
: world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
  getr regs2 5 = w64 nps /\ getr regs2 29 = w64 nr /\ getr regs2 13 = w64 sn /\
  getr regs2 24 = w64 (-8) /\
  rtmb_bytes rsegs (w_H W2) mem2 (pp + len) (Model.enc_pod w5b_e42) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 16384) 8 (len + 16) /\
  (fsv = 1 -> rtmb_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Cursor.le32 1)) /\
  (forall o, 0x30 <= o < 0x3d -> aview rsegs (w_H W2) mem2 (shadow_addr F + o) = Some 248).

Lemma w5bi_lenpod : Z.of_nat (length (Model.enc_pod w5b_e42)) = 16.
Proof. reflexivity. Qed.
Lemma w5bi_len4 : Z.of_nat (length (Cursor.le32 1)) = 4.
Proof. reflexivity. Qed.
(* the inclusions between the stages' write sets *)
Lemma w5bi_W2_F12 : forall R F a, F + 0x180 <= a < F + 0x18c -> w5bi_W2 R F a.
Proof. intros R F a Ha. unfold w5bi_W2. right. left. lia. Qed.
Lemma w5bi_W2_sh : forall R F a, shadow_addr F + 0x30 <= a < shadow_addr F + 0x3d -> w5bi_W2 R F a.
Proof. intros R F a Ha. unfold w5bi_W2. left. exact Ha. Qed.
Lemma w5bi_W3_W2 : forall R F pp len a, w5bi_W2 R F a -> w5bi_W3 R F pp len a.
Proof. intros R F pp len a Ha. unfold w5bi_W3. left. exact Ha. Qed.
Lemma w5bi_W3_pwe : forall R F pp len sp0 a,
pwe_E pp len w5b_e42 a \/ (sp0 + (R - sp0) - T_pwe_STK <= a < sp0 + (R - sp0)) -> w5bi_W3 R F pp len a.
Proof.
intros R F pp len sp0 a [Ha | Ha]; unfold w5bi_W3; [right; exact Ha|].
left. unfold w5bi_W2. right. right. assert (HT : T_pwe_STK = 4144) by reflexivity. lia.
Qed.
Lemma w5bi_W4_W3 : forall R F pp len fsv a, w5bi_W3 R F pp len a -> w5bi_W4 R F pp len fsv a.
Proof. intros R F pp len fsv a Ha. unfold w5bi_W4. left. exact Ha. Qed.
Lemma w5bi_W4_hp : forall R F pp len fsv a,
fsv = 1 /\ pp + 0x400c <= a < pp + 0x4010 -> w5bi_W4 R F pp len fsv a.
Proof. intros R F pp len fsv a Ha. unfold w5bi_W4. right. exact Ha. Qed.
Lemma w5bi_W4_sh : forall R F pp len fsv a,
shadow_addr F + 0x30 <= a < shadow_addr F + 0x3d -> w5bi_W4 R F pp len fsv a.
Proof.
intros R F pp len fsv a Ha. apply w5bi_W4_W3. apply w5bi_W3_W2. apply w5bi_W2_sh. exact Ha.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* checked_memset (0x51d54), the kernel's contract of the intrinsic *)
Hypothesis W5B_AMEMSET : aintrin_realizes rsegs B OSet 0x51d54.
(* pod_write_ent (0x83cc4), lib/AU/PweSpec.v's contract *)
Hypothesis W5B_PWE : pod_write_ent_specX rsegs B MT PWE_ENT.

(* ======================================== what every run of the piece takes ========================================
   the harness's journal from the segment's start, the real frame [R, R + 0x220) inside the journal's stack window
   with the callees' stack below it, and the frame for locals F = the side-stack frame (4, pos) the harness holds *)
Definition w5bi_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 16 = 0 /\ R + 0x220 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos.

(* the facts of the frame for locals and of the real frame that every run re-derives *)
Lemma w5bi_frame : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
w5bi_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
F mod 32 = 0 /\ in_app F 1024 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\
0 <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\
(forall a, F <= a < F + 1024 -> apresent (w_H W) memc a) /\
(forall i, 0 <= i < 128 -> apresent (w_H W) memc (shadow_addr F + i)) /\
In (4, pos) (frames Sc) /\ alloc_ceiling + 16384 <= R /\ R <= 140737488355328 /\ sp0 mod 16 = 0.
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos (HJ & HR16 & HRs & HRlo & Hown & Hfeq).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (Hal32 & Happ & Hfr4 & Hfsh4).
rewrite <- Hfeq in Hal32, Happ, Hfr4, Hfsh4.
change (fs_frame_bytes 4) with 1024 in Happ, Hfr4. change (fs_frame_bytes 4 / 8) with 128 in Hfsh4.
destruct (rtsb_fbounds F Hal32 Happ) as (HF0 & HFc & Hsa0 & Hsac & Hsep & _).
unfold T_SEG_STK, ASTACK in *.
split; [exact Hal32|]. split; [exact Happ|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hsep|].
split; [intros a Ha; exact (proj1 (Hfr4 a Ha))|].
split; [intros i Hi; exact (proj1 (Hfsh4 i Hi))|].
split; [exact Hin4|]. split; [lia|]. split; [lia | exact Hsp0al].
Qed.
(* the first block, as the piece reads it *)
Lemma w5bi_blk : forall ly S W mem md pp,
AR rsegs B ly S W mem md -> In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
4096 <= pp /\ pp mod 16 = 0 /\ pp mod 8 = 0 /\ pp + 19744 <= alloc_ceiling /\ in_app pp Layout.PP_SIZE /\
(forall a, pp <= a < pp + 19744 -> apresent (w_H W) mem a).
Proof using LAWS.
intros ly S W mem md pp HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md pp Layout.PP_SIZE HAR Hin) as (H16 & H4096 & Hceil & Happ & Hpres & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hceil, Hpres.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (H8 : pp mod 8 = 0).
{ rewrite (Z.div_mod pp 16) by lia. rewrite H16, Z.add_0_r.
  replace (16 * (pp / 16)) with ((2 * (pp / 16)) * 8) by lia. apply Z.mod_mul. lia. }
assert (HPV : Layout.PP_SIZE = 19744) by reflexivity. rewrite HPV in Hceil, Hpres.
split; [lia|]. split; [exact H16|]. split; [exact H8|]. split; [lia|]. split; [rewrite <- Hrq; exact Happ|].
intros a Ha. exact (proj1 (Hpres a Ha)).
Qed.
(* a shadow byte of the frame is no byte of the first block (the shadow band is apart from application memory) *)
Lemma w5bi_sep_sh_blk : forall F pp i, F mod 32 = 0 -> 4096 <= F -> F + 1024 <= alloc_ceiling ->
in_app pp Layout.PP_SIZE -> 0 <= i < 128 -> ~ (pp <= shadow_addr F + i < pp + 19744).
Proof.
intros F pp i H32 HF0 HFc Happ Hi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hx : shadow_addr F + i = shadow_of_addr SHADOW_OFF (F + 8 * i)).
{ rewrite (rtsb_fsh_of F (8 * i)) by lia. f_equal.
  replace (8 * i) with (i * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
rewrite Hx. change 19744 with Layout.PP_SIZE.
apply (rtmb_shadow_not_app (F + 8 * i) pp Layout.PP_SIZE); [|exact Happ].
unfold kHighMemEnd. lia.
Qed.

(* ======================================== run 1: 0x82398 -> 0x51d54 ======================================== *)
Lemma w5bi_b1 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos nps nr sn : Z),
w5bi_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 5 = w64 nps -> getr regs 29 = w64 nr -> getr regs 14 = w64 sn ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (F + 0x18c) ->
0 <= nps < 2 ^ 64 -> 0 <= nr < 2 ^ 64 -> 0 <= sn < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs 0x82398 regs memc mdc)
 (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x51d54
   [1; 10; 11; 12; 18; 22; 24]%bv
   (fun a => shadow_addr F + 0x30 <= a < shadow_addr F + 0x3d)
   (fun W2 regs2 mem2 =>
      getr regs2 1 = w64 0x823e8 /\ getr regs2 10 = w64 (F + 0x18c) /\ getr regs2 11 = w64 0 /\
      getr regs2 12 = w64 92 /\ getr regs2 18 = w64 nps /\ getr regs2 22 = w64 nr /\ getr regs2 24 = w64 sn /\
      getr regs2 2 = getr regs 2 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
      getr regs2 9 = getr regs 9 /\ getr regs2 19 = getr regs 19 /\ getr regs2 20 = getr regs 20 /\
      getr regs2 25 = getr regs 25 /\
      (forall o, 0x30 <= o < 0x3d -> aview rsegs (w_H W2) mem2 (shadow_addr F + o) = Some 0))).
Proof using LAWS MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos nps nr sn
  Hctx H9 H19 H5 H29 H14 V78 Hnps Hnr Hsn.
pose proof Hctx as (HJ & HR16 & HRs & HRlo & Hown & Hfeq).
pose proof (w5bi_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx)
  as (Hal32 & Happ & HF0 & HFc & Hsa0 & Hsac & Hsep & Hfrb & Hfshb & Hin4 & Hrlo & Hr47 & Hsp0al).
pose proof w5b_wx as Hwx. pose proof w5b_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs (w5bi_x1 F)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = w64 (shadow_addr F)) by (subst E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E5 : ew E 5 = w64 nps) by (subst E; rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact H5).
assert (E29 : ew E 29 = w64 nr) by (subst E; rewrite (ew_Ereg_nat regs _ 29 29%bv eq_refl); exact H29).
assert (E14 : ew E 14 = w64 sn) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E33 : ew E 33 = w64 (F + 0x18c)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (HE : E = Ereg regs (w5bi_x1 F)) by reflexivity.
assert (HAE : env_agree 32 (Ereg regs (w5bi_x1 F)) E) by (rewrite HE; apply env_agree_refl).
clearbody E.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr F) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = F + 0x18c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E w5bi_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82398) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w5bi_ss1.
  apply (w5b_entry rsegs _ _ regs (w5bi_x1 F) E); [exact HE | | | | |].
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold w5bi_r1R, w5bi_r1S. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ R 0x78 8 (SOff 33 0) (F + 0x18c));
        [ rewrite (w5b_den_off E 33 (F + 0x18c) 0 E33) by lia; rewrite Z.add_0_r; reflexivity
        | change (8 * Z.of_N 8) with 64; lia | lia | exact V78 ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 19 (shadow_addr F));
        [ exact U19 | lia | lia | intros o Ho; apply Hfshb; lia | apply Forall_nil ].
  - unfold w5bi_r1R, w5bi_r1S; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U9, U19; repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x82398) with (Z_to_bv 64 0x82398).
aj_run_to w5b_tbl_ok HS HJ 0x51d54.
{ change (ss_mem w5bi_ss1) with [w5bi_r1R; w5bi_r1S]. unfold w5bi_r1R, w5bi_r1S.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (rtsb_awr_ok_fsh E _ _ STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own 19%nat pos);
    [ reflexivity | cbn [YP09.r_base]; rewrite U19, Hfeq; reflexivity | exact Hown
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil ]. }
w5bi_region HS 1%nat HRS.
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [1; 10; 11; 12; 18; 22; 24]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ eapply (regs_kept_of_st_ok rsegs E _ ms regs (w5bi_x1 F) (w_H W) [1; 10; 11; 12; 18; 22; 24]%bv HS HAE).
  vm_compute. reflexivity. }
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [exact RK|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [apply w5b_same_io_wvb|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hn. apply (w5b_kept_run rsegs E (ss_mem w5bi_ss1) (w_H W) memc (ms_mem ms) a HFr Ha).
  intros (r & Hr & Hb). change (ss_mem w5bi_ss1) with [w5bi_r1R; w5bi_r1S] in Hr.
  unfold w5bi_r1R, w5bi_r1S in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; [lia|]. rewrite U19 in Hb. apply Hn. lia. }
split; [w5bi_reg (1%bv : bv 5); reflexivity|].
split; [w5bi_reg (10%bv : bv 5); rewrite (w5b_den_off E 33 (F + 0x18c) 0 E33) by lia; rewrite Z.add_0_r; reflexivity|].
split; [w5bi_reg (11%bv : bv 5); reflexivity|].
split; [w5bi_reg (12%bv : bv 5); reflexivity|].
split; [w5bi_reg (18%bv : bv 5); rewrite (w5b_den_off E 5 nps 0 E5) by lia; rewrite Z.add_0_r; reflexivity|].
split; [w5bi_reg (22%bv : bv 5); rewrite (w5b_den_off E 29 nr 0 E29) by lia; rewrite Z.add_0_r; reflexivity|].
split; [w5bi_reg (24%bv : bv 5); rewrite (w5b_den_off E 14 sn 0 E14) by lia; rewrite Z.add_0_r; reflexivity|].
split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
w5bi_sh13 E HRS U19 0.
Qed.

(* ======================================== run 2: 0x823e8 -> 0x83cc4 ======================================== *)
Lemma w5bi_b2 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pp pos : Z),
w5bi_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) ->
getr regs 9 = w64 R ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 (F + 0x180) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
SRr rsegs W (cfg_at rsegs 0x823e8 regs memc mdc)
 (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x83cc4
   [1; 10; 11]%bv
   (fun a => F + 0x180 <= a < F + 0x18c)
   (fun W2 regs2 mem2 =>
      getr regs2 1 = w64 0x82408 /\ getr regs2 10 = w64 pp /\ getr regs2 11 = w64 (F + 0x180) /\
      getr regs2 2 = getr regs 2 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
      getr regs2 9 = getr regs 9 /\ getr regs2 19 = getr regs 19 /\ getr regs2 20 = getr regs 20 /\
      getr regs2 25 = getr regs 25 /\ getr regs2 18 = getr regs 18 /\ getr regs2 22 = getr regs 22 /\
      getr regs2 24 = getr regs 24 /\
      rtmb_bytes rsegs (w_H W2) mem2 (F + 0x180) ((Cursor.le32 4 ++ Cursor.le32 4) ++ Cursor.le32 7))).
Proof using LAWS MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pp pos Hctx Hpp H9 V80 V168.
pose proof Hctx as (HJ & HR16 & HRs & HRlo & Hown & Hfeq).
pose proof (w5bi_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx)
  as (Hal32 & Happ & HF0 & HFc & Hsa0 & Hsac & Hsep & Hfrb & Hfshb & Hin4 & Hrlo & Hr47 & Hsp0al).
pose proof HJ as (HAR & _).
destruct (w5bi_blk lyc Sc W memc mdc pp HAR Hpp) as (Hpp0 & Hpp16 & Hpp8 & Hppc & Hppapp & Hppres).
pose proof w5b_wx as Hwx. pose proof w5b_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs (w5bi_x2 F pp)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E33 : ew E 33 = w64 (F + 0x180)) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (HE : E = Ereg regs (w5bi_x2 F pp)) by reflexivity.
assert (HAE : env_agree 32 (Ereg regs (w5bi_x2 F pp)) E) by (rewrite HE; apply env_agree_refl).
clearbody E.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = F + 0x180) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = pp) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E w5bi_ss2 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x823e8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w5bi_ss2.
  apply (w5b_entry rsegs _ _ regs (w5bi_x2 F pp) E); [exact HE | | | | |].
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold w5bi_r2R, w5bi_r2F. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs E _ R 0x80 8 (SOff 33 0) (F + 0x180));
          [ rewrite (w5b_den_off E 33 (F + 0x180) 0 E33) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V80 ].
      * apply (chunk_ok_val rsegs E _ R 0x168 8 (SOff 34 0) pp);
          [ rewrite (w5b_den_off E 34 pp 0 E34) by lia; rewrite Z.add_0_r; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia | exact V168 ].
    + apply (rtmb_rw_region rsegs E (w_H W) memc 33 (F + 0x180));
        [ exact U33 | lia | lia | intros o Ho; apply Hfrb; lia | apply Forall_nil ].
  - unfold w5bi_r2R, w5bi_r2F; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U9, U33; repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x823e8) with (Z_to_bv 64 0x823e8).
aj_run_to w5b_tbl_ok HS HJ 0x83cc4.
{ change (ss_mem w5bi_ss2) with [w5bi_r2R; w5bi_r2F]. unfold w5bi_r2R, w5bi_r2F.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply (rtsb_awr_ok_fobj E _ _ STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own 33%nat pos 0x180);
    [ reflexivity | cbn [YP09.r_base]; rewrite U33, Hfeq; reflexivity | exact Hown
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil ]. }
w5bi_region HS 1%nat HRF.
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [1; 10; 11]%bv -> getr (ms_regs ms) r = getr regs r).
{ eapply (regs_kept_of_st_ok rsegs E _ ms regs (w5bi_x2 F pp) (w_H W) [1; 10; 11]%bv HS HAE).
  vm_compute. reflexivity. }
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [exact RK|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [apply w5b_same_io_wvb|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hn. apply (w5b_kept_run rsegs E (ss_mem w5bi_ss2) (w_H W) memc (ms_mem ms) a HFr Ha).
  intros (r & Hr & Hb). change (ss_mem w5bi_ss2) with [w5bi_r2R; w5bi_r2F] in Hr.
  unfold w5bi_r2R, w5bi_r2F in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; [lia|]. rewrite U33 in Hb. apply Hn. lia. }
split; [w5bi_reg (1%bv : bv 5); reflexivity|].
split; [w5bi_reg (10%bv : bv 5); rewrite (w5b_den_off E 34 pp 0 E34) by lia; rewrite Z.add_0_r; reflexivity|].
split; [w5bi_reg (11%bv : bv 5); rewrite (w5b_den_off E 33 (F + 0x180) 0 E33) by lia; rewrite Z.add_0_r; reflexivity|].
do 10 (split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|]).
(* the three words of e42's header and body *)
assert (Vt : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x180 + 0) 4 4).
{ apply (w5bi_val4 E (w_H W) (ms_mem ms) (F + 0x180) 0 4); [|lia].
  apply (rtsb_chunks E _ 33%nat _ _ _ _ _ _ HRF U33); cbn [In]; repeat (first [left; reflexivity | right]). }
assert (Vs : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x180 + 4) 4 4).
{ apply (w5bi_val4 E (w_H W) (ms_mem ms) (F + 0x180) 4 4); [|lia].
  apply (rtsb_chunks E _ 33%nat _ _ _ _ _ _ HRF U33); cbn [In]; repeat (first [left; reflexivity | right]). }
assert (Vb : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x180 + 8) 4 7).
{ apply (w5bi_val4 E (w_H W) (ms_mem ms) (F + 0x180) 8 7); [|lia].
  apply (rtsb_chunks E _ 33%nat _ _ _ _ _ _ HRF U33); cbn [In]; repeat (first [left; reflexivity | right]). }
apply rtmb_bytes_app. split.
{ apply rtmb_bytes_app. split.
  - rewrite Z.add_0_r in Vt. exact (rtmb_bytes_of_val rsegs _ _ _ 4 4 Vt).
  - change (Z.of_nat (length (Cursor.le32 4))) with 4. exact (rtmb_bytes_of_val rsegs _ _ _ 4 4 Vs). }
change (Z.of_nat (length (Cursor.le32 4 ++ Cursor.le32 4))) with 8.
exact (rtmb_bytes_of_val rsegs _ _ _ 4 7 Vb).
Qed.

(* ======================================== run 3: 0x82408 -> 0x82434 ======================================== *)
Lemma w5bi_b3 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pp pos fsv sn nps nr : Z),
w5bi_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 9 = w64 R -> getr regs 20 = w64 SHADOW_OFF -> getr regs 25 = w64 1 ->
getr regs 18 = w64 nps -> getr regs 22 = w64 nr -> getr regs 24 = w64 sn ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x90) 8 (pp + 0x400c) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x160) 8 fsv ->
(fsv = 0 \/ fsv = 1) -> 0 <= nps < 2 ^ 64 -> 0 <= nr < 2 ^ 64 -> 0 <= sn < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs 0x82408 regs memc mdc)
 (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82434
   [5; 10; 11; 12; 13; 29]%bv
   (fun a => fsv = 1 /\ pp + 0x400c <= a < pp + 0x4010)
   (fun W2 regs2 mem2 =>
      getr regs2 5 = w64 nps /\ getr regs2 29 = w64 nr /\ getr regs2 13 = w64 sn /\
      getr regs2 19 = getr regs 19 /\ getr regs2 24 = getr regs 24 /\
      (fsv = 1 -> rtmb_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Cursor.le32 1)))).
Proof using LAWS MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pp pos fsv sn nps nr
  Hctx Hpp Hfresh H9 H20 H25 H18 H22 H24 V90 V160 Hfsv Hnps Hnr Hsn.
pose proof Hctx as (HJ & HR16 & HRs & HRlo & Hown & Hfeq).
pose proof (w5bi_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx)
  as (Hal32 & Happ & HF0 & HFc & Hsa0 & Hsac & Hsep & Hfrb & Hfshb & Hin4 & Hrlo & Hr47 & Hsp0al).
pose proof HJ as (HAR & _).
destruct (w5bi_blk lyc Sc W memc mdc pp HAR Hpp) as (Hpp0 & Hpp16 & Hpp8 & Hppc & Hppapp & Hppres).
pose proof w5b_wx as Hwx. pose proof w5b_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HPS : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
assert (HPV : Layout.PP_SIZE = 19744) by reflexivity.
set (E := Ereg regs (w5bi_x3 pp)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = w64 nps) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E22 : ew E 22 = w64 nr) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = w64 sn) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 W5B_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 pp) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (HE : E = Ereg regs (w5bi_x3 pp)) by reflexivity.
assert (HAE : env_agree 32 (Ereg regs (w5bi_x3 pp)) E) by (rewrite HE; apply env_agree_refl).
clearbody E.
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = W5B_SB) by (rewrite E32; apply unsigned_lit_small; unfold W5B_SB; lia).
assert (U33 : bv_unsigned (ew E 33) = pp) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Hsh : sh_ok rsegs w5b_Bx w5bi_SH3 E (mrestrict (w_H W) memc)).
{ constructor; [|constructor].
  apply (w5b_shent_blk B LAWS lyc Sc W memc mdc pp Layout.PP_SIZE E 33 0x4000 0x4018 pp);
  try assumption; rewrite ?HPS, ?HPV; lia. }
assert (HR0 : regs_ok E w5bi_sr3 regs).
{ unfold w5bi_sr3. apply w5b_regs_ok_override; [apply w5b_regs_ok_override| |].
  - rewrite HE. apply regs_ok_Ereg.
  - apply w5b_nz. vm_compute. lia.
  - unfold w5b_Bx. rewrite (w5b_den_off E 32 W5B_SB 0 E32) by (unfold W5B_SB; lia).
    rewrite Z.add_0_r, H20. reflexivity.
  - apply w5b_nz. vm_compute. lia.
  - cbn [sv_denot]. rewrite H25. reflexivity. }
assert (HFK : facts_ok E w5bi_f3).
{ split; [|split; [exact I | exact I]].
  cbn [w5bi_f3 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U32, U33.
  repeat split; first [ lia | (unfold W5B_SB; lia) | (change (2 ^ 4) with 16; assumption)
                      | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity) ]. }
destruct Hfsv as [-> | ->].
all: lazymatch goal with Vd : val_mem _ _ (_ + 0x160) 8 ?f |- _ =>
  assert (HS : st_ok rsegs E (w5bi_ss3 f) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82408) memc (seg_rom rsegs))));
  [ rewrite restrict_mkst_fx; unfold w5bi_ss3;
    apply (w5b_entry rsegs _ _ regs (w5bi_x3 pp) E); [exact HE | | | | |];
    [ exact HR0
    | vm_compute; reflexivity
    | unfold w5bi_r3R, w5bi_r3P; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (rtmb_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |];
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        [ apply (chunk_ok_val rsegs E _ R 0x90 8 (SOff 33 0x400c) (pp + 0x400c));
            [ rewrite (w5b_den_off E 33 pp 0x400c E33) by lia; reflexivity
            | change (8 * Z.of_N 8) with 64; lia | lia | exact V90 ]
        | apply (chunk_ok_val rsegs E _ R 0x160 8 (SLit f) f);
            [ reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vd ] ]
      | apply (rtmb_rw_region rsegs E (w_H W) memc 33 pp);
          [ exact U33 | lia | lia | intros o Ho; apply Hppres; cbn [YP09.r_wlo YP09.r_whi] in Ho; lia
          | apply Forall_nil ] ]
    | unfold w5bi_r3R, w5bi_r3P; cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U9, U33; repeat split; lia
    | exact HFK ]
  | ] end.
all: unfold cfg_at; change (w64 0x82408) with (Z_to_bv 64 0x82408).
all: aj_run_to_tok w5b_tbl_ok HS HJ Hsh w5b_Bspan 0x82434.
all: try (lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 33%nat pp);
    [ reflexivity | exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
      replace a with (pp + (a - pp)) by lia;
      apply (rt_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hpp | exact Hfresh | rewrite HPS, HPV; lia]
    | ] ]).
all: lazymatch goal with HSf : st_ok _ ?Ef _ (restrict _ _) |- _ =>
  assert (HA : env_agree 34 E Ef) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  assert (F18 : ew Ef 18 = w64 nps) by (etransitivity; [apply (proj1 HA); lia | exact E18]);
  assert (F22 : ew Ef 22 = w64 nr) by (etransitivity; [apply (proj1 HA); lia | exact E22]);
  assert (F24 : ew Ef 24 = w64 sn) by (etransitivity; [apply (proj1 HA); lia | exact E24]);
  assert (F33 : bv_unsigned (ew Ef 33) = pp)
    by (etransitivity; [f_equal; apply (proj1 HA); lia | exact U33]);
  pose proof HSf as (_ & _ & _ & _ & _ & _ & HRf & _); cbn [ms_regs restrict] in HRf end.
all: w5bi_region HS 1%nat HRP.
all: apply SRr_ret; red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists.
all: split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
all: split; [exact HJ|].
all: assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [5; 10; 11; 12; 13; 29]%bv ->
       getr (ms_regs ms) r = getr regs r)
     by (lazymatch goal with HSf : st_ok _ ?Ef ?ssf _ |- _ =>
           exact (w5b_regs_kept E Ef 34 w5bi_sr3 (ss_regs ssf) regs (ms_regs ms) [5; 10; 11; 12; 13; 29]%bv
                    HR0 HRf HA ltac:(vm_compute; reflexivity)) end).
all: split; [exact RK|].
all: split; [reflexivity|].
all: split; [apply Permutation_refl|].
all: split; [first [apply same_io_refl | apply w5b_same_io_wvb]|].
all: split; [apply mo_le_refl; exact MTL|].
all: split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
    apply (w5b_kept_run rsegs E _ (w_H W) memc (ms_mem ms) a HFr Ha);
    let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in intros (r & Hr & Hb);
    lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
    cbn [In] in Hr; destruct Hr as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U33 in Hb;
    first [lia | (apply Hn; split; [reflexivity | lia])]
  |].
all: split;
  [ w5bi_reg (5%bv : bv 5); rewrite (w5b_den_off _ 18 nps 0 F18) by lia; rewrite Z.add_0_r; reflexivity |].
all: split;
  [ w5bi_reg (29%bv : bv 5); rewrite (w5b_den_off _ 22 nr 0 F22) by lia; rewrite Z.add_0_r; reflexivity |].
all: split;
  [ w5bi_reg (13%bv : bv 5); rewrite (w5b_den_off _ 24 sn 0 F24) by lia; rewrite Z.add_0_r; reflexivity |].
all: split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
all: split; [apply RK; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]|].
- intros Hf1. discriminate Hf1.
- intros _. apply rtmb_bytes_of_val.
  lazymatch goal with HSf : st_ok _ ?Ef _ _ |- _ =>
    apply (w5bi_val4 Ef (w_H W) (ms_mem ms) pp 0x400c 1); [|lia];
    apply (rtsb_chunks Ef _ 33%nat _ _ _ _ _ _ HRP F33) end;
  cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* ======================================== run 4: 0x82434 -> 0x8257c ======================================== *)
Lemma w5bi_b4 : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos : Z),
w5bi_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 19 = w64 (shadow_addr F) ->
SRr rsegs W (cfg_at rsegs 0x82434 regs memc mdc)
 (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x8257c
   [10; 24]%bv
   (fun a => shadow_addr F + 0x30 <= a < shadow_addr F + 0x3d)
   (fun W2 regs2 mem2 =>
      getr regs2 24 = w64 (-8) /\
      (forall o, 0x30 <= o < 0x3d -> aview rsegs (w_H W2) mem2 (shadow_addr F + o) = Some 248))).
Proof using LAWS MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H19.
pose proof Hctx as (HJ & HR16 & HRs & HRlo & Hown & Hfeq).
pose proof (w5bi_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx)
  as (Hal32 & Happ & HF0 & HFc & Hsa0 & Hsac & Hsep & Hfrb & Hfshb & Hin4 & Hrlo & Hr47 & Hsp0al).
pose proof w5b_wx as Hwx. pose proof w5b_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs w5bi_x4).
assert (E19 : ew E 19 = w64 (shadow_addr F)) by (subst E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HE : E = Ereg regs w5bi_x4) by reflexivity.
assert (HAE : env_agree 32 (Ereg regs w5bi_x4) E) by (rewrite HE; apply env_agree_refl).
clearbody E.
assert (U19 : bv_unsigned (ew E 19) = shadow_addr F) by (rewrite E19; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E w5bi_ss4 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82434) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w5bi_ss4.
  apply (w5b_entry rsegs _ _ regs w5bi_x4 E); [exact HE | | | | |].
  - rewrite HE. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold w5bi_r4S. apply Forall_cons; [|apply Forall_nil].
    apply (rtmb_rw_region rsegs E (w_H W) memc 19 (shadow_addr F));
      [ exact U19 | lia | lia | intros o Ho; apply Hfshb; lia | apply Forall_nil ].
  - unfold w5bi_r4S; cbn [pairwise_disjoint all_disjoint]; repeat split.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x82434) with (Z_to_bv 64 0x82434).
aj_run_to w5b_tbl_ok HS HJ 0x8257c.
{ change (ss_mem w5bi_ss4) with [w5bi_r4S]. unfold w5bi_r4S.
  apply (rtsb_awr_ok_fsh E _ _ STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own 19%nat pos);
    [ reflexivity | cbn [YP09.r_base]; rewrite U19, Hfeq; reflexivity | exact Hown
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil ]. }
w5bi_region HS 0%nat HRS.
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [10; 24]%bv -> getr (ms_regs ms) r = getr regs r).
{ eapply (regs_kept_of_st_ok rsegs E _ ms regs w5bi_x4 (w_H W) [10; 24]%bv HS HAE).
  vm_compute. reflexivity. }
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [exact RK|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [apply w5b_same_io_wvb|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hn. apply (w5b_kept_run rsegs E (ss_mem w5bi_ss4) (w_H W) memc (ms_mem ms) a HFr Ha).
  intros (r & Hr & Hb). change (ss_mem w5bi_ss4) with [w5bi_r4S] in Hr.
  unfold w5bi_r4S in Hr. cbn [In] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite U19 in Hb. apply Hn. lia. }
split.
{ w5bi_reg (24%bv : bv 5). cbn [sv_denot]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
w5bi_sh13 E HRS U19 18446744073709551608.
Qed.
(* ======================================== the chain's normaliser ========================================
   A stage's post, read at the piece's clobber list and at the bytes written so far: a register outside the
   piece's list is one the stage kept, a byte outside the stage's own write set is one it kept, and the stage's
   result is re-read with its kept clauses in hand. *)
Lemma w5bi_mono : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob'
  (Wr Wr' : Z -> Prop) R R' W2 c2,
(forall r : bv 5, In r clob -> In r clob') ->
(forall a, Wr a -> Wr' a) ->
(forall W3 regs3 mem3,
   (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W) memc a) ->
   (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs3 r = getr regs r) ->
   R W3 regs3 mem3 -> R' W3 regs3 mem3) ->
rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr R W2 c2 ->
rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob' Wr' R' W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob' Wr Wr' R R' W2 c2
  HC HW HR (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & Hk & Hf & Hp & Hio & Hmo & Hm & HRv).
exists ly2, S2, regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; apply Hk; [exact Hr0 | intros X; exact (Hn (HC r X))]|].
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|].
split; [intros a Ha Hn; apply Hm; [exact Ha | intros X; exact (Hn (HW a X))]|].
exact (HR W2 regs2 mem2 Hm Hk HRv).
Qed.

(* ======================================== the core walk ========================================
   The four runs and the two calls, chained with rtsb_post_seq / rtsb_intrin_seq / rtsb_pwe_at. Each stage is
   normalised to the piece's clobber list and to the bytes written so far, so the next stage reads the real-frame
   cells it needs back out of that stage's own kept clause. *)
Lemma w5b_int_core : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pp pos len fsv sn nps nr : Z),
w5bi_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
st_nev S + k <= EV_MAX ->
getr regs 2 = w64 R -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 20 = w64 SHADOW_OFF ->
getr regs 5 = w64 nps -> getr regs 29 = w64 nr -> getr regs 14 = w64 sn -> getr regs 25 = w64 1 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x78) 8 (F + 0x18c) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 (F + 0x180) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x90) 8 (pp + 0x400c) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x160) 8 fsv ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x168) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + Layout.OFF_LEN) 8 len ->
rt_fsh rsegs (w_H W) memc F (rtmb_sh false false false false false false false) ->
0 <= len -> len mod 8 = 0 -> len + 16 <= Layout.POD_BUF_MAX ->
(fsv = 0 \/ fsv = 1) -> 0 <= nps < 2 ^ 64 -> 0 <= nr < 2 ^ 64 -> 0 <= sn < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs 0x82398 regs memc mdc)
  (w5b_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x8257c w5bi_clob
     (w5bi_E F pp len fsv)
     (fun W2 regs2 mem2 =>
        rtmb_bytes rsegs (w_H W2) mem2 (pp + len) (Model.enc_pod w5b_e42) /\
        val_mem rsegs (mrestrict (w_H W2) mem2) (pp + Layout.OFF_LEN) 8 (len + 16) /\
        (fsv = 1 -> rtmb_bytes rsegs (w_H W2) mem2 (pp + 0x400c) (Cursor.le32 1)) /\
        rt_fsh rsegs (w_H W2) mem2 F (rtmb_sh false false false false false false false) /\
        getr regs2 5 = w64 nps /\ getr regs2 29 = w64 nr /\ getr regs2 13 = w64 sn /\
        getr regs2 24 = w64 (-8))).
Proof using MTL LAWS W5B_AMEMSET W5B_PWE.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pp pos len fsv sn nps nr
  Hctx Hpp Hfresh Hnev H2 H3 H4 H9 H19 H20 H5 H29 H14 H25 V78 V80 V90 V160 V168 VLEN HFSH0
  Hlen0 Hlen8 HlenB Hfsv Hnps Hnr Hsn.
pose proof Hctx as (HJ & HR16 & HRs & HRlo & Hown & Hfeq).
pose proof (w5bi_frame STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos Hctx)
  as (Hal32 & Happ & HF0 & HFc & Hsa0 & Hsac & Hsep & Hfrb & Hfshb & Hin4 & Hrlo & Hr47 & Hsp0al).
pose proof HJ as (HAR & Hly & _).
destruct (w5bi_blk lyc Sc W memc mdc pp HAR Hpp) as (Hpp0 & Hpp16 & Hpp8 & Hppc & Hppapp & Hppres).
destruct (rtsb_fbounds F Hal32 Happ) as (_ & _ & _ & _ & _ & Hamr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
assert (HTP : T_pwe_STK = 4144) by reflexivity.
assert (HPV : Layout.PP_SIZE = 19744) by reflexivity.
assert (HOL : Layout.OFF_LEN = 16384) by reflexivity.
assert (HPB : Layout.POD_BUF_MAX = 16384) by reflexivity.
assert (HEN : Layout.ENT_SIZE = 104) by reflexivity.
assert (HPL : pwe_len w5b_e42 = 16) by exact w5b_e42_len.
assert (Hspz : spZ regs = R) by (unfold spZ; rewrite H2; apply unsigned_lit_small; lia).
rewrite HOL in VLEN. rewrite HPB in HlenB.
(* the frame keeps one address under every layout of the journal; its bytes and its shadow stay present *)
assert (FA : forall ly2 S2 W2 mem2 md2,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k -> frame_addr ly2 4 pos = F).
{ intros ly2 S2 W2 mem2 md2 HJ2. pose proof HJ2 as (_ & Hly2 & _).
  rewrite (w5bi_fa _ ly ly2 4 pos Hly2), Hfeq, (w5bi_fa _ ly lyc 4 pos Hly). reflexivity. }
assert (FSHP : forall ly2 S2 W2 mem2 md2,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
  (forall i, 0 <= i < 128 -> apresent (w_H W2) mem2 (shadow_addr F + i)) /\
  (forall a, F <= a < F + 1024 -> apresent (w_H W2) mem2 a)).
{ intros ly2 S2 W2 mem2 md2 HJ2. pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
  assert (Hin2 : In (4, pos) (frames S2)) by (rewrite Hfrs2; apply in_or_app; left; exact Hown).
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin2) as (_ & _ & Hfr & Hfsh).
  rewrite (FA ly2 S2 W2 mem2 md2 HJ2) in Hfr, Hfsh.
  change (fs_frame_bytes 4) with 1024 in Hfr. change (fs_frame_bytes 4 / 8) with 128 in Hfsh.
  split; [intros i Hi; exact (proj1 (Hfsh i Hi)) | intros a Ha; exact (proj1 (Hfr a Ha))]. }
(* the first block is apart from the frame for locals and from the frame's shadow *)
assert (Hbf : pp + 19744 <= F \/ F + 1024 <= pp).
{ pose proof (sep_block_frame rsegs B LAWS lyc Sc W memc mdc pp Layout.PP_SIZE 4 pos HAR Hpp Hin4) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz.
  change (req_size Layout.PP_SIZE) with 19744 in Hz. change (fs_frame_bytes 4) with 1024 in Hz.
  rewrite (FA lyc Sc W memc mdc HJ) in Hz. lia. }
assert (Hal8 : F mod 8 = 0).
{ destruct (rtsb_fdiv F Hal32) as [E1 _]. rewrite E1.
  replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring. apply Z_mod_mult. }
assert (Hbs : forall i, 0 <= i < 128 -> ~ (pp <= shadow_addr F + i < pp + 19744)).
{ intros i Hi. exact (w5bi_sep_sh_blk F pp i Hal32 HF0 HFc Hppapp Hi). }
(* ---------------- stage 1: run 1 and the memset, 0x82398 -> 0x823e8 ---------------- *)
assert (HA : SRr rsegs W (cfg_at rsegs 0x82398 regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x823e8 w5bi_clob
     (w5bi_W2 R F) (w5bi_RA F pp len nps nr sn))).
{ eapply SRr_mono.
  { eapply (rtsb_intrin_seq B MT LAWS OSet 0x51d54 0x823e8 W5B_AMEMSET).
    - exact (w5bi_b1 STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos nps nr sn
               Hctx H9 H19 H5 H29 H14 V78 Hnps Hnr Hsn).
    - intros ly1 S1 W1 regs1 mem1 md1 HJ1
        (T1 & T10 & T11 & T12 & T18 & T22 & T24 & T2 & T3 & T4 & T9 & T19 & T20 & T25 & TSH).
      destruct (FSHP ly1 S1 W1 mem1 md1 HJ1) as (PSH1 & _).
      split; [exact T10|]. split; [exact T11|]. split; [exact T12|].
      split; [unfold spZ; rewrite T2, H2; replace (sp0 + (R - sp0)) with R by ring;
              apply unsigned_lit_small; lia|].
      split; [rewrite T3; exact H3|]. split; [rewrite T4; exact H4|]. split; [exact T1|].
      split.
      { intros a Ha. split.
        - apply (rtsb_awr_fobj STK sp0 FP (ablocks B ly S) (ablocks B ly1 S1) ly1 own pos a Hown).
          rewrite (FA ly1 S1 W1 mem1 md1 HJ1). lia.
        - rewrite Hes. lia. }
      split.
      { intros x Hx. exists 0. split.
        - replace x with (F + (x - F)) by ring. rewrite (rtsb_fsh_of F (x - F) Hal32 ltac:(lia)).
          apply TSH.
          split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia].
        - left. reflexivity. }
      split.
      { intros _ s Hs.
        destruct (w5bi_hull_in F 0x18c 92 Hal32 ltac:(lia) ltac:(lia) ltac:(lia) s Hs) as [Hs1 Hs2].
        replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
        apply (aview_some_of_apresent rsegs). apply PSH1. lia. }
      exact I.
    - lia.
    - lia.
    - lia.
    - apply (Hamr 0x18c 92); lia.
    - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
    - lia.
    - rewrite Hes. lia.
    - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ Hpost.
  eapply w5bi_mono; [ | | | exact Hpost ].
  - intros r Hr. refine (w5bi_clob_sub _ r _ Hr). vm_compute. reflexivity.
  - intros a [Ha | [Ha | Ha]]; unfold w5bi_W2; [left | right; left | right; right]; lia.
  - intros W3 regs3 mem3 Hkept Hkreg
      (regs1 & mem1 & (T1 & T10 & T11 & T12 & T18 & T22 & T24 & T2 & T3 & T4 & T9 & T19 & T20 & T25 & TSH)
       & Hcs & G10 & GSET & GKM).
    assert (Hcsr : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs1 r).
    { intros r Hr. rewrite <- (w5bi_getr5 regs3 r _ eq_refl), <- (w5bi_getr5 regs1 r _ eq_refl).
      apply Hcs. exact Hr. }
    red.
    split; [rewrite (Hcsr 18%bv ltac:(apply rtsb_callee; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]));
            exact T18|].
    split; [rewrite (Hcsr 22%bv ltac:(apply rtsb_callee; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]));
            exact T22|].
    split; [rewrite (Hcsr 24%bv ltac:(apply rtsb_callee; [vm_compute; lia | apply w5bi_notin; vm_compute; reflexivity]));
            exact T24|].
    split.
    { intros o Ho. rewrite GKM; [apply TSH; lia | lia | lia | rewrite Hes; lia]. }
    split.
    { intros i Hi. rewrite (GSET i Hi). reflexivity. }
    apply (w5bi_val_kept (w_H W) memc (w_H W3) mem3 (pp + 16384) 8 len VLEN).
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hkept; [lia|].
    intros [Hy | [Hy | Hy]]; [pose proof (Hbs (x - shadow_addr F) ltac:(lia)) | | ]; lia. }
(* ---------------- stage 2: run 2, 0x823e8 -> pod_write_ent's entry ---------------- *)
assert (HB : SRr rsegs W (cfg_at rsegs 0x82398 regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x83cc4 w5bi_clob
     (w5bi_W2 R F) (w5bi_RB F pp len nps nr sn))).
{ eapply SRr_mono.
  { eapply (rtsb_post_seq B MT MTL).
    { exact HA. }
    intros W1 ly1 S1 regs1 mem1 md1 Hwle HJ1 Hkreg1 Hfr1 Hperm1 Hio1 Hmo1 Hm1
      (A18 & A22 & A24 & ASH & AZ & ALEN).
    assert (HI : SRr rsegs W1 (cfg_at rsegs 0x823e8 regs1 mem1 md1)
      (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 0x83cc4 w5bi_clob
         (w5bi_W2 R F) (w5bi_RB F pp len nps nr sn))).
    { eapply SRr_mono.
      { apply (w5bi_b2 STK sp0 FP ly S W0 mem0 md0 own k ly1 S1 W1 mem1 md1 regs1 R F pp pos).
        - split; [exact HJ1|]. split; [exact HR16|]. split; [exact HRs|]. split; [exact HRlo|].
          split; [exact Hown|]. symmetry. exact (FA ly1 S1 W1 mem1 md1 HJ1).
        - exact (Permutation_in _ (Permutation_sym Hperm1) Hpp).
        - rewrite (Hkreg1 9%bv ltac:(vm_compute; lia) ltac:(apply w5bi_notin; vm_compute; reflexivity)).
          exact H9.
        - apply (w5bi_val_kept (w_H W) memc (w_H W1) mem1 (R + 0x80) 8 (F + 0x180) V80).
          intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hm1; [lia|].
          unfold w5bi_W2. intros [Hy | [Hy | Hy]]; lia.
        - apply (w5bi_val_kept (w_H W) memc (w_H W1) mem1 (R + 0x168) 8 pp V168).
          intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hm1; [lia|].
          unfold w5bi_W2. intros [Hy | [Hy | Hy]]; lia. }
      cbv beta. intros W4 c4 _ Hp4. eapply w5bi_mono; [ | | | exact Hp4 ].
      - intros r Hr. refine (w5bi_clob_sub _ r _ Hr). vm_compute. reflexivity.
      - exact (w5bi_W2_F12 R F).
      - intros W5 regs5 mem5 Hkept5 Hkreg5
          (D1 & D10 & D11 & D2 & D3 & D4 & D9 & D19 & D20 & D25 & D18 & D22 & D24 & DENT).
        red. split; [rewrite D18; exact A18|]. split; [rewrite D22; exact A22|].
        split; [rewrite D24; exact A24|].
        split; [exact D1|]. split; [exact D10|]. split; [exact D11|].
        split.
        { intros o Ho. rewrite Hkept5; [apply ASH; lia | lia | lia]. }
        split.
        { rewrite w5b_e42_mem. apply rtmb_bytes_app. split; [exact DENT|].
          change (Z.of_nat (length ((Cursor.le32 4 ++ Cursor.le32 4) ++ Cursor.le32 7))) with 12.
          replace (F + 0x180 + 12) with (F + 0x18c) by ring.
          apply (rtmb_memset_bytes rsegs (w_H W5) mem5 (F + 0x18c) 0 92).
          intros i Hi. cbn [Z.of_nat] in Hi. change (0 mod 256) with 0.
          rewrite Hkept5; [apply AZ; lia | lia | lia]. }
        apply (w5bi_val_kept (w_H W1) mem1 (w_H W5) mem5 (pp + 16384) 8 len ALEN).
        intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hkept5; [lia | lia]. }
    exact HI. }
  cbv beta. intros W2 c2 _ Hpost. eapply w5bi_mono; [ | | | exact Hpost ].
  - intros r Hr. refine (w5bi_clob_sub _ r _ Hr). vm_compute. reflexivity.
  - intros a [Ha | Ha]; exact Ha.
  - intros W3 regs3 mem3 _ _ HRv. exact HRv. }
(* ---------------- stage 3: the call pod_write_ent, 0x83cc4 -> 0x82408 ---------------- *)
assert (HC : SRr rsegs W (cfg_at rsegs 0x82398 regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82408 w5bi_clob
     (w5bi_W3 R F pp len) (w5bi_RC pp len nps nr sn))).
{ eapply SRr_mono.
  { eapply (rtsb_post_seq B MT MTL).
    { exact HB. }
    intros W1 ly1 S1 regs1 mem1 md1 Hwle HJ1 Hkreg1 Hfr1 Hperm1 Hio1 Hmo1 Hm1
      (B18 & B22 & B24 & B1 & B10 & B11 & BSH & BENT & BLEN).
    assert (Hin1 : In (pp, Layout.PP_SIZE) (ablocks B ly1 S1))
      by exact (Permutation_in _ (Permutation_sym Hperm1) Hpp).
    pose proof HJ1 as (HAR1 & _).
    assert (HspR : spZ regs1 = R).
    { unfold spZ.
      rewrite (Hkreg1 2%bv ltac:(vm_compute; lia) ltac:(apply w5bi_notin; vm_compute; reflexivity)), H2.
      apply unsigned_lit_small. lia. }
    assert (FSH1 : rt_fsh rsegs (w_H W1) mem1 F (rtmb_sh false false false false true false false)).
    { rewrite <- (rtmb_sh_e42_in false false false false false false false).
      apply (rtmb_fsh_set rsegs (w_H W) memc (w_H W1) mem1 F _ 48 13 0); [exact HFSH0 | | ].
      - intros i Hi. cbn [Z.of_nat Nat.add] in Hi. apply BSH. lia.
      - intros i Hi Hni. rewrite rtmb_sh_len in Hi. cbn [Z.of_nat Nat.add] in Hi, Hni.
        apply Hm1; [lia|]. unfold w5bi_W2. intros [Hy | [Hy | Hy]]; lia. }
    destruct (FSHP ly1 S1 W1 mem1 md1 HJ1) as (PSH1 & _).
    assert (HI : SRr rsegs W1 (cfg_at rsegs 0x83cc4 regs1 mem1 md1)
      (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 0x82408 w5bi_clob
         (w5bi_W3 R F pp len) (w5bi_RC pp len nps nr sn))).
    { eapply SRr_mono.
      { eapply (rtsb_pwe_at B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1
                  pp len 0x82408 (R - sp0) w5b_e42).
        - exact B1.
        - rewrite HspR. ring.
        - destruct (pwe_pp_of_block rsegs B ly1 S1 W1 mem1 md1 pp HAR1 Hin1)
            as (P1 & P2 & P3 & P4 & P5 & P6).
          destruct (rtsb_pwe_site F 0x180 (F + 0x180) pp (spZ regs1) Hal32 Happ eq_refl
                      ltac:(lia) ltac:(reflexivity) ltac:(rewrite HEN; lia)
                      ltac:(rewrite HPV; lia) ltac:(rewrite HspR; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5).
          destruct (rtsb_pwe_len_of_wf w5b_e42 w5b_e42_wf) as (L1 & L2 & L3 & L4).
          apply (W5B_PWE STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 pp (F + 0x180) len
                   w5b_e42).
          + split; [exact HJ1|].
            split; [rewrite B1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|].
            split; [unfold raZ; rewrite B1; rewrite unsigned_lit_small by lia; lia|].
            split; [rewrite (Hkreg1 3%bv ltac:(vm_compute; lia)
                               ltac:(apply w5bi_notin; vm_compute; reflexivity)); exact H3|].
            split; [rewrite (Hkreg1 4%bv ltac:(vm_compute; lia)
                               ltac:(apply w5bi_notin; vm_compute; reflexivity)); exact H4|].
            split; [rewrite HspR; exact HR16|].
            split; [rewrite HspR, HTP; lia|].
            split; [rewrite HspR; lia | exact Hnev].
          + exact B10.
          + exact B11.
          + lia.
          + exact Hpp8.
          + rewrite HPV. lia.
          + exact P4.
          + exact P5.
          + exact P6.
          + exact (pwe_awr_fresh B STK sp0 FP ly S ly1 S1 own pp len w5b_e42 Hin1 Hfresh Hlen0
                     ltac:(rewrite HPL, HPB; lia)).
          + rewrite HspR, HPV, HTP. lia.
          + rewrite HOL. exact BLEN.
          + exact Hlen0.
          + exact Hlen8.
          + rewrite HPL, HPB. lia.
          + exact Q1.
          + exact Q2.
          + exact Q3.
          + exact L2.
          + rewrite HEN. exact L3.
          + exact L4.
          + exact BENT.
          + rewrite HEN.
            replace (F + 0x180) with (F + RTMB_E42 + 0) by (unfold RTMB_E42; ring).
            apply (rtmb_B_ra_e42 rsegs (w_H W1) mem1 F false false false false false false 0 104);
              [exact FSH1 | exact Hal8 | lia | lia].
          + rewrite HEN. intros s Hs.
            destruct (w5bi_hull_in F 0x180 104 Hal32 ltac:(lia) ltac:(lia) ltac:(lia) s Hs) as [Hs1 Hs2].
            replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
            apply (aview_some_of_apresent rsegs). apply PSH1. lia.
          + exact Q4.
          + exact Q5. }
      cbv beta. intros W4 c4 _ Hp4. eapply w5bi_mono; [ | | | exact Hp4 ].
      - intros r Hr. refine (w5bi_clob_sub _ r _ Hr). vm_compute. reflexivity.
      - exact (w5bi_W3_pwe R F pp len sp0).
      - intros W5 regs5 mem5 Hkept5 Hkreg5 (DPOD & DLEN & DSH & DRA1 & DRA2).
        red.
        split; [rewrite (Hkreg5 18%bv ltac:(vm_compute; lia)
                          ltac:(apply w5bi_notin; vm_compute; reflexivity)); exact B18|].
        split; [rewrite (Hkreg5 22%bv ltac:(vm_compute; lia)
                          ltac:(apply w5bi_notin; vm_compute; reflexivity)); exact B22|].
        split; [rewrite (Hkreg5 24%bv ltac:(vm_compute; lia)
                          ltac:(apply w5bi_notin; vm_compute; reflexivity)); exact B24|].
        split; [exact DPOD|]. rewrite HPL, HOL in DLEN. exact DLEN. }
    exact HI. }
  cbv beta. intros W2 c2 _ Hpost. eapply w5bi_mono; [ | | | exact Hpost ].
  - intros r Hr. refine (w5bi_clob_sub _ r _ Hr). vm_compute. reflexivity.
  - intros a [Ha | Ha]; [apply w5bi_W3_W2; exact Ha | exact Ha].
  - intros W3 regs3 mem3 _ _ HRv. exact HRv. }
(* ---------------- stage 4: run 3, 0x82408 -> 0x82434 ---------------- *)
assert (HD : SRr rsegs W (cfg_at rsegs 0x82398 regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc 0x82434 w5bi_clob
     (w5bi_W4 R F pp len fsv) (w5bi_RD pp len fsv nps nr sn))).
{ eapply SRr_mono.
  { eapply (rtsb_post_seq B MT MTL).
    { exact HC. }
    intros W1 ly1 S1 regs1 mem1 md1 Hwle HJ1 Hkreg1 Hfr1 Hperm1 Hio1 Hmo1 Hm1
      (C18 & C22 & C24 & CPOD & CLEN).
    assert (HI : SRr rsegs W1 (cfg_at rsegs 0x82408 regs1 mem1 md1)
      (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 0x82434 w5bi_clob
         (w5bi_W4 R F pp len fsv) (w5bi_RD pp len fsv nps nr sn))).
    { eapply SRr_mono.
      { apply (w5bi_b3 STK sp0 FP ly S W0 mem0 md0 own k ly1 S1 W1 mem1 md1 regs1 R F pp pos fsv sn nps nr).
        - split; [exact HJ1|]. split; [exact HR16|]. split; [exact HRs|]. split; [exact HRlo|].
          split; [exact Hown|]. symmetry. exact (FA ly1 S1 W1 mem1 md1 HJ1).
        - exact (Permutation_in _ (Permutation_sym Hperm1) Hpp).
        - exact Hfresh.
        - rewrite (Hkreg1 9%bv ltac:(vm_compute; lia)
                    ltac:(apply w5bi_notin; vm_compute; reflexivity)). exact H9.
        - rewrite (Hkreg1 20%bv ltac:(vm_compute; lia)
                    ltac:(apply w5bi_notin; vm_compute; reflexivity)). exact H20.
        - rewrite (Hkreg1 25%bv ltac:(vm_compute; lia)
                    ltac:(apply w5bi_notin; vm_compute; reflexivity)). exact H25.
        - exact C18.
        - exact C22.
        - exact C24.
        - apply (w5bi_val_kept (w_H W) memc (w_H W1) mem1 (R + 0x90) 8 (pp + 0x400c) V90).
          intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hm1; [lia|].
          unfold w5bi_W3, w5bi_W2, pwe_E. rewrite HPL, HOL.
          intros [[Hy | [Hy | Hy]] | [Hy | Hy]]; lia.
        - apply (w5bi_val_kept (w_H W) memc (w_H W1) mem1 (R + 0x160) 8 fsv V160).
          intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hm1; [lia|].
          unfold w5bi_W3, w5bi_W2, pwe_E. rewrite HPL, HOL.
          intros [[Hy | [Hy | Hy]] | [Hy | Hy]]; lia.
        - exact Hfsv.
        - exact Hnps.
        - exact Hnr.
        - exact Hsn. }
      cbv beta. intros W4 c4 _ Hp4. eapply w5bi_mono; [ | | | exact Hp4 ].
      - intros r Hr. refine (w5bi_clob_sub _ r _ Hr). vm_compute. reflexivity.
      - exact (w5bi_W4_hp R F pp len fsv).
      - intros W5 regs5 mem5 Hkept5 Hkreg5 (D5 & D29 & D13 & D19 & D24 & DHP).
        red. split; [exact D5|]. split; [exact D29|]. split; [exact D13|].
        split.
        { apply (rtmb_bytes_kept rsegs (w_H W1) mem1); [exact CPOD|].
          intros x Hx. rewrite w5bi_lenpod in Hx. apply Hkept5; [lia|]. intros [_ Hy]. lia. }
        split.
        { apply (w5bi_val_kept (w_H W1) mem1 (w_H W5) mem5 (pp + 16384) 8 (len + 16) CLEN).
          intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hkept5; [lia|]. intros [_ Hy]. lia. }
        exact DHP. }
    exact HI. }
  cbv beta. intros W2 c2 _ Hpost. eapply w5bi_mono; [ | | | exact Hpost ].
  - intros r Hr. refine (w5bi_clob_sub _ r _ Hr). vm_compute. reflexivity.
  - intros a [Ha | Ha]; [apply w5bi_W4_W3; exact Ha | exact Ha].
  - intros W3 regs3 mem3 _ _ HRv. exact HRv. }
(* ---------------- stage 5: run 4, 0x82434 -> LATCH7, and the piece's post ---------------- *)
eapply SRr_mono.
{ eapply (rtsb_post_seq B MT MTL).
  { exact HD. }
  intros W1 ly1 S1 regs1 mem1 md1 Hwle HJ1 Hkreg1 Hfr1 Hperm1 Hio1 Hmo1 Hm1
    (E5 & E29 & E13 & EPOD & ELEN & EHP).
  assert (HI : SRr rsegs W1 (cfg_at rsegs 0x82434 regs1 mem1 md1)
    (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 0x8257c w5bi_clob
       (w5bi_W4 R F pp len fsv) (w5bi_RE F pp len fsv nps nr sn))).
  { eapply SRr_mono.
    { apply (w5bi_b4 STK sp0 FP ly S W0 mem0 md0 own k ly1 S1 W1 mem1 md1 regs1 R F pos).
      - split; [exact HJ1|]. split; [exact HR16|]. split; [exact HRs|]. split; [exact HRlo|].
        split; [exact Hown|]. symmetry. exact (FA ly1 S1 W1 mem1 md1 HJ1).
      - rewrite (Hkreg1 19%bv ltac:(vm_compute; lia)
                  ltac:(apply w5bi_notin; vm_compute; reflexivity)). exact H19. }
    cbv beta. intros W4 c4 _ Hp4. eapply w5bi_mono; [ | | | exact Hp4 ].
    - intros r Hr. refine (w5bi_clob_sub _ r _ Hr). vm_compute. reflexivity.
    - exact (w5bi_W4_sh R F pp len fsv).
    - intros W5 regs5 mem5 Hkept5 Hkreg5 (G24 & G8).
      red.
      split; [rewrite (Hkreg5 5%bv ltac:(vm_compute; lia)
                        ltac:(apply w5bi_notin; vm_compute; reflexivity)); exact E5|].
      split; [rewrite (Hkreg5 29%bv ltac:(vm_compute; lia)
                        ltac:(apply w5bi_notin; vm_compute; reflexivity)); exact E29|].
      split; [rewrite (Hkreg5 13%bv ltac:(vm_compute; lia)
                        ltac:(apply w5bi_notin; vm_compute; reflexivity)); exact E13|].
      split; [exact G24|].
      split.
      { apply (rtmb_bytes_kept rsegs (w_H W1) mem1); [exact EPOD|].
        intros x Hx. rewrite w5bi_lenpod in Hx. apply Hkept5; [lia|]. intros Hy.
        pose proof (Hbs (x - shadow_addr F) ltac:(lia)). lia. }
      split.
      { apply (w5bi_val_kept (w_H W1) mem1 (w_H W5) mem5 (pp + 16384) 8 (len + 16) ELEN).
        intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply Hkept5; [lia|]. intros Hy.
        pose proof (Hbs (x - shadow_addr F) ltac:(lia)). lia. }
      split.
      { intros Hf1. apply (rtmb_bytes_kept rsegs (w_H W1) mem1); [exact (EHP Hf1)|].
        intros x Hx. rewrite w5bi_len4 in Hx. apply Hkept5; [lia|]. intros Hy.
        pose proof (Hbs (x - shadow_addr F) ltac:(lia)). lia. }
      exact G8. }
  exact HI. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & Hk & Hf & Hp & Hio & Hmo & Hm &
  (G5 & G29 & G13 & G24 & GPOD & GLEN & GHP & G8)).
red. exists ly2, S2, regs2, mem2, md2.
split; [exact Hc|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; apply Hk; [exact Hr0 | intros X; apply Hn; apply in_app_or in X; tauto]|].
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|].
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 16384 <= a < R) -> ~ w5bi_E F pp len fsv a ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hst HE. apply Hm; [exact Ha|].
  assert (HN : ~ w5bi_W4 R F pp len fsv a).
  { unfold w5bi_W4, w5bi_W3, w5bi_W2. intros [[[Hy | [Hy | Hy]] | Hy] | Hy].
    - apply HE. unfold w5bi_E. right. left. exact Hy.
    - apply HE. unfold w5bi_E. left. exact Hy.
    - exact (Hst Hy).
    - apply HE. unfold w5bi_E. right. right. left. exact Hy.
    - apply HE. unfold w5bi_E. right. right. right. exact Hy. }
  intros [HW | HW]; exact (HN HW). }
split.
{ intros a Ha Hst HE. rewrite Hspz, HTS in Hst. exact (KEPT a Ha Hst HE). }
split; [exact GPOD|].
split; [rewrite HOL; exact GLEN|].
split; [exact GHP|].
split.
{ rewrite <- (rtmb_sh_e42_out false false false false false false false).
  apply (rtmb_fsh_set rsegs (w_H W) memc (w_H W2) mem2 F _ 48 13 248); [exact HFSH0 | | ].
  - intros i Hi. cbn [Z.of_nat Nat.add] in Hi. apply G8. lia.
  - intros i Hi Hni. rewrite rtmb_sh_len in Hi. cbn [Z.of_nat Nat.add] in Hi, Hni.
    pose proof (Hbs i ltac:(lia)) as Hz.
    apply KEPT; [lia | lia |].
    unfold w5bi_E, pwe_E. rewrite HPL, HOL. intros [Hy | [Hy | [Hy | [_ Hy]]]]; lia. }
split; [exact G5|]. split; [exact G29|]. split; [exact G13 | exact G24].
Qed.
End c.

Print Assumptions w5b_int_core.
